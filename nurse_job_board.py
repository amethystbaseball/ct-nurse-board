#!/usr/bin/env python3
"""
nurse_job_board.py
==================
Aggregates public RN / APRN job listings from Connecticut hospital career
portals into a local job board (SQLite + a static HTML page).

It does NOT scrape Indeed/LinkedIn. It pulls from each health system's own
applicant tracking system (ATS), which is more reliable and on far firmer
legal footing than parsing third-party HTML:

  - Yale New Haven Health  -> iCIMS   (jobs.ynhhs.org)
  - Hartford HealthCare    -> Phenom  (hhccareers.org)

Add more systems by adding entries to SOURCES and (if they run a different
ATS) writing a small adapter. Most large hospital systems run one of:
iCIMS, Phenom, Workday, Taleo, or Greenhouse.

Usage
-----
    pip install requests beautifulsoup4
    python nurse_job_board.py --refresh     # pull all sources into the DB
    python nurse_job_board.py --export       # write board.html from the DB
    python nurse_job_board.py                 # refresh + export (default)

    python nurse_job_board.py --refresh --source ynhh   # one source only
    python nurse_job_board.py --refresh --verbose

Run it on a schedule with cron, e.g. every 6 hours:
    0 */6 * * *  cd /path/to/tool && /usr/bin/python3 nurse_job_board.py
"""

from __future__ import annotations

import argparse
import dataclasses
import datetime as dt
import hashlib
import html
import json
import re
import sqlite3
import sys
import time
from typing import Iterable, Optional

import requests
from bs4 import BeautifulSoup

# --------------------------------------------------------------------------- #
# Configuration
# --------------------------------------------------------------------------- #

DB_PATH = "jobs.db"
OUTPUT_HTML = "board.html"
OUTPUT_JSON = "jobs.json"

# Be a polite citizen: identify yourself, throttle, and don't hammer.
USER_AGENT = "CT-Nurse-Job-Board/1.0 (personal aggregator; contact: you@example.com)"
REQUEST_DELAY_SEC = 1.5        # pause between requests to the same host
REQUEST_TIMEOUT_SEC = 30
MAX_SEARCH_PAGES = 25          # safety cap per source

# Server-side keyword queries used to narrow results before we classify.
# Broad on purpose; the classifier below does the precise RN/APRN bucketing.
NURSE_KEYWORDS = ["registered nurse", "nurse practitioner", "APRN"]

# Only keep listings whose location text contains one of these terms. This is
# what filters out, e.g., Trinity's national Workday postings from other states.
# Set TARGET_LOCATIONS = [] to keep every location.
TARGET_LOCATIONS = ["CT", "Connecticut"]

# Hide listings older than this many days from the board (they stay in the DB
# archive, they just don't display). Healthcare portals leave "evergreen" reqs
# open for a year or more; this keeps the board current. Raise it to show more
# history, or set to a huge number (e.g. 36500) to effectively disable.
MAX_AGE_DAYS = 60

# Each source: a key, a display name, an adapter type, and a base URL.
SOURCES = [
    {
        "key": "ynhh",
        "name": "Yale New Haven Health",
        "adapter": "icims",
        "base_url": "https://jobs.ynhhs.org",
    },
    {
        "key": "hhc",
        "name": "Hartford HealthCare",
        "adapter": "phenom",
        "base_url": "https://www.hhccareers.org",
    },
    {
        # Trinity Health Of New England (St. Francis, St. Mary's, Johnson
        # Memorial) posts through the national Trinity Health Workday tenant.
        # Locations get filtered to CT downstream; you can also pre-filter
        # server-side with appliedFacets if you want.
        "key": "trinity_ne",
        "name": "Trinity Health Of New England",
        "adapter": "workday",
        "host": "https://trinityhealth.wd1.myworkdayjobs.com",
        "tenant": "trinityhealth",
        "site": "Jobs",
    },
    {
        "key": "stamford",
        "name": "Stamford Health",
        "adapter": "oracle",
        "host": "https://fa-ewfb-saasfaprod1.fa.ocs.oraclecloud.com",
        "site": "Careers",
    },
    {
        "key": "ctchildrens",
        "name": "Connecticut Children's",
        "adapter": "oracle",
        "host": "https://fa-evav-saasfaprod1.fa.ocs.oraclecloud.com",
        "site": "connecticutchildrenscareers",
    },
    # Add more here. To add another Workday system, copy the Trinity block and
    # change host/tenant/site. Find those three by opening the system's careers
    # page: the URL looks like
    #   https://<tenant>.wdN.myworkdayjobs.com/<site>
    # so host = scheme+subdomain, tenant = the subdomain, site = path segment.
    #
    # Candidate CT systems still to confirm:
    #   Nuvance Health  -> in transition to Northwell; old Jobvite instance at
    #                      jobs.jobvite.com/nuvance. Unstable now; revisit after
    #                      the Northwell migration settles.
    #   Stamford Health -> platform unconfirmed; check the careers page URL.
    #   VA Connecticut  -> federal; USAJobs API (separate adapter, easy add).
]


# --------------------------------------------------------------------------- #
# Data model
# --------------------------------------------------------------------------- #

@dataclasses.dataclass
class Job:
    source_key: str
    source_name: str
    external_id: str
    title: str
    location: str
    url: str
    role: str = ""              # "RN" or "APRN", filled by classify_role
    description: str = ""
    posted_at: str = ""         # ISO date string if available
    first_seen: str = ""
    last_seen: str = ""

    def fingerprint(self) -> str:
        """Stable hash to collapse the same posting seen twice.

        Uses employer + normalized title + normalized location, NOT the URL,
        so a re-posted/duplicated req with a new ID still dedupes.
        """
        norm = lambda s: re.sub(r"\s+", " ", (s or "").strip().lower())
        basis = f"{self.source_key}|{norm(self.title)}|{norm(self.location)}"
        return hashlib.sha1(basis.encode("utf-8")).hexdigest()


# --------------------------------------------------------------------------- #
# Role classification (RN vs APRN vs not-a-nurse)
# --------------------------------------------------------------------------- #

# APRN is checked first because it's more specific. A "Psych Nurse
# Practitioner" is APRN, not RN, even though "nurse" matches both.
_APRN_PATTERNS = [
    r"\baprn\b",
    r"\bnurse practitioner\b",
    r"\b(fnp|pmhnp|agacnp|agpcnp|acnp|pnp|nnp|whnp)\b",
    r"\bcrna\b", r"\bnurse anesthetist\b",
    r"\bcnm\b", r"\bnurse midwife\b", r"\bmidwife\b",
    r"\bclinical nurse specialist\b", r"\bcns\b",
    r"\badvanced practice\b",
]

_RN_PATTERNS = [
    r"\bregistered nurse\b",
    r"\brn\b",
    r"\bstaff nurse\b",
    r"\bclinical nurse\b",
    r"\bcharge nurse\b",
    r"\bnurse (manager|coordinator|educator|supervisor)\b",
]

# Hard excludes: roles that contain "nurse" but aren't RN/APRN positions.
_EXCLUDE_PATTERNS = [
    r"\bnursing assistant\b", r"\bcna\b", r"\bnurse aide\b", r"\bnurse's aide\b",
    r"\bpatient care (tech|technician|associate|assistant)\b", r"\bpct\b", r"\bpca\b",
    r"\bnurse extern\b", r"\bstudent nurse\b", r"\bnurse intern\b",
    r"\bunit (secretary|clerk)\b", r"\bscheduler\b",
    r"\bphysician assistant\b", r"\bphysician's assistant\b", r"\bphys assistant\b",
    r"(?<![a-z])PA(?![a-z])",  # standalone PA (Physician Assistant); case-sensitive on purpose
    r"\blicensed practical nurse\b", r"\blpn\b",  # remove this line if you want LPNs too
]

_APRN_RE = re.compile("|".join(_APRN_PATTERNS), re.I)
_RN_RE = re.compile("|".join(_RN_PATTERNS), re.I)
# Most excludes are case-insensitive; the standalone "PA" rule is case-sensitive
# (added without re.I via inline handling) so it matches "PA" but not "pa" inside words.
_EXCLUDE_RE = re.compile("|".join(p for p in _EXCLUDE_PATTERNS if p != r"(?<![a-z])PA(?![a-z])"), re.I)
_PA_RE = re.compile(r"(?<![A-Za-z])PA(?![A-Za-z])")  # standalone uppercase PA token


def classify_role(title: str, description: str = "") -> Optional[str]:
    """Return 'APRN', 'RN', or None (drop). Title is weighted most heavily."""
    title = title or ""
    # Genuine nurse-practitioner signals win first, so a combined APRN posting
    # isn't dropped by the PA exclusion below.
    if _APRN_RE.search(title):
        return "APRN"
    # Hard non-nurse excludes (CNA, PCA, PCT, LPN, scheduler, physician assistant).
    if _EXCLUDE_RE.search(title) or _PA_RE.search(title):
        return None
    if _RN_RE.search(title):
        return "RN"
    # Fall back to description only if the title was ambiguous but nurse-ish.
    blob = f"{title} {description}"
    if _APRN_RE.search(blob):
        return "APRN"
    if _EXCLUDE_RE.search(title) or _PA_RE.search(title):
        return None
    if _RN_RE.search(blob):
        return "RN"
    return None


# Location filter: keep only listings whose location text matches a target.
_LOC_RE = (re.compile("|".join(r"\b" + re.escape(t) + r"\b" for t in TARGET_LOCATIONS), re.I)
           if TARGET_LOCATIONS else None)


def is_target_location(location: str) -> bool:
    """True if the listing is in a target location (or filtering is disabled)."""
    if _LOC_RE is None:
        return True
    return bool(location) and bool(_LOC_RE.search(location))


# --------------------------------------------------------------------------- #
# HTTP helper
# --------------------------------------------------------------------------- #

def make_session() -> requests.Session:
    s = requests.Session()
    s.headers.update({"User-Agent": USER_AGENT, "Accept": "*/*"})
    return s


def polite_get(session: requests.Session, url: str, **kw) -> requests.Response:
    time.sleep(REQUEST_DELAY_SEC)
    return session.get(url, timeout=REQUEST_TIMEOUT_SEC, **kw)


def polite_post(session: requests.Session, url: str, **kw) -> requests.Response:
    time.sleep(REQUEST_DELAY_SEC)
    return session.post(url, timeout=REQUEST_TIMEOUT_SEC, **kw)


# --------------------------------------------------------------------------- #
# Adapter: iCIMS / Jibe  (Yale New Haven Health)
# --------------------------------------------------------------------------- #
# jobs.ynhhs.org is a JavaScript app on iCIMS's "Jibe" career-site platform.
# The job list isn't in the HTML; it's served from a JSON API at /api/jobs.
#   GET https://<base>/api/jobs?keyword=<kw>&page=<n>&limit=<N>
# Response: {"jobs":[{"data":{...}}], "totalCount":N}. The public posting URL
# is https://<base>/jobs/<slug-or-id>.

_jibe_dumped = {"done": False}


def fetch_icims(source: dict, session: requests.Session, verbose: bool) -> list[Job]:
    base = source["base_url"].rstrip("/")
    endpoint = f"{base}/api/jobs"
    limit = 50
    by_id: dict[str, Job] = {}

    for kw in NURSE_KEYWORDS:
        page = 1
        for _ in range(MAX_SEARCH_PAGES):
            params = {"keyword": kw, "page": page, "limit": limit,
                      "sortBy": "posted_date"}
            try:
                resp = polite_get(session, endpoint, params=params,
                                  headers={"Accept": "application/json"})
            except requests.RequestException as e:
                if verbose:
                    print(f"  [jibe] request failed ({kw} p{page}): {e}",
                          file=sys.stderr)
                break
            if resp.status_code != 200:
                if verbose:
                    print(f"  [jibe] HTTP {resp.status_code} for {kw} p{page}")
                break
            try:
                data = resp.json()
            except ValueError:
                break

            arr = data.get("jobs") or []
            total = data.get("totalCount") or data.get("total") or 0

            if verbose and not _jibe_dumped["done"] and arr:
                _jibe_dumped["done"] = True
                d0 = arr[0].get("data", arr[0])
                print(f"  [jibe] totalCount={total}; sample data keys: {sorted(d0.keys())}")

            if not arr:
                break

            for item in arr:
                d = item.get("data", item)
                slug = d.get("slug") or d.get("id") or d.get("req_id") or ""
                if not slug or slug in by_id:
                    continue
                loc = (d.get("full_location") or
                       ", ".join(p for p in (d.get("city", ""), d.get("state", "")) if p))
                by_id[str(slug)] = Job(
                    source_key=source["key"],
                    source_name=source["name"],
                    external_id=str(d.get("req_id") or slug),
                    title=(d.get("title") or "").strip(),
                    location=loc,
                    url=f"{base}/jobs/{slug}",
                    description=_strip_html(d.get("description")
                                            or d.get("descriptionTeaser") or ""),
                    posted_at=_iso_date(d.get("posted_date") or d.get("postedDate") or ""),
                )

            if verbose:
                print(f"  [jibe] '{kw}' p{page}: {len(arr)} rows ({len(by_id)} total)")
            page += 1
            if (total and page * limit > total) or len(arr) < limit:
                break

    return list(by_id.values())


# --------------------------------------------------------------------------- #
# Adapter: Phenom  (Hartford HealthCare)
# --------------------------------------------------------------------------- #
# Phenom career sites expose a JSON search widget at POST /widgets. We page
# through results with the `from` offset and read the jobs array out of the
# refineSearch payload.

def fetch_phenom(source: dict, session: requests.Session, verbose: bool) -> list[Job]:
    base = source["base_url"].rstrip("/")
    endpoint = f"{base}/widgets"
    page_size = 20
    by_id: dict[str, Job] = {}

    for kw in NURSE_KEYWORDS:
        offset = 0
        for _ in range(MAX_SEARCH_PAGES):
            payload = {
                "lang": "en_us",
                "deviceType": "desktop",
                "country": "us",
                "pageName": "search-results",
                "ddoKey": "refineSearch",
                "sortBy": "Most relevant",
                "subsearch": "",
                "from": offset,
                "jobs": True,
                "counts": True,
                "all_fields": ["category", "country", "state", "city", "type"],
                "size": page_size,
                "keywords": kw,
                "global": True,
                "selected_fields": {},
                "locationData": {},
            }
            try:
                resp = polite_post(session, endpoint, json=payload,
                                   headers={"Content-Type": "application/json"})
            except requests.RequestException as e:
                if verbose:
                    print(f"  [phenom] request failed ({kw} @{offset}): {e}",
                          file=sys.stderr)
                break
            if resp.status_code != 200:
                break
            try:
                data = resp.json()
            except ValueError:
                break

            jobs_arr = _phenom_jobs_array(data)
            if not jobs_arr:
                break

            # One-time diagnostic: show the field names + url-ish values of the
            # first job so we can see exactly how this site names its links.
            if verbose and not _phenom_dumped["done"] and jobs_arr:
                _phenom_dumped["done"] = True
                sample = jobs_arr[0]
                print(f"  [phenom] sample job keys: {sorted(sample.keys())}")
                for k in sample:
                    if "url" in k.lower() or "link" in k.lower() or "path" in k.lower():
                        print(f"  [phenom] sample {k} = {sample[k]!r}")

            for j in jobs_arr:
                ext_id = str(j.get("jobSeqNo") or j.get("id") or j.get("jobId") or "")
                if not ext_id or ext_id in by_id:
                    continue
                url = _phenom_url(j, base)
                loc = j.get("location") or ", ".join(
                    p for p in (j.get("city", ""), j.get("state", "")) if p)
                by_id[ext_id] = Job(
                    source_key=source["key"],
                    source_name=source["name"],
                    external_id=ext_id,
                    title=(j.get("title") or "").strip(),
                    location=loc,
                    url=url,
                    description=_strip_html(j.get("descriptionTeaser")
                                            or j.get("description") or ""),
                    posted_at=_iso_date(j.get("postedDate") or j.get("dateCreated") or ""),
                )

            if verbose:
                print(f"  [phenom] '{kw}' @{offset}: {len(jobs_arr)} rows "
                      f"({len(by_id)} total)")
            if len(jobs_arr) < page_size:
                break
            offset += page_size

    return list(by_id.values())


def _phenom_jobs_array(data: dict) -> list[dict]:
    """Handle the couple of shapes Phenom responses come in."""
    if not isinstance(data, dict):
        return []
    rs = data.get("refineSearch") or data
    block = rs.get("data") if isinstance(rs, dict) else None
    if isinstance(block, dict) and isinstance(block.get("jobs"), list):
        return block["jobs"]
    if isinstance(data.get("jobs"), list):
        return data["jobs"]
    return []


# One-time flag so the diagnostic field dump only prints once per run.
_phenom_dumped = {"done": False}

# Phenom job objects name the link differently across sites. Try the common
# fields, then fall back to building one from the job id + a title slug.
_PHENOM_URL_FIELDS = ["applyUrl", "jobUrl", "url", "jobDetailUrl",
                      "detailUrl", "canonicalUrl", "jobPostingUrl"]


def _phenom_url(j: dict, base: str) -> str:
    for f in _PHENOM_URL_FIELDS:
        v = j.get(f)
        if isinstance(v, str) and v.strip():
            v = v.strip()
            if v.startswith("//"):
                return "https:" + v
            if v.startswith("/"):
                return base + v
            if v.startswith("http"):
                return v
    # Fallback: Phenom detail pages resolve from the job id; a missing slug
    # still redirects to the canonical posting.
    jid = j.get("jobId") or j.get("jobSeqNo") or j.get("id")
    if jid:
        slug = re.sub(r"[^a-z0-9]+", "-", (j.get("title") or "").lower()).strip("-")
        tail = f"/job/{jid}" + (f"/{slug}" if slug else "")
        return base + "/us/en" + tail
    return ""


# --------------------------------------------------------------------------- #
# Adapter: Workday  (Trinity Health Of New England, and most large systems)
# --------------------------------------------------------------------------- #
# Workday exposes a clean JSON search API at:
#     POST https://<host>/wday/cxs/<tenant>/<site>/jobs
# Body: {"appliedFacets":{}, "limit":20, "offset":N, "searchText":"<kw>"}
# Each jobPosting gives title, externalPath, locationsText, and postedOn.
# The public posting URL is host + "/" + site + externalPath.

def fetch_workday(source: dict, session: requests.Session, verbose: bool) -> list[Job]:
    host = source["host"].rstrip("/")
    tenant = source["tenant"]
    site = source["site"]
    endpoint = f"{host}/wday/cxs/{tenant}/{site}/jobs"
    limit = 20
    by_path: dict[str, Job] = {}

    for kw in NURSE_KEYWORDS:
        offset = 0
        for _ in range(MAX_SEARCH_PAGES):
            payload = {"appliedFacets": {}, "limit": limit,
                       "offset": offset, "searchText": kw}
            try:
                resp = polite_post(session, endpoint, json=payload,
                                   headers={"Content-Type": "application/json",
                                            "Accept": "application/json"})
            except requests.RequestException as e:
                if verbose:
                    print(f"  [workday] request failed ({kw} @{offset}): {e}",
                          file=sys.stderr)
                break
            if resp.status_code != 200:
                break
            try:
                data = resp.json()
            except ValueError:
                break

            postings = data.get("jobPostings") or []
            if not postings:
                break

            for p in postings:
                path = p.get("externalPath") or ""
                if not path or path in by_path:
                    continue
                url = f"{host}/{site}{path}"
                by_path[path] = Job(
                    source_key=source["key"],
                    source_name=source["name"],
                    external_id=path.rsplit("_", 1)[-1] if "_" in path else path,
                    title=(p.get("title") or "").strip(),
                    location=(p.get("locationsText") or "").strip(),
                    url=url,
                    description="",  # detail body needs a second call; not required
                    posted_at=_workday_posted_date(p.get("postedOn", "")),
                )

            if verbose:
                print(f"  [workday] '{kw}' @{offset}: {len(postings)} rows "
                      f"({len(by_path)} total)")
            total = data.get("total", 0)
            offset += limit
            if offset >= total or len(postings) < limit:
                break

    return list(by_path.values())


def _workday_posted_date(value: str) -> str:
    """Workday's postedOn is usually relative text like 'Posted 3 Days Ago'."""
    if not value:
        return ""
    text = value.lower()
    today = dt.date.today()
    if "today" in text:
        return today.isoformat()
    if "yesterday" in text:
        return (today - dt.timedelta(days=1)).isoformat()
    m = re.search(r"(\d+)\s*day", text)
    if m:
        return (today - dt.timedelta(days=int(m.group(1)))).isoformat()
    m = re.search(r"(\d+)\s*month", text)
    if m:
        return (today - dt.timedelta(days=30 * int(m.group(1)))).isoformat()
    return _iso_date(value)  # fall back if it's an actual date string


# --------------------------------------------------------------------------- #
# Adapter: Oracle Recruiting Cloud  (Stamford Health, Connecticut Children's)
# --------------------------------------------------------------------------- #
# Oracle's candidate-experience REST API:
#   GET https://<host>/hcmRestApi/resources/latest/recruitingCEJobRequisitions
#       ?finder=findReqs;siteNumber=<site>,limit=N,offset=O,keyword=<kw>...
# Response: items[0].requisitionList[] with Id, Title, PrimaryLocation, PostedDate.
# The public posting URL is built from the site + requisition Id.

_oracle_dumped = {"done": False}


def fetch_oracle(source: dict, session: requests.Session, verbose: bool) -> list[Job]:
    host = source["host"].rstrip("/")
    site = source["site"]
    endpoint = f"{host}/hcmRestApi/resources/latest/recruitingCEJobRequisitions"
    limit = 50
    by_id: dict[str, Job] = {}

    for kw in NURSE_KEYWORDS:
        offset = 0
        for _ in range(MAX_SEARCH_PAGES):
            finder = (f"findReqs;siteNumber={site},"
                      f"facetsList=LOCATIONS;TITLES;CATEGORIES;POSTING_DATES,"
                      f"limit={limit},offset={offset},sortBy=POSTING_DATES_DESC,"
                      f"keyword={kw}")
            params = {
                "onlyData": "true",
                "expand": "requisitionList.secondaryLocations,flexFieldsFacet.values",
                "finder": finder,
            }
            try:
                resp = polite_get(session, endpoint, params=params,
                                  headers={"Accept": "application/json"})
            except requests.RequestException as e:
                if verbose:
                    print(f"  [oracle] request failed ({kw} @{offset}): {e}",
                          file=sys.stderr)
                break
            if resp.status_code != 200:
                if verbose:
                    print(f"  [oracle] HTTP {resp.status_code} for {kw} @{offset}")
                break
            try:
                data = resp.json()
            except ValueError:
                break

            items = data.get("items") or []
            block = items[0] if items else {}
            reqs = block.get("requisitionList") or []
            total = block.get("TotalJobsCount", 0)

            if verbose and not _oracle_dumped["done"]:
                _oracle_dumped["done"] = True
                print(f"  [oracle] TotalJobsCount={total}; "
                      f"sample req keys: {sorted(reqs[0].keys()) if reqs else '(none)'}")

            if not reqs:
                break

            for r in reqs:
                jid = str(r.get("Id") or r.get("RequisitionId") or "")
                if not jid or jid in by_id:
                    continue
                loc = r.get("PrimaryLocation") or ""
                if not loc:
                    sec = r.get("secondaryLocations") or []
                    loc = ", ".join(s.get("Name", "") for s in sec if isinstance(s, dict))
                url = f"{host}/hcmUI/CandidateExperience/en/sites/{site}/job/{jid}"
                by_id[jid] = Job(
                    source_key=source["key"],
                    source_name=source["name"],
                    external_id=jid,
                    title=(r.get("Title") or "").strip(),
                    location=loc,
                    url=url,
                    posted_at=_iso_date(r.get("PostedDate") or ""),
                )

            if verbose:
                print(f"  [oracle] '{kw}' @{offset}: {len(reqs)} rows "
                      f"({len(by_id)} total)")
            offset += limit
            if (total and offset >= total) or len(reqs) < limit:
                break

    return list(by_id.values())


# --------------------------------------------------------------------------- #
# Shared helpers
# --------------------------------------------------------------------------- #

ADAPTERS = {"icims": fetch_icims, "phenom": fetch_phenom,
            "workday": fetch_workday, "oracle": fetch_oracle}


def _strip_html(text: str) -> str:
    if not text:
        return ""
    return re.sub(r"\s+", " ", BeautifulSoup(text, "html.parser").get_text(" ")).strip()


def _iso_date(value: str) -> str:
    if not value:
        return ""
    value = str(value)
    for fmt in ("%Y-%m-%dT%H:%M:%S", "%Y-%m-%d", "%m/%d/%Y", "%Y-%m-%dT%H:%M:%SZ"):
        try:
            return dt.datetime.strptime(value[:len(fmt) + 2 if "T" in fmt else len(fmt)],
                                        fmt).date().isoformat()
        except ValueError:
            continue
    m = re.search(r"\d{4}-\d{2}-\d{2}", value)
    return m.group(0) if m else ""


# --------------------------------------------------------------------------- #
# Storage
# --------------------------------------------------------------------------- #

def init_db(conn: sqlite3.Connection) -> None:
    conn.execute("""
        CREATE TABLE IF NOT EXISTS jobs (
            fingerprint TEXT PRIMARY KEY,
            source_key  TEXT,
            source_name TEXT,
            external_id TEXT,
            title       TEXT,
            location    TEXT,
            url         TEXT,
            role        TEXT,
            description TEXT,
            posted_at   TEXT,
            first_seen  TEXT,
            last_seen   TEXT,
            active      INTEGER DEFAULT 1
        )
    """)
    conn.commit()


def upsert_jobs(conn: sqlite3.Connection, jobs: Iterable[Job]) -> tuple[int, int]:
    now = dt.datetime.now().isoformat(timespec="seconds")
    new_count = updated = 0
    for job in jobs:
        fp = job.fingerprint()
        row = conn.execute("SELECT fingerprint FROM jobs WHERE fingerprint = ?",
                           (fp,)).fetchone()
        if row:
            conn.execute(
                "UPDATE jobs SET last_seen=?, active=1, url=?, title=?, "
                "location=?, role=?, posted_at=? WHERE fingerprint=?",
                (now, job.url, job.title, job.location, job.role,
                 job.posted_at, fp))
            updated += 1
        else:
            conn.execute(
                "INSERT INTO jobs (fingerprint, source_key, source_name, "
                "external_id, title, location, url, role, description, "
                "posted_at, first_seen, last_seen, active) "
                "VALUES (?,?,?,?,?,?,?,?,?,?,?,?,1)",
                (fp, job.source_key, job.source_name, job.external_id,
                 job.title, job.location, job.url, job.role, job.description,
                 job.posted_at, now, now))
            new_count += 1
    conn.commit()
    return new_count, updated


def deactivate_stale(conn: sqlite3.Connection, source_key: str, run_ts: str) -> int:
    """Mark jobs from this source that we did NOT see in this run as inactive."""
    cur = conn.execute(
        "UPDATE jobs SET active=0 WHERE source_key=? AND last_seen < ? AND active=1",
        (source_key, run_ts))
    conn.commit()
    return cur.rowcount


# --------------------------------------------------------------------------- #
# Refresh + export
# --------------------------------------------------------------------------- #

def refresh(conn: sqlite3.Connection, only: Optional[str], verbose: bool) -> None:
    session = make_session()
    for source in SOURCES:
        if only and source["key"] != only:
            continue
        adapter = ADAPTERS.get(source["adapter"])
        if not adapter:
            print(f"! no adapter '{source['adapter']}' for {source['key']}",
                  file=sys.stderr)
            continue

        run_ts = dt.datetime.now().isoformat(timespec="seconds")
        print(f"-> {source['name']} ({source['adapter']}) ...")
        try:
            raw_jobs = adapter(source, session, verbose)
        except Exception as e:  # noqa: BLE001 - keep one bad source from killing the run
            print(f"   ERROR: {e}", file=sys.stderr)
            continue

        kept: list[Job] = []
        dropped_no_url = dropped_loc = dropped_role = 0
        for job in raw_jobs:
            if not (job.url or "").lower().startswith(("http://", "https://")):
                dropped_no_url += 1  # no usable link; nothing a student can act on
                continue
            if not is_target_location(job.location):
                dropped_loc += 1
                continue
            role = classify_role(job.title, job.description)
            if not role:
                dropped_role += 1
                continue
            job.role = role
            kept.append(job)

        new_count, updated = upsert_jobs(conn, kept)
        stale = deactivate_stale(conn, source["key"], run_ts)
        print(f"   {len(raw_jobs)} pulled -> {len(kept)} RN/APRN "
              f"({new_count} new, {updated} updated, {stale} closed)")
        print(f"   dropped: {dropped_no_url} no-link, {dropped_loc} non-CT, "
              f"{dropped_role} not-RN/APRN")


def _active_recent_rows(conn: sqlite3.Connection) -> list:
    """Active listings no older than MAX_AGE_DAYS (undated ones are kept).

    Newest first; undated listings sort to the bottom.
    """
    cutoff = (dt.date.today() - dt.timedelta(days=MAX_AGE_DAYS)).isoformat()
    return conn.execute(
        "SELECT title, role, source_name, location, url, posted_at, first_seen "
        "FROM jobs WHERE active=1 AND (posted_at = '' OR posted_at >= ?) "
        "ORDER BY (posted_at='' ), posted_at DESC, first_seen DESC",
        (cutoff,)).fetchall()


def export_html(conn: sqlite3.Connection, path: str) -> int:
    rows = _active_recent_rows(conn)

    generated = dt.datetime.now().strftime("%B %d, %Y at %I:%M %p")
    esc = lambda s: html.escape(str(s or ""))

    tr = []
    for title, role, src, loc, url, posted, first_seen in rows:
        badge = "aprn" if role == "APRN" else "rn"
        date_shown = posted or first_seen[:10]
        tr.append(f"""        <tr data-role="{role}">
          <td><a href="{esc(url)}" target="_blank" rel="noopener">{esc(title)}</a></td>
          <td><span class="badge {badge}">{esc(role)}</span></td>
          <td>{esc(src)}</td>
          <td>{esc(loc)}</td>
          <td class="date">{esc(date_shown)}</td>
        </tr>""")

    rn_n = sum(1 for r in rows if r[1] == "RN")
    aprn_n = sum(1 for r in rows if r[1] == "APRN")

    doc = f"""<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Connecticut Nursing Jobs</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=EB+Garamond:ital,wght@0,400;0,500;0,600;1,400&family=DM+Sans:wght@400;500;600;700&display=swap" rel="stylesheet">
<style>
  :root {{
    --blue:#00356b; --gold:#BD9B60; --ink:#23201a; --muted:#6f6754;
    --parchment:#f4efe1; --card:#fdfbf6; --line:#e3dbc7;
  }}
  * {{ box-sizing:border-box; }}
  body {{ font-family:'DM Sans',system-ui,sans-serif; color:var(--ink);
          margin:0; padding:0 0 3rem; background:var(--parchment); }}
  .masthead {{ background:var(--blue); border-bottom:3px solid var(--gold);
               padding:2rem 1rem 1.6rem; }}
  .masthead .inner {{ max-width:1000px; margin:0 auto; }}
  .masthead h1 {{ font-family:'EB Garamond',Georgia,serif; font-weight:500;
                  color:#fff; margin:0; font-size:2.1rem; letter-spacing:.01em; }}
  .masthead .meta {{ color:var(--gold); font-size:.85rem; margin-top:.45rem;
                     letter-spacing:.02em; }}
  .wrap {{ max-width:1000px; margin:0 auto; padding:1.75rem 1rem 0; }}
  .controls {{ display:flex; gap:.5rem; margin-bottom:1.25rem; flex-wrap:wrap; }}
  .controls input {{ flex:1; min-width:220px; padding:.6rem .8rem;
                     border:1px solid var(--line); border-radius:6px;
                     font-family:'DM Sans',sans-serif; font-size:.95rem;
                     background:var(--card); color:var(--ink); }}
  .controls input:focus {{ outline:none; border-color:var(--blue);
                           box-shadow:0 0 0 2px rgba(0,53,107,.12); }}
  .controls button {{ padding:.6rem 1rem; border:1px solid var(--line);
                      border-radius:6px; background:var(--card); cursor:pointer;
                      font-family:'DM Sans',sans-serif; font-size:.9rem;
                      font-weight:500; color:var(--blue); }}
  .controls button.active {{ background:var(--blue); color:#fff; border-color:var(--blue); }}
  table {{ width:100%; border-collapse:collapse; background:var(--card);
           border:1px solid var(--line); border-radius:8px; overflow:hidden;
           box-shadow:0 1px 3px rgba(35,32,26,.06); }}
  th, td {{ text-align:left; padding:.8rem .95rem; border-bottom:1px solid var(--line);
            font-size:.92rem; vertical-align:top; }}
  th {{ background:var(--blue); color:#fff; font-size:.72rem; font-weight:600;
        text-transform:uppercase; letter-spacing:.07em; }}
  tbody tr:nth-child(even) {{ background:rgba(189,155,96,.05); }}
  tr:last-child td {{ border-bottom:none; }}
  td a {{ color:var(--blue); text-decoration:none; font-weight:500; }}
  td a:hover {{ text-decoration:underline; text-decoration-color:var(--gold); }}
  .date {{ color:var(--muted); white-space:nowrap; }}
  .badge {{ display:inline-block; padding:.12rem .55rem; border-radius:3px;
            font-size:.7rem; font-weight:600; letter-spacing:.04em; }}
  .badge.rn {{ background:var(--blue); color:#fff; }}
  .badge.aprn {{ background:var(--gold); color:var(--blue); }}
  .foot {{ max-width:1000px; margin:1.5rem auto 0; padding:1rem 1rem 0;
           border-top:1px solid var(--line); color:var(--muted);
           font-size:.78rem; line-height:1.5; }}
  .foot strong {{ color:var(--blue); }}
</style></head>
<body>
  <header class="masthead"><div class="inner">
    <h1>Connecticut Nursing Jobs</h1>
    <div class="meta">{len(rows)} open positions &middot; {rn_n} RN &middot; {aprn_n} APRN &middot; updated {generated}</div>
  </div></header>
  <div class="wrap">
  <div class="controls">
    <input id="q" type="search" placeholder="Filter by title, location, employer...">
    <button data-f="ALL" class="active">All</button>
    <button data-f="RN">RN</button>
    <button data-f="APRN">APRN</button>
  </div>
  <table><thead><tr>
    <th>Title</th><th>Role</th><th>Employer</th><th>Location</th><th>Posted</th>
  </tr></thead><tbody id="rows">
{chr(10).join(tr)}
  </tbody></table>
  </div>
  <div class="foot">
    <strong>Disclaimer:</strong> This board aggregates publicly available job
    listings from third-party hospital career websites. Yale School of Nursing
    is not affiliated with these employers and is not responsible for the
    content, accuracy, or availability of any third-party website. Listings may
    be outdated, modified, or filled at any time. Students should verify all
    details, including current availability, qualifications, and terms of
    employment, directly with the prospective employer before applying.
  </div>
<script>
  const q = document.getElementById('q');
  const rows = [...document.querySelectorAll('#rows tr')];
  let roleFilter = 'ALL';
  function apply() {{
    const term = q.value.trim().toLowerCase();
    rows.forEach(r => {{
      const matchRole = roleFilter === 'ALL' || r.dataset.role === roleFilter;
      const matchText = !term || r.textContent.toLowerCase().includes(term);
      r.style.display = (matchRole && matchText) ? '' : 'none';
    }});
  }}
  q.addEventListener('input', apply);
  document.querySelectorAll('.controls button').forEach(b => {{
    b.addEventListener('click', () => {{
      document.querySelectorAll('.controls button').forEach(x => x.classList.remove('active'));
      b.classList.add('active');
      roleFilter = b.dataset.f;
      apply();
    }});
  }});
</script>
</body></html>"""

    with open(path, "w", encoding="utf-8") as f:
        f.write(doc)
    return len(rows)


def export_json(conn: sqlite3.Connection, path: str) -> int:
    """Write the active jobs as a JSON feed for the Slate portal page to fetch."""
    rows = _active_recent_rows(conn)

    jobs = [{
        "title": title,
        "role": role,
        "employer": src,
        "location": loc,
        "url": url,
        "posted": posted or (first_seen[:10] if first_seen else ""),
    } for title, role, src, loc, url, posted, first_seen in rows]

    now = dt.datetime.now()
    feed = {
        "generated_at": now.isoformat(timespec="seconds"),
        "generated_display": now.strftime("%B %d, %Y at %I:%M %p"),
        "counts": {
            "total": len(jobs),
            "rn": sum(1 for j in jobs if j["role"] == "RN"),
            "aprn": sum(1 for j in jobs if j["role"] == "APRN"),
        },
        "jobs": jobs,
    }
    with open(path, "w", encoding="utf-8") as f:
        json.dump(feed, f, ensure_ascii=False, indent=2)
    return len(jobs)


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #

def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Aggregate CT RN/APRN job listings.")
    p.add_argument("--refresh", action="store_true", help="pull sources into the DB")
    p.add_argument("--export", action="store_true", help="write the HTML board")
    p.add_argument("--json", action="store_true", help="write the JSON feed (jobs.json)")
    p.add_argument("--source", help="limit refresh to one source key (e.g. ynhh)")
    p.add_argument("--db", default=DB_PATH)
    p.add_argument("--out", default=OUTPUT_HTML)
    p.add_argument("--json-out", default=OUTPUT_JSON)
    p.add_argument("--verbose", action="store_true")
    args = p.parse_args(argv)

    any_flag = args.refresh or args.export or args.json
    # Default with no flags = refresh + HTML export (unchanged behavior).
    do_refresh = args.refresh or not any_flag
    do_export = args.export or not any_flag
    do_json = args.json

    conn = sqlite3.connect(args.db)
    init_db(conn)

    if do_refresh:
        refresh(conn, args.source, args.verbose)
    if do_export:
        n = export_html(conn, args.out)
        print(f"-> wrote {args.out} ({n} active jobs)")
    if do_json:
        n = export_json(conn, args.json_out)
        print(f"-> wrote {args.json_out} ({n} active jobs)")

    conn.close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
