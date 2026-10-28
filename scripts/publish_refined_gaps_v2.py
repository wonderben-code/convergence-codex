#!/usr/bin/env python3
"""Publish version 2 of 'The Refined Gaps' to Zenodo as a NEW VERSION of the existing record.

Three explicit stages, so nothing is published by accident:
  STAGE=draft    python3 scripts/publish_refined_gaps_v2.py   # create the new-version draft, print its reserved DOI
  STAGE=upload   python3 scripts/publish_refined_gaps_v2.py   # build the PDF, upload PDF + .md, set metadata (draft stays a draft)
  STAGE=publish  python3 scripts/publish_refined_gaps_v2.py   # publish the draft (mints the DOI; irreversible)
PDF_ONLY=1 builds the PDF and stops. Concept DOI 10.5281/zenodo.23637018; record 23637019 stays as v1.
Token: ZENODO_TOKEN from the environment (never printed or written anywhere).
Template: scripts/publish_staked_gaps_v2.py.
"""

import json
import os
import time
from pathlib import Path

import markdown
import requests
from weasyprint import HTML

BASE = "https://zenodo.org/api"
ROOT = Path("/Users/ekramalam/convergence-codex")
MD_PATH = ROOT / "papers" / "the_refined_gaps_2026.md"
PDF_PATH = ROOT / "papers" / "the_refined_gaps_2026.pdf"
RESULT_PATH = ROOT / "papers" / "the_refined_gaps_2026.v2.zenodo.json"
STATE_PATH = Path(os.environ.get("STATE_PATH", "/tmp/refined_gaps_v2_draft.json"))
V1_DEPOSITION_ID = 23637019
V2_DATE = "2026-10-28"

ADDENDUM_NOTE = (
    "VERSION 2 (28 October 2026). The v1 text (25 October 2026) is unchanged; an addendum is appended that "
    "scores the tests run since v1 against the pre-registered table (Section 7) and kill-conditions "
    "(Section 8). R1 (the three-generation bound on M4) holds in a re-posed form, as Lean theorems about frames "
    "of M4 and M3; R2 (Chain Theory's attach sites are the quaternions i, j, k) is refuted, with a Lean proof "
    "that no quaternion action exists on a three-dimensional generation space, and recorded under Section 8 "
    "as a refutation at the L14 site conditional on Chain Theory's own open result 197.5; R3 (the read cap) is "
    "confirmed in its bimodule shape and refuted in its Dirac-operator shape; R9' (parity at M16) is answered "
    "and L12 is re-posed as two choices; R11 is consistent and Chain Theory's Conjecture 0 narrows L11 from four "
    "alternatives to two. A test not on the list found a correction of the Tree's own: read as a physical "
    "boundary condition with Standard-Model running, the L15 Higgs coupling window excludes the measured Higgs "
    "mass (it requires about 131-176 GeV), the known tension of the spectral Standard Model. No grade changes "
    "(6 GENUINE, 13 PARTIAL, 3 POSTULATE, 2 OPEN). New pre-registered predictions R13-R16 (the sigma field; the "
    "Higgs cells; where the generations live; the read cap through the vacuum) are stated for v3."
)

CSS = """
@page { size: A4; margin: 2.4cm 2cm;
    @bottom-center { content: counter(page); font-family: 'Georgia', serif; font-size: 10pt; color: #666; } }
body { font-family: 'Georgia', 'Arial Unicode MS', 'Noto Sans', 'Times New Roman', serif; font-size: 11pt; line-height: 1.55; color: #1a1a1a; }
h1 { font-size: 21pt; margin: 0 0 4pt 0; color: #111; page-break-after: avoid; }
h1 + h3 { color: #555; font-size: 12.5pt; font-weight: normal; margin-top: 0; }
h2 { font-size: 15pt; margin: 26pt 0 8pt 0; color: #222; border-bottom: 1px solid #ccc; padding-bottom: 4pt; page-break-after: avoid; }
h3 { font-size: 12.5pt; margin: 18pt 0 6pt 0; color: #333; page-break-after: avoid; }
p { margin: 0 0 8pt 0; text-align: justify; }
strong { color: #111; } em { font-style: italic; }
hr { border: none; border-top: 1px solid #ddd; margin: 18pt 0; }
ul, ol { margin: 4pt 0 8pt 0; padding-left: 20pt; } li { margin-bottom: 4pt; }
code { font-family: 'Menlo', 'Arial Unicode MS', 'Courier New', monospace; font-size: 9pt; background: #f4f4f4; padding: 1pt 3pt; border-radius: 2pt; }
blockquote { border-left: 3pt solid #999; margin: 10pt 0; padding: 4pt 14pt; color: #333; font-style: italic; }
a { color: #1a4a8a; text-decoration: none; }
table { border-collapse: collapse; width: 100%; font-size: 8.5pt; margin: 8pt 0 12pt 0; }
th, td { border: 1px solid #ccc; padding: 3pt 5pt; vertical-align: top; text-align: left; }
th { background: #f0f0f0; } tr { page-break-inside: avoid; }
"""


def build_pdf() -> None:
    body = MD_PATH.read_text()
    assert "{{V2_DOI}}" not in body, "fill the reserved DOI into the header before building"
    html_body = markdown.markdown(body, extensions=["tables", "fenced_code", "smarty", "sane_lists"],
                                  extension_configs={"smarty": {"smart_angled_quotes": True}})
    html_full = f"<!DOCTYPE html><html><head><meta charset=\"utf-8\"><style>{CSS}</style></head><body>{html_body}</body></html>"
    HTML(string=html_full).write_pdf(str(PDF_PATH))
    print(f"PDF written: {PDF_PATH} ({PDF_PATH.stat().st_size // 1024} KB)")


def _headers():
    token = os.environ.get("ZENODO_TOKEN", "")
    if not token:
        raise SystemExit("ZENODO_TOKEN not set.")
    return {"Authorization": f"Bearer {token}"}


def _req(method, url, retries=5, **kw):
    for attempt in range(1, retries + 1):
        try:
            r = requests.request(method, url, timeout=kw.pop("timeout", (30, 300)), **kw)
            if r.status_code >= 500:
                raise requests.HTTPError(f"{r.status_code}")
            return r
        except (requests.ConnectionError, requests.Timeout, requests.HTTPError) as e:
            print(f"  retry {method} after attempt {attempt}: {type(e).__name__} {e}")
            time.sleep(8 * attempt)
    raise SystemExit(f"{method} {url} failed after {retries} attempts")


def stage_draft():
    H = _headers()
    r = _req("POST", f"{BASE}/deposit/depositions/{V1_DEPOSITION_ID}/actions/newversion", headers=H)
    if r.status_code not in (200, 201):
        raise SystemExit(f"newversion error {r.status_code}: {r.text[:800]}")
    draft = _req("GET", r.json()["links"]["latest_draft"], headers=H).json()
    if not draft.get("metadata", {}).get("prereserve_doi"):
        rr = _req("PUT", f"{BASE}/deposit/depositions/{draft['id']}", headers={**H, "Content-Type": "application/json"},
                  data=json.dumps({"metadata": {**{k: v for k, v in draft["metadata"].items() if k in
                                                   ("title", "upload_type", "publication_type", "description", "creators")},
                                                "prereserve_doi": True}}))
        draft = rr.json() if rr.status_code == 200 else draft
    state = {"draft_id": draft["id"], "reserved_doi": draft["metadata"].get("prereserve_doi", {}).get("doi"),
             "web": f"https://zenodo.org/uploads/{draft['id']}", "submitted": draft.get("submitted")}
    STATE_PATH.write_text(json.dumps(state, indent=2))
    print(json.dumps(state, indent=2))


def stage_upload():
    H = _headers(); HJ = {**H, "Content-Type": "application/json"}
    state = json.loads(STATE_PATH.read_text()); new_id = state["draft_id"]
    build_pdf()
    draft = _req("GET", f"{BASE}/deposit/depositions/{new_id}", headers=H).json()
    if draft.get("submitted"):
        raise SystemExit("draft already published — refusing to modify")
    bucket = draft["links"]["bucket"]
    for f in draft.get("files", []):
        print(f"  removing inherited file {f['filename']}")
        _req("DELETE", f"{BASE}/deposit/depositions/{new_id}/files/{f['id']}", headers=H)
    for p in (PDF_PATH, MD_PATH):
        print(f"Uploading {p.name} ({p.stat().st_size // 1024} KB)...")
        ru = _req("PUT", f"{bucket}/{p.name}", data=p.read_bytes(), headers={**H, "Content-Type": "application/octet-stream"})
        ru.raise_for_status()
    md = draft["metadata"]
    md["version"] = "v2"
    md["publication_date"] = V2_DATE
    desc = md.get("description", "")
    if "VERSION 2 (28 October 2026)" not in desc:
        md["description"] = desc + f"<p><strong>{ADDENDUM_NOTE}</strong></p>"
    md["notes"] = (md.get("notes", "") + " Version 2 (28 Oct 2026) appends an addendum scoring the pre-registered "
                   "residuals (R1-R12) and records a correction of the Tree's L15 Higgs window against the measured Higgs mass.").strip()
    rel = md.get("related_identifiers", [])
    for ident in ("https://github.com/wonderben-code/convergence-codex/tree/main/lean_verify/chain_theory",
                  "https://github.com/wonderben-code/convergence-codex/tree/main/scripts/chain_theory"):
        if not any(x.get("identifier") == ident for x in rel):
            rel.append({"identifier": ident, "relation": "isSupplementedBy", "scheme": "url"})
    md["related_identifiers"] = rel
    refs = md.get("references", [])
    for ref in ("Buttazzo, D. et al. (2013). Investigating the near-criticality of the Higgs boson. JHEP 12, 089.",
                "Chamseddine, A. H. and Connes, A. (2012). Resilience of the spectral standard model. JHEP 09, 104.",
                "Chamseddine, A. H., Connes, A. and van Suijlekom, W. D. (2013). Beyond the spectral standard model: emergence of Pati-Salam unification. JHEP 11, 132.",
                "Horodecki, P. (1997). Separability criterion and inseparable mixed states with positive partial transposition. Phys. Lett. A 232, 333."):
        if ref not in refs:
            refs.append(ref)
    md["references"] = refs
    keep = {"title", "upload_type", "publication_type", "description", "creators", "keywords", "publication_date",
            "license", "language", "version", "access_right", "notes", "related_identifiers", "references", "prereserve_doi"}
    md = {k: v for k, v in md.items() if k in keep}
    r = _req("PUT", f"{BASE}/deposit/depositions/{new_id}", json={"metadata": md}, headers=HJ)
    if r.status_code != 200:
        raise SystemExit(f"Metadata error {r.status_code}: {r.text[:1200]}")
    d = _req("GET", f"{BASE}/deposit/depositions/{new_id}", headers=H).json()
    print("DRAFT READY (not published)")
    print("  files:", sorted(x["filename"] for x in d.get("files", [])))
    print("  title:", d["metadata"].get("title"))
    print("  version:", d["metadata"].get("version"), "| date:", d["metadata"].get("publication_date"))
    print("  reserved DOI:", d["metadata"].get("prereserve_doi", {}).get("doi"))
    print("  state:", d.get("state"), "| submitted:", d.get("submitted"))
    print("  web:", f"https://zenodo.org/uploads/{new_id}")


def stage_publish():
    H = _headers()
    state = json.loads(STATE_PATH.read_text()); new_id = state["draft_id"]
    d = _req("GET", f"{BASE}/deposit/depositions/{new_id}", headers=H).json()
    if not d.get("submitted"):
        r = _req("POST", f"{BASE}/deposit/depositions/{new_id}/actions/publish", headers=H)
        if r.status_code != 202:
            d2 = _req("GET", f"{BASE}/deposit/depositions/{new_id}", headers=H).json()
            if not d2.get("submitted"):
                raise SystemExit(f"Publish error {r.status_code}: {r.text[:1200]}")
        d = _req("GET", f"{BASE}/deposit/depositions/{new_id}", headers=H).json()
    info = {"deposition_id": new_id, "version": "v2", "doi": d.get("doi"), "concept_doi": d.get("conceptdoi"),
            "record_url": d.get("links", {}).get("record_html") or f"https://zenodo.org/records/{new_id}",
            "doi_url": d.get("links", {}).get("doi")}
    RESULT_PATH.write_text(json.dumps(info, indent=2))
    print("PUBLISHED v2"); print(json.dumps(info, indent=2))


if __name__ == "__main__":
    if os.environ.get("PDF_ONLY"):
        build_pdf()
    else:
        {"draft": stage_draft, "upload": stage_upload, "publish": stage_publish}[os.environ["STAGE"]]()
