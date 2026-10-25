#!/usr/bin/env python3
"""Publish version 2 of 'The Staked Gaps' to Zenodo as a NEW VERSION of the existing record.

One-shot:  ZENODO_TOKEN=<token> python3 scripts/publish_staked_gaps_v2.py
Creates a new version under concept DOI 10.5281/zenodo.23338725 (record 23338726 stays as v1).
PDF built from papers/the_staked_gaps_2026.md (v1 text unchanged + appended addendum).
Template: scripts/publish_staked_gaps.py / publish_refined_gaps.py.
"""

import json
import os
from pathlib import Path

import markdown
import requests
from weasyprint import HTML

BASE = "https://zenodo.org/api"
ROOT = Path("/Users/ekramalam/convergence-codex")
MD_PATH = ROOT / "papers" / "the_staked_gaps_2026.md"
PDF_PATH = ROOT / "papers" / "the_staked_gaps_2026.pdf"
RESULT_PATH = ROOT / "papers" / "the_staked_gaps_2026.v2.zenodo.json"
V1_DEPOSITION_ID = 23338726
V2_DATE = "2026-10-25"

ADDENDUM_NOTE = (
    "VERSION 2 (25 October 2026). The v1 text (13 October 2026) is unchanged; an addendum is appended, "
    "keeping Section 8's commitment to record under this paper's own DOI lineage whenever something "
    "arrives that bears on the staked predictions. Ten days after v1, A. D. Wissner-Gross released Chain "
    "Theory (23 October 2026), an independent Lean-checked programme deriving Standard-Model structure "
    "from finitely many entangled finite-dimensional systems. The addendum records precisely what that "
    "release does for the staked predictions: the six headline gaps G1-G6 received no candidates; the "
    "box-level openings L14 (three generations), L23 (mass gap), L21 (Born rule) and L9 (signature) "
    "received candidate mechanisms at Chain Theory's own conditional grade; the pre-registered "
    "trichotomy returned 'extends the walked branch'; one computation (Chain Theory's 172-record count "
    "realised inside the Tree's M_16) is reported; ten joint tests are pre-registered; caveats on both "
    "programmes are stated. No grade changes. The successor paper, The Refined Gaps (2026), takes the "
    "candidates as given and states the sharper residual predictions."
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
table { border-collapse: collapse; width: 100%; font-size: 9pt; margin: 8pt 0 12pt 0; }
th, td { border: 1px solid #ccc; padding: 3pt 5pt; vertical-align: top; text-align: left; }
th { background: #f0f0f0; } tr { page-break-inside: avoid; }
"""


def build_pdf(md_path: Path, pdf_path: Path) -> None:
    body = md_path.read_text()
    html_body = markdown.markdown(body, extensions=["tables", "fenced_code", "smarty", "sane_lists"],
                                  extension_configs={"smarty": {"smart_angled_quotes": True}})
    html_full = f"<!DOCTYPE html><html><head><meta charset=\"utf-8\"><style>{CSS}</style></head><body>{html_body}</body></html>"
    HTML(string=html_full).write_pdf(str(pdf_path))
    print(f"PDF written: {pdf_path} ({pdf_path.stat().st_size // 1024} KB)")


def _headers():
    token = os.environ.get("ZENODO_TOKEN", "")
    if not token:
        raise SystemExit("ZENODO_TOKEN not set — export it before running (see your memory file).")
    return {"Authorization": f"Bearer {token}"}


def publish_new_version(pdf_path: Path) -> dict:
    H = _headers(); HJ = {**H, "Content-Type": "application/json"}
    print(f"Creating new version of deposition {V1_DEPOSITION_ID}...")
    r = requests.post(f"{BASE}/deposit/depositions/{V1_DEPOSITION_ID}/actions/newversion", headers=H, timeout=60)
    if r.status_code not in (200, 201):
        print("newversion error:", r.status_code, r.text[:800]); r.raise_for_status()
    latest_draft = r.json()["links"]["latest_draft"]
    r = requests.get(latest_draft, headers=H, timeout=60); r.raise_for_status()
    draft = r.json(); new_id = draft["id"]; bucket = draft["links"]["bucket"]
    print(f"  New draft deposition ID: {new_id}")
    # remove files inherited from v1
    for f in draft.get("files", []):
        print(f"  removing inherited file {f['filename']}")
        rd = requests.delete(f"{BASE}/deposit/depositions/{new_id}/files/{f['id']}", headers=H, timeout=60)
        if rd.status_code not in (204, 200):
            print("  delete warning:", rd.status_code, rd.text[:300])
    for p in (pdf_path, MD_PATH):
        print(f"Uploading {p.name} ({p.stat().st_size // 1024} KB)...")
        with p.open("rb") as fh:
            ru = requests.put(f"{bucket}/{p.name}", data=fh, headers={**H, "Content-Type": "application/octet-stream"}, timeout=180)
        ru.raise_for_status()
    # metadata: inherit v1's, update version/date/description/notes
    md = draft["metadata"]
    md["version"] = "v2"
    md["publication_date"] = V2_DATE
    desc = md.get("description", "")
    if "VERSION 2 (25 October 2026)" not in desc:
        md["description"] = desc + f"<p><strong>{ADDENDUM_NOTE}</strong></p>"
    md["notes"] = (md.get("notes", "") + " Version 2 (25 Oct 2026) appends the first addendum: candidates "
                   "from Chain Theory (A. D. Wissner-Gross, 23 Oct 2026), cited at its own grades.").strip()
    rel = md.get("related_identifiers", [])
    for ident in ("https://alexwg.org/publications/ChainTheoryAlpha.pdf",
                  "https://alexwg.org/publications/ChainTheoryCompendium.pdf"):
        if not any(x.get("identifier") == ident for x in rel):
            rel.append({"identifier": ident, "relation": "references", "scheme": "url"})
    md["related_identifiers"] = rel
    refs = md.get("references", [])
    for ref in ("Wissner-Gross, A. D. (2026). A Parameter-Free Candidate for the Fine-Structure Constant from Entangled Qudits. alexwg.org/publications/ChainTheoryAlpha.pdf",
                "Wissner-Gross, A. D. (2026). Chain Theory: Toward Fundamental Physics from Distilling Networks of Entangled Qudits, working draft release 0.1. alexwg.org/publications/ChainTheoryCompendium.pdf",
                "Mala, M. E. (2026). The Refined Gaps. Convergence Codex programme."):
        if ref not in refs:
            refs.append(ref)
    md["references"] = refs
    # Zenodo rejects some read-only keys on PUT; keep the standard editable set
    keep = {"title", "upload_type", "publication_type", "description", "creators", "keywords", "publication_date",
            "license", "language", "version", "access_right", "notes", "related_identifiers", "references"}
    md = {k: v for k, v in md.items() if k in keep}
    print("Setting metadata (v2)...")
    r = requests.put(f"{BASE}/deposit/depositions/{new_id}", json={"metadata": md}, headers=HJ, timeout=60)
    if r.status_code != 200:
        print("Metadata error:", r.status_code, r.text[:1200]); r.raise_for_status()
    print("Publishing v2...")
    r = requests.post(f"{BASE}/deposit/depositions/{new_id}/actions/publish", headers=H, timeout=60)
    if r.status_code != 202:
        print("Publish error:", r.status_code, r.text[:1200]); r.raise_for_status()
    res = r.json()
    return {"deposition_id": new_id, "version": "v2", "doi": res.get("doi"), "concept_doi": res.get("conceptdoi"),
            "record_url": res.get("links", {}).get("record_html"), "doi_url": res.get("links", {}).get("doi")}


def main():
    print("=" * 60); print("PUBLISH — The Staked Gaps, version 2"); print("=" * 60)
    build_pdf(MD_PATH, PDF_PATH)
    if os.environ.get("PDF_ONLY"):
        print("PDF_ONLY set — not publishing."); return
    info = publish_new_version(PDF_PATH)
    print("\nPUBLISHED v2.")
    for k, v in info.items():
        print(f"  {k}: {v}")
    RESULT_PATH.write_text(json.dumps(info, indent=2))
    print(f"\nResult saved: {RESULT_PATH}")


if __name__ == "__main__":
    main()
