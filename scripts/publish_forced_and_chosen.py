#!/usr/bin/env python3
"""Generate PDF for 'The Forced and the Chosen' and publish it to Zenodo as a NEW deposition.

One-shot:  ZENODO_TOKEN=<token> python3 scripts/publish_forced_and_chosen.py
Creates a NEW Zenodo record (new DOI) — does NOT touch any existing record.
Template: scripts/publish_staked_gaps.py.
"""

import json
import os
import re
from pathlib import Path

import markdown
import requests
from weasyprint import HTML

BASE = "https://zenodo.org/api"

ROOT = Path("/Users/ekramalam/convergence-codex")
MD_PATH = ROOT / "papers" / "the_forced_and_the_chosen_2026.md"
PDF_PATH = ROOT / "papers" / "the_forced_and_the_chosen_2026.pdf"
RESULT_PATH = ROOT / "papers" / "the_forced_and_the_chosen_2026.zenodo.json"

TITLE = ("The Forced and the Chosen: The Tree of Reality's Declared Inputs, "
         "and the Plenitude of its Branches")
PUBLICATION_DATE = "2026-10-14"
GAPS_DOI = "10.5281/zenodo.23338726"
CAPSTONE_DOI = "10.5281/zenodo.23011897"
RELATED_REPO = "https://github.com/wonderben-code/convergence-codex"

KEYWORDS = [
    "theory of everything",
    "pre-registration",
    "plenitude",
    "modal realism",
    "sibling branches",
    "Tree of Reality",
    "tree of life",
    "noncommutative geometry",
    "three generations",
    "falsifiable predictions",
    "Bitcoin timestamping",
]

DESCRIPTION_NOTE = (
    "Companion to The Staked Gaps (DOI 10.5281/zenodo.23338726) and The Tree of Reality "
    "(DOI 10.5281/zenodo.23011897). Where The Staked Gaps pre-registered the theory's open "
    "problems, this paper pre-registers its DECLARED CHOICES, in three honest classes: "
    "(1) derivable postulates we predict the mathematics will force (POSTULATE to GENUINE); "
    "(2) proven forks that stay branches (the tree-of-life feature, machine-checked to admit "
    "coherent alternatives); and (3) PLENITUDE — the prediction that at every genuine fork all "
    "coherent branches are realised ('all that can be, becomes'), staked at its honest "
    "conjectural tier. Two distinctions are kept sharp so the bold claim stays rigorous: a "
    "convention (chirality) is not a new world, and a completeness-question (a possible fourth "
    "lineage) is not an alternative branch. The branches are predictions not yet computed; "
    "computing them is the sequel (Tree v2)."
)

REFERENCES = [
    "Mala, M. E. (2026). The Staked Gaps. DOI: 10.5281/zenodo.23338726.",
    "Mala, M. E. (2026). The Tree of Reality: An Evolutionary Theory of Everything. DOI: 10.5281/zenodo.23011897.",
    "Mala, M. E. (2026). The Infinite Ground (origin of the plenitude conjecture).",
    "Lawvere, F. W. (1969). Diagonal arguments and cartesian closed categories.",
    "Chamseddine, A. H., Connes, A. and Marcolli, M. (2007). Gravity and the Standard Model with neutrino mixing. Adv. Theor. Math. Phys.",
]

CSS = """
@page { size: A4; margin: 2.4cm 2cm;
    @bottom-center { content: counter(page); font-family: 'Georgia', serif; font-size: 10pt; color: #666; } }
body { font-family: 'Georgia', 'Arial Unicode MS', 'Noto Sans', 'Times New Roman', serif; font-size: 11pt; line-height: 1.55; color: #1a1a1a; }
h1 { font-size: 21pt; margin: 0 0 4pt 0; color: #111; page-break-after: avoid; }
h1 + p em { color: #555; font-size: 12pt; }
h2 { font-size: 15pt; margin: 26pt 0 8pt 0; color: #222; border-bottom: 1px solid #ccc; padding-bottom: 4pt; page-break-after: avoid; }
h3 { font-size: 12.5pt; margin: 18pt 0 6pt 0; color: #333; page-break-after: avoid; }
p { margin: 0 0 8pt 0; text-align: justify; }
strong { color: #111; } em { font-style: italic; }
hr { border: none; border-top: 1px solid #ddd; margin: 18pt 0; }
ul, ol { margin: 4pt 0 8pt 0; padding-left: 20pt; } li { margin-bottom: 4pt; }
code { font-family: 'Menlo', 'Arial Unicode MS', 'Courier New', monospace; font-size: 9.5pt; background: #f4f4f4; padding: 1pt 3pt; border-radius: 2pt; }
blockquote { border-left: 3pt solid #999; margin: 10pt 0; padding: 4pt 14pt; color: #333; font-style: italic; }
a { color: #1a4a8a; text-decoration: none; }
"""


def strip_frontmatter(md_text: str):
    if not md_text.startswith("---\n"):
        return md_text
    end = md_text.find("\n---\n", 4)
    return md_text if end < 0 else md_text[end + 5:]


def build_pdf(md_path: Path, pdf_path: Path) -> None:
    body = strip_frontmatter(md_path.read_text())
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


def upload_to_zenodo(pdf_path: Path) -> dict:
    headers = _headers()
    description_html = (
        "<p><strong>The Forced and the Chosen.</strong> The Tree of Reality's declared inputs, "
        "and the plenitude of its branches.</p>"
        f"<p>{DESCRIPTION_NOTE}</p>"
        "<p>Independent research, AI-collaborative, not peer-reviewed. Read in that light. "
        "Verify what catches your eye. Challenge what you doubt.</p>"
    )
    print("Creating deposition (NEW record)...")
    r = requests.post(f"{BASE}/deposit/depositions", json={},
                      headers={**headers, "Content-Type": "application/json"}, timeout=60)
    r.raise_for_status()
    dep = r.json(); dep_id = dep["id"]; bucket = dep["links"]["bucket"]
    print(f"  Deposition ID: {dep_id}")
    for p in (pdf_path, MD_PATH):
        print(f"Uploading {p.name} ({p.stat().st_size // 1024} KB)...")
        with p.open("rb") as f:
            r = requests.put(f"{bucket}/{p.name}", data=f,
                             headers={**headers, "Content-Type": "application/octet-stream"}, timeout=120)
        r.raise_for_status()
    print("Setting metadata...")
    metadata = {"metadata": {
        "title": TITLE, "upload_type": "publication", "publication_type": "preprint",
        "description": description_html,
        "creators": [{"name": "Mala, Mark E.", "orcid": "0009-0007-8760-5553", "affiliation": "Independent Researcher"}],
        "keywords": KEYWORDS, "publication_date": PUBLICATION_DATE, "license": "cc-by-4.0",
        "language": "eng", "version": "v1", "access_right": "open",
        "notes": ("Copyright (C) 2026 Mark E. Mala. Companion to The Staked Gaps and The Tree of Reality "
                  "for the Convergence Codex programme (infinitography.com). Bitcoin-timestamped via "
                  "wonderben-code/convergence-codex."),
        "related_identifiers": [
            {"identifier": GAPS_DOI, "relation": "isSupplementTo", "scheme": "doi"},
            {"identifier": CAPSTONE_DOI, "relation": "isSupplementTo", "scheme": "doi"},
            {"identifier": RELATED_REPO, "relation": "isSupplementedBy", "scheme": "url"},
        ],
        "references": REFERENCES,
    }}
    r = requests.put(f"{BASE}/deposit/depositions/{dep_id}", json=metadata,
                     headers={**headers, "Content-Type": "application/json"}, timeout=60)
    if r.status_code != 200:
        print("Metadata error:", r.status_code, r.text[:1000]); r.raise_for_status()
    print("Publishing...")
    r = requests.post(f"{BASE}/deposit/depositions/{dep_id}/actions/publish", headers=headers, timeout=60)
    if r.status_code != 202:
        print("Publish error:", r.status_code, r.text[:1000]); r.raise_for_status()
    result = r.json()
    return {"deposition_id": dep_id, "doi": result.get("doi"),
            "concept_doi": result.get("conceptdoi"),
            "record_url": result.get("links", {}).get("record_html"),
            "doi_url": result.get("links", {}).get("doi")}


def main():
    print("=" * 60); print("PUBLISH — The Forced and the Chosen"); print("=" * 60)
    build_pdf(MD_PATH, PDF_PATH)
    info = upload_to_zenodo(PDF_PATH)
    print("\nPUBLISHED.")
    for k, v in info.items():
        print(f"  {k}: {v}")
    RESULT_PATH.write_text(json.dumps(info, indent=2))
    print(f"\nResult saved: {RESULT_PATH}")


if __name__ == "__main__":
    main()
