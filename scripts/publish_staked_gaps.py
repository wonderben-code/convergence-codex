#!/usr/bin/env python3
"""Generate PDF for 'The Staked Gaps' and publish it to Zenodo as a NEW deposition.

One-shot. Run once:  ZENODO_TOKEN=<token> python3 scripts/publish_staked_gaps.py
(Or just `python3 scripts/publish_staked_gaps.py` if ZENODO_TOKEN is in your env.)

Creates a NEW Zenodo record (new DOI) — it does NOT touch the capstone's record.
Captures the DOI to papers/the_staked_gaps_2026.zenodo.json.
Template: scripts/publish_tree_of_reality.py.
"""

import json
import os
import re
import sys
from pathlib import Path

import markdown
import requests
from weasyprint import HTML

BASE = "https://zenodo.org/api"

ROOT = Path("/Users/ekramalam/convergence-codex")
MD_PATH = ROOT / "papers" / "the_staked_gaps_2026.md"
PDF_PATH = ROOT / "papers" / "the_staked_gaps_2026.pdf"
RESULT_PATH = ROOT / "papers" / "the_staked_gaps_2026.zenodo.json"

TITLE = ("The Staked Gaps: A Pre-Registered Table of Open Problems and "
         "Predicted Solutions for the Tree of Reality")
PUBLICATION_DATE = "2026-10-13"
CAPSTONE_DOI = "10.5281/zenodo.23011897"
RELATED_REPO = "https://github.com/wonderben-code/convergence-codex"

KEYWORDS = [
    "theory of everything",
    "open problems",
    "pre-registration",
    "falsifiable predictions",
    "Mendeleev prediction",
    "Tree of Reality",
    "noncommutative geometry",
    "Yang-Mills mass gap",
    "spectral action",
    "unbounded operators",
    "automated theorem proving",
    "machine-verified mathematics",
    "Bitcoin timestamping",
]

DESCRIPTION_NOTE = (
    "Companion to The Tree of Reality (DOI 10.5281/zenodo.23011897). Publishes the "
    "theory's incompleteness as content: each named gap (the two open links and the "
    "hardest partial residues) is located to an exact failing step and given OUR "
    "predicted shape of its solution, calibrated by how tightly the framework "
    "determines it — a single pinned shape, a small bounded set of candidates, or a "
    "flagged direction — together with the result that would refute the theory at that "
    "site. A second, staked prediction forecasts that these gaps will be closed soon, "
    "in the shapes and gated order given, by advancing automated reasoning, human-machine "
    "teams, or the authors. The predictions sharpen those first registered in the capstone "
    "(28 September 2026); both the capstone registration and this paper are dated and "
    "Bitcoin-anchored, and the 6 October 2026 frontier-model mathematics release is "
    "discussed as a dated, honestly-caveated data point on the meta-prediction."
)

REFERENCES = [
    "Mala, M. E. (2026). The Tree of Reality: An Evolutionary Theory of Everything. DOI: 10.5281/zenodo.23011897.",
    "Mala, M. E. (2026). How to Grow a Universe (the lay account).",
    "Lawvere, F. W. (1969). Diagonal arguments and Cartesian closed categories.",
    "Chamseddine, A. H., Connes, A. and Marcolli, M. (2007). Gravity and the Standard Model with neutrino mixing. Adv. Theor. Math. Phys.",
    "Osterwalder, K. and Schrader, R. (1973, 1975). Axioms for Euclidean Green's functions.",
]

# ─── PDF styling (from the capstone publisher) ──────────────────────────

CSS = """
@page { size: A4; margin: 2.4cm 2cm;
    @bottom-center { content: counter(page); font-family: 'Georgia', serif; font-size: 10pt; color: #666; } }
body { font-family: 'Georgia', 'Times New Roman', serif; font-size: 11pt; line-height: 1.55; color: #1a1a1a; }
h1 { font-size: 21pt; margin: 0 0 4pt 0; color: #111; page-break-after: avoid; }
h1 + p em { color: #555; font-size: 12pt; }
h2 { font-size: 15pt; margin: 26pt 0 8pt 0; color: #222; border-bottom: 1px solid #ccc; padding-bottom: 4pt; page-break-after: avoid; }
h3 { font-size: 12.5pt; margin: 18pt 0 6pt 0; color: #333; page-break-after: avoid; }
p { margin: 0 0 8pt 0; text-align: justify; }
strong { color: #111; } em { font-style: italic; }
hr { border: none; border-top: 1px solid #ddd; margin: 18pt 0; }
table { width: 100%; border-collapse: collapse; margin: 10pt 0; font-size: 9.5pt; page-break-inside: avoid; }
thead { background: #f5f5f5; }
th { border: 1px solid #999; padding: 5pt 7pt; text-align: left; font-weight: bold; }
td { border: 1px solid #ccc; padding: 4pt 7pt; text-align: left; }
tr:nth-child(even) td { background: #fafafa; }
ul, ol { margin: 4pt 0 8pt 0; padding-left: 20pt; } li { margin-bottom: 4pt; }
code { font-family: 'Menlo', 'Courier New', monospace; font-size: 9.5pt; background: #f4f4f4; padding: 1pt 3pt; border-radius: 2pt; }
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
    html_body = markdown.markdown(
        body,
        extensions=["tables", "fenced_code", "smarty", "sane_lists"],
        extension_configs={"smarty": {"smart_angled_quotes": True}},
    )
    html_full = (
        "<!DOCTYPE html><html><head><meta charset=\"utf-8\">"
        f"<style>{CSS}</style></head><body>{html_body}</body></html>"
    )
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
        "<p><strong>The Staked Gaps.</strong> A pre-registered table of open problems and "
        "predicted solutions for the Tree of Reality.</p>"
        f"<p>{DESCRIPTION_NOTE}</p>"
        "<p>Independent research, AI-collaborative, not peer-reviewed. Read in that light. "
        "Verify what catches your eye. Challenge what you doubt.</p>"
    )

    print("Creating deposition (NEW record — does not touch the capstone)...")
    r = requests.post(f"{BASE}/deposit/depositions", json={},
                      headers={**headers, "Content-Type": "application/json"}, timeout=60)
    r.raise_for_status()
    dep = r.json()
    dep_id = dep["id"]
    bucket = dep["links"]["bucket"]
    print(f"  Deposition ID: {dep_id}")

    for p in (pdf_path, MD_PATH):
        print(f"Uploading {p.name} ({p.stat().st_size // 1024} KB)...")
        with p.open("rb") as f:
            r = requests.put(f"{bucket}/{p.name}", data=f,
                             headers={**headers, "Content-Type": "application/octet-stream"}, timeout=120)
        r.raise_for_status()

    print("Setting metadata...")
    metadata = {"metadata": {
        "title": TITLE,
        "upload_type": "publication",
        "publication_type": "preprint",
        "description": description_html,
        "creators": [{"name": "Mala, Mark E.", "orcid": "0009-0007-8760-5553",
                      "affiliation": "Independent Researcher"}],
        "keywords": KEYWORDS,
        "publication_date": PUBLICATION_DATE,
        "license": "cc-by-4.0",
        "language": "eng",
        "version": "v1",
        "access_right": "open",
        "notes": ("Copyright (C) 2026 Mark E. Mala. Companion to The Tree of Reality for the "
                  "Convergence Codex programme (infinitography.com). Bitcoin-timestamped via "
                  "wonderben-code/convergence-codex. Predictions first registered in the capstone, "
                  "28 September 2026."),
        "related_identifiers": [
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
    return {
        "deposition_id": dep_id,
        "doi": result.get("doi"),
        "concept_doi": result.get("conceptdoi"),
        "record_url": result.get("links", {}).get("record_html"),
        "doi_url": result.get("links", {}).get("doi"),
    }


def main():
    print("=" * 60)
    print("PUBLISH — The Staked Gaps")
    print("=" * 60)
    build_pdf(MD_PATH, PDF_PATH)
    info = upload_to_zenodo(PDF_PATH)
    print("\nPUBLISHED.")
    for k, v in info.items():
        print(f"  {k}: {v}")
    RESULT_PATH.write_text(json.dumps(info, indent=2))
    print(f"\nResult saved: {RESULT_PATH}")


if __name__ == "__main__":
    main()
