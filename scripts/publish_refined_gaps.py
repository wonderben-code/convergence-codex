#!/usr/bin/env python3
"""Generate PDF for 'The Refined Gaps' and publish it to Zenodo as a NEW deposition.

One-shot:  ZENODO_TOKEN=<token> python3 scripts/publish_refined_gaps.py
Creates a NEW Zenodo record (new DOI) — does NOT touch any existing record.
Template: scripts/publish_forced_and_chosen.py.
"""

import json
import os
from pathlib import Path

import markdown
import requests
from weasyprint import HTML

BASE = "https://zenodo.org/api"

ROOT = Path("/Users/ekramalam/convergence-codex")
MD_PATH = ROOT / "papers" / "the_refined_gaps_2026.md"
PDF_PATH = ROOT / "papers" / "the_refined_gaps_2026.pdf"
RESULT_PATH = ROOT / "papers" / "the_refined_gaps_2026.zenodo.json"

TITLE = ("The Refined Gaps: What the Tree of Reality's Open Boxes Become if Chain Theory's "
         "Candidates Hold — a Validation of the Posture, and a Sharper Set of Predictions")
PUBLICATION_DATE = "2026-10-25"
GAPS_DOI = "10.5281/zenodo.23338726"
CAPSTONE_DOI = "10.5281/zenodo.23011897"
FORCED_DOI = "10.5281/zenodo.23356221"
RELATED_REPO = "https://github.com/wonderben-code/convergence-codex"
CHAIN_THEORY_ALPHA = "https://alexwg.org/publications/ChainTheoryAlpha.pdf"
CHAIN_THEORY_COMPENDIUM = "https://alexwg.org/publications/ChainTheoryCompendium.pdf"

KEYWORDS = [
    "theory of everything",
    "pre-registration",
    "Chain Theory",
    "Tree of Reality",
    "entangled qudits",
    "noncommutative geometry",
    "spectral action",
    "Standard Model",
    "three generations",
    "fine-structure constant",
    "falsifiable predictions",
    "Lean 4",
    "Bitcoin timestamping",
]

DESCRIPTION_NOTE = (
    "Successor to The Staked Gaps (DOI 10.5281/zenodo.23338726), which published the Tree of Reality's "
    "open problems as pre-registered predictions: where each gap sits, what shape its filler must take, "
    "who would fill it ('advancing AI, human-machine teams, or the authors'), and what would refute the "
    "theory at each site. Ten days later A. D. Wissner-Gross released Chain Theory, an independent, "
    "Lean-checked, graded programme deriving Standard-Model structure from finitely many entangled "
    "finite-dimensional systems. Its objects are built from exactly the three dimensions the Tree forces "
    "(2, 4, 3) and its results land on exactly the residues the Tree named (three generations, "
    "confinement, the Born rule, Lorentzian signature, the three lineages, chirality). The Tree's "
    "pre-registered trichotomy for any newly found structure returned its first verdict: 'extends the "
    "walked branch'. This paper (1) states precisely what that fit validates (the method: forced objects, "
    "located residues, the meta-prediction's agent and timetable) and what it does not (no physical "
    "identification on either side, none of the headline gaps G1-G6, no grade, not the fine-structure "
    "constant); (2) takes each candidate as if correct and shows each gap sharpens into a covered part "
    "and a smaller residual; (3) pre-registers twelve residual predictions R1-R12 with kill-conditions and "
    "the computation or proof that tests each, including four predictions for Chain Theory's own open "
    "items and one joint prediction neither programme could state alone (Chain Theory's particle webs "
    "embed at the Tree's fourth level, M_256, where the Chamseddine-Connes-Marcolli algebra sits). One "
    "new computation: Chain Theory's 172-record count reproduced exactly from its rules and realised "
    "inside the Tree's M_16; the numerator transfers, the third qubit first appears at M_256, and the "
    "count lives in Chain Theory's record space rather than the operator algebra. Chain Theory is cited "
    "throughout at its own grades; its author's corrections will be incorporated in v2."
)

REFERENCES = [
    "Wissner-Gross, A. D. (2026). A Parameter-Free Candidate for the Fine-Structure Constant from Entangled Qudits. alexwg.org/publications/ChainTheoryAlpha.pdf",
    "Wissner-Gross, A. D. (2026). Chain Theory: Toward Fundamental Physics from Distilling Networks of Entangled Qudits, working draft release 0.1. alexwg.org/publications/ChainTheoryCompendium.pdf",
    "Wissner-Gross, A. D. (2026). Chain Theory: An Introduction. alexwg.org/publications/ChainTheoryTalk.pdf",
    "Wissner-Gross, A. D. (2026). ChainAlpha.lean. alexwg.org/publications/ChainAlpha.lean",
    "Mala, M. E. (2026). The Staked Gaps. DOI: 10.5281/zenodo.23338726.",
    "Mala, M. E. (2026). The Tree of Reality: An Evolutionary Theory of Everything. DOI: 10.5281/zenodo.23011897.",
    "Mala, M. E. (2026). The Forced and the Chosen. DOI: 10.5281/zenodo.23356221.",
    "Chamseddine, A. H. and Connes, A. (1997). The spectral action principle. Commun. Math. Phys. 186, 731.",
    "Chamseddine, A. H., Connes, A. and Marcolli, M. (2007). Gravity and the standard model with neutrino mixing. Adv. Theor. Math. Phys. 11, 991.",
    "Baez, J. C. and Huerta, J. (2010). The algebra of grand unified theories. Bull. AMS 47, 483.",
    "Stormer, E. (1963). Acta Math. 110, 233; Woronowicz, S. L. (1976). Rep. Math. Phys. 10, 165; Choi, M.-D. (1975). Linear Algebra Appl. 12, 95.",
    "Lawvere, F. W. (1969). Diagonal arguments and cartesian closed categories.",
]

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
table { border-collapse: collapse; width: 100%; font-size: 9pt; margin: 8pt 0 12pt 0; page-break-inside: auto; }
th, td { border: 1px solid #ccc; padding: 3pt 5pt; vertical-align: top; text-align: left; }
th { background: #f0f0f0; }
tr { page-break-inside: avoid; }
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


def upload_to_zenodo(pdf_path: Path) -> dict:
    headers = _headers()
    description_html = (
        "<p><strong>The Refined Gaps.</strong> What the Tree of Reality's open boxes become if Chain "
        "Theory's candidates hold: a validation of the posture, and a sharper set of predictions.</p>"
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
        "notes": ("Copyright (C) 2026 Mark E. Mala. Successor to The Staked Gaps for the Convergence Codex "
                  "programme (infinitography.com). Chain Theory (A. D. Wissner-Gross, 23 Oct 2026) is cited "
                  "throughout at its own grades; corrections from its author will be incorporated in v2. "
                  "Bitcoin-timestamped via wonderben-code/convergence-codex."),
        "related_identifiers": [
            {"identifier": GAPS_DOI, "relation": "isContinuedBy", "scheme": "doi"},
            {"identifier": CAPSTONE_DOI, "relation": "isSupplementTo", "scheme": "doi"},
            {"identifier": FORCED_DOI, "relation": "isSupplementTo", "scheme": "doi"},
            {"identifier": RELATED_REPO, "relation": "isSupplementedBy", "scheme": "url"},
            {"identifier": CHAIN_THEORY_ALPHA, "relation": "references", "scheme": "url"},
            {"identifier": CHAIN_THEORY_COMPENDIUM, "relation": "references", "scheme": "url"},
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
    print("=" * 60); print("PUBLISH — The Refined Gaps"); print("=" * 60)
    build_pdf(MD_PATH, PDF_PATH)
    if os.environ.get("PDF_ONLY"):
        print("PDF_ONLY set — not publishing."); return
    info = upload_to_zenodo(PDF_PATH)
    print("\nPUBLISHED.")
    for k, v in info.items():
        print(f"  {k}: {v}")
    RESULT_PATH.write_text(json.dumps(info, indent=2))
    print(f"\nResult saved: {RESULT_PATH}")


if __name__ == "__main__":
    main()
