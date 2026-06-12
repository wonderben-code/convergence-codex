#!/usr/bin/env python3
"""Generate PDF for the Tree of Reality paper and publish to Zenodo.

One-shot script. Run once. Captures DOI in stdout + saves result JSON.
Template: scripts/publish_paper_g.py (used successfully 2026-06-12).
"""

import json
import os
import re
import sys
from pathlib import Path

import markdown
import requests
from weasyprint import HTML

# ─── Config ─────────────────────────────────────────────────────────────

TOKEN = os.environ.get("ZENODO_TOKEN", "")  # set ZENODO_TOKEN env var before running
if not TOKEN:
    raise SystemExit("ZENODO_TOKEN not set — see memory file for active token")
BASE = "https://zenodo.org/api"
HEADERS = {"Authorization": f"Bearer {TOKEN}"}

ROOT = Path("/Users/ekramalam/convergence-codex")
MD_PATH = ROOT / "papers" / "tree_of_reality.md"
PDF_PATH = ROOT / "papers" / "tree_of_reality.pdf"
RESULT_PATH = ROOT / "papers" / "tree_of_reality.zenodo.json"

TITLE = "The Tree of Reality: A Causal Cladogram from the Reflexive-Domain Seed to Physics, with Honest Status Tags Throughout"
PUBLICATION_DATE = "2026-06-12"
KEYWORDS = [
    "theory of everything",
    "causal cladogram",
    "reflexive domain",
    "noncommutative geometry",
    "spectral triple",
    "Standard Model emergence",
    "co-evolved similarity",
    "falsifiable predictions",
    "Lawvere fixed point",
    "machine-verified mathematics",
    "Bitcoin timestamping",
]
DESCRIPTION_NOTE = (
    "Companion to The Shape of the Theory (Paper G, DOI 10.5281/zenodo.20661837). "
    "Maps how physics branches from nothing: Lawvere's reflexive domain "
    "D = (D → D) forces the seed M₂(ℂ), which cascades through "
    "endomorphism iteration and bifurcates into three independent lineages "
    "(END / AUT / ⟨·,·⟩), each independently producing a Connes "
    "spectral triple — co-evolved similarity, not convergence. Every claim "
    "wears one of seven status tags (PROVED / PARTIAL / CLAIMED / PREDICTED / "
    "SPECULATIVE / DOWNSTREAM / META). The May 2026 audit findings are stated "
    "openly; the genuinely Mathlib-backed core is enumerated explicitly. "
    "Includes the full predictions catalogue (17 falsifiable predictions, "
    "flagship: proton decay within Hyper-Kamiokande reach)."
)
REFERENCES = [
    "Mala, M. E. (2026). The Shape of the Theory. DOI: 10.5281/zenodo.20661837.",
    "Mala, M. E. (2026). Pansophia: A Four-Component Architecture for Autonomous Knowledge Work. DOI: 10.5281/zenodo.19974680.",
    "Mala, M. E. (2026). Paper D: Machine-Verified Foundation. DOI: 10.5281/zenodo.20005115.",
    "Mala, M. E. (2026). Paper E: Three Lineages from One Seed. DOI: 10.5281/zenodo.20011467.",
    "Mala, M. E. (2026). Paper F: Complete Mathematical Programme (GToE). DOI: 10.5281/zenodo.20026519.",
    "Connes, A. and Marcolli, M. (2008). Noncommutative Geometry, Quantum Fields and Motives. AMS.",
    "Chamseddine, A. H. and Connes, A. (1997). The spectral action principle. Comm. Math. Phys.",
    "Chamseddine, A. H., Connes, A. and Marcolli, M. (2007). Gravity and the Standard Model with neutrino mixing. Adv. Theor. Math. Phys.",
    "Lawvere, F. W. (1969). Diagonal arguments and Cartesian closed categories.",
    "Scott, D. (1972). Continuous lattices.",
    "Gleason, A. M. (1957). Measures on the closed subspaces of a Hilbert space. J. Math. Mech.",
    "Stone, M. H. (1932). On one-parameter unitary groups in Hilbert space. Ann. Math.",
    "Lovelock, D. (1971). The Einstein tensor and its generalizations. J. Math. Phys.",
    "Pati, J. C. and Salam, A. (1974). Lepton number as the fourth color. Phys. Rev. D.",
    "Starobinsky, A. A. (1980). A new type of isotropic cosmological models without singularity. Phys. Lett. B.",
]
RELATED_REPO = "https://github.com/wonderben-code/convergence-codex"
PAPER_G_DOI = "10.5281/zenodo.20661837"

# ─── PDF generation ─────────────────────────────────────────────────────

CSS = """
@page {
    size: A4;
    margin: 2.4cm 2cm;
    @bottom-center {
        content: counter(page);
        font-family: 'Georgia', serif;
        font-size: 10pt;
        color: #666;
    }
}
body {
    font-family: 'Georgia', 'Times New Roman', serif;
    font-size: 11pt;
    line-height: 1.55;
    color: #1a1a1a;
}
h1 {
    font-size: 22pt;
    margin: 0 0 4pt 0;
    color: #111;
    page-break-after: avoid;
}
h1 + p em {
    color: #555;
    font-size: 12pt;
}
h2 {
    font-size: 15pt;
    margin: 26pt 0 8pt 0;
    color: #222;
    border-bottom: 1px solid #ccc;
    padding-bottom: 4pt;
    page-break-after: avoid;
}
h3 {
    font-size: 12.5pt;
    margin: 18pt 0 6pt 0;
    color: #333;
    page-break-after: avoid;
}
p { margin: 0 0 8pt 0; text-align: justify; }
strong { color: #111; }
em { font-style: italic; }
hr { border: none; border-top: 1px solid #ddd; margin: 18pt 0; }
table {
    width: 100%;
    border-collapse: collapse;
    margin: 10pt 0;
    font-size: 10pt;
    page-break-inside: avoid;
}
thead { background: #f5f5f5; }
th { border: 1px solid #999; padding: 5pt 7pt; text-align: left; font-weight: bold; }
td { border: 1px solid #ccc; padding: 4pt 7pt; text-align: left; }
tr:nth-child(even) td { background: #fafafa; }
ul, ol { margin: 4pt 0 8pt 0; padding-left: 20pt; }
li { margin-bottom: 4pt; }
code {
    font-family: 'Menlo', 'Courier New', monospace;
    font-size: 9.5pt;
    background: #f4f4f4;
    padding: 1pt 3pt;
    border-radius: 2pt;
}
pre {
    font-family: 'Menlo', 'Courier New', monospace;
    font-size: 9pt;
    background: #f4f4f4;
    padding: 10pt;
    border: 1px solid #ddd;
    border-radius: 3pt;
    white-space: pre-wrap;
    word-wrap: break-word;
    page-break-inside: avoid;
}
blockquote {
    border-left: 3pt solid #999;
    margin: 10pt 0;
    padding: 4pt 14pt;
    color: #333;
    font-style: italic;
}
.math-block {
    text-align: center;
    font-family: 'Cambria Math', 'STIX Two Math', 'Georgia', serif;
    font-size: 12pt;
    margin: 14pt 0;
    page-break-inside: avoid;
}
.math-inline {
    font-family: 'Cambria Math', 'STIX Two Math', 'Georgia', serif;
}
a { color: #1a4a8a; text-decoration: none; }
"""


def latex_to_unicode(s: str) -> str:
    """Light LaTeX -> unicode for the small set of expressions in the paper."""
    repl = [
        (r"\rightarrow", "→"),
        (r"\mathrm{Tr}", "Tr"),
        (r"\langle", "⟨"),
        (r"\rangle", "⟩"),
        (r"\psi", "ψ"),
        (r"\Lambda", "Λ"),
        (r"\Sigma", "Σ"),
        (r"\Omega", "Ω"),
        (r"\theta", "θ"),
        (r"\alpha", "α"),
        (r"\sigma", "σ"),
        (r"\delta", "δ"),
        (r"\pi", "π"),
        (r"\sim", "∼"),
        (r"\times", "×"),
        (r"\approx", "≈"),
        (r"\to", "→"),
    ]
    for a, b in repl:
        s = s.replace(a, b)
    s = re.sub(r"\^2", "²", s)
    s = re.sub(r"\^0", "⁰", s)
    return s


def preprocess_math(md_text: str) -> str:
    """Convert $$...$$ and $...$ to span/div with unicode rendering."""
    def block(m):
        inner = latex_to_unicode(m.group(1).strip())
        return f"\n\n<div class=\"math-block\">{inner}</div>\n\n"
    def inline(m):
        inner = latex_to_unicode(m.group(1).strip())
        return f"<span class=\"math-inline\">{inner}</span>"
    md_text = re.sub(r"\$\$(.+?)\$\$", block, md_text, flags=re.DOTALL)
    md_text = re.sub(r"\$([^\$\n]+?)\$", inline, md_text)
    return md_text


def strip_frontmatter(md_text: str) -> tuple[dict, str]:
    """Strip YAML frontmatter and return (meta, body)."""
    if not md_text.startswith("---\n"):
        return {}, md_text
    end = md_text.find("\n---\n", 4)
    if end < 0:
        return {}, md_text
    frontmatter = md_text[4:end]
    body = md_text[end + 5 :]
    meta = {}
    for line in frontmatter.splitlines():
        m = re.match(r'^(\w+):\s*"?(.*?)"?\s*$', line)
        if m:
            meta[m.group(1)] = m.group(2)
    return meta, body


def build_pdf(md_path: Path, pdf_path: Path) -> None:
    text = md_path.read_text()
    _, body = strip_frontmatter(text)
    body = preprocess_math(body)
    html_body = markdown.markdown(
        body,
        extensions=["tables", "fenced_code", "smarty", "sane_lists"],
        extension_configs={"smarty": {"smart_angled_quotes": True}},
    )
    html_full = f"""<!DOCTYPE html>
<html><head><meta charset=\"utf-8\"><style>{CSS}</style></head>
<body>{html_body}</body></html>"""
    HTML(string=html_full).write_pdf(str(pdf_path))
    print(f"PDF written: {pdf_path} ({pdf_path.stat().st_size // 1024} KB)")


# ─── Zenodo upload ──────────────────────────────────────────────────────


def upload_to_zenodo(pdf_path: Path) -> dict:
    description_html = (
        "<p><strong>The Tree of Reality.</strong> A causal cladogram from the "
        "reflexive-domain seed to physics, with honest status tags throughout.</p>"
        f"<p>{DESCRIPTION_NOTE}</p>"
        "<p>Independent research, AI-collaborative, not peer-reviewed. Read in that light. "
        "Verify what catches your eye. Challenge what you doubt.</p>"
    )

    # 1. Create deposition
    print("Creating deposition...")
    r = requests.post(
        f"{BASE}/deposit/depositions",
        json={},
        headers={**HEADERS, "Content-Type": "application/json"},
        timeout=60,
    )
    r.raise_for_status()
    dep = r.json()
    dep_id = dep["id"]
    bucket = dep["links"]["bucket"]
    print(f"  Deposition ID: {dep_id}")

    # 2. Upload PDF
    print(f"Uploading PDF ({pdf_path.stat().st_size // 1024} KB)...")
    with pdf_path.open("rb") as f:
        r = requests.put(
            f"{bucket}/{pdf_path.name}",
            data=f,
            headers={**HEADERS, "Content-Type": "application/octet-stream"},
            timeout=120,
        )
    r.raise_for_status()

    # 3. Also upload the .md source
    md = MD_PATH
    print(f"Uploading source MD ({md.stat().st_size // 1024} KB)...")
    with md.open("rb") as f:
        r = requests.put(
            f"{bucket}/{md.name}",
            data=f,
            headers={**HEADERS, "Content-Type": "application/octet-stream"},
            timeout=60,
        )
    r.raise_for_status()

    # 4. Metadata
    print("Setting metadata...")
    metadata = {
        "metadata": {
            "title": TITLE,
            "upload_type": "publication",
            "publication_type": "preprint",
            "description": description_html,
            "creators": [
                {
                    "name": "Mala, Mark E.",
                    "orcid": "0009-0007-8760-5553",
                    "affiliation": "Independent Researcher",
                }
            ],
            "keywords": KEYWORDS,
            "publication_date": PUBLICATION_DATE,
            "license": "cc-by-4.0",
            "language": "eng",
            "version": "v1",
            "access_right": "open",
            "notes": (
                "Copyright (C) 2026 Mark E. Mala. Companion to The Shape of the Theory "
                "(Paper G) for the Convergence Codex programme (infinitography.com). "
                "Bitcoin-timestamped via wonderben-code/convergence-codex."
            ),
            "related_identifiers": [
                {
                    "identifier": RELATED_REPO,
                    "relation": "isSupplementedBy",
                    "scheme": "url",
                },
                {
                    "identifier": PAPER_G_DOI,
                    "relation": "isSupplementTo",
                    "scheme": "doi",
                },
            ],
            "references": REFERENCES,
        }
    }
    r = requests.put(
        f"{BASE}/deposit/depositions/{dep_id}",
        json=metadata,
        headers={**HEADERS, "Content-Type": "application/json"},
        timeout=60,
    )
    if r.status_code != 200:
        print("Metadata error:", r.status_code, r.text[:1000])
        r.raise_for_status()

    # 5. Publish
    print("Publishing...")
    r = requests.post(
        f"{BASE}/deposit/depositions/{dep_id}/actions/publish",
        headers=HEADERS,
        timeout=60,
    )
    if r.status_code != 202:
        print("Publish error:", r.status_code, r.text[:1000])
        r.raise_for_status()
    result = r.json()
    return {
        "deposition_id": dep_id,
        "doi": result.get("doi"),
        "concept_doi": result.get("conceptdoi"),
        "html_url": result.get("links", {}).get("html"),
        "record_url": result.get("links", {}).get("record_html"),
        "doi_url": result.get("links", {}).get("doi"),
    }


def main():
    print("=" * 60)
    print("PUBLISH — The Tree of Reality")
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
