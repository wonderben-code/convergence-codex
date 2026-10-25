# Reading log

What was read, how, and what is not yet understood — so that anyone on the Chain Theory side can
see exactly where these notes may be wrong and correct them.

## 25 October 2026 — first reading

| Document | How read | Coverage |
|---|---|---|
| Announcement post (theinnermostloop.substack.com/p/chain-theory, 24 Oct 2026) | full text | complete |
| *A Parameter-Free Candidate for the Fine-Structure Constant from Entangled Qudits* (24 pp, 23 Oct 2026) | text extracted with `pdftotext -layout`; read for the axiom, definitions, Theorems 1–2, Conjecture 1, Table I, the alternatives table, the related-programmes paragraph | substantial; the Supplemental Material's lemma on sector sizes and Table S1 read via the slides' restatement |
| *Chain Theory: Toward Fundamental Physics from Distilling Networks of Entangled Qudits* (754 pp, release 0.1, 23 Oct 2026) | text extracted (≈440,000 words); read in full: abstract, introduction, framework chapter (Part I opening, Definitions 1.1–1.6, Conjecture 0, Conjecture 2, the register matrix), Part XVI opening and Table 239.1, the glossary; read by targeted search: Parts III–XI for the boxes cited in 01 and 03–05 (35.1, 40.1, 41.1, 50.1, 53.1, 54.1, 55.1, 58.1, 59.1, 61.1, 64.1, 64.2, 65.1, 65.2, 74.1, 78.1, 79.1, 83.1, 90.1, 90.2, 99.1, 104.1, 115.1, 149.1, 152.1, 157.1, 171.1, 172.1, 177.1, 185.1, 195.1, 197.1–197.5, 198.3, 200.1, 202.1, 217.1, 220.3, 221.1, 224.1, 225.1, 230.1, 233.2, 235.2); searched for: noncommutative, Connes, spectral action, Clifford, Pati, SU(4), quaternion, division algebra, Lawvere, fixed point, Wheeler, Bekenstein, three generations, Born rule, Lorentz, signature, confinement, cosmological, Weinberg, Koide | partial — the derivations inside most boxes were not read line by line |
| *Chain Theory: An Introduction* (71 slides, 23 Oct 2026) | full text | complete |
| `ChainAlpha.lean` (Core Lean 4.35) | ≈70 % read verbatim (header, definitions, record construction, counts, the "what this file does not check" list); the closed-form evaluation and `#print axioms` in the tail were not read directly but are reported in the slides and README | partial |
| C. S. Carson, "The Sand Castles of Brazzaville Beach" (independent commentary) | full text | complete; used only to confirm which claims are conjectures |

## Things not yet understood (and therefore possibly misstated above)

1. **"Office."** The glossary's definition was not located verbatim; 02 gives "≈ a coupling or
   quantum number" from context (the Higgs quartic "as the ratio of offices", "the coupling
   office of the chain sum", "a link whose office is zero and whose center acts"). Correction
   welcome.
2. **The move table.** Conjecture 0 is "graded a conditional theorem under its move table"; the
   table itself was not studied. 05's suggestion that End-iteration might reproduce it is a
   hypothesis, not a reading.
3. **"Depth" and "rung" vs the cascade's levels.** 02 and 04 guess depth n ↔ M_{2^{2^n}}. This
   may be wrong: Chain Theory's depth counts waves of a *closure*, which may not align with
   levels of a *tower*.
4. **The derivation inside 83.1.** "Three, a theorem of the valence" was read as stated; the
   exhaustive-check derivation behind it (rungs, dressings, "thirty-six of thirty-six") was not
   followed in detail.
5. **The gravity Part (VI).** Read for standing and headlines only. The construction of the depth
   metric and the Laplacian was not followed.
6. **The W and Z webs.** 164.5 ("the ratio of the two offices is exactly ½") is cited in 05 as
   relevant to the Weinberg angle; whether that ½ is the quantity that fixes M_W/M_Z, or
   something else, was not determined.
7. **Chain Theory's "three registers" vs the Tree's "three lineages".** 03 notes both programmes
   fan into three. These are almost certainly different threes; 03 says so, but the temptation to
   identify them should be resisted until Q9 is attempted.

## Corrections

None yet. Corrections from the Chain Theory side will be recorded here with the date and the
file they change.
