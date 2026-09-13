/-
  SpectrumReflection.lean — composing the estate's two `L`/`Q` transfers, and the
  graph that shows they are different theorems.

  WHY THIS FILE EXISTS. The estate has two ways to turn a question about `Q` into a
  question about `L`, and they are not the same way:

    * `SignlessConjugateMultiplicity.finrank_eigenspace_signlessLap_eq_lap_of_colorable`
      — on a TWO-COLOURABLE graph, `mult_Q(μ) = mult_L(μ)`. **The same `μ`.** The
      two spectra coincide pointwise, by a diagonal sign conjugation.
    * `SignlessRegularSimple.finrank_signless_eq_finrank_lap_of_regular`
      — on a `Δ`-REGULAR graph, `mult_Q(μ) = mult_L(2Δ − μ)`. **A different `μ`.**
      The two spectra are reflections of each other about `Δ`, by a reindexing,
      and the file says explicitly "with no two-colourability anywhere".

  Nothing in the estate composes them, and composing them says something about
  **`L` alone**:

      on a graph that is BOTH regular and two-colourable,
      `mult_L(μ) = mult_L(2Δ − μ)` — the Laplacian spectrum is symmetric about `Δ`.

  No signless operator appears in that statement. It is the sort of fact a reader
  would expect to be somewhere and it is nowhere.

  WHAT THIS FILE PROVES.

  1. **`finrank_lap_reflect_of_regular_colorable`** — the symmetry above, and
     `finrank_signless_reflect_of_regular_colorable`, the same for `Q` (immediate,
     since on such a graph the two spectra coincide).
  2. `finrank_lap_star_top`, `finrank_lap_star_one`, `finrank_lap_star_zero`,
     `sum_finrank_lap_star` — **the star's ORDINARY Laplacian spectrum**, three
     lines each from `SignlessStarSpectrum` through the colourability transfer.
     This is the successor `SignlessStarSpectrum` named in its own header and in
     `fences_accepted.txt`, and it is exactly as small as that note said: the star
     is bipartite, so the transfer does all of it.
  3. **`reflection_fails_star`** — and the star is why item 1 needs BOTH
     hypotheses. It is two-colourable and not regular, its Laplacian spectrum is
     `{0, 1, |V|}` with multiplicities `1, |V| − 2, 1`, and reflecting `0` about
     `Δ = |V| − 1` lands at `2|V| − 2`, which for `|V| ≥ 3` is above the largest
     eigenvalue and so has multiplicity `0 ≠ 1`. **`regularity_not_removable`**
     states that as the non-implication.

  WHAT IS NOT CLAIMED. **The converse of item 1 is not touched**: a graph can have
  a symmetric Laplacian spectrum without being regular or bipartite, and nothing
  here says otherwise. **No instance of item 1 is spelled out**, though the even
  cycle, the torus and the box are all regular and two-colourable and the estate
  has all three; instantiating is a `rw` per family and nothing consumes it
  (`ERRATUM 246`). **Two-colourability is not shown necessary either** — item 3
  removes regularity only, and a witness for the other direction would have to be
  regular, non-bipartite, and have an asymmetric spectrum. Not attempted.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import SignlessStarSpectrum
import SignlessRegularSimple
import SignlessConjugateMultiplicity

namespace SpectrumReflection

open Matrix SimpleGraph LaplacianSignless GraphLaplacian
open StarAdjNormExact SignlessStarExact SignlessStarSpectrum

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. The two transfers, composed -/

/-- **A REGULAR TWO-COLOURABLE GRAPH HAS A LAPLACIAN SPECTRUM SYMMETRIC ABOUT `Δ`.**
Neither transfer says this on its own: two-colourability moves `Q` to `L` at the
same eigenvalue, regularity moves it at the reflected one, and the composite is a
statement about `L` with no `Q` in it. -/
theorem finrank_lap_reflect_of_regular_colorable {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hcol : G.Colorable 2) (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id))
      = Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (G.lapMatrix ℝ) - ((2 * Δ : ℝ) - μ) • LinearMap.id)) := by
  rw [← SignlessConjugateMultiplicity.finrank_eigenspace_signlessLap_eq_lap_of_colorable hcol μ]
  exact SignlessRegularSimple.finrank_signless_eq_finrank_lap_of_regular G hreg μ

/-- The same for `Q`, since on such a graph the two spectra coincide pointwise. -/
theorem finrank_signless_reflect_of_regular_colorable {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hcol : G.Colorable 2) (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G) - μ • LinearMap.id))
      = Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (signlessLap G) - ((2 * Δ : ℝ) - μ) • LinearMap.id)) := by
  rw [SignlessConjugateMultiplicity.finrank_eigenspace_signlessLap_eq_lap_of_colorable hcol μ,
    SignlessConjugateMultiplicity.finrank_eigenspace_signlessLap_eq_lap_of_colorable hcol
      ((2 * Δ : ℝ) - μ)]
  exact finrank_lap_reflect_of_regular_colorable hreg hcol μ

/-! ## 2. The star's ordinary Laplacian spectrum -/

variable {c : V}

/-- The transfer, at the star, once. -/
theorem finrank_lap_star_eq (c : V) (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((starGraph c).lapMatrix ℝ) - μ • LinearMap.id))
      = Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (signlessLap (starGraph c)) - μ • LinearMap.id)) :=
  (SignlessConjugateMultiplicity.finrank_eigenspace_signlessLap_eq_lap_of_colorable
    (starGraph_colorable_two c) μ).symm

theorem finrank_lap_star_top [Nontrivial V] (c : V) (h3 : 3 ≤ Fintype.card V) :
    Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' ((starGraph c).lapMatrix ℝ)
        - (Fintype.card V : ℝ) • LinearMap.id)) = 1 :=
  (finrank_lap_star_eq c _).trans (finrank_signless_star_top c h3)

theorem finrank_lap_star_one [Nontrivial V] (c : V) (h3 : 3 ≤ Fintype.card V) :
    Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' ((starGraph c).lapMatrix ℝ) - (1 : ℝ) • LinearMap.id))
      = Fintype.card V - 2 :=
  (finrank_lap_star_eq c _).trans (finrank_signless_star_one c h3)

theorem finrank_lap_star_zero [Nontrivial V] (c : V) (h3 : 3 ≤ Fintype.card V) :
    Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' ((starGraph c).lapMatrix ℝ) - (0 : ℝ) • LinearMap.id)) = 1 :=
  (finrank_lap_star_eq c _).trans (finrank_signless_star_zero c h3)

/-- **THE STAR'S LAPLACIAN SPECTRUM IS COMPLETE TOO.** The successor
`SignlessStarSpectrum` named, and it is the size that file predicted: the star is
bipartite, so the transfer does all of it and nothing new is proved about the
star. -/
theorem sum_finrank_lap_star [Nontrivial V] (c : V) (h3 : 3 ≤ Fintype.card V) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((starGraph c).lapMatrix ℝ)
          - (Fintype.card V : ℝ) • LinearMap.id))
      + Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((starGraph c).lapMatrix ℝ) - (1 : ℝ) • LinearMap.id))
      + Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((starGraph c).lapMatrix ℝ) - (0 : ℝ) • LinearMap.id))
      = Fintype.card V := by
  rw [finrank_lap_star_top c h3, finrank_lap_star_one c h3, finrank_lap_star_zero c h3]
  omega

/-! ## 3. And the star shows §1 needs regularity -/

/-- Above the largest eigenvalue there is nothing. `2|V| − 2` exceeds `|V|` once
`|V| ≥ 3`, so it is not an eigenvalue and its eigenspace is `0`. -/
theorem finrank_lap_star_above [Nontrivial V] (c : V) (h3 : 3 ≤ Fintype.card V) :
    Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' ((starGraph c).lapMatrix ℝ)
        - (2 * (Fintype.card V : ℝ) - 2) • LinearMap.id)) = 0 := by
  rw [finrank_lap_star_eq c _]
  classical
  set hQ := LaplacianSignlessDefinite.signlessLap_isHermitian (starGraph c) with hQdef
  refine HermitianDimensionSum.finrank_eigenspace_eq_zero_of_notMem hQ ?_
  intro hmem
  -- an eigenvalue is at most the top, and the top is `|V|`
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  have hle : hQ.eigenvalues i ≤ RayleighVariational.topEigen hQ :=
    SignlessPerronSimple.le_topEigen hQ i
  rw [hi, topEigen_signlessLap_star c] at hle
  have h3R : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast h3
  linarith

/-- **THE REFLECTION FAILS ON THE STAR.** `mult_L(0) = 1` and
`mult_L(2Δ − 0) = mult_L(2|V| − 2) = 0`, where `Δ = |V| − 1`. -/
theorem reflection_fails_star [Nontrivial V] (c : V) (h3 : 3 ≤ Fintype.card V) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((starGraph c).lapMatrix ℝ) - (0 : ℝ) • LinearMap.id))
      ≠ Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((starGraph c).lapMatrix ℝ)
          - (2 * (Fintype.card V : ℝ) - 2 - 0) • LinearMap.id)) := by
  rw [finrank_lap_star_zero c h3, sub_zero, finrank_lap_star_above c h3]
  exact one_ne_zero

/-- **SO REGULARITY IS NOT REMOVABLE FROM §1.** The star is two-colourable
(`SignlessStarExact.starGraph_colorable_two`) and the reflection fails on it, so
two-colourability alone does not give the symmetry. Its maximum degree is
`|V| − 1` and its leaves have degree `1`, so it is not regular at any degree once
`|V| ≥ 3` — which is what `finrank_lap_reflect_of_regular_colorable` needs and
does not get. -/
theorem regularity_not_removable [Nontrivial V] (c : V) (h3 : 3 ≤ Fintype.card V) :
    (starGraph c).Colorable 2
      ∧ ¬ ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
            (Matrix.toLin' ((starGraph c).lapMatrix ℝ) - μ • LinearMap.id))
          = Module.finrank ℝ (LinearMap.ker
            (Matrix.toLin' ((starGraph c).lapMatrix ℝ)
              - (2 * ((Fintype.card V : ℝ) - 1) - μ) • LinearMap.id)) := by
  refine ⟨starGraph_colorable_two c, fun h => ?_⟩
  have h0 := h 0
  rw [finrank_lap_star_zero c h3] at h0
  rw [show (2 * ((Fintype.card V : ℝ) - 1) - 0) = 2 * (Fintype.card V : ℝ) - 2 from by ring,
    finrank_lap_star_above c h3] at h0
  exact one_ne_zero h0

/-! ## 4. Review round 64 — the ways this could be hollow

**"§1 could be one of its two inputs restated."** It is neither. Each input relates
`Q` to `L`; the conclusion mentions only `L`. And the two inputs do genuinely
different things — one preserves the eigenvalue and one reflects it — which is the
whole reason the composite says anything.

**"§2 could be new work on the star."** It is not, and the header and the
docstrings say so: the star is bipartite, so every one of its Laplacian
multiplicities is the corresponding signless one, proved yesterday. §2 is the
successor `SignlessStarSpectrum` named for itself, discharged at the size that
file predicted. Recording it as small is the point; recording it as a result would
be `ERRATUM 541` again.

**"§3 might not need `h3`."** It does. At `|V| = 2` the star is a single edge,
which IS regular, and the reflection holds there — the separation is genuinely a
statement about `|V| ≥ 3`.

**"§3 could be vacuous — maybe `2|V| − 2` is never an eigenvalue for a boring
reason."** That is exactly the reason, and it is the right one: the star's top
eigenvalue is `|V|` and `2|V| − 2 > |V|` for `|V| ≥ 3`, so `finrank_lap_star_above`
is proved from `SignlessPerronSimple.le_topEigen` and
`SignlessStarExact.topEigen_signlessLap_star` rather than by inspecting a
spectrum. A witness that fails a symmetry by being above the top is still a
witness.

**"The converse might be easy and is being avoided."** It is not attempted and the
header says so. A graph with a symmetric Laplacian spectrum that is neither
regular nor bipartite would settle it, and the estate's search machinery for such
witnesses is exactly what `SeparatingGraphLap` needed six vertices and an
exhaustive machine search to produce.
-/

end

end SpectrumReflection
