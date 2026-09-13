import SeparatingGraphLap
import SignlessTwins

/-!
# And its signless spectrum is not simple, so the two questions are genuinely different

`SignlessSimpleFamilies` and `SignlessConjugateMultiplicity` both fence the same thing, and
`SignlessSimpleNotNecessary` separated what they were asking: the hypothesis question is settled,
and what neither could supply is **a graph where the two simplicities disagree** — one operator
with a simple spectrum and the other without. `SignlessTwins` then proved that no twin-rich graph
can be one and emptied the estate of candidates. `SeparatingGraphLap` built a graph and proved its
**Laplacian** simple. **This is the other half, and the item closes.**

## What is proved

**`signlessLap_sepGraph`** — `Q` on the witness as an explicit `6 × 6` matrix.

**`sepQ_mulVec_two`, `sepQ_mulVec_two'`** — **two integer eigenvectors at the same eigenvalue `2`**:
`(0, −1, 1, 0, 0, 0)` and `(1, 0, 0, −1, 1, 1)`. The first is the difference of the closed twin pair
`1, 2`, and `SignlessTwins.signlessLap_mulVec_twinDiff_closed` predicts its eigenvalue exactly —
`deg − 1 = 2` — so **half of this was a theorem before it was a computation**. The second is not a
twin difference and is where the degeneracy actually comes from.

**`two_le_finrank_sepQ`** — hence `Q`'s eigenspace at `2` is at least a plane.

**`not_finrank_signless_le_one_sep`** — so **`Q` is not simple** on a graph whose **`L` is**.

**`simplicity_transfer_fails`** — **THE THEOREM THE TWO FENCES ASKED FOR.** There is a graph — not
two-colourable, connected, six vertices — on which

```
(∀ μ, finrank Q-eigenspace ≤ 1)   is FALSE
(∀ μ, finrank L-eigenspace ≤ 1)   is TRUE
```

so the equivalence `SignlessSimpleFamilies` proves for two-colourable graphs **fails without that
hypothesis**. Together with `SignlessSimpleNotNecessary` the hypothesis is now pinned from both
sides: **sufficient, not necessary, and not removable.**

**`the_full_picture`** — the two witnesses as one statement, since they are only interesting
together: **the paw** is not two-colourable and **has** the transfer, **this graph** is not
two-colourable and **fails** it. The third fact — two-colourability implies the transfer — is
`SignlessSimpleFamilies.finrank_signless_le_one_iff_lap_of_colorable` and is **cited rather than
restated**, its binders being a general graph's and not a witness's.

## What is NOT here

* **NO CHARACTERISATION.** Which graphs have the transfer is **not** determined. Two-colourable ones
  do, the paw does, this one does not, and there is no criterion (`ERRATUM 246`).
* **NO MINIMALITY IN LEAN.** That six vertices is the smallest is the machine search of the previous
  unit, fenced there and fenced here: ⚠ **not formalised.**
* **NOTHING ABOUT THE OTHER DIRECTION.** The search found five isomorphism classes with `Q` simple
  and `L` degenerate and **none of them is built**; this file exhibits the transfer failing one way
  only. The statement *the two properties are independent* would need both and is not made.
* **NOTHING ABOUT `Q`'s OTHER EIGENVALUES.** Only the eigenspace at `2` is measured, and only from
  below. The remaining four eigenvalues are the roots of `λ³ − 9λ² + 20λ − 4` and `1`, and **none of
  that is proved here** — the file needs a plane and finds one.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): none. Every statement is about one explicit
graph on `Fin 6`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SeparatingSignless

open Matrix SimpleGraph LaplacianSignless SeparatingGraphLap

/-! ## 1. `Q` on the witness -/

def sepQ : Matrix (Fin 6) (Fin 6) ℝ :=
  !![2, 0, 0, 1, 0, 1;
     0, 3, 1, 1, 1, 0;
     0, 1, 3, 1, 1, 0;
     1, 1, 1, 3, 0, 0;
     0, 1, 1, 0, 2, 0;
     1, 0, 0, 0, 0, 1]

theorem signlessLap_sepGraph : signlessLap sepGraph = sepQ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [signlessLap, SimpleGraph.degMatrix, SimpleGraph.adjMatrix, sepQ,
      sepGraph_adj, sepAdj, sepGraph_degree]

/-! ## 2. Two eigenvectors at `2` -/

/-- The closed twin difference `e₁ − e₂`. `SignlessTwins.signlessLap_mulVec_twinDiff_closed`
predicts its eigenvalue as `deg − 1 = 2`, and this is that prediction checked entry by entry. -/
def sepQVecA : Fin 6 → ℝ := ![0, -1, 1, 0, 0, 0]

/-- **AND ONE THAT IS NOT A TWIN DIFFERENCE**, which is where the degeneracy comes from. -/
def sepQVecB : Fin 6 → ℝ := ![1, 0, 0, -1, 1, 1]

theorem sepQ_mulVec_two : sepQ *ᵥ sepQVecA = (2 : ℝ) • sepQVecA := by
  ext v
  fin_cases v <;>
    simp [sepQ, sepQVecA, Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> norm_num

theorem sepQ_mulVec_two' : sepQ *ᵥ sepQVecB = (2 : ℝ) • sepQVecB := by
  ext v
  fin_cases v <;>
    simp [sepQ, sepQVecB, Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> norm_num

theorem sepQVec_linearIndependent : LinearIndependent ℝ ![sepQVecA, sepQVecB] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h1 := congrFun hab 1
  have h0 := congrFun hab 0
  simp [sepQVecA, sepQVecB] at h0 h1
  exact ⟨by linarith, by linarith⟩

/-! ## 3. So the eigenspace at `2` is a plane -/

theorem mem_ker_sepQVecA : sepQVecA ∈ LinearMap.ker
    (Matrix.toLin' (signlessLap sepGraph) - (2 : ℝ) • LinearMap.id) := by
  refine (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr ?_
  rw [signlessLap_sepGraph]; exact sepQ_mulVec_two

theorem mem_ker_sepQVecB : sepQVecB ∈ LinearMap.ker
    (Matrix.toLin' (signlessLap sepGraph) - (2 : ℝ) • LinearMap.id) := by
  refine (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr ?_
  rw [signlessLap_sepGraph]; exact sepQ_mulVec_two'

theorem two_le_finrank_sepQ :
    2 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (signlessLap sepGraph) - (2 : ℝ) • LinearMap.id)) := by
  have hsub : Submodule.span ℝ (Set.range ![sepQVecA, sepQVecB])
      ≤ LinearMap.ker (Matrix.toLin' (signlessLap sepGraph) - (2 : ℝ) • LinearMap.id) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    fin_cases i
    · exact mem_ker_sepQVecA
    · exact mem_ker_sepQVecB
  have hcard : Module.finrank ℝ
      (Submodule.span ℝ (Set.range ![sepQVecA, sepQVecB])) = 2 := by
    rw [finrank_span_eq_card sepQVec_linearIndependent]
    simp
  rw [← hcard]
  exact Submodule.finrank_mono hsub

/-- **`Q` IS NOT SIMPLE ON A GRAPH WHOSE `L` IS.** -/
theorem not_finrank_signless_le_one_sep :
    ¬ ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap sepGraph) - μ • LinearMap.id)) ≤ 1 := by
  intro h
  have h2 := two_le_finrank_sepQ
  have h1 := h 2
  omega

/-! ## 4. So the transfer fails without two-colourability -/

/-- **THE THEOREM THE TWO FENCES ASKED FOR.** -/
theorem simplicity_transfer_fails :
    ¬ sepGraph.Colorable 2 ∧
    ¬ ((∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (signlessLap sepGraph) - μ • LinearMap.id)) ≤ 1)
        ↔ (∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (sepGraph.lapMatrix ℝ) - μ • LinearMap.id)) ≤ 1)) := by
  refine ⟨?_, ?_⟩
  · -- the triangle `1–2–3` needs three colours
    intro hcol
    obtain ⟨C⟩ := hcol
    have h12 : C 1 ≠ C 2 := C.valid (by decide)
    have h23 : C 2 ≠ C 3 := C.valid (by decide)
    have h13 : C 1 ≠ C 3 := C.valid (by decide)
    have hthree : ∀ a b c : Fin 2, a ≠ b → b ≠ c → a ≠ c → False := by decide
    exact hthree _ _ _ h12 h23 h13
  · intro hiff
    exact not_finrank_signless_le_one_sep (hiff.mpr fun ν => finrank_lapMatrix_le_one_sep ν)

/-- **THE TWO WITNESSES, TOGETHER.** Off the two-colourable case the transfer sometimes holds and
sometimes fails, so two-colourability is a genuine sufficient condition with nothing hiding behind
it. The sufficient half is `SignlessSimpleFamilies.finrank_signless_le_one_iff_lap_of_colorable`. -/
theorem the_full_picture :
    (¬ PawSimpleSpectrum.pawGraph.Colorable 2 ∧
      ((∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (signlessLap PawSimpleSpectrum.pawGraph) - μ • LinearMap.id)) ≤ 1)
        ↔ (∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (PawSimpleSpectrum.pawGraph.lapMatrix ℝ) - μ • LinearMap.id)) ≤ 1)))
    ∧ (¬ sepGraph.Colorable 2 ∧
      ¬ ((∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (signlessLap sepGraph) - μ • LinearMap.id)) ≤ 1)
        ↔ (∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (sepGraph.lapMatrix ℝ) - μ • LinearMap.id)) ≤ 1))) :=
  ⟨⟨PawSignlessSpectrum.not_colorable_two_paw,
    SignlessSimpleNotNecessary.simple_transfer_paw⟩, simplicity_transfer_fails⟩

end SeparatingSignless
