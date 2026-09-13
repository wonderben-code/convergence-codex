import HermitianDimensionSum

/-!
# `K_{1,1,2,2}`'s multiplicity table and characteristic polynomial — and a theorem re-proved

**THIS UNIT SET OUT TO CLOSE A HOLE THAT WAS CLOSED YESTERDAY** (`ERRATUM 527`). Entry 66's `§6`
named the multiplicity at a part value **with** a half-sized part as *the last hole in an otherwise
complete description of this family's spectrum*, and called it *genuine mathematics rather than
plumbing*. **It was neither a hole nor mathematics**: `SecularPoleMultiplicity`, committed
2026-09-12 by this same campaign, proves `inf_le_ker_secularMap`,
`finrank_ker_secularMap_eq_half` and `finrank_signless_size_eq_half` — the same three statements,
by the same argument, under the same names — and its own header says *what was missing was the
reverse inclusion, and it is three lines*. This file re-derived all three before `dupname_scan`
said so. **They are deleted; what remains is what was actually new.**

## What is proved

**`finrank_five_P1123_direct`** — **the formula reproduces entry 66's subtraction.** That entry got
the multiplicity `2` at `K_{1,1,2,3}`'s value `5` as `7 − 3 − 1 − 1`, because the part-value count
did not reach it; here it is `1·(2 − 1) + 2 − 1` from
`SecularPoleMultiplicity.finrank_signless_size_eq_half`. Two independent routes to one number, and
the graph is a day newer than the formula, so this check could not have been made when the formula
was written — `SecularPoleMultiplicity`'s own check is against the diamond.

**`finrank_four_P1122`, `finrank_two_P1122`, `finrank_root_P1122`, `finrank_lo_P1122`,
`finrank_hi_P1122`** — **`K_{1,1,2,2}`'s multiplicity table, `3, 1, 1, 1`**, which entry 66 named
as blocked and which the day-old formula settles immediately. **The value `2` is a pole and not a
part value**, so its multiplicity comes through `finrank_signless_eigenspace_of_ne` rather than the
part-value split — the same closed form, reached the other way, because the formula is about a
**vanishing denominator** and not about part values.

**`herm_P1122`, `image_eigenvalues_P1122`, `charpoly_signlessLap_P1122`** — so the characteristic
polynomial is `(X − 4)³(X − 2)(X − (6 − 2√2))(X − (6 + 2√2))`, of degree `6`. The chain's fourth,
after the equipartite family, the singleton family, `K_{1,3,3}`, the paw and `K_{1,1,2,3}` — sixth,
counting properly.

## What is NOT here

* **NO GENERAL MULTIPLICITY THEOREM IS STATED, as of 2026-09-13 (entry 67).** Every piece is now a
  closed form and assembling them into one statement needs a case split on part-value-hood and on
  whether the half-sized set is empty. That was true before this unit and is still true.
* **NO CHARACTERISTIC POLYNOMIAL FOR A FAMILY, as of 2026-09-13 (entry 67).** Individual graphs
  only; nothing uniform in the sizes.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): this file is about two named graphs and its
theorems take none. **No mass, no propagator, no metric.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessP1122Charpoly

open Matrix Polynomial Finset SimpleGraph LaplacianSignless
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularBound UnbalancedMultipartiteSecularEquation
open SecularPoleMultiplicity
open SignlessP1122Exact SignlessSpectrumTrichotomy SignlessDoublingFails

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. The check: the formula reproduces a number obtained by subtraction -/

/-- Entry 66 got this `2` as `7 − 3 − 1 − 1`; here it is `1·(2 − 1) + 2 − 1`. -/
theorem finrank_five_P1123_direct :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph SignlessRootOverlap.P1123))
          - (5 : ℝ) • LinearMap.id)) = 2 := by
  have h := finrank_signless_size_eq_half (V := SignlessRootOverlap.P1123) (n := 2) (by norm_num)
    (by rw [SignlessRootOverlap.total_P1123]; norm_num) SignlessRootOverlap.nonempty_P1123 0
    (by decide)
  rw [show ((Fintype.card (Σ i, SignlessRootOverlap.P1123 i) : ℝ) - ((2 : ℕ) : ℝ)) = 5 from by
    rw [SignlessRootOverlap.total_P1123]; norm_num] at h
  rw [h, show Fintype.card {i : Fin 4 // Fintype.card (SignlessRootOverlap.P1123 i) = 2} = 1 from
      by decide,
    show Fintype.card {i : Fin 4 // 2 * Fintype.card (SignlessRootOverlap.P1123 i) = 2} = 2 from
      by decide]

/-! ## 2. So `K_{1,1,2,2}` gets its table -/

theorem herm_P1122 : (signlessLap (completeMultipartiteGraph P1122)).IsHermitian :=
  LaplacianSignlessDefinite.signlessLap_isHermitian _

theorem finrank_four_P1122 :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph P1122)) - (4 : ℝ) • LinearMap.id)) = 3 := by
  have h := finrank_signless_size_eq_half (V := P1122) (n := 2) (by norm_num)
    (by rw [total_P1122]; norm_num) (fun _ => ⟨0⟩) 0 (by decide)
  rw [show ((Fintype.card (Σ i, P1122 i) : ℝ) - ((2 : ℕ) : ℝ)) = 4 from by
    rw [total_P1122]; norm_num] at h
  rw [h, show Fintype.card {i : Fin 4 // Fintype.card (P1122 i) = 2} = 2 from by decide,
    show Fintype.card {i : Fin 4 // 2 * Fintype.card (P1122 i) = 2} = 2 from by decide]

/-- **AND AT A POLE THAT IS NOT A PART VALUE, THE SAME CLOSED FORM.** -/
theorem finrank_two_P1122 :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph P1122)) - (2 : ℝ) • LinearMap.id)) = 1 := by
  have hval : ∀ i : Fin 4, ((Fintype.card (Σ i, P1122 i) : ℝ) - Fintype.card (P1122 i))
      ≠ (2 : ℝ) := by
    intro i
    rw [total_P1122]
    rcases size_cases i with h | h <;> rw [h] <;> norm_num
  rw [finrank_signless_eigenspace_of_ne (V := P1122) (fun _ => ⟨0⟩) hval]
  have h := finrank_ker_secularMap_eq_half (V := P1122) (n := 4) (fun _ => ⟨0⟩) 2 (by decide)
  rw [show ((Fintype.card (Σ i, P1122 i) : ℝ) - ((4 : ℕ) : ℝ)) = 2 from by
    rw [total_P1122]; norm_num] at h
  rw [h, show Fintype.card {i : Fin 4 // 2 * Fintype.card (P1122 i) = 4} = 2 from by decide]

theorem finrank_root_P1122 {μ : ℝ} (h5 : μ ≠ 5) (h4 : μ ≠ 4) (h2 : μ ≠ 2)
    (hroot : secularSum (V := P1122) μ = -1) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph P1122)) - μ • LinearMap.id)) = 1 := by
  refine finrank_signless_eigenspace_secular_one (V := P1122) (fun _ => ⟨0⟩) 0 ?_ ?_ hroot
  · intro i
    rw [total_P1122]
    rcases size_cases i with h | h <;> rw [h] <;> push_cast <;> intro hc
    · exact h5 (by linarith)
    · exact h4 (by linarith)
  · intro i
    rw [total_P1122]
    rcases size_cases i with h | h <;> rw [h] <;> push_cast <;> intro hc
    · exact h4 (by linarith)
    · exact h2 (by linarith)

theorem finrank_lo_P1122 :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph P1122)) - lo • LinearMap.id)) = 1 := by
  obtain ⟨lo1, lo2⟩ := lo_bounds
  exact finrank_root_P1122 (by linarith) (by linarith) (by linarith)
    ((root_iff lo (by linarith) (by linarith)).mpr (Or.inl rfl))

theorem finrank_hi_P1122 :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph P1122)) - hi • LinearMap.id)) = 1 := by
  obtain ⟨hi1, hi2⟩ := hi_bounds
  exact finrank_root_P1122 (by linarith) (by linarith) (by linarith)
    ((root_iff hi (by linarith) (by linarith)).mpr (Or.inr rfl))

/-! ## 3. And its characteristic polynomial -/

theorem image_eigenvalues_P1122 :
    Finset.univ.image herm_P1122.eigenvalues = ({2, 4, lo, hi} : Finset ℝ) := by
  ext μ
  rw [HermitianCharpoly.mem_image_eigenvalues_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact spectrum_P1122 μ

/-- **`Q`'S CHARACTERISTIC POLYNOMIAL ON `K_{1,1,2,2}`.** -/
theorem charpoly_signlessLap_P1122 :
    (signlessLap (completeMultipartiteGraph P1122)).charpoly
      = (X - C (2 : ℝ)) * (X - C (4 : ℝ)) ^ 3 * (X - C lo) * (X - C hi) := by
  obtain ⟨lo1, lo2⟩ := lo_bounds
  obtain ⟨hi1, hi2⟩ := hi_bounds
  have n2 : (2 : ℝ) ∉ ({4, lo, hi} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · norm_num at h
    · rw [← h] at lo1; norm_num at lo1
    · rw [← h] at hi1; norm_num at hi1
  have n4 : (4 : ℝ) ∉ ({lo, hi} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · rw [← h] at lo2; norm_num at lo2
    · rw [← h] at hi1; norm_num at hi1
  have nlo : lo ∉ ({hi} : Finset ℝ) := by
    simp only [Finset.mem_singleton]
    intro h; rw [h] at lo2; linarith
  rw [HermitianCharpoly.charpoly_eq_prod_pow_finrank herm_P1122, image_eigenvalues_P1122,
    Finset.prod_insert n2, Finset.prod_insert n4, Finset.prod_insert nlo,
    Finset.prod_singleton, finrank_two_P1122, finrank_four_P1122, finrank_lo_P1122,
    finrank_hi_P1122]
  ring

end SignlessP1122Charpoly
