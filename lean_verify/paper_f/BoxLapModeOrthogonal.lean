import BoxLapBasis
import BoxModeOrthogonal
import SymmetricEigenOrthogonal

/-!
# The box's Laplacian modes are orthogonal

`BoxMassiveSpectrum` closed `UNLOCK_WATCHLIST`'s *a BOX is not a circulant* item and its
`STATUS (21)` names four things that are **not** proved. This file takes the second, which is the
only one of the four that changes a number anywhere else in the estate:

> *"No Loewner statement, so `BoxMassiveBound`'s constant does not move — the exact maximum
> `2d + 2d·cos(π/n) + m²` is below that file's bound `2d + 2d·cos(π/(n+1)) + m²`, but converting an
> eigenvalue maximum into `massive ≼ c·1` needs these modes shown **orthogonal**, which
> `BoxModeOrthogonal` does for the **adjacency** modes and nobody has done for these."*

> **`cosMode_dotProduct_eq_zero`** — the path's `n` half-step cosine modes are pairwise orthogonal.
>
> **`siteLapVec_dotProduct`** — the box's pairing is the product of `d` path pairings, one per axis.
>
> **`siteLapVec_dotProduct_eq_zero`** and **`siteLapVec_dotProduct_self_pos`** — so the box's `n^d`
> Laplacian modes are an **orthogonal** basis.

## Both arguments are already here, and neither is the other

At `d = 1` the **distinct-eigenvalue** argument applies — `SimpleGraph.isSymm_lapMatrix` and
`BoxLapBasis.lapEigenvalue_injective` — exactly as `SymmetricEigenOrthogonal` used it for the
adjacency modes. At `d ≥ 2` it does **not**, because the sums repeat; there the pairing has to
**factorise**, which is `BoxModeOrthogonal.prodVec_dotProduct` and `dotProduct_comp_equiv`, both
stated generally enough that this file reuses them without a word of new algebra. **Two different
reasons for one conclusion, in the same order as for the adjacency modes** — which is the point
worth noticing, since the two mode families are unrelated as functions.

## What this is NOT

**No norm is computed.** Positivity, not a value; the classical `((n+1)/2)^d`-shaped constant is
**not** proved here and as of 31 Aug 2026 is not costed (`ERRATUM 194`, `ERRATUM 246`).

**No operator bound is drawn here.** Feeding this to
`OrthogonalQuadForm.quadForm_le_of_orthogonal_eigenbasis` is the next step and **is not taken in
this file**.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BoxLapModeOrthogonal

open Finset Matrix SimpleGraph BoxGraph BoxGraphSuccIso PathLapSpectrum BoxLapSpectrum BoxLapBasis

variable {d m : ℕ}

/-! ## 1. The path, by distinct eigenvalues -/

/-- **THE PATH'S HALF-STEP COSINE MODES ARE PAIRWISE ORTHOGONAL.** -/
theorem cosMode_dotProduct_eq_zero {m : ℕ} {k l : Fin (m + 1)} (hkl : k ≠ l) :
    cosMode (m + 1) k.val ⬝ᵥ cosMode (m + 1) l.val = 0 := by
  refine SymmetricEigenOrthogonal.dotProduct_eq_zero_of_eigen_ne
    (SimpleGraph.isSymm_lapMatrix ℝ (pathGraph (m + 1)))
    (lapMatrix_mulVec_cosMode m k.val) (lapMatrix_mulVec_cosMode m l.val) ?_
  intro hcon
  exact hkl (lapEigenvalue_injective m hcon)

/-! ## 2. The box, by factorisation -/

/-- `BoxLapBasis.siteLapVec_succ` stated with the **`Equiv`** rather than the `SimpleGraph.Iso`.
The two coercions are definitionally equal — this is `rfl` on the previous theorem — but
`BoxModeOrthogonal.dotProduct_comp_equiv` is stated for an `Equiv`, and `rw` matches syntactically.
Not a second proof: one line, and the reason it exists is the coercion and nothing else. -/
theorem siteLapVec_succ_equiv (d m : ℕ) (k : Site (d + 1) (m + 1)) :
    siteLapVec (d + 1) (m + 1) k
      = (BoxProdAdjSpectrum.prodVec (cosMode (m + 1) (k 0).val)
          (siteLapVec d (m + 1) (Fin.tail k))) ∘ (consSite d (m + 1)).symm :=
  siteLapVec_succ d m k

/-- **ONE FACTOR PER AXIS.** -/
theorem siteLapVec_dotProduct (d m : ℕ) (k l : Site d (m + 1)) :
    siteLapVec d (m + 1) k ⬝ᵥ siteLapVec d (m + 1) l
      = ∏ i, cosMode (m + 1) (k i).val ⬝ᵥ cosMode (m + 1) (l i).val := by
  induction d with
  | zero => simp [siteLapVec, boxLapVec, dotProduct]
  | succ d ih =>
      rw [siteLapVec_succ_equiv, siteLapVec_succ_equiv, BoxModeOrthogonal.dotProduct_comp_equiv,
        BoxModeOrthogonal.prodVec_dotProduct, ih, Fin.prod_univ_succ]
      rfl

/-- **DIFFERENT FREQUENCY VECTORS ARE ORTHOGONAL** — they differ on some axis, and that axis alone
contributes a zero factor. -/
theorem siteLapVec_dotProduct_eq_zero {k l : Site d (m + 1)} (hkl : k ≠ l) :
    siteLapVec d (m + 1) k ⬝ᵥ siteLapVec d (m + 1) l = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ l i := by
    by_contra hcon
    exact hkl (funext fun i => not_not.1 fun h => hcon ⟨i, h⟩)
  rw [siteLapVec_dotProduct]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (cosMode_dotProduct_eq_zero hi)

/-- **AND EVERY MODE HAS STRICTLY POSITIVE SQUARE NORM.** -/
theorem siteLapVec_dotProduct_self_pos (k : Site d (m + 1)) :
    0 < siteLapVec d (m + 1) k ⬝ᵥ siteLapVec d (m + 1) k := by
  rw [siteLapVec_dotProduct]
  refine Finset.prod_pos fun i _ => ?_
  have hne : cosMode (m + 1) (k i).val ≠ 0 := by
    intro hcon
    have h := congrFun hcon (⟨0, Nat.succ_pos m⟩ : Fin (m + 1))
    have hpos := cosMode_corner_pos (n := m + 1) (k := (k i).val) (Nat.succ_pos m) (k i).isLt
    rw [h] at hpos
    exact lt_irrefl 0 hpos
  have hnn : (0 : ℝ) ≤ cosMode (m + 1) (k i).val ⬝ᵥ cosMode (m + 1) (k i).val := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exact absurd (dotProduct_self_eq_zero.1 h.symm) hne

end BoxLapModeOrthogonal
