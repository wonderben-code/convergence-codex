import BoxAdjBasis
import SymmetricEigenOrthogonal

/-!
# The box's modes are pairwise orthogonal, and the argument is not the path's

`SymmetricEigenOrthogonal` made the path's `n` sine modes pairwise orthogonal in one line — a
symmetric matrix's eigenvectors at **different** eigenvalues are `⬝ᵥ`-orthogonal, and
`PathAdjBasis.eigenvalue_injective` says the path's are different. It then recorded, precisely,
why that argument **cannot** reach the box: in `d ≥ 2` the eigenvalues **repeat**, since `(1, 2)`
and `(2, 1)` give the same sum of cosines. **So the box needs a different reason, and the reason is
the product structure.**

> **`prodVec_dotProduct`** — the dot product **factorises**: `(u ⊗ w) ⬝ᵥ (u' ⊗ w')`
> `= (u ⬝ᵥ u')·(w ⬝ᵥ w')`.
>
> **`siteVec_dotProduct`** — hence, by induction on the dimension,
> `siteVec d n k ⬝ᵥ siteVec d n l = ∏ᵢ (pathVec-on-axis-i pairing)`: the box's pairing is the
> product of `d` path pairings, one per axis.
>
> **`siteVec_dotProduct_eq_zero`** — so two **different** frequency vectors are orthogonal, because
> they differ on **some** axis and that axis contributes a zero factor. **Orthogonality on one
> axis is enough**, and no distinctness of the box's eigenvalues is used or available.
>
> **`siteVec_dotProduct_self_pos`** — and each mode has strictly positive square norm, so the
> family is an orthogonal basis and not merely a pairwise-orthogonal family that might contain `0`.

## Why `Finset.prod_eq_zero` is the whole of it

Two frequency vectors that differ somewhere differ **on one axis**, and one vanishing factor kills
a product. That is why the repeated eigenvalues are irrelevant here: the argument never compares
eigenvalues at all, only frequencies, and frequencies **are** distinguishable by construction —
`k ≠ l` as functions `Site d n → Site d n`.

## What this is NOT

**No norm is computed.** `siteVec_dotProduct_self_pos` gives positivity and not a value; the
classical `((n+1)/2)^d` is **not** proved here, and as of 31 Aug 2026 no cost is offered for it
(`ERRATUM 194`, `ERRATUM 246`).

**No operator bound follows yet.** Turning an orthogonal eigenbasis into
`x ⬝ᵥ A *ᵥ x ≤ ρ·(x ⬝ᵥ x)` needs the expansion of an arbitrary `x` in this basis and a term-by-term
comparison; **that is a further unit and is not written here.**

**Still the adjacency matrix.** `UNLOCK_WATCHLIST`'s *a BOX is not a circulant* item is blocked on
`GraphLaplacian.massive` = `D − A + m²` with the true degree. **It does not move.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BoxModeOrthogonal

open Finset Matrix BoxGraph BoxGraphSuccIso BoxAdjBasis PathAdjSpectrum

variable {d n : ℕ}

/-! ## 1. The dot product factorises across a product of index types -/

/-- **`(u ⊗ w) ⬝ᵥ (u' ⊗ w') = (u ⬝ᵥ u')·(w ⬝ᵥ w')`.** -/
theorem prodVec_dotProduct {α β : Type*} [Fintype α] [Fintype β]
    (u u' : α → ℝ) (w w' : β → ℝ) :
    BoxProdAdjSpectrum.prodVec u w ⬝ᵥ BoxProdAdjSpectrum.prodVec u' w'
      = (u ⬝ᵥ u') * (w ⬝ᵥ w') := by
  simp only [dotProduct, BoxProdAdjSpectrum.prodVec]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- Relabelling the index type leaves the dot product alone. -/
theorem dotProduct_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : β ≃ α) (v w : α → ℝ) :
    (v ∘ e) ⬝ᵥ (w ∘ e) = v ⬝ᵥ w := by
  simp only [dotProduct, Function.comp_apply]
  exact e.sum_comp fun a => v a * w a

/-! ## 2. The box's pairing is a product of path pairings -/

/-- **ONE FACTOR PER AXIS.** -/
theorem siteVec_dotProduct (d n : ℕ) (k l : Site d n) :
    siteVec d n k ⬝ᵥ siteVec d n l
      = ∏ i, pathVec n ((k i).val + 1) ⬝ᵥ pathVec n ((l i).val + 1) := by
  induction d with
  | zero => simp [siteVec, BoxAdjSpectrum.boxVec, dotProduct]
  | succ d ih =>
      rw [siteVec_succ, siteVec_succ, dotProduct_comp_equiv, prodVec_dotProduct, ih,
        Fin.prod_univ_succ]
      rfl

/-! ## 3. Hence orthogonality, and a nonzero norm -/

/-- **DIFFERENT FREQUENCY VECTORS ARE ORTHOGONAL** — they differ on some axis, and that axis alone
contributes a zero factor (`SymmetricEigenOrthogonal.pathVec_dotProduct_eq_zero`). -/
theorem siteVec_dotProduct_eq_zero {k l : Site d n} (hkl : k ≠ l) :
    siteVec d n k ⬝ᵥ siteVec d n l = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ l i := by
    by_contra hcon
    exact hkl (funext fun i => not_not.1 fun h => hcon ⟨i, h⟩)
  rw [siteVec_dotProduct]
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (SymmetricEigenOrthogonal.pathVec_dotProduct_eq_zero hi)

/-- **AND EVERY MODE HAS STRICTLY POSITIVE SQUARE NORM**, so the family is an orthogonal basis. -/
theorem siteVec_dotProduct_self_pos (hn : 0 < n) (k : Site d n) :
    0 < siteVec d n k ⬝ᵥ siteVec d n k := by
  rw [siteVec_dotProduct]
  refine Finset.prod_pos fun i _ => ?_
  have hne : pathVec n ((k i).val + 1) ≠ 0 :=
    PathAdjBasis.pathVec_ne_zero (Nat.succ_pos _) (k i).isLt hn
  have hnn : (0 : ℝ) ≤ pathVec n ((k i).val + 1) ⬝ᵥ pathVec n ((k i).val + 1) := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exact absurd (dotProduct_self_eq_zero.1 h.symm) hne

end BoxModeOrthogonal
