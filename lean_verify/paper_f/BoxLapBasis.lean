import BoxLapSpectrum
import ProdVecIndependent
import SignlessTorusComplete
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The box's free-boundary Laplacian modes are a basis, so that spectrum is complete

`BoxLapSpectrum` diagonalised `L_{boxGraph d n}` by half-step cosines and closed on one question,
the same one `BoxAdjSpectrum` closed on: are the `n^d` modes **all** of them? It also recorded why
the cheap answer is unavailable — at `d = 1` the eigenvalues `2 − 2cos(kπ/n)` are distinct, but at
`d ≥ 2` the sums repeat, `(1,2)` and `(2,1)` giving the same value. This file answers it, and the
route is the one that worked for the adjacency matrix.

> **`cosMode_linearIndependent`** — at `d = 1` the `n` modes are independent, and here the
> **distinct-eigenvalue** route does work: `2 − 2cos(kπ/n)` is injective on `k = 0 … n−1` because
> those angles lie in `[0, π)` and `Real.injOn_cos` is injective there.
>
> **`siteLapVec_linearIndependent`** — hence, by the product-of-bases argument and an induction on
> the dimension, the `n^d` box modes are independent.
>
> **`boxLapBasis`** — so they are a **basis** of `Site d n → ℝ`, indexed by the box's own sites.
>
> **`lapEigenvalue_iff`** — and therefore a real `μ` is an eigenvalue of `L_{boxGraph d n}`
> **iff**
> `μ = ∑ᵢ (2 − 2cos(kᵢπ/n))` for some frequency vector with each `kᵢ` in `0 … n−1`. **There are no
> others.**

## What this is NOT

**It is not `massive`.** `GraphLaplacian.massive` is `L + m²`, so every eigenvalue shifts by `m²`
and every eigenvector is unchanged. **That shift is not stated here**, and until it is,
`UNLOCK_WATCHLIST`'s *a BOX is not a circulant* item is not closed — the item is about the estate's
own operator. As of 31 Aug 2026 the shift is not costed (`ERRATUM 194`, `ERRATUM 246`).

**No multiplicity is computed.** Which frequency vectors share an eigenvalue is not asked here, and
`TorusNonReflectionCollision` shows on the torus that the answer is not the obvious one.

**No orthogonality.** `BoxModeOrthogonal` does that for the adjacency modes; nothing here repeats it
for these, and no operator norm bound is drawn.

**The item's sentence remains true.** No character is an eigenvector; these modes are
non-characters. The obstruction is routed around, not refuted.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BoxLapBasis

open Finset Matrix SimpleGraph BoxGraph BoxGraphSuccIso PathLapSpectrum BoxLapSpectrum

variable {d m : ℕ}

/-! ## 1. The one-dimensional modes are independent -/

/-- `2·half (m+1) k` is the angle `kπ/(m+1)`. -/
theorem two_half (m k : ℕ) :
    2 * half (m + 1) k = (k : ℝ) * Real.pi / ((m : ℝ) + 1) := by
  have h2 : (2 : ℝ) * ((m : ℝ) + 1) ≠ 0 := by positivity
  rw [half]
  push_cast
  field_simp

theorem angle_mem (m : ℕ) (k : Fin (m + 1)) :
    2 * half (m + 1) k.val ∈ Set.Icc 0 Real.pi := by
  rw [two_half]
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hk : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
  have hkm : (k.val : ℝ) ≤ (m : ℝ) := by
    have : k.val ≤ m := Nat.lt_succ_iff.1 k.isLt
    exact_mod_cast this
  constructor
  · positivity
  · rw [div_le_iff₀ hm]
    nlinarith [Real.pi_pos]

/-- **THE `d = 1` EIGENVALUES ARE DISTINCT**, because the angles lie in `[0, π]` where cosine is
injective. -/
theorem lapEigenvalue_injective (m : ℕ) :
    Function.Injective fun k : Fin (m + 1) => 2 - 2 * Real.cos (2 * half (m + 1) k.val) := by
  intro a b hab
  simp only [sub_right_inj, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at hab
  have hcos := Real.injOn_cos (angle_mem m a) (angle_mem m b) hab
  rw [two_half, two_half] at hcos
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp at hcos
  exact Fin.ext (by exact_mod_cast hcos)

theorem hasEigenvector_cosMode (m : ℕ) (k : Fin (m + 1)) :
    Module.End.HasEigenvector (Matrix.mulVecLin ((pathGraph (m + 1)).lapMatrix ℝ))
      (2 - 2 * Real.cos (2 * half (m + 1) k.val)) (cosMode (m + 1) k.val) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact lapMatrix_mulVec_cosMode m k.val
  · intro hcon
    have h := congrFun hcon (⟨0, Nat.succ_pos m⟩ : Fin (m + 1))
    have hpos := cosMode_corner_pos (n := m + 1) (k := k.val) (Nat.succ_pos m) k.isLt
    rw [h] at hpos
    exact lt_irrefl 0 hpos

/-- **THE PATH'S `n` COSINE MODES ARE INDEPENDENT.** -/
theorem cosMode_linearIndependent (m : ℕ) :
    LinearIndependent ℝ fun k : Fin (m + 1) => cosMode (m + 1) k.val :=
  Module.End.eigenvectors_linearIndependent' _ _ (lapEigenvalue_injective m) _
    (hasEigenvector_cosMode m)

/-! ## 2. The box's modes, indexed by its own sites -/

/-- The mode at a site-indexed frequency: coordinate `kᵢ` names the frequency `kᵢ`, so the `n`
frequencies used on each axis are `0 … n−1` — exactly §1's range. -/
noncomputable def siteLapVec (d n : ℕ) (k : Site d n) : Site d n → ℝ :=
  boxLapVec d n fun i => (k i).val

theorem siteLapVec_succ (d m : ℕ) (k : Site (d + 1) (m + 1)) :
    siteLapVec (d + 1) (m + 1) k
      = (BoxProdAdjSpectrum.prodVec (cosMode (m + 1) (k 0).val)
          (siteLapVec d (m + 1) (Fin.tail k))) ∘ (boxGraph_succ_iso d (m + 1)).symm := by
  funext p
  simp only [siteLapVec, boxLapVec, BoxProdAdjSpectrum.prodVec, Fin.prod_univ_succ, Fin.tail,
    Function.comp_apply]
  rfl

/-- **THE `n^d` BOX MODES ARE INDEPENDENT.** -/
theorem siteLapVec_linearIndependent (m d : ℕ) :
    LinearIndependent ℝ (siteLapVec d (m + 1)) := by
  induction d with
  | zero =>
      refine LinearIndependent.of_subsingleton (default : Site 0 (m + 1)) ?_
      intro hcon
      have h := congrFun hcon (default : Site 0 (m + 1))
      simp [siteLapVec, boxLapVec] at h
  | succ d ih =>
      have hprod := ProdVecIndependent.prodVec_linearIndependent
        (cosMode_linearIndependent m) ih
      have hdom := ProdVecIndependent.linearIndependent_comp_equiv
        (v := fun p : Fin (m + 1) × Site d (m + 1) =>
          BoxProdAdjSpectrum.prodVec (cosMode (m + 1) p.1.val) (siteLapVec d (m + 1) p.2))
        (consSite d (m + 1)).symm hprod
      have hidx := hdom.comp (consSite d (m + 1)).symm (Equiv.injective _)
      have hfam : ((fun p : Fin (m + 1) × Site d (m + 1) =>
          BoxProdAdjSpectrum.prodVec (cosMode (m + 1) p.1.val) (siteLapVec d (m + 1) p.2)
            ∘ (consSite d (m + 1)).symm) ∘ (consSite d (m + 1)).symm)
          = siteLapVec (d + 1) (m + 1) := by
        funext k
        rw [siteLapVec_succ]
        exact rfl
      rwa [hfam] at hidx

/-! ## 3. The basis, and the complete spectrum -/

/-- **THE BOX'S LAPLACIAN MODES, AS A BASIS INDEXED BY ITS OWN SITES.** -/
noncomputable def boxLapBasis (d m : ℕ) :
    Module.Basis (Site d (m + 1)) ℝ (Site d (m + 1) → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank (siteLapVec_linearIndependent m d) (by simp)

theorem boxLapBasis_apply (d m : ℕ) (k : Site d (m + 1)) :
    boxLapBasis d m k = siteLapVec d (m + 1) k :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) k

theorem lapMatrix_mulVec_siteLapVec (d m : ℕ) (k : Site d (m + 1)) :
    (boxGraph d (m + 1)).lapMatrix ℝ *ᵥ siteLapVec d (m + 1) k
      = boxLapEig d (m + 1) (fun i => (k i).val) • siteLapVec d (m + 1) k :=
  lapMatrix_mulVec_boxLapVec m d _

/-- **THE BOX'S FREE-BOUNDARY LAPLACIAN SPECTRUM, EXACTLY.**

**Named `lapEigenvalue_iff` and not `eigenvalue_iff`**, which is taken twice already and once on
**this very graph**: `BoxSpectrumComplete.eigenvalue_iff` is the box's **adjacency** spectrum over
`ℝ`, and `SignlessTorusComplete.eigenvalue_iff` the torus's signless Laplacian over `ℂ`. The first
of those differs from this one **only** in `adjMatrix` versus `lapMatrix`, which is the whole
subject of this sequence and far too easy to misread from a name alone (`newnames_scan`,
31 Aug 2026). -/
theorem lapEigenvalue_iff (d m : ℕ) (μ : ℝ) :
    (∃ x : Site d (m + 1) → ℝ, x ≠ 0 ∧ (boxGraph d (m + 1)).lapMatrix ℝ *ᵥ x = μ • x)
      ↔ ∃ k : Site d (m + 1), boxLapEig d (m + 1) (fun i => (k i).val) = μ :=
  SignlessTorusComplete.eigenvalue_iff_of_basis _ (boxLapBasis d m)
    (fun k => boxLapEig d (m + 1) fun i => (k i).val)
    (fun k => by rw [boxLapBasis_apply]; exact lapMatrix_mulVec_siteLapVec d m k) μ

end BoxLapBasis
