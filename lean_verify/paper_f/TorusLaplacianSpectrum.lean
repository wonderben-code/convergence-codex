import TorusRegular

/-!
# The eigenvectors of the periodic lattice, in every dimension

`CycleLaplacianSpectrum` computed the spectrum of `massive` on the **ring** — the estate's first
eigenvalue of a graph Laplacian — and `CycleGreenFormula` turned it into a closed-form propagator.
Both are `d = 1`. **This file removes that restriction**, which is the hypothesis the queue's
standing instruction is about and which `WALLS §W2.1` §4 asks for by name: the wall wants `G_n`
*"for the box **or torus** approximants"*, and after `ERRATUM 339` the surviving objection to a
character argument is that a **box** has a boundary and an uneven degree. The **torus** has neither.

> **`cx_massive_mulVec_chiD`** — for every `k`, the product character `χ_k` is an eigenvector of
> `massive (torusGraph d n) m`, with eigenvalue
>
> ```
> ν(k)  =  2d + m²  −  Σ_{i<d} ( ζ^{k_i} + ζ^{−k_i} )  =  2d + m² − 2 Σ_{i<d} cos(2π k_i / n)
> ```
>
> at every side length `n ≥ 3` and in **every dimension**.

**THE WHOLE FILE IS THE NEIGHBOUR SUM, AND THAT IS WHERE THE DIMENSION ENTERS.** `massive` acts by
`(deg p + m²)·x p − Σ_{q ∼ p} x q`, so everything turns on evaluating the sum over neighbours.
`TorusEmbeddingAllDims` supplies the two halves that make the neighbours nameable — every cyclic
step is a neighbour (`stepT_adj`) and the `2d` steps are distinct (`stepT_injective`) — and
`TorusDecay.adjT_eq_stepT` supplies the converse, that every neighbour **is** a step. Together they
give **`neighborFinset_eq_image`**, an identification of the neighbour set with the image of the
`2d` steps, which the degree theorem alone does not give: `torusGraph_degree_eq` counts the
neighbours and does not name them.

**THE PRODUCT CHARACTER FACTORISES ALONG A STEP, WHICH IS WHY THE ONE-DIMENSIONAL LEMMAS SUFFICE.**
`chiD` is a product over the axes of `CycleLaplacianSpectrum.chi`, a step moves exactly one
coordinate (`stepT_apply_of_ne`), and on that coordinate it is `± 1` in `Fin n`
(`stepT_apply_self_true`, `stepT_apply_self_false` — the estate had these only in the `.val` form,
which is not the form `chi_add_one` consumes). So each of the `2d` terms is `χ_k(p)` times a single
root of unity, and no `d`-dimensional Fourier theory appears anywhere.

## What this is NOT

**It is not a diagonalisation, and it is not `G_n`.** An eigenvector family is not a basis until it
is shown to span, and **nothing here shows that** — `CycleGreenFormula.sum_chi_mul_inv` is the
`d = 1` spanning statement and its product analogue is not proved here. **So no entry of
`green (torusGraph d n) m` is computed**, which is exactly the clause `ERRATUM 339` had to correct
in the wall for the one-dimensional case; it is stated here in advance rather than left to go stale.

**And it is not the step.** `WALLS §W2.1` §4's third clause stands untouched: there is no sequence,
no limit, and no `ℤ^d` propagator `G` defined anywhere in this estate. A closed form at each `n`
would still not be a convergence statement, and this is not even a closed form.

**Side length `≥ 3` is a hypothesis and not a convenience.** At `n ≤ 2` the `2d` steps are not
distinct — forward and backward along an axis coincide at `n = 2`, and a step returns to where it
started at `n = 1` — so the neighbour set is smaller than the step image and the sum below counts
terms that are not there. `TorusDecay.torusGraph_degree_le` is an inequality for this reason.

**This is a statement about a MATRIX and its eigenvectors.** No measure appears; `gaussianField` is
not mentioned; and although `FieldIsoInvariance.gaussianField_torus_eq_cycleGraph` does connect the
`d = 1` lattice's *field* to the ring's, nothing here is transported along it. `OS4` does not move
and no published tag moves.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusLaplacianSpectrum

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection CycleLaplacianSpectrum

variable {d n : ℕ}

/-! ## 1. A step is `± 1` on the coordinate it moves -/

/-- A forward step adds one, in `Fin` arithmetic. The estate has this in the `.val` form
(`TorusEmbeddingAllDims.val_stepT_true`); `chi_add_one` consumes the `Fin` form. -/
theorem stepT_apply_self_true (N : ℕ) (p : Site d (N + 3)) (i : Fin d) :
    TorusDecay.stepT p i true i = p i + 1 := by
  refine Fin.ext ?_
  rw [TorusEmbeddingAllDims.val_stepT_true, Fin.val_add]
  have hlt := (p i).isLt
  have hone : (1 : Fin (N + 3)).val = 1 := by simp
  rw [hone]
  by_cases hw : (p i).val + 1 = N + 3
  · simp [hw]
  · rw [if_neg hw, Nat.mod_eq_of_lt (by omega : (p i).val + 1 < N + 3)]

/-- A backward step subtracts one, in `Fin` arithmetic. -/
theorem stepT_apply_self_false (N : ℕ) (p : Site d (N + 3)) (i : Fin d) :
    TorusDecay.stepT p i false i = p i - 1 := by
  have hround : TorusDecay.stepT (TorusDecay.stepT p i false) i true = p := by
    funext j
    by_cases hj : j = i
    · subst hj
      refine Fin.ext ?_
      rw [TorusEmbeddingAllDims.val_stepT_true, TorusEmbeddingAllDims.val_stepT_false]
      have hlt := (p j).isLt
      split_ifs <;> omega
    · rw [TorusEmbeddingAllDims.stepT_apply_of_ne _ hj,
        TorusEmbeddingAllDims.stepT_apply_of_ne _ hj]
  have h := stepT_apply_self_true N (TorusDecay.stepT p i false) i
  rw [hround] at h
  rw [h]
  exact (add_sub_cancel_right _ _).symm

/-! ## 2. The neighbours of a site, named rather than counted -/

/-- **THE NEIGHBOUR SET IS THE IMAGE OF THE `2d` STEPS.** `torusGraph_degree_eq` counts the
neighbours; this names them, which is what a sum over them needs. -/
theorem neighborFinset_eq_image (hn : 3 ≤ n) (p : Site d n) :
    (torusGraph d n).neighborFinset p
      = Finset.image (fun t : Fin d × Bool => TorusDecay.stepT p t.1 t.2) Finset.univ := by
  ext q
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro h
    obtain ⟨t, ht⟩ := TorusDecay.adjT_eq_stepT h
    exact ⟨t, ht.symm⟩
  · rintro ⟨t, rfl⟩
    exact TorusEmbeddingAllDims.stepT_adj hn p t.1 t.2

/-! ## 3. The product character -/

/-- The character of the periodic lattice at frequency `k`: a product of the ring's characters,
one per axis. -/
noncomputable def chiD (n : ℕ) (k p : Site d n) : ℂ := ∏ i : Fin d, chi n (k i) (p i)

theorem chiD_ne_zero (n : ℕ) (k p : Site d n) : chiD n k p ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => chi_ne_zero n (k i) (p i)

/-- The factors away from the moved axis are untouched, which is the only thing the product
structure is used for. -/
theorem prod_erase_stepT (N : ℕ) (k p : Site d (N + 3)) (i : Fin d) (b : Bool) :
    (∏ j ∈ Finset.univ.erase i, chi (N + 3) (k j) (TorusDecay.stepT p i b j))
      = ∏ j ∈ Finset.univ.erase i, chi (N + 3) (k j) (p j) :=
  Finset.prod_congr rfl fun j hj => by
    rw [TorusEmbeddingAllDims.stepT_apply_of_ne _ (Finset.ne_of_mem_erase hj)]

/-- **A FORWARD STEP MULTIPLIES THE CHARACTER BY ONE ROOT OF UNITY.** -/
theorem chiD_stepT_true (N : ℕ) (k p : Site d (N + 3)) (i : Fin d) :
    chiD (N + 3) k (TorusDecay.stepT p i true)
      = zeta (N + 3) ^ (k i).val * chiD (N + 3) k p := by
  rw [chiD, chiD, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), prod_erase_stepT,
    stepT_apply_self_true, chi_add_one]
  ring

/-- **AND A BACKWARD STEP BY ITS INVERSE.** -/
theorem chiD_stepT_false (N : ℕ) (k p : Site d (N + 3)) (i : Fin d) :
    chiD (N + 3) k (TorusDecay.stepT p i false)
      = (zeta (N + 3) ^ (k i).val)⁻¹ * chiD (N + 3) k p := by
  rw [chiD, chiD, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), prod_erase_stepT,
    stepT_apply_self_false, chi_sub_one]
  ring

/-! ## 4. The eigenvector equation -/

/-- The eigenvalue at frequency `k`, as a sum of one term per axis. -/
noncomputable def nu (N : ℕ) (m : ℝ) (k : Site d (N + 3)) : ℂ :=
  (2 * d + (m : ℂ) ^ 2)
    - ∑ i : Fin d, (zeta (N + 3) ^ (k i).val + (zeta (N + 3) ^ (k i).val)⁻¹)

/-- **THE PRODUCT CHARACTERS ARE EIGENVECTORS OF THE PERIODIC LATTICE, IN EVERY DIMENSION.** -/
theorem cx_massive_mulVec_chiD (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    MatrixLoewner.cx (massive (torusGraph d (N + 3)) m) *ᵥ chiD (N + 3) k
      = nu N m k • chiD (N + 3) k := by
  classical
  have hn : 3 ≤ N + 3 := by omega
  funext p
  rw [cx_massive_mulVec, neighborFinset_eq_image hn p,
    Finset.sum_image fun t _ t' _ h => TorusEmbeddingAllDims.stepT_injective hn p h]
  have hdeg : ((torusGraph d (N + 3)).degree p : ℂ) = 2 * d := by
    rw [TorusEmbeddingAllDims.torusGraph_degree_eq hn p]
    push_cast; ring
  have hsum : (∑ t : Fin d × Bool, chiD (N + 3) k (TorusDecay.stepT p t.1 t.2))
      = (∑ i : Fin d, (zeta (N + 3) ^ (k i).val + (zeta (N + 3) ^ (k i).val)⁻¹))
          * chiD (N + 3) k p := by
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool, chiD_stepT_true, chiD_stepT_false]
    ring
  rw [hdeg, hsum, Pi.smul_apply, smul_eq_mul, nu]
  ring

/-- One axis's contribution is real: a root of unity plus its inverse is twice a cosine. The
`d = 1` file proves this inside `eigenvalue_eq_real`; here it is needed one axis at a time. -/
theorem zeta_pow_add_inv (N : ℕ) (a : Fin (N + 3)) :
    zeta (N + 3) ^ a.val + (zeta (N + 3) ^ a.val)⁻¹
      = ((2 * Real.cos (2 * Real.pi * a.val / ((N : ℝ) + 3)) : ℝ) : ℂ) := by
  rw [zeta_pow_eq_exp, ← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

/-- **THE EIGENVALUE IS REAL**, and is `2d + m² − 2 Σᵢ cos(2π kᵢ / n)` — one cosine per axis, which
is the `d = 1` formula with a sum in place of its single term. -/
theorem nu_eq_real (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    nu N m k
      = ((2 * d + m ^ 2
          - ∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3)) : ℝ) : ℂ) := by
  rw [nu, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => zeta_pow_add_inv N (k i)]
  push_cast
  ring

/-- **THE `d = 1` CASE IS THE RING'S EIGENVALUE, LITERALLY** — a generalisation is instantiated,
not merely asserted to specialise (`ERRATUM 201`). This is a statement about `nu` alone: it does
**not** transport the eigenvector equation along `TorusCycleGraph.torusGraph_one_iso`, which is a
separate step and is not taken here. -/
theorem nu_one (N : ℕ) (m : ℝ) (k : Site 1 (N + 3)) :
    nu N m k
      = (2 + (m : ℂ) ^ 2) - (zeta (N + 3) ^ (k 0).val + (zeta (N + 3) ^ (k 0).val)⁻¹) := by
  rw [nu, Fin.sum_univ_one]
  push_cast
  ring

end TorusLaplacianSpectrum
