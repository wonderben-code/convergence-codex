import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Algebraic curvature tensors, their two traces, and a witness

`WALLS.md` W5 (Einstein equations from the spectral action) records **no staircase climbed at
all**, and names its own first move:

> *"either serious Riemannian-geometry Mathlib development (outside this campaign's reach) or
> the algebraic Lovelock stair — which IS a bounded build and is the honest first move if this
> wall is ever attacked."*

Its failing step is *"the estate has no formal object for `a₂`"*, and two dated notes on that
wall exist only to stop a reader inferring otherwise from the names `SpectralAction.lean` and
`F3_10a_HeatKernelCanonicity.lean`. This file is the first rung of the stair W5 names: the
**object** in whose vocabulary the algebraic part of `a₂` is written.

> **`IsAlgCurv`** — a four-index array with the curvature symmetries: antisymmetric in the first
> pair, antisymmetric in the second, symmetric under exchanging the pairs, and satisfying the
> first Bianchi identity.
>
> **`ricci`** and **`scal`** — its two traces, contracted with the Euclidean metric in an
> orthonormal frame, so the metric is `δ` and the contraction is a plain sum.
>
> **`ricci_symm`** — the Ricci trace is symmetric. Both antisymmetries and the pair symmetry are
> used; none of them is decorative.
>
> **`constCurv`** and its lemmas — the constant-curvature tensor `δ_{ad}δ_{bc} − δ_{ac}δ_{bd}`
> **satisfies every clause**, with `ricci = (n−1)·δ` and `scal = n(n−1)`.
>
> **`scal_constCurv_pos`** — and it is **not the zero tensor** for `n ≥ 2`. That theorem is the
> one that makes the witness worth anything: `R = 0` satisfies all four clauses, so exhibiting
> *a* witness establishes nothing at all. `IsMirrorHalf` sat in this estate for a week with only
> the trivial witness, and the file that noticed said so; this one is checked rather than
> assumed.

## Why components rather than multilinear maps

`IsAlgCurv` is stated on `Fin n → Fin n → Fin n → Fin n → ℝ`, i.e. on **components in an
orthonormal frame**, not on a multilinear map over a vector space. That is deliberate and it is a
restriction: multilinearity is then automatic and the metric is `δ`, at the cost of fixing a
frame. Every statement below is therefore a statement about a frame, and the frame-independence
that a geometric treatment would need is **not proved and not claimed**.

## What this is NOT, and the gap is not narrowed by it

**This is not `a₂`, and it is not a step toward `a₂` that shortens the wall.** `a₂` is a
heat-kernel coefficient in the asymptotic expansion of `Tr f(D/Λ)` as `Λ → ∞` **on a manifold**.
There is no manifold here, no connection, no covariant derivative and no heat kernel; there is a
four-index array of reals with four symmetry clauses. What this supplies is the vocabulary —
Ricci, scalar — in which the algebraic part of `a₂` is *written down*, which W5 says the estate
did not have.

**The Lovelock classification itself is not attempted.** The algebraic content of Lovelock's
theorem is that the `O(n)`-equivariant linear maps from algebraic curvature tensors to symmetric
2-tensors are spanned by `R ↦ Ric` and `R ↦ scal · δ`. That is invariant theory, it needs the
group action written down and a Schur-type argument, and **nothing here begins it**. It is not
stated as a `def` either: `ERRATUM 108` refuted a gap object of this project that nobody had
tried to falsify, and naming this one before its small cases have been read would repeat that.

**Mathlib has none of this, probed 2026-08-11 by shape and not by name.** `RicciTensor`,
`ScalarCurvature`, `AlgebraicCurvature`, `sectionalCurvature`: **zero files each**. `Riemann`
matches 28 files and *none of them is geometry* — six are L-series, five box integrals, three
complex analysis, two modular forms; only three are under `Geometry/Manifold` and those are
`RiemannianMetric`. The single file matching `curvature` is
`MeasureTheory/Measure/Doubling.lean`, which is not this. The estate's own two `Ricci` mentions
are both prose: a docstring in `BakryEmeryGap.lean` and a comment in
`F3_8b_SpectralActionComputation.lean`.
-/

namespace AlgebraicCurvature

open Finset

variable {n : ℕ}

/-! ## 1. The object -/

/-- **An algebraic curvature tensor**, in components in an orthonormal frame: antisymmetric in
the first pair, antisymmetric in the second, symmetric under exchange of the pairs, and
satisfying the first Bianchi identity. -/
structure IsAlgCurv (R : Fin n → Fin n → Fin n → Fin n → ℝ) : Prop where
  /-- Antisymmetry in the first two slots. -/
  antisymm_left : ∀ a b c d, R a b c d = -R b a c d
  /-- Antisymmetry in the last two slots. -/
  antisymm_right : ∀ a b c d, R a b c d = -R a b d c
  /-- Symmetry under exchanging the two pairs. -/
  pair_symm : ∀ a b c d, R a b c d = R c d a b
  /-- The first Bianchi identity. -/
  bianchi : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0

/-! ## 2. The two traces

In an orthonormal frame the metric is `δ`, so contracting is summing a repeated index. -/

/-- **The Ricci trace**, `Ric b c = ∑ₐ R a b c a`. -/
def ricci (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) : ℝ := ∑ a, R a b c a

/-- **The scalar curvature**, the trace of `ricci`. -/
def scal (R : Fin n → Fin n → Fin n → Fin n → ℝ) : ℝ := ∑ b, ricci R b b

/-- **THE RICCI TRACE IS SYMMETRIC.** All three of the symmetry clauses are used: the pair
symmetry moves `R a b c a` to `R c a a b`, and the two antisymmetries bring it back to
`R a c b a`, which is the other trace term. -/
theorem ricci_symm {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R) (b c : Fin n) :
    ricci R b c = ricci R c b := by
  refine Finset.sum_congr rfl fun a _ => ?_
  calc R a b c a = R c a a b := hR.pair_symm a b c a
    _ = -R a c a b := hR.antisymm_left c a a b
    _ = -(-R a c b a) := by rw [hR.antisymm_right a c a b]
    _ = R a c b a := neg_neg _

/-! ## 3. A witness, so the structure is not vacuous

`IsMirrorHalf` spent a week in this estate with only the trivial witness, and the file that
noticed said so. A structure with four clauses deserves an instance before anything is proved
about it in general — **and the instance has to be checked for being non-trivial, because the
zero tensor satisfies every clause here.** `scal_constCurv_pos` is that check. -/

/-- The Kronecker delta of the orthonormal frame — the metric, in components. -/
def delta (a b : Fin n) : ℝ := if a = b then 1 else 0

@[simp] theorem delta_self (a : Fin n) : delta a a = 1 := by simp [delta]

theorem delta_symm (a b : Fin n) : delta a b = delta b a := by
  simp only [delta]; by_cases h : a = b <;> simp [h, eq_comm]

/-- Contracting two deltas over a shared index leaves one. -/
theorem sum_delta_mul (b c : Fin n) : ∑ a, delta a c * delta b a = delta b c := by
  rw [Finset.sum_eq_single c]
  · simp [delta_self]
  · intro x _ hx; simp [delta, hx]
  · intro hc; exact absurd (Finset.mem_univ c) hc

/-- **The constant-curvature tensor**, `δ_{ad} δ_{bc} − δ_{ac} δ_{bd}`. -/
def constCurv (n : ℕ) (a b c d : Fin n) : ℝ := delta a d * delta b c - delta a c * delta b d

/-- **IT SATISFIES EVERY CLAUSE.** With the metric written as `delta`, the two antisymmetries are
pure `ring` identities in the four products; the pair symmetry and Bianchi need only that `delta`
is symmetric, and then also close by `ring`. No case analysis anywhere. -/
theorem isAlgCurv_constCurv (n : ℕ) : IsAlgCurv (constCurv n) where
  antisymm_left a b c d := by simp only [constCurv]; ring
  antisymm_right a b c d := by simp only [constCurv]; ring
  pair_symm a b c d := by
    simp only [constCurv]
    rw [delta_symm c b, delta_symm d a, delta_symm c a, delta_symm d b]; ring
  bianchi a b c d := by
    simp only [constCurv]
    rw [delta_symm c a, delta_symm b a, delta_symm c b]; ring

/-- **ITS RICCI TRACE IS `(n − 1) δ`.** The `n` is the diagonal `δ_{aa}` summed over the frame;
the `−1` is the contracted pair of deltas. -/
theorem ricci_constCurv (n : ℕ) (b c : Fin n) :
    ricci (constCurv n) b c = ((n : ℝ) - 1) * delta b c := by
  simp only [ricci, constCurv, delta_self, one_mul]
  rw [Finset.sum_sub_distrib, sum_delta_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **AND ITS SCALAR CURVATURE IS `n (n − 1)`.** -/
@[simp]
theorem scal_constCurv (n : ℕ) : scal (constCurv n) = (n : ℝ) * ((n : ℝ) - 1) := by
  simp only [scal, ricci_constCurv, delta_self, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- **THE WITNESS IS NOT THE ZERO TENSOR**, for `n ≥ 2`. Without this the witness above would be
worth nothing: `R = 0` satisfies all four clauses of `IsAlgCurv`, so a structure of this shape is
*always* inhabited and inhabitation alone is no evidence that the clauses are consistent with
curvature actually being present. -/
theorem scal_constCurv_pos {n : ℕ} (hn : 2 ≤ n) : 0 < scal (constCurv n) := by
  rw [scal_constCurv]
  have h1 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith

/-- Hence `constCurv n` is not identically zero for `n ≥ 2`. -/
theorem constCurv_ne_zero {n : ℕ} (hn : 2 ≤ n) : constCurv n ≠ fun _ _ _ _ => (0 : ℝ) := by
  intro h
  have := scal_constCurv_pos hn
  rw [h] at this
  simp [scal, ricci] at this

/-! ## 4. What no theorem here uses

**`bianchi` is not consumed by anything in this file.** `ricci_symm` uses the pair symmetry and
both antisymmetries; the witness lemmas verify Bianchi but nothing downstream reads it. It is in
the structure because an algebraic curvature tensor has it, not because a proof below needs it,
and a reader should not infer that the clause is load-bearing here. It becomes load-bearing in
the classification this file does not attempt. -/

end AlgebraicCurvature
