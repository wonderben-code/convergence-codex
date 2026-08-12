import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.UnitaryGroup

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
>
> **`pair_symm_of_bianchi`** (§5) — **one of the four clauses is redundant.** The two
> antisymmetries and the first Bianchi identity imply the pair symmetry, by way of
> `bianchi_alt_sum`, which is the cancellation identity behind it stated as a theorem rather than
> as an explanation. `IsAlgCurv.mk'` is the three-clause constructor that follows.
>
> **`bianchi_not_implied`** (§6) — **and no other clause is.** `ω ⊗ ω` for the standard symplectic
> form on `Fin 4` satisfies both antisymmetries and the pair symmetry and fails Bianchi. The
> dimension is forced downward as far as this file can force it: `eq_zero_of_le_one` rules out
> `n ≤ 1` and `bianchi_of_antisymm_two` rules out `n = 2`; `n = 3` is open here and said to be.
>
> **`antisymm_left_not_implied`** (§10) — **and the dependency picture is complete.** The left
> antisymmetry does not follow from the right one and Bianchi either; the witness is three entries
> on `Fin 3`, and `antisymm_left_of_two` proves `Fin 3` minimal. So of the four clauses **exactly
> one is redundant — the pair symmetry — and only in the presence of both antisymmetries.**
>
> **`ricciG`, `scalG`, `ricciG_symm`** (§9) — the orthonormal frame comes off. The two traces
> contract against an **arbitrary** metric and the symmetry of the Ricci trace needs only that the
> metric is symmetric; `ricciG_delta` and `scalG_delta` recover §2 as the `δ` case.
>
> **`traces_independent`, `traces_dependent_two`** (§11) — the small cases of W5's Lovelock item,
> read rather than guessed. The two maps that item names, `R ↦ Ric` and `R ↦ scal · δ`, are
> **linearly independent from dimension three up and proportional at dimension two**, so they are a
> basis of their span only for `n ≥ 3`. The separating witness is `knSquare (projOff k)`, whose
> Ricci trace is `(n−2)` times a *projector*; `isAlgCurv_knSquare` builds it by removing `δ` from
> §3's witness, and `knSquare_delta` is the `rfl` that keeps `constCurv` as the special case.
> **The spanning half of the classification is not begun.**
>
> **`traces_equivariant`** (§12) — the membership check §11 skipped. §11 proved the two maps
> independent inside a family it never showed either belonged to; `act` is the change of frame,
> `IsOrth` is orthogonality (derived from **Mathlib's** `Matrix.orthogonalGroup` by
> `isOrth_of_mem_orthogonalGroup`, with two distinct witnesses), `isAlgCurv_act` shows the space of
> algebraic curvature tensors is invariant, and `ricci_act` / `scal_act` / `act2_delta` show both
> maps commute with the frame change.
>
> **`lovelock_two`** (§13) — **and in dimension two the item is COMPLETE, both halves.** Any
> homogeneous `O(2)`-equivariant map out of algebraic curvature tensors is a multiple of
> `R ↦ scal R · δ`, so the family has no members outside the span of the two named maps. Three
> facts make it affordable and none survives to `n ≥ 3`: the domain is a line, the generator is
> fixed by the group (`act_constCurv`, §14, which holds in every dimension), and
> **`eq_smul_delta_of_invariant`** — an invariant
> 2-tensor is a multiple of the metric, by reflections and transpositions alone, with no averaging.
> `lovelock_two_ricci` checks the hypotheses are met by `Ric` itself and recovers §11's constant
> `½` through the new machinery. **For `n ≥ 3` the spanning half is untouched.**

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

**Mathlib has no curvature, probed 2026-08-11 by shape and not by name.** `RicciTensor`,
`ScalarCurvature`, `AlgebraicCurvature`, `sectionalCurvature`, `RiemannCurvature`,
`CurvatureTensor`, `covariantDerivative`, `LeviCivita`, `EinsteinTensor`, `Lovelock`,
`HeatKernel`: **zero files each**. Across all of Mathlib, **exactly one file matches `curvature`
case-insensitively** and it is `MeasureTheory/Measure/Doubling.lean`, which is not this. Inside
`Geometry/`, `curvature`, `Christoffel`, `geodesic`, `parallelTransport` and `Levi` are all zero,
and every match for `Connection` is `GaloisConnection`. The estate's own two `Ricci` mentions are
both prose: a docstring in `BakryEmeryGap.lean` and a comment in
`F3_8b_SpectralActionComputation.lean`.

**WHAT MATHLIB DOES HAVE, and an earlier draft of this paragraph got it wrong.** That draft read
*"`Riemann` matches 28 files and none of them is geometry … only three are under
`Geometry/Manifold` and those are `RiemannianMetric`"*, which is self-contradictory and false in
its first clause. Three of the 28 **are** geometry, and reading them rather than their titles
shows a substantial Riemannian metric layer: `Topology/VectorBundle/Riemannian.lean`
(`RiemannianMetric`, `ContinuousRiemannianMetric`, `RiemannianBundle`),
`Geometry/Manifold/VectorBundle/Riemannian.lean` (`ContMDiffRiemannianMetric`) and
`Geometry/Manifold/Riemannian/` (`IsRiemannianManifold`, path length, and the induced extended
metric). `Geometry/Manifold/VectorField/LieBracket.lean` supplies `mlieBracket`.

So the honest boundary is one layer up from where that draft put it: **Mathlib has metrics and the
Lie bracket, and no connection.** Curvature is defined in terms of the connection —
`R(X,Y)Z = ∇_X∇_Y Z − ∇_Y∇_X Z − ∇_{[X,Y]}Z` — so two of those three ingredients exist and the
middle one does not. None of that changes what this file is: `IsAlgCurv` is components in a frame
with no manifold anywhere near it, and it connects to none of those declarations.
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

/-- **A delta under a sum is an evaluation:** `∑ₐ δ_{ac} f a = f c`, for an arbitrary `f`. Stated
in this generality because §11 contracts a delta against something that is not another delta; the
next lemma, which is all §§3 and 9 need, is its `f = δ_{b·}` case and is now that case rather than
a second proof of the same three-line argument. -/
theorem sum_delta_left (c : Fin n) (f : Fin n → ℝ) : ∑ a, delta a c * f a = f c := by
  rw [Finset.sum_eq_single c]
  · simp [delta_self]
  · intro x _ hx; simp [delta, hx]
  · intro hc; exact absurd (Finset.mem_univ c) hc

/-- Contracting two deltas over a shared index leaves one. -/
theorem sum_delta_mul (b c : Fin n) : ∑ a, delta a c * delta b a = delta b c :=
  sum_delta_left c fun a => delta b a

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

/-! ## 4. What no theorem here uses — **SUPERSEDED BY §5, and kept as written**

> **`bianchi` is not consumed by anything in this file.** `ricci_symm` uses the pair symmetry and
> both antisymmetries; the witness lemmas verify Bianchi but nothing downstream reads it. It is in
> the structure because an algebraic curvature tensor has it, not because a proof below needs it,
> and a reader should not infer that the clause is load-bearing here. It becomes load-bearing in
> the classification this file does not attempt.

That paragraph was true of §§1–3 and is **false of the file as it now stands**: `bianchi` is what
proves the pair symmetry in §5, so it is load-bearing here after all, and the classification is not
where it first earns its place. It is quoted rather than deleted because the observation is what
produced §5 — noticing a clause was inert is what made asking *which clauses are inert* the next
question, and the answer turned out to be a theorem rather than a note.

## 5. Which of the four clauses are load-bearing

The question §4 raised, asked properly. Three of the four dependencies among the clauses are
settled below and the fourth — whether `bianchi` follows from the rest — is settled in §6, in the
negative, by a witness. -/

section Dependencies

variable {R : Fin n → Fin n → Fin n → Fin n → ℝ}

/-- A slot repeated across an antisymmetric pair kills the tensor: `R a a c d = 0`. -/
theorem diag_left_eq_zero (hL : ∀ a b c d, R a b c d = -R b a c d) (a c d : Fin n) :
    R a a c d = 0 := by
  have h := hL a a c d
  linarith

/-- The same on the right: `R a b c c = 0`. **Used by nothing below** — it is the mirror of
`diag_left_eq_zero` and is here because a vocabulary file that carries one half of a symmetric pair
and not the other is a nuisance downstream. Said explicitly, because §4 is what this file thinks of
declarations whose role a reader might over-read. -/
theorem diag_right_eq_zero (hR : ∀ a b c d, R a b c d = -R a b d c) (a b c : Fin n) :
    R a b c c = 0 := by
  have h := hR a b c c
  linarith

/-- **THE IDENTITY BEHIND THE NEXT THEOREM, PROVED RATHER THAN ASSERTED.** Writing `B(x,y,z,w)`
for the Bianchi sum `R x y z w + R y z x w + R z x y w`,

`B(a,b,c,d) − B(a,b,d,c) − B(a,c,d,b) + B(b,c,d,a) = 2 (R a b c d − R c d a b)`

**using only the two antisymmetries.** Ten of the twelve terms on the left cancel in pairs and the
remaining two double. This was the file's explanation of `pair_symm_of_bianchi`, sitting in a
docstring where nothing checked it; it is a theorem now, so the explanation and the proof are the
same object. -/
theorem bianchi_alt_sum
    (hL : ∀ a b c d, R a b c d = -R b a c d)
    (hR : ∀ a b c d, R a b c d = -R a b d c)
    (a b c d : Fin n) :
    (R a b c d + R b c a d + R c a b d) - (R a b d c + R b d a c + R d a b c)
      - (R a c d b + R c d a b + R d a c b) + (R b c d a + R c d b a + R d b c a)
      = 2 * (R a b c d - R c d a b) := by
  have e1 := hR a b c d
  have e2 := hR b c a d
  have e3 := hL a c d b
  have e4 := hR c a b d
  have e5 := hR d a b c
  have e6 := hR c d a b
  have e7 := hL d b c a
  have e8 := hR b d a c
  linarith

/-- **THE PAIR SYMMETRY IS NOT AN INDEPENDENT ASSUMPTION.** The two antisymmetries and the first
Bianchi identity imply it: the left-hand side of `bianchi_alt_sum` is a signed sum of four Bianchi
sums, so it vanishes, and its right-hand side is `2 (R a b c d − R c d a b)`.

This is the classical fact that the four symmetries of a Riemann tensor are one redundant. It is
also what makes the `bianchi` clause load-bearing in this file — see §4. -/
theorem pair_symm_of_bianchi
    (hL : ∀ a b c d, R a b c d = -R b a c d)
    (hR : ∀ a b c d, R a b c d = -R a b d c)
    (hB : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0)
    (a b c d : Fin n) : R a b c d = R c d a b := by
  have key := bianchi_alt_sum hL hR a b c d
  rw [hB a b c d, hB a b d c, hB a c d b, hB b c d a] at key
  linarith

/-- Given the pair symmetry, the right antisymmetry is the left one conjugated by it. -/
theorem antisymm_right_of_pair_symm
    (hL : ∀ a b c d, R a b c d = -R b a c d)
    (hP : ∀ a b c d, R a b c d = R c d a b)
    (a b c d : Fin n) : R a b c d = -R a b d c := by
  rw [hP a b c d, hP a b d c]
  exact hL c d a b

/-- And symmetrically. So **in the presence of the pair symmetry the two antisymmetries are
equivalent**, and the structure has two different three-clause presentations, not one. -/
theorem antisymm_left_of_pair_symm
    (hR : ∀ a b c d, R a b c d = -R a b d c)
    (hP : ∀ a b c d, R a b c d = R c d a b)
    (a b c d : Fin n) : R a b c d = -R b a c d := by
  rw [hP a b c d, hP b a c d]
  exact hR c d a b

/-- **A THREE-CLAUSE CONSTRUCTOR**, which is the practical content of `pair_symm_of_bianchi`:
anyone exhibiting an algebraic curvature tensor has one fewer clause to check. -/
theorem IsAlgCurv.mk'
    (hL : ∀ a b c d, R a b c d = -R b a c d)
    (hR : ∀ a b c d, R a b c d = -R a b d c)
    (hB : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0) :
    IsAlgCurv R where
  antisymm_left := hL
  antisymm_right := hR
  pair_symm := pair_symm_of_bianchi hL hR hB
  bianchi := hB

/-- **BELOW DIMENSION TWO THERE IS NOTHING TO CLASSIFY:** every algebraic curvature tensor
vanishes identically, from the left antisymmetry alone, because `Fin n` is then a subsingleton and
every index equals every other. So the hypothesis `2 ≤ n` carried by `scal_constCurv_pos` and
`constCurv_ne_zero` is **sharp** rather than a convenience — at `n ≤ 1` those statements are false,
not merely unproved. -/
theorem eq_zero_of_le_one (hn : n ≤ 1) (hL : ∀ a b c d, R a b c d = -R b a c d)
    (a b c d : Fin n) : R a b c d = 0 := by
  have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
  have hab : a = b := Subsingleton.elim a b
  subst hab
  exact diag_left_eq_zero hL a c d

/-- **AND SHARPNESS IS A THEOREM, NOT A REMARK.** The previous docstring said `2 ≤ n` is sharp
because `constCurv` vanishes below it; here that is proved, so the word "sharp" is carried by
something. `constCurv_ne_zero`'s conclusion is therefore false at `n ≤ 1` rather than merely
unproved. -/
theorem constCurv_eq_zero_of_le_one (hn : n ≤ 1) (a b c d : Fin n) :
    constCurv n a b c d = 0 :=
  eq_zero_of_le_one hn (isAlgCurv_constCurv n).antisymm_left a b c d

/-- **ON `Fin 2` THE BIANCHI IDENTITY IS FREE**, from the left antisymmetry alone — neither the
right antisymmetry nor the pair symmetry is needed. Among any three indices drawn from a
two-element type two coincide, and each of the three coincidences makes one term of the Bianchi sum
vanish and the other two cancel by antisymmetry. This is what stops `Fin 2` from being a candidate
witness in §6, and it is the exact point at which the argument fails for larger `n`: the pigeonhole
step, and nothing else. -/
theorem bianchi_of_antisymm_two {R : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ}
    (hL : ∀ a b c d, R a b c d = -R b a c d) (a b c d : Fin 2) :
    R a b c d + R b c a d + R c a b d = 0 := by
  have hz := diag_left_eq_zero hL
  by_cases hab : a = b
  · rw [hab]
    have h1 := hz b c d
    have h2 := hL b c b d
    linarith
  by_cases hbc : b = c
  · rw [hbc]
    have h1 := hz c a d
    have h2 := hL a c c d
    linarith
  by_cases hac : a = c
  · rw [hac]
    have h1 := hz c b d
    have h2 := hL c b c d
    linarith
  · exfalso
    have ha := a.isLt
    have hb := b.isLt
    have hc := c.isLt
    have n1 : a.val ≠ b.val := fun h => hab (Fin.ext h)
    have n2 : b.val ≠ c.val := fun h => hbc (Fin.ext h)
    have n3 : a.val ≠ c.val := fun h => hac (Fin.ext h)
    omega

end Dependencies

/-! ## 6. And `bianchi` is NOT redundant — a witness, not an assertion

§5 removes one clause from the structure. It would be easy to leave the reader thinking the other
three are equally soft, and easier still to *say* they are not without checking. This section
exhibits a tensor satisfying **both antisymmetries and the pair symmetry** and **failing Bianchi**,
so the remaining three-clause presentation is minimal in the one direction §5 leaves open.

The witness is `ω ⊗ ω` for `ω` the standard symplectic form on `Fin 4`. Antisymmetry of `ω` costs
no case analysis at all: `ω` is defined as `f a b − f b a`, so `ω a b = -ω b a` is `ring`. The
Bianchi sum at `(0,1,2,3)` is the Plücker expression `ω₀₁ω₂₃ + ω₁₂ω₀₃ + ω₂₀ω₁₃`, which is `1`,
and that single evaluation is the whole refutation. -/

/-- An asymmetric seed; only `symp` below is used, and only through `symp_antisymm`. -/
def sympSeed (a b : Fin 4) : ℝ := if a = 0 ∧ b = 1 then 1 else if a = 2 ∧ b = 3 then 1 else 0

/-- The standard symplectic form on `Fin 4`, as `sympSeed` antisymmetrised. -/
def symp (a b : Fin 4) : ℝ := sympSeed a b - sympSeed b a

theorem symp_antisymm (a b : Fin 4) : symp a b = -symp b a := by
  simp only [symp]; ring

/-- `ω ⊗ ω`. -/
def sympCurv (a b c d : Fin 4) : ℝ := symp a b * symp c d

theorem sympCurv_antisymm_left (a b c d : Fin 4) :
    sympCurv a b c d = -sympCurv b a c d := by
  simp only [sympCurv]; rw [symp_antisymm a b]; ring

theorem sympCurv_antisymm_right (a b c d : Fin 4) :
    sympCurv a b c d = -sympCurv a b d c := by
  simp only [sympCurv]; rw [symp_antisymm c d]; ring

theorem sympCurv_pair_symm (a b c d : Fin 4) : sympCurv a b c d = sympCurv c d a b := by
  simp only [sympCurv]; ring

/-- **THE BIANCHI SUM IS `1` AT `(0,1,2,3)`.** -/
theorem sympCurv_bianchi_ne_zero :
    sympCurv 0 1 2 3 + sympCurv 1 2 0 3 + sympCurv 2 0 1 3 = 1 := by
  norm_num [sympCurv, symp, sympSeed, Fin.ext_iff]

theorem not_isAlgCurv_sympCurv : ¬ IsAlgCurv sympCurv := by
  intro h
  have h0 := h.bianchi 0 1 2 3
  rw [sympCurv_bianchi_ne_zero] at h0
  exact one_ne_zero h0

/-- **SO THE OTHER THREE CLAUSES DO NOT IMPLY `bianchi`**, and this is the theorem that says so
rather than four lemmas a reader has to assemble. Together with `pair_symm_of_bianchi`: of the four
clauses of `IsAlgCurv`, the pair symmetry is redundant and the Bianchi identity is not.

**The dimension is not arbitrary and the file proves it is not.** `eq_zero_of_le_one` kills `n ≤ 1`
outright, and `bianchi_of_antisymm_two` shows no witness can exist over `Fin 2` either — there the
Bianchi identity follows from the left antisymmetry alone. `Fin 3` is **not settled here**: no
witness is offered and no proof that none exists, and the reason is that the argument that works
for `Fin 2` is pigeonhole on three indices and simply stops. So what is established is that the
smallest witness lives in dimension `3` or `4`, and that `4` works. -/
theorem bianchi_not_implied :
    ∃ R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ,
      (∀ a b c d, R a b c d = -R b a c d) ∧
      (∀ a b c d, R a b c d = -R a b d c) ∧
      (∀ a b c d, R a b c d = R c d a b) ∧
      ¬ (∀ a b c d, R a b c d + R b c a d + R c a b d = 0) := by
  refine ⟨sympCurv, sympCurv_antisymm_left, sympCurv_antisymm_right, sympCurv_pair_symm, ?_⟩
  intro hB
  have h0 := hB 0 1 2 3
  rw [sympCurv_bianchi_ne_zero] at h0
  exact one_ne_zero h0

/-! ## 8. The Einstein trace, and the one classification this file can afford

`IsAlgCurv` was built because W5's algebraic stair is about **maps out of** the space of algebraic
curvature tensors. The distinguished one is the Einstein combination, and the smallest case of the
classification is `n = 2`, where the space turns out to be one-dimensional and the Einstein
combination is therefore identically zero — the algebraic shadow of the fact that the Einstein
tensor carries no information in two dimensions.

Still not `a₂`, still no manifold, and the `n = 4` classification is still not attempted. -/

section Einstein

variable {R : Fin n → Fin n → Fin n → Fin n → ℝ}

/-- **THE EINSTEIN COMBINATION**, `Ric − ½ scal · δ`. -/
noncomputable def einstein (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) : ℝ :=
  ricci R b c - (1 / 2) * scal R * delta b c

theorem einstein_symm (hR : IsAlgCurv R) (b c : Fin n) : einstein R b c = einstein R c b := by
  simp only [einstein, ricci_symm hR b c, delta_symm b c]

/-- **ITS TRACE IS `(1 − n/2) scal`.** In particular it is `−scal` in four dimensions
(`trace_einstein_four`) and `0` in two — the first sign that `n = 2` is degenerate. -/
theorem trace_einstein (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ b, einstein R b b = (1 - (n : ℝ) / 2) * scal R := by
  simp only [einstein, delta_self, mul_one]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← scal]
  ring

theorem trace_einstein_four (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ b, einstein R b b = -scal R := by
  rw [trace_einstein]; norm_num

theorem einstein_constCurv (n : ℕ) (b c : Fin n) :
    einstein (constCurv n) b c = ((n : ℝ) - 1) * (1 - (n : ℝ) / 2) * delta b c := by
  simp only [einstein, ricci_constCurv, scal_constCurv]
  ring

/-! ### The two-dimensional classification -/

/-- **EVERY ALGEBRAIC CURVATURE TENSOR ON `Fin 2` IS A MULTIPLE OF `constCurv`**, and the
multiple is read off at a single component. This is the `n = 2` case of the classification W5's
account lists as not attempted; it is affordable here only because the space is one-dimensional
and the proof is sixteen instances of the two antisymmetries. Neither the pair symmetry nor
Bianchi is needed — by `bianchi_of_antisymm_two` the latter is free in this dimension anyway. -/
theorem eq_smul_constCurv_two {R : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ}
    (hL : ∀ a b c d, R a b c d = -R b a c d)
    (hR : ∀ a b c d, R a b c d = -R a b d c) (a b c d : Fin 2) :
    R a b c d = -R 0 1 0 1 * constCurv 2 a b c d := by
  have k0 : ∀ c d : Fin 2, R 0 0 c d = 0 := fun c d => diag_left_eq_zero hL 0 c d
  have k1 : ∀ c d : Fin 2, R 1 1 c d = 0 := fun c d => diag_left_eq_zero hL 1 c d
  have m0 : ∀ a b : Fin 2, R a b 0 0 = 0 := fun a b => diag_right_eq_zero hR a b 0
  have m1 : ∀ a b : Fin 2, R a b 1 1 = 0 := fun a b => diag_right_eq_zero hR a b 1
  have p1 : R 1 0 0 1 = -R 0 1 0 1 := hL 1 0 0 1
  have p2 : R 0 1 1 0 = -R 0 1 0 1 := by have h := hR 0 1 0 1; linarith
  have p3 : R 1 0 1 0 = R 0 1 0 1 := by have h := hR 1 0 0 1; linarith
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [constCurv, delta, k0, k1, m0, m1, p1, p2, p3]

/-- Hence its Ricci trace is a multiple of the metric. -/
theorem ricci_two {R : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ}
    (hL : ∀ a b c d, R a b c d = -R b a c d)
    (hR : ∀ a b c d, R a b c d = -R a b d c) (b c : Fin 2) :
    ricci R b c = -R 0 1 0 1 * delta b c := by
  have h : ∀ a, R a b c a = -R 0 1 0 1 * constCurv 2 a b c a :=
    fun a => eq_smul_constCurv_two hL hR a b c a
  simp only [ricci]
  rw [Finset.sum_congr rfl fun a _ => h a, ← Finset.mul_sum]
  have hc := ricci_constCurv 2 b c
  simp only [ricci] at hc
  rw [hc]
  norm_num

/-- **AND THE EINSTEIN COMBINATION VANISHES IDENTICALLY IN TWO DIMENSIONS**, for every algebraic
curvature tensor and not merely for the constant-curvature one. The scalar curvature is `2λ`, the
Ricci trace is `λ δ`, and `λ δ − ½ · 2λ · δ = 0`. -/
theorem einstein_eq_zero_two {R : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ}
    (hL : ∀ a b c d, R a b c d = -R b a c d)
    (hR : ∀ a b c d, R a b c d = -R a b d c) (b c : Fin 2) :
    einstein R b c = 0 := by
  have hs : scal R = 2 * -R 0 1 0 1 := by
    simp only [scal]
    rw [Finset.sum_congr rfl fun b _ => ricci_two hL hR b b]
    simp [delta_self, Finset.sum_const, Finset.card_univ]
  simp only [einstein, ricci_two hL hR, hs]
  ring

/-- **AND THAT VANISHING IS NOT VACUOUS**, by the standard §3 set for this file. It would be worth
nothing if every algebraic curvature tensor on `Fin 2` were zero — `eq_smul_constCurv_two` says
they are all multiples of one tensor, and a one-dimensional space could still be `{0}`. It is not:
`constCurv 2` satisfies every clause and has scalar curvature `2`. So `einstein_eq_zero_two` says
something about a class that has non-zero members, which is what makes it the algebraic shadow of
"the Einstein tensor carries no information in two dimensions" rather than a triviality. -/
theorem exists_scal_ne_zero_two :
    ∃ R : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ, IsAlgCurv R ∧ scal R ≠ 0 :=
  ⟨constCurv 2, isAlgCurv_constCurv 2, by rw [scal_constCurv]; norm_num⟩

end Einstein

/-! ## 9. Removing the orthonormal frame: contraction against an arbitrary metric

Everything above contracts with `δ`, which is the statement "the frame is orthonormal". That is one
of the two restrictions the header names, and this section removes it: `ricciG` and `scalG` contract
with an arbitrary `g`, and **`ricciG_symm` needs only that `g` is symmetric** — no positivity, no
non-degeneracy, no relation to `R`.

The old definitions are recovered as the `δ` case (`ricciG_delta`, `scalG_delta`), so nothing above
is orphaned and the generalisation is checked against what it generalises rather than asserted to
subsume it.

**The other restriction is untouched and this does not weaken it.** These are still components
indexed by `Fin n`, not multilinear maps on a vector space, and there is still no manifold. What has
gone is the assumption that the metric is the identity — which is `WALLS` §W5.0 item 2's first step
and not more than that. -/

section GeneralMetric

variable {R : Fin n → Fin n → Fin n → Fin n → ℝ} {g : Fin n → Fin n → ℝ}

/-- **The Ricci trace against an arbitrary inverse metric**, `Ric_{bc} = g^{ad} R_{dbca}`. -/
def ricciG (g : Fin n → Fin n → ℝ) (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) : ℝ :=
  ∑ a, ∑ d, g a d * R d b c a

/-- It is the old one when the frame is orthonormal. -/
theorem ricciG_delta (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) :
    ricciG delta R b c = ricci R b c := by
  simp only [ricciG, ricci]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · simp [delta_self]
  · intro x _ hx; simp [delta, Ne.symm hx]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **THE RICCI TRACE IS SYMMETRIC FOR ANY SYMMETRIC METRIC.** `ricci_symm` assumed the metric was
`δ`; the only property of it the proof ever used is that it is symmetric. The tensor identity doing
the work is `R_{dbca} = R_{acbd}`, from the pair symmetry and both antisymmetries — the same three
clauses as before, so no hypothesis on `R` is added either. -/
theorem ricciG_symm (hg : ∀ a d, g a d = g d a) (hR : IsAlgCurv R) (b c : Fin n) :
    ricciG g R b c = ricciG g R c b := by
  have key : ∀ a d : Fin n, R d b c a = R a c b d := by
    intro a d
    calc R d b c a = R c a d b := hR.pair_symm d b c a
      _ = -R a c d b := hR.antisymm_left c a d b
      _ = -(-R a c b d) := by rw [hR.antisymm_right a c d b]
      _ = R a c b d := neg_neg _
  simp only [ricciG]
  calc ∑ a, ∑ d, g a d * R d b c a
      = ∑ a, ∑ d, g a d * R a c b d := by
        exact Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun d _ => by rw [key a d]
    _ = ∑ d, ∑ a, g a d * R a c b d := Finset.sum_comm
    _ = ∑ a, ∑ d, g a d * R d c b a := by
        exact Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun d _ => by rw [hg a d]

/-- **The scalar curvature against the same metric.** -/
def scalG (g : Fin n → Fin n → ℝ) (R : Fin n → Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ b, ∑ c, g b c * ricciG g R b c

theorem scalG_delta (R : Fin n → Fin n → Fin n → Fin n → ℝ) : scalG delta R = scal R := by
  simp only [scalG, scal]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single b]
  · simp [delta_self, ricciG_delta]
  · intro x _ hx; simp [delta, Ne.symm hx]
  · intro h; exact absurd (Finset.mem_univ b) h

/-- And the witness still works, with its old value, so the generalisation is not vacuous at the
one tensor this file can compute with. -/
theorem scalG_delta_constCurv (n : ℕ) : scalG delta (constCurv n) = (n : ℝ) * ((n : ℝ) - 1) := by
  rw [scalG_delta, scal_constCurv]

end GeneralMetric

/-! ## 10. The last clause: `antisymm_left` does not follow from the other two either

§7 recorded, as an open question of this file's own, whether the left antisymmetry follows from
`antisymm_right` and `bianchi` without the pair symmetry. **It does not**, and here is the witness.

The tensor below is three entries on `Fin 3`, antisymmetrised in its last pair so that
`antisymm_right` costs nothing, and it satisfies Bianchi. It has `R 0 0 1 2 = 1`, which the left
antisymmetry forbids outright: that clause forces `R a a c d = 0` (`diag_left_eq_zero`).

**`Fin 3` is minimal, and that is proved rather than asserted**: `antisymm_left_of_two` below shows
that on `Fin 2` the left antisymmetry *does* follow from the right one and Bianchi, so no
two-dimensional witness exists — the same shape as `bianchi_of_antisymm_two` in §5, and for the same
pigeonhole reason.

*One figure here is arithmetic done outside Lean and is labelled as such rather than left looking
like the rest*: solving the linear system gives the space of tensors with `antisymm_right` and
Bianchi as dimension `1` at `n = 2` and dimension `9` at `n = 3`. Nothing below depends on those
numbers; they are why the search stopped at three. -/

/-- **AT `n = 2` THERE IS NOTHING TO FIND.** The left antisymmetry follows from the right one and
Bianchi, by the same pigeonhole that made Bianchi free in §5: among three indices drawn from a
two-element type two coincide. So the witness below could not have lived on `Fin 2`. -/
theorem antisymm_left_of_two {R : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ}
    (hR : ∀ a b c d, R a b c d = -R a b d c)
    (hB : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0) (a b c d : Fin 2) :
    R a b c d = -R b a c d := by
  have z : ∀ x y w : Fin 2, R x y w w = 0 := fun x y w => diag_right_eq_zero hR x y w
  have z000 := z 0 0 0
  have z001 := z 0 0 1
  have z010 := z 0 1 0
  have z011 := z 0 1 1
  have z100 := z 1 0 0
  have z101 := z 1 0 1
  have z110 := z 1 1 0
  have z111 := z 1 1 1
  have b0000 := hB 0 0 0 0
  have r0000 := hR 0 0 0 0
  have b0001 := hB 0 0 0 1
  have r0001 := hR 0 0 0 1
  have b0010 := hB 0 0 1 0
  have r0010 := hR 0 0 1 0
  have b0011 := hB 0 0 1 1
  have r0011 := hR 0 0 1 1
  have b0100 := hB 0 1 0 0
  have r0100 := hR 0 1 0 0
  have b0101 := hB 0 1 0 1
  have r0101 := hR 0 1 0 1
  have b0110 := hB 0 1 1 0
  have r0110 := hR 0 1 1 0
  have b0111 := hB 0 1 1 1
  have r0111 := hR 0 1 1 1
  have b1000 := hB 1 0 0 0
  have r1000 := hR 1 0 0 0
  have b1001 := hB 1 0 0 1
  have r1001 := hR 1 0 0 1
  have b1010 := hB 1 0 1 0
  have r1010 := hR 1 0 1 0
  have b1011 := hB 1 0 1 1
  have r1011 := hR 1 0 1 1
  have b1100 := hB 1 1 0 0
  have r1100 := hR 1 1 0 0
  have b1101 := hB 1 1 0 1
  have r1101 := hR 1 1 0 1
  have b1110 := hB 1 1 1 0
  have r1110 := hR 1 1 1 0
  have b1111 := hB 1 1 1 1
  have r1111 := hR 1 1 1 1
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp only [Fin.zero_eta, Fin.mk_one] <;> linarith

/-- Three entries, and everything else zero. -/
def cwSeed (a b c d : Fin 3) : ℝ :=
  (if a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 2 then 1 else 0)
  + (if a = 0 ∧ b = 2 ∧ c = 0 ∧ d = 1 then 1 else 0)
  + (if a = 1 ∧ b = 0 ∧ c = 2 ∧ d = 0 then 1 else 0)

/-- The witness: `cwSeed` antisymmetrised in its last pair, so `antisymm_right` is `ring`. -/
def cw (a b c d : Fin 3) : ℝ := cwSeed a b c d - cwSeed a b d c

theorem cw_antisymm_right (a b c d : Fin 3) : cw a b c d = -cw a b d c := by
  simp only [cw]; ring

theorem cw_bianchi (a b c d : Fin 3) : cw a b c d + cw b c a d + cw c a b d = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [cw, cwSeed]

theorem cw_diag_ne_zero : cw 0 0 1 2 = 1 := by
  simp [cw, cwSeed]

/-- **SO THE LEFT ANTISYMMETRY IS INDEPENDENT OF THE OTHER TWO.** With `bianchi_not_implied` and
`pair_symm_of_bianchi`, the dependency picture of `IsAlgCurv` is now complete: **exactly one of the
four clauses is redundant, the pair symmetry, and it is redundant only in the presence of both
antisymmetries.** -/
theorem antisymm_left_not_implied :
    ∃ R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ,
      (∀ a b c d, R a b c d = -R a b d c) ∧
      (∀ a b c d, R a b c d + R b c a d + R c a b d = 0) ∧
      ¬ (∀ a b c d, R a b c d = -R b a c d) := by
  refine ⟨cw, cw_antisymm_right, cw_bianchi, ?_⟩
  intro hL
  have := diag_left_eq_zero hL 0 1 2
  rw [cw_diag_ne_zero] at this
  exact one_ne_zero this

/-! ## 11. The Lovelock shadow: its two candidate maps, and the dimension where they part

`WALLS` §W5.0 §6 item 4 names the algebraic content of Lovelock's theorem — that the
`O(n)`-equivariant linear maps from algebraic curvature tensors to symmetric 2-tensors are spanned
by `R ↦ Ric` and `R ↦ scal · δ` — and then **refuses to write it as a `def`**, in these words:

> `ERRATUM 108` refuted a gap object of this project that nobody had tried to falsify, and naming
> this one before its small cases have been read would repeat that.

This section reads the small cases, and it still does not name the object. The group action is not
written down here and no Schur-type argument is attempted. What is settled here is the part of
"these two span" that needs no invariant theory to prove: **whether the two named maps are
independent of each other**, dimension by dimension.

*Read this section together with §12, which was written after it and because of it.* Independence
is only half of "these two are a basis of the equivariant maps" — the other half is that the two
**are** equivariant, which this section assumed and never checked. §12 checks it. What is below is
true as stated; it is weaker than the wall's item 4 half it was first advertised as settling.

**They are not always.** At `n = 2` they are proportional — `ricci_eq_half_scal_two`, which is §8's
`einstein_eq_zero_two` read as a statement about the maps rather than about a tensor — so the span
of the pair is one-dimensional there and the pair is not a basis of it. **From `n = 3` up they are
independent** (`traces_independent`), and what separates them is a curvature tensor whose Ricci
trace is a *projector* rather than a multiple of the metric.

That witness is `constCurv` with the metric replaced by a rank-`(n−1)` projector, which needs §3's
witness lemmas proved for an arbitrary symmetric form rather than for `δ`. So the section opens by
removing that restriction: **`isAlgCurv_knSquare`** says the Kulkarni–Nomizu square `h_{ad}h_{bc} −
h_{ac}h_{bd}` of *any* symmetric `h` is an algebraic curvature tensor, and `knSquare_delta` is the
`rfl` recording that §3's `constCurv` is its `h = δ` case. The proof in §3 already used nothing
about `δ` beyond `delta_symm`; this is that observation cashed rather than noticed.

**What this does and does not do to the wall's sentence.** The sentence says *spanned by*, and a
span is allowed to be smaller than the number of vectors offered, so **nothing here refutes it**.
What is refuted is the reading — natural, and the reading a premature `def` would have frozen —
that the two maps are a *basis* in every dimension. That reading is false at `n = 2`. The other
half of item 4, that nothing outside their span is equivariant, is the invariant theory, and it is
**not begun here**: no group, no action, no averaging.

**Still no `a₂`, still no manifold.** Everything below is a four-index array of reals. -/

section LovelockShadow

variable {h : Fin n → Fin n → ℝ}

/-- **The Kulkarni–Nomizu square of a form**, `h_{ad} h_{bc} − h_{ac} h_{bd}`. §3's `constCurv` is
its `h = δ` case, definitionally — see `knSquare_delta`. -/
def knSquare (h : Fin n → Fin n → ℝ) (a b c d : Fin n) : ℝ := h a d * h b c - h a c * h b d

/-- `constCurv` **is** the Kulkarni–Nomizu square of the metric, and this is `rfl` rather than a
resemblance, so §3's witness is genuinely the special case and not a parallel construction. -/
theorem knSquare_delta (n : ℕ) : knSquare (delta : Fin n → Fin n → ℝ) = constCurv n := rfl

/-- **AND IT IS AN ALGEBRAIC CURVATURE TENSOR FOR EVERY SYMMETRIC `h`.** One restrictive hypothesis
removed from `isAlgCurv_constCurv`: that proof used no property of `δ` except `delta_symm`, and
symmetry of `h` is all that is asked here. No positivity, no non-degeneracy. -/
theorem isAlgCurv_knSquare (hs : ∀ a b, h a b = h b a) : IsAlgCurv (knSquare h) where
  antisymm_left a b c d := by simp only [knSquare]; ring
  antisymm_right a b c d := by simp only [knSquare]; ring
  pair_symm a b c d := by
    simp only [knSquare]
    rw [hs c b, hs d a, hs c a, hs d b]; ring
  bianchi a b c d := by
    simp only [knSquare]
    rw [hs c a, hs b a, hs c b]; ring

/-- **ITS RICCI TRACE IS `(tr h) · h − h²`.** With `h = δ` this is `n·δ − δ = (n−1)δ`, which is
`ricci_constCurv`; with `h` a projector, below, the two terms have different coefficients and the
trace comes out proportional to `h` rather than to `δ`. That difference is the whole of §11. -/
theorem ricci_knSquare (h : Fin n → Fin n → ℝ) (b c : Fin n) :
    ricci (knSquare h) b c = (∑ a, h a a) * h b c - ∑ a, h a c * h b a := by
  simp only [ricci, knSquare]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]

/-! ### The projector, and the tensor built from it -/

/-- **The metric with one diagonal entry switched off**: `δ` minus the rank-one projector onto the
`k` axis, i.e. the orthogonal projector onto the hyperplane `x_k = 0`. Its trace is `n − 1` rather
than `n`, it is idempotent, and it is **not** a multiple of `δ` as soon as there is a coordinate
besides `k` — which is what makes it separate the two maps. -/
def projOff (k a b : Fin n) : ℝ := delta a b - delta a k * delta b k

theorem projOff_symm (k : Fin n) : ∀ a b, projOff k a b = projOff k b a := by
  intro a b
  simp only [projOff]
  rw [delta_symm a b]; ring

/-- The switched-off coordinate is annihilated: `P_{bk} = 0` for every `b`. -/
@[simp] theorem projOff_right_eq_zero (k b : Fin n) : projOff k b k = 0 := by
  simp [projOff]

theorem projOff_diag_eq_zero (k : Fin n) : projOff k k k = 0 := projOff_right_eq_zero k k

theorem projOff_diag_eq_one {k a : Fin n} (hak : a ≠ k) : projOff k a a = 1 := by
  simp [projOff, delta, hak]

/-- **ITS TRACE IS `n − 1`.** -/
theorem sum_projOff_diag (k : Fin n) : ∑ a, projOff k a a = (n : ℝ) - 1 := by
  have hpt : ∀ a : Fin n, projOff k a a = 1 - delta a k * delta a k := by
    intro a; simp only [projOff, delta_self]
  rw [Finset.sum_congr rfl fun a _ => hpt a, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    sum_delta_left k fun a => delta a k, delta_self]

/-- **AND IT IS IDEMPOTENT.** The proof is two evaluations and one vanishing: contracting the free
delta picks out `P_{bc}`, and the correction term contracts to `P_{bk}`, which is `0`. -/
theorem sum_projOff_mul (k b c : Fin n) : ∑ a, projOff k a c * projOff k b a = projOff k b c := by
  have hpt : ∀ a : Fin n, projOff k a c * projOff k b a
      = delta a c * projOff k b a - delta c k * (delta a k * projOff k b a) := by
    intro a; simp only [projOff]; ring
  rw [Finset.sum_congr rfl fun a _ => hpt a, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_delta_left c fun a => projOff k b a, sum_delta_left k fun a => projOff k b a,
    projOff_right_eq_zero, mul_zero, sub_zero]

theorem isAlgCurv_projOffCurv (k : Fin n) : IsAlgCurv (knSquare (projOff k)) :=
  isAlgCurv_knSquare (projOff_symm k)

/-- **ITS RICCI TRACE IS `(n − 2) · P`** — a multiple of the *projector*, not of the metric. The
trace supplies `n − 1` and idempotence takes one back off. -/
theorem ricci_projOffCurv (k b c : Fin n) :
    ricci (knSquare (projOff k)) b c = ((n : ℝ) - 2) * projOff k b c := by
  rw [ricci_knSquare, sum_projOff_diag, sum_projOff_mul]
  ring

theorem scal_projOffCurv (k : Fin n) :
    scal (knSquare (projOff k)) = ((n : ℝ) - 2) * ((n : ℝ) - 1) := by
  simp only [scal, ricci_projOffCurv]
  rw [← Finset.mul_sum, sum_projOff_diag]

/-- **AND THE WITNESS IS NOT THE ZERO TENSOR**, for `n ≥ 3`. This file's §3 standard: a witness
whose non-triviality is not checked is worth nothing, because `R = 0` satisfies every clause. -/
theorem scal_projOffCurv_pos (hn : 3 ≤ n) (k : Fin n) : 0 < scal (knSquare (projOff k)) := by
  rw [scal_projOffCurv]
  have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith

/-- **AND ITS RICCI TRACE IS NOT A MULTIPLE OF THE METRIC**, once `n ≥ 3`. That is the separation,
and it is two evaluations: at the switched-off coordinate the trace is `0` while `δ` is `1`, and at
any other coordinate the trace is `n − 2`, which is non-zero exactly when `n ≠ 2`. Both halves fail
at `n = 2` — there is no other coordinate to use, and `n − 2` is zero anyway. -/
theorem ricci_not_smul_delta (hn : 3 ≤ n) :
    ∃ k : Fin n, ∀ lam : ℝ, ¬ ∀ b c, ricci (knSquare (projOff k)) b c = lam * delta b c := by
  obtain ⟨k, j, hjk⟩ : ∃ k j : Fin n, j ≠ k :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  refine ⟨k, fun lam hlam => ?_⟩
  have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 := hlam k k
  have h2 := hlam j j
  rw [ricci_projOffCurv, projOff_diag_eq_zero, delta_self] at h1
  rw [ricci_projOffCurv, projOff_diag_eq_one hjk, delta_self] at h2
  linarith

/-! ### The two maps, and the dimension at which they part -/

/-- **THE TWO CANDIDATE MAPS OF THE LOVELOCK SHADOW ARE LINEARLY INDEPENDENT FROM DIMENSION THREE
UP.** A relation `α · Ric + β · scal · δ = 0` holding for *every* algebraic curvature tensor forces
`α = β = 0`, and two evaluations of the projector witness do it: at the switched-off coordinate the
Ricci term drops out and `β · scal` must vanish with `scal = (n−2)(n−1) > 0`; at any other
coordinate `α · (n − 2)` must then vanish too.

**This sentence used to end "— the half that needs no group action", and that was wrong.** It
needs no group action to *prove*, which is what the observation was; but the half itself is *the
two named maps are equivariant and independent*, and independence alone leaves the first conjunct
unchecked. §12 supplies it. Corrected in place rather than deleted, because the error is the
point: two things can be shown distinct without either having been shown to be what it is called. -/
theorem traces_independent (hn : 3 ≤ n) {α β : ℝ}
    (hz : ∀ R : Fin n → Fin n → Fin n → Fin n → ℝ, IsAlgCurv R → ∀ b c,
      α * ricci R b c + β * (scal R * delta b c) = 0) :
    α = 0 ∧ β = 0 := by
  obtain ⟨k, j, hjk⟩ : ∃ k j : Fin n, j ≠ k :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 := hz _ (isAlgCurv_projOffCurv k) k k
  have h2 := hz _ (isAlgCurv_projOffCurv k) j j
  rw [ricci_projOffCurv, scal_projOffCurv, projOff_diag_eq_zero, delta_self] at h1
  rw [ricci_projOffCurv, scal_projOffCurv, projOff_diag_eq_one hjk, delta_self] at h2
  have hP : (0 : ℝ) < ((n : ℝ) - 2) * ((n : ℝ) - 1) := by nlinarith
  have hb : β = 0 := by
    have h1' : β * (((n : ℝ) - 2) * ((n : ℝ) - 1)) = 0 := by linarith
    rcases mul_eq_zero.mp h1' with hh | hh
    · exact hh
    · exact absurd hh (ne_of_gt hP)
  refine ⟨?_, hb⟩
  rw [hb] at h2
  have h2' : α * ((n : ℝ) - 2) = 0 := by linarith
  rcases mul_eq_zero.mp h2' with hh | hh
  · exact hh
  · exact absurd hh (ne_of_gt (by linarith : (0 : ℝ) < (n : ℝ) - 2))

/-- **AT `n = 2` THE TWO MAPS ARE PROPORTIONAL.** This is §8's `einstein_eq_zero_two` restated as a
fact about the maps: `Ric = ½ scal · δ` for *every* algebraic curvature tensor on `Fin 2`, not for
some. -/
theorem ricci_eq_half_scal_two {R : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ} (hR : IsAlgCurv R)
    (b c : Fin 2) : ricci R b c = 1 / 2 * (scal R * delta b c) := by
  have h := einstein_eq_zero_two hR.antisymm_left hR.antisymm_right b c
  simp only [einstein] at h
  linarith

/-- **SO IN DIMENSION TWO THE PAIR IS DEPENDENT**, in exactly the sense `traces_independent` denies
from dimension three up: a relation with `α ≠ 0`, holding for every algebraic curvature tensor. The
span of the two maps is therefore one-dimensional at `n = 2` and two-dimensional from `n = 3`, so
**the pair is a basis of its span only from three up** — which is the reading of `WALLS` §W5.0 §6
item 4 that a premature `def` would have frozen, and it is false in the smallest dimension where
there is anything at all to classify.

`exists_scal_ne_zero_two` of §8 keeps this from being vacuous: the class it quantifies over has
members with non-zero scalar curvature. -/
theorem traces_dependent_two :
    ∃ α β : ℝ, (α ≠ 0 ∨ β ≠ 0) ∧
      ∀ R : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ, IsAlgCurv R → ∀ b c,
        α * ricci R b c + β * (scal R * delta b c) = 0 := by
  refine ⟨1, -(1 / 2), Or.inl one_ne_zero, fun R hR b c => ?_⟩
  have h := ricci_eq_half_scal_two hR b c
  linarith

/-- **AND THE SPAN AT `n = 2` IS ONE-DIMENSIONAL, NOT ZERO.** `traces_dependent_two` on its own is
compatible with both maps vanishing identically, in which case "proportional" would be a flattering
name for "both zero" and the comparison with `n ≥ 3` would be empty. It is not that case: the
second map is non-zero already at §3's witness. -/
theorem scal_delta_ne_zero_two :
    ∃ R : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ, IsAlgCurv R ∧ ∃ b c : Fin 2,
      scal R * delta b c ≠ 0 := by
  obtain ⟨R, hR, hs⟩ := exists_scal_ne_zero_two
  exact ⟨R, hR, 0, 0, by simpa using hs⟩

end LovelockShadow

/-! ## 12. The group arrives, and §11's missing membership check

**§11 proved the two maps independent without ever checking they are in the family.** The family
`WALLS` §W5.0 §6 item 4 is about is the `O(n)`-**equivariant** linear maps; §11 showed `R ↦ Ric`
and `R ↦ scal·δ` are linearly independent of each other and never once asked whether either
commutes with a rotation. Independence inside a set one has not shown either element belongs to is
a weaker fact than it reads as, and this section supplies what was missing.

`act` is the rotation action on four-index arrays, `act2` the same rotation on 2-tensors, and
`IsOrth` is orthogonality in the two forms the contractions need — rows and columns — which
`isOrth_of_mem_orthogonalGroup` derives from membership in **Mathlib's own**
`Matrix.orthogonalGroup`, so the predicate is not one this file invented for its own convenience.
`isOrth_delta`, `isOrth_reflect` and `reflect_ne_delta` keep it from being a class with one
trivial inhabitant, which is this file's §3 standard applied to a hypothesis rather than to a
witness — and the third of those is what makes the first two count as two. That the reflection
lies outside `SO(n)` is **true and not proved here**: no determinant is computed in this file.

**`isAlgCurv_act`** — the space of algebraic curvature tensors is invariant, so "maps *from*
algebraic curvature tensors" is a sentence about something the action preserves. The four clauses
are four relabellings of the summation index, done as `Equiv`s rather than as chains of
`Finset.sum_comm`; only Bianchi needs the tensor's own clause pointwise.

**`ricci_equivariant`** and **`scalDelta_equivariant`** — the check §11 skipped. `Ric` transforms
as a 2-tensor (which needs the columns of `Q` orthonormal, contracting the first slot against the
fourth) and `scal` is invariant outright, while `δ` is fixed by `act2` (which needs the rows). So
both maps of §11 are members of the family, and `traces_equivariant` states the two together.

**What this still does not do.** It gives the group, the action and the membership of the two named
maps. **It does not show the family has no other members** — that is the spanning half of item 4,
the Schur-type argument, and there is no averaging, no character and no irreducible decomposition
anywhere below. Item 4 remains half a build. Still no `a₂`, still no manifold. -/

section Equivariance

variable {Q : Fin n → Fin n → ℝ}

/-- **Orthogonality of `Q`**, in the two forms this section contracts with. Over a square real
matrix each clause implies the other, and `isOrth_of_mem_orthogonalGroup` derives both from one
membership; they are both fields because `ricci_act` contracts down a column and `act2_delta`
across a row, and threading `mul_eq_one_comm` through each use would obscure which is which. -/
structure IsOrth (Q : Fin n → Fin n → ℝ) : Prop where
  /-- The rows are orthonormal: `Q Qᵀ = 1`. -/
  rows : ∀ x y, ∑ a, Q x a * Q y a = delta x y
  /-- The columns are orthonormal: `Qᵀ Q = 1`. -/
  cols : ∀ x y, ∑ a, Q a x * Q a y = delta x y

/-- **AND IT IS MATHLIB'S ORTHOGONAL GROUP**, not a predicate invented here to be convenient. -/
theorem isOrth_of_mem_orthogonalGroup {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M ∈ Matrix.orthogonalGroup (Fin n) ℝ) : IsOrth (fun a b => M a b) := by
  have hrow : M * M.transpose = 1 := (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp hM
  have hcol : M.transpose * M = 1 := mul_eq_one_comm.mp hrow
  constructor
  · intro x y
    have h := congrFun (congrFun hrow x) y
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply, delta] using h
  · intro x y
    have h := congrFun (congrFun hcol x) y
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply, delta] using h

/-- Contracting two deltas along their second index. -/
theorem sum_delta_right (a b : Fin n) : ∑ x, delta a x * delta b x = delta a b := by
  have h : ∀ x : Fin n, delta a x * delta b x = delta x a * delta b x := by
    intro x; rw [delta_symm a x]
  rw [Finset.sum_congr rfl fun x _ => h x, sum_delta_left a fun x => delta b x, delta_symm b a]

/-- The identity is orthogonal. -/
theorem isOrth_delta : IsOrth (delta : Fin n → Fin n → ℝ) where
  rows := sum_delta_right
  cols x y := by
    have h : ∀ a : Fin n, delta a x * delta a y = delta x a * delta y a := by
      intro a; rw [delta_symm a x, delta_symm a y]
    rw [Finset.sum_congr rfl fun a _ => h a, sum_delta_right]

/-- **The reflection in the hyperplane `x_k = 0`** — `δ` with one diagonal entry negated. -/
def reflect (k a b : Fin n) : ℝ := delta a b - 2 * (delta a k * delta b k)

/-- **AND IT IS ORTHOGONAL TOO**, so `IsOrth` is not a class with one inhabitant — the §3 standard
applied to a hypothesis rather than to a witness. `reflect_ne_delta` is the half that makes this
worth stating; without it "two witnesses" would be one witness written twice.

*What is deliberately NOT claimed*: that `reflect k` lies outside `SO(n)`. It does, and this file
does not prove it — no determinant is computed anywhere below, and nothing here depends on the
distinction. -/
theorem isOrth_reflect (k : Fin n) : IsOrth (reflect k) := by
  have key : ∀ x y : Fin n, ∑ a, reflect k x a * reflect k y a = delta x y := by
    intro x y
    have h : ∀ a : Fin n, reflect k x a * reflect k y a
        = delta x a * delta y a - 2 * delta y k * (delta a k * delta x a)
          - 2 * delta x k * (delta a k * delta y a)
          + 4 * (delta x k * delta y k) * (delta a k * delta a k) := by
      intro a; simp only [reflect]; ring
    have s2 : ∑ a : Fin n, 2 * delta y k * (delta a k * delta x a) = 2 * delta y k * delta x k := by
      rw [← Finset.mul_sum, sum_delta_left k fun a => delta x a]
    have s3 : ∑ a : Fin n, 2 * delta x k * (delta a k * delta y a) = 2 * delta x k * delta y k := by
      rw [← Finset.mul_sum, sum_delta_left k fun a => delta y a]
    have s4 : ∑ a : Fin n, 4 * (delta x k * delta y k) * (delta a k * delta a k)
        = 4 * (delta x k * delta y k) * 1 := by
      rw [← Finset.mul_sum, sum_delta_left k fun a => delta a k, delta_self]
    rw [Finset.sum_congr rfl fun a _ => h a, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, sum_delta_right x y, s2, s3, s4]
    ring
  have hs : ∀ a b : Fin n, reflect k a b = reflect k b a := by
    intro a b; simp only [reflect]; rw [delta_symm a b]; ring
  refine ⟨key, fun x y => ?_⟩
  have h : ∀ a : Fin n, reflect k a x * reflect k a y = reflect k x a * reflect k y a := by
    intro a; rw [hs a x, hs a y]
  rw [Finset.sum_congr rfl fun a _ => h a, key]

/-- **AND THE TWO WITNESSES ARE DIFFERENT**, at the one entry the reflection moves. Without this
`isOrth_delta` and `isOrth_reflect` would be one inhabitant written twice, and the sentence above
about the §3 standard would be doing no work. -/
theorem reflect_ne_delta (k : Fin n) : reflect k ≠ (delta : Fin n → Fin n → ℝ) := by
  intro h
  have h1 : reflect k k k = delta k k := by rw [h]
  simp only [reflect, delta_self] at h1
  norm_num at h1

/-! ### How a four-index array transforms under `Q` -/

/-- **THE CHANGE OF FRAME BY `Q`**, on a four-index array: each slot is contracted with a copy of
`Q`. The four summation slots are bundled into one product index so that permuting them is an
`Equiv` and `Fintype.sum_equiv` does every relabelling below in one line, rather than a chain of
`Finset.sum_comm` under three binders.

**It is called `act` and the composition law is NOT proved.** `act_delta` below checks that the
identity frame change is the identity; that `act (Q · Q') = act Q ∘ act Q'`, which is the other
half of being a group action and what a `MulAction` instance would assert, is **not established
here and is not used below** — every theorem in this section quantifies over a single `Q`. -/
def act (Q : Fin n → Fin n → ℝ) (R : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) : ℝ :=
  ∑ p : Fin n × Fin n × Fin n × Fin n,
    Q a p.1 * Q b p.2.1 * Q c p.2.2.1 * Q d p.2.2.2 * R p.1 p.2.1 p.2.2.1 p.2.2.2

/-- **The same change of frame on a 2-tensor**, which is where the two maps of §11 land. -/
def act2 (Q : Fin n → Fin n → ℝ) (S : Fin n → Fin n → ℝ) (b c : Fin n) : ℝ :=
  ∑ b', ∑ c', Q b b' * Q c c' * S b' c'

/-- **THE IDENTITY FRAME CHANGE IS THE IDENTITY**, so the formula above is the transformation law
and not merely a plausible-looking quadruple sum. Only one term of the product index survives. -/
theorem act_delta (R : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    act delta R a b c d = R a b c d := by
  simp only [act]
  rw [Finset.sum_eq_single (a, b, c, d)]
  · simp
  · intro p _ hp
    by_cases h1 : a = p.1
    · by_cases h2 : b = p.2.1
      · by_cases h3 : c = p.2.2.1
        · by_cases h4 : d = p.2.2.2
          · exact absurd (by rw [h1, h2, h3, h4]) hp
          · simp [delta, h4]
        · simp [delta, h3]
      · simp [delta, h2]
    · simp [delta, h1]
  · intro h; exact absurd (Finset.mem_univ (a, b, c, d)) h

variable {R : Fin n → Fin n → Fin n → Fin n → ℝ}

theorem act_antisymm_left (Q : Fin n → Fin n → ℝ) (hL : ∀ a b c d, R a b c d = -R b a c d)
    (a b c d : Fin n) : act Q R a b c d = -act Q R b a c d := by
  simp only [act, ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv
    ⟨fun p => (p.2.1, p.1, p.2.2.1, p.2.2.2), fun p => (p.2.1, p.1, p.2.2.1, p.2.2.2),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun p => ?_
  simp only [Equiv.coe_fn_mk]
  rw [hL p.1 p.2.1 p.2.2.1 p.2.2.2]
  ring

theorem act_antisymm_right (Q : Fin n → Fin n → ℝ) (hR : ∀ a b c d, R a b c d = -R a b d c)
    (a b c d : Fin n) : act Q R a b c d = -act Q R a b d c := by
  simp only [act, ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv
    ⟨fun p => (p.1, p.2.1, p.2.2.2, p.2.2.1), fun p => (p.1, p.2.1, p.2.2.2, p.2.2.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun p => ?_
  simp only [Equiv.coe_fn_mk]
  rw [hR p.1 p.2.1 p.2.2.1 p.2.2.2]
  ring

theorem act_pair_symm (Q : Fin n → Fin n → ℝ) (hP : ∀ a b c d, R a b c d = R c d a b)
    (a b c d : Fin n) : act Q R a b c d = act Q R c d a b := by
  simp only [act]
  refine Fintype.sum_equiv
    ⟨fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1), fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun p => ?_
  simp only [Equiv.coe_fn_mk]
  rw [hP p.1 p.2.1 p.2.2.1 p.2.2.2]
  ring

theorem act_bianchi (Q : Fin n → Fin n → ℝ)
    (hB : ∀ a b c d, R a b c d + R b c a d + R c a b d = 0) (a b c d : Fin n) :
    act Q R a b c d + act Q R b c a d + act Q R c a b d = 0 := by
  have e2 : act Q R b c a d
      = ∑ p : Fin n × Fin n × Fin n × Fin n,
          Q a p.1 * Q b p.2.1 * Q c p.2.2.1 * Q d p.2.2.2 * R p.2.1 p.2.2.1 p.1 p.2.2.2 := by
    refine (Fintype.sum_equiv
      ⟨fun p => (p.2.1, p.2.2.1, p.1, p.2.2.2), fun p => (p.2.2.1, p.1, p.2.1, p.2.2.2),
        fun _ => rfl, fun _ => rfl⟩ _ _ fun p => ?_).symm
    simp only [Equiv.coe_fn_mk]
    ring
  have e3 : act Q R c a b d
      = ∑ p : Fin n × Fin n × Fin n × Fin n,
          Q a p.1 * Q b p.2.1 * Q c p.2.2.1 * Q d p.2.2.2 * R p.2.2.1 p.1 p.2.1 p.2.2.2 := by
    refine (Fintype.sum_equiv
      ⟨fun p => (p.2.2.1, p.1, p.2.1, p.2.2.2), fun p => (p.2.1, p.2.2.1, p.1, p.2.2.2),
        fun _ => rfl, fun _ => rfl⟩ _ _ fun p => ?_).symm
    simp only [Equiv.coe_fn_mk]
    ring
  rw [e2, e3]
  simp only [act]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun p _ => ?_
  have hp := hB p.1 p.2.1 p.2.2.1 p.2.2.2
  have hz : Q a p.1 * Q b p.2.1 * Q c p.2.2.1 * Q d p.2.2.2 *
      (R p.1 p.2.1 p.2.2.1 p.2.2.2 + R p.2.1 p.2.2.1 p.1 p.2.2.2
        + R p.2.2.1 p.1 p.2.1 p.2.2.2) = 0 := by
    rw [hp, mul_zero]
  linarith [hz]

/-- **THE SPACE OF ALGEBRAIC CURVATURE TENSORS IS INVARIANT UNDER THE ACTION.** So "the maps out of
algebraic curvature tensors" is a phrase about something the group preserves, which is what makes
the classification a question about representations rather than about an arbitrary subset. Note the
orthogonality of `Q` is **not needed here** — every clause is a relabelling — and is not assumed. -/
theorem isAlgCurv_act (Q : Fin n → Fin n → ℝ) (hR : IsAlgCurv R) : IsAlgCurv (act Q R) where
  antisymm_left := act_antisymm_left Q hR.antisymm_left
  antisymm_right := act_antisymm_right Q hR.antisymm_right
  pair_symm := act_pair_symm Q hR.pair_symm
  bianchi := act_bianchi Q hR.bianchi

/-! ### And the two maps are equivariant -/

/-- **THE RICCI TRACE TRANSFORMS AS A 2-TENSOR**, which is the first half of the membership check
§11 skipped. Orthogonality enters exactly once, contracting the first slot against the fourth: the
sum `∑ₐ Q_{a p₁} Q_{a p₄}` is a column inner product and is `δ_{p₁p₄}`. -/
theorem ricci_act (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) :
    ricci (act Q R) b c = act2 Q (ricci R) b c := by
  have key : ricci (act Q R) b c
      = ∑ x, ∑ y, ∑ z, Q b y * Q c z * R x y z x := by
    simp only [ricci, act]
    rw [Finset.sum_comm]
    have step : ∀ p : Fin n × Fin n × Fin n × Fin n,
        ∑ a, Q a p.1 * Q b p.2.1 * Q c p.2.2.1 * Q a p.2.2.2 * R p.1 p.2.1 p.2.2.1 p.2.2.2
          = delta p.1 p.2.2.2 * (Q b p.2.1 * Q c p.2.2.1 * R p.1 p.2.1 p.2.2.1 p.2.2.2) := by
      intro p
      have h : ∀ a : Fin n,
          Q a p.1 * Q b p.2.1 * Q c p.2.2.1 * Q a p.2.2.2 * R p.1 p.2.1 p.2.2.1 p.2.2.2
            = (Q a p.1 * Q a p.2.2.2) *
              (Q b p.2.1 * Q c p.2.2.1 * R p.1 p.2.1 p.2.2.1 p.2.2.2) := by
        intro a; ring
      rw [Finset.sum_congr rfl fun a _ => h a, ← Finset.sum_mul, hQ.cols]
    rw [Finset.sum_congr rfl fun p _ => step p]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z _ => ?_
    have h : ∀ w : Fin n, delta x w * (Q b y * Q c z * R x y z w)
        = delta w x * (Q b y * Q c z * R x y z w) := by
      intro w; rw [delta_symm x w]
    rw [Finset.sum_congr rfl fun w _ => h w,
      sum_delta_left x fun w => Q b y * Q c z * R x y z w]
  rw [key, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [ricci]
  rw [← Finset.mul_sum]

/-- **`δ` IS FIXED BY THE ACTION ON 2-TENSORS**, which needs the rows of `Q` orthonormal — the
other half of `IsOrth`, and the reason both halves are fields of it. -/
theorem act2_delta (hQ : IsOrth Q) (b c : Fin n) : act2 Q delta b c = delta b c := by
  simp only [act2]
  have inner : ∀ b' : Fin n, ∑ c', Q b b' * Q c c' * delta b' c' = Q b b' * Q c b' := by
    intro b'
    have h : ∀ c' : Fin n, Q b b' * Q c c' * delta b' c' = delta c' b' * (Q b b' * Q c c') := by
      intro c'; rw [delta_symm b' c']; ring
    rw [Finset.sum_congr rfl fun c' _ => h c', sum_delta_left b' fun c' => Q b b' * Q c c']
  rw [Finset.sum_congr rfl fun b' _ => inner b', hQ.rows]

/-- **AND THE SCALAR CURVATURE IS INVARIANT OUTRIGHT.** -/
theorem scal_act (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    scal (act Q R) = scal R := by
  simp only [scal]
  rw [Finset.sum_congr rfl fun b _ => ricci_act hQ R b b]
  simp only [act2]
  rw [Finset.sum_comm]
  have inner : ∀ y : Fin n, ∑ b, ∑ z, Q b y * Q b z * ricci R y z
      = ∑ z, delta y z * ricci R y z := by
    intro y
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Finset.sum_mul, hQ.cols]
  rw [Finset.sum_congr rfl fun y _ => inner y]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h : ∀ z : Fin n, delta y z * ricci R y z = delta z y * ricci R y z := by
    intro z; rw [delta_symm y z]
  rw [Finset.sum_congr rfl fun z _ => h z, sum_delta_left y fun z => ricci R y z]

/-- **AND SO THE SECOND MAP IS EQUIVARIANT TOO.** -/
theorem scalDelta_act (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) :
    scal (act Q R) * delta b c = act2 Q (fun b' c' => scal R * delta b' c') b c := by
  have hpull : act2 Q (fun b' c' => scal R * delta b' c') b c = scal R * act2 Q delta b c := by
    simp only [act2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun c' _ => ?_
    ring
  rw [hpull, act2_delta hQ, scal_act hQ]

/-- **BOTH OF §11'S MAPS ARE `O(n)`-EQUIVARIANT.** This is the membership check §11 did not make:
it proved the two independent of each other inside a family it never showed either belonged to.
They do belong to it.

**And no more than that.** The classification's remaining content is that the family has *no other*
members, which is the invariant theory — no averaging over the group, no character, no irreducible
decomposition appears anywhere in this file. `WALLS` §W5.0 §6 item 4 is half a build. -/
theorem traces_equivariant (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∀ b c, ricci (act Q R) b c = act2 Q (ricci R) b c) ∧
      (∀ b c, scal (act Q R) * delta b c
        = act2 Q (fun b' c' => scal R * delta b' c') b c) :=
  ⟨ricci_act hQ R, scalDelta_act hQ R⟩

/-! ### The first invariant-theoretic step, and item 4 complete in dimension two -/

/-- `reflect k` is **diagonal**: it scales slot `b` by `1 − 2δ_{bk}`, which is `−1` at `k` and `1`
elsewhere. Written this way so `act2` against it is two evaluations. -/
theorem reflect_apply (k b b' : Fin n) : reflect k b b' = (1 - 2 * delta b k) * delta b b' := by
  by_cases h : b = b'
  · subst h
    simp only [reflect, delta_self, mul_one]
    by_cases hk : b = k <;> simp [delta, hk]
  · have h0 : delta b b' = 0 := by simp [delta, h]
    simp only [reflect, h0, mul_zero]
    by_cases hk : b = k
    · have hb' : delta b' k = 0 := by
        have : b' ≠ k := by rw [← hk]; exact fun e => h e.symm
        simp [delta, this]
      simp [hb']
    · simp [delta, hk]

theorem act2_reflect (k : Fin n) (S : Fin n → Fin n → ℝ) (b c : Fin n) :
    act2 (reflect k) S b c = (1 - 2 * delta b k) * ((1 - 2 * delta c k) * S b c) := by
  simp only [act2, reflect_apply]
  have inner : ∀ b' : Fin n,
      ∑ c', (1 - 2 * delta b k) * delta b b' * ((1 - 2 * delta c k) * delta c c') * S b' c'
        = (1 - 2 * delta b k) * delta b b' * ((1 - 2 * delta c k) * S b' c) := by
    intro b'
    have h : ∀ c' : Fin n,
        (1 - 2 * delta b k) * delta b b' * ((1 - 2 * delta c k) * delta c c') * S b' c'
          = delta c' c *
            ((1 - 2 * delta b k) * delta b b' * ((1 - 2 * delta c k) * S b' c')) := by
      intro c'; rw [delta_symm c c']; ring
    rw [Finset.sum_congr rfl fun c' _ => h c',
      sum_delta_left c fun c' =>
        (1 - 2 * delta b k) * delta b b' * ((1 - 2 * delta c k) * S b' c')]
  rw [Finset.sum_congr rfl fun b' _ => inner b']
  have h2 : ∀ b' : Fin n,
      (1 - 2 * delta b k) * delta b b' * ((1 - 2 * delta c k) * S b' c)
        = delta b' b * ((1 - 2 * delta b k) * ((1 - 2 * delta c k) * S b' c)) := by
    intro b'; rw [delta_symm b b']; ring
  rw [Finset.sum_congr rfl fun b' _ => h2 b',
    sum_delta_left b fun b' => (1 - 2 * delta b k) * ((1 - 2 * delta c k) * S b' c)]

theorem delta_perm (σ : Equiv.Perm (Fin n)) (x y : Fin n) : delta (σ x) (σ y) = delta x y := by
  by_cases h : x = y
  · subst h; simp [delta_self]
  · have hσ : σ x ≠ σ y := fun e => h (σ.injective e)
    simp [delta, h, hσ]

/-- **The permutation matrices**, the second family of orthogonal frame changes this section uses.
Between them and the reflections they pin an invariant 2-tensor down completely. -/
def permMat (σ : Equiv.Perm (Fin n)) (a b : Fin n) : ℝ := delta (σ a) b

theorem isOrth_permMat (σ : Equiv.Perm (Fin n)) : IsOrth (permMat σ) := by
  constructor
  · intro x y
    simp only [permMat]
    rw [sum_delta_right (σ x) (σ y), delta_perm]
  · intro x y
    simp only [permMat]
    rw [Fintype.sum_equiv σ (fun a => delta (σ a) x * delta (σ a) y)
      (fun z => delta z x * delta z y) fun _ => rfl]
    have h : ∀ z : Fin n, delta z x * delta z y = delta x z * delta y z := by
      intro z; rw [delta_symm z x, delta_symm z y]
    rw [Finset.sum_congr rfl fun z _ => h z, sum_delta_right]

theorem act2_permMat (σ : Equiv.Perm (Fin n)) (S : Fin n → Fin n → ℝ) (b c : Fin n) :
    act2 (permMat σ) S b c = S (σ b) (σ c) := by
  simp only [act2, permMat]
  have inner : ∀ b' : Fin n, ∑ c', delta (σ b) b' * delta (σ c) c' * S b' c'
      = delta (σ b) b' * S b' (σ c) := by
    intro b'
    have h : ∀ c' : Fin n, delta (σ b) b' * delta (σ c) c' * S b' c'
        = delta c' (σ c) * (delta (σ b) b' * S b' c') := by
      intro c'; rw [delta_symm (σ c) c']; ring
    rw [Finset.sum_congr rfl fun c' _ => h c',
      sum_delta_left (σ c) fun c' => delta (σ b) b' * S b' c']
  rw [Finset.sum_congr rfl fun b' _ => inner b']
  have h2 : ∀ b' : Fin n, delta (σ b) b' * S b' (σ c) = delta b' (σ b) * S b' (σ c) := by
    intro b'; rw [delta_symm (σ b) b']
  rw [Finset.sum_congr rfl fun b' _ => h2 b', sum_delta_left (σ b) fun b' => S b' (σ c)]

/-- **A 2-TENSOR FIXED BY EVERY ORTHOGONAL FRAME CHANGE IS A MULTIPLE OF THE METRIC.** This is the
first genuinely invariant-theoretic statement in this file, and it is the shape of the argument the
full classification needs — but it is cheap, because **two families of group elements suffice and
neither requires averaging**. A reflection forces every off-diagonal entry to vanish (it flips the
sign of exactly one of the two slots), and a transposition forces the diagonal entries to agree.
No character, no irreducible decomposition, no integration over the group. -/
theorem eq_smul_delta_of_invariant (i : Fin n) {S : Fin n → Fin n → ℝ}
    (hS : ∀ Q, IsOrth Q → ∀ b c, act2 Q S b c = S b c) (b c : Fin n) :
    S b c = S i i * delta b c := by
  have off : ∀ x y : Fin n, x ≠ y → S x y = 0 := by
    intro x y hxy
    have h := hS (reflect x) (isOrth_reflect x) x y
    rw [act2_reflect, delta_self] at h
    have hyx : delta y x = 0 := by simp [delta, Ne.symm hxy]
    rw [hyx] at h
    linarith
  have diag : ∀ x : Fin n, S x x = S i i := by
    intro x
    have h := hS (permMat (Equiv.swap x i)) (isOrth_permMat _) x x
    rw [act2_permMat, Equiv.swap_apply_left] at h
    exact h.symm
  by_cases h : b = c
  · subst h; rw [delta_self, mul_one]; exact diag b
  · have h0 : delta b c = 0 := by simp [delta, h]
    rw [off b c h, h0, mul_zero]

theorem scal_smul (lam : ℝ) (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    scal (fun a b c d => lam * R a b c d) = lam * scal R := by
  simp only [scal, ricci, Finset.mul_sum]

/-- The one contraction the next theorem needs: four copies of `Q` against a pair of deltas
coupling slot 1 to slot 4 and slot 2 to slot 3. **Two of the four sums collapse on the deltas** and
what is left factors into two row inner products, which orthogonality turns into deltas. -/
theorem sum_act_delta_pair (hQ : IsOrth Q) (a b c d : Fin n) :
    ∑ p : Fin n × Fin n × Fin n × Fin n,
      Q a p.1 * Q b p.2.1 * Q c p.2.2.1 * Q d p.2.2.2 * (delta p.1 p.2.2.2 * delta p.2.1 p.2.2.1)
      = delta a d * delta b c := by
  have hw : ∀ x y z : Fin n, ∑ w, Q a x * Q b y * Q c z * Q d w * (delta x w * delta y z)
      = Q a x * Q b y * Q c z * Q d x * delta y z := by
    intro x y z
    have h : ∀ w : Fin n, Q a x * Q b y * Q c z * Q d w * (delta x w * delta y z)
        = delta w x * (Q a x * Q b y * Q c z * Q d w * delta y z) := by
      intro w; rw [delta_symm x w]; ring
    rw [Finset.sum_congr rfl fun w _ => h w,
      sum_delta_left x fun w => Q a x * Q b y * Q c z * Q d w * delta y z]
  have hz : ∀ x y : Fin n, ∑ z, Q a x * Q b y * Q c z * Q d x * delta y z
      = Q a x * Q b y * Q c y * Q d x := by
    intro x y
    have h : ∀ z : Fin n, Q a x * Q b y * Q c z * Q d x * delta y z
        = delta z y * (Q a x * Q b y * Q c z * Q d x) := by
      intro z; rw [delta_symm y z]; ring
    rw [Finset.sum_congr rfl fun z _ => h z,
      sum_delta_left y fun z => Q a x * Q b y * Q c z * Q d x]
  simp only [Fintype.sum_prod_type]
  have step : ∀ x : Fin n,
      ∑ y, ∑ z, ∑ w, Q a x * Q b y * Q c z * Q d w * (delta x w * delta y z)
        = Q a x * Q d x * ∑ y, Q b y * Q c y := by
    intro x
    have inner : ∀ y : Fin n,
        ∑ z, ∑ w, Q a x * Q b y * Q c z * Q d w * (delta x w * delta y z)
          = Q a x * Q b y * Q c y * Q d x := by
      intro y
      rw [Finset.sum_congr rfl fun z _ => hw x y z, hz x y]
    rw [Finset.sum_congr rfl fun y _ => inner y, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [Finset.sum_congr rfl fun x _ => step x, ← Finset.sum_mul, hQ.rows a d, hQ.rows b c]

/-- **THE CONSTANT-CURVATURE TENSOR IS FIXED BY EVERY ORTHOGONAL FRAME CHANGE, IN EVERY DIMENSION.**

*This replaces a `Fin 2`-only version.* That one went through the one-dimensionality of `Fin 2`:
`act Q` lands back in the space, so it scales the generator by some `λ`, and `scal_act` forces
`2λ = 2`. The argument is short and **does not generalise at all** — it is the line, not the
tensor, doing the work. The proof here is the direct one and is dimension-free: the two deltas of
`constCurv` collapse two of the four summation slots, and orthogonality closes the rest.

So `WALLS` §W5.0 §6 item 4 loses one of the three `n = 2`-specific ingredients §13 leaned on. The
other two — that the domain is a line, and hence that one value determines the map — are the ones
that actually confine `lovelock_two` to two dimensions. -/
theorem act_constCurv (hQ : IsOrth Q) (a b c d : Fin n) :
    act Q (constCurv n) a b c d = constCurv n a b c d := by
  simp only [act]
  have split : ∀ p : Fin n × Fin n × Fin n × Fin n,
      Q a p.1 * Q b p.2.1 * Q c p.2.2.1 * Q d p.2.2.2 * constCurv n p.1 p.2.1 p.2.2.1 p.2.2.2
        = Q a p.1 * Q b p.2.1 * Q c p.2.2.1 * Q d p.2.2.2 *
            (delta p.1 p.2.2.2 * delta p.2.1 p.2.2.1)
          - Q a p.1 * Q b p.2.1 * Q c p.2.2.1 * Q d p.2.2.2 *
            (delta p.1 p.2.2.1 * delta p.2.1 p.2.2.2) := by
    intro p; simp only [constCurv]; ring
  have second : ∑ p : Fin n × Fin n × Fin n × Fin n,
      Q a p.1 * Q b p.2.1 * Q c p.2.2.1 * Q d p.2.2.2 * (delta p.1 p.2.2.1 * delta p.2.1 p.2.2.2)
      = delta a c * delta b d := by
    rw [Fintype.sum_equiv
      ⟨fun p => (p.1, p.2.1, p.2.2.2, p.2.2.1), fun p => (p.1, p.2.1, p.2.2.2, p.2.2.1),
        fun _ => rfl, fun _ => rfl⟩ _
      (fun p : Fin n × Fin n × Fin n × Fin n =>
        Q a p.1 * Q b p.2.1 * Q d p.2.2.1 * Q c p.2.2.2 *
          (delta p.1 p.2.2.2 * delta p.2.1 p.2.2.1))
      fun p => by simp only [Equiv.coe_fn_mk]; ring]
    exact sum_act_delta_pair hQ a b d c
  rw [Finset.sum_congr rfl fun p _ => split p, Finset.sum_sub_distrib,
    sum_act_delta_pair hQ a b c d, second]
  simp only [constCurv]

/-- **AND SO, IN EVERY DIMENSION, AN EQUIVARIANT MAP SENDS THE CONSTANT-CURVATURE TENSOR TO A
MULTIPLE OF THE METRIC.** This is the part of `lovelock_two`'s argument that survives past `n = 2`,
and it is a genuine constraint at every dimension: whatever an equivariant map does to the rest of
the space, on this one direction it agrees with `R ↦ scal R · δ` up to scale.

**It is not the classification and does not approach it.** The space of algebraic curvature tensors
has dimension `6` at `n = 3` and `20` at `n = 4`; this pins the map down on a *line* inside it. -/
theorem equivariant_constCurv (i : Fin n)
    {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    (b c : Fin n) : T (constCurv n) b c = T (constCurv n) i i * delta b c := by
  refine eq_smul_delta_of_invariant i (fun Q hQ b c => ?_) b c
  have h1 := hequiv Q hQ (constCurv n) (isAlgCurv_constCurv n) b c
  have h2 : act Q (constCurv n) = constCurv n := by
    funext a b c d; exact act_constCurv hQ a b c d
  rw [h2] at h1
  exact h1.symm

/-- **AND SO `WALLS` §W5.0 §6 ITEM 4 IS COMPLETE IN DIMENSION TWO** — both halves, not just the
independence half of §11. Any map from algebraic curvature tensors to 2-tensors that is homogeneous
and `O(2)`-equivariant **is** a multiple of `R ↦ scal R · δ`, so the family has no members outside
the span of §11's two maps.

Three things make this affordable where the general case is not. The domain is a *line*
(`eq_smul_constCurv_two`), so the map is determined by one value; the generator is *fixed* by the
group (`act_constCurv`), so that value is an invariant 2-tensor; and an invariant 2-tensor is a
multiple of `δ` (`eq_smul_delta_of_invariant`) by reflections and transpositions alone. **Two of
the three do not survive to `n ≥ 3`** — the space of algebraic curvature tensors has dimension
`6` at `n = 3` and `20` at `n = 4`, so the map is not determined by one value, and what replaces
"the domain is a
line" is the irreducible decomposition this file does not have. *The middle one does survive*: §14
proves `act_constCurv` in every dimension, and `equivariant_constCurv` is what it buys — an
equivariant map is pinned to a multiple of `δ` on that one direction, at every `n`.

Only *homogeneity* is assumed, not additivity — the domain is one-dimensional, so additivity would
be a hypothesis the proof never reaches for. -/
theorem lovelock_two {T : (Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ) → Fin 2 → Fin 2 → ℝ}
    (hom : ∀ (lam : ℝ) (R : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ) (b c : Fin 2),
      T (fun a b c d => lam * R a b c d) b c = lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c) :
    ∃ lam : ℝ, ∀ R, IsAlgCurv R → ∀ b c, T R b c = lam * (scal R * delta b c) := by
  have hinv : ∀ Q, IsOrth Q → ∀ b c,
      act2 Q (T (constCurv 2)) b c = T (constCurv 2) b c := by
    intro Q hQ b c
    have h1 := hequiv Q hQ (constCurv 2) (isAlgCurv_constCurv 2) b c
    have h2 : act Q (constCurv 2) = constCurv 2 := by
      funext a b c d; exact act_constCurv hQ a b c d
    rw [h2] at h1
    exact h1.symm
  have hS := eq_smul_delta_of_invariant (0 : Fin 2) hinv
  refine ⟨T (constCurv 2) 0 0 / 2, fun R hR b c => ?_⟩
  have hrep : R = fun a b c d => -R 0 1 0 1 * constCurv 2 a b c d := by
    funext a b c d; exact eq_smul_constCurv_two hR.antisymm_left hR.antisymm_right a b c d
  have hTR : T R b c = -R 0 1 0 1 * T (constCurv 2) b c := by
    conv_lhs => rw [hrep]
    exact hom _ _ b c
  have hscal : scal R = 2 * -R 0 1 0 1 := by
    conv_lhs => rw [hrep]
    rw [scal_smul, scal_constCurv]
    have hc : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [hc]
    ring
  rw [hTR, hS b c, hscal]
  ring

theorem ricci_smul (lam : ℝ) (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) :
    ricci (fun a b c d => lam * R a b c d) b c = lam * ricci R b c := by
  simp only [ricci, Finset.mul_sum]

/-- **AND THE HYPOTHESES ARE MET BY THE MAP THE CLASSIFICATION IS ACTUALLY ABOUT.** `lovelock_two`
is satisfied by the zero map, so without this it would be a theorem about a class whose only
evident member is trivial — the §3 standard again, now applied to a hypothesis pair. `Ric` is
homogeneous (`ricci_smul`) and equivariant (`ricci_act`), so the classification applies to it.

**And what it produces is `½`, which §11 got by a different route.** The constant `lovelock_two`
extracts is `Ric(constCurv 2)₀₀ / 2 = (2−1)/2`, and `ricci_eq_half_scal_two` says the constant is
`½`. This statement is proved *through* `lovelock_two`, not from §11, so the two agreeing is a
check on the machinery rather than a restatement of it. -/
theorem lovelock_two_ricci :
    ∃ lam : ℝ, ∀ R : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ, IsAlgCurv R → ∀ b c,
      ricci R b c = lam * (scal R * delta b c) :=
  lovelock_two (fun lam R b c => ricci_smul lam R b c)
    (fun _ hQ R _ b c => ricci_act hQ R b c)

end Equivariance

/-! ## 7. What this file does NOT settle

§7 used to record the question §10 has now answered. What remains outside this file is unchanged:
**none of §§5–6, §10, §11 or §12 is a step toward `a₂`.** They are statements about a structure
with four clauses on a finite index type, and the wall named in the header is untouched by them.

§§11–13 narrow one thing and it is worth being exact about which. `WALLS` §W5.0 §6 item 4 has two
halves — *the two named maps are equivariant and independent* and *nothing outside their span is
equivariant*. §11 settles the independence, dimension by dimension, and finds it **false at
`n = 2` and true from `n = 3`**; §12 supplies the equivariance, which §11 had assumed without
checking; §13 settles the second half **in dimension two only** (`lovelock_two`), where the domain
is one-dimensional and the classification collapses to "an invariant 2-tensor is a multiple of the
metric".

**For `n ≥ 3` the second half is not started, and `n = 2` gives no purchase on it.** The three
facts §13 leans on all fail there: the space of algebraic curvature tensors has dimension `6` at
`n = 3` and `20` at `n = 4` rather than `1`, so the map is not determined by one value; what
replaces "the domain is a line" is the irreducible decomposition of that space under `O(n)`, and
nothing in this file computes one. `eq_smul_delta_of_invariant` **does** hold in every dimension
and is the one piece of §13 that transfers.

Two things §12 writes down but does not prove, both said at the point of use: that
`act (Q · Q') = act Q ∘ act Q'`, so `act` is a change-of-frame formula rather than a `MulAction`
(`act_delta` is the identity half and nothing below composes two frames), and that `reflect k` has
determinant `−1`, so nothing here distinguishes `O(n)` from `SO(n)`. -/

end AlgebraicCurvature
