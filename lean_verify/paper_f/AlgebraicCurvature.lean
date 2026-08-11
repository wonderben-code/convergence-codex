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

/-! ## 7. What §§5–6 do NOT settle

They say nothing about **`antisymm_left` alone**. `antisymm_left_of_pair_symm` shows it follows
from `antisymm_right` together with the pair symmetry, so it is redundant in *that* presentation;
whether it follows from `antisymm_right` and `bianchi` without the pair symmetry is **not decided
here and no witness is offered either way**. Nor is any of this a step toward `a₂`: §§5–6 are
statements about a structure with four clauses, and the wall named in the header is untouched by
them. -/

end AlgebraicCurvature
