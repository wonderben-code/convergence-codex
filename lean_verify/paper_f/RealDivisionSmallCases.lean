import RealDivisionPureDim
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Step 3, the two small cases: dimension one is `ℝ` and dimension two is `ℂ`

`RealDivisionPureDim` finished leg (c) step 2 — a finite-dimensional real division algebra has
dimension `1`, `2` or `4` — and its header said the whole remaining gap is step 3, *which* algebra
sits at each dimension. **This file closes two of the three cases.** The one it does not close is
the one Frobenius's theorem is usually remembered for.

> **§1. One lemma does both cases, and would do the third.** `bijective_of_finrank_eq` — an
> `ℝ`-algebra map into `D` from **any division ring** of the same dimension is bijective; the source
> is not assumed commutative. Injectivity is free (`RingHom.injective`: a ring map out of a division
> ring into a nontrivial ring has trivial kernel), and surjectivity is
> `Submodule.eq_top_of_finrank_eq` applied to the range, whose dimension is the source's by
> `LinearMap.finrank_range_of_inj`. **No property of `ℝ` or `ℂ` enters**; the two cases below differ
> only in which map they hand it.
>
> **§2. Dimension one.** `algEquiv_real` — the map is `Algebra.ofId ℝ D`, which every `ℝ`-algebra
> has, and `Module.finrank_self` gives the hypothesis. There is nothing else to check: at dimension
> one the scalars already exhaust `D`.
>
> **§3. Dimension two.** `exists_sq_neg_one` — at dimension at least two the pure part is nonzero
> (`RealDivisionPureSpace.finrank_eq_succ`), so it has an element squaring to `-1`
> (`exists_smul_sq_neg_one`). **That element is exactly what `ℂ` is presented by**, so
> `Complex.liftAux` — Mathlib's universal property, stated for an arbitrary `ℝ`-algebra and not only
> a commutative one — supplies the map, and §1 does the rest. `algEquiv_complex`.
>
> **§4. Packaging.** `real_or_complex_of_finrank_le_two`, and `finrank_eq_four_of_not_iso` — a `D`
> isomorphic to neither is four-dimensional. That one is stated on the equivalence types rather
> than on the dimension, so it needs no converse implication and says something the trichotomy
> alone does not.

**WHAT THIS IS.** Two of Frobenius's three cases, with the classification statement in each:
`dim D = 1` gives `ℝ ≃ₐ[ℝ] D` and `dim D = 2` gives `ℂ ≃ₐ[ℝ] D`. Combined with
`RealDivisionPureDim`, **a real division algebra isomorphic to neither `ℝ` nor `ℂ` has dimension
exactly four.**

**WHAT THIS IS NOT** (`ERRATUM 60`). **The quaternion case is not here.** `dim D = 4 → ℍ ≃ₐ[ℝ] D`
needs a multiplication table on `1, i, j, ij`, not a dimension count.

**AND THE FIRST DRAFT OF THIS PARAGRAPH SAID THE TOOL FOR IT DOES NOT EXIST, WHICH IS FALSE**
(`ERRATUM 410`, and `ERRATUM 42` is the rule that caught it). It said the quaternion case is *"the
one case where the source algebra is noncommutative, so `Complex.liftAux` has no analogue to reach
for"*. **`QuaternionAlgebra.Basis.liftHom` is exactly that analogue**, in
`Mathlib/Algebra/QuaternionBasis.lean`, and its four hypotheses at `ℍ[ℝ] = ℍ[ℝ,-1,0,-1]` are
`i * i = -1`, `j * j = -1`, `i * j = k` and `j * i = -k` — **which is precisely what this chain
already proves** about a normalised orthogonal pure pair and its product. The claim was written
from memory and probed only because this project has a rule against exactly that.

So: **not attempted here**, and the route is now a named one rather than a denial. No cost is
offered (`ERRATUM 194`, `ERRATUM 246`). **Frobenius's theorem does not close in this file.** **No
published tag moves and nothing in the earlier files is restated.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RealDivisionSmallCases

open RealDivisionPure RealDivisionPureForm RealDivisionPureSpace
open RealDivisionFormFun RealDivisionPureBasis RealDivisionPureDim

variable {D : Type*} [DivisionRing D] [Algebra ℝ D] [Module.Finite ℝ D]

/-! ### §1. An algebra map from a field of the same dimension is an isomorphism -/

/-- **The shared step.** Injectivity is free because the source is a division ring; surjectivity is
the dimension hypothesis applied to the range. Nothing here is about `ℝ` or `ℂ`, and the source is
**not** assumed commutative — that is the generality the quaternion case will need, and stating it
now costs nothing (`ERRATUM 274`, `ERRATUM 278`). -/
theorem bijective_of_finrank_eq {K : Type*} [DivisionRing K] [Algebra ℝ K] (f : K →ₐ[ℝ] D)
    (h : Module.finrank ℝ K = Module.finrank ℝ D) : Function.Bijective f := by
  have hinj : Function.Injective f := (f : K →+* D).injective
  refine ⟨hinj, ?_⟩
  have hinjl : Function.Injective (f.toLinearMap : K →ₗ[ℝ] D) := hinj
  have hrange : LinearMap.range (f.toLinearMap : K →ₗ[ℝ] D) = ⊤ :=
    Submodule.eq_top_of_finrank_eq ((LinearMap.finrank_range_of_inj hinjl).trans h)
  exact LinearMap.range_eq_top.mp hrange

/-! ### §2. Dimension one is `ℝ` -/

/-- At dimension one the scalars already exhaust `D`. -/
noncomputable def algEquivReal (h : Module.finrank ℝ D = 1) : ℝ ≃ₐ[ℝ] D :=
  AlgEquiv.ofBijective (Algebra.ofId ℝ D)
    (bijective_of_finrank_eq _ (by rw [Module.finrank_self, h]))

/-- The `Prop` form, so §4 can put it on one side of a disjunction. -/
theorem algEquiv_real (h : Module.finrank ℝ D = 1) : Nonempty (ℝ ≃ₐ[ℝ] D) :=
  ⟨algEquivReal h⟩

/-! ### §3. Dimension two is `ℂ` -/

/-- **The element `ℂ` is presented by.** At dimension at least two the pure part is nonzero, and a
nonzero pure element scales to one squaring to `-1`. -/
theorem exists_sq_neg_one (h : 2 ≤ Module.finrank ℝ D) : ∃ i : D, i * i = -1 := by
  have hsucc := finrank_eq_succ (D := D)
  haveI : Nontrivial (pureSubmodule D) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨u, hu⟩ := exists_ne (0 : pureSubmodule D)
  obtain ⟨t, _, hti⟩ := exists_smul_sq_neg_one (mem_pureSubmodule.mp u.2)
    (fun hc => hu (Submodule.coe_eq_zero.mp hc))
  exact ⟨t • (u : D), by rw [hti]; simp⟩

/-- At dimension two, `Complex.liftAux` at that element is the isomorphism. -/
noncomputable def algEquivComplex (h : Module.finrank ℝ D = 2) : ℂ ≃ₐ[ℝ] D :=
  AlgEquiv.ofBijective (Complex.liftAux _ (exists_sq_neg_one (D := D) (by omega)).choose_spec)
    (bijective_of_finrank_eq _ (by rw [Complex.finrank_real_complex, h]))

/-- The `Prop` form, for the same reason. -/
theorem algEquiv_complex (h : Module.finrank ℝ D = 2) : Nonempty (ℂ ≃ₐ[ℝ] D) :=
  ⟨algEquivComplex h⟩

/-! ### §4. What the two cases leave -/

/-- Below dimension three there are only the two answers. -/
theorem real_or_complex_of_finrank_le_two (h : Module.finrank ℝ D ≤ 2) :
    Nonempty (ℝ ≃ₐ[ℝ] D) ∨ Nonempty (ℂ ≃ₐ[ℝ] D) := by
  rcases finrank_eq_one_two_or_four (D := D) with h1 | h2 | h4
  · exact Or.inl (algEquiv_real h1)
  · exact Or.inr (algEquiv_complex h2)
  · omega

/-- **What is left of Frobenius's theorem, stated where it belongs — on the isomorphisms, not on
the dimension.** A real division algebra isomorphic to neither `ℝ` nor `ℂ` has dimension exactly
four. The hypothesis is `IsEmpty` on the two equivalence types, so nothing here needs the converse
implications *(`D ≃ₐ[ℝ] ℝ` forces `dim D = 1`)*, which are true and are not used. Whether such a `D`
is `ℍ` is not decided here and is not attempted. -/
theorem finrank_eq_four_of_not_iso (h : IsEmpty (ℝ ≃ₐ[ℝ] D)) (h' : IsEmpty (ℂ ≃ₐ[ℝ] D)) :
    Module.finrank ℝ D = 4 := by
  rcases finrank_eq_one_two_or_four (D := D) with h1 | h2 | h4
  · exact (h.false (algEquivReal h1)).elim
  · exact (h'.false (algEquivComplex h2)).elim
  · exact h4

end RealDivisionSmallCases
