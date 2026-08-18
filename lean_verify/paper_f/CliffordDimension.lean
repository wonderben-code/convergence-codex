import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.Data.Complex.Basic

/-!
# `dim CliffordAlgebra Q = 2 ^ dim V`, for every quadratic form at once

`F1_7_SpacetimeForced.clifford_complex_even_dims` states the even-`n` classification table. Its
`n = 2` and `n = 4` conjuncts are genuine — `clifford2_finrank` and `clifford4_finrank`, each built
by a bespoke chain through `CliffordAlgebra.prodEquiv` and the quaternion algebra. Its `n = 6` and
`n = 8` conjuncts are

```
(2 : ℕ) ^ (6 / 2) = 8 ∧ (8 : ℕ) ^ 2 = 64
(2 : ℕ) ^ (8 / 2) = 16 ∧ (16 : ℕ) ^ 2 = 256
```

— true statements about natural numbers standing where statements about algebras should be, with a
recorded reason:

> *"OUT OF SCOPE: would need CliffordAlgebra for 6D quadratic form"*

**That reason prices a technique, not the statement.** Mathlib's `CliffordAlgebra` is defined for
*any* quadratic form on *any* module; there is nothing out of scope about a six-dimensional one.
What the statement needs is a dimension formula, and one formula covers every dimension at once.

> **`finrank_cliffordAlgebra`** — for `V` finite-dimensional over a field `K` with `2` invertible,
> and for **every** `Q : QuadraticForm K V`,
> `Module.finrank K (CliffordAlgebra Q) = 2 ^ Module.finrank K V`.

## The route, in two steps, both of them Mathlib's

`CliffordAlgebra.equivExterior Q : CliffordAlgebra Q ≃ₗ[K] ExteriorAlgebra K V` needs only
`Invertible (2 : K)` — it is `changeFormEquiv` from `Q` to the zero form. And a basis `b` of `V`
indexed by a linearly ordered type gives `b.ExteriorAlgebra`, a basis of `ExteriorAlgebra K V`
indexed by `Finset I`, whose cardinality is `2 ^ card I`. So the whole content is
`Fintype.card_finset` transported across a linear equivalence. **No Clifford algebra is
constructed, no quadratic form is chosen, and no dimension is treated separately.**

## The dimension carries no information about `Q`, and that is the point and the limit

The formula holds for **every** `Q` — nondegenerate, degenerate, or zero — because `equivExterior`
is an equivalence of *modules* regardless. This is what makes `n = 6` and `n = 8` free, and it is
also exactly why the result is weaker than the classification table it fills a hole in:

**A DIMENSION IS NOT AN ISOMORPHISM.** `Cl₆(ℂ) ≅ M₈(ℂ)` is **not proved here and nothing here bears
on it.** The estate already knows the gap is real work: at `n = 4`, `clifford4_matrix4_finrank_eq`
(the dimensions agree) and `CliffordIso`'s `AlgEquiv` (the algebras agree) were separate units, and
the second was much the harder. Since `finrank (CliffordAlgebra Q) = 2 ^ n` for the **zero** form
too, and `CliffordAlgebra 0 = ExteriorAlgebra` is commutative in no useful sense matching `M₈(ℂ)`,
the dimension provably cannot distinguish the algebras in the table. **What is supplied is the
arithmetic conjuncts' subject matter, not the classification.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordDimension

open Module

section General

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **THE EXTERIOR ALGEBRA OF AN `n`-DIMENSIONAL SPACE HAS DIMENSION `2 ^ n`.** A basis of `V`
indexed by `Fin n` gives a basis of `ExteriorAlgebra K V` indexed by `Finset (Fin n)`. -/
theorem finrank_exteriorAlgebra :
    finrank K (ExteriorAlgebra K V) = 2 ^ finrank K V := by
  have b := Module.finBasis K V
  rw [finrank_eq_card_basis b.ExteriorAlgebra, Fintype.card_finset, Fintype.card_fin]

/-- **AND SO DOES THE CLIFFORD ALGEBRA OF ANY QUADRATIC FORM ON IT**, in characteristic not two.
The form is arbitrary: nondegenerate, degenerate and zero all give `2 ^ n`. -/
theorem finrank_cliffordAlgebra [Invertible (2 : K)] (Q : QuadraticForm K V) :
    finrank K (CliffordAlgebra Q) = 2 ^ finrank K V :=
  (CliffordAlgebra.equivExterior Q).finrank_eq.trans (finrank_exteriorAlgebra K V)

/-- **THE FORM THE ESTATE'S OWN CLIFFORD ALGEBRAS NEED.** `Q₄` lives on `(ℂ × ℂ) × (ℂ × ℂ)`,
`Q₁₃` and `Q₃₁` on products of `ℝ`s — **not** on `Fin n → K`. Stating the dimension against a
hypothesis `finrank K V = n` rather than against a chosen carrier is what lets the general theorem
be applied to them, and until it is applied the claim that it subsumes their bespoke chains is
asserted rather than shown. -/
theorem finrank_cliffordAlgebra_of_finrank_eq [Invertible (2 : K)] {n : ℕ}
    (Q : QuadraticForm K V) (hV : finrank K V = n) :
    finrank K (CliffordAlgebra Q) = 2 ^ n := by
  rw [finrank_cliffordAlgebra K V Q, hV]

end General

/-! ## The complex case, which is what `F1_7_SpacetimeForced`'s table is about -/

section Complex

/-- **`dim_ℂ Cl(Q) = 2 ^ n` for every complex quadratic form on an `n`-dimensional space.** The
`Invertible (2 : ℂ)` witness is supplied inside the proof rather than as a global instance: this
file has no business installing one on `ℂ` for the rest of the library. -/
theorem finrank_cliffordAlgebra_complex (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (Q : QuadraticForm ℂ V) :
    finrank ℂ (CliffordAlgebra Q) = 2 ^ finrank ℂ V := by
  haveI : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)
  exact finrank_cliffordAlgebra ℂ V Q

/-- **`dim Cl₆(ℂ) = 64`, THE FIRST CONJUNCT THAT WAS ARITHMETIC.** For every quadratic form on a
six-dimensional complex space, without constructing one. -/
theorem finrank_clifford_six (Q : QuadraticForm ℂ (Fin 6 → ℂ)) :
    finrank ℂ (CliffordAlgebra Q) = 64 := by
  rw [finrank_cliffordAlgebra_complex _ Q]
  simp

/-- **`dim Cl₈(ℂ) = 256`, THE SECOND.** -/
theorem finrank_clifford_eight (Q : QuadraticForm ℂ (Fin 8 → ℂ)) :
    finrank ℂ (CliffordAlgebra Q) = 256 := by
  rw [finrank_cliffordAlgebra_complex _ Q]
  simp

/-- **AND THE TWO THAT WERE ALREADY GENUINE, WITHOUT THEIR CHAINS.** `clifford4_finrank` reaches
`16` through `CliffordAlgebra.prodEquiv` and the quaternion algebra, for one specific `Q₄`; this
reaches it for **every** quadratic form on a four-dimensional complex space. **The original is not
superseded and is not wrong** — it is a different statement about a different object, and the
`prodEquiv` chain is what `CliffordIso` needs for the *algebra* isomorphism, which this cannot
give. What is shown is that the **dimension** never needed the chain. -/
theorem finrank_clifford_four (Q : QuadraticForm ℂ (Fin 4 → ℂ)) :
    finrank ℂ (CliffordAlgebra Q) = 16 := by
  rw [finrank_cliffordAlgebra_complex _ Q]
  simp

/-- The `n = 2` entry likewise. -/
theorem finrank_clifford_two (Q : QuadraticForm ℂ (Fin 2 → ℂ)) :
    finrank ℂ (CliffordAlgebra Q) = 4 := by
  rw [finrank_cliffordAlgebra_complex _ Q]
  simp

/-- **THE TABLE'S SHAPE, FOR EVERY EVEN `n` AT ONCE.** `Cl_{2k}(ℂ)` has dimension `2 ^ (2k)`, which
is `(2 ^ k) ^ 2` — the square of the matrix size the classification predicts. **This is a
statement about dimensions matching, not about algebras being isomorphic**; it says the arithmetic
in the table is consistent with the classification, which is all the arithmetic conjuncts ever
said. -/
theorem finrank_clifford_even (k : ℕ) (Q : QuadraticForm ℂ (Fin (2 * k) → ℂ)) :
    finrank ℂ (CliffordAlgebra Q) = (2 ^ k) ^ 2 := by
  have h : finrank ℂ (Fin (2 * k) → ℂ) = k * 2 := by simp [Nat.mul_comm]
  rw [finrank_cliffordAlgebra_complex _ Q, h, pow_mul]

end Complex

/-! ## The real case, which the Minkowski files need -/

section Real

/-- **`dim_ℝ Cl(Q) = 2 ^ n` over the reals**, which covers the signatures
`CliffordRealMinkowski` and `CliffordRealMajorana` work with: both reach `16` for their own
`Q₁₃` and `Q₃₁` through `prodEquiv`, and both dimensions are this theorem at `n = 4`. As above,
**their algebra isomorphisms are untouched** — those are the content and this is not it. -/
theorem finrank_cliffordAlgebra_real (V : Type*) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V) :
    finrank ℝ (CliffordAlgebra Q) = 2 ^ finrank ℝ V := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  exact finrank_cliffordAlgebra ℝ V Q

end Real

end CliffordDimension
