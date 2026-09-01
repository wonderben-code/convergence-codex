import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import Mathlib.Analysis.Quaternion

/-!
# Every element of a finite-dimensional real division algebra satisfies a quadratic

`UNLOCK_WATCHLIST`'s Frobenius item records that `ℝ`, `ℂ` and `ℍ` being the **only**
finite-dimensional real division algebras is absent from this Mathlib — probed by shape, since all
37 files matching `Frobenius` are the characteristic-`p` endomorphism, the Frobenius number or
Frobenius elements — and that `RealDivisionTrichotomy` distinguishes the three without saying they
exhaust anything. The item declines to cost the theorem. **This is its first rung and only its
first rung**, stated so the rest can be named precisely.

> **`natDegree_minpoly_le_two`** — for `D` a division ring, an `ℝ`-algebra, finite-dimensional over
> `ℝ`, the minimal polynomial of any `d : D` has degree at most `2`.
>
> **`exists_quadratic`** — hence `d * d + a • d + b • 1 = 0` for some real `a`, `b`. This is the
> form the rest of Frobenius's proof consumes: it is what makes `{d | d * d ∈ ℝ≤0}` a subspace and
> gives the quadratic form the classification is really about.

## Where the content is, and it is not here

**Mathlib supplies the only hard step.** `Irreducible.degree_le_two` — *an irreducible real
polynomial has degree at most two* — is the fundamental theorem of algebra in the form this needs,
and it is already stated for `Polynomial ℝ`. What this file adds is that a **division ring**'s
minimal polynomials are irreducible (`minpoly.irreducible`, which wants `IsDomain D`, and a
division ring is one) and the passage from the polynomial to the relation. Three lemmas and a case
split on degree `1` against degree `2`.

**THE `d = 1` CASE IS WHY THE STATEMENT IS `∃ a b` AND NOT `d * d = a • d + b • 1`.** At degree `1`
the element is a real scalar and the natural quadratic is `(X + c)²`, not the minimal polynomial;
writing the conclusion as a monic quadratic annihilating `d` covers both degrees uniformly, and the
consumer — a quadratic form on the pure part — wants exactly that.

## What this does NOT do, and it is most of Frobenius's theorem

1. **No classification.** Nothing here says `D` is `ℝ`, `ℂ` or `ℍ`, and nothing here bounds
   `finrank ℝ D`. The remaining legs, named so the item can carry them: **(a)** the *pure* part
   `V = {d | d * d = b • 1 with b ≤ 0}` is an `ℝ`-subspace and `D = ℝ ∙ 1 ⊕ V` — this is where the
   quadratic above is spent; **(b)** `V` carries a negative-definite quadratic form and its
   multiplication makes `D` a quotient of a Clifford algebra; **(c)** `dim V ∈ {0, 1, 3}`.
   **None is attempted and no cost is claimed for any of them** (`ERRATUM 194`, `ERRATUM 246`).
2. **Associativity and finite-dimensionality are hypotheses, not conclusions.** The octonions are a
   real division algebra and are not associative; dropping `Module.Finite` admits transcendental
   elements and the statement is false.
3. **It bears on nothing else in this estate.** `RealDivisionTrichotomy` separates the three named
   families and does not use this; the item's own note says a classification would not close
   `ASSUMPTIONS 49`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RealDivisionQuadratic

open Polynomial

variable {D : Type*} [DivisionRing D] [Algebra ℝ D] [Module.Finite ℝ D]

/-- Every element is integral over `ℝ`, because `D` is finite-dimensional. -/
theorem isIntegral (d : D) : IsIntegral ℝ d := IsIntegral.of_finite ℝ d

/-- **The minimal polynomial has degree at most two.** `minpoly.irreducible` needs `D` to be a
domain, which a division ring is, and `Irreducible.degree_le_two` is the fundamental theorem of
algebra in the shape this consumes. -/
theorem natDegree_minpoly_le_two (d : D) : (minpoly ℝ d).natDegree ≤ 2 :=
  ((minpoly.irreducible (isIntegral d)).natDegree_le_two)

/-- And it is not constant, since `D` is nontrivial. -/
theorem natDegree_minpoly_pos (d : D) : 0 < (minpoly ℝ d).natDegree :=
  minpoly.natDegree_pos (isIntegral d)

/-- **Every element satisfies a MONIC REAL QUADRATIC.** At degree `2` this is the minimal
polynomial itself; at degree `1` the element is a real scalar and the square of the minimal
polynomial serves. Stating it as a polynomial rather than as a relation on `d * d` is what makes
the two degrees one case: `Monic.pow` and `natDegree_pow` do the whole of the degree-`1` branch. -/
theorem exists_monic_quadratic (d : D) :
    ∃ p : Polynomial ℝ, p.Monic ∧ p.natDegree = 2 ∧ aeval d p = 0 := by
  have hint : IsIntegral ℝ d := isIntegral d
  have hmonic : (minpoly ℝ d).Monic := minpoly.monic hint
  have haeval : aeval d (minpoly ℝ d) = 0 := minpoly.aeval ℝ d
  have hle : (minpoly ℝ d).natDegree ≤ 2 := natDegree_minpoly_le_two d
  have hpos : 0 < (minpoly ℝ d).natDegree := natDegree_minpoly_pos d
  interval_cases h : (minpoly ℝ d).natDegree
  · exact ⟨minpoly ℝ d ^ 2, hmonic.pow 2, by rw [natDegree_pow, h], by
      rw [map_pow, haeval]; simp⟩
  · exact ⟨minpoly ℝ d, hmonic, h, haeval⟩

/-- **The same, as a relation.** `d * d + a • d + b • 1 = 0` for real `a`, `b` — the form the
pure-part argument consumes, since it is what makes `{d | d * d ∈ ℝ≤0 • 1}` closed under addition
once the cross terms are collected. -/
theorem exists_quadratic (d : D) : ∃ a b : ℝ, d * d + a • d + b • 1 = 0 := by
  obtain ⟨p, hmonic, hdeg, haeval⟩ := exists_monic_quadratic d
  have hq : p = Polynomial.C (p.coeff 2) * Polynomial.X ^ 2
      + Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) :=
    Polynomial.eq_quadratic_of_degree_le_two
      (by rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdeg]; norm_num)
  have h2 : p.coeff 2 = 1 := by
    have := hmonic.coeff_natDegree
    rwa [hdeg] at this
  rw [hq, h2] at haeval
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, map_one,
    one_mul] at haeval
  refine ⟨p.coeff 1, p.coeff 0, ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, mul_one, ← haeval]
  ring_nf
  rw [sq]

/-- **Not vacuous**: `ℂ` is such an algebra and `Complex.I` really does satisfy `x² + 1 = 0`
(`ERRATUM 201` — a general statement instantiated rather than left standing). -/
theorem exists_quadratic_complex_I :
    ∃ a b : ℝ, Complex.I * Complex.I + a • Complex.I + b • 1 = 0 :=
  exists_quadratic Complex.I

/-- And so does every quaternion, which is the case the classification's third branch is about. -/
theorem exists_quadratic_quaternion (q : Quaternion ℝ) :
    ∃ a b : ℝ, q * q + a • q + b • 1 = 0 :=
  exists_quadratic q

end RealDivisionQuadratic
