/-
  TextbookSobolevPiSharp.lean — the n-dimensional Gaussian Poincaré constant
  is SHARP, in the quantified sense, on the textbook Sobolev space.

  WHY THIS FILE EXISTS. The 1-dimensional chain says two different things
  about the constant `1`, and the n-dimensional chain says only the weaker
  of them.

  * ATTAINED. There is a member of the class on which the two sides of
    Poincaré are equal. In 1 dimension that is
    `TextbookSobolev.poincare_sobolevWeak_sharp`; in n dimensions it is
    `TextbookSobolevPiScaled.poincare_sharp_var`, and at variance 1 the
    estate has both halves (`W6ConversePi.coord_sobolevWeakPi` puts the
    coordinate in the class, `HermitePiPoincare.coord_var` computes its
    variance) and never composed them.
  * NO SMALLER CONSTANT WORKS. A statement quantified over every candidate
    constant `c`: if `c` serves EVERY member of the class then `1 ≤ c`.
    In 1 dimension that is `PoincareSteinScaled.no_better_constant_scaled`.
    ⚠ **THE NEXT CLAUSE IS FALSE AND IS KEPT AS WRITTEN** (`ERRATUM 94`,
    `ERRATUM 547`). `GaussianPoincareProduct.no_better_constant_MV` and
    `GaussianProductMeasure.no_better_constant_measure` are both n-dimensional
    *no smaller constant works* statements — for the POLYNOMIAL class and for it
    at measure level. **What is true is narrower and is what this file
    contributes**: the estate does not have it for the SOBOLEV/STEIN classes —
    the textbook Lebesgue-weak-derivative class, the `Cc^∞`-tested class, or the
    Hermite-tested class — which are the three §3 covers. The two classes are
    nested (a polynomial with its gradient is a textbook member) so this file's
    statement is the stronger, and **that nesting is not proved here**: it needs
    `MvPolynomial` evaluation to be `ContDiff` and `MemLp`, neither of which is
    in Mathlib or this estate, so it is a unit of plumbing and not a remark
    (`ERRATUM 246`).

    ⚠ **THE PRECEDING REPAIR IS ITSELF WRONG IN ONE CLAUSE AND IS KEPT AS
    WRITTEN** (`ERRATUM 94`, `ERRATUM 548`). *"so this file's statement is the
    stronger"* is **backwards**. Both theorems read *if `c` serves every member
    of the class then `1 ≤ c`*; polynomials sit INSIDE the textbook class, so
    quantifying over the textbook class is the STRONGER hypothesis, and a
    theorem with a stronger hypothesis is the WEAKER theorem.
    `no_better_constant_sobolevWeakPi` is a **corollary** of
    `no_better_constant_MV`, not a strengthening of it. The nesting the clause
    said is not proved here is now proved — `MvPolynomialSobolev` (2026-09-13)
    has the `ContDiff` and `MemLp` halves and the membership
    `sobolevWeakPi_eval`, and derives this file's conclusion from the
    polynomial one in `no_better_constant_sobolevWeakPi_of_MV`. **This file's
    own proof is not withdrawn**: it proves the same conclusion independently,
    from `coord_sobolevWeakPi` and the estate's own attainment, with no
    polynomial anywhere. What was wrong was one word about which of two
    theorems implies the other. The false clause:
    **In n dimensions the estate does not have it in any class**, and
    `poincare_sharp_var`'s own docstring asserts it in prose — *"so the
    constant is attained and no smaller one can work"* — with nothing
    proving the second clause. Attainment is a fact about one function;
    "no smaller constant works" quantifies over all constants, and the
    second does not follow from the first by unfolding a definition.

  The gap was found by `RE-SWEEP #27`, batch 20, comparing the 1-d and n-d
  Gaussian-Sobolev chains declaration by declaration rather than by reading
  either chain's prose.

  WHAT THIS FILE PROVES.

  1. `var_coordPi`, `gradSq_coordPi` — the two sides at the coordinate
     witness, at variance 1: both are `1`.
  2. `poincare_sobolevWeakPi_sharp` — ATTAINMENT on the textbook class at
     variance 1, the twin of `TextbookSobolev.poincare_sobolevWeak_sharp`.
  3. **`no_better_constant_sobolevWeakPi`** — the quantified statement, on
     the textbook Lebesgue-weak-derivative class.
  4. `no_better_constant_smoothSteinPairPi`, `no_better_constant_steinPairPi`
     — the same on the `Cc^∞`-tested and the Hermite-tested classes. Three
     descriptions of one class, so the three are equivalent; they are stated
     separately because a reader consuming one of them should not have to
     route through `SteinSmoothPi` to see it.
  5. **`no_better_constant_smoothSteinPairPiVar`** — and at EVERY variance:
     any `c` serving every σ-pair satisfies `σ² ≤ c`. This is the twin of
     `no_better_constant_scaled` and is the strongest statement in the
     n-dimensional chain.
  6. `sobolevWeakPi_witnesses`, `poincare_sobolevWeakPi_of_coeff` — the last
     two 1-d statements with no n-d twin: the two named members of the
     textbook class, and Poincaré entered from the coefficient condition.

  WHAT IT DOES NOT PROVE. Nothing here is about a class larger than the one
  already built, and nothing here needs `n ≥ 1` to be interesting except by
  necessity: every statement in §3–§5 takes a coordinate index `i : Fin n`,
  so at `n = 0` there is no witness and the theorems are vacuous rather than
  false. That is not a defect of the constant — at `n = 0` the measure is a
  point mass, every variance is `0`, and every constant serves.
-/
import TextbookSobolevPiScaled

namespace TextbookSobolevPiSharp

open MeasureTheory ProbabilityTheory Filter Topology
open GaussianProductMeasure HermitePi HermitePiStein HermitePiPoincare
open TextbookSobolevPi W6ConversePi SteinSmoothPi HermitePiCoeff
open TextbookSobolevPiScaled

noncomputable section

variable {n : ℕ}

/-! ## 1. The two sides at the coordinate witness, at variance 1 -/

/-- The variance of the coordinate function `x ↦ xᵢ` under `γⁿ` is `1`.
    `HermitePiPoincare.coord_var` says this at the multi-index `eᵢ`, and
    `Hpi_single_eq_coord` is the identification of that Hermite product with
    the coordinate. -/
theorem var_coordPi (n : ℕ) (i : Fin n) :
    (∫ x : Fin n → ℝ, x i * x i ∂gaussPi n)
        - (∫ x : Fin n → ℝ, x i ∂gaussPi n) ^ 2 = 1 := by
  have h := HermitePiPoincare.coord_var n i
  simpa only [Hpi_single_eq_coord] using h

/-- The squared weak gradient of the coordinate integrates to `1`: the
    gradient is the constant vector `eᵢ`, and `γⁿ` is a probability
    measure. -/
theorem gradSq_coordPi (n : ℕ) (i : Fin n) :
    (∑ j : Fin n, ∫ _x : Fin n → ℝ,
        (if j = i then (1:ℝ) else 0) * (if j = i then (1:ℝ) else 0) ∂gaussPi n) = 1 := by
  classical
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]; simp
  · intro j _ hj; rw [if_neg hj]; simp
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-! ## 2. Attainment on the textbook class -/

/-- **THE CONSTANT IS ATTAINED ON THE TEXTBOOK CLASS.** The coordinate
    function is a member with weak gradient `eᵢ`, and for it the two sides
    of `W6ConversePi.poincare_sobolevWeakPi` are equal — both are `1`.
    The twin of `TextbookSobolev.poincare_sobolevWeak_sharp`. -/
theorem poincare_sobolevWeakPi_sharp (n : ℕ) (i : Fin n) :
    SobolevWeakPi n (fun x => x i) (fun j _ => if j = i then (1:ℝ) else 0)
      ∧ (∫ x : Fin n → ℝ, x i * x i ∂gaussPi n)
            - (∫ x : Fin n → ℝ, x i ∂gaussPi n) ^ 2
          = ∑ j : Fin n, ∫ _x : Fin n → ℝ,
              (if j = i then (1:ℝ) else 0) * (if j = i then (1:ℝ) else 0) ∂gaussPi n :=
  ⟨coord_sobolevWeakPi n i, by rw [var_coordPi n i, gradSq_coordPi n i]⟩

/-! ## 3. No smaller constant works — the quantified statement -/

/-- **NO SMALLER CONSTANT WORKS, ON THE TEXTBOOK CLASS.** If `c` serves
    every member of `SobolevWeakPi n` then `1 ≤ c`. This is the statement
    `poincare_sobolevWeakPi` needs in order to say that `1` is THE constant
    rather than SOME constant, and it is what the n-dimensional chain was
    missing: the estate had attainment at one function and nothing
    quantified over `c`. -/
theorem no_better_constant_sobolevWeakPi (n : ℕ) (i : Fin n) (c : ℝ)
    (h : ∀ (f : (Fin n → ℝ) → ℝ) (g : Fin n → ((Fin n → ℝ) → ℝ)),
      SobolevWeakPi n f g →
        (∫ x, f x * f x ∂gaussPi n) - (∫ x, f x ∂gaussPi n) ^ 2
          ≤ c * ∑ j : Fin n, ∫ x, g j x * g j x ∂gaussPi n) :
    1 ≤ c := by
  have hx := h _ _ (coord_sobolevWeakPi n i)
  rw [gradSq_coordPi n i, mul_one, var_coordPi n i] at hx
  exact hx

/-- The same on the `Cc^∞`-tested class. -/
theorem no_better_constant_smoothSteinPairPi (n : ℕ) (i : Fin n) (c : ℝ)
    (h : ∀ (f : (Fin n → ℝ) → ℝ) (g : Fin n → ((Fin n → ℝ) → ℝ)),
      SmoothSteinPairPi n f g →
        (∫ x, f x * f x ∂gaussPi n) - (∫ x, f x ∂gaussPi n) ^ 2
          ≤ c * ∑ j : Fin n, ∫ x, g j x * g j x ∂gaussPi n) :
    1 ≤ c :=
  no_better_constant_sobolevWeakPi n i c fun f g hfg =>
    h f g ((smoothSteinPairPi_iff_sobolevWeakPi n f g).mpr hfg)

/-- And on the Hermite-tested class, which is the one
    `HermitePiPoincare.poincare_steinPi` is stated for. -/
theorem no_better_constant_steinPairPi (n : ℕ) (i : Fin n) (c : ℝ)
    (h : ∀ (f : (Fin n → ℝ) → ℝ) (g : Fin n → ((Fin n → ℝ) → ℝ)),
      SteinPairPi n f g →
        (∫ x, f x * f x ∂gaussPi n) - (∫ x, f x ∂gaussPi n) ^ 2
          ≤ c * ∑ j : Fin n, ∫ x, g j x * g j x ∂gaussPi n) :
    1 ≤ c :=
  no_better_constant_sobolevWeakPi n i c fun f g hfg =>
    h f g ((steinPairPi_iff_sobolevWeakPi n f g).mpr hfg)

/-! ## 4. At every variance -/

/-- The squared gradient at variance σ², which is again `1` because
    `gaussPiVar σ n` is a probability measure and the gradient is `eᵢ`. -/
theorem gradSq_coordPiVar (σ : ℝ) (n : ℕ) (i : Fin n) :
    (∑ j : Fin n, ∫ _x : Fin n → ℝ,
        (if j = i then (1:ℝ) else 0) * (if j = i then (1:ℝ) else 0)
          ∂gaussPiVar σ n) = 1 := by
  classical
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]; simp
  · intro j _ hj; rw [if_neg hj]; simp
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- **σ² IS SHARP AT EVERY σ ≠ 0, IN THE QUANTIFIED SENSE.** If `c` serves
    every σ-pair then `σ² ≤ c`. The twin of
    `PoincareSteinScaled.no_better_constant_scaled`, and the strongest
    sharpness statement in the n-dimensional chain: `poincare_sharp_var`
    exhibits a function on which both sides are `σ²`, which by itself leaves
    open whether some smaller constant serves the whole class. -/
theorem no_better_constant_smoothSteinPairPiVar {σ : ℝ} (hσ : σ ≠ 0)
    (i : Fin n) (c : ℝ)
    (h : ∀ (f : (Fin n → ℝ) → ℝ) (g : Fin n → ((Fin n → ℝ) → ℝ)),
      SmoothSteinPairPiVar σ n f g →
        (∫ x, f x * f x ∂gaussPiVar σ n) - (∫ x, f x ∂gaussPiVar σ n) ^ 2
          ≤ c * ∑ j : Fin n, ∫ x, g j x * g j x ∂gaussPiVar σ n) :
    σ ^ 2 ≤ c := by
  have hx := h _ _ (coord_memVar hσ i)
  rw [gradSq_coordPiVar σ n i, mul_one, var_coord_scaled σ i] at hx
  exact hx

/-! ## 5. The last two statements with no n-dimensional twin -/

/-- **THE TWO NAMED WITNESSES, IN THE TEXTBOOK CLASS.** The twin of
    `TextbookSobolev.sobolevWeak_witnesses`: the coordinate, and its
    absolute value with the sign function as weak gradient. The second is
    the one that matters — it is not a.e. equal to any differentiable
    function, so the textbook class is strictly larger than the `C¹` one. -/
theorem sobolevWeakPi_witnesses (n : ℕ) (i : Fin n) :
    SobolevWeakPi n (fun x => x i) (fun j _ => if j = i then (1:ℝ) else 0)
      ∧ SobolevWeakPi n (AbsSteinWitnessPi.absCoord n i)
          (AbsSteinWitnessPi.sgnCoord n i) :=
  ⟨coord_sobolevWeakPi n i, absCoord_sobolevWeakPi n i⟩

/-- **POINCARÉ ENTERED FROM THE COEFFICIENT CONDITION**, on the textbook
    class — the twin of `TextbookSobolev.poincare_sobolevWeak_of_coeff`.
    The hypothesis is a statement about Hermite coefficients alone; the
    conclusion produces a weak gradient and the inequality for it. So the
    whole n-dimensional chain — Hermite pairing, `Cc^∞` pairing, Lebesgue
    weak derivatives, coefficients, and the inequality — closes on one
    object, as it does in 1 dimension. -/
theorem poincare_sobolevWeakPi_of_coeff {f : (Fin n → ℝ) → ℝ}
    (hf : MemLp f 2 (gaussPi n)) (hsum : Summable (wt n f)) :
    ∃ g : Fin n → ((Fin n → ℝ) → ℝ), SobolevWeakPi n f g ∧
      (∫ x, f x * f x ∂gaussPi n) - (∫ x, f x ∂gaussPi n) ^ 2
        ≤ ∑ j : Fin n, ∫ x, g j x * g j x ∂gaussPi n := by
  obtain ⟨g, hg⟩ := (sobolevWeakPi_iff_summable hf).mpr hsum
  exact ⟨g, hg, poincare_sobolevWeakPi n hg⟩

/-! ## 6. Review round 59 — the ways this could be hollow

**"§3 could be vacuous at every `n`."** It takes an `i : Fin n`, so at
`n = 0` there is no such `i` and nothing is claimed. At every `n ≥ 1` the
hypothesis is satisfiable — `poincare_sobolevWeakPi` itself satisfies it
with `c = 1`, so the theorems say exactly that `1` is the least such `c`
and not that no `c` exists.

**"§3 could be `poincare_sharp_var` with the quantifier written in."** It
could not: `poincare_sharp_var` produces an equality at one function, and
its hypothesis is nothing. §3's hypothesis quantifies over the whole class,
and the content is that the witness lies INSIDE that class — which is
`coord_sobolevWeakPi`, proved from the Lebesgue definition and not from
either pairing.

**"The three classes in §3 make it look like three theorems."** They are
one theorem and two corollaries, and the corollaries are one line each; the
docstrings say so. What makes them worth stating is that a reader holding
`poincare_steinPi` should not have to know `SteinSmoothPi` exists to learn
that its constant is least.

**"§5's second witness could be reached by going round through §4 of
`SteinSmoothPi`."** It is: `absCoord_sobolevWeakPi` is proved there from
`AbsSteinWitnessPi.absCoord_steinPairPi` through the class equality. That
is not circular for this purpose — the equality of classes is a theorem,
not a definition — but it is worth naming, because the coordinate witness
in §2 deliberately does NOT go that way and the two are not the same kind
of fact.
-/

end

end TextbookSobolevPiSharp
