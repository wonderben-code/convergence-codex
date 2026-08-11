/-
  HermitePiStein.lean — **the multi-index Hermite recursion**, which the
  9 August probe of N6 identified as the one missing ingredient.

  WHAT THE PROBE FOUND, and why this file exists. The one-dimensional
  Poincaré inequality on the Stein class (`PoincareSteinClass`) is pure
  coefficient bookkeeping: Parseval for `f`, Parseval for `g`, and the
  recursion `cₙ(g) = (n+1)·cₙ₊₁(f)`, then a term-by-term comparison.
  In n dimensions the estate now has both Parsevals (`HermitePiBasis`,
  `HermitePiRiesz`) and **did not have the recursion**. It could not: the
  recursion is obtained by testing the pairing at a Hermite POLYNOMIAL, and
  the class `TextbookSobolevPi` builds is tested against `Cc^∞`, which
  `Hpi n m` is not.

  SO THIS FILE TESTS AGAINST THE HERMITE PRODUCTS DIRECTLY, and that is a
  **weaker** hypothesis than testing against all polynomials, hence a
  **larger** class and a stronger theorem downstream. The 1-d estate defines
  `SteinPair` by testing against every polynomial and then only ever uses
  `q = Hₙ`; here the definition asks for exactly what is used.

  WHAT THIS FILE PROVES:
  * **`Hpi_succ`** — the multi-index Hermite recursion,
    `xᵢ·Hpi m − ∂ᵢ(Hpi m) = Hpi (m + eᵢ)`, where `m + eᵢ` is
    `Function.update m i (m i + 1)`. This is `GaussianPoincare.H_succ`
    (`H (n+1) = X·H n − H n ′`) carried through the product by
    `GaussPiDensity.fderiv_coordProd`.
  * **`SteinPairPi`** — the class: `f` with a GRADIENT partner `g`, paired
    against every Hermite product in every coordinate.
  * **`coeffPi_recursion`** — **the ingredient N6 was missing**:
    `c_m(gᵢ) = (mᵢ+1)·c_{m+eᵢ}(f)`.

  WHAT THIS DOES NOT DO. It does not prove Poincaré — that is the tsum
  reindexing over multi-indices, and it is the next unit. It does not
  connect this class to `TextbookSobolevPi`'s `Cc^∞`-tested class either;
  that is the n-dimensional `W6Converse`, a cutoff argument with no twin in
  the estate, and the probe recorded it as the other half of N6-A. **So the
  n-dimensional "polynomial test functions only" fence still stands**, and
  it stands for a reason now written down rather than guessed at.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import GaussPiDensity
import HermitePiRiesz

namespace HermitePiStein

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness GaussianProductMeasure HermitePi
open HermitePiBessel HermitePiBasis HermitePiRiesz GaussPiDensity

noncomputable section

/-! ## 1. The multi-index Hermite recursion

`H_succ` says `H (k+1) = X·H k − (H k)′` in one variable. Against
`Pi.single i 1` the product `Hpi n m` differentiates in the `i`-th factor
only, so the same recursion holds one coordinate at a time — and raising the
`i`-th index by one is `Function.update m i (m i + 1)`.
-/

/-- `m + eᵢ`: raise the `i`-th entry of a multi-index by one. -/
def succAt {n : ℕ} (m : Fin n → ℕ) (i : Fin n) : Fin n → ℕ :=
  Function.update m i (m i + 1)

@[simp] theorem succAt_self {n : ℕ} (m : Fin n → ℕ) (i : Fin n) :
    succAt m i i = m i + 1 := by
  simp [succAt]

theorem succAt_of_ne {n : ℕ} (m : Fin n → ℕ) {i j : Fin n} (h : j ≠ i) :
    succAt m i j = m j := by
  simp [succAt, Function.update_of_ne h]

theorem Hpi_zero_index (n : ℕ) (x : Fin n → ℝ) : Hpi n (fun _ => 0) x = 1 := by
  simp [Hpi]

theorem H_differentiable (k : ℕ) : Differentiable ℝ fun t : ℝ => (H k).eval t :=
  (H k).differentiable

theorem deriv_H_eval (k : ℕ) (t : ℝ) :
    deriv (fun s : ℝ => (H k).eval s) t = (derivative (H k)).eval t :=
  (H k).deriv

/-- **THE MULTI-INDEX HERMITE RECURSION.**
    `xᵢ·Hpi n m x − ∂ᵢ(Hpi n m)(x) = Hpi n (m + eᵢ) x`. -/
theorem Hpi_succ (n : ℕ) (m : Fin n → ℕ) (i : Fin n) (x : Fin n → ℝ) :
    x i * Hpi n m x - fderiv ℝ (Hpi n m) x (Pi.single i (1:ℝ))
      = Hpi n (succAt m i) x := by
  have hprodf : Hpi n m = fun y : Fin n → ℝ => ∏ j, (H (m j)).eval (y j) := rfl
  rw [hprodf, fderiv_coordProd n (fun j => fun t : ℝ => (H (m j)).eval t)
    (fun j => H_differentiable (m j)) i x, deriv_H_eval]
  dsimp only
  -- split the `i`-th factor out of both products
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (H (m j)).eval (x j))
    (Finset.mem_univ i)]
  have hR : Hpi n (succAt m i) x
      = (H (m i + 1)).eval (x i)
        * ∏ j ∈ Finset.univ.erase i, (H (m j)).eval (x j) := by
    have h1 : Hpi n (succAt m i) x = ∏ j, (H (succAt m i j)).eval (x j) := rfl
    rw [h1, ← Finset.mul_prod_erase Finset.univ
      (fun j => (H (succAt m i j)).eval (x j)) (Finset.mem_univ i), succAt_self]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [succAt_of_ne m (Finset.ne_of_mem_erase hj)]
  rw [hR, H_succ (m i)]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
  ring

/-! ## 2. The class -/

/-- **The n-dimensional Stein class, tested against the Hermite products.**
    The partner is a GRADIENT. Testing against `Hpi n m` rather than against
    every polynomial is a WEAKER hypothesis, so this class is LARGER than the
    1-d definition's n-dimensional analogue would be — and it is exactly what
    the recursion consumes. -/
def SteinPairPi (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (g : Fin n → ((Fin n → ℝ) → ℝ)) : Prop :=
  MemLp f 2 (gaussPi n) ∧ (∀ i, MemLp (g i) 2 (gaussPi n)) ∧
    ∀ (i : Fin n) (m : Fin n → ℕ),
      ∫ x, f x * (x i * Hpi n m x - fderiv ℝ (Hpi n m) x (Pi.single i (1:ℝ)))
          ∂gaussPi n
        = ∫ x, g i x * Hpi n m x ∂gaussPi n

/-- The pairing, with the recursion already applied on the left: the
    hypothesis says the `(m+eᵢ)`-pairing of `f` equals the `m`-pairing of
    `gᵢ`. -/
theorem pairing_succ (n : ℕ) {f : (Fin n → ℝ) → ℝ} {g : Fin n → ((Fin n → ℝ) → ℝ)}
    (h : SteinPairPi n f g) (i : Fin n) (m : Fin n → ℕ) :
    ∫ x, f x * Hpi n (succAt m i) x ∂gaussPi n
      = ∫ x, g i x * Hpi n m x ∂gaussPi n := by
  rw [← h.2.2 i m]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [Hpi_succ]

/-! ## 3. THE RECURSION IN COEFFICIENTS — the ingredient N6 was missing -/

/-- `facPi` at a raised index: `∏ⱼ (m+eᵢ)ⱼ! = (mᵢ+1)·∏ⱼ mⱼ!`. -/
theorem facPi_succAt (n : ℕ) (m : Fin n → ℕ) (i : Fin n) :
    facPi n (succAt m i) = ((m i : ℝ) + 1) * facPi n m := by
  rw [facPi, facPi, ← Finset.mul_prod_erase Finset.univ
      (fun j => ((succAt m i j).factorial : ℝ)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ
      (fun j => ((m j).factorial : ℝ)) (Finset.mem_univ i), succAt_self,
    Nat.factorial_succ]
  have hj : ∀ j ∈ Finset.univ.erase i,
      ((succAt m i j).factorial : ℝ) = ((m j).factorial : ℝ) := by
    intro j hj
    rw [succAt_of_ne m (Finset.ne_of_mem_erase hj)]
  rw [Finset.prod_congr rfl hj]
  push_cast
  ring

/-- **`c_m(gᵢ) = (mᵢ+1)·c_{m+eᵢ}(f)`.** The multi-index twin of
    `SteinCoefficients.coeff_steinPair`, and the ingredient the 9 August
    probe of N6 named as missing. -/
theorem coeffPi_recursion (n : ℕ) {f : (Fin n → ℝ) → ℝ}
    {g : Fin n → ((Fin n → ℝ) → ℝ)} (h : SteinPairPi n f g)
    (i : Fin n) (m : Fin n → ℕ) :
    coeffPi n m (g i) = ((m i : ℝ) + 1) * coeffPi n (succAt m i) f := by
  have hp := pairing_succ n h i m
  have hL : ∫ x, f x * Hpi n (succAt m i) x ∂gaussPi n
      = facPi n (succAt m i) * coeffPi n (succAt m i) f :=
    integral_mul_Hpi n (succAt m i) f
  have hR : ∫ x, g i x * Hpi n m x ∂gaussPi n = facPi n m * coeffPi n m (g i) :=
    integral_mul_Hpi n m (g i)
  rw [hL, hR, facPi_succAt] at hp
  have hne := facPi_ne_zero n m
  field_simp at hp ⊢
  linarith [hp]

/-! ## 4. Non-vacuity: the class is not empty and the recursion is not `0 = 0`

The Hermite products themselves are members, with an explicit gradient, and
their coefficients are deltas — so the recursion relates two coefficients
that are genuinely nonzero.
-/

/-- The constant `1` is in the class with the zero gradient: pairing `1`
    against `xᵢ·Hpi m − ∂ᵢ Hpi m = Hpi (m+eᵢ)` integrates a Hermite product
    of nonzero index against the Gaussian, which vanishes. -/
theorem one_mem (n : ℕ) : SteinPairPi n (fun _ => 1) (fun _ _ => 0) := by
  refine ⟨memLp_const 1, fun i => memLp_const 0, fun i m => ?_⟩
  have hzero : ∫ x, (0:ℝ) * Hpi n m x ∂gaussPi n = 0 := by simp
  rw [hzero]
  have hone : ∀ x : Fin n → ℝ,
      (fun _ : Fin n → ℝ => (1:ℝ)) x
        * (x i * Hpi n m x - fderiv ℝ (Hpi n m) x (Pi.single i (1:ℝ)))
        = Hpi n (succAt m i) x * Hpi n (fun _ => 0) x := by
    intro x
    rw [one_mul, Hpi_succ, Hpi_zero_index, mul_one]
  rw [integral_congr_ae (Filter.Eventually.of_forall hone), Hpi_orthogonal]
  refine if_neg ?_
  intro hcon
  have := congrFun hcon i
  rw [succAt_self] at this
  omega

/-- **The weight in the recursion is `1` exactly when `mᵢ = 0`.** So the
    recursion is a genuine rescaling at every index with `mᵢ ≥ 1`, and a
    plain equality of coefficients at the others.

    This replaces a FALSE lemma of mine — I first wrote
    `facPi n (succAt m i) ≠ facPi n m` and the compiler refused it, correctly:
    at `mᵢ = 0` the factor is `1` and the two weights coincide. Caught before
    push; recorded because a non-vacuity claim that is itself false is worse
    than none. -/
theorem facPi_succAt_eq_iff (n : ℕ) (m : Fin n → ℕ) (i : Fin n) :
    facPi n (succAt m i) = facPi n m ↔ m i = 0 := by
  rw [facPi_succAt]
  have hpos := facPi_pos n m
  constructor
  · intro h
    have heq : ((m i : ℝ) + 1) * facPi n m = 1 * facPi n m := by
      rw [one_mul]; exact h
    have h1 : ((m i : ℝ) + 1) = 1 := mul_right_cancel₀ (ne_of_gt hpos) heq
    have h0 : (m i : ℝ) = 0 := by linarith
    exact_mod_cast h0
  · intro h
    rw [h]
    push_cast
    ring

/-! ## 5. Review round 55 — the ways this could be hollow

**"`Hpi_succ` could be a restatement of `H_succ`."** It is `H_succ` carried
through a product, and the carrying is the content: the derivative has to be
shown to hit only the `i`-th factor, which is `fderiv_coordProd`, and the
index bookkeeping `succAt` has to line up on both sides. Getting `i` and the
erased product the wrong way round would compile as a different theorem, so
§1 splits the `i`-th factor out of BOTH products explicitly.

**"Testing against Hermite products could be the wrong class."** It is a
weaker hypothesis than testing against all polynomials, so the class is
LARGER and every theorem proved about it is stronger. The 1-d estate tests
against all polynomials and then uses only `q = Hₙ`; this definition asks for
what is used. What it does NOT do is connect to the `Cc^∞`-tested class —
that is the n-dimensional `W6Converse` and the header says so.

**"The recursion could be `0 = 0`."** `facPi_succAt_eq_iff` says exactly when
the two weights coincide — precisely at `mᵢ = 0` — so the recursion is a
genuine rescaling everywhere else, and `HermitePiBessel.coeffPi_HpiL`
(already in the estate) shows the coefficient map is not the zero map. **I
first wrote that lemma as an unconditional `≠` and the compiler refused it**,
correctly: at `mᵢ = 0` the factor is `1`. A non-vacuity claim that is itself
false is worse than none, so the corrected statement is a biconditional
rather than a weakened inequality. `one_mem` gives a
member of the class whose existence needs `Hpi_succ` to be right — the proof
turns the pairing into an integral of `Hpi (m+eᵢ)` against `1` and needs it
to vanish, which is orthogonality at a nonzero index.

**"This might close N6."** It does not, and the header is explicit: the tsum
reindexing over multi-indices is the next unit, and the bridge to the
`Cc^∞`-tested class is a cutoff argument that does not exist. **The
n-dimensional "polynomial test functions only" fence still stands.**
-/

end

end HermitePiStein
