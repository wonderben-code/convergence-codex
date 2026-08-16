import LatticeIsserlisSmeared
import GaussianMeasure
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Every even moment of the lattice field, and a `def` that finally has a theorem

`LatticeMoments` computed the moments of `⟪f,·⟫` up to the fourth and stopped, because four is
where the polarisation needed them. This removes the order restriction: **every moment, at every
order**, with the odd ones zero and the even ones `(2k−1)‼·(fᵀGf)^k`.

## The `def` this connects to, which is the reason the unit is worth more than its statement

`GaussianMeasure` has carried, since the estate was audited:

```
/-- The Gaussian moment formula coefficient for the 2k-th moment.
    For X ~ N(0, σ²), E[X^{2k}] = (2k-1)!! · σ^{2k}.
    This function computes the coefficient (2k-1)!!. -/
def gaussianMomentCoeff (k : ℕ) : ℕ := (2 * k - 1)‼
```

together with `gaussianMomentCoeff_zero/_one/_two/_three` whose docstrings read *"The 4th moment
coefficient is 3: E[X⁴] = 3σ⁴"*. **The `def` is honest about being only the coefficient — but no
statement anywhere in the estate connects it to a moment.** `grep` for `gaussianMomentCoeff`
alongside an integral returns nothing; three files (`F3_8k_NonPerturbativeQuantisation`,
`F3_9a_InternalConvergence`, `F4_3g_ClusterExpansion`) consume it as though the identity held.

**`moment_even_eq_coeff` below is that identity**, for this estate's lattice field. It is the same
move `IsingTransferMatrix` made against the certificate shells whose `gap` was a stored scalar: a
number named after a theorem stops being a name and becomes the theorem's value.

## What is proved

* `contDiff_expQuad`, `contDiff_lin`, `iteratedDeriv_lin` — the smoothness and the linear factor's
  derivatives at `0`, which are `0`, `c`, and nothing;
* **`iteratedDeriv_expQuad_rec`** — the recursion `g^{(n+2)}(0) = (n+1)·c·g^{(n)}(0)`, by Leibniz
  (`iteratedDeriv_mul`) on `g' = (c·t)·g`. **The linear factor kills every term of the sum but
  one**, which is why the whole file is short;
* `iteratedDeriv_expQuad_odd`, **`iteratedDeriv_expQuad_even`** — hence `0` and `(2k−1)‼·c^k`;
* **`moment_odd`**, **`moment_even`** — the same for the field:
  `∫ ⟪f,ω⟫^(2k+1) = 0` and `∫ ⟪f,ω⟫^(2k) = (2k−1)‼·(fᵀGf)^k`;
* **`moment_even_eq_coeff`** — stated with `gaussianMomentCoeff`;
* `moment_two_of_general`, `moment_four_of_general` — `LatticeMoments`' two nontrivial cases
  recovered from the general one, which is the check that the generalisation specialises back.

## What this is NOT

**It is the diagonal.** The moments of `⟪f,·⟫` for a single `f` — not
`∫ ⟪f₁,ω⟫⋯⟪f_{2n},ω⟫`, which at order `2n` is a sum over `(2n−1)‼` pairings and needs an index type
for those pairings that **Mathlib does not have**: `IsPerfectMatching` is a predicate on
`SimpleGraph.Subgraph`, not a carrier one can sum over. `LatticeIsserlisFour` does order four by
polarising twice; whether the same trick reaches order six **is not estimated here** (`ERRATUM
181`).

*ADDENDUM, same day. The paragraph above is true about the CLOSED form and is not the whole story:
Wick also has a RECURSIVE statement, `E[X₁⋯X_{2n}] = ∑_{j≥2} ⟨X₁,X_j⟩·E[∏_{i≠1,j} X_i]`, which
needs no pairings type — only `Finset.erase` and a `Finset` product. What THAT needs is Gaussian
integration by parts for the CORRELATED field, which the estate has only for product Gaussians.
So the obstruction is real but it is not the one named here, and the watchlist sub-trigger is
re-pointed accordingly. Recorded before the sentence could be repeated a second time, which is the
narrow rule `ERRATUM 181` left behind.*

**And OS4 does not move.** Finite volume throughout. **No published tag moves**, and in particular
`GaussianMeasure`'s own file is not edited — the connection is made here, in a file that imports it.
-/

namespace LatticeMomentsGeneral

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian Nat
open LatticeMoments LatticeIsserlis LatticeIsserlisSmeared

/-! ## 1. The generating function's derivatives -/

theorem contDiff_expQuad (c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.exp (c * t ^ 2 / 2)) :=
  Real.contDiff_exp.comp (((contDiff_id.pow 2).const_smul c).div_const 2)

theorem contDiff_lin (c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => c * t) :=
  contDiff_const.mul contDiff_id

/-- The linear factor has derivatives `0`, `c`, and then nothing — which is the whole reason the
Leibniz sum below collapses to one term. -/
theorem iteratedDeriv_lin (c : ℝ) (j : ℕ) :
    iteratedDeriv j (fun t : ℝ => c * t) 0 = if j = 0 then 0 else if j = 1 then c else 0 := by
  match j with
  | 0 => simp
  | 1 =>
      rw [iteratedDeriv_one]
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul c).deriv
  | (n + 2) =>
      rw [iteratedDeriv_succ']
      have hd : deriv (fun t : ℝ => c * t) = fun _ => c := by
        funext t
        simpa using ((hasDerivAt_id t).const_mul c).deriv
      rw [hd, iteratedDeriv_const]
      simp

/-- **THE MOMENT RECURSION.** `g^{(n+2)}(0) = (n+1)·c·g^{(n)}(0)`.

`g' = (c·t)·g`, so `g^{(n+2)} = (n+1)`-th derivative of a product, and Leibniz turns that into a
sum over `j` of `C(n+1,j)·(c·t)^{(j)}(0)·g^{(n+1−j)}(0)`. **The linear factor is zero at `0` and
constant thereafter, so only `j = 1` survives.** -/
theorem iteratedDeriv_expQuad_rec (c : ℝ) (n : ℕ) :
    iteratedDeriv (n + 2) (fun t : ℝ => Real.exp (c * t ^ 2 / 2)) 0
      = ((n : ℝ) + 1) * c * iteratedDeriv n (fun t : ℝ => Real.exp (c * t ^ 2 / 2)) 0 := by
  have hd : deriv (fun t : ℝ => Real.exp (c * t ^ 2 / 2))
      = (fun t : ℝ => c * t) * (fun t : ℝ => Real.exp (c * t ^ 2 / 2)) := by
    funext t
    exact (LatticeMoments.hasDerivAt_expQuad c t).deriv
  rw [iteratedDeriv_succ', hd,
    iteratedDeriv_mul ((contDiff_lin c).contDiffAt.of_le (by exact_mod_cast le_top))
      ((contDiff_expQuad c).contDiffAt.of_le (by exact_mod_cast le_top))]
  rw [Finset.sum_eq_single 1]
  · rw [iteratedDeriv_lin]
    simp
  · intro j _ hj
    rw [iteratedDeriv_lin]
    simp [hj]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **THE ODD DERIVATIVES VANISH**, by the recursion off `g'(0) = 0`. -/
theorem iteratedDeriv_expQuad_odd (c : ℝ) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (fun t : ℝ => Real.exp (c * t ^ 2 / 2)) 0 = 0 := by
  induction k with
  | zero =>
      have h := (iteratedDeriv_expQuad c).1
      simpa using h
  | succ j ih =>
      have hidx : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by omega
      rw [hidx, iteratedDeriv_expQuad_rec, ih]
      ring

/-- **AND THE EVEN ONES ARE `(2k−1)‼·cᵏ`.** The double factorial appears because the recursion
multiplies by `2k+1` each time it steps two. -/
theorem iteratedDeriv_expQuad_even (c : ℝ) (k : ℕ) :
    iteratedDeriv (2 * k) (fun t : ℝ => Real.exp (c * t ^ 2 / 2)) 0
      = ((2 * k - 1)‼ : ℝ) * c ^ k := by
  induction k with
  | zero => simp
  | succ j ih =>
      have hidx : 2 * (j + 1) = 2 * j + 2 := by omega
      rw [hidx, iteratedDeriv_expQuad_rec, ih]
      have hdf : (2 * j + 2 - 1)‼ = (2 * j + 1) * (2 * j - 1)‼ := by
        match j with
        | 0 => decide
        | (i + 1) =>
            have h1 : 2 * (i + 1) + 2 - 1 = (2 * i + 1) + 2 := by omega
            have h2 : 2 * (i + 1) + 1 = (2 * i + 1) + 2 := by omega
            have h3 : 2 * (i + 1) - 1 = 2 * i + 1 := by omega
            rw [h1, h2, h3, Nat.doubleFactorial_add_two]
      rw [hdf]
      push_cast
      ring

/-! ## 2. The moments of the field -/

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-- **EVERY ODD MOMENT VANISHES**, at every order — `LatticeMoments` had `n = 1` and `n = 3`. -/
theorem moment_odd (hm : m ≠ 0) (f : EuclideanSpace ℝ V) (k : ℕ) :
    ∫ ω, (inner ℝ f ω : ℝ) ^ (2 * k + 1) ∂(gaussianField G m) = 0 :=
  (moment_eq_iteratedDeriv (G := G) hm f (2 * k + 1)).trans
    (iteratedDeriv_expQuad_odd (linVar G m f) k)

/-- **AND EVERY EVEN MOMENT IS `(2k−1)‼·(fᵀGf)ᵏ`.** `LatticeMoments` had `k = 1` and `k = 2`. -/
theorem moment_even (hm : m ≠ 0) (f : EuclideanSpace ℝ V) (k : ℕ) :
    ∫ ω, (inner ℝ f ω : ℝ) ^ (2 * k) ∂(gaussianField G m)
      = ((2 * k - 1)‼ : ℝ) * (linVar G m f) ^ k :=
  (moment_eq_iteratedDeriv (G := G) hm f (2 * k)).trans
    (iteratedDeriv_expQuad_even (linVar G m f) k)

/-- **THE SAME, WITH `gaussianMomentCoeff`.**

That `def` has been in the estate since the audit, with a docstring saying what `E[X^{2k}]` is and
no statement connecting it to any integral. **This is the connection**, for the lattice field. -/
theorem moment_even_eq_coeff (hm : m ≠ 0) (f : EuclideanSpace ℝ V) (k : ℕ) :
    ∫ ω, (inner ℝ f ω : ℝ) ^ (2 * k) ∂(gaussianField G m)
      = (gaussianMomentCoeff k : ℝ) * (linVar G m f) ^ k :=
  moment_even hm f k

/-! ## 3. Specialising back

A generalisation that does not recover the cases it was built from is a different theorem. -/

/-- `LatticeMoments.moment_two`, from the general form. -/
theorem moment_two_of_general (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m) = linVar G m f := by
  have h := moment_even (G := G) hm f 1
  norm_num at h
  exact h

/-- `LatticeMoments.moment_four`, from the general form — including the factor of three, which is
`3‼`. -/
theorem moment_four_of_general (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ f ω : ℝ) ^ 4 ∂(gaussianField G m) = 3 * (linVar G m f) ^ 2 := by
  have h := moment_even (G := G) hm f 2
  norm_num at h
  exact h

end LatticeMomentsGeneral
