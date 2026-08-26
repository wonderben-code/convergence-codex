import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Data.Real.Sqrt

/-!
# Equal power sums force equal multisets — leg (ii), and leg (iii) from the even ones

`RayleighPow`'s header, and the watchlist item it serves, name three legs of the
trace-to-spectrum bridge. Leg (i) — that `Tr(Aᵏ)` **is** `∑ λᵢᵏ` — has been in the estate since
`TransferPowerSum`. Leg (ii) is the step from *equal power sums* to *equal multisets of
eigenvalues*, and it has stood unbuilt with one line of diagnosis against it:

> **Newton IS the only route** from equal power sums to equal multisets, and it remains the only
> route for a NON-Hermitian matrix.

That diagnosis is correct and this file takes the route. It is deliberately **not** about matrices:
the content is about two families of real numbers, and every matrix statement in this estate that
wants it can supply its own eigenvalue family.

## What Mathlib supplies and what it does not

Mathlib has Newton's identities **formally**, as an identity between multivariate polynomials
(`MvPolynomial.mul_esymm_eq_sum`), together with the evaluation bridge
`MvPolynomial.aeval_esymm_eq_multiset_esymm`. It has Vieta
(`Multiset.prod_X_add_C_eq_sum_esymm`) and the root multiset of a split polynomial
(`Polynomial.roots_multiset_prod_X_sub_C`).

**What it does not have is the implication itself** — `psum_eq_of` … `→ multiset_eq` appears
nowhere, in any spelling. What is done here is the induction that turns the recursion into a
determination, and the two Vieta steps that turn equal symmetric functions back into equal
multisets.

## The two legs, and why they are two

* **`multiset_eq_of_sum_pow_eq`** (leg ii) — equality of `∑ᵢ fᵢᵏ` and `∑ᵢ gᵢᵏ` for
  `1 ≤ k ≤ card σ` forces `f` and `g` to have the same multiset of values. **No positivity, no
  ordering, no Hermitian hypothesis**: this is true of any two real families.
* **`multiset_eq_of_sum_even_pow_eq`** (leg iii) — from the **even** power sums alone, plus
  `0 ≤ fᵢ` and `0 ≤ gᵢ`. This is the shape the spectral-action side of this estate actually has:
  `SpectralAction §9` sees the Yukawa matrix through its **even** moments only, and
  `SpectralActionSpectrum.eigenvalues_nonneg` is what makes the square root unambiguous.

**The separation is the point and it corrects an assumption in the record.** The watchlist item
asks for the legs *"over non-negative reals"*, as if positivity were a hypothesis of the bridge.
It is not: leg (ii) needs none. Positivity is what leg (iii) needs, and it needs it for a different
reason — not to run Newton, but because **even moments determine the multiset of squares**, and
recovering the multiset itself from the multiset of squares is exactly where a sign choice enters.

## Not covered, stated per `ERRATUM 60`

* This says nothing about whether two matrices with equal traces of powers are similar. Equal
  eigenvalue multisets are not similarity — a Jordan block and a diagonal matrix share theirs.
* It gives no bound and no algorithm: `k` power sums determine the multiset of `k` numbers, and
  nothing here is quantitative about how far apart two multisets are when their power sums are
  close.
* It is stated for `ℝ`. The proof uses only that the coefficients live in a characteristic-zero
  domain, so the same argument runs over `ℂ`; that generalisation is **not** taken here, because
  nothing in the estate needs it and an untaken generalisation is worth less than a used one.
-/

namespace PowerSumMultiset

open Finset MvPolynomial

variable {σ : Type*} [Fintype σ]

/-! ## 1. The two evaluation bridges -/

/-- Evaluating the formal power sum at a family gives the family's power sum. -/
private lemma aeval_psum (f : σ → ℝ) (k : ℕ) :
    aeval f (psum σ ℝ k) = ∑ i, f i ^ k := by
  simp [psum]

/-- Shorthand: the `k`-th elementary symmetric function of the family's value multiset. -/
noncomputable def E (f : σ → ℝ) (k : ℕ) : ℝ := (Multiset.map f Finset.univ.val).esymm k

lemma E_zero (f : σ → ℝ) : E f 0 = 1 := by
  simp [E, Multiset.esymm]

/-! ## 2. Newton's recursion, at a family rather than formally -/

/-- **NEWTON'S IDENTITY FOR A FAMILY OF REALS.** `k · eₖ` is a fixed expression in
`e₀, …, e_{k−1}` and `p₁, …, p_k`. This is `MvPolynomial.mul_esymm_eq_sum` evaluated at `f`;
the content is entirely Mathlib's and the evaluation is the only step here. -/
theorem mul_E_eq_sum (f : σ → ℝ) (k : ℕ) :
    (k : ℝ) * E f k
      = (-1) ^ (k + 1) * ∑ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 < k),
          (-1) ^ a.1 * E f a.1 * (∑ i, f i ^ a.2) := by
  have h := congrArg (aeval f) (MvPolynomial.mul_esymm_eq_sum σ ℝ k)
  simpa [E, map_sum, map_mul, map_pow, aeval_esymm_eq_multiset_esymm, aeval_psum,
    map_natCast, map_neg, map_one] using h

/-! ## 3. Leg (ii): equal power sums force equal elementary symmetric functions -/

/-- The induction. If two families agree on every power sum up to `n`, they agree on every
elementary symmetric function up to `n`. Strong induction on `k`: Newton determines `k · eₖ`
from strictly earlier `e`'s and the power sums, and `k ≠ 0` is invertible in `ℝ`. -/
theorem E_eq_of_sum_pow_eq {f g : σ → ℝ} {n : ℕ}
    (h : ∀ k, 1 ≤ k → k ≤ n → ∑ i, f i ^ k = ∑ i, g i ^ k) :
    ∀ k, k ≤ n → E f k = E g k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkn
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [E_zero]
    have hsum : ∑ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 < k),
          (-1 : ℝ) ^ a.1 * E f a.1 * (∑ i, f i ^ a.2)
        = ∑ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 < k),
          (-1 : ℝ) ^ a.1 * E g a.1 * (∑ i, g i ^ a.2) := by
      refine Finset.sum_congr rfl fun a ha => ?_
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at ha
      obtain ⟨hadd, hlt⟩ := ha
      have h1 : E f a.1 = E g a.1 := ih a.1 hlt (le_trans hlt.le hkn)
      have h2 : ∑ i, f i ^ a.2 = ∑ i, g i ^ a.2 := by
        refine h a.2 ?_ ?_
        · omega
        · omega
      rw [h1, h2]
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hfk := mul_E_eq_sum f k
    rw [hsum, ← mul_E_eq_sum g k] at hfk
    exact mul_left_cancel₀ hk0 hfk

/-! ## 4. Leg (ii): back from symmetric functions to the multiset, by Vieta -/

/-- The monic polynomial with the family's values as its roots, written from the elementary
symmetric functions. This is `Multiset.prod_X_add_C_eq_sum_esymm` at the negated multiset, with
`Multiset.esymm_neg` absorbing the sign. -/
private lemma prod_X_sub_C_eq (f : σ → ℝ) :
    (Multiset.map (fun a => Polynomial.X - Polynomial.C a)
        (Multiset.map f Finset.univ.val)).prod
      = ∑ j ∈ Finset.range (Fintype.card σ + 1),
          Polynomial.C ((-1) ^ j * E f j) * Polynomial.X ^ (Fintype.card σ - j) := by
  have hcard : (Multiset.map (fun a => -a) (Multiset.map f Finset.univ.val)).card
      = Fintype.card σ := by simp
  have hprod := Multiset.prod_X_add_C_eq_sum_esymm
    (Multiset.map (fun a => -a) (Multiset.map f Finset.univ.val))
  rw [hcard] at hprod
  have hmap : Multiset.map (fun r => Polynomial.X + Polynomial.C r)
      (Multiset.map (fun a => -a) (Multiset.map f Finset.univ.val))
      = Multiset.map (fun a => Polynomial.X - Polynomial.C a)
        (Multiset.map f Finset.univ.val) := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun a _ => by rw [Function.comp_apply, map_neg, sub_eq_add_neg]
  rw [hmap] at hprod
  refine hprod.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [Multiset.esymm_neg]
  rfl

/-- **LEG (ii). EQUAL POWER SUMS FORCE EQUAL MULTISETS.** If `∑ᵢ fᵢᵏ = ∑ᵢ gᵢᵏ` for every
`1 ≤ k ≤ card σ`, the two families take the same values with the same multiplicities.

**No positivity and no ordering.** The route is Newton's recursion to the elementary symmetric
functions, Vieta back to the monic polynomial with those roots, and the root multiset of a split
polynomial. -/
theorem multiset_eq_of_sum_pow_eq {f g : σ → ℝ}
    (h : ∀ k, 1 ≤ k → k ≤ Fintype.card σ → ∑ i, f i ^ k = ∑ i, g i ^ k) :
    Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val := by
  have hE := E_eq_of_sum_pow_eq h
  have hpoly : (Multiset.map (fun a => Polynomial.X - Polynomial.C a)
        (Multiset.map f Finset.univ.val)).prod
      = (Multiset.map (fun a => Polynomial.X - Polynomial.C a)
        (Multiset.map g Finset.univ.val)).prod := by
    rw [prod_X_sub_C_eq f, prod_X_sub_C_eq g]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hE j (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
  have hf := Polynomial.roots_multiset_prod_X_sub_C (Multiset.map f Finset.univ.val)
  have hg := Polynomial.roots_multiset_prod_X_sub_C (Multiset.map g Finset.univ.val)
  rw [← hf, ← hg, hpoly]

/-! ## 5. Leg (iii): the even power sums, where positivity is what is needed -/

/-- **LEG (iii). THE EVEN POWER SUMS DETERMINE A NON-NEGATIVE FAMILY.**

The hypothesis is `∑ᵢ fᵢ^(2k) = ∑ᵢ gᵢ^(2k)` for `1 ≤ k ≤ card σ` — the moments a spectral action
sees — together with non-negativity of both families.

**Positivity enters here and nowhere earlier.** Leg (ii) applied to the squares gives that `f` and
`g` have the same multiset of SQUARES; going back from that to the same multiset of values is a
choice of square root, and `0 ≤ fᵢ` is what makes it unambiguous. -/
theorem multiset_eq_of_sum_even_pow_eq {f g : σ → ℝ}
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (h : ∀ k, 1 ≤ k → k ≤ Fintype.card σ → ∑ i, f i ^ (2 * k) = ∑ i, g i ^ (2 * k)) :
    Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val := by
  have hsq : Multiset.map (fun i => f i ^ 2) Finset.univ.val
      = Multiset.map (fun i => g i ^ 2) Finset.univ.val := by
    refine multiset_eq_of_sum_pow_eq (fun k hk hkn => ?_)
    have hf' : ∀ i : σ, (f i ^ 2) ^ k = f i ^ (2 * k) := fun i => by
      rw [← pow_mul]
    have hg' : ∀ i : σ, (g i ^ 2) ^ k = g i ^ (2 * k) := fun i => by
      rw [← pow_mul]
    simp only [hf', hg']
    exact h k hk hkn
  have hroot : ∀ (u : σ → ℝ), (∀ i, 0 ≤ u i) →
      Multiset.map u Finset.univ.val
        = Multiset.map Real.sqrt (Multiset.map (fun i => u i ^ 2) Finset.univ.val) := by
    intro u hu
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    rw [Function.comp_apply, Real.sqrt_sq (hu i)]
  rw [hroot f hf, hroot g hg, hsq]

end PowerSumMultiset
