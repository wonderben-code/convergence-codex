import LatticeWickCount
import LatticeIsserlisFour

/-!
# General-order Isserlis, written down

The `UNLOCK_WATCHLIST` records that this theorem could not even be **stated** here:

> the right-hand side of general-order Isserlis, a sum over pairings, **has no carrier in Mathlib
> today and the first person to want it will have to give one.**

`Involutions.perfectMatchings` is that carrier. This file uses it to write the statement down, and
proves the cases the estate already has by other means.

## The statement

For `k` test functions `f : Fin k → E`, **any `k`, odd or even**,

```
∫ ∏ᵢ ⟪fᵢ, ω⟫ dμ  =  ∑_{σ a pairing of Fin k}  ∏_{i < σ i} ⟨fᵢ, G f_{σ i}⟩
```

At odd `k` the sum is empty, because an odd set has no pairing
(`Involutions.perfectMatchings_eq_empty_of_odd`), and the statement asserts the integral vanishes.
**That half is proved outright**, in `LatticeOddVanishing`, off the field's symmetry under
`ω ↦ −ω`; the even half is the open one.

The inner product runs over `{i | i < σ i}` — **one representative per pair** — which is what makes
`pairProduct` the propagator product of the pairing rather than its square.

## What is proved

* `pairProduct` and **`IsserlisGeneral`**, the statement as a `Prop`. This is the shape
  `IsingTopRatio.UniformSubTopRatio` uses for `W4`'s open item: **a named `Prop` cannot drift**,
  and a later unit either proves it or does not;
* `isserlisGeneral_zero` — `k = 0`. The empty product integrates to `1`, and `Fin 0` has exactly
  one pairing whose product is empty. **Both sides are `1` for different reasons** and the case is
  not vacuous;
* `isserlisGeneral_two` — `k = 2`, which is `LatticeIsserlisSmeared.smeared_twoPoint`;
* **`isserlisGeneral_four`** — `k = 4`, from `LatticeIsserlisFour.isserlis_four`. This is the first
  case where the sum has more than one term, and it is the one that tests whether the statement is
  the RIGHT one: the three pairings of `Fin 4` are enumerated by `decide`, their pair products
  computed, and the result matched against a theorem proved by polarising a fourth moment twice.
  **If `pairProduct` had the wrong index set — every `i` rather than one per pair — this would
  fail**, and nothing else in the file would have noticed;
* `pairProduct_const` and `isserlisGeneral_diagonal` — and the statement holds at **every** even
  `k` when the test functions all coincide, which is a locus rather than three points.

## What is NOT proved

**`IsserlisGeneral G m k` at even `k ≥ 6`.** The odd `k` are proved (`LatticeOddVanishing`),
`k = 0, 2, 4` are proved here, and the diagonal holds at every even `k`; the general even proof
needs Gaussian integration by parts for the correlated field at a
**product** observable, which this estate has only for the exponential
(`LatticeSteinIdentity`) and for a power of one test function (`LatticeWickRecursion`). That is
the watchlist's other blocker, it is unchanged, and **nothing here shortens it**. No estimate is
offered (`ERRATUM 194`).

Finite volume throughout. **No wall moves. No published tag moves.**
-/

namespace WickPairings

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian Nat
open LatticeMoments LatticeIsserlis LatticeIsserlisSmeared LatticeIsserlisFour
open LatticeMomentsGeneral LatticeWickRecursion Involutions

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-- The propagator product a pairing contributes: one factor per PAIR, indexed by the smaller of
its two elements. -/
noncomputable def pairProduct (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) {n : ℕ}
    (f : Fin n → EuclideanSpace ℝ V) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∏ i ∈ Finset.univ.filter (fun i => i < σ i), dotG G m (f i) (f (σ i))

/-- **GENERAL-ORDER ISSERLIS, STATED.** Not proved here beyond `n ≤ 2`; named so that it cannot
drift, in the shape `IsingTopRatio.UniformSubTopRatio` uses for `W4`'s open item. -/
def IsserlisGeneral (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (k : ℕ) : Prop :=
  ∀ f : Fin k → EuclideanSpace ℝ V,
    ∫ ω, ∏ i, (inner ℝ (f i) ω : ℝ) ∂(gaussianField G m)
      = ∑ σ : ↑(perfectMatchings (Fin k)), pairProduct G m f σ.1

/-! ## 1. `n = 0`, where both sides are `1` for different reasons -/

theorem isserlisGeneral_zero : IsserlisGeneral G m 0 := by
  intro f
  have hone : (Finset.univ : Finset ↑(perfectMatchings (Fin 0))) = {⟨1, by decide⟩} := by
    decide
  simp only [Finset.univ_eq_empty, Finset.prod_empty, integral_const, smul_eq_mul, mul_one]
  rw [Finset.sum_congr hone (fun _ _ => rfl), Finset.sum_singleton]
  simp [pairProduct]

/-! ## 2. `n = 1`, which is the smeared two-point function -/

theorem isserlisGeneral_two (hm : m ≠ 0) : IsserlisGeneral G m 2 := by
  intro f
  have hone : (Finset.univ : Finset ↑(perfectMatchings (Fin 2)))
      = {⟨Equiv.swap 0 1, by decide⟩} := by decide
  rw [Finset.sum_congr hone (fun _ _ => rfl), Finset.sum_singleton]
  have hfil : (Finset.univ.filter (fun i : Fin 2 => i < Equiv.swap (0 : Fin 2) 1 i))
      = {0} := by decide
  simp only [pairProduct, hfil, Finset.prod_singleton]
  have hswap : Equiv.swap (0 : Fin 2) 1 0 = 1 := Equiv.swap_apply_left 0 1
  rw [hswap]
  have hprod : ∀ ω : EuclideanSpace ℝ V, (∏ i : Fin 2, (inner ℝ (f i) ω : ℝ))
      = (inner ℝ (f 0) ω : ℝ) * (inner ℝ (f 1) ω : ℝ) := fun ω => by
    rw [Fin.prod_univ_two]
  simp only [hprod]
  exact smeared_twoPoint hm (f 0) (f 1)

/-! ## 3. `n = 2`, which is the case that tests whether the statement is the right one -/

/-- **`n = 2`, FROM `LatticeIsserlisFour.isserlis_four`.** The three pairings of `Fin 4` are
enumerated by `decide`, their index sets `{i | i < σ i}` computed the same way, and the resulting
three products matched against a theorem proved by polarising a fourth moment twice.

**This is the case that can fail.** If `pairProduct` ranged over every `i` rather than one
representative per pair, each term would be the square of what it should be and this proof would
not close; `n = 0` and `n = 1` would not have noticed. -/
theorem isserlisGeneral_four (hm : m ≠ 0) : IsserlisGeneral G m 4 := by
  intro f
  have huniv : (Finset.univ : Finset ↑(perfectMatchings (Fin 4)))
      = {⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide⟩,
         ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by decide⟩,
         ⟨Equiv.swap 0 3 * Equiv.swap 1 2, by decide⟩} := by decide
  rw [Finset.sum_congr huniv (fun _ _ => rfl), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have h1 : (Finset.univ.filter (fun i : Fin 4 =>
      i < (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) i)) = {0, 2} := by decide
  have h2 : (Finset.univ.filter (fun i : Fin 4 =>
      i < (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) i)) = {0, 1} := by decide
  have h3 : (Finset.univ.filter (fun i : Fin 4 =>
      i < (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) i)) = {0, 1} := by decide
  have a1 : (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 0 = 1 := by decide
  have a2 : (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 2 = 3 := by decide
  have b1 : (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) 0 = 2 := by decide
  have b2 : (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) 1 = 3 := by decide
  have c1 : (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) 0 = 3 := by decide
  have c2 : (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) 1 = 2 := by decide
  simp only [pairProduct, h1, h2, h3]
  rw [Finset.prod_insert (by decide), Finset.prod_singleton,
    Finset.prod_insert (by decide), Finset.prod_singleton,
    Finset.prod_insert (by decide), Finset.prod_singleton,
    a1, a2, b1, b2, c1, c2]
  have hprod : ∀ ω : EuclideanSpace ℝ V, (∏ i : Fin 4, (inner ℝ (f i) ω : ℝ))
      = (inner ℝ (f 0) ω : ℝ) * (inner ℝ (f 1) ω : ℝ) * (inner ℝ (f 2) ω : ℝ)
        * (inner ℝ (f 3) ω : ℝ) := fun ω => by
    rw [Fin.prod_univ_four]
  simp only [hprod]
  linear_combination isserlis_four (G := G) hm (f 0) (f 1) (f 2) (f 3)

/-! ## 4. The statement is TRUE at every order on the diagonal

`n ≤ 2` are three points. This is a whole locus, at every `n`: when all `2n` test functions are the
SAME, `IsserlisGeneral`'s right-hand side is `(2n−1)‼·(fᵀGf)^n`, which is exactly what
`LatticeWickCount.moment_eq_card_perfectMatchings` says the left-hand side is.

**This is a check on the STATEMENT and not a step towards proving it.** It says the two sides agree
wherever the test functions coincide; the content of Isserlis is what happens when they do not.
What makes it worth having is that it holds at **every** `n`, so a mis-stated coefficient or a
mis-chosen index set would show up here at some order even if `n = 0, 1, 2` passed. -/

/-- At a constant test function every pairing contributes `(fᵀGf)` once per pair, and there are
`n` pairs — `Involutions.two_mul_card_lt_image`. -/
theorem pairProduct_const (n : ℕ) (f : EuclideanSpace ℝ V)
    (σ : ↑(perfectMatchings (Fin (2 * n)))) :
    pairProduct G m (fun _ => f) σ.1 = (linVar G m f) ^ n := by
  have hcard : 2 * (Finset.univ.filter (fun i => i < σ.1 i)).card = 2 * n := by
    rw [two_mul_card_lt_image σ.2, Fintype.card_fin]
  have hn : (Finset.univ.filter (fun i => i < σ.1 i)).card = n := by omega
  simp only [pairProduct, Finset.prod_const, hn, ← linVar_eq_dotG]

/-- **AND HENCE THE STATEMENT HOLDS AT EVERY ORDER ON THE DIAGONAL.** -/
theorem isserlisGeneral_diagonal (hm : m ≠ 0) (n : ℕ) (f : EuclideanSpace ℝ V) :
    ∫ ω, ∏ _i : Fin (2 * n), (inner ℝ f ω : ℝ) ∂(gaussianField G m)
      = ∑ σ : ↑(perfectMatchings (Fin (2 * n))), pairProduct G m (fun _ => f) σ.1 := by
  have hprod : ∀ ω : EuclideanSpace ℝ V,
      (∏ _i : Fin (2 * n), (inner ℝ f ω : ℝ)) = (inner ℝ f ω : ℝ) ^ (2 * n) := fun ω => by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [hprod, Finset.sum_congr rfl (fun σ _ => pairProduct_const (G := G) n f σ),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hk : (2 * n) / 2 = n := by omega
  rw [LatticeWickCount.moment_eq_card_perfectMatchings hm f (2 * n), hk]

end WickPairings
