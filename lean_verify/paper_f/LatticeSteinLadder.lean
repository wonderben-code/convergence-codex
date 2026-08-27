import LatticeSteinRung
import SteinSumRecursion

/-!
# The rung's closed form, and its derivative

Every record in this project names **one** thing standing between the Wick ladder and
general-order Isserlis: the **closed** reading of a rung — a sum over the involutions of the index
set — has to be differentiated in the test function. `LatticeSteinRung` proved the integral
reading at every order this morning; `SteinSumRecursion` proved the closed form's recursion. This
file writes the closed form down as a term and differentiates it.

## The shape

A rung is `T_n(a; f) = ∫ ∏ᵢ⟪aᵢ,ω⟫·exp⟪f,ω⟫ dμ`, and its closed form is
`steinSum a f · exp(½⟨f,Gf⟩)` where

```
steinSum a f = ∑_{σ ∈ involutions (Fin n)} (∏_{i < σ i} ⟨aᵢ, G a_{σ i}⟩)·(∏_{σ i = i} ⟨f, G aᵢ⟩).
```

**The `f`-dependence is entirely in the second product, and it is affine in `f` factor by
factor** — which is what makes the derivative a finite sum of products with one factor replaced,
and Mathlib's `HasDerivAt.fun_finset_prod` exactly the right tool. The pair product does not mention
`f` at all.

## What is proved

* `steinSum` — the closed form, off `SteinSumRecursion.steinTerm` at the two weights a rung
  carries: `pairW` (propagator between test functions, no `f`) and `fixW f` (propagator against
  `f`);
* `steinSum_repSet_indep` — it does not depend on the representative device, so writing it with
  `<` is a choice and not part of the statement (`PairWeightRep.prod_repSet_eq`, with `dotG_comm`
  as the symmetry);
* `steinSum_zero_eq_one` — at no test functions it is `1`, so the ladder's base case is exactly
  `LatticeGeneratingFunctional.generatingFunctional`;
* **`hasDerivAt_steinSum`** — the derivative in the test function, at every order;
* **`hasDerivAt_steinClosed`** — and the whole closed side, `steinSum · exp(½⟨f,Gf⟩)`, by one
  product rule;
* `ladder_zero` — the base case stated in the ladder's own shape;
* `steinSum_one`, `steinSum_one_derivative_agrees` — **the check**: at one test function the
  closed form is `⟨f,Ga⟩` by direct computation, whose ray derivative is `⟨c,Ga⟩` by inspection,
  and `HasDerivAt.unique` then forces the general formula of `hasDerivAt_steinSum` to evaluate to
  the same thing. Neither route passes through the other.

**WHAT THE RECORDS ASKED FOR, AND WHICH HALF THIS IS.** Every record names the outstanding item as
*"the closed form differentiated in the test function, and matched against the integral's
derivative"*. **The differentiation is this file. The matching is not**, and the section below
says what it needs.

## What is NOT proved, and it is now a re-indexing rather than a derivative

The induction step needs `hasDerivAt_steinClosed`'s value to be recognised as
`steinSum (a with c appended) f`. That identification is
`SteinSumRecursion.sum_steinTerm_option` transported from `Option α` to `Fin (n+1)` — the same
transport `PairingRecursion` performed for `perfectMatchings`, now wanted for `involutions` with
the fixed-point factor carried along. **It is not done here**, and until it is, no rung above the
third is built and general-order Isserlis follows from none of this. **Not costed**
(`ERRATUM 194`).
-/

namespace LatticeSteinLadder

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open LatticeMoments LatticeIsserlis LatticeIsserlisSmeared LatticeIsserlisFour
open LatticeSteinIdentity Involutions PairWeightRep SteinSumRecursion

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The two weights a rung carries -/

/-- The pair weight: the propagator between two of the rung's test functions. **It does not
mention `f`**, which is why the derivative below touches only the other factor. -/
noncomputable def pairW (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) {n : ℕ}
    (a : Fin n → EuclideanSpace ℝ V) : Fin n → Fin n → ℝ :=
  fun i j => dotG G m (a i) (a j)

/-- The fixed-point weight: the propagator against the exponential's test function. **Affine in
`f`**, factor by factor. -/
noncomputable def fixW (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) {n : ℕ}
    (a : Fin n → EuclideanSpace ℝ V) (f : EuclideanSpace ℝ V) : Fin n → ℝ :=
  fun i => dotG G m f (a i)

theorem pairW_comm (hm : m ≠ 0) {n : ℕ} (a : Fin n → EuclideanSpace ℝ V) (i j : Fin n) :
    pairW G m a i j = pairW G m a j i :=
  dotG_comm hm (a i) (a j)

/-! ## 2. The closed form -/

/-- **THE CLOSED FORM OF A RUNG.** One term per involution: the pairs contracted with each other,
the fixed points contracted with `f`. -/
noncomputable def steinSum (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) {n : ℕ}
    (a : Fin n → EuclideanSpace ℝ V) (f : EuclideanSpace ℝ V) : ℝ :=
  ∑ σ : ↑(involutions (Fin n)),
    steinTerm (pairW G m a) (fixW G m a f)
      (Finset.univ.filter (fun i => i < σ.1 i)) σ.1

/-- **THE `<` IS A DEVICE AND NOT PART OF THE STATEMENT.** Any representative choice gives the
same sum, by `PairWeightRep.prod_repSet_eq` with `dotG_comm` as the symmetry. -/
theorem steinSum_repSet_indep (hm : m ≠ 0) {n : ℕ} (a : Fin n → EuclideanSpace ℝ V)
    (f : EuclideanSpace ℝ V) (rep : Equiv.Perm (Fin n) → Finset (Fin n))
    (hrep : ∀ σ ∈ involutions (Fin n), IsRepSet σ (rep σ)) :
    steinSum G m a f
      = ∑ σ : ↑(involutions (Fin n)), steinTerm (pairW G m a) (fixW G m a f) (rep σ.1) σ.1 := by
  refine Finset.sum_congr rfl fun σ _ => ?_
  exact steinTerm_repSet_eq σ.2 (pairW_comm hm a) _ (isRepSet_filter_lt σ.2) (hrep _ σ.2)

/-- At no test functions the closed form is `1`: the one involution of `Fin 0` contributes an
empty pair product and an empty fixed-point product. -/
theorem steinSum_zero_eq_one (a : Fin 0 → EuclideanSpace ℝ V) (f : EuclideanSpace ℝ V) :
    steinSum G m a f = 1 := by
  have h1 : Fintype.card ↑(involutions (Fin 0)) = 1 := card_involutions_fin_zero
  obtain ⟨σ, hσ⟩ := Fintype.card_eq_one_iff.mp h1
  rw [steinSum, Finset.sum_eq_single σ (fun b _ hb => absurd (hσ b) hb) (by simp)]
  simp [steinTerm]

/-- **THE LADDER'S BASE CASE**, and it is exactly the generating functional. -/
theorem ladder_zero (hm : m ≠ 0) (a : Fin 0 → EuclideanSpace ℝ V) (f : EuclideanSpace ℝ V) :
    ∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) * Real.exp (inner ℝ f ω : ℝ) ∂(gaussianField G m)
      = steinSum G m a f * Real.exp (linVar G m f / 2) := by
  rw [steinSum_zero_eq_one, one_mul, linVar]
  simpa using LatticeGeneratingFunctional.generatingFunctional (G := G) hm f

/-! ## 3. The derivative of the closed form

The whole `f`-dependence sits in `∏_{σ i = i} ⟨f, G aᵢ⟩`, each factor affine in the ray parameter,
so `HasDerivAt.finset_prod` applies term by term and the pair product rides along as a constant. -/

/-- Each fixed-point factor is affine along the ray, with slope the propagator against `c`. -/
theorem hasDerivAt_fixW {n : ℕ} (a : Fin n → EuclideanSpace ℝ V)
    (f c : EuclideanSpace ℝ V) (i : Fin n) (s : ℝ) :
    HasDerivAt (fun t : ℝ => fixW G m a (f + t • c) i) (dotG G m c (a i)) s := by
  have h : ∀ t : ℝ, fixW G m a (f + t • c) i = dotG G m f (a i) + t * dotG G m c (a i) := by
    intro t
    simp [fixW, dotG_add_left, dotG_smul_left]
  simpa [h] using
    ((hasDerivAt_id s).mul_const (dotG G m c (a i))).const_add (dotG G m f (a i))

/-- **THE DERIVATIVE OF THE CLOSED FORM, AT EVERY ORDER.** One term per involution and per fixed
point of it: that fixed point's factor is replaced by the propagator against `c`. -/
theorem hasDerivAt_steinSum {n : ℕ} (a : Fin n → EuclideanSpace ℝ V)
    (f c : EuclideanSpace ℝ V) :
    HasDerivAt (fun s : ℝ => steinSum G m a (f + s • c))
      (∑ σ : ↑(involutions (Fin n)),
        (∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), pairW G m a i (σ.1 i))
          * ∑ j ∈ Finset.univ.filter (fun j => σ.1 j = j),
              (∏ i ∈ (Finset.univ.filter (fun i => σ.1 i = i)).erase j,
                fixW G m a f i) * dotG G m c (a j)) 0 := by
  classical
  simp only [steinSum, steinTerm]
  refine HasDerivAt.fun_sum (u := (Finset.univ : Finset ↑(involutions (Fin n)))) ?_
  intro σ _
  have hprod : HasDerivAt
      (fun s : ℝ => ∏ i ∈ Finset.univ.filter (fun i => σ.1 i = i), fixW G m a (f + s • c) i)
      (∑ j ∈ Finset.univ.filter (fun j => σ.1 j = j),
        (∏ i ∈ (Finset.univ.filter (fun i => σ.1 i = i)).erase j,
          fixW G m a (f + (0 : ℝ) • c) i) • dotG G m c (a j)) 0 :=
    HasDerivAt.fun_finset_prod (fun i _ => hasDerivAt_fixW a f c i 0)
  simpa [smul_eq_mul] using hprod.const_mul
    (∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), pairW G m a i (σ.1 i))

/-- The exponential half: `⟨f + sc, G(f + sc)⟩` is quadratic in `s`, so its derivative at `0` is
`⟨f, Gc⟩` — `linVar_add_smul` is where the quadratic is named. -/
theorem hasDerivAt_expLinVar (hm : m ≠ 0) (f c : EuclideanSpace ℝ V) :
    HasDerivAt (fun s : ℝ => Real.exp (linVar G m (f + s • c) / 2))
      (dotG G m f c * Real.exp (linVar G m f / 2)) 0 := by
  have hq : ∀ s : ℝ, linVar G m (f + s • c) / 2
      = linVar G m f / 2 + s * dotG G m f c + s ^ 2 * (linVar G m c / 2) := by
    intro s
    rw [linVar_add_smul hm]
    ring
  have hbase : HasDerivAt
      (fun s : ℝ => linVar G m f / 2 + s * dotG G m f c + s ^ 2 * (linVar G m c / 2))
      (dotG G m f c) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => linVar G m f / 2 + s * dotG G m f c)
        (dotG G m f c) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dotG G m f c)).const_add
        (linVar G m f / 2)
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2 * (linVar G m c / 2)) 0 (0 : ℝ) := by
      simpa using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (linVar G m c / 2))
    simpa using h1.add h2
  simpa [hq, mul_comm] using hbase.exp

/-- **THE CLOSED SIDE OF THE RUNG STEP, AT EVERY ORDER.** One product rule over §3's two halves.
This is the object every record in this project has been calling the last outstanding piece. -/
theorem hasDerivAt_steinClosed (hm : m ≠ 0) {n : ℕ} (a : Fin n → EuclideanSpace ℝ V)
    (f c : EuclideanSpace ℝ V) :
    HasDerivAt (fun s : ℝ => steinSum G m a (f + s • c) * Real.exp (linVar G m (f + s • c) / 2))
      ((∑ σ : ↑(involutions (Fin n)),
          (∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), pairW G m a i (σ.1 i))
            * ∑ j ∈ Finset.univ.filter (fun j => σ.1 j = j),
                (∏ i ∈ (Finset.univ.filter (fun i => σ.1 i = i)).erase j,
                  fixW G m a f i) * dotG G m c (a j))
        * Real.exp (linVar G m f / 2)
        + steinSum G m a f * (dotG G m f c * Real.exp (linVar G m f / 2))) 0 := by
  simpa using (hasDerivAt_steinSum (G := G) (m := m) a f c).mul
    (hasDerivAt_expLinVar (G := G) hm f c)

/-! ## 4. The check, at one test function

`steinSum` at `n = 1` is small enough to compute by hand, and its ray derivative is then visible
by inspection. `HasDerivAt.unique` forces §3's general formula to agree with it — an arithmetic
identity that would fail if the formula's index sets or its `erase` were wrong. -/

/-- The one involution of `Fin 1` is the identity: no pairs, one fixed point. -/
theorem steinSum_one (a f : EuclideanSpace ℝ V) :
    steinSum G m ![a] f = dotG G m f a := by
  have h1 : Fintype.card ↑(involutions (Fin 1)) = 1 := card_involutions_fin_one
  obtain ⟨σ, hσ⟩ := Fintype.card_eq_one_iff.mp h1
  rw [steinSum, Finset.sum_eq_single σ (fun b _ hb => absurd (hσ b) hb) (by simp)]
  have hid : σ.1 = 1 := Subsingleton.elim _ _
  have hlt : (Finset.univ.filter (fun i : Fin 1 => i < σ.1 i)) = ∅ := by
    rw [hid]; decide
  have hfix : (Finset.univ.filter (fun i : Fin 1 => σ.1 i = i)) = {0} := by
    rw [hid]; decide
  have hterm : steinTerm (pairW G m ![a]) (fixW G m ![a] f)
      (Finset.univ.filter (fun i => i < σ.1 i)) σ.1
      = (∏ i ∈ (∅ : Finset (Fin 1)), pairW G m ![a] i (σ.1 i))
        * ∏ i ∈ ({0} : Finset (Fin 1)), fixW G m ![a] f i := by
    rw [steinTerm, hlt, hfix]
  rw [hterm, Finset.prod_empty, Finset.prod_singleton, one_mul, fixW]
  simp

/-- The ray derivative of that, by inspection: `⟨f + sc, Ga⟩` is affine in `s` with slope
`⟨c, Ga⟩`. This route does not mention `hasDerivAt_steinSum`. -/
theorem hasDerivAt_steinSum_one_direct (a f c : EuclideanSpace ℝ V) :
    HasDerivAt (fun s : ℝ => steinSum G m ![a] (f + s • c)) (dotG G m c a) 0 := by
  have h : ∀ s : ℝ, steinSum G m ![a] (f + s • c) = dotG G m f a + s * dotG G m c a := by
    intro s
    rw [steinSum_one, dotG_add_left, dotG_smul_left]
  simpa [h] using ((hasDerivAt_id (0 : ℝ)).mul_const (dotG G m c a)).const_add (dotG G m f a)

/-- **AND THE TWO AGREE, WHICH IS THE CHECK.** `HasDerivAt.unique` turns the agreement of two
independently proved derivatives into an equation between §3's general formula and the
hand-computed answer. A specialisation of `hasDerivAt_steinSum` would have shown nothing. -/
theorem steinSum_one_derivative_agrees (a f c : EuclideanSpace ℝ V) :
    (∑ σ : ↑(involutions (Fin 1)),
        (∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), pairW G m ![a] i (σ.1 i))
          * ∑ j ∈ Finset.univ.filter (fun j => σ.1 j = j),
              (∏ i ∈ (Finset.univ.filter (fun i => σ.1 i = i)).erase j,
                fixW G m ![a] f i) * dotG G m c (![a] j))
      = dotG G m c a :=
  (hasDerivAt_steinSum ![a] f c).unique (hasDerivAt_steinSum_one_direct a f c)

end LatticeSteinLadder
