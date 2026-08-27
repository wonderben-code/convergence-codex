import SteinSumSucc
import InvolutionFixedSum
import LatticeSteinRung

/-!
# The ladder, closed

`LatticeSteinTwo` derived a ladder whose rung `k` is `T_k(a;f) = ∫ ∏ᵢ⟪aᵢ,ω⟫·exp⟪f,ω⟫`, built two
rungs of it, and recorded that the general `k` was **derived and not costed**. Since then:

* `LatticeSteinMajorant` — the dominating function at every order, one lemma instead of a literal
  that doubles per rung;
* `LatticeSteinRung` — the rung step's **integral** reading, at every order;
* `LatticeSteinLadder` — the rung step's **closed** reading, at every order;
* `InvolutionSums`, `PairWeightRep`, `SteinSumRecursion`, `SteinTermTransport`, `SteinSumSucc` —
  the closed form's recursion, carried to the index type the theorem uses;
* `InvolutionFixedSum` — that recursion's double sum, read from the other end.

**This file puts them together.** The two readings of the same derivative are equated, the closed
side is recognised as the closed form one order up, and the induction runs.

## What is proved

* `erase_filter_fixed` — deleting `b` from an involution's fixed points is filtering them by
  `i ≠ b`, which is the one Finset identity the match needs;
* **`steinClosed_deriv_eq`** — `LatticeSteinLadder.hasDerivAt_steinClosed`'s value **is**
  `steinSum` at the appended test function. `InvolutionFixedSum.sum_fixedPoints_comm` and
  `SteinSumSucc.steinSum_succ` are the two halves;
* **`ladder_succ`** — the induction step, by `HasDerivAt.unique` on the two readings;
* **`ladder`** — and hence, at every order,
  `∫ ∏ᵢ⟪aᵢ,ω⟫·exp⟪f,ω⟫ = steinSum a f · exp(½⟨f,Gf⟩)`.

## What this is NOT

**It is not `WickPairings.IsserlisGeneral`.** That theorem is `ladder` at `f = 0`, where the
fixed-point factors vanish and only the perfect matchings survive — and identifying the surviving
sum with `WickPairings.pairProduct` is **not done here**. So general-order Isserlis does not
follow from this file alone, and no claim is made that it does. **Not costed** (`ERRATUM 194`).
-/

namespace LadderStep

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open Equiv Function Involutions PairWeightRep SteinSumRecursion
open LatticeSteinLadder LatticeSteinRung SteinSumSucc InvolutionFixedSum
open LatticeMoments LatticeIsserlisSmeared LatticeSteinIdentity

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The one Finset identity the match needs -/

/-- Deleting `b` from an involution's fixed points is the same as filtering them by `i ≠ b`. The
recursion produces the second form and the derivative produces the first. -/
theorem erase_filter_fixed {n : ℕ} (g : Equiv.Perm (Fin n)) (b : Fin n) :
    (Finset.univ.filter (fun i => g i = i)).erase b
      = Finset.univ.filter (fun i => g i = i ∧ i ≠ b) := by
  ext i
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-! ## 2. The closed side's derivative is the closed form one order up -/

/-- **THE MATCH.** `hasDerivAt_steinClosed`'s value, with `c` taken as the new test function, is
`steinSum` of the extended family times the same exponential. `sum_fixedPoints_comm` turns the
derivative's sum-over-fixed-points into the recursion's sum-over-indices, and `steinSum_succ` is
the recursion. -/
theorem steinClosed_deriv_eq (hm : m ≠ 0) {n : ℕ} (a' : Fin (n + 1) → EuclideanSpace ℝ V)
    (f : EuclideanSpace ℝ V) :
    (∑ σ : ↑(involutions (Fin n)),
        (∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i),
            pairW G m (Fin.tail a') i (σ.1 i))
          * ∑ j ∈ Finset.univ.filter (fun j => σ.1 j = j),
              (∏ i ∈ (Finset.univ.filter (fun i => σ.1 i = i)).erase j,
                fixW G m (Fin.tail a') f i) * dotG G m (a' 0) (Fin.tail a' j))
      + steinSum G m (Fin.tail a') f * dotG G m f (a' 0)
      = steinSum G m a' f := by
  classical
  rw [steinSum_succ hm a' f]
  have hswap : ∑ σ : ↑(involutions (Fin n)),
      (∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), pairW G m (Fin.tail a') i (σ.1 i))
        * ∑ j ∈ Finset.univ.filter (fun j => σ.1 j = j),
            (∏ i ∈ (Finset.univ.filter (fun i => σ.1 i = i)).erase j,
              fixW G m (Fin.tail a') f i) * dotG G m (a' 0) (Fin.tail a' j)
      = ∑ b : Fin n, dotG G m (a' 0) (a' b.succ)
          * ∑ g : {g : Equiv.Perm (Fin n) // g ∈ involutions (Fin n) ∧ g b = b},
              (∏ i ∈ Finset.univ.filter (fun i => i < g.1 i),
                  dotG G m (a' i.succ) (a' (g.1 i).succ))
                * ∏ i ∈ Finset.univ.filter (fun i => g.1 i = i ∧ i ≠ b),
                    dotG G m f (a' i.succ) := by
    have hstep : ∀ σ : ↑(involutions (Fin n)),
        (∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), pairW G m (Fin.tail a') i (σ.1 i))
          * ∑ j ∈ Finset.univ.filter (fun j => σ.1 j = j),
              (∏ i ∈ (Finset.univ.filter (fun i => σ.1 i = i)).erase j,
                fixW G m (Fin.tail a') f i) * dotG G m (a' 0) (Fin.tail a' j)
        = ∑ j ∈ Finset.univ.filter (fun j => σ.1 j = j),
            ((∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i),
                dotG G m (a' i.succ) (a' (σ.1 i).succ))
              * ∏ i ∈ Finset.univ.filter (fun i => σ.1 i = i ∧ i ≠ j),
                  dotG G m f (a' i.succ))
              * dotG G m (a' 0) (a' j.succ) := by
      intro σ
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [erase_filter_fixed]
      simp only [pairW, fixW, Fin.tail]
      ring
    simp only [hstep]
    rw [sum_fixedPoints_comm (α := Fin n) (M := ℝ)
      (fun σ j => ((∏ i ∈ Finset.univ.filter (fun i => i < σ i),
            dotG G m (a' i.succ) (a' (σ i).succ))
          * ∏ i ∈ Finset.univ.filter (fun i => σ i = i ∧ i ≠ j),
              dotG G m f (a' i.succ)) * dotG G m (a' 0) (a' j.succ))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by ring
  rw [hswap]
  ring

/-! ## 3. The induction -/

/-- **THE LADDER, AS A PROPOSITION**, so that the induction hypothesis is available at every test
function — which it must be, since the step differentiates it. -/
def Ladder (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (n : ℕ) : Prop :=
  ∀ (a : Fin n → EuclideanSpace ℝ V) (f : EuclideanSpace ℝ V),
    ∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) * Real.exp (inner ℝ f ω : ℝ) ∂(gaussianField G m)
      = steinSum G m a f * Real.exp (linVar G m f / 2)

/-- **THE STEP.** The two readings of one derivative, equated. -/
theorem ladder_succ (hm : m ≠ 0) {n : ℕ} (ih : Ladder G m n) : Ladder G m (n + 1) := by
  intro a' f
  set c := a' 0 with hc
  set a := Fin.tail a' with ha
  have hfun : (fun s : ℝ => ∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ))
        * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ c ω : ℝ)) ∂(gaussianField G m))
      = fun s : ℝ => steinSum G m a (f + s • c) * Real.exp (linVar G m (f + s • c) / 2) := by
    funext s
    rw [← ih a (f + s • c)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [inner_add_left, real_inner_smul_left]
  have hray := hasDerivAt_rung_ray (G := G) hm a f c
  rw [hfun] at hray
  have hval := hray.unique (hasDerivAt_steinClosed (G := G) hm a f c)
  have hprod : ∀ ω : EuclideanSpace ℝ V,
      (∏ i, (inner ℝ (a' i) ω : ℝ)) * Real.exp (inner ℝ f ω : ℝ)
        = (∏ i, (inner ℝ (a i) ω : ℝ)) * (inner ℝ c ω : ℝ)
            * Real.exp (inner ℝ f ω : ℝ) := by
    intro ω
    rw [Fin.prod_univ_succ]
    simp only [ha, hc, Fin.tail]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hprod), hval,
    ← steinClosed_deriv_eq (G := G) hm a' f]
  simp only [ha, hc]
  ring

/-- **THE LADDER, AT EVERY ORDER.** -/
theorem ladder (hm : m ≠ 0) : ∀ n : ℕ, Ladder G m n
  | 0 => fun a f => ladder_zero hm a f
  | n + 1 => ladder_succ hm (ladder hm n)

end LadderStep
