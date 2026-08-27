import PairingWeight
import IsserlisAll

/-!
# Relabelling a pairing sum, and the correlation factorises across a split

`PairingWeight.sum_prod_eq_mul` factorises the pairing SUM when the weight across a split
vanishes. `IsserlisAll.isserlisGeneral_all` identifies a pairing sum with a Gaussian INTEGRAL —
but at `Fin k`, and the two sides of a split are subtypes of `Fin k`. **This file is the
relabelling that closes the gap, and the theorem it buys.**

## The relabelling costs nothing, and the reason is `PairWeightRep`

Transporting `∑ over the matchings of ι` to `∑ over the matchings of κ` along an equivalence moves
the `<`-device to a set that is no longer a `<`-filter, because an equivalence need not preserve
order. **That does not matter**, and `PairWeightRep.prod_repSet_eq` is why: for a symmetric
weight, the product does not depend on which representative is taken from each pair. So no order
hypothesis appears below.

## What is proved

* **`sum_pm_transport`** — the pairing sum is invariant under relabelling the index type, for a
  symmetric weight;
* **`integral_prod_split`** — **the theorem**: for the correlated Gaussian field on a finite
  graph, if the propagator between two groups of test functions vanishes, the correlation of all
  of them is the product of the two groups' correlations, **at every order**;
* **`integral_prod_split_two_agrees`** — **the check, and the two routes share no step.** At two
  test functions split one and one, `integral_prod_split` says the product of the two one-function
  correlations equals the two-point function. `LatticeIsserlisSmeared.smeared_twoPoint` computes
  that two-point function directly, by polarising a second moment — no pairings, no ladder, no
  split. The identity is that the four-file route and the polarisation route give the same number.

## What is NOT here

The estimate. This is the case where the cross-propagator is **exactly zero**; clustering proper
bounds the difference when it is merely small, and that needs the crossing terms counted and
bounded rather than deleted. **Not costed** (`ERRATUM 194`). Finite volume throughout.
-/

namespace PairingRelabel

open Equiv Function Involutions PairWeightRep PairingSplit PairingRestrict PairingGlue
open PairingWeight PairingRecursion
open MeasureTheory ProbabilityTheory GraphLaplacian LatticeIsserlisSmeared WickPairings

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
variable [Fintype κ] [DecidableEq κ] [LinearOrder κ]

/-! ## 1. Relabelling -/

/-- **A PAIRING SUM DOES NOT CARE HOW THE INDICES ARE NAMED.** No order hypothesis on `e`: the
`<`-device is a representative set, and `PairWeightRep.prod_repSet_eq` says the product is the
same at any of them. -/
theorem sum_pm_transport (e : ι ≃ κ) {w : κ → κ → ℝ} (hw : ∀ x y, w x y = w y x) :
    ∑ τ : ↑(perfectMatchings κ), ∏ x ∈ Finset.univ.filter (fun x => x < τ.1 x), w x (τ.1 x)
      = ∑ σ : ↑(perfectMatchings ι), ∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i),
          w (e i) (e (σ.1 i)) := by
  classical
  refine (Fintype.sum_equiv (perfectMatchingsCongr e) _ _ ?_).symm
  intro σ
  have hinv : ((perfectMatchingsCongr e) σ).1 ∈ involutions κ :=
    ((perfectMatchingsCongr e) σ).2.1
  rw [← prod_repSet_permCongr e σ.1 (Finset.univ.filter (fun i => i < σ.1 i)) w,
    ← perfectMatchingsCongr_coe e σ]
  exact (prod_repSet_eq hinv hw (isRepSet_filter_lt hinv)
    (by rw [perfectMatchingsCongr_coe]
        exact isRepSet_permCongr e (isRepSet_filter_lt σ.2.1))).symm

/-! ## 2. The correlation factorises -/

section Field

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-- One side's pairing sum, read as an integral. `sum_pm_transport` renames the subtype's indices
to `Fin` and `IsserlisAll.isserlisGeneral_all` does the rest. -/
theorem sum_pm_eq_integral (hm : m ≠ 0) {k : ℕ} (a : Fin k → EuclideanSpace ℝ V)
    {T : Type*} [Fintype T] [DecidableEq T] [LinearOrder T] (ε : T → Fin k) :
    ∑ τ : ↑(perfectMatchings T),
        ∏ x ∈ Finset.univ.filter (fun x => x < τ.1 x), dotG G m (a (ε x)) (a (ε (τ.1 x)))
      = ∫ ω, (∏ x : T, (inner ℝ (a (ε x)) ω : ℝ)) ∂(gaussianField G m) := by
  classical
  set e : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm with he
  rw [sum_pm_transport e (w := fun x y => dotG G m (a (ε x)) (a (ε y)))
      (fun x y => dotG_comm hm _ _)]
  have hI : ∫ ω, (∏ i : Fin (Fintype.card T), (inner ℝ (a (ε (e i))) ω : ℝ))
        ∂(gaussianField G m)
      = ∑ σ : ↑(perfectMatchings (Fin (Fintype.card T))),
          ∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i),
            dotG G m (a (ε (e i))) (a (ε (e (σ.1 i)))) :=
    IsserlisAll.isserlisGeneral_all (G := G) (m := m) hm (Fintype.card T) (fun i => a (ε (e i)))
  rw [← hI]
  refine congrArg (MeasureTheory.integral (gaussianField G m)) (funext fun ω => ?_)
  exact Fintype.prod_equiv e (fun i => (inner ℝ (a (ε (e i))) ω : ℝ))
    (fun x => (inner ℝ (a (ε x)) ω : ℝ)) fun i => rfl

/-- **THE CORRELATION FACTORISES ACROSS A SPLIT THE PROPAGATOR DOES NOT CROSS.** At every order,
for the correlated Gaussian field on a finite graph: if `⟨aᵢ, G aⱼ⟩ = 0` whenever `i` is in `S`
and `j` is not, then the correlation of all the `aᵢ` is the product of the two groups'
correlations. **Exact, not approximate** — the crossing pairings are deleted rather than
bounded. -/
theorem integral_prod_split (hm : m ≠ 0) {k : ℕ} (a : Fin k → EuclideanSpace ℝ V)
    (S : Finset (Fin k)) (hzero : ∀ i ∈ S, ∀ j ∉ S, dotG G m (a i) (a j) = 0) :
    ∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
      = (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
        * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m)) := by
  classical
  rw [IsserlisAll.isserlisGeneral_all hm k a,
    show (∑ σ : ↑(perfectMatchings (Fin k)), pairProduct G m a σ.1)
      = ∑ σ : ↑(perfectMatchings (Fin k)),
          ∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), dotG G m (a i) (a (σ.1 i)) from rfl,
    PairingWeight.sum_prod_eq_mul (w := fun i j => dotG G m (a i) (a j))
      (fun i j => dotG_comm hm _ _) hzero,
    sum_pm_eq_integral hm a (fun x : {x : Fin k // x ∈ S} => (x : Fin k)),
    sum_pm_eq_integral hm a (fun y : {y : Fin k // y ∉ S} => (y : Fin k))]

/-! ## 3. The check

The four-file route to `integral_prod_split` runs through the pairing split, the bijection, the
weight, the relabelling and general-order Isserlis. `LatticeIsserlisSmeared.smeared_twoPoint`
reaches the two-point function by polarising a second moment and touches none of that. At two test
functions the two must agree, and the theorem below is that agreement. -/

/-- **THE CHECK.** At two test functions split one and one, `integral_prod_split` says the product
of the two sides' correlations is the two-point function — which `smeared_twoPoint` computes by
polarisation. Neither route passes through the other. -/
theorem integral_prod_split_two_agrees (hm : m ≠ 0) (a : Fin 2 → EuclideanSpace ℝ V)
    (hzero : ∀ i ∈ ({0} : Finset (Fin 2)), ∀ j ∉ ({0} : Finset (Fin 2)),
      dotG G m (a i) (a j) = 0) :
    (∫ ω, (∏ x : {x : Fin 2 // x ∈ ({0} : Finset (Fin 2))}, (inner ℝ (a x) ω : ℝ))
        ∂(gaussianField G m))
      * (∫ ω, (∏ y : {y : Fin 2 // y ∉ ({0} : Finset (Fin 2))}, (inner ℝ (a y) ω : ℝ))
        ∂(gaussianField G m))
      = dotG G m (a 0) (a 1) := by
  rw [← integral_prod_split hm a ({0} : Finset (Fin 2)) hzero]
  have hprod : ∀ ω : EuclideanSpace ℝ V,
      (∏ i : Fin 2, (inner ℝ (a i) ω : ℝ)) = (inner ℝ (a 0) ω : ℝ) * (inner ℝ (a 1) ω : ℝ) :=
    fun ω => Fin.prod_univ_two _
  rw [show (fun ω : EuclideanSpace ℝ V => ∏ i : Fin 2, (inner ℝ (a i) ω : ℝ))
      = fun ω => (inner ℝ (a 0) ω : ℝ) * (inner ℝ (a 1) ω : ℝ) from funext hprod]
  exact smeared_twoPoint hm (a 0) (a 1)

end Field

end PairingRelabel
