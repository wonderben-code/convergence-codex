import LatticeSteinLadder
import SteinTermTransport

/-!
# The rung's closed form, one order up

`SteinSumRecursion.sum_steinTerm_option` is the rung term's recursion at index type `Option α`.
`LatticeSteinLadder.steinSum` lives at `Fin n`, because `WickPairings.IsserlisGeneral` does.
`SteinTermTransport` moved the *term* across a relabelling, fixed points and all. **This moves the
recursion**, and what comes out is a statement about `steinSum` itself:

```
steinSum a' f = ⟨f, G a'₀⟩ · steinSum (tail a') f
                 + ∑_b ⟨a'₀, G a'_{b+1}⟩ · (the pairings of the rest that use up b).
```

The first term is the branch where the new index is left alone; the second is the branch where it
is paired with `b`, **and `b` is then used up** — which is why the surviving product runs over
`fix g` without `b`. That clause is `SteinSumRecursion.steinTerm_opt`'s and it survives the
transport unchanged.

## Why this is the shape the ladder wants

`LatticeSteinLadder.hasDerivAt_steinClosed` differentiates the closed side and produces exactly two
pieces: `steinSum a f · ⟨f, Gc⟩`, and a double sum over involutions and their fixed points.
`InvolutionFixedSum.sum_fixedPoints_comm` reads that double sum from the other end, as a sum over
`b` of the involutions fixing `b`. **The two pieces are then the two terms above**, and the
induction step closes. That last identification is **not made here** — see below.

## What is proved

* **`steinSum_succ`** — the recursion for `steinSum`, at every order;
* `steinSum_succ_one` — **the check**: at one test function the recursion's right-hand side
  collapses to `⟨f, Ga⟩`, and `LatticeSteinLadder.steinSum_one` reaches the same value by
  enumerating the one involution of `Fin 1` directly. Neither route passes through the other.

## What is NOT proved

The induction itself. Closing it needs `steinSum_succ` matched against
`hasDerivAt_steinClosed` through `sum_fixedPoints_comm`, then `LatticeSteinRung.hasDerivAt_rung_ray`
for the integral side, then `HasDerivAt.unique`. **None of that is here**, no rung above the third
is built, and general-order Isserlis follows from none of it. **Not costed** (`ERRATUM 194`).

**⚠ SUPERSEDED 2026-08-27 — the same day — and kept as written (`ERRATUM 94`).** Every step named
above was taken in `LadderStep`: `steinSum_succ` matched against `hasDerivAt_steinClosed` through
`sum_fixedPoints_comm` (`LadderStep.steinClosed_deriv_eq`), then
`LatticeSteinRung.hasDerivAt_rung_ray`, then `HasDerivAt.unique` (`LadderStep.ladder_succ`), then
the induction (`LadderStep.ladder`). *"No rung above the third is built"* is therefore false, and
general-order Isserlis is `IsserlisAll.isserlisGeneral_all`. *"None of that is here"* is scoped to
this file and stays true (`ERRATUM 302`).
-/

namespace SteinSumSucc

open Equiv Function Involutions PairWeightRep SteinSumRecursion PairingRecursion
open SteinTermTransport LatticeSteinLadder
open LatticeIsserlisSmeared

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-- **THE CLOSED FORM'S RECURSION, AT `Fin (n+1)`.** The new index `0` is either left alone —
contributing `⟨f, G a'₀⟩` and leaving the rest untouched — or paired with some `b`, contributing
`⟨a'₀, G a'_{b+1}⟩` and **using `b` up**, so that `b` no longer contributes a fixed-point factor. -/
theorem steinSum_succ (hm : m ≠ 0) {n : ℕ} (a' : Fin (n + 1) → EuclideanSpace ℝ V)
    (f : EuclideanSpace ℝ V) :
    steinSum G m a' f
      = dotG G m f (a' 0) * steinSum G m (Fin.tail a') f
        + ∑ b : Fin n, dotG G m (a' 0) (a' b.succ)
            * ∑ g : {g : Equiv.Perm (Fin n) // g ∈ involutions (Fin n) ∧ g b = b},
                (∏ i ∈ Finset.univ.filter (fun i => i < g.1 i),
                    dotG G m (a' i.succ) (a' (g.1 i).succ))
                  * ∏ i ∈ Finset.univ.filter (fun i => g.1 i = i ∧ i ≠ b),
                      dotG G m f (a' i.succ) := by
  classical
  set e : Fin (n + 1) ≃ Option (Fin n) := finSuccEquiv n with he
  set W : Option (Fin n) → Option (Fin n) → ℝ :=
    fun x y => dotG G m (a' (e.symm x)) (a' (e.symm y)) with hW
  set U : Option (Fin n) → ℝ := fun x => dotG G m f (a' (e.symm x)) with hU
  have hWsymm : ∀ x y, W x y = W y x := fun x y => dotG_comm hm _ _
  set rep : Equiv.Perm (Option (Fin n)) → Finset (Option (Fin n)) :=
    fun τ => (Finset.univ.filter
      (fun i : Fin (n + 1) => i < (e.symm.permCongr τ) i)).image e with hrepdef
  have hrep : ∀ τ ∈ involutions (Option (Fin n)), IsRepSet τ (rep τ) := by
    intro τ hτ
    have hinv : (e.symm.permCongr τ) ∈ involutions (Fin (n + 1)) :=
      (involutionsCongr e.symm ⟨τ, hτ⟩).2
    have h := isRepSet_permCongr e (isRepSet_filter_lt hinv)
    rw [permCongr_symm_permCongr] at h
    simpa [hrepdef] using h
  have hrepα : ∀ g ∈ involutions (Fin n),
      IsRepSet g (Finset.univ.filter (fun i => i < g i)) := fun g hg => isRepSet_filter_lt hg
  -- the left side, relabelled
  have hleft : steinSum G m a' f
      = ∑ τ : ↑(involutions (Option (Fin n))), steinTerm W U (rep τ.1) τ.1 := by
    refine Fintype.sum_equiv (involutionsCongr e) _ _ fun σ => ?_
    have hback : e.symm.permCongr ((involutionsCongr e) σ).1 = σ.1 := by
      ext x; simp [involutionsCongr, Equiv.permCongr_apply]
    have hcoe : ((involutionsCongr e) σ).1 = e.permCongr σ.1 := rfl
    have hset : rep ((involutionsCongr e) σ).1
        = (Finset.univ.filter (fun i : Fin (n + 1) => i < σ.1 i)).image e := by
      rw [hrepdef]; simp only [hback]
    have hWe : (fun i j : Fin (n + 1) => W (e i) (e j)) = pairW G m a' := by
      funext i j; simp [hW, pairW]
    have hUe : (fun i : Fin (n + 1) => U (e i)) = fixW G m a' f := by
      funext i; simp [hU, fixW]
    rw [hset, hcoe, steinTerm_permCongr e σ.1 _ W U, hWe, hUe]
  rw [hleft, sum_steinTerm_option W U hWsymm rep hrep
    (fun g => Finset.univ.filter (fun i => i < g i)) hrepα]
  have h0 : e.symm none = 0 := by simp [he]
  have hs : ∀ i : Fin n, e.symm (some i) = i.succ := by intro i; simp [he]
  simp only [hW, hU, h0, hs]
  have htail : ∑ x : ↑(involutions (Fin n)),
      steinTerm (fun i j => dotG G m (a' i.succ) (a' j.succ))
        (fun i => dotG G m f (a' i.succ)) (Finset.univ.filter (fun i => i < x.1 i)) x.1
      = steinSum G m (Fin.tail a') f := by
    rw [steinSum]
    rfl
  rw [htail]

/-! ## The check

At one test function the recursion has an empty second branch and a `Fin 0` first branch, so its
right-hand side collapses. `LatticeSteinLadder.steinSum_one` computes the same left-hand side by
enumerating the one involution of `Fin 1`. The two routes share no step. -/

/-- **THE CHECK.** `steinSum_succ` at `n = 0` gives `⟨f, Ga⟩`, which is what
`LatticeSteinLadder.steinSum_one` gets by enumeration. Both branches of the recursion are
exercised: the first collapses through `steinSum_zero_eq_one`, the second is an empty sum. -/
theorem steinSum_succ_one (hm : m ≠ 0) (a f : EuclideanSpace ℝ V) :
    steinSum G m ![a] f = dotG G m f a := by
  rw [steinSum_succ hm ![a] f, steinSum_zero_eq_one (G := G) (m := m) (Fin.tail ![a]) f]
  simp

end SteinSumSucc
