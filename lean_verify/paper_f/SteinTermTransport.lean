import SteinSumRecursion
import PairingRecursion

/-!
# Relabelling a rung's term

`SteinSumRecursion.sum_steinTerm_option` is the rung term's recursion at index type `Option α`;
`LatticeSteinLadder.steinSum` lives at `Fin n`, because that is where
`WickPairings.IsserlisGeneral` lives. Closing the ladder's induction step means carrying the first
to the second, and `PairingRecursion` already did the analogous carry for `perfectMatchings`.

**The new work is the fixed points.** `PairingRecursion` transported a product over one
representative per pair; a rung's term carries a **second** product, over the indices the
involution leaves alone, and that set has to move too. `fixedPoints_permCongr` is the statement
that it does, and everything else here is that plus `PairingRecursion.prod_repSet_permCongr`.

## What is proved

* `fixedPoints_permCongr` — relabelling an involution relabels its fixed points;
* **`steinTerm_permCongr`** — hence the whole term transports, both products at once;
* `card_fixedPoints_permCongr` — **the check**, and a note on why it is this one.

**THE OBVIOUS CHECK IS VACUOUS HERE, AND WAS WRITTEN AND DELETED RATHER THAN KEPT WITH A CAVEAT.**
Every other transport in this campaign is checked by specialising its weights to `1` and
recovering a counting theorem. Do that to `steinTerm_permCongr` and both sides become a product of
ones: the statement degenerates to `1 = 1` and **says nothing about the transport at all** — it
does not even mention it. So the check here is `card_fixedPoints_permCongr`, which counts the
fixed points on either side of `fixedPoints_permCongr` and can only agree because the two sets
correspond point by point. A relabelling that lost or gained a fixed point would change that
number.

**WHAT IS NOT HERE.** The assembly. Turning `sum_steinTerm_option` into a statement about
`involutions (Fin (n+1))` also needs `Involutions.involutionsCongr` summed over, the two branches
matched against `LatticeSteinLadder.hasDerivAt_steinClosed` and
`InvolutionFixedSum.sum_fixedPoints_comm`, and `finSuccEquiv`'s two values substituted. **None of
that is done here**, no rung above the third is built, and general-order Isserlis follows from
none of it. **Not costed** (`ERRATUM 194`).
-/

namespace SteinTermTransport

open Equiv Function Involutions PairWeightRep SteinSumRecursion PairingRecursion

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {M : Type*} [CommMonoid M]

/-- **RELABELLING AN INVOLUTION RELABELS ITS FIXED POINTS.** `e.permCongr σ` fixes `e i` exactly
when `σ` fixes `i`, so the fixed-point set moves by `Finset.image e`. -/
theorem fixedPoints_permCongr (e : ι ≃ κ) (σ : Equiv.Perm ι) :
    (Finset.univ.filter (fun x : κ => (e.permCongr σ) x = x))
      = (Finset.univ.filter (fun i : ι => σ i = i)).image e := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Equiv.permCongr_apply]
  constructor
  · intro h
    refine ⟨e.symm x, ?_, by simp⟩
    exact e.injective (by simpa using h)
  · rintro ⟨i, hi, rfl⟩
    simp [hi]

/-- **AND THE WHOLE TERM TRANSPORTS**, both products at once: the pair product by
`PairingRecursion.prod_repSet_permCongr`, the fixed-point product by the lemma above. -/
theorem steinTerm_permCongr (e : ι ≃ κ) (σ : Equiv.Perm ι) (S : Finset ι)
    (W : κ → κ → M) (U : κ → M) :
    steinTerm W U (S.image e) (e.permCongr σ)
      = steinTerm (fun i j => W (e i) (e j)) (fun i => U (e i)) S σ := by
  rw [steinTerm, steinTerm, prod_repSet_permCongr e σ S W, fixedPoints_permCongr e σ,
    Finset.prod_image (fun x _ y _ h => e.injective h)]

/-! ## The check

Specialising `steinTerm_permCongr` to the weights `1` makes both sides a product of ones and the
statement `1 = 1`, which says nothing about the transport. That version was written and deleted.
What is here instead counts. -/

/-- **THE CHECK.** Counting the fixed points on either side of
`fixedPoints_permCongr` must agree, and it can only agree because the sets correspond point by
point — a relabelling that lost or gained a fixed point would change the count. -/
theorem card_fixedPoints_permCongr (e : ι ≃ κ) (σ : Equiv.Perm ι) :
    (Finset.univ.filter (fun x : κ => (e.permCongr σ) x = x)).card
      = (Finset.univ.filter (fun i : ι => σ i = i)).card := by
  rw [fixedPoints_permCongr e σ, Finset.card_image_of_injective _ e.injective]

end SteinTermTransport
