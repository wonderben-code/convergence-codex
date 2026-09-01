import LovelockSectionalWitness
import LovelockActInverse
import LovelockCurvProjectionAdjoint

/-!
# Bridge 2 closed: orbit-orthogonality *is* sectional vanishing on orthonormal pairs

`WALLS` §W5.0 §5g left the sectional route with two bridges, and
`LovelockSectionalWitness` (`bd67033`) built half of the second — the pairing against the witness's
underlying **square**. Its header named what was still missing: *"replacing `knSquare (twoProj i j)`
by its Weyl part … needs `⟨Y, ricciPart X⟩ = 0` and `⟨Y, scalPart X⟩ = 0` for Ricci-flat `Y` … plus
linearity of `ip` in its second argument. That assembly is not in this file."* **It is in this
one, and bridge 2 is now closed.**

## What is proved

* `ip_ricciPart_eq_zero`, `ip_scalPart_eq_zero` — a Ricci-flat algebraic curvature tensor is
  `ip`-orthogonal to **any** array's Ricci and scalar summands. Both are one rewrite:
  `ricciPart X` is a multiple of `(tracefreeRicci X) ⊙ δ` and dies by
  `LovelockOrthogonality.ip_eq_zero_of_ricci_eq_zero`; `scalPart X` is a multiple of
  `knSquare δ` and dies by `ip_knSquare_delta`, whose value `2·scal Y` vanishes with the trace;
* **`ip_weylPart_right`** — hence `⟨Y, weylPart X⟩ = ⟨Y, X⟩`. **One restrictive hypothesis
  removed from the estate's orthogonality results:** `LovelockOrthogonality`'s three theorems pair
  the summands *of the same tensor*, and this pairs a Ricci-flat tensor against the Weyl summand of
  **any other**;
* **`ip_weyl_witness`** — `⟨Y, weylPart (knSquare (twoProj i j))⟩ = 4·Y i j j i`. The witness's Weyl
  part reads off exactly one sectional entry;
* **`ip_act_weyl_witness`** — and after a frame change,
  `⟨Z, act Q W⟩ = 4·sec Z (row i of Qᵀ) (row j of Qᵀ)`, by `ip_act_transp` and
  `LovelockSectionalWitness.sec_rows`. **That is bridge 2: orthogonality to the witness's orbit and
  vanishing of sectional entries on orthonormal pairs are the same condition, not two conditions
  that resemble each other**;
* `transp_transp` — `rfl`, and needed only to state the next item without a spurious transpose;
* **`eq_zero_of_ip_orbit`** — **the route assembled, with its one remaining gap written as an
  explicit hypothesis** rather than as prose. Given `hext` — that sectional vanishing on all pairs
  of rows of orthogonal matrices implies sectional vanishing on all pairs — a Ricci-flat algebraic
  curvature tensor orthogonal to the whole orbit of the witness is **zero**.

## What `hext` is, and why it is a hypothesis and not a theorem

`hext` is bridge 1 of §5g, and **it is the only thing left on this route.** The mathematics is one
line: for a dependent pair the sectional entry vanishes by antisymmetry, and an independent pair
normalises to an orthonormal one, on which the entry scales by a positive factor. **The Lean form
needs *extend an orthonormal pair to an orthogonal matrix***, and this estate has no bridge to
Mathlib's `OrthonormalBasis` machinery. Stating it as a hypothesis is `LovelockReduction`'s own
device — `classification_of_killsWeyl_of_ricciProportional` does the same with its two open `Prop`s
— and it is preferred here to a `sorry`, which would put an unproved statement in the estate for
something nobody is currently attempting.

**`KillsWeyl` at `n ≥ 4` does not follow from this file.** `eq_zero_of_ip_orbit` is conditional, and
its hypothesis is unproved. **The watchlist item does not move.** What has changed is that §5g's two
bridges are now one, and that one is a named hypothesis of a named theorem rather than a paragraph.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.


## ⚠ THE `OrthonormalBasis` BRIDGE NAMED BELOW WAS BUILT FIFTY-EIGHT MINUTES LATER

Annotated 1 September 2026, kept as written (`ERRATUM 94`, `ERRATUM 391`). This file was committed
at **2026-08-15 23:30**. `LovelockOrthonormalFrame` was committed at **2026-08-16 00:28** —
fifty-eight minutes — and `exists_isOrth_rows` extends an orthonormal pair to an orthogonal matrix
through Mathlib's `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`, which is the bridge
named here as missing.

**`LovelockSectional` already records this**, in a dated `⚠ SUPERSEDED` note of 2026-08-27 found by
`ERRATUM 313` — *"the 'Mathlib bridge this estate has not built' IS built"*. That note was added to
one file carrying the claim and not to this one, which is `ERRATUM 390`'s one-in-four pattern again.

**`hext` as a hypothesis is not withdrawn and the reasoning for it stands**: stating an open step as
a hypothesis rather than a `sorry` is `LovelockReduction`'s device and is right. What changed is
that the step is no longer open.
-/

namespace LovelockWitnessPairing

open AlgebraicCurvature LovelockProjections LovelockOrthogonality LovelockEquivariance
  LovelockCurvProjectionAdjoint LovelockActInverse LovelockFrameInverse WeylNonzeroGeneral
  LovelockSectional LovelockSectionalWitness Finset

variable {n : ℕ} {Q : Fin n → Fin n → ℝ}

/-- A Ricci-flat algebraic curvature tensor is orthogonal to **any** array's Ricci summand, which
is a multiple of `(tracefreeRicci X) ⊙ δ`. -/
theorem ip_ricciPart_eq_zero {Y : Fin n → Fin n → Fin n → Fin n → ℝ} (hY : IsAlgCurv Y)
    (h0 : ∀ b c, ricci Y b c = 0) (X : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip Y (ricciPart X) = 0 := by
  have hfun : ricciPart X
      = fun a b c d => (1 / ((n : ℝ) - 2)) * kn (tracefreeRicci X) delta a b c d := rfl
  rw [hfun, ip_smul_right, ip_eq_zero_of_ricci_eq_zero hY h0, mul_zero]

/-- And to its scalar summand, whose pairing is `2·scal Y` and so vanishes with the trace. -/
theorem ip_scalPart_eq_zero {Y : Fin n → Fin n → Fin n → Fin n → ℝ} (hY : IsAlgCurv Y)
    (h0 : ∀ b c, ricci Y b c = 0) (X : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip Y (scalPart X) = 0 := by
  have hfun : scalPart X
      = fun a b c d => (scal X / ((n : ℝ) * ((n : ℝ) - 1)))
          * knSquare (delta : Fin n → Fin n → ℝ) a b c d := rfl
  have hs : scal Y = 0 := by
    simp only [scal]
    exact Finset.sum_eq_zero fun b _ => h0 b b
  rw [hfun, ip_smul_right, ip_knSquare_delta hY, hs, mul_zero, mul_zero]

/-- **A RICCI-FLAT TENSOR DOES NOT SEE THE OTHER TWO SUMMANDS.** -/
theorem ip_weylPart_right {Y : Fin n → Fin n → Fin n → Fin n → ℝ} (hY : IsAlgCurv Y)
    (h0 : ∀ b c, ricci Y b c = 0) (X : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip Y (weylPart X) = ip Y X := by
  have hfun : weylPart X
      = fun a b c d => (X a b c d - ricciPart X a b c d) - scalPart X a b c d := rfl
  rw [hfun, ip_sub_right, ip_sub_right, ip_ricciPart_eq_zero hY h0,
    ip_scalPart_eq_zero hY h0, sub_zero, sub_zero]

/-- **AND SO THE WITNESS'S WEYL PART READS OFF ONE SECTIONAL ENTRY**, not merely its underlying
square. -/
theorem ip_weyl_witness {Y : Fin n → Fin n → Fin n → Fin n → ℝ} (hY : IsAlgCurv Y)
    (h0 : ∀ b c, ricci Y b c = 0) (i j : Fin n) :
    ip Y (weylPart (knSquare (twoProj i j))) = 4 * Y i j j i := by
  rw [ip_weylPart_right hY h0, ip_knSquare_twoProj hY]

/-- **BRIDGE 2, CLOSED.** -/
theorem ip_act_weyl_witness (hQ : IsOrth Q) {Z : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hZ : IsAlgCurv Z) (h0 : ∀ b c, ricci Z b c = 0) (i j : Fin n) :
    ip Z (act Q (weylPart (knSquare (twoProj i j))))
      = 4 * sec Z (fun t => transp Q i t) (fun t => transp Q j t) := by
  have hT : IsOrth (transp Q) := isOrth_transp hQ
  have hZ' : IsAlgCurv (act (transp Q) Z) := isAlgCurv_act _ hZ
  have h0' : ∀ b c, ricci (act (transp Q) Z) b c = 0 := by
    intro b c
    rw [ricci_act hT]
    simp only [act2]
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
    rw [h0 p q, mul_zero]
  rw [ip_comm Z (act Q (weylPart (knSquare (twoProj i j)))), ip_act_transp hQ,
    ip_comm (weylPart (knSquare (twoProj i j))) (act (transp Q) Z),
    ip_weyl_witness hZ' h0']
  rfl

/-- `rfl`; needed only so the next statement carries no spurious transpose. -/
theorem transp_transp (Q : Fin n → Fin n → ℝ) (a b : Fin n) : transp (transp Q) a b = Q a b := rfl

/-- **THE ROUTE ASSEMBLED, WITH ITS ONE REMAINING GAP AS AN EXPLICIT HYPOTHESIS.** -/
theorem eq_zero_of_ip_orbit
    (hext : ∀ W : Fin n → Fin n → Fin n → Fin n → ℝ, IsAlgCurv W →
      (∀ P : Fin n → Fin n → ℝ, IsOrth P → ∀ i j,
        sec W (fun t => P i t) (fun t => P j t) = 0) →
      ∀ x y, sec W x y = 0)
    {Z : Fin n → Fin n → Fin n → Fin n → ℝ} (hZ : IsAlgCurv Z) (h0 : ∀ b c, ricci Z b c = 0)
    (horth : ∀ P : Fin n → Fin n → ℝ, IsOrth P → ∀ i j,
      ip Z (act P (weylPart (knSquare (twoProj i j)))) = 0)
    (a b c d : Fin n) : Z a b c d = 0 := by
  refine eq_zero_of_sec hZ (hext Z hZ ?_) a b c d
  intro P hP i j
  have hkey := ip_act_weyl_witness (isOrth_transp hP) hZ h0 i j
  rw [horth (transp P) (isOrth_transp hP) i j] at hkey
  have hfun : (fun t => transp (transp P) i t) = fun t => P i t := by
    funext t; exact transp_transp P i t
  have hfun2 : (fun t => transp (transp P) j t) = fun t => P j t := by
    funext t; exact transp_transp P j t
  rw [hfun, hfun2] at hkey
  linarith

end LovelockWitnessPairing
