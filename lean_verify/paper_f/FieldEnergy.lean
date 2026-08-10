import PeierlsConditional
import IsingBoundaryField

/-!
# The Peierls energy estimate survives the boundary field, with the same constant

`UNLOCK_WATCHLIST`'s **field-model Peierls route** lists five steps and flags **S4** — does
`ContourSubtract`'s surgery still bound the weight once the Hamiltonian carries a boundary
field? — as the one nobody had checked, and guesses that "the sign is favourable". **This
file settles it, and the guess was too weak: the field term is not favourable, it is
invariant.**

## Why

The surgery is exclusive-or with a **`+`-cut**: a configuration `τ` realising the bond set,
which by definition is `false` at every boundary site. Exclusive-or with `false` is the
identity, so `σ` and `σ xor τ` **agree on the whole boundary** — and `boundaryTerm`, the only
thing the field sees, reads nothing else. The field contribution is therefore literally the
same before and after, and it cancels:

`exp (-β H_h σ) = exp (-4β |γ|) · exp (-β H_h (σ xor τ))`,

the identical relation `PeierlsConditional.gibbs_plus_bound_of_cut` uses for the field-free
Hamiltonian, with `H_h` in place of `H` and **no loss anywhere**.

> **`gibbs_field_bound_of_cut`** — for a `+`-cut `γ`, the boundary-field weight of the
> configurations whose contour contains `γ` is at most `exp (-4β|γ|)` times the **total**
> partition sum, at every field strength `h`.

## Two things this is, and two it is not

* It **is** stated over **all** configurations. The `+`-boundary filter that
  `gibbs_plus_bound_of_cut` carries on both sides was needed only to keep the image of the
  surgery inside the `+` class; with no class to stay inside, it is not needed at all, so the
  field version is **simpler** than the conditioned one rather than harder.
* It **is** S4 of the mapped route, and it moves that step from "unchecked, sign favourable"
  to "proved, no loss".
* It is **not** a Peierls estimate for the field model. The entropy side — which contours can
  occur, and how many — is untouched, and with a free boundary the contour of a down site need
  not close at all. That is S1, S3a and S3b of the map, none of which is begun.
* It is **not** progress on `IsingBoundaryField.MagnetisationBound`, which stays untouched
  and stays false at `h = 0` for positive `m` (`BoundaryFieldRatio`).
-/

namespace FieldEnergy

open IsingFiniteVolume IsingContourEnergy IsingBoundaryField DualObstruction
open PlusCondition PeierlsConditional

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The field term does not see the surgery -/

/-- **Exclusive-or with a boundary-`false` configuration leaves the boundary alone**, hence
leaves `boundaryTerm` — the only functional of `σ` the field reads — exactly where it was. -/
theorem boundaryTerm_xorC {τ : Config n} (hbdy : ∀ p : Site n, isBoundary p = true → τ p = false)
    (σ : Config n) : boundaryTerm n (xorC σ τ) = boundaryTerm n σ := by
  rw [boundaryTerm, boundaryTerm]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : isBoundary p
  · simp only [hp, if_true, xorC, hbdy p hp, Bool.xor_false]
  · simp [hp]

/-- The Gibbs weight factors into the field-free weight and a boundary factor. -/
theorem exp_isingHB_split (h β : ℝ) (σ : Config n) :
    Real.exp (-β * isingHB n h σ)
      = Real.exp (-β * isingH n σ) * Real.exp (β * h * boundaryTerm n σ) := by
  rw [← Real.exp_add, isingHB]
  congr 1
  ring

/-! ## 2. So the surgery costs exactly what it costs without the field -/

/-- **The exchange relation, with the field.** Removing a `+`-cut `γ` from a configuration's
contour divides its boundary-field weight by `exp (-4β|γ|)`, exactly as it does without the
field, because the boundary factor is common to both sides. -/
theorem exp_isingHB_xorC {γ : Finset (Sym2 (Site n))} {τ : Config n} (hcon : contour τ = γ)
    (hbdy : ∀ p : Site n, isBoundary p = true → τ p = false) (h β : ℝ) {σ : Config n}
    (hsub : γ ⊆ contour σ) :
    Real.exp (-β * isingHB n h σ)
      = Real.exp (-(4 * β) * (γ.card : ℝ)) * Real.exp (-β * isingHB n h (xorC σ τ)) := by
  classical
  have hsub' : contour τ ⊆ contour σ := hcon ▸ hsub
  have hcard : ((contour (xorC σ τ)).card : ℝ) = ((contour σ).card : ℝ) - (γ.card : ℝ) := by
    rw [contour_xor_of_subset hsub', Finset.card_sdiff, Finset.inter_eq_left.mpr hsub',
      hcon, Nat.cast_sub (Finset.card_le_card hsub)]
  have hfree : Real.exp (-β * isingH n σ)
      = Real.exp (-(4 * β) * (γ.card : ℝ)) * Real.exp (-β * isingH n (xorC σ τ)) := by
    rw [IsingContourGibbs.peierls_weight n β σ,
      IsingContourGibbs.peierls_weight n β (xorC σ τ), hcard]
    simp only [← Real.exp_add]
    congr 1
    ring
  rw [exp_isingHB_split, exp_isingHB_split, boundaryTerm_xorC hbdy, hfree]
  ring

/-! ## 3. The energy estimate for the boundary-field model -/

/-- **THE PEIERLS ENERGY ESTIMATE, WITH A BOUNDARY FIELD.** For a `+`-cut `γ`, the
boundary-field weight of the configurations whose contour contains `γ` is at most
`exp (-4β|γ|)` times the whole partition sum — at **every** field strength, with the same
constant as the field-free estimate and no loss.

Compare `PeierlsConditional.gibbs_plus_bound_of_cut`, which carries a `+`-boundary filter on
both sides. That filter was there to keep the surgery inside the `+` class; here there is no
class to stay inside, and the statement is over **all** configurations. -/
theorem gibbs_field_bound_of_cut {γ : Finset (Sym2 (Site n))} (hγ : IsPlusCut γ) (h β : ℝ) :
    ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => γ ⊆ contour σ),
        Real.exp (-β * isingHB n h σ)
      ≤ Real.exp (-(4 * β) * (γ.card : ℝ)) *
        ∑ σ : Config n, Real.exp (-β * isingHB n h σ) := by
  classical
  obtain ⟨τ, hcon, hbdy⟩ := hγ
  set A := (Finset.univ : Finset (Config n)).filter (fun σ => γ ⊆ contour σ) with hA
  have hfac : ∀ σ ∈ A, Real.exp (-β * isingHB n h σ) =
      Real.exp (-(4 * β) * (γ.card : ℝ)) * Real.exp (-β * isingHB n h (xorC σ τ)) := by
    intro σ hσ
    exact exp_isingHB_xorC hcon hbdy h β (Finset.mem_filter.mp hσ).2
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
  have hinj : ∀ a ∈ A, ∀ b ∈ A, xorC a τ = xorC b τ → a = b := fun a _ b _ hEq => by
    have := congrArg (fun c => xorC c τ) hEq
    simpa [xorC_involutive τ a, xorC_involutive τ b] using this
  rw [← Finset.sum_image (f := fun c : Config n => Real.exp (-β * isingHB n h c)) hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun _ _ _ => Real.exp_nonneg _

/-- The boundary-field partition sum is positive: a finite sum of exponentials over a
nonempty type. -/
theorem partition_pos (n : ℕ) (h β : ℝ) : 0 < ∑ σ : Config n, Real.exp (-β * isingHB n h σ) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨fun _ => true, Finset.mem_univ _⟩

/-- The same as a probability against the boundary-field Gibbs measure's weight ratio. -/
theorem prob_field_bound_of_cut {γ : Finset (Sym2 (Site n))} (hγ : IsPlusCut γ) (h β : ℝ) :
    (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => γ ⊆ contour σ),
        Real.exp (-β * isingHB n h σ)) /
      (∑ σ : Config n, Real.exp (-β * isingHB n h σ))
      ≤ Real.exp (-(4 * β) * (γ.card : ℝ)) := by
  rw [div_le_iff₀ (partition_pos n h β)]
  exact gibbs_field_bound_of_cut hγ h β

end FieldEnergy
