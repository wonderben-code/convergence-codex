/-
  IsingNaiveBound.lean — why the obvious route to Peierls fails, proved
  rather than asserted.

  WHY. Seven files now prove that flipping spins costs `4` per unit of
  contour and that the Peierls sum can be reindexed onto contours. A reader
  is entitled to ask why that does not already give the magnetisation bound,
  and **the answer is a theorem the estate did not have.**

  The obvious route is a union bound: every non-constant configuration is
  suppressed relative to the ground state by at least `e^{-4β}`, and there
  are fewer than `2^(n²)` of them, so the total non-ground mass is at most
  `2^(n²)·e^{-4β}`. **That bound is worthless**, because at any fixed `β`
  the prefactor beats the suppression once the box is large enough. Peierls
  escapes by never using it: it groups configurations by contour LENGTH and
  races `3^L` against `e^{-4βL}`, so the exponent grows with the same
  parameter as the count.

  WHAT THIS FILE PROVES:
  1. **`contour_card_pos`** — a non-constant configuration has at least one
     broken bond.
  2. **`gibbs_le_of_not_const`** — hence
     `gibbs{σ} ≤ e^{-4β}·gibbs{allTrue}` for every non-constant `σ`. The
     single-configuration Peierls estimate: exact, with no limits in it, and
     the sharpest thing the energy identity gives on its own.
  3. **`naive_union_bound_fails`** — and the union bound built from it is
     vacuous in the volume: at any fixed `β` and any target `C`, some box
     size makes the prefactor exceed `C`.

  WHAT THIS DOES NOT DO. **It proves a route dead, not a theorem alive.** A
  negative result about one's own easiest approach is worth writing down and
  is not progress toward the wall. No `3^{|γ|}`, no circuits, no
  "surrounds", and `IsingBoundaryField.MagnetisationBound` is untouched.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import IsingContourGibbs

namespace IsingNaiveBound

open IsingFiniteVolume IsingContourEnergy IsingContourSeparation IsingContourGibbs
open MeasureTheory

variable {n : ℕ}

/-! ## 1. A non-constant configuration breaks a bond -/

theorem contour_card_pos (hn : 0 < n) {σ : Config n}
    (h1 : σ ≠ fun _ => true) (h2 : σ ≠ fun _ => false) :
    0 < (contour σ).card := by
  rcases Nat.eq_zero_or_pos (contour σ).card with h0 | hpos
  · exact absurd ((contour_eq_empty_iff hn σ).mp (Finset.card_eq_zero.mp h0))
      (by rw [const_iff_eq hn]; tauto)
  · exact hpos

/-! ## 2. The single-configuration Peierls estimate -/

/-- **`gibbs{σ} ≤ e^{-4β}·gibbs{allTrue}`** for every non-constant `σ`.
    Exact, with no limits in it, and the sharpest bound the energy identity
    gives on a single configuration. -/
theorem gibbs_le_of_not_const (hn : 0 < n) {β : ℝ} (hβ : 0 ≤ β) {σ : Config n}
    (h1 : σ ≠ fun _ => true) (h2 : σ ≠ fun _ => false) :
    FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n)) {σ}
      ≤ ENNReal.ofReal (Real.exp (-(4 * β)))
        * FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n))
            {(fun _ => true)} := by
  have hc : (1:ℝ) ≤ ((contour σ).card : ℝ) := by
    exact_mod_cast contour_card_pos hn h1 h2
  have hstep : ENNReal.ofReal (Real.exp (-(4 * β) * ((contour σ).card : ℝ)))
      ≤ ENNReal.ofReal (Real.exp (-(4 * β))) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))
  rw [gibbs_singleton_contour n β σ]
  exact mul_le_mul_left hstep _

/-! ## 3. The union bound is vacuous in the volume

`card_config = 2^(n²)` configurations, each suppressed by at most
`e^{-4β}`. The product is the only bound available without geometry, and
this section says it is worthless.
-/

/-- **THE NAIVE UNION BOUND FAILS.** At any fixed `β` and any target `C`,
    some box size makes the prefactor `2^(n²)·e^{-4β}` exceed `C`. So the
    only bound the energy identity supplies on its own is vacuous exactly in
    the limit the physics is about.

    This is why Peierls counts contours rather than configurations: grouping
    by contour LENGTH puts the same parameter in the exponent on both sides,
    `3^L` against `e^{-4βL}`, and that race can be won. -/
theorem naive_union_bound_fails (β : ℝ) (C : ℝ) :
    ∃ N : ℕ, 0 < N ∧ C < (2 : ℝ) ^ (N * N) * Real.exp (-(4 * β)) := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (max C 0 / Real.exp (-(4 * β))) one_lt_two
  refine ⟨k + 1, Nat.succ_pos k, ?_⟩
  have hpos : 0 < Real.exp (-(4 * β)) := Real.exp_pos _
  have hle : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ ((k + 1) * (k + 1)) := by
    refine pow_le_pow_right₀ (by norm_num) ?_
    nlinarith
  have hC : C ≤ max C 0 := le_max_left _ _
  have hdiv : max C 0 / Real.exp (-(4 * β)) < (2 : ℝ) ^ k := hk
  have : max C 0 < (2 : ℝ) ^ k * Real.exp (-(4 * β)) := by
    rw [div_lt_iff₀ hpos] at hdiv
    exact hdiv
  calc C ≤ max C 0 := hC
    _ < (2 : ℝ) ^ k * Real.exp (-(4 * β)) := this
    _ ≤ (2 : ℝ) ^ ((k + 1) * (k + 1)) * Real.exp (-(4 * β)) := by
        exact mul_le_mul_of_nonneg_right hle (le_of_lt hpos)

/-! ## 4. Review round 74 — the ways this could be hollow

**"A negative result could be padding."** It could, so here is the test it
has to pass: does anything change if it is deleted? Yes — without it, the
seven contour files end with a reindexing and an energy identity and no
statement of why they do not conclude. §3 is the sentence "and this is why
the entropy half is necessary" turned into a theorem. `WALLS.md` has been
asserting the `3^{|γ|}` count is needed; this is the first thing in the
estate that shows the cheap alternative is dead rather than merely
untried.

**"§2 could be weaker than advertised."** It is, and the draft of this
paragraph got the reason wrong in the direction that flatters the file. It
said `|γ| = 1` "really does exist on a large enough box". **That is
unproved and is probably false**: `IsingContourPlaquette.even_plaquette`
says every unit square carries an even number of broken bonds, so a lone
broken bond sitting inside a square would make that square's count odd. The
bound is `e^{-4β}` because `contour_card_pos` supplies only `|γ| ≥ 1`, and
the true minimum is very likely `2` — a corner site has degree two, and
flipping it breaks exactly those two bonds.

**Why that is not fixed here.** Turning "probably 2" into a theorem needs
"every bond lies in some unit square", which is four cases of `Fin`
arithmetic against the box boundary, and it would improve §2 from `e^{-4β}`
to `e^{-8β}` while changing nothing whatever in §3 — the union bound fails
for either constant. It is recorded in `UNLOCK_WATCHLIST.md` as a named open
question rather than done cheaply here or, worse, asserted. Sharpening
beyond a constant is the "surrounds a site" notion the estate does not
have.

**"§3 could be a statement about nothing."** It quantifies over `β` first
and then produces `N`, which is the correct order: it says the bound fails
at EVERY fixed temperature, not merely at some. Reversing the quantifiers
would give a true but empty statement, since for fixed `N` a large enough
`β` does make the prefactor small — that is the finite-volume
low-temperature regime, and it is exactly the regime that is not a phase
transition.

**"This could be read as progress."** It is the opposite and the header
says so. Closing off one's own easiest route is worth recording because it
converts "we should do the hard count" from a plan into a necessity, but
`MagnetisationBound` is untouched and no part of the entropy half is
nearer.
-/

end IsingNaiveBound
