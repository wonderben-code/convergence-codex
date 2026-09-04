import TorusEigenspaceLowerBound
import TorusEightNotTight

/-!
# When the torus degeneracy bound is an equality: exactly when the fibre is one orbit

`TorusEigenspaceLowerBound.two_pow_mul_multinomial_le_finrank` bounds the multiplicity of an
eigenvalue of the massive torus Laplacian below by `2 ^ |interiorAxes k| · multinomial`, with no
hypotheses. `UNLOCK_WATCHLIST` opened an item asking **which frequencies make it an equality**, and
argued in prose that the answer is *"exactly when the eigenvalue's fibre is a single orbit"*, from
three results the estate already had. **That sentence is a theorem here.** The hard question the
item names — *which* frequencies those are — is a question about coincidences among sums of
cosines and is **not touched**; what this file does is replace the prose criterion with a proved
one, so the open question is stated against something checkable.

## What is proved

**`nuRFibre`** names the eigenvalue's fibre as a `Finset`, and **`finrank_eq_card_nuRFibre`** says
the multiplicity **is** its size. That bridge — `Nat.card` of a subtype to `Finset.card` of a
filter — was written inline in `TorusHyperoctahedral.orbit_card_le_finrank_eigenspace` and again in
`TorusEightNotTight.nine_le_finrank_eight`, **the same four lines twice**; naming it is
`ERRATUM 348`'s rule (*a correction is only as reachable as the function that holds it*) applied to
a bridge rather than to a correction.

**`card_orbit_eq_finrank_iff`** — `(orbit k).card = dim ↔ orbit k = nuRFibre`. Both directions are
one step, because the orbit is *contained* in the fibre
(`TorusEigenspaceLowerBound.orbit_subset_nuR_fibre`) and a subset of a finite set with the same
cardinality is the whole of it.

**`bound_eq_finrank_iff`** — the same in the published form, with `2 ^ |interiorAxes k| ·
multinomial` on the left, by `TorusOrbitMultinomial.card_orbit`.

**`card_orbit_lt_finrank_iff`** — and the strict form: the bound is **strict** exactly when the
orbit is a **proper** subset of the fibre. Together these say the bound's slack is precisely the
part of the fibre lying outside the orbit, which is what *"the sum has one term"* meant.

## The criterion is not vacuous, and the estate already had the witness

**`card_orbit_le_two_pow_mul_factorial`** — `(orbit k).card ≤ 2 ^ d · d !` at **every** frequency,
by `Finset.card_image_le` alone. **This does not out-reach `TorusOrbitMultinomial.card_orbit`**,
which is unconditional and *exact*, and from which the same bound follows through
`|interiorAxes k| ≤ d` and `multinomial ≤ d !`. What the image route buys is that it needs neither
of those and mentions neither `interiorAxes` nor the multinomial — it is the corollary's whole
ingredient, and the corollary is the only consumer.

**`orbit_ssubset_nuRFibre_eight`** — at `d = 2`, side `24`, the orbit of `(1, 6)` is a **proper**
subset of its fibre. `TorusEightNotTight.nine_le_finrank_eight` proves `9 ≤ dim` there and the
orbit has at most `2 ^ 2 · 2 ! = 8` elements. **So the estate's known non-tightness is now an
orbit statement**, which is the form the open item is phrased in — and it shows the criterion above
is not vacuously true.

## What is NOT here

**The open question is not answered and is not narrowed.** Which frequencies have single-orbit
fibres is a question about vanishing sums of cosines; the watchlist item records that Mathlib has no
classification of vanishing sums of roots of unity (`0` Conway–Jones, `0` Redei–Schoenberg, probed
2026-08-31) and **no cost is offered here either** (`ERRATUM 194`, `ERRATUM 246`).

**No sum over orbits is constructed.** The item's phrasing *"`dim` is the sum of `card_orbit` over
the orbits the fibre contains"* would need the fibre's partition as an indexed family;
`TorusEigenspaceLowerBound.orbit_eq_of_mem` is the ingredient and nothing here assembles it. The
one-term case is exactly what the biconditionals above capture, and that is the case the bound is
about.

> ⚠ **BUILT IN THE NEXT UNIT** (2026-09-04, `ERRATUM 94`; the paragraph is kept because naming the
> gap precisely is what got it built, for the third time today).
> `TorusFibreOrbitPartition.finrank_eq_sum_card_orbit` is the sum, indexed by `orbitsOf` — the
> image of the fibre under `orbit` — and `card_orbitsOf_eq_one_iff` joins it to the criterion
> above, so *"the bound is an equality exactly when the sum has one term"* is now one theorem
> rather than two informal restatements. **`orbit_eq_of_mem` really was the only ingredient**, and
> `mem_orbit_self`, which the estate had not named, was the other line.

**Nothing is claimed about `d = 1`.** `TorusGenericFrequency` settles attainment there and this file
does not revisit it.

**No wall moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusBoundTightIff

open Matrix GraphLaplacian SimpleGraph Finset BoxGraph TorusReflection
open MassiveTorusSpectrum TorusRealMultiplicity TorusHyperoctahedral TorusReflectionCount
open TorusOrbitMultinomial TorusEigenspaceLowerBound

variable {d : ℕ}

/-! ## 1. The fibre, and the multiplicity as its size -/

/-- **THE FIBRE OF THE EIGENVALUE AT `k`**, as a `Finset`: every frequency carrying `k`'s
eigenvalue. -/
noncomputable def nuRFibre (N : ℕ) (m : ℝ) (k : Site d (N + 3)) : Finset (Site d (N + 3)) :=
  Finset.univ.filter fun k' : Site d (N + 3) => nuR N m k' = nuR N m k

/-- **THE MULTIPLICITY IS THE SIZE OF THE FIBRE.** `TorusRealMultiplicity`'s statement counts a
subtype with `Nat.card`; this is the same fact as a `Finset.card`, which is the form every counting
argument in this chain actually uses. Written inline twice before this file. -/
theorem finrank_eq_card_nuRFibre (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (massive (torusGraph d (N + 3)) m) - (nuR N m k) • LinearMap.id))
      = (nuRFibre N m k).card := by
  classical
  rw [finrank_eigenspace_massive_real N m (nuR N m k), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  rfl

/-- The orbit sits inside the fibre — `orbit_subset_nuR_fibre`, in this file's vocabulary. -/
theorem orbit_subset_nuRFibre (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    orbit k ⊆ nuRFibre N m k :=
  orbit_subset_nuR_fibre N m k

/-! ## 2. Tight exactly when the fibre is one orbit -/

/-- **THE BOUND IS AN EQUALITY EXACTLY WHEN THE FIBRE IS THE ORBIT.** The watchlist item stated
this in prose from three results it named; here it is, from those three. -/
theorem card_orbit_eq_finrank_iff (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    (orbit k).card = Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (massive (torusGraph d (N + 3)) m) - (nuR N m k) • LinearMap.id))
      ↔ orbit k = nuRFibre N m k := by
  rw [finrank_eq_card_nuRFibre]
  constructor
  · intro h
    exact Finset.eq_of_subset_of_card_le (orbit_subset_nuRFibre N m k) h.ge
  · intro h
    rw [h]

/-- **THE SAME IN THE PUBLISHED FORM**, with the explicit lower bound on the left. -/
theorem bound_eq_finrank_iff (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    2 ^ (interiorAxes k).card
        * Nat.multinomial univ (fun c : Fin (N + 3) => Fintype.card {i // cls k i = c})
      = Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (massive (torusGraph d (N + 3)) m) - (nuR N m k) • LinearMap.id))
      ↔ orbit k = nuRFibre N m k := by
  rw [← card_orbit k]
  exact card_orbit_eq_finrank_iff N m k

/-- **AND STRICT EXACTLY WHEN THE ORBIT IS A PROPER PART OF THE FIBRE.** The bound's slack is the
part of the fibre outside the orbit, with nothing else in it. -/
theorem card_orbit_lt_finrank_iff (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    (orbit k).card < Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (massive (torusGraph d (N + 3)) m) - (nuR N m k) • LinearMap.id))
      ↔ orbit k ⊂ nuRFibre N m k := by
  rw [finrank_eq_card_nuRFibre]
  constructor
  · intro h
    exact Finset.ssubset_iff_subset_ne.mpr
      ⟨orbit_subset_nuRFibre N m k, fun he => (Nat.ne_of_lt h) (congrArg Finset.card he)⟩
  · exact Finset.card_lt_card

/-! ## 3. The criterion is not vacuous: an orbit properly inside its fibre -/

/-- **THE ORBIT IS NEVER BIGGER THAN `2 ^ d · d !`**, at any frequency and with no hypotheses —
`Finset.card_image_le` and nothing else. `TorusOrbitMultinomial.card_orbit` is unconditional and
exact and implies this; the point of the image route is that it needs neither `interiorAxes` nor
the multinomial identity to get the one number the corollary below uses. -/
theorem card_orbit_le_two_pow_mul_factorial {N : ℕ} (k : Site d (N + 3)) :
    (orbit k).card ≤ 2 ^ d * Nat.factorial d := by
  classical
  refine (Finset.card_image_le).trans ?_
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_finset, Fintype.card_perm,
    Fintype.card_fin]

/-- **AT `d = 2`, SIDE `24`, THE ORBIT OF `(1, 6)` IS A PROPER PART OF ITS FIBRE.** `9 ≤ dim` is
`TorusEightNotTight.nine_le_finrank_eight` and the orbit has at most `8` elements, so the criterion
above is not vacuously true. -/
theorem orbit_ssubset_nuRFibre_eight (m : ℝ) :
    orbit TorusEightNotTight.fA ⊂ nuRFibre 21 m TorusEightNotTight.fA := by
  refine (card_orbit_lt_finrank_iff 21 m TorusEightNotTight.fA).mp ?_
  refine lt_of_le_of_lt (card_orbit_le_two_pow_mul_factorial TorusEightNotTight.fA) ?_
  refine lt_of_lt_of_le ?_ (TorusEightNotTight.nine_le_finrank_eight m)
  norm_num [Nat.factorial]

end TorusBoundTightIff
