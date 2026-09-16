/-
  ConeTopEigen: the cone's TOP eigenvalue, written down, proved simple, and separated from
  everything else by an explicit gap

  WHY THIS FILE EXISTS. `PROOF_STRATEGY` §6's third question — *if the unit I just finished was
  a B, retry B→C right now, before touching the queue.* Unit 85 proved the maximum degree bounds
  an adjacency eigenvalue in eigenvector form, and its whole reason for existing was a ceiling it
  did not itself prove. This is the ceiling. It is also `UNLOCK_WATCHLIST` **L37122**'s own
  trigger — *revisit when a ceiling on `λ₂` appears from another direction* — for one family.

  THE ARITHMETIC THE WHOLE FILE TURNS ON, and it is one line. With `S = n + 2d + 1` and
  `D = S² − 8dn` the hub quadratic's discriminant, both

      `D − (2d + 1 − n)² = 4n`     and     `D − (n − 2d − 1)² = 4n`

  because the two squares are equal. So a single positivity fact separates the larger hub root
  from `2d + 1` **above** and the smaller one from `2d + 1` **below**, and `4n > 0` is the entire
  content of both.

  WHAT IS PROVED.

  * **`sq_lt_hubDisc`** — `(2d + 1 − n)² < D` at every `n ≥ 1` and every `d`, by `nlinarith` on
    the identity above. Unit 79's `cone_disc_pos` is the `n`-free ancestor of this; this is the
    sharpened form the separation needs.
  * **`two_mul_add_one_lt_hubRootPlus`** and **`hubRootMinus_lt_two_mul_add_one`** — the two hub
    roots sit strictly on opposite sides of `2d + 1`.
  * **`rimEig_eq_bot_of_lt`** — the rim's zero-sum eigenspace is **trivial** at any `μ` with
    `d < |μ|`. This is unit 85 read as a statement about a submodule rather than about a number,
    and it is what makes the top simple.
  * **`le_two_mul_add_one_of_ne_hubRootPlus`** — **THE CEILING.** Every eigenvalue of the cone's
    signless Laplacian other than `hubRootPlus` is at most `2d + 1`. Unit 80's
    `eigenvalue_dichotomy` splits, unit 83's `hubRoot_iff_eq` names the two roots, and unit 85
    bounds the rim branch.
  * **`isGreatest_coneSpectrum`** — so `hubRootPlus` **is** the top of the spectrum, as an
    `IsGreatest`: it is an eigenvalue (unit 83) and nothing exceeds it.
  * **`cone_gap_pos`** — and the gap below it is explicit and strictly positive:
    `hubRootPlus − (2d + 1) = (√D − (2d + 1 − n))/2 > 0`. Not `gap_pos`: that name is taken
    eight times in this estate, and one of the eight is the same shape as this statement.
  * **`finrank_coneEig_hubRootPlus`** — **THE TOP IS SIMPLE**, its eigenspace exactly one
    dimension. `hubRootPlus − d − 1 > d`, so the rim contributes nothing by
    `rimEig_eq_bot_of_lt`, and unit 83's `finrank_coneEig_of_hubRoot` turns `0` into `0 + 1`.

  WHAT IS **NOT** CLAIMED.

  * **`λ₂` IS NOT EVALUATED, AND THE CEILING IS NOT SHOWN TIGHT.** `2d + 1` is an upper bound on
    everything below the top; whether any eigenvalue attains it depends on the rim's spectrum,
    which this chain has computed for no `G`. L37122 asked for *a ceiling on `λ₂`* and gets one;
    it did not ask for the value and does not get it.
  * **NO ORDERING OF THE REST OF THE SPECTRUM.** One eigenvalue is identified and separated. The
    other `n − 1` are still the rim's, unevaluated, and nothing here says which is second.
  * **NOTHING FOR A NON-REGULAR RIM**, and nothing about Mathlib's `IsHermitian.eigenvalues`
    indexing — the fence this cluster has met in every unit and has still not crossed.
  * **NOTHING ABOUT THE CASCADE, THE SPINE OR ANY WALL.**

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import ConeMultiplicityExact
import AdjEigenvectorBound

namespace ConeTopEigen

open SimpleGraph LaplacianSignless Matrix ConeSignlessSpectrum ConeSignlessExhaustion
open ConeMultiplicity ConeMultiplicityExact

/-! ## The separation, which is one positivity fact used twice -/

section Separation

variable (n d : ℕ)

/-- **THE SHARPENED DISCRIMINANT BOUND.** `D − (2d + 1 − n)² = 4n`, so a positive vertex count
separates the roots from `2d + 1`. Unit 79's `cone_disc_pos` is this with `n` dropped. -/
theorem sq_lt_hubDisc (hn : 0 < n) :
    (2 * (d : ℝ) + 1 - (n : ℝ)) ^ 2 < hubDisc n d := by
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  change (2 * (d : ℝ) + 1 - (n : ℝ)) ^ 2
      < ((n : ℝ) + 2 * d + 1) ^ 2 - 4 * (2 * d * (n : ℝ))
  nlinarith [hn']

/-- and the same identity with the sign of `n − 2d − 1` the other way. -/
theorem sq_lt_hubDisc' (hn : 0 < n) :
    ((n : ℝ) - 2 * (d : ℝ) - 1) ^ 2 < hubDisc n d := by
  have h := sq_lt_hubDisc n d hn
  have : ((n : ℝ) - 2 * (d : ℝ) - 1) ^ 2 = (2 * (d : ℝ) + 1 - (n : ℝ)) ^ 2 := by ring
  rw [this]; exact h

/-- **THE LARGER HUB ROOT IS STRICTLY ABOVE `2d + 1`.** -/
theorem two_mul_add_one_lt_hubRootPlus (hn : 0 < n) :
    2 * (d : ℝ) + 1 < hubRootPlus n d := by
  have hD : (0 : ℝ) ≤ hubDisc n d := (hubDisc_pos n d).le
  have hlt : 2 * (d : ℝ) + 1 - (n : ℝ) < Real.sqrt (hubDisc n d) := by
    calc 2 * (d : ℝ) + 1 - (n : ℝ) ≤ |2 * (d : ℝ) + 1 - (n : ℝ)| := le_abs_self _
      _ = Real.sqrt ((2 * (d : ℝ) + 1 - (n : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ < Real.sqrt (hubDisc n d) := by
          exact Real.sqrt_lt_sqrt (sq_nonneg _) (sq_lt_hubDisc n d hn)
  rw [hubRootPlus]
  linarith

/-- **AND THE SMALLER ONE IS STRICTLY BELOW IT.** -/
theorem hubRootMinus_lt_two_mul_add_one (hn : 0 < n) :
    hubRootMinus n d < 2 * (d : ℝ) + 1 := by
  have hlt : (n : ℝ) - 2 * (d : ℝ) - 1 < Real.sqrt (hubDisc n d) := by
    calc (n : ℝ) - 2 * (d : ℝ) - 1 ≤ |(n : ℝ) - 2 * (d : ℝ) - 1| := le_abs_self _
      _ = Real.sqrt (((n : ℝ) - 2 * (d : ℝ) - 1) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ < Real.sqrt (hubDisc n d) := Real.sqrt_lt_sqrt (sq_nonneg _) (sq_lt_hubDisc' n d hn)
  rw [hubRootMinus]
  linarith

/-- **THE GAP, EXPLICIT AND POSITIVE.**

**NOT CALLED `gap_pos`, AND THE NAME WAS CHECKED RATHER THAN CHOSEN.** `newnames_scan` reported
`gap_pos` taken in `CascadeFoundation` and `IsingTransferMatrix`; the estate has **eight** of
them. Six are structure-field positivity (`0 < self.gap`, `0 < self.spectral_gap`) and would not
have been confused with this, but **`IsingTransferMatrix.gap_pos` is the same SHAPE as this
one** — `0 < lamPlus β − |lamMinus β|`, a top minus a bound on everything else — so the flag was
right and the collision would have been the confusing kind. Renamed rather than accepted. -/
theorem cone_gap_pos (hn : 0 < n) : 0 < hubRootPlus n d - (2 * (d : ℝ) + 1) :=
  sub_pos.2 (two_mul_add_one_lt_hubRootPlus n d hn)

end Separation

/-! ## The rim contributes nothing above the degree -/

section Rim

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **UNIT 85, READ AS A STATEMENT ABOUT A SUBMODULE.** Above the degree the rim's zero-sum
eigenspace is trivial, because a nonzero member would be an adjacency eigenvector carrying an
eigenvalue larger in modulus than the degree. -/
theorem rimEig_eq_bot_of_lt {d : ℕ} (hreg : ∀ i, G.degree i = d) {mu : ℝ}
    (hmu : (d : ℝ) < |mu|) : rimEig G mu = ⊥ := by
  refine Submodule.eq_bot_iff _ |>.2 fun y hy => ?_
  by_contra hne
  have hy' := (mem_rimEig G).1 hy
  exact absurd (AdjEigenvectorBound.abs_le_of_regular G hreg hne hy'.1) (not_le.2 hmu)

end Rim

/-! ## The top of the spectrum -/

section Top

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **THE CEILING.** Every eigenvalue of the cone's signless Laplacian other than `hubRootPlus`
is at most `2d + 1`: unit 80's dichotomy splits it, unit 83 names the two hub roots, and unit 85
bounds the rim branch. -/
theorem le_two_mul_add_one_of_ne_hubRootPlus [Nonempty V] {d : ℕ}
    (hreg : ∀ i, G.degree i = d) {lam : ℝ} {x : Option V → ℝ} (hx : x ≠ 0)
    (hQ : signlessLap (coneGraph G) *ᵥ x = lam • x)
    (hne : lam ≠ hubRootPlus (Fintype.card V) d) :
    lam ≤ 2 * (d : ℝ) + 1 := by
  have hn : 0 < Fintype.card V := Fintype.card_pos
  rcases eigenvalue_dichotomy G hreg hx hQ with hroot | ⟨y, hy0, _, hye⟩
  · rcases (hubRoot_iff_eq (Fintype.card V) d lam).1 hroot with h | h
    · exact absurd h hne
    · rw [h]
      exact (hubRootMinus_lt_two_mul_add_one (Fintype.card V) d hn).le
  · have habs := AdjEigenvectorBound.abs_le_of_regular G hreg hy0 hye
    have := le_of_abs_le habs
    linarith

/-- **SO `hubRootPlus` IS THE TOP OF THE SPECTRUM**, as an `IsGreatest`: unit 83 makes it an
eigenvalue and the ceiling above makes it the largest. -/
theorem isGreatest_coneSpectrum [Nonempty V] {d : ℕ} (hreg : ∀ i, G.degree i = d) :
    IsGreatest {lam : ℝ | ∃ x : Option V → ℝ, x ≠ 0 ∧
        signlessLap (coneGraph G) *ᵥ x = lam • x} (hubRootPlus (Fintype.card V) d) := by
  have hn : 0 < Fintype.card V := Fintype.card_pos
  constructor
  · have h1 := one_le_finrank_coneEig_hubRootPlus G hreg
    have hne : coneEig G (hubRootPlus (Fintype.card V) d) ≠ ⊥ :=
      Submodule.one_le_finrank_iff.1 h1
    obtain ⟨x, hxmem, hx0⟩ := Submodule.ne_bot_iff _ |>.1 hne
    exact ⟨x, hx0, (mem_coneEig G).1 hxmem⟩
  · rintro lam ⟨x, hx, hQ⟩
    by_cases hb : lam = hubRootPlus (Fintype.card V) d
    · exact hb.le
    · exact le_trans (le_two_mul_add_one_of_ne_hubRootPlus G hreg hx hQ hb)
        (two_mul_add_one_lt_hubRootPlus (Fintype.card V) d hn).le

/-- **AND THE TOP IS SIMPLE.** `hubRootPlus − d − 1 > d`, so the rim's zero-sum eigenspace there
is trivial, and unit 83's multiplicity formula turns `0` into `0 + 1`. -/
theorem finrank_coneEig_hubRootPlus [Nonempty V] {d : ℕ} (hreg : ∀ i, G.degree i = d) :
    Module.finrank ℝ (coneEig G (hubRootPlus (Fintype.card V) d)) = 1 := by
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have hgt : (d : ℝ) < |hubRootPlus (Fintype.card V) d - (d : ℝ) - 1| := by
    have h := two_mul_add_one_lt_hubRootPlus (Fintype.card V) d hn
    have hpos : (d : ℝ) < hubRootPlus (Fintype.card V) d - (d : ℝ) - 1 := by linarith
    calc (d : ℝ) < hubRootPlus (Fintype.card V) d - (d : ℝ) - 1 := hpos
      _ ≤ |hubRootPlus (Fintype.card V) d - (d : ℝ) - 1| := le_abs_self _
  have hbot := rimEig_eq_bot_of_lt G hreg hgt
  have hrim : Module.finrank ℝ
      (rimEig G (hubRootPlus (Fintype.card V) d - (d : ℝ) - 1)) = 0 := by
    rw [hbot]; simp
  have hmain := finrank_coneEig_of_hubRoot G hreg
    (hubRoot_hubRootPlus (Fintype.card V) d)
  omega

end Top

end ConeTopEigen
