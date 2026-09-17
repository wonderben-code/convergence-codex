/-
  ConeSpectralGap: how far below the top the rest of the cone's spectrum sits — a gap that grows
  LINEARLY in the number of vertices, and the wheel's gap bracketed to within `8/n`

  **WHY THIS FILE EXISTS.** The watchlist item *a quantitative gap for the signless Laplacian —
  how far below the top is `λ₂`?* asks for one shape and one shape only: **something of the form
  `topEigen − λ₂ ≥ f(G)`**, because that is what a spectral-gap argument consumes. Six units of
  this chain fenced the second eigenvalue as absent; unit 93 named it for the wheel and unit 107
  removed its hypothesis. The item's own last status says what is still missing in the plainest
  terms available: *`λ₂` is NAMED and the top is named; **how far apart they are as a function of
  `N` is still not bounded here**.* This file bounds it.

  **WHAT WAS IN THE ESTATE BEFORE, CHECKED BY GREP AND NOT RECALLED.** Every declaration
  mentioning `hubRootPlus` was read. The bounds on it were **two constants**:
  `ConeTopEigen.two_mul_add_one_lt_hubRootPlus` (`2d + 1 < hubRootPlus`) and
  `WheelTable.five_lt_hubRootPlus_wheel` (`5 < hubRootPlus (n+3) 2`). **Nothing anywhere bounded
  the top eigenvalue in terms of the SIZE of the graph**, which is exactly what a gap growing with
  the graph needs, and it is why the item could be one step from its trigger for two days without
  moving.

  **THE ONE IDEA, AND IT IS AN IDENTITY.** The hub quadratic's discriminant
  `hubDisc n d = (n + 2d + 1)² − 8dn` is a **shifted square**:

      hubDisc n d = (n − 2d + 1)² + 8d.

  Unit 79 proved it positive and used the fact nowhere; written this way it does more than stay
  positive, because `√((n − 2d + 1)² + 8d) ≥ n − 2d + 1` with no case split at all. Feeding that
  into the quadratic formula gives `n + 1 ≤ hubRootPlus n d`, and the trivial
  `hubDisc n d ≤ (n + 2d + 1)²` gives `hubRootPlus n d ≤ n + 2d + 1`: **the cone's top eigenvalue
  is `|V| + 1` to within `2d`.** No spectral theorem, no Perron theory, no characteristic
  polynomial — the same economy the rest of this cluster runs on.

  **THE ITEM'S SHAPE, FOR THE WHOLE CONE FAMILY.** Unit 86's ceiling says every eigenvalue of the
  cone's `Q` other than `hubRootPlus` is at most `2d + 1`. Subtracting,

      topEigen − λ ≥ |V(G)| − 2d   for every eigenvalue λ ≠ topEigen,

  at the cone over ANY `d`-regular graph. That is `f(G) = |V(G)| − 2d`, which is the item's
  literal request, and it is **informative exactly when `|V| > 2d`** — said here rather than
  elsewhere, because for a dense base graph the bound is true and empty.

  **AND THE WHEEL, WHERE BOTH ENDS CAN BE PINNED.** At `d = 2` and base `cycleGraph (n+3)` the
  discriminant is the integer `n² + 16`, so `n + 4 ≤ hubRootPlus (n+3) 2 ≤ n + 6`, and unit 93's
  `λ₂ = 3 + 2cos(2π/N)` is trapped in `[3, 5)`. Hence

      n − 1 < topEigen − λ₂ ≤ n − 1 + 8/n   (n ≥ 1),

  **a two-sided bracket whose two ends close on each other**: the gap is `n − 1` to within `8/n`,
  so it is `Θ(|V|)` and the lower bound is asymptotically exact rather than merely true. The upper
  half is where unit 93's `5 − 4π²/N² ≤ λ₂` earns its keep — a ceiling on the gap needs a FLOOR
  under `λ₂`, and the only floor available is the rate at which `λ₂` approaches `5`.

  **AND THE TWO HALVES TOGETHER SAY THE GENERAL BOUND IS SHARP, WHICH IS THE STRONGEST CLAIM HERE.**
  At the wheel `|V(G)| = n + 3` and `d = 2`, so the general `f(G) = |V(G)| − 2d` reads `n − 1` —
  **the same `n − 1` the wheel's gap sits within `8/n` of.** So `|V(G)| − 2d` is not merely a true
  lower bound: it is **approached along the wheel family**, and no better function of `|V|` and `d`
  alone can be written. That is one theorem read twice rather than a new one, which is why it is
  said here and not restated as a declaration.

  **WHAT THIS DOES NOT DO, AND THE ITEM STAYS OPEN ON IT.** The item asks for `topEigen − λ₂ ≥
  f(G)` **in general**. What is here is the cone family, plus the wheel sharpened. Nothing here
  bounds `λ₂` at a graph that is not a cone, and the item's floor/ceiling asymmetry stands
  everywhere else. The second half of its closing condition — *the same ceiling at a graph that is
  not a cone* — is untouched, and `ERRATUM 246` applies: naming that as the residue is not a claim
  it is short.

  **ONE FENCE, UNCHANGED.** `λ₂` here is an `IsGreatest` in eigenvector form, not the estate's
  `SignlessSecondEigen.secondEigen`, which is a `sup'` over `IsHermitian.eigenvalues`. Unit 93
  named the route between them; this file does not travel it and claims nothing about `secondEigen`.

  **AND ONE THING IS NEW TO THE CLUSTER AND IS NOT HIDDEN: A NUMERIC BOUND ON `π`.** Grepped
  before it was used — **no file in `paper_f` had ever cited `Real.pi_lt_d2`, `pi_gt_d2`,
  `pi_lt_four`, `pi_le_four` or `pi_gt_three`**, and unit 93's row says of itself *no numerical
  estimate of `π`*. `four_mul_pi_sq_div_le` uses `Real.pi_lt_d2` (`π < 3.15`), and it is the ONLY
  declaration here that does. Its job is entirely cosmetic: it turns `4/n + 4π²/N²` into `8/n`.
  **The un-estimated form is stated separately as `hubRootPlus_sub_rimVal_one_le_sub_one_add` and
  stands without it**, so a reader who declines the estimate keeps the bracket and loses only the
  tidy right-hand side. The import `Mathlib.Analysis.Real.Pi.Bounds` is why the build gains TWO
  jobs and not one — 5010 to 5012, one for the new root and one for that module, which had never
  been in the closure.
-/

import ConeTopEigen
import WheelCollision
import Mathlib.Analysis.Real.Pi.Bounds

namespace ConeSpectralGap

open SimpleGraph LaplacianSignless Matrix
open ConeSignlessSpectrum ConeMultiplicity ConeMultiplicityExact ConeTopEigen
open WheelSpectrum WheelMultiplicity WheelTable WheelSecondEigen

/-! ## The discriminant is a shifted square

Unit 79's `cone_disc_pos` says `hubDisc` is positive. The identity below says WHERE the positivity
comes from — a square plus `8d` — and that is what turns a positivity into a size bound. -/

/-- **THE HUB DISCRIMINANT, COMPLETED AS A SQUARE.** `(n + 2d + 1)² − 8dn = (n − 2d + 1)² + 8d`.
Pure algebra; the content is the shape, not the proof. -/
theorem hubDisc_eq_sq_add (n d : ℕ) :
    hubDisc n d = ((n : ℝ) - 2 * d + 1) ^ 2 + 8 * d := by
  unfold hubDisc
  ring

/-! ## The general bracket: the cone's top eigenvalue is `|V| + 1` to within `2d` -/

section General

variable (n d : ℕ)

/-- **THE TOP HUB ROOT IS AT LEAST `n + 1`**, at every `n` and `d`, with no hypothesis.
`√((n − 2d + 1)² + 8d) ≥ n − 2d + 1` needs no sign information about `n − 2d + 1`, because a square
root dominates the thing whose square it dominates via `le_abs_self`. **This is the file's whole
lower half**: it is the first bound anywhere in the estate that ties the cone's top eigenvalue to
the SIZE of the base graph. -/
theorem add_one_le_hubRootPlus : (n : ℝ) + 1 ≤ hubRootPlus n d := by
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hsq : ((n : ℝ) - 2 * d + 1) ^ 2 ≤ hubDisc n d := by
    rw [hubDisc_eq_sq_add]; linarith
  have h : (n : ℝ) - 2 * d + 1 ≤ Real.sqrt (hubDisc n d) := by
    calc (n : ℝ) - 2 * d + 1 ≤ |(n : ℝ) - 2 * d + 1| := le_abs_self _
      _ = Real.sqrt (((n : ℝ) - 2 * d + 1) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (hubDisc n d) := Real.sqrt_le_sqrt hsq
  rw [hubRootPlus]
  linarith

/-- **AND AT MOST `n + 2d + 1`**, which is the sum of the two roots: the lower root is
non-negative, so the upper one cannot exceed the sum. Proved here from
`hubDisc n d ≤ (n + 2d + 1)²`, i.e. from `8dn ≥ 0`, which needs nothing about the roots at all. -/
theorem hubRootPlus_le_add_two_mul_add_one : hubRootPlus n d ≤ (n : ℝ) + 2 * d + 1 := by
  have hnn : (0 : ℝ) ≤ (n : ℝ) + 2 * d + 1 := by positivity
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h : Real.sqrt (hubDisc n d) ≤ (n : ℝ) + 2 * d + 1 := by
    rw [← Real.sqrt_sq hnn]
    apply Real.sqrt_le_sqrt
    unfold hubDisc
    nlinarith
  rw [hubRootPlus]
  linarith

end General

/-! ## The item's shape, for the whole cone family

`topEigen − λ ≥ |V(G)| − 2d` for every eigenvalue below the top. The bound is informative exactly
when `|V| > 2d`; at a dense base graph it is true and says nothing, which is stated rather than
hidden. -/

section ConeGap

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **THE QUANTITATIVE GAP THE ITEM ASKS FOR, AT THE CONE OVER ANY `d`-REGULAR GRAPH.** Unit 86's
ceiling puts everything but `hubRootPlus` at or below `2d + 1`; the lower bound above puts
`hubRootPlus` at or above `|V| + 1`. Subtracting gives `f(G) = |V(G)| − 2d`, which **grows
linearly in the number of vertices** at fixed degree.

**WHAT IT DOES NOT SAY.** For `|V| ≤ 2d` the right-hand side is `≤ 0` and the statement is empty —
the cone over a dense graph is not separated by this argument, and nothing here claims it is. -/
theorem card_sub_two_mul_le_hubRootPlus_sub [Nonempty V] {d : ℕ}
    (hreg : ∀ i, G.degree i = d) {lam : ℝ} {x : Option V → ℝ} (hx : x ≠ 0)
    (hQ : signlessLap (coneGraph G) *ᵥ x = lam • x)
    (hne : lam ≠ hubRootPlus (Fintype.card V) d) :
    (Fintype.card V : ℝ) - 2 * (d : ℝ) ≤ hubRootPlus (Fintype.card V) d - lam := by
  have hceil := le_two_mul_add_one_of_ne_hubRootPlus G hreg hx hQ hne
  have hfloor := add_one_le_hubRootPlus (Fintype.card V) d
  linarith

end ConeGap

/-! ## The wheel, where the discriminant is an integer and both ends can be pinned -/

section Wheel

variable (n : ℕ)

/-- **THE WHEEL'S DISCRIMINANT IS `n² + 16`.** At `d = 2` over a base of `n + 3` vertices the
shifted square of `hubDisc_eq_sq_add` is `(n + 3 − 3)² + 16`. -/
theorem hubDisc_wheel_eq_sq_add_sixteen : hubDisc (n + 3) 2 = (n : ℝ) ^ 2 + 16 := by
  rw [hubDisc_eq_sq_add]
  push_cast
  ring

/-- The wheel's top root, with the discriminant evaluated — the form the three bounds below all
read off. -/
theorem hubRootPlus_wheel_eq :
    hubRootPlus (n + 3) 2 = ((n : ℝ) + 8 + Real.sqrt ((n : ℝ) ^ 2 + 16)) / 2 := by
  rw [hubRootPlus, hubDisc_wheel_eq_sq_add_sixteen]
  push_cast
  ring_nf

/-- **`n + 4 ≤ hubRootPlus (n+3) 2`**, from `√(n² + 16) ≥ n`. This is
`add_one_le_hubRootPlus` at the wheel's index, kept as its own statement because the wheel's `n`
is the base graph's size MINUS three and getting that shift wrong is `ERRATUM 633`. -/
theorem add_four_le_hubRootPlus_wheel : (n : ℝ) + 4 ≤ hubRootPlus (n + 3) 2 := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h : (n : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2 + 16) := by
    have h1 : Real.sqrt ((n : ℝ) ^ 2) ≤ Real.sqrt ((n : ℝ) ^ 2 + 16) :=
      Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_sq hn0] at h1
  rw [hubRootPlus_wheel_eq]
  linarith

/-- **AND `hubRootPlus (n+3) 2 ≤ n + 6`**, from `√(n² + 16) ≤ n + 4`. So the wheel's top eigenvalue
is `n + 5 = N + 2` to within one — a two-sided pin the general bracket does not give, because the
general upper bound `n + 2d + 1` reads `n + 8` here. -/
theorem hubRootPlus_wheel_le_add_six : hubRootPlus (n + 3) 2 ≤ (n : ℝ) + 6 := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h : Real.sqrt ((n : ℝ) ^ 2 + 16) ≤ (n : ℝ) + 4 := by
    rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ (n : ℝ) + 4)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  rw [hubRootPlus_wheel_eq]
  linarith

/-- **AND `n/2 + 6 ≤ hubRootPlus (n+3) 2`**, from `√(n² + 16) ≥ 4`. Weaker than `n + 4` for
`n > 4` and STRONGER for `n < 4`, which is the whole point: at the small wheels the linear bound
is vacuous and this one is not. -/
theorem div_two_add_six_le_hubRootPlus_wheel : (n : ℝ) / 2 + 6 ≤ hubRootPlus (n + 3) 2 := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h : (4 : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2 + 16) := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  rw [hubRootPlus_wheel_eq]
  linarith

/-- **THE SHARP UPPER BOUND: `hubRootPlus (n+3) 2 ≤ n + 4 + 4/n` for `n ≥ 1`**, from
`√(n² + 16) ≤ n + 8/n`, whose square is `n² + 16 + 64/n²`. Together with
`add_four_le_hubRootPlus_wheel` this says the top eigenvalue is `n + 4` to within `4/n`, so the
lower bound is asymptotically exact rather than merely true. -/
theorem hubRootPlus_wheel_le_add_four_add_four_div (hn : 1 ≤ n) :
    hubRootPlus (n + 3) 2 ≤ (n : ℝ) + 4 + 4 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h : Real.sqrt ((n : ℝ) ^ 2 + 16) ≤ (n : ℝ) + 2 * (4 / (n : ℝ)) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (n : ℝ) + 2 * (4 / (n : ℝ)))]
    apply Real.sqrt_le_sqrt
    have hexp : ((n : ℝ) + 2 * (4 / (n : ℝ))) ^ 2
        = (n : ℝ) ^ 2 + 16 + 64 / (n : ℝ) ^ 2 := by
      field_simp
      ring
    rw [hexp]
    have : (0 : ℝ) ≤ 64 / (n : ℝ) ^ 2 := by positivity
    linarith
  rw [hubRootPlus_wheel_eq]
  linarith

end Wheel

/-! ## A floor under the wheel's second eigenvalue

A ceiling on the gap needs a FLOOR under `λ₂`, and this is the cheap one: from the fourth wheel on
the frequency-one angle is at most a quarter turn, so its cosine is non-negative. -/

section RimFloor

variable (n : ℕ)

/-- **`3 ≤ λ₂` FROM THE FOURTH WHEEL ON**, off unit 93's `zero_le_cos_angle_one`. It fails at
`n = 0`, where `rimVal 0 1 = 2`, which is why every gap ceiling below carries `1 ≤ n`. -/
theorem three_le_rimVal_one (hn : 1 ≤ n) : 3 ≤ rimVal n 1 := by
  have hc := zero_le_cos_angle_one n hn
  unfold rimVal
  linarith

end RimFloor

/-! ## The wheel's gap, bracketed

`n − 1 < topEigen − λ₂ ≤ n − 1 + 8/n`. The two ends close on each other, so the gap is `Θ(N)` and
the lower bound is asymptotically exact. -/

section WheelGap

variable (n : ℕ)

/-- **THE GAP IS MORE THAN `n − 1 = N − 4`.** Unit 93's `λ₂ < 5` and `n + 4 ≤ topEigen`. Strict,
because `λ₂ < 5` is strict at every wheel: unit 92's `rimVal_ne_five`. -/
theorem sub_one_lt_hubRootPlus_sub_rimVal_one :
    (n : ℝ) - 1 < hubRootPlus (n + 3) 2 - rimVal n 1 := by
  have htop := add_four_le_hubRootPlus_wheel n
  have hlam := rimVal_one_lt_five n
  linarith

/-- **AND MORE THAN `n/2 + 1`**, which is positive at every wheel including the ones where
`n − 1` says nothing. -/
theorem div_two_add_one_lt_hubRootPlus_sub_rimVal_one :
    (n : ℝ) / 2 + 1 < hubRootPlus (n + 3) 2 - rimVal n 1 := by
  have htop := div_two_add_six_le_hubRootPlus_wheel n
  have hlam := rimVal_one_lt_five n
  linarith

/-- **SO THE WHEEL'S GAP IS POSITIVE AT EVERY WHEEL**, `n = 0` included. -/
theorem hubRootPlus_sub_rimVal_one_pos : 0 < hubRootPlus (n + 3) 2 - rimVal n 1 := by
  have h := div_two_add_one_lt_hubRootPlus_sub_rimVal_one n
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- **THE CEILING ON THE GAP, IN THE FORM THE TWO INGREDIENTS GIVE IT.** The top is at most
`n + 4 + 4/n` and unit 93's `five_sub_le_rimVal_one` puts `λ₂` at least `5 − 4π²/N²`, so the gap is
at most `n − 1 + 4/n + 4π²/N²`. **This is where the rate at which `λ₂` approaches `5` is load
bearing**: a bound on the gap from above is a bound on `λ₂` from below, and `λ₂ < 5` is the wrong
direction for it. -/
theorem hubRootPlus_sub_rimVal_one_le_sub_one_add (hn : 1 ≤ n) :
    hubRootPlus (n + 3) 2 - rimVal n 1
      ≤ (n : ℝ) - 1 + 4 / (n : ℝ) + 4 * Real.pi ^ 2 / ((n + 3 : ℕ) : ℝ) ^ 2 := by
  have htop := hubRootPlus_wheel_le_add_four_add_four_div n hn
  have hlam := five_sub_le_rimVal_one n
  linarith

/-- `4π²/N² ≤ 4/n` for `n ≥ 1`, i.e. `π²n ≤ (n + 3)²`, off `Real.pi_lt_d2` (`π < 3.15`). The
quadratic `4n² − 15.69n + 36` has negative discriminant, so no case split on `n` is needed. -/
theorem four_mul_pi_sq_div_le (hn : 1 ≤ n) :
    4 * Real.pi ^ 2 / ((n + 3 : ℕ) : ℝ) ^ 2 ≤ 4 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcast : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
  have hpisq : Real.pi ^ 2 < 9.9225 := by
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  rw [hcast, div_le_div_iff₀ (by positivity) hn0]
  nlinarith [sq_nonneg ((n : ℝ) - 2), hn0.le]

/-- **THE BRACKET, CLOSED: `n − 1 < topEigen − λ₂ ≤ n − 1 + 8/n` for `n ≥ 1`.** The two ends are
`8/n` apart, so the wheel's spectral gap is `n − 1 = N − 4` to within `8/n` — **`Θ(N)`, with the
lower bound asymptotically exact.** No `Filter` and no `atTop`: an inequality at each `N`, as units
91 and 93 did for their rates. -/
theorem hubRootPlus_sub_rimVal_one_le_sub_one_add_eight_div (hn : 1 ≤ n) :
    hubRootPlus (n + 3) 2 - rimVal n 1 ≤ (n : ℝ) - 1 + 8 / (n : ℝ) := by
  have h := hubRootPlus_sub_rimVal_one_le_sub_one_add n hn
  have hpi := four_mul_pi_sq_div_le n hn
  have hsplit : (8 : ℝ) / (n : ℝ) = 4 / (n : ℝ) + 4 / (n : ℝ) := by ring
  rw [hsplit]
  linarith

/-- **AND THE GAP AS A STATEMENT ABOUT EVERY EIGENVALUE, WHICH IS THE ITEM'S LITERAL SHAPE AT THE
WHEEL.** Unit 107's `le_rimVal_one_of_eigen_of_ne_uncond` puts every eigenvalue but the top at or
below `λ₂`, unconditionally on `1 ≤ n`; so the gap bound above is a gap bound for all of them at
once. -/
theorem sub_one_lt_hubRootPlus_sub_of_eigen (hn : 1 ≤ n) {lam : ℝ}
    {x : Option (Fin (n + 3)) → ℝ} (hx0 : x ≠ 0)
    (hx : signlessLap (coneGraph (cycleGraph (n + 3))) *ᵥ x = lam • x)
    (hne : lam ≠ hubRootPlus (n + 3) 2) :
    (n : ℝ) - 1 < hubRootPlus (n + 3) 2 - lam := by
  have hle := WheelCollision.le_rimVal_one_of_eigen_of_ne_uncond hn hx0 hx hne
  have h := sub_one_lt_hubRootPlus_sub_rimVal_one n
  linarith

end WheelGap

end ConeSpectralGap
