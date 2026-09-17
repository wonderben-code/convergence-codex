/-
  WheelSecondEigen: the wheel's second eigenvalue, named — and the cone's ceiling shown sharp over
  the family and attained by no member of it

  WHY THIS FILE EXISTS. `RE-SWEEP #61` (2026-09-17) read the live watchlist against units 83–92 and
  its second finding was about `L37357`, *a quantitative gap for the signless Laplacian — how far
  below the top is `λ₂`?* That item's governing trigger says it would close on *a rim spectrum that
  makes the cone's `2d + 1` sharp*, and units 87 and 92 supply one. The sweep's own marker states
  the limit honestly: **`λ₂` was DETERMINED by a finite comparison and STATED nowhere.** This file
  performs the comparison.

  **WHAT THE COMPARISON IS.** Unit 92's table says the wheel's eigenvalues are `hubRootPlus`,
  `hubRootMinus`, and the rim values `3 + 2cos(2πk/N)`. So `λ₂` is whichever of `hubRootMinus` and
  the largest rim value is bigger. Cosine is decreasing, so the largest rim value is at `k = 1`;
  and the hub root loses, from the fourth wheel on.

  **THE HYPOTHESIS `1 ≤ n` IS SHARP, AND IT IS A THEOREM HERE RATHER THAN A REMARK.**
  `hubRootMinus_eq_rimVal_one_zero` proves `hubRootMinus 3 2 = rimVal 0 1`, so the strict
  inequality is FALSE at `n = 0` and the hypothesis is not a convenience. **The first draft of this
  paragraph asserted it in prose, citing unit 91's `hubRootMinus_eq_rim_three`**, which gives
  `hubRootMinus 3 2 = 3 + 2cos(2π·1/3)` and NOT the equality with `rimVal 0 1` — those differ by an
  arithmetic step no declaration performed. `estateclaim_scan` asked for the query behind the
  sentence; the answer is the theorem. That is the third unit in a row in which unit 91's collision
  decides where a statement can start.

  WHAT IS PROVED.

  * **`rimVal_le_rimVal_one`** — the rim's largest value is at frequency one, off
    `Real.cos_le_cos_of_nonneg_of_le_pi` with unit 90's `angle_mem_Icc` supplying the interval.
  * **`hubRootMinus_lt_three`, `zero_le_cos_angle_one`, `half_le_cos_angle_one`** — the three
    pieces the comparison splits into, and the split is at `N = 6`. Above it, unit 91's
    `hubRootMinus < 4` meets `cos(2π/N) ≥ 1/2`. Below it, the root has not reached `3` — the
    squared inequality is exactly `24 > 4N`, so the threshold is `N < 6` and not an estimate —
    while the cosine is already non-negative.
  * **`hubRootMinus_eq_rimVal_one_zero`, `hubRootMinus_lt_rimVal_one`** — the equality at the
    third wheel, and so the strict inequality at every wheel but that one.
  * **`isGreatest_wheel_second`** — **THE SECOND EIGENVALUE, NAMED**: `3 + 2cos(2π/N)` is the
    greatest eigenvalue other than the top. Stated as an `IsGreatest` over the eigenvalues other
    than `hubRootPlus`, so it needs no second-eigenvalue definition to be true of.
  * **`finrank_coneEig_rimVal_one`** — and its multiplicity is exactly two, straight off unit 92.
  * **`rimVal_one_lt_five`, `five_sub_le_rimVal_one`** — **THE BRACKET**:
    `5 - 4π²/N² ≤ λ₂ < 5`. The upper half is strict at every wheel, off unit 92's
    `rimVal_ne_five`; the lower half is `Real.one_sub_sq_div_two_le_cos`. **So unit 86's ceiling
    `2d + 1 = 5` is approached and reached by nothing**, which is the only sense in which a ceiling
    with no attaining member can be called sharp, and it is stated as an inequality at each `N`
    rather than as a limit — no `Filter`, no `atTop`, the same choice unit 91 made for its rate.

  WHAT IS **NOT** CLAIMED.

  * **THE `IsHermitian.eigenvalues` FENCE IS NOT CROSSED, AND THIS TIME THE CROSSING IS PRICED.**
    The estate's own second-eigenvalue object is
    `SignlessSecondEigen.secondEigen hA = (univ.erase (topIdx hA)).sup' _ hA.eigenvalues`, defined
    through the enumeration this cluster has side-stepped in every unit. `isGreatest_wheel_second`
    is in eigenvector form and **is not connected to it here**. Unlike the earlier units' fences,
    the route is now visible and named:
    `HermitianFibreCount.finrank_eigenspace_hermitian_eq_card_fibre` turns an eigenspace dimension
    into the size of the fibre `{i | eigenvalues i = μ}`, so unit 92's
    `finrank = 2 > 0` produces an INDEX carrying `λ₂`, and unit 86's simple top produces one
    carrying the top. **Naming a route is not a claim it is short** (`ERRATUM 194`), and it is
    not attempted here (`ERRATUM 246`) — but it is no longer an unexamined fence, and that
    difference is the point of saying it.
    [**ATTEMPTED AND DONE, 2026-09-17, unit 113** (`ERRATUM 94`, kept rather than struck):
    `WheelSecondFence.secondEigen_eq_rimVal_one` proves `secondEigen (wheelHerm n) = rimVal n 1`
    for every `n ≥ 1`. **AND THIS BULLET NAMED ONLY ONE HALF OF THE ROUTE.** The fibre count is
    the half stated above; the other half is `HermitianCharpoly.mem_image_eigenvalues_iff`, which
    turns an index into an eigenvector and back, had been in the estate since 2026-09-12, and is
    named in no fence sentence of this cluster. This row's ledger entry additionally claimed the
    route was *named for the first time*, which is false — see the erratum.]
  * **NOTHING ABOUT `λ₂` AT A GRAPH THAT IS NOT A WHEEL.** `L37357`'s general question —
    `topEigen − λ₂ ≥ f(G)` for arbitrary `G` — is untouched, and the research-scale reading in that
    item stands for it. What closes here is one half of that item's own closing condition.
  * **THE NON-COLLISION HYPOTHESIS IS INHERITED, NOT DISCHARGED.** `isGreatest_wheel_second` and
    `finrank_coneEig_rimVal_one` take unit 92's `hcol`, which is false at `N = 3` and proved only
    at `N = 4`. The three comparison lemmas and the whole bracket are **unconditional**.
  * **NO LIMIT, NO ASYMPTOTICS, NO `π` ESTIMATE.** `5 - 4π²/N²` is exact as written; nothing here
    evaluates `π` or bounds it numerically.
  * **NOTHING ABOUT THE CASCADE, THE SPINE OR ANY WALL.**

  THE HYPOTHESES, READ OFF THE BINDERS. `1 ≤ n` is taken by three declarations and is sharp at
  `N = 3` as above. `hcol` is taken by two and by nothing in `Compare` or `Bracket`.
  `hubRootMinus_lt_three` takes `n + 3 < 6`, which is the exact threshold its squared inequality
  gives, and `half_le_cos_angle_one` takes `3 ≤ n`, the complementary case.

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import WheelTable

namespace WheelSecondEigen

open SimpleGraph LaplacianSignless Matrix
open ConeSignlessSpectrum ConeMultiplicity ConeMultiplicityExact ConeTopEigen
open WheelSpectrum WheelMultiplicity ConeDimensionSum WheelTable
open CycleEigenvalueDistinct WheelHubCollision

/-! ## The largest rim value sits at frequency one -/

section Compare

variable (n : ℕ)

/-- **COSINE IS DECREASING, SO THE RIM'S LARGEST VALUE IS AT `k = 1`.** -/
theorem rimVal_le_rimVal_one {k : ℕ} (h1 : 1 ≤ k) (h2 : 2 * k ≤ n + 3) :
    rimVal n k ≤ rimVal n 1 := by
  have hN : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
  have hmono : Real.cos (2 * Real.pi * (k : ℝ) / ((n + 3 : ℕ) : ℝ))
      ≤ Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) / ((n + 3 : ℕ) : ℝ)) := by
    refine Real.cos_le_cos_of_nonneg_of_le_pi (cycle_angle_nonneg (N := n + 3) 1) ?_ ?_
    · exact (angle_mem_Icc (N := n + 3) (by omega) h2).2
    · rw [div_le_div_iff_of_pos_right hN]
      have hk : ((1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
      have := Real.pi_pos
      nlinarith
  unfold rimVal
  linarith

/-- Below the sixth wheel the lower hub root has not yet climbed past `3`. The threshold is
`N < 6`, exactly: the squared inequality is `24 > 4N`. -/
theorem hubRootMinus_lt_three (hn : n + 3 < 6) : hubRootMinus (n + 3) 2 < 3 := by
  have hN : ((n + 3 : ℕ) : ℝ) < 6 := by exact_mod_cast hn
  have hN0 : (3 : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by
    have : (3 : ℕ) ≤ n + 3 := by omega
    exact_mod_cast this
  have hlt : ((n + 3 : ℕ) : ℝ) - 1 < Real.sqrt (hubDisc (n + 3) 2) := by
    refine Real.lt_sqrt_of_sq_lt ?_
    change _ < (((n + 3 : ℕ) : ℝ) + 2 * 2 + 1) ^ 2 - 4 * (2 * 2 * ((n + 3 : ℕ) : ℝ))
    nlinarith
  rw [hubRootMinus]
  linarith

/-- The angle at frequency one is at most a quarter turn from the fourth wheel on, so its cosine
is non-negative. -/
theorem zero_le_cos_angle_one (hn : 1 ≤ n) :
    0 ≤ Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) / ((n + 3 : ℕ) : ℝ)) := by
  have hN : (4 : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by
    have : (4 : ℕ) ≤ n + 3 := by omega
    exact_mod_cast this
  have hpi := Real.pi_pos
  have hle : 2 * Real.pi * ((1 : ℕ) : ℝ) / ((n + 3 : ℕ) : ℝ) ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    push_cast at hN ⊢
    nlinarith
  have := Real.cos_le_cos_of_nonneg_of_le_pi (cycle_angle_nonneg (N := n + 3) 1)
    (by linarith : Real.pi / 2 ≤ Real.pi) hle
  rw [Real.cos_pi_div_two] at this
  exact this

/-- And at most a sixth of a turn from the sixth wheel on, so its cosine is at least a half —
which is where the rim's largest value passes `4`, the value unit 91's lower root approaches. -/
theorem half_le_cos_angle_one (hn : 3 ≤ n) :
    (1 : ℝ) / 2 ≤ Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) / ((n + 3 : ℕ) : ℝ)) := by
  have hN : (6 : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by
    have : (6 : ℕ) ≤ n + 3 := by omega
    exact_mod_cast this
  have hpi := Real.pi_pos
  have hle : 2 * Real.pi * ((1 : ℕ) : ℝ) / ((n + 3 : ℕ) : ℝ) ≤ Real.pi / 3 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    push_cast at hN ⊢
    nlinarith
  have := Real.cos_le_cos_of_nonneg_of_le_pi (cycle_angle_nonneg (N := n + 3) 1)
    (by linarith : Real.pi / 3 ≤ Real.pi) hle
  rw [Real.cos_pi_div_three] at this
  exact this

/-- **AND THE HYPOTHESIS BELOW IS SHARP, AS A THEOREM AND NOT AS A REMARK.** At the third wheel
the lower hub root and the rim's largest value are the same number, so the strict inequality that
follows is FALSE at `n = 0`. `estateclaim_scan` asked for the query behind the header sentence that
said so, and this is the answer it should have had in the first place. -/
theorem hubRootMinus_eq_rimVal_one_zero : hubRootMinus 3 2 = rimVal 0 1 := by
  rw [hubRootMinus_three_two]
  unfold rimVal
  rw [show 2 * Real.pi * ((1 : ℕ) : ℝ) / ((0 + 3 : ℕ) : ℝ) = 2 * Real.pi * 1 / 3 by
      push_cast; ring, cos_two_pi_div_three]
  ring

/-- **THE LOWER HUB ROOT IS BELOW THE RIM'S LARGEST VALUE, FROM THE FOURTH WHEEL ON — AND THE
HYPOTHESIS IS SHARP.** At `N = 3` the two are EQUAL, both `2`, which is unit 91's collision. The
proof splits at `N = 6`: above it unit 91's `< 4` meets `cos ≥ 1/2`, below it the root has not
reached `3` and the cosine is already non-negative. -/
theorem hubRootMinus_lt_rimVal_one (hn : 1 ≤ n) : hubRootMinus (n + 3) 2 < rimVal n 1 := by
  rcases le_or_gt 3 n with h | h
  · have hc := half_le_cos_angle_one n h
    have h4 := hubRootMinus_lt_four (n + 3)
    unfold rimVal
    linarith
  · have hc := zero_le_cos_angle_one n hn
    have h3 := hubRootMinus_lt_three n (by omega)
    unfold rimVal
    linarith

end Compare

/-! ## The second eigenvalue, named -/

section Second

variable (n : ℕ)

theorem one_ne_zero_fin : (⟨1, by omega⟩ : Fin (n + 3)) ≠ 0 := by
  intro h
  exact absurd (congrArg Fin.val h) (by simp)

theorem rimVal_one_ne_hubRootPlus : rimVal n 1 ≠ hubRootPlus (n + 3) 2 := by
  intro h
  have hmem := rimVal_mem_rimSet n (k := 1) (by omega) (by omega)
  rw [h] at hmem
  exact hubRootPlus_notMem_rimSet n hmem

theorem eigen_rimVal_one : ∃ x : Option (Fin (n + 3)) → ℝ, x ≠ 0 ∧
    signlessLap (coneGraph (cycleGraph (n + 3))) *ᵥ x = rimVal n 1 • x := by
  have h := wheel_rim_eigenvalue n ⟨1, by omega⟩ (one_ne_zero_fin n)
  rw [← rimVal_eq_wheel n ⟨1, by omega⟩] at h
  exact h

/-- Everything other than the top is at or below the rim's largest value. -/
theorem le_rimVal_one_of_eigen_of_ne (hcol : hubRootMinus (n + 3) 2 ∉ rimSet n) (hn : 1 ≤ n)
    {lam : ℝ} {x : Option (Fin (n + 3)) → ℝ} (hx0 : x ≠ 0)
    (hx : signlessLap (coneGraph (cycleGraph (n + 3))) *ᵥ x = lam • x)
    (hne : lam ≠ hubRootPlus (n + 3) 2) : lam ≤ rimVal n 1 := by
  have hmem := mem_wheelSet_of_eigen n hcol hx0 hx
  rw [wheelSet, Finset.mem_insert, Finset.mem_insert] at hmem
  rcases hmem with rfl | rfl | hmem
  · exact absurd rfl hne
  · exact (hubRootMinus_lt_rimVal_one n hn).le
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hmem
    have h := Finset.mem_Icc.1 hk
    exact rimVal_le_rimVal_one n h.1 (by omega)

/-- **THE WHEEL'S SECOND EIGENVALUE, NAMED**: `3 + 2cos(2π/N)`, the greatest eigenvalue other than
the top. This is the value `RE-SWEEP #61`'s `L37357` marker says was determined and unstated. -/
theorem isGreatest_wheel_second (hcol : hubRootMinus (n + 3) 2 ∉ rimSet n) (hn : 1 ≤ n) :
    IsGreatest {lam : ℝ | (∃ x, x ≠ 0 ∧
        signlessLap (coneGraph (cycleGraph (n + 3))) *ᵥ x = lam • x)
      ∧ lam ≠ hubRootPlus (n + 3) 2} (rimVal n 1) := by
  refine ⟨⟨eigen_rimVal_one n, rimVal_one_ne_hubRootPlus n⟩, ?_⟩
  intro lam hlam
  obtain ⟨⟨x, hx0, hx⟩, hne⟩ := hlam
  exact le_rimVal_one_of_eigen_of_ne n hcol hn hx0 hx hne

/-- And its multiplicity is exactly two, off unit 92's table. -/
theorem finrank_coneEig_rimVal_one (hcol : hubRootMinus (n + 3) 2 ∉ rimSet n) :
    Module.finrank ℝ (coneEig (cycleGraph (n + 3)) (rimVal n 1)) = 2 :=
  finrank_coneEig_rimVal n hcol (k := 1) (by omega) (by omega) (by omega)

end Second

/-! ## The bracket: the cone's ceiling is sharp over the family and attained by none -/

section Bracket

variable (n : ℕ)

/-- **STRICTLY BELOW THE CEILING, AT EVERY WHEEL.** `2d + 1 = 5` is never attained. -/
theorem rimVal_one_lt_five : rimVal n 1 < 5 :=
  lt_of_le_of_ne (WheelHubCollision.rim_value_mem_Icc _).2 (rimVal_ne_five n (by omega) (by omega))

/-- **AND WITHIN `4π²/N²` OF IT**, off `Real.one_sub_sq_div_two_le_cos`. So the ceiling is
approached and never reached: the separation `2d + 1 − λ₂` is positive at every wheel and tends to
nothing across the family — **which is the only sense in which a ceiling with no attaining member
can be sharp.** No `Filter`, no `atTop`: an inequality at each `N`. -/
theorem five_sub_le_rimVal_one :
    5 - 4 * Real.pi ^ 2 / ((n + 3 : ℕ) : ℝ) ^ 2 ≤ rimVal n 1 := by
  have hN : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
  have hc := Real.one_sub_sq_div_two_le_cos
    (x := 2 * Real.pi * ((1 : ℕ) : ℝ) / ((n + 3 : ℕ) : ℝ))
  have hsq : (2 * Real.pi * ((1 : ℕ) : ℝ) / ((n + 3 : ℕ) : ℝ)) ^ 2
      = 4 * Real.pi ^ 2 / ((n + 3 : ℕ) : ℝ) ^ 2 := by
    push_cast
    field_simp
    ring
  rw [hsq] at hc
  unfold rimVal
  linarith

end Bracket

end WheelSecondEigen
