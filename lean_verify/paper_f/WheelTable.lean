/-
  WheelTable: the wheel's complete multiplicity table, with the hypothesis unit 91 showed is a
  hypothesis written into the statement

  WHY THIS FILE EXISTS. `PROOF_STRATEGY` §7 has asked for the wheel's multiplicity table since
  unit 87, and six units assembled its ingredients: the rim's values (unit 87), their multiplicity
  from below (unit 88), the dimension-sum bound and the exactness principle (unit 89), the values'
  distinctness and count (unit 90), and the top's simplicity (unit 86). Units 89 and 90 both said
  the last thing needed was `hubRootMinus` distinct from every rim value. **Unit 91 evaluated that
  at `N = 3` and found it FALSE** (`ERRATUM 622`), so this file does the only honest thing left:
  it states the non-collision as a hypothesis, `hcol : hubRootMinus (n+3) 2 ∉ rimSet n`, and
  proves the table under it — then proves the hypothesis is not vacuous.

  **CHECKED NUMERICALLY BEFORE ANY LEAN WAS WRITTEN, at seven instances.** The predicted table —
  one at each hub root, two at each rim value, one at the half turn — was compared against the
  eigenvalues of the wheel's signless Laplacian computed directly for `N = 3` through `N = 9`. It
  agrees at all seven, **including `N = 3`, where the collision makes `2` appear three times**
  rather than as `1 + 2` at two values. That check is floating point and is not evidence for
  anything proved here; it is what stopped a wrong table being stated. `ERRATUM 622`'s rule is
  that the smallest instances get evaluated first, and this is the first unit written after it.

  **AND THE HYPOTHESIS IS SHOWN SATISFIABLE**, which matters more than usual here: unit 91 proved
  it FAILS at `N = 3`, so a conditional table could in principle have had an empty class of
  instances. `hubRootMinus_notMem_rimSet_one` proves it HOLDS at `N = 4`, by computing
  `rimSet 1 = {3, 1}` and `hubDisc 4 2 = 17` and comparing. **A conditional theorem whose
  hypothesis is never checked for satisfiability is the shape of `ERRATUM 13`'s vacuous
  statement**, and one instance is the cheapest possible guard against it.

  WHAT IS PROVED.

  * **`rimVal`, `rimSet`** — the rim value `3 + 2cos(2πk/N)` and the `Finset` of them, indexed by
    the half-range `[1, N/2]`. `rimVal_mem_rimSet` is the statement that the fold loses nothing,
    off unit 90's `cos_reflect`; `card_rimSet` gives `N/2`, off unit 90's half-range injectivity.
  * **`rimVal_eq_one_iff`, `rimVal_ne_five`, `rimVal_ne_one_of_ne`** — the two ends of the rim's
    range are reached only at the two exceptional frequencies: `5` only at `k = 0`, and `1` only
    at the half turn `2k = N`. Both go through `Real.injOn_cos` on the interval unit 90 supplies.
  * **`sum_rim_mult`** — **THE ARITHMETIC COINCIDENCE THE WHOLE TABLE TURNS ON.** Summed over the
    half-range, *two at each frequency, one at the half turn* is `N - 1` **at both parities**: an
    odd `N` has no half turn but one fewer frequency. Had those differed the table would have
    needed two statements.
  * **`five_lt_hubRootPlus_wheel`, `hubRootPlus_notMem_rimSet`** — the top is out of the rim's
    range, off unit 86.
  * **`one_lt_hubRootMinus_two`** — **unit 91's hypothesis was sufficient and not necessary.** At
    `d = 2` the sharp condition `n(2d - 1) > 2d` reads `3N > 4`, which every wheel satisfies, so
    the lower root clears the bottom of the rim range with **no hypothesis at all**. Unit 91
    asked for `2d < n`, which would have excluded `N = 3` and `N = 4`.
  * **`wheelMult`, `wheelSet`, `sum_wheelMult`, `lb_wheelMult`** — the claimed multiplicities, the
    set they live on, the fact that they sum to exactly `card V + 1 = n + 4`, and the fact that
    each is a lower bound. The lower bounds are units 83, 86 and 88 read off at each value.
  * **`finrank_coneEig_eq_wheelMult`** — **THE TABLE.** Unit 89's pigeonhole closes every
    eigenvalue at once, because the lower bounds already fill the space.
  * **`finrank_coneEig_rimVal`** — **THE RIM'S EXHAUSTION, WHICH IS WHAT THE CHAIN HAS OWED SINCE
    UNIT 88**: the multiplicity is EXACTLY two, not merely at least two.
  * **`finrank_coneEig_rimVal_half`** — and exactly one at the half turn. Unit 88's `sin ≠ 0`
    hypothesis turns out to be **sharp**, not an artefact of its route.
  * **`finrank_coneEig_hubRootMinus_eq_one`** — and the lower hub root is simple. Unit 83 gave
    `1 ≤`; this is the equality, and unit 91's `N = 3` is why it needs the hypothesis.
  * **`finrank_coneEig_wheel_four_three`** — **the second exactly computed multiplicity in this
    chain and the first that came out of the general table**: the four-spoke wheel has the
    eigenvalue `3` with multiplicity exactly `2`.
  * **`sum_finrank_eq_card`, `mem_wheelSet_of_eigen`, `eigen_of_mem_wheelSet`,
    `wheel_spectrum_eq`** — **AND NOTHING IS OUTSIDE THE TABLE.** The dimensions fill the space
    exactly, so `HermitianFibreCount.mem_of_isEigenvalue_of_sum_eq` says a further eigenvalue
    would need a dimension there is no room for; and every value listed is an eigenvalue because
    the table gives it a positive dimension. **The spectrum is the set equality.**
    **THIS BULLET REPLACES A FENCE THIS HEADER'S FIRST DRAFT CARRIED**, which read *that the wheel
    has no eigenvalue outside it does follow … and is not assembled here*. It was true of the
    draft and false of the file within the hour: the theorem it disclaimed was one application of
    a lemma the file already imported. `ERRATUM 94` keeps superseded text, and this note is that
    text's record — the fence was never shipped, and the reason it existed at all is worth one
    sentence: **“this follows but is not done” is a claim about cost, and unit 91's rule is that
    claims about cost get the cheapest instance run first.**

  WHAT IS **NOT** CLAIMED.

  * **THE HYPOTHESIS IS NOT DISCHARGED FOR ANY `N` OTHER THAN `4`.** It is false at `N = 3` and
    proved at `N = 4`; every other wheel is open. Deciding it in general is a quadratic irrational
    against a value of `2cos` at a rational multiple of `π` — `L102`'s library-blocked species,
    **not attempted and no cost offered** (`ERRATUM 194`, `ERRATUM 246`). The floating-point scan
    recorded on `UNLOCK_WATCHLIST` is labelled there as floating point and is not evidence.
  * **THE SPECTRUM EQUALITY IS IN THE EIGENVECTOR FORM AND NOT IN MATHLIB'S.**
    `wheel_spectrum_eq` is about `{lam | ∃ x ≠ 0, Q *ᵥ x = lam • x}`. **Nothing here connects it to
    `Matrix.IsHermitian.eigenvalues`**, whose indexing is the fence this cluster has met in every
    unit and has side-stepped in every unit, this one included. No `Set.range`, no
    `Polynomial.roots`, no `charpoly`.
  * **NOTHING ABOUT ANY OTHER `d`-REGULAR GRAPH.** Every statement here is about `cycleGraph
    (n + 3)` and its cone. **The estate's other graph families were CHECKED rather than
    dismissed**, and the first draft of this bullet was wrong about them. `awk` over the index for
    adjacency eigenvector statements returns families for the path (`PathAdjSpectrum`), the box
    and the box product (`BoxAdjSpectrum`, `BoxProdAdjSpectrum`), the complete graph
    (`CompleteSignlessSpectrum`) and the multipartite graph (`MultipartiteSpectrum`,
    `UnbalancedMultipartite`). The cone construction needs the base `d`-REGULAR, which the path,
    the box, the box product and the unbalanced multipartite graph are not. **But the complete
    graph IS regular — `LaplacianMultiplicityBound.degree_top` — and its zero-sum eigenvectors ARE
    in the estate**, so the cone route does apply there. What it would give is nothing new, since
    the cone over `⊤` is again `⊤` (obvious, and **not proved here or anywhere in the estate**) and
    `CompleteSignlessSpectrum` handles that case directly. So the cycle is the only base where
    this route says something the estate did not already have — **which is a fact about which
    families are regular and which cones are new, not about what the estate lacks.**
  * **NO CHARACTERISTIC POLYNOMIAL.** The route is eigenvectors and a pigeonhole throughout; no
    determinant, no factorisation, and none of the classical route's machinery appears.
  * **NOTHING ABOUT THE CASCADE, THE SPINE OR ANY WALL.**

  THE HYPOTHESES, READ OFF THE BINDERS. `hcol` is taken by eleven declarations and by nothing in
  the `Values`, `Arith` or `Separate` sections, which are unconditional. `rimVal_eq_one_iff` and
  `rimVal_ne_five` take `1 ≤ k` and `2 * k ≤ n + 3` because they are statements about the
  half-range; `rimVal_ne_one_of_ne` and `finrank_coneEig_rimVal` take the unfolded `k ≠ 0` and
  `k < n + 3` instead, and pay for it with a fold through `cos_reflect`.

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import CycleEigenvalueDistinct
import WheelHubCollision

namespace WheelTable

open SimpleGraph LaplacianSignless Matrix
open ConeSignlessSpectrum ConeMultiplicity ConeMultiplicityExact ConeTopEigen
open WheelSpectrum WheelMultiplicity ConeDimensionSum
open CycleEigenvalueDistinct

/-! ## The rim's values, and the half-range they are all attained on -/

section Values

/-- The wheel's rim value at frequency `k`: the cycle's adjacency eigenvalue shifted by the rim
degree `d + 1 = 3`. -/
noncomputable def rimVal (n k : ℕ) : ℝ :=
  3 + 2 * Real.cos (2 * Real.pi * (k : ℝ) / ((n + 3 : ℕ) : ℝ))

variable (n : ℕ)

/-- The rim values, as a `Finset`, indexed by the HALF-range. `rimVal_mem_rimSet` below is the
statement that nothing is lost. -/
noncomputable def rimSet : Finset ℝ :=
  (Finset.Icc 1 ((n + 3) / 2)).image (rimVal n)

theorem rimVal_injOn_half :
    Set.InjOn (rimVal n) {k : ℕ | 2 * k ≤ n + 3} := by
  intro a ha b hb hab
  refine eigenvalue_injOn_half (N := n + 3) (by omega) ha hb ?_
  have : (3 : ℝ) + 2 * Real.cos (2 * Real.pi * (a : ℝ) / ((n + 3 : ℕ) : ℝ))
      = 3 + 2 * Real.cos (2 * Real.pi * (b : ℝ) / ((n + 3 : ℕ) : ℝ)) := hab
  simpa using this

theorem card_rimSet : (rimSet n).card = (n + 3) / 2 := by
  rw [rimSet, Finset.card_image_of_injOn, Nat.card_Icc]
  · omega
  · intro a ha b hb hab
    simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
    exact rimVal_injOn_half n (by simpa using (by omega : 2 * a ≤ n + 3))
      (by simpa using (by omega : 2 * b ≤ n + 3)) hab

/-- **NOTHING IS LOST BY THE FOLD.** Every frequency other than `0` gives a value already in
`rimSet`, because `k` and `N - k` give the same cosine. -/
theorem rimVal_mem_rimSet {k : ℕ} (hk : k ≠ 0) (hkN : k < n + 3) :
    rimVal n k ∈ rimSet n := by
  rcases le_or_gt (2 * k) (n + 3) with h | h
  · exact Finset.mem_image_of_mem _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  · refine Finset.mem_image.2 ⟨n + 3 - k, Finset.mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
    unfold rimVal
    rw [cos_reflect (N := n + 3) (by omega) (by omega : k ≤ n + 3)]

end Values

/-! ## The arithmetic: the rim's lower bounds sum to `N - 1` -/

section Arith

variable (n : ℕ)

/-- The bottom of the rim's range is attained exactly at the half turn, which needs `N` even. -/
theorem rimVal_eq_one_iff {k : ℕ} (h1 : 1 ≤ k) (h2 : 2 * k ≤ n + 3) :
    rimVal n k = 1 ↔ 2 * k = n + 3 := by
  constructor
  · intro h
    have hc : Real.cos (2 * Real.pi * (k : ℝ) / ((n + 3 : ℕ) : ℝ)) = Real.cos Real.pi := by
      rw [Real.cos_pi]
      unfold rimVal at h
      linarith
    have hang := angle_mem_Icc (N := n + 3) (by omega) h2
    have hpi : Real.pi ∈ Set.Icc 0 Real.pi := ⟨Real.pi_pos.le, le_refl _⟩
    have heq := Real.injOn_cos hang hpi hc
    have hN : ((n + 3 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    -- `field_simp` clears the denominator AND cancels `π`, which it knows is non-zero.
    field_simp at heq
    exact_mod_cast heq
  · intro h
    unfold rimVal
    have hk : ((n + 3 : ℕ) : ℝ) = 2 * (k : ℝ) := by exact_mod_cast h.symm
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [hk, show 2 * Real.pi * (k : ℝ) / (2 * (k : ℝ)) = Real.pi by field_simp, Real.cos_pi]
    ring

/-- **AND THE SUM IS `N - 1` AT BOTH PARITIES.** Two at every frequency on the half-range, one at
the half turn when there is one — and an odd `N` has no half turn but one fewer frequency, so the
two cases agree. That coincidence is what makes the table a single statement. -/
theorem sum_rim_mult :
    ∑ k ∈ Finset.Icc 1 ((n + 3) / 2), (if 2 * k = n + 3 then 1 else 2) = n + 2 := by
  classical
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' (n + 3)
  · have hdiv : (n + 3) / 2 = m := by omega
    have hmem : m ∈ Finset.Icc 1 m := Finset.mem_Icc.2 ⟨by omega, le_refl _⟩
    have hrest : ∀ x ∈ (Finset.Icc 1 m).erase m,
        (if 2 * x = n + 3 then (1 : ℕ) else 2) = 2 := by
      intro x hx
      rw [Finset.mem_erase] at hx
      exact if_neg (by omega)
    rw [hdiv, ← Finset.sum_erase_add _ _ hmem, Finset.sum_congr rfl hrest,
      Finset.sum_const, Finset.card_erase_of_mem hmem, Nat.card_Icc, if_pos (by omega)]
    simp only [smul_eq_mul]
    omega
  · have hdiv : (n + 3) / 2 = m := by omega
    have hall : ∀ x ∈ Finset.Icc 1 m, (if 2 * x = n + 3 then (1 : ℕ) else 2) = 2 := by
      intro x _
      exact if_neg (by omega)
    rw [hdiv, Finset.sum_congr rfl hall, Finset.sum_const, Nat.card_Icc]
    simp only [smul_eq_mul]
    omega

end Arith

/-! ## The rim's range, and the two hub roots kept out of it -/

section Separate

variable (n : ℕ)

/-- The TOP of the rim's range is attained only at frequency `0`, which is not a rim frequency. -/
theorem rimVal_ne_five {k : ℕ} (h1 : 1 ≤ k) (h2 : 2 * k ≤ n + 3) : rimVal n k ≠ 5 := by
  intro h
  have hc : Real.cos (2 * Real.pi * (k : ℝ) / ((n + 3 : ℕ) : ℝ)) = Real.cos 0 := by
    rw [Real.cos_zero]
    unfold rimVal at h
    linarith
  have hang := angle_mem_Icc (N := n + 3) (by omega) h2
  have h0 : (0 : ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_refl _, Real.pi_pos.le⟩
  have heq := Real.injOn_cos hang h0 hc
  have hN : ((n + 3 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  -- `heq : 2 * π * ↑k / ↑(n + 3) = 0`, and the denominator is not the zero factor.
  have hnum : 2 * Real.pi * (k : ℝ) = 0 := (div_eq_zero_iff.1 heq).resolve_right hN
  have hk0 : (k : ℝ) = 0 := by
    rcases mul_eq_zero.1 hnum with h | h
    · linarith [Real.pi_pos]
    · exact h
  exact absurd (by exact_mod_cast hk0 : k = 0) (by omega)

/-- Every rim value lies in `[1, 5]`, off unit 91's `rim_value_mem_Icc`. -/
theorem rimSet_le_five {v : ℝ} (hv : v ∈ rimSet n) : v ≤ 5 := by
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hv
  exact (WheelHubCollision.rim_value_mem_Icc _).2

/-- The wheel's top clears the whole rim range, off unit 86. -/
theorem five_lt_hubRootPlus_wheel : (5 : ℝ) < hubRootPlus (n + 3) 2 := by
  have h := two_mul_add_one_lt_hubRootPlus (n + 3) 2 (by omega)
  norm_num at h
  exact h

theorem hubRootPlus_notMem_rimSet : hubRootPlus (n + 3) 2 ∉ rimSet n := by
  intro h
  exact absurd (rimSet_le_five n h) (not_le.2 (five_lt_hubRootPlus_wheel n))

/-- **UNIT 91'S HYPOTHESIS WAS SUFFICIENT AND NOT NECESSARY**, and at `d = 2` the sharp condition
`n(2d - 1) > 2d` reads `3N > 4`, which every wheel satisfies. So the lower root clears the bottom
of the rim range at EVERY wheel, with no hypothesis at all. -/
theorem one_lt_hubRootMinus_two : 1 < hubRootMinus (n + 3) 2 := by
  have hlt : Real.sqrt (hubDisc (n + 3) 2) < ((n + 3 : ℕ) : ℝ) + 3 := by
    rw [Real.sqrt_lt' (by positivity)]
    change (((n + 3 : ℕ) : ℝ) + 2 * 2 + 1) ^ 2 - 4 * (2 * 2 * ((n + 3 : ℕ) : ℝ)) < _
    have h3 : (3 : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by
      have : (3 : ℕ) ≤ n + 3 := by omega
      exact_mod_cast this
    nlinarith
  rw [hubRootMinus]
  push_cast at hlt ⊢
  linarith

end Separate

/-! ## The table -/

section Table

variable (n : ℕ)

/-- The multiplicity the table asserts: `1` at each hub root, `1` at the half turn, `2` at every
other rim value. -/
noncomputable def wheelMult : ℝ → ℕ := fun v =>
  if v = hubRootPlus (n + 3) 2 then 1
  else if v = hubRootMinus (n + 3) 2 then 1
  else if v = 1 then 1
  else 2

/-- Every eigenvalue the wheel is known to have. -/
noncomputable def wheelSet : Finset ℝ :=
  insert (hubRootPlus (n + 3) 2) (insert (hubRootMinus (n + 3) 2) (rimSet n))

theorem rimVal_eq_wheel (K : Fin (n + 3)) :
    rimVal n (K : ℕ) = 3 + 2 * Real.cos (2 * Real.pi * ((K : ℕ) : ℝ) / ((n : ℝ) + 3)) := by
  unfold rimVal
  push_cast
  ring

theorem rimVal_injOn_Icc : Set.InjOn (rimVal n) ↑(Finset.Icc 1 ((n + 3) / 2)) := by
  intro a ha b hb hab
  simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
  exact rimVal_injOn_half n (by simp only [Set.mem_setOf_eq]; omega)
    (by simp only [Set.mem_setOf_eq]; omega) hab

/-- Off the half-range too, the bottom value is reached only at the half turn. -/
theorem rimVal_ne_one_of_ne {k : ℕ} (hk : k ≠ 0) (hkN : k < n + 3) (hone : 2 * k ≠ n + 3) :
    rimVal n k ≠ 1 := by
  rcases le_or_gt (2 * k) (n + 3) with h | h
  · exact fun hv => hone ((rimVal_eq_one_iff n (by omega) h).1 hv)
  · intro hv
    have hfold : rimVal n (n + 3 - k) = rimVal n k := by
      unfold rimVal
      rw [cos_reflect (N := n + 3) (by omega) (by omega : k ≤ n + 3)]
    exact absurd ((rimVal_eq_one_iff n (by omega) (by omega)).1 (hfold.trans hv)) (by omega)

theorem wheelMult_hubRootPlus : wheelMult n (hubRootPlus (n + 3) 2) = 1 := by
  unfold wheelMult
  rw [if_pos rfl]

theorem wheelMult_hubRootMinus : wheelMult n (hubRootMinus (n + 3) 2) = 1 := by
  unfold wheelMult
  rw [if_neg (hubRootMinus_lt_hubRootPlus (n + 3) 2).ne, if_pos rfl]

theorem wheelMult_rimVal (hcol : hubRootMinus (n + 3) 2 ∉ rimSet n)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 ((n + 3) / 2)) :
    wheelMult n (rimVal n k) = if 2 * k = n + 3 then 1 else 2 := by
  have hmem : rimVal n k ∈ rimSet n := Finset.mem_image_of_mem _ hk
  rw [Finset.mem_Icc] at hk
  have h1 : 1 ≤ k := hk.1
  have h2 : 2 * k ≤ n + 3 := by omega
  have hp : rimVal n k ≠ hubRootPlus (n + 3) 2 := by
    intro h
    rw [h] at hmem
    exact hubRootPlus_notMem_rimSet n hmem
  have hm : rimVal n k ≠ hubRootMinus (n + 3) 2 := by
    intro h
    rw [h] at hmem
    exact hcol hmem
  unfold wheelMult
  rw [if_neg hp, if_neg hm]
  by_cases hone : 2 * k = n + 3
  · rw [if_pos ((rimVal_eq_one_iff n h1 h2).2 hone), if_pos hone]
  · rw [if_neg (fun hv => hone ((rimVal_eq_one_iff n h1 h2).1 hv)), if_neg hone]

/-- **THE LOWER BOUNDS ADD UP TO EXACTLY `card V + 1`.** One at each hub root, two at every rim
value except the half turn, one there — and that is `n + 4`, which is the whole space. -/
theorem sum_wheelMult (hcol : hubRootMinus (n + 3) 2 ∉ rimSet n) :
    ∑ v ∈ wheelSet n, wheelMult n v = n + 4 := by
  classical
  have hmne : hubRootMinus (n + 3) 2 ≠ hubRootPlus (n + 3) 2 :=
    (hubRootMinus_lt_hubRootPlus (n + 3) 2).ne
  have hpnotin : hubRootPlus (n + 3) 2 ∉ insert (hubRootMinus (n + 3) 2) (rimSet n) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h => hmne h.symm, hubRootPlus_notMem_rimSet n⟩
  rw [wheelSet, Finset.sum_insert hpnotin, Finset.sum_insert hcol,
    wheelMult_hubRootPlus, wheelMult_hubRootMinus, rimSet,
    Finset.sum_image (rimVal_injOn_Icc n),
    Finset.sum_congr rfl (fun k hk => wheelMult_rimVal n hcol hk), sum_rim_mult]
  omega

/-- Every value in `wheelSet` carries at least the multiplicity the table claims. -/
theorem lb_wheelMult (hcol : hubRootMinus (n + 3) 2 ∉ rimSet n) :
    ∀ v ∈ wheelSet n, wheelMult n v ≤ Module.finrank ℝ (coneEig (cycleGraph (n + 3)) v) := by
  intro v hv
  have hc : Fintype.card (Fin (n + 3)) = n + 3 := Fintype.card_fin _
  rw [wheelSet, Finset.mem_insert, Finset.mem_insert] at hv
  rcases hv with rfl | rfl | hv
  · rw [wheelMult_hubRootPlus, finrank_wheel_top n]
  · have h := one_le_finrank_coneEig_hubRootMinus (cycleGraph (n + 3)) (cycle_reg n)
    rw [hc] at h
    rw [wheelMult_hubRootMinus]
    exact h
  · obtain ⟨k, hkmem, rfl⟩ := Finset.mem_image.1 hv
    have hk := Finset.mem_Icc.1 hkmem
    have h1 : 1 ≤ k := hk.1
    have h2 : 2 * k ≤ n + 3 := by omega
    have hklt : k < n + 3 := by omega
    have hKne : (⟨k, hklt⟩ : Fin (n + 3)) ≠ 0 := by
      intro h
      exact absurd (congrArg Fin.val h) (by simpa using (by omega : k ≠ 0))
    have hKval : ((⟨k, hklt⟩ : Fin (n + 3)) : ℕ) = k := rfl
    rw [wheelMult_rimVal n hcol hkmem]
    by_cases hone : 2 * k = n + 3
    · rw [if_pos hone]
      have h := one_le_finrank_wheel_rim n ⟨k, hklt⟩ hKne
      rw [← rimVal_eq_wheel n ⟨k, hklt⟩, hKval] at h
      exact h
    · rw [if_neg hone]
      have hsin : Real.sin (2 * Real.pi * (((⟨k, hklt⟩ : Fin (n + 3)) : ℕ) : ℝ)
          / ((n : ℝ) + 3)) ≠ 0 := by
        intro hs
        rw [hKval, show ((n : ℝ) + 3) = ((n + 3 : ℕ) : ℝ) by push_cast; ring] at hs
        rcases Real.sin_eq_zero_iff_cos_eq.1 hs with h | h
        · exact rimVal_ne_five n h1 h2 (by unfold rimVal; rw [h]; norm_num)
        · exact hone ((rimVal_eq_one_iff n h1 h2).1 (by unfold rimVal; rw [h]; norm_num))
      have h := two_le_finrank_wheel_rim n ⟨k, hklt⟩ hKne hsin
      rw [← rimVal_eq_wheel n ⟨k, hklt⟩, hKval] at h
      exact h

/-- **THE TABLE.** Under the one hypothesis unit 91 showed is a genuine hypothesis, the pigeonhole
closes EVERY eigenvalue at once: the wheel's signless Laplacian has exactly the multiplicities
`wheelMult` names, and nothing else. -/
theorem finrank_coneEig_eq_wheelMult (hcol : hubRootMinus (n + 3) 2 ∉ rimSet n) :
    ∀ v ∈ wheelSet n, Module.finrank ℝ (coneEig (cycleGraph (n + 3)) v) = wheelMult n v := by
  have hc : Fintype.card (Fin (n + 3)) = n + 3 := Fintype.card_fin _
  refine finrank_coneEig_eq_of_sum_eq (cycleGraph (n + 3)) (lb_wheelMult n hcol) ?_
  rw [sum_wheelMult n hcol, hc]

end Table

/-! ## The table, read off at each value -/

section Readoff

variable (n : ℕ)

/-- **THE RIM'S EXHAUSTION, WHICH IS WHAT THE CHAIN HAS BEEN OWING SINCE UNIT 88**: the rim
multiplicity is EXACTLY two, not merely at least two, at every frequency other than `0` and the
half turn. -/
theorem finrank_coneEig_rimVal (hcol : hubRootMinus (n + 3) 2 ∉ rimSet n)
    {k : ℕ} (hk : k ≠ 0) (hkN : k < n + 3) (hone : 2 * k ≠ n + 3) :
    Module.finrank ℝ (coneEig (cycleGraph (n + 3)) (rimVal n k)) = 2 := by
  have hmem := rimVal_mem_rimSet n hk hkN
  have h := finrank_coneEig_eq_wheelMult n hcol (rimVal n k)
    (by rw [wheelSet]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem))
  rw [h]
  have hp : rimVal n k ≠ hubRootPlus (n + 3) 2 := by
    intro hv
    rw [hv] at hmem
    exact hubRootPlus_notMem_rimSet n hmem
  have hm : rimVal n k ≠ hubRootMinus (n + 3) 2 := by
    intro hv
    rw [hv] at hmem
    exact hcol hmem
  unfold wheelMult
  rw [if_neg hp, if_neg hm, if_neg (rimVal_ne_one_of_ne n hk hkN hone)]

/-- **AND AT THE HALF TURN IT IS EXACTLY ONE.** `N` even has one rim value whose eigenvector is
real up to scale, and `sin` vanishing there is exactly why unit 88's second vector was not
available — a hypothesis that turns out to be sharp. -/
theorem finrank_coneEig_rimVal_half (hcol : hubRootMinus (n + 3) 2 ∉ rimSet n)
    {k : ℕ} (hk : 2 * k = n + 3) :
    Module.finrank ℝ (coneEig (cycleGraph (n + 3)) (rimVal n k)) = 1 := by
  have hk0 : k ≠ 0 := by omega
  have hklt : k < n + 3 := by omega
  have hmem := rimVal_mem_rimSet n (k := k) hk0 hklt
  have h := finrank_coneEig_eq_wheelMult n hcol (rimVal n k)
    (by rw [wheelSet]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem))
  rw [h]
  have hp : rimVal n k ≠ hubRootPlus (n + 3) 2 := by
    intro hv
    rw [hv] at hmem
    exact hubRootPlus_notMem_rimSet n hmem
  have hm : rimVal n k ≠ hubRootMinus (n + 3) 2 := by
    intro hv
    rw [hv] at hmem
    exact hcol hmem
  unfold wheelMult
  rw [if_neg hp, if_neg hm,
    if_pos ((rimVal_eq_one_iff n (k := k) (by omega) (by omega)).2 hk)]

/-- **AND THE LOWER HUB ROOT IS SIMPLE.** Unit 83 gave `1 ≤`; this is the equality, and unit 91's
`N = 3` shows it is false without the hypothesis. -/
theorem finrank_coneEig_hubRootMinus_eq_one (hcol : hubRootMinus (n + 3) 2 ∉ rimSet n) :
    Module.finrank ℝ (coneEig (cycleGraph (n + 3)) (hubRootMinus (n + 3) 2)) = 1 := by
  have h := finrank_coneEig_eq_wheelMult n hcol (hubRootMinus (n + 3) 2)
    (by rw [wheelSet]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  rw [h, wheelMult_hubRootMinus]

end Readoff

/-! ## The hypothesis is satisfiable, and the second exact multiplicity in this chain -/

section Witness

theorem rimVal_one_one : rimVal 1 1 = 3 := by
  unfold rimVal
  rw [show 2 * Real.pi * ((1 : ℕ) : ℝ) / ((1 + 3 : ℕ) : ℝ) = Real.pi / 2 by push_cast; ring,
    Real.cos_pi_div_two]
  ring

theorem rimVal_one_two : rimVal 1 2 = 1 :=
  (rimVal_eq_one_iff 1 (k := 2) (by omega) (by omega)).2 (by omega)

theorem rimSet_one : rimSet 1 = {3, 1} := by
  rw [rimSet, show (1 + 3) / 2 = 2 from by norm_num,
    show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from by decide,
    Finset.image_insert, Finset.image_singleton, rimVal_one_one, rimVal_one_two]

theorem hubDisc_four_two : hubDisc 4 2 = 17 := by
  unfold hubDisc
  norm_num

theorem hubRootMinus_four_ne_three : hubRootMinus 4 2 ≠ 3 := by
  have h4 : (4 : ℝ) < Real.sqrt (hubDisc 4 2) := by
    rw [hubDisc_four_two]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  rw [hubRootMinus]
  intro h
  norm_num at h
  linarith

/-- **THE HYPOTHESIS IS NOT VACUOUS.** Unit 91 showed it FAILS at `N = 3`; here it HOLDS at
`N = 4`, so the table has content. Without this the whole section could have been a theorem about
an empty class, which is `ERRATUM 622`'s rule applied to the file's own hypothesis. -/
theorem hubRootMinus_notMem_rimSet_one : hubRootMinus 4 2 ∉ rimSet 1 := by
  rw [rimSet_one]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨hubRootMinus_four_ne_three, (one_lt_hubRootMinus_two 1).ne'⟩

/-- **AND SO THE SECOND EXACTLY COMPUTED MULTIPLICITY IN THIS CHAIN**, the first obtained from the
general table rather than by hand: the four-spoke wheel's signless Laplacian has the eigenvalue
`3` with multiplicity exactly `2`. -/
theorem finrank_coneEig_wheel_four_three :
    Module.finrank ℝ (coneEig (cycleGraph 4) 3) = 2 := by
  have h := finrank_coneEig_rimVal 1 hubRootMinus_notMem_rimSet_one (k := 1)
    (by omega) (by omega) (by omega)
  rw [rimVal_one_one] at h
  exact h

end Witness

/-! ## And so the spectrum is exactly `wheelSet` -/

section Spectrum

variable (n : ℕ)

theorem sum_finrank_eq_card (hcol : hubRootMinus (n + 3) 2 ∉ rimSet n) :
    ∑ v ∈ wheelSet n, Module.finrank ℝ (coneEig (cycleGraph (n + 3)) v)
      = Fintype.card (Option (Fin (n + 3))) := by
  rw [Finset.sum_congr rfl (fun v hv => finrank_coneEig_eq_wheelMult n hcol v hv),
    sum_wheelMult n hcol, Fintype.card_option, Fintype.card_fin]

/-- **NOTHING IS OUTSIDE THE TABLE.** The dimensions already fill the space, so a further
eigenvalue would need a dimension there is no room for. -/
theorem mem_wheelSet_of_eigen (hcol : hubRootMinus (n + 3) 2 ∉ rimSet n)
    {lam : ℝ} {x : Option (Fin (n + 3)) → ℝ} (hx0 : x ≠ 0)
    (hx : signlessLap (coneGraph (cycleGraph (n + 3))) *ᵥ x = lam • x) :
    lam ∈ wheelSet n :=
  HermitianFibreCount.mem_of_isEigenvalue_of_sum_eq
    (signlessLap_coneGraph_isHermitian (cycleGraph (n + 3))) (wheelSet n)
    (sum_finrank_eq_card n hcol) hx0 hx

/-- And every value in the table really is an eigenvalue, because the table gives it a positive
dimension. -/
theorem eigen_of_mem_wheelSet (hcol : hubRootMinus (n + 3) 2 ∉ rimSet n)
    {lam : ℝ} (hlam : lam ∈ wheelSet n) :
    ∃ x : Option (Fin (n + 3)) → ℝ, x ≠ 0 ∧
      signlessLap (coneGraph (cycleGraph (n + 3))) *ᵥ x = lam • x := by
  have hpos : 1 ≤ Module.finrank ℝ (coneEig (cycleGraph (n + 3)) lam) := by
    rw [finrank_coneEig_eq_wheelMult n hcol lam hlam]
    unfold wheelMult
    split_ifs <;> omega
  obtain ⟨x, hxmem, hx0⟩ := (Submodule.ne_bot_iff _).1 (Submodule.one_le_finrank_iff.1 hpos)
  exact ⟨x, hx0, (mem_coneEig (cycleGraph (n + 3))).1 hxmem⟩

/-- **THE SPECTRUM, AS A SET EQUALITY.** Under the one hypothesis, the wheel's signless Laplacian
has exactly the eigenvalues `wheelSet` lists and exactly the multiplicities `wheelMult` gives. -/
theorem wheel_spectrum_eq (hcol : hubRootMinus (n + 3) 2 ∉ rimSet n) :
    {lam : ℝ | ∃ x, x ≠ 0 ∧
        signlessLap (coneGraph (cycleGraph (n + 3))) *ᵥ x = lam • x} = ↑(wheelSet n) := by
  ext lam
  simp only [Set.mem_setOf_eq, Finset.mem_coe]
  exact ⟨fun ⟨x, hx0, hx⟩ => mem_wheelSet_of_eigen n hcol hx0 hx,
    fun h => eigen_of_mem_wheelSet n hcol h⟩

end Spectrum

end WheelTable
