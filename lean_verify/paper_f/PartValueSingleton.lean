import SignlessP1122Exact

/-!
# A part value is an eigenvalue exactly when its part has two vertices

`SignlessP1122Exact` found the first graph in this chain whose spectrum is **smaller** than the
trichotomy's cover: at `K_{1,1,2,2}` the part value `N − 1` is a candidate and is not an
eigenvalue. Its `§6` asked the general question — *is a part value attached to a part of size two
or more ever missed?* — and named the answer as untouched. **It is never missed, and a part value
attached to a singleton is always missed.** Both halves are here, and together they are a
characterisation.

**THE ARITHMETIC IS SMALLER THAN THE QUESTION LOOKS.** At `μ = N − 1` the secular sum's terms are
`nᵢ / (1 − 2nᵢ)`, and every one of them is **below `−1/2`** — a one-line calculation, because
`nᵢ/(1 − 2nᵢ) + 1/2 = 1/(2(1 − 2nᵢ))` and the denominator is negative. With two parts or more the
sum is therefore below `−1`, so `N − 1` is **never** a secular root, and the eigenspace at a part
value of size `n` has dimension `k_n · (n − 1)`, which at `n = 1` is zero.

## What is proved

**`term_lt`, `secularSum_sub_one_lt`** — every term at `N − 1` is below `−1/2`, so with at least
two parts the sum is below `−1`. No hypothesis on the sizes beyond non-emptiness.

**`not_isEigen_sub_one`** — `N − 1` is **not an eigenvalue**, for any complete multipartite graph
with at least two non-empty parts. It does not even need a part of size one: without one the value
is not a part value and the statement is still true and still worth having, because the trichotomy
lists candidates by size and this rules the value out once and for all.

**`part_value_isEigen_iff`** — **the characterisation**: with at least two non-empty parts, the
part value `N − nⱼ` is an eigenvalue **iff** `2 ≤ nⱼ`. The forward direction is the theorem above;
the backward direction is `SignlessDoubleBracket.isEigen_part_value`, which has been in the chain
since entry 194 and whose `2 ≤ nⱼ` hypothesis nobody had asked about.

**`card_spectrum_lt_three_mul_of_singleton`** — **and the upper bound improves for a whole class
of graphs**: if any part is a singleton, `#spec < 3s`. `SignlessDoublingFails` proved the same
conclusion from a **size coincidence** `nⱼ = 2nᵢ`; this is an independent and much commoner
sufficient condition, and the two together cover both graphs the chain has found below the
bracket.

**`lt_three_mul_P1122`, `lt_three_mul_Part133`** — both of them, by the new route. `K_{1,1,2,2}`
had it from the coincidence `2 = 2 · 1`; `K_{1,3,3}` did **not** have it from anything — entry 180
computed its spectrum to be `{1, 4, 9}`, three values against `3s = 6`, and no general statement in
the chain predicted that. Now one does.

## What is NOT here

* **NOTHING ABOUT POLES.** `pole_isEigen_iff` already characterises them — a pole off the part
  values is an eigenvalue iff at least two parts share its size — and this file does not use it or
  combine the two into a description of the whole cover. The combination is the obvious next step
  and is **not taken**, because the coincidence cases (a pole that is also a part value) are what
  make it hard and nothing here touches them. Not attempted (`ERRATUM 246`).
* **NO EXACT COUNT FOR ANY NEW GRAPH.** The bound is `< 3s`, not a value; `K_{1,3,3}` and
  `K_{1,1,2,2}` have exact counts from their own units and no third graph gains one here.
* **NO MULTIPLICITIES, NO ROOT VALUES, NOTHING OVER `ℂ`, NO WALL MOVES, NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `∀ i, Nonempty (V i)` and `2 ≤ card ι`
throughout — the second is what makes `N ≠ 1` and gives the sum its second term — plus a part of
size one where the statement is about one. **Both `DecidableEq`s are omitted on the two arithmetic
lemmas.** No mass, no propagator, no metric.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace PartValueSingleton

open Matrix Finset SimpleGraph LaplacianSignless SignlessSpectrumTrichotomy
open SignlessDoubleBracket SignlessDoublingFails SecularRootExact SecularRootCount
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. Every term at `N - 1` is below `-1/2` -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem term_lt (hne : ∀ i, Nonempty (V i)) (i : ι) :
    (Fintype.card (V i) : ℝ)
        / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)
            - ((Fintype.card (Σ i, V i) : ℝ) - 1)) < -(1 / 2) := by
  have h1 : 1 ≤ Fintype.card (V i) := Fintype.card_pos_iff.mpr (hne i)
  have h1' : (1 : ℝ) ≤ Fintype.card (V i) := by exact_mod_cast h1
  rw [show (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)
      - ((Fintype.card (Σ i, V i) : ℝ) - 1) = 1 - 2 * Fintype.card (V i) from by ring]
  rw [div_lt_iff_of_neg (show (1 : ℝ) - 2 * Fintype.card (V i) < 0 by linarith)]
  linarith

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **`N - 1` IS NEVER A SECULAR ROOT** once there are two parts. -/
theorem secularSum_sub_one_lt (hne : ∀ i, Nonempty (V i)) (htwo : 2 ≤ Fintype.card ι) :
    secularSum (V := V) ((Fintype.card (Σ i, V i) : ℝ) - 1) < -1 := by
  classical
  have hb : ∑ i : ι, (Fintype.card (V i) : ℝ)
        / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)
            - ((Fintype.card (Σ i, V i) : ℝ) - 1))
      < ∑ _i : ι, (-(1 / 2) : ℝ) := by
    refine Finset.sum_lt_sum_of_nonempty ?_ (fun i _ => term_lt hne i)
    exact Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega))
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at hb
  have hc : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast htwo
  have heq : secularSum (V := V) ((Fintype.card (Σ i, V i) : ℝ) - 1)
      = ∑ i : ι, (Fintype.card (V i) : ℝ)
        / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)
            - ((Fintype.card (Σ i, V i) : ℝ) - 1)) := rfl
  rw [heq]
  nlinarith [hb]

/-! ## 2. So it is not an eigenvalue -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem one_lt_total (hne : ∀ i, Nonempty (V i)) (htwo : 2 ≤ Fintype.card ι) :
    1 < Fintype.card (Σ i, V i) := by
  classical
  rw [Fintype.card_sigma]
  calc 1 < Fintype.card ι := by omega
    _ = ∑ _i : ι, 1 := by simp
    _ ≤ ∑ i, Fintype.card (V i) :=
        Finset.sum_le_sum fun i _ => Fintype.card_pos_iff.mpr (hne i)

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem card_part_lt_total (hne : ∀ i, Nonempty (V i)) (htwo : 2 ≤ Fintype.card ι) (j : ι) :
    Fintype.card (V j) < Fintype.card (Σ i, V i) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k : ι, k ≠ j := Fintype.exists_ne_of_one_lt_card (by omega) j
  rw [Fintype.card_sigma]
  have hsplit := Finset.add_sum_erase Finset.univ (fun i => Fintype.card (V i))
    (Finset.mem_univ j)
  have hk' : k ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩
  have hkle := Finset.single_le_sum (f := fun i => Fintype.card (V i))
    (fun i _ => Nat.zero_le _) hk'
  have hkpos := Fintype.card_pos_iff.mpr (hne k)
  simp only at hsplit hkle
  omega

/-- **THE PART VALUE OF A SINGLETON IS NEVER AN EIGENVALUE.** -/
theorem not_isEigen_sub_one (hne : ∀ i, Nonempty (V i)) (htwo : 2 ≤ Fintype.card ι) :
    ¬ IsEigen V ((Fintype.card (Σ i, V i) : ℝ) - 1) := by
  have hone : ((Fintype.card (Σ i, V i) : ℝ) - ((1 : ℕ) : ℝ))
      = (Fintype.card (Σ i, V i) : ℝ) - 1 := by norm_num
  have hfr := finrank_signless_size_secular_zero (V := V) (n := 1) (by norm_num)
    (by have := one_lt_total (V := V) hne htwo; omega) hne
    (by intro i; omega)
    (by rw [hone]; exact ne_of_lt (secularSum_sub_one_lt (V := V) hne htwo))
  rw [hone] at hfr
  intro hx
  have hpos := (isEigenvector_iff_finrank_pos
    (signlessLap (completeMultipartiteGraph V)) ((Fintype.card (Σ i, V i) : ℝ) - 1)).mp hx
  rw [hfr] at hpos
  omega

/-! ## 3. The characterisation -/

/-- **A PART VALUE IS AN EIGENVALUE EXACTLY WHEN ITS PART HAS TWO VERTICES.** -/
theorem part_value_isEigen_iff (hne : ∀ i, Nonempty (V i)) (htwo : 2 ≤ Fintype.card ι) (j : ι) :
    IsEigen V ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V j))
      ↔ 2 ≤ Fintype.card (V j) := by
  constructor
  · intro hx
    by_contra hlt
    have h1 : Fintype.card (V j) = 1 := by
      have := Fintype.card_pos_iff.mpr (hne j); omega
    rw [h1] at hx
    exact not_isEigen_sub_one (V := V) hne htwo (by exact_mod_cast hx)
  · intro h2
    exact isEigen_part_value (V := V) hne j h2
      (Nat.ne_of_lt (card_part_lt_total (V := V) hne htwo j))

/-! ## 4. And the bracket's top improves for every graph with a singleton part -/

/-- **A SINGLETON PART PUTS THE SPECTRUM BELOW `3s`**, by a route independent of
`SignlessDoublingFails`'s size coincidence. -/
theorem card_spectrum_lt_three_mul_of_singleton (hne : ∀ i, Nonempty (V i))
    (htwo : 2 ≤ Fintype.card ι) {j : ι} (h1 : Fintype.card (V j) = 1) :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen V μ)
      ∧ S.card < 3 * (Finset.univ.image (fun k : ι => Fintype.card (V k))).card := by
  classical
  have hι : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨S, hS, -, -⟩ := exists_spectrum_bracket (V := V) hne hι
  obtain ⟨R, hRcard, hR⟩ := exists_roots_finset_exact (V := V) hne hι
  refine ⟨S, hS, ?_⟩
  set N : ℝ := (Fintype.card (Σ i, V i) : ℝ) with hN
  set sizes := Finset.univ.image (fun k : ι => Fintype.card (V k)) with hsizes
  set P := (partValues V).erase (N - 1) with hP
  have hmem : (N - 1) ∈ partValues V :=
    (mem_partValues_iff (V := V) _).mpr ⟨j, by rw [h1, Nat.cast_one]⟩
  have hPcard : P.card = sizes.card - 1 := by
    rw [hP, Finset.card_erase_of_mem hmem, card_partValues_eq_card_sizes (V := V)]
  have hspos : 0 < sizes.card := Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _
    (Finset.mem_univ j)⟩
  have hsub : S ⊆ P ∪ poles V ∪ R := by
    intro μ hμ
    have hx : IsEigen V μ := (hS μ).mp hμ
    by_cases hval : ∃ k, (N - Fintype.card (V k)) = μ
    · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      refine Finset.mem_erase.mpr ⟨?_, (mem_partValues_iff (V := V) _).mpr hval⟩
      rintro rfl
      exact not_isEigen_sub_one (V := V) hne htwo hx
    by_cases hpole : ∃ k, (N - 2 * Fintype.card (V k)) = μ
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ ((mem_poles_iff (V := V) _).mpr hpole))
    · rcases eigenvalue_trichotomy (V := V) hne (Classical.choice hι) hx with h | h | h
      · exact absurd h hval
      · exact absurd h hpole
      · refine Finset.mem_union_right _ ((hR μ).mpr ⟨h, fun k hk => ?_⟩)
        exact hpole ⟨k, by linarith⟩
  have hQcard : (poles V).card = sizes.card := card_poles_eq_card_sizes (V := V)
  have hle1 : (P ∪ poles V ∪ R).card ≤ (P ∪ poles V).card + R.card := Finset.card_union_le _ _
  have hle2 : (P ∪ poles V).card ≤ P.card + (poles V).card := Finset.card_union_le _ _
  have := Finset.card_le_card hsub
  omega

/-! ## 5. Both graphs the chain has found below the bracket -/

theorem lt_three_mul_P1122 :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen P1122 μ)
      ∧ S.card < 3 * (Finset.univ.image (fun k : Fin 4 => Fintype.card (P1122 k))).card :=
  card_spectrum_lt_three_mul_of_singleton (V := P1122) (fun _ => ⟨0⟩) (by decide)
    (j := 0) (by decide)

theorem lt_three_mul_Part133 :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen SecularRootAtPartValue.Part133 μ)
      ∧ S.card < 3 * (Finset.univ.image
          (fun k : Fin 3 => Fintype.card (SecularRootAtPartValue.Part133 k))).card :=
  card_spectrum_lt_three_mul_of_singleton (V := SecularRootAtPartValue.Part133)
    (fun _ => ⟨0⟩) (by decide) (j := 0) (by decide)

end PartValueSingleton
