import SignlessDoublingFails

/-!
# The sharpness condition, replaced by the arithmetic it was standing in for

`SignlessSharpBracket` got `#spec = 3s` from three conditions, the third being *every size less than
twice every other*, and `SignlessDoublingFails` showed the *exactly twice* half of it necessary and
left the *more than twice* half merely sufficient. **That half was never the real condition.** It is
a crude way of forcing a sum to be empty, and what the argument needs is only that the sum be small.

**Where it comes from.** At a part value `μ = N − nⱼ` the secular sum's terms are
`nᵢ / (nⱼ − 2nᵢ)`. Each index of the **same** size contributes exactly `−1`; each index with
`2nᵢ > nⱼ` contributes something `≤ 0`; and each index with `2nᵢ < nⱼ` contributes something
**positive**. `SignlessSharpBracket`'s third condition makes the last class empty. **The estimate
only needs the positive class to sum to less than `k_{nⱼ} − 1`**, where `k_{nⱼ}` is how many parts
share the size.

## What is proved

> **`partTerm`, `secularSum_at_part_value_eq`, `partTerm_of_eq`, `partTerm_nonpos`** — the terms
> named, and the two facts about them: `−1` at the same size, `≤ 0` off the small indices.
>
> **`secularSum_at_part_value_lt`** — **the estimate**: if no size is exactly twice `nⱼ` and the
> positive part sums to less than `k_{nⱼ} − 1`, then `secularSum (N − nⱼ) < −1`. Splitting on
> `nᵢ = nⱼ` and then bounding the rest by the small indices, the discarded terms being non-positive.
>
> **`card_spectrum_eq_three_mul'`** — **the sharp count, refactored onto what it actually uses**:
> parts of at least two vertices, every size at least twice, no size exactly twice another, **and no
> part value a secular root**. `SignlessSharpBracket`'s theorem is this one with the last hypothesis
> discharged by its third condition; this one takes it as given, so any argument for it will do.
>
> **`P2299`, `not_spread_P2299`, `bound_P2299`, `card_spectrum_P2299`** — **and the weakening
> reaches a graph the old condition does not.** `K_{2,2,9,9}`: `9 > 2 · 2`, so
> `SignlessSharpBracket`'s third condition **fails** (`not_spread_P2299`, by `decide`), and the
> positive part is `2/5 + 2/5 = 4/5 < 1` all the same, so its signless Laplacian has **exactly six**
> distinct eigenvalues.

## What is NOT here

* **NO CHARACTERISATION.** The positive-part bound is **sufficient** and there is no claim that it
  is necessary. It **is** sharp at the known counterexample — at `K_{1,3,3}` the positive part is
  exactly `1/(3 − 2) = 1` and `k₃ − 1 = 1`, so the bound fails **by equality** and the sum lands
  exactly on `−1`. Whether every failure of the bound costs sharpness is **open, not attempted**
  (`ERRATUM 246`).
* **THE OLD THEOREM IS NOT REPLACED.** `SignlessSharpBracket.card_spectrum_eq_three_mul` stays as it
  is, with its own hypotheses and its own witness; this file adds a second route to the same
  conclusion and does not edit the first.
* **NO MULTIPLICITIES, NO ROOT VALUES, NOTHING OVER `ℂ`.**
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances; the estimate takes `∀ i, Nonempty (V i)`, one index `j`, that no size is exactly twice
`nⱼ`, and the bound, and **omits both `DecidableEq`s in §1**. **No mass, no propagator, no metric.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SecularPositivePart

open Matrix Finset SimpleGraph LaplacianSignless SignlessSpectrumTrichotomy
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-- The terms of the secular sum at the part value `N - n_j`, as a function of the index. -/
noncomputable def partTerm (V : ι → Type*) [∀ i, Fintype (V i)] (j i : ι) : ℝ :=
  (Fintype.card (V i) : ℝ) / ((Fintype.card (V j) : ℝ) - 2 * Fintype.card (V i))

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem secularSum_at_part_value_eq (j : ι) :
    secularSum (V := V) ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V j))
      = ∑ i, partTerm V j i := by
  simp only [secularSum, partTerm]
  exact Finset.sum_congr rfl fun i _ => by ring_nf

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- At an index of the same size the term is exactly `-1`. -/
theorem partTerm_of_eq (hne : ∀ i, Nonempty (V i)) {j i : ι}
    (h : Fintype.card (V i) = Fintype.card (V j)) : partTerm V j i = -1 := by
  have hpos : (0 : ℝ) < Fintype.card (V j) := by
    have := Fintype.card_pos_iff.mpr (hne j)
    exact_mod_cast this
  rw [partTerm, h]
  field_simp
  norm_num

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- Off the small indices the term is non-positive. -/
theorem partTerm_nonpos {j i : ι} (h : ¬ 2 * Fintype.card (V i) < Fintype.card (V j))
    (hne2 : 2 * Fintype.card (V i) ≠ Fintype.card (V j)) : partTerm V j i ≤ 0 := by
  have hlt : (Fintype.card (V j) : ℝ) - 2 * Fintype.card (V i) < 0 := by
    have : Fintype.card (V j) < 2 * Fintype.card (V i) := by omega
    have : (Fintype.card (V j) : ℝ) < 2 * Fintype.card (V i) := by exact_mod_cast this
    linarith
  exact div_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_lt hlt)

/-! ## 2. So a bound on the positive part decides the part value -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem secularSum_at_part_value_lt (hne : ∀ i, Nonempty (V i)) (j : ι)
    (hne2 : ∀ i, 2 * Fintype.card (V i) ≠ Fintype.card (V j))
    (hbound : ∑ i ∈ Finset.univ.filter
        (fun i => 2 * Fintype.card (V i) < Fintype.card (V j)), partTerm V j i
      < (Fintype.card {k : ι // Fintype.card (V k) = Fintype.card (V j)} : ℝ) - 1) :
    secularSum (V := V) ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V j)) < -1 := by
  classical
  set E := Finset.univ.filter (fun i => Fintype.card (V i) = Fintype.card (V j)) with hE
  set A := Finset.univ.filter (fun i => ¬ Fintype.card (V i) = Fintype.card (V j)) with hA
  set Sm := Finset.univ.filter
    (fun i => 2 * Fintype.card (V i) < Fintype.card (V j)) with hSm
  have hjpos : 0 < Fintype.card (V j) := Fintype.card_pos_iff.mpr (hne j)
  have hSmA : Sm ⊆ A := by
    intro i hi
    rw [hSm, Finset.mem_filter] at hi
    rw [hA, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun hcon => by omega⟩
  have hsplit : ∑ i, partTerm V j i = ∑ i ∈ E, partTerm V j i + ∑ i ∈ A, partTerm V j i :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm
  have hEsum : ∑ i ∈ E, partTerm V j i = -(E.card : ℝ) := by
    rw [Finset.sum_congr rfl (fun i hi => partTerm_of_eq hne
      ((Finset.mem_filter.mp hi).2)), Finset.sum_const, nsmul_eq_mul]
    ring
  have hEcard : E.card = Fintype.card {k : ι // Fintype.card (V k) = Fintype.card (V j)} := by
    rw [hE, ← Fintype.card_subtype]
  have hAsum : ∑ i ∈ A, partTerm V j i ≤ ∑ i ∈ Sm, partTerm V j i := by
    have hsd := Finset.sum_sdiff (f := fun i => partTerm V j i) hSmA
    have hnp : ∑ i ∈ A \ Sm, partTerm V j i ≤ 0 := by
      refine Finset.sum_nonpos fun i hi => ?_
      simp only [Finset.mem_sdiff, hSm, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact partTerm_nonpos hi.2 (hne2 i)
    linarith
  rw [secularSum_at_part_value_eq, hsplit, hEsum, hEcard]
  linarith

/-! ## 3. The sharp count, refactored onto what it actually uses -/

theorem card_spectrum_eq_three_mul' (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι)
    (hsize : ∀ i, 2 ≤ Fintype.card (V i))
    (htwice : ∀ i, 2 ≤ Fintype.card {j : ι // Fintype.card (V j) = Fintype.card (V i)})
    (hnodouble : ∀ i j : ι, Fintype.card (V i) ≠ 2 * Fintype.card (V j))
    (hroot : ∀ j : ι, secularSum (V := V)
      ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V j)) ≠ -1) :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen V μ)
      ∧ S.card = 3 * (Finset.univ.image (fun i : ι => Fintype.card (V i))).card := by
  classical
  obtain ⟨S, hS, -, hhigh⟩ := exists_spectrum_bracket (V := V) hne hι
  obtain ⟨R, hRcard, hRchar, hRe⟩ := SecularRootsOffPoles.exists_roots_finset_eigen
    (V := V) hne hι
  refine ⟨S, hS, ?_⟩
  set N : ℝ := (Fintype.card (Σ i, V i) : ℝ) with hN
  set sizes := Finset.univ.image (fun i : ι => Fintype.card (V i)) with hsizes
  have hinjP : Function.Injective (fun n : ℕ => N - n) := by
    intro a b h
    have : (a : ℝ) = b := by simpa using h
    exact_mod_cast this
  have hinjQ : Function.Injective (fun n : ℕ => N - 2 * n) := by
    intro a b h
    have h2 : (2 : ℝ) * a = 2 * b := by simp only at h; linarith
    have : (a : ℝ) = b := by linarith
    exact_mod_cast this
  set P := sizes.image (fun n : ℕ => N - n) with hPdef
  set Q := sizes.image (fun n : ℕ => N - 2 * n) with hQdef
  have hPcard : P.card = sizes.card := Finset.card_image_of_injective _ hinjP
  have hQcard : Q.card = sizes.card := Finset.card_image_of_injective _ hinjQ
  have hPQ : Disjoint P Q := by
    rw [Finset.disjoint_left]
    rintro μ hμP hμQ
    simp only [hPdef, hQdef, hsizes, Finset.mem_image, Finset.mem_univ, true_and] at hμP hμQ
    obtain ⟨a, ⟨i, rfl⟩, rfl⟩ := hμP
    obtain ⟨b, ⟨k, rfl⟩, hb⟩ := hμQ
    have : (Fintype.card (V i) : ℝ) = 2 * Fintype.card (V k) := by linarith
    exact hnodouble i k (by exact_mod_cast this)
  have hQR : Disjoint Q R := by
    rw [Finset.disjoint_left]
    rintro μ hμQ hμR
    simp only [hQdef, hsizes, Finset.mem_image, Finset.mem_univ, true_and] at hμQ
    obtain ⟨a, ⟨i, rfl⟩, rfl⟩ := hμQ
    exact ((hRchar _).mp hμR).2 i (by ring)
  have hPR : Disjoint P R := by
    rw [Finset.disjoint_left]
    rintro μ hμP hμR
    simp only [hPdef, hsizes, Finset.mem_image, Finset.mem_univ, true_and] at hμP
    obtain ⟨a, ⟨i, rfl⟩, rfl⟩ := hμP
    exact hroot i ((hRchar _).mp hμR).1
  have hsub : P ∪ Q ∪ R ⊆ S := by
    intro μ hμ
    rw [Finset.mem_union, Finset.mem_union] at hμ
    rcases hμ with (h | h) | h
    · simp only [hPdef, hsizes, Finset.mem_image, Finset.mem_univ, true_and] at h
      obtain ⟨a, ⟨i, rfl⟩, rfl⟩ := h
      exact (hS _).mpr (SignlessDoubleBracket.isEigen_part_value hne i (hsize i)
        (SignlessDoubleBracket.card_ne_total i (hsize i) (htwice i)))
    · simp only [hQdef, hsizes, Finset.mem_image, Finset.mem_univ, true_and] at h
      obtain ⟨a, ⟨i, rfl⟩, rfl⟩ := h
      have htw : 2 ≤ Fintype.card {j : ι // 2 * Fintype.card (V j) = 2 * Fintype.card (V i)} := by
        have hequiv : {j : ι // 2 * Fintype.card (V j) = 2 * Fintype.card (V i)}
            ≃ {j : ι // Fintype.card (V j) = Fintype.card (V i)} :=
          Equiv.subtypeEquivRight (fun j => by constructor <;> intro h <;> omega)
        rw [Fintype.card_congr hequiv]
        exact htwice i
      exact (hS _).mpr (SignlessDoubleBracket.isEigen_pole hne i htw (fun j => hnodouble j i))
    · exact (hS _).mpr (hRe μ h)
  have hdisjU : Disjoint (P ∪ Q) R := Finset.disjoint_union_left.mpr ⟨hPR, hQR⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisjU, Finset.card_union_of_disjoint hPQ,
    hPcard, hQcard, hRcard] at hcard
  omega

/-! ## 4. And it reaches a graph the strict condition does not -/

/-- Two parts of two and two parts of nine: `9 > 2 · 2`, so `SignlessSharpBracket`'s third condition
**fails**, and the positive part is `2/5 + 2/5 = 4/5 < 1` all the same. -/
abbrev P2299 : Fin 4 → Type := fun i => Fin (2 + 7 * (i.1 / 2))

theorem card_P2299 (i : Fin 4) : Fintype.card (P2299 i) = 2 + 7 * (i.1 / 2) := by
  simp [P2299]

theorem sizes_P2299 :
    (Finset.univ.image (fun i : Fin 4 => Fintype.card (P2299 i))).card = 2 := by decide

theorem not_spread_P2299 :
    ¬ (∀ i k : Fin 4, Fintype.card (P2299 k) < 2 * Fintype.card (P2299 i)) := by decide

theorem bound_P2299 (j : Fin 4) :
    ∑ i ∈ Finset.univ.filter
        (fun i => 2 * Fintype.card (P2299 i) < Fintype.card (P2299 j)),
        partTerm P2299 j i
      < (Fintype.card {k : Fin 4 // Fintype.card (P2299 k) = Fintype.card (P2299 j)} : ℝ) - 1 := by
  have hk : Fintype.card {k : Fin 4 // Fintype.card (P2299 k) = Fintype.card (P2299 j)} = 2 := by
    fin_cases j <;> decide
  rw [hk, Finset.sum_filter]
  fin_cases j <;>
    · simp only [partTerm, card_P2299, Fin.sum_univ_four]
      norm_num

/-- **AND ITS SPECTRUM IS EXACTLY `3s = 6`**, where `SignlessSharpBracket` cannot reach it. -/
theorem card_spectrum_P2299 :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen P2299 μ) ∧ S.card = 6 := by
  obtain ⟨S, hS, hcard⟩ := card_spectrum_eq_three_mul' (V := P2299) (fun _ => ⟨0⟩) ⟨0⟩
    (by decide) (by decide) (by decide)
    (fun j => by
      have h := secularSum_at_part_value_lt (V := P2299) (fun _ => ⟨0⟩) j
        (by fin_cases j <;> decide) (bound_P2299 j)
      linarith)
  rw [sizes_P2299] at hcard
  exact ⟨S, hS, by omega⟩

end SecularPositivePart
