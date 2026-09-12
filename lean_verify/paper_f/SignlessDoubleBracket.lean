import SignlessBracketAttained

/-!
# The bracket's lower bound doubles, under three arithmetic conditions on the part sizes

`SignlessSpectrumTrichotomy` put `Q`'s distinct eigenvalues between `s` and `3s`, and
`SignlessBracketAttained` showed the upper bound tight at `K_{2,2}`. **The lower bound is the weak
end**: it counts the secular roots, one above each pole, and ignores the other two families
entirely. **Under three conditions on the part sizes it doubles**, and the conditions are arithmetic
rather than spectral — they can be checked by looking at a list of numbers.

**The three conditions, and each is used exactly once.**

* **every part has at least two vertices** — a part value `N − n` has multiplicity
  `kₙ·(n − 1) + …`, which is positive as soon as `n ≥ 2`, and is **zero** at `n = 1` unless the
  value is also a secular root. So this is what makes the part-value family non-empty;
* **every size occurs at least twice** — `pole_isEigen_iff` says a pole off the part values is an
  eigenvalue **exactly** when two parts have half its `n`. So this is what makes the pole family
  non-empty, and it is a biconditional, so the condition is not merely sufficient;
* **no size is twice another** — a pole `N − 2nᵢ` equals a part value `N − nⱼ` exactly when
  `nⱼ = 2nᵢ`. So this is what makes the two families disjoint.

## What is proved

> **`isEigen_part_value`** — a part value of a size that occurs is an eigenvalue, from
> `UnbalancedMultipartiteSecular.finrank_signless_size_eq` with the multiplicity bounded below by
> `1 · (n − 1)`.
>
> **`two_mul_card_le`, `card_ne_total`** — two parts of the same size force `2n ≤ N`, hence `n ≠ N`,
> which is the side condition the multiplicity theorem takes and which the *twice* hypothesis
> supplies for free. Summing over `{j₁, j₂}` and nothing else.
>
> **`isEigen_pole`** — a pole whose size occurs twice, and which is off the part values, is an
> eigenvalue. `pole_isEigen_iff` with the cast bookkeeping done.
>
> **`two_s_le_card_spectrum`** — **THE BOUND**: `2s ≤ #spec`. The `s` part values and the `s` poles
> are two injective images of the size set, disjoint by the third condition, both inside the
> spectrum.
>
> **`P2233`, `four_le_card_spectrum_P2233`** — **and the hypotheses are satisfiable**:
> `K_{2,2,3,3}` — two parts of two and two of three — meets all three by `decide`, so its signless
> Laplacian has **at least four** distinct eigenvalues, against the trichotomy's ceiling of six.
> Stated because a theorem whose hypotheses nobody has exhibited is a hypothesis
> (`IndefiniteCoupling`'s standard, and this estate's).

## What is NOT here

* **`3s` IS NOT REACHED, AND THE MISSING STEP IS EXACTLY ONE.** The bracket's own lower bound of `s`
  is the **secular roots**, one above each pole. Adding them to the `2s` above would give `3s` — and
  needs those `s` roots shown distinct from the `s` part values and the `s` poles. The location
  results (`SecularRootLocation`, `SecularRootSeparation`) place the roots between consecutive
  poles, which looks like enough, and **assembling it is not attempted here**
  (`ERRATUM 246`). So `K_{2,2,3,3}` is bracketed `4 ≤ #spec ≤ 6` and not resolved.
* **THE THREE CONDITIONS ARE SUFFICIENT AND NOT SHOWN NECESSARY.** `K_{2,2}` violates the third —
  its only size is `2` and `2 ≠ 2·2`, so in fact it does not; but it has one size occurring twice
  and satisfies all three, and its bound `2s = 2` is far below its actual `3`. **The conditions buy
  a general lower bound, not a sharp one**, and which graphs are sharp is the open question above.
* **NO MULTIPLICITIES AND NO CHARACTERISTIC POLYNOMIAL.** The count is of **distinct** eigenvalues
  throughout.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances, `∀ i, Nonempty (V i)`, `Nonempty ι`, and the three arithmetic conditions; the two
counting lemmas of §2 omit the `DecidableEq` on the fibres, which they do not use. **No mass, no
propagator, no metric.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessDoubleBracket

open Matrix Finset SimpleGraph LaplacianSignless SignlessSpectrumTrichotomy
open UnbalancedMultipartite UnbalancedMultipartiteSecular

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. A part value of a size that occurs is an eigenvalue -/

theorem isEigen_part_value (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (h2 : 2 ≤ Fintype.card (V i₀))
    (hlt : Fintype.card (V i₀) ≠ Fintype.card (Σ i, V i)) :
    IsEigen V ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i₀)) := by
  rw [IsEigen, UnbalancedMultipartiteSecularEquation.isEigenvector_iff_finrank_pos,
    finrank_signless_size_eq (V := V) (n := Fintype.card (V i₀)) (by omega) hlt hne]
  have hk : 1 ≤ Fintype.card {i : ι // Fintype.card (V i) = Fintype.card (V i₀)} :=
    Fintype.card_pos_iff.mpr ⟨⟨i₀, rfl⟩⟩
  have : 1 ≤ Fintype.card (V i₀) - 1 := by omega
  calc 0 < 1 * 1 := by norm_num
    _ ≤ Fintype.card {i : ι // Fintype.card (V i) = Fintype.card (V i₀)}
          * (Fintype.card (V i₀) - 1) := Nat.mul_le_mul hk this
    _ ≤ _ := Nat.le_add_right _ _

/-! ## 2. Two parts of the same size force that size below `N` -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem two_mul_card_le (i₀ : ι)
    (htwice : 2 ≤ Fintype.card {j : ι // Fintype.card (V j) = Fintype.card (V i₀)}) :
    2 * Fintype.card (V i₀) ≤ Fintype.card (Σ i, V i) := by
  classical
  obtain ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩, hne12⟩ := Fintype.exists_pair_of_one_lt_card htwice
  have hj : j₁ ≠ j₂ := fun h => hne12 (Subtype.ext h)
  have hpair : ({j₁, j₂} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
  have hsum : ∑ j ∈ ({j₁, j₂} : Finset ι), Fintype.card (V j)
      ≤ ∑ j, Fintype.card (V j) :=
    Finset.sum_le_sum_of_subset hpair
  rw [Finset.sum_pair hj, hj₁, hj₂] at hsum
  rw [Fintype.card_sigma]
  omega

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem card_ne_total (i₀ : ι) (h2 : 2 ≤ Fintype.card (V i₀))
    (htwice : 2 ≤ Fintype.card {j : ι // Fintype.card (V j) = Fintype.card (V i₀)}) :
    Fintype.card (V i₀) ≠ Fintype.card (Σ i, V i) := by
  have := two_mul_card_le i₀ htwice
  omega

/-! ## 3. And a pole whose size occurs twice is an eigenvalue -/

theorem isEigen_pole (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (htwice : 2 ≤ Fintype.card {i : ι // 2 * Fintype.card (V i) = 2 * Fintype.card (V i₀)})
    (hnodouble : ∀ i : ι, Fintype.card (V i) ≠ 2 * Fintype.card (V i₀)) :
    IsEigen V ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i₀)) := by
  have hval : ∀ i : ι, ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i))
      ≠ (Fintype.card (Σ i, V i) : ℝ) - (2 * Fintype.card (V i₀) : ℕ) := by
    intro i h
    have : (Fintype.card (V i) : ℝ) = ((2 * Fintype.card (V i₀) : ℕ) : ℝ) := by linarith
    exact hnodouble i (by exact_mod_cast this)
  have hpush : ((2 * Fintype.card (V i₀) : ℕ) : ℝ) = 2 * Fintype.card (V i₀) := by push_cast; ring
  have h := (pole_isEigen_iff (V := V) (n := 2 * Fintype.card (V i₀)) hne i₀ rfl hval).mpr htwice
  rwa [hpush] at h

/-! ## 4. So the lower bound of the bracket doubles -/

theorem two_s_le_card_spectrum (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι)
    (hsize : ∀ i, 2 ≤ Fintype.card (V i))
    (htwice : ∀ i, 2 ≤ Fintype.card {j : ι // Fintype.card (V j) = Fintype.card (V i)})
    (hnodouble : ∀ i j : ι, Fintype.card (V i) ≠ 2 * Fintype.card (V j)) :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen V μ)
      ∧ 2 * (Finset.univ.image (fun i : ι => Fintype.card (V i))).card ≤ S.card := by
  classical
  obtain ⟨S, hS, -, -⟩ := exists_spectrum_bracket (V := V) hne hι
  refine ⟨S, hS, ?_⟩
  set N : ℝ := (Fintype.card (Σ i, V i) : ℝ) with hN
  set sizes := Finset.univ.image (fun i : ι => Fintype.card (V i)) with hsizes
  have hinjP : Function.Injective (fun n : ℕ => N - n) := by
    intro a b h
    have : (a : ℝ) = b := by simpa using h
    exact_mod_cast this
  have hinjQ : Function.Injective (fun n : ℕ => N - 2 * n) := by
    intro a b h
    have : (2 : ℝ) * a = 2 * b := by simp only at h; linarith
    have : (a : ℝ) = b := by linarith
    exact_mod_cast this
  have hPcard : (sizes.image (fun n : ℕ => N - n)).card = sizes.card :=
    Finset.card_image_of_injective _ hinjP
  have hQcard : (sizes.image (fun n : ℕ => N - 2 * n)).card = sizes.card :=
    Finset.card_image_of_injective _ hinjQ
  have hdisj : Disjoint (sizes.image (fun n : ℕ => N - n))
      (sizes.image (fun n : ℕ => N - 2 * n)) := by
    rw [Finset.disjoint_left]
    rintro μ hμP hμQ
    simp only [hsizes, Finset.mem_image, Finset.mem_univ, true_and] at hμP hμQ
    obtain ⟨a, ⟨i, rfl⟩, rfl⟩ := hμP
    obtain ⟨b, ⟨j, rfl⟩, hb⟩ := hμQ
    have : (Fintype.card (V i) : ℝ) = 2 * Fintype.card (V j) := by linarith
    exact hnodouble i j (by exact_mod_cast this)
  have hsub : (sizes.image (fun n : ℕ => N - n)) ∪ (sizes.image (fun n : ℕ => N - 2 * n)) ⊆ S := by
    intro μ hμ
    rw [Finset.mem_union] at hμ
    rcases hμ with h | h
    · simp only [hsizes, Finset.mem_image, Finset.mem_univ, true_and] at h
      obtain ⟨a, ⟨i, rfl⟩, rfl⟩ := h
      exact (hS _).mpr (isEigen_part_value hne i (hsize i) (card_ne_total i (hsize i) (htwice i)))
    · simp only [hsizes, Finset.mem_image, Finset.mem_univ, true_and] at h
      obtain ⟨a, ⟨i, rfl⟩, rfl⟩ := h
      have htw : 2 ≤ Fintype.card {j : ι // 2 * Fintype.card (V j) = 2 * Fintype.card (V i)} := by
        have hequiv : {j : ι // 2 * Fintype.card (V j) = 2 * Fintype.card (V i)}
            ≃ {j : ι // Fintype.card (V j) = Fintype.card (V i)} :=
          Equiv.subtypeEquivRight (fun j => by constructor <;> intro h <;> omega)
        rw [Fintype.card_congr hequiv]
        exact htwice i
      exact (hS _).mpr (isEigen_pole hne i htw (fun j => hnodouble j i))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hPcard, hQcard] at hcard
  omega

/-! ## 5. And the hypotheses are not empty: `K_{2,2,3,3}` -/

/-- Two parts of two and two parts of three. -/
abbrev P2233 : Fin 4 → Type := fun i => Fin (2 + i.1 / 2)

theorem card_P2233 (i : Fin 4) : Fintype.card (P2233 i) = 2 + i.1 / 2 := by
  simp [P2233]

theorem sizes_P2233 :
    (Finset.univ.image (fun i : Fin 4 => Fintype.card (P2233 i))).card = 2 := by decide

theorem four_le_card_spectrum_P2233 :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen P2233 μ) ∧ 4 ≤ S.card := by
  obtain ⟨S, hS, hcard⟩ := two_s_le_card_spectrum (V := P2233) (fun _ => ⟨0⟩) ⟨0⟩
    (by decide) (by decide) (by decide)
  rw [sizes_P2233] at hcard
  exact ⟨S, hS, by omega⟩

end SignlessDoubleBracket
