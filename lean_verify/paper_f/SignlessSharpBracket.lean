import SecularRootsOffPoles

/-!
# The bracket collapses: `3s` exactly, under three conditions on the part sizes

`SignlessSpectrumTrichotomy` bracketed `Q`'s distinct eigenvalues between `s` and `3s`.
`SignlessBracketAttained` made the ceiling tight at one graph, `SignlessDoubleBracket` raised the
floor to `2s`, and `SecularRootsOffPoles` found the pole–root disjointness free and the part-value–
root disjointness **false in general** — `SecularRootAtPartValue` exhibits `K_{1,3,3}`, where a part
value satisfies the secular equation. **So the last step could only be bought with a hypothesis, and
this file buys it with one line of arithmetic.**

**The computation.** At a part value `μ = N − nⱼ` the secular sum's denominators become
`nⱼ − 2nᵢ`, so

* at any `i` with `nᵢ = nⱼ` the term is `nⱼ / (−nⱼ) = −1`, and there are at least two such `i` when
  every size occurs twice — **already `−2`**;
* at every other `i` the term is `nᵢ / (nⱼ − 2nᵢ)`, which is `≤ 0` **exactly when `nⱼ < 2nᵢ`**.

Hence `secularSum (N − nⱼ) ≤ −2 < −1`, and a part value is never a secular root. **`K_{1,3,3}` is
the case where the second bullet fails**: its size-`1` part gives `3 − 2 = 1 > 0` and a term of
`+1`, which cancels one of the `−1`s and lands the sum exactly on `−1`. The counterexample is not an
accident of that graph; it is the only way the argument can fail.

## What is proved

> **`secularSum_at_part_value_le`** — `secularSum (N − nⱼ) ≤ −2`, by splitting the sum on
> `nᵢ = nⱼ` and bounding the two halves: the first is a constant `−1` with at least two terms, the
> second is a sum of non-positive terms.
>
> **`part_value_not_secular_root`** — hence never `−1`.
>
> **`card_spectrum_eq_three_mul`** — **THE SHARP COUNT**: with every part of at least two vertices,
> every size occurring at least twice, and **every size less than twice every other**, `Q` has
> **exactly `3s`** distinct eigenvalues. The three families are the `s` part values, the `s` poles
> and the `s` secular roots; pairwise disjointness is the three bullets above plus
> `SecularRootsOffPoles`; and the trichotomy's `≤ 3s` closes it from the other side.
>
> **`card_spectrum_P2233`** — and the four-part witness two units back is resolved:
> `K_{2,2,3,3}` has **exactly six** distinct eigenvalues, where `SignlessDoubleBracket` could say
> only *at least four* and the ceiling was six.

## What is NOT here

* **THE THIRD CONDITION IS NOT SHOWN NECESSARY**, only sufficient. `K_{2,2}` satisfies all three
  and is sharp; `K_{1,3,3}` fails the third and is **not** sharp, having `s = 2` and three
  eigenvalues rather than six — so the condition is doing real work at least once, and whether some
  graph violating it is nevertheless sharp is **open, not attempted** (`ERRATUM 246`).

  ⚠ **HALF OF IT IS NECESSARY, PROVED THE SAME DAY, AND THE BULLET IS KEPT AS WRITTEN**
  (`ERRATUM 94`). The third condition has two halves. `SignlessDoublingFails`: if some size is
  **exactly** twice another then the pole `N − 2nᵢ` **is** the part value `N − nⱼ`, two of the three
  families share a member, and the cover — each family of size `s` — is at most `3s − 1`, so
  `#spec < 3s` with **no other hypothesis on the sizes at all**. `K_{1,1,2,2}` is the boundary case
  exhibited. **The other half** — *no size is more than twice another* — **stays merely
  sufficient**: `K_{1,3,3}` violates it and is not sharp, but for a **different reason**, a secular
  root landing on a part value rather than a pole doing so.
* **NO MULTIPLICITIES AND NO CHARACTERISTIC POLYNOMIAL.** `3s` counts **distinct** eigenvalues. The
  multiplicities are computed elsewhere in this chain and are not assembled into `N` here.
* **NO ROOT VALUES.** The `s` secular roots are counted and located between poles, never evaluated —
  as everywhere in this chain.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances, `∀ i, Nonempty (V i)`, `Nonempty ι`, and the three arithmetic conditions; §§1–2 omit both
`DecidableEq`s, the estimate being about a sum of reals. **No mass, no propagator, no metric.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessSharpBracket

open Matrix Finset SimpleGraph LaplacianSignless SignlessSpectrumTrichotomy
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation
open SignlessDoubleBracket SecularRootsOffPoles

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. At a part value the secular sum is at most `-2` -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem secularSum_at_part_value_le (hne : ∀ i, Nonempty (V i)) (j : ι)
    (htwice : 2 ≤ Fintype.card {k : ι // Fintype.card (V k) = Fintype.card (V j)})
    (hspread : ∀ i k : ι, Fintype.card (V k) < 2 * Fintype.card (V i)) :
    secularSum (V := V) ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V j)) ≤ -2 := by
  classical
  set N : ℝ := (Fintype.card (Σ i, V i) : ℝ) with hN
  set μ : ℝ := N - Fintype.card (V j) with hμ
  have hterm : ∀ i : ι, N - 2 * Fintype.card (V i) - μ
      = (Fintype.card (V j) : ℝ) - 2 * Fintype.card (V i) := by
    intro i; rw [hμ]; ring
  have hden_neg : ∀ i : ι, (Fintype.card (V j) : ℝ) - 2 * Fintype.card (V i) < 0 := by
    intro i
    have := hspread i j
    have : (Fintype.card (V j) : ℝ) < 2 * Fintype.card (V i) := by exact_mod_cast this
    linarith
  have hsplit : secularSum (V := V) μ
      = ∑ i, (Fintype.card (V i) : ℝ) / ((Fintype.card (V j) : ℝ) - 2 * Fintype.card (V i)) := by
    simp only [secularSum]
    exact Finset.sum_congr rfl fun i _ => by rw [hterm i]
  rw [hsplit, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i => Fintype.card (V i) = Fintype.card (V j))]
  have heq : ∀ i ∈ Finset.univ.filter (fun i => Fintype.card (V i) = Fintype.card (V j)),
      (Fintype.card (V i) : ℝ) / ((Fintype.card (V j) : ℝ) - 2 * Fintype.card (V i)) = -1 := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [hi.2]
    have hpos : (0 : ℝ) < Fintype.card (V j) := by
      have := Fintype.card_pos_iff.mpr (hne j)
      exact_mod_cast this
    field_simp
    norm_num
  rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
  have hcard : 2 ≤ (Finset.univ.filter
      (fun i => Fintype.card (V i) = Fintype.card (V j))).card := by
    rw [← Fintype.card_subtype]
    exact htwice
  have hnonpos : ∑ i ∈ Finset.univ.filter (fun i => ¬ Fintype.card (V i) = Fintype.card (V j)),
      (Fintype.card (V i) : ℝ) / ((Fintype.card (V j) : ℝ) - 2 * Fintype.card (V i)) ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => ?_
    have h1 : (0 : ℝ) ≤ Fintype.card (V i) := Nat.cast_nonneg _
    exact div_nonpos_of_nonneg_of_nonpos h1 (le_of_lt (hden_neg i))
  have h2 : (2 : ℝ) ≤ (Finset.univ.filter
      (fun i => Fintype.card (V i) = Fintype.card (V j))).card := by exact_mod_cast hcard
  nlinarith

/-! ## 2. So no part value is a secular root -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem part_value_not_secular_root (hne : ∀ i, Nonempty (V i)) (j : ι)
    (htwice : 2 ≤ Fintype.card {k : ι // Fintype.card (V k) = Fintype.card (V j)})
    (hspread : ∀ i k : ι, Fintype.card (V k) < 2 * Fintype.card (V i)) :
    secularSum (V := V) ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V j)) ≠ -1 := by
  have h := secularSum_at_part_value_le hne j htwice hspread
  intro hcon
  rw [hcon] at h
  linarith

/-! ## 3. And the bracket collapses: `#spec = 3s` -/

theorem card_spectrum_eq_three_mul (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι)
    (hsize : ∀ i, 2 ≤ Fintype.card (V i))
    (htwice : ∀ i, 2 ≤ Fintype.card {j : ι // Fintype.card (V j) = Fintype.card (V i)})
    (hspread : ∀ i k : ι, Fintype.card (V k) < 2 * Fintype.card (V i)) :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen V μ)
      ∧ S.card = 3 * (Finset.univ.image (fun i : ι => Fintype.card (V i))).card := by
  classical
  obtain ⟨S, hS, -, hhigh⟩ := exists_spectrum_bracket (V := V) hne hι
  obtain ⟨R, hRcard, hRchar, hRe⟩ := exists_roots_finset_eigen (V := V) hne hι
  refine ⟨S, hS, ?_⟩
  set N : ℝ := (Fintype.card (Σ i, V i) : ℝ) with hN
  set sizes := Finset.univ.image (fun i : ι => Fintype.card (V i)) with hsizes
  have hnodouble : ∀ i j : ι, Fintype.card (V i) ≠ 2 * Fintype.card (V j) := by
    intro i j h
    have := hspread j i
    omega
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
    exact part_value_not_secular_root hne i (htwice i) hspread ((hRchar _).mp hμR).1
  have hsub : P ∪ Q ∪ R ⊆ S := by
    intro μ hμ
    rw [Finset.mem_union, Finset.mem_union] at hμ
    rcases hμ with (h | h) | h
    · simp only [hPdef, hsizes, Finset.mem_image, Finset.mem_univ, true_and] at h
      obtain ⟨a, ⟨i, rfl⟩, rfl⟩ := h
      exact (hS _).mpr (isEigen_part_value hne i (hsize i) (card_ne_total i (hsize i) (htwice i)))
    · simp only [hQdef, hsizes, Finset.mem_image, Finset.mem_univ, true_and] at h
      obtain ⟨a, ⟨i, rfl⟩, rfl⟩ := h
      have htw : 2 ≤ Fintype.card {j : ι // 2 * Fintype.card (V j) = 2 * Fintype.card (V i)} := by
        have hequiv : {j : ι // 2 * Fintype.card (V j) = 2 * Fintype.card (V i)}
            ≃ {j : ι // Fintype.card (V j) = Fintype.card (V i)} :=
          Equiv.subtypeEquivRight (fun j => by constructor <;> intro h <;> omega)
        rw [Fintype.card_congr hequiv]
        exact htwice i
      exact (hS _).mpr (isEigen_pole hne i htw (fun j => hnodouble j i))
    · exact (hS _).mpr (hRe μ h)
  have hdisjU : Disjoint (P ∪ Q) R := Finset.disjoint_union_left.mpr ⟨hPR, hQR⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisjU, Finset.card_union_of_disjoint hPQ,
    hPcard, hQcard, hRcard] at hcard
  omega

/-! ## 4. And the four-part witness is resolved -/

theorem card_spectrum_P2233 :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen SignlessDoubleBracket.P2233 μ) ∧ S.card = 6 := by
  obtain ⟨S, hS, hcard⟩ := card_spectrum_eq_three_mul (V := SignlessDoubleBracket.P2233)
    (fun _ => ⟨0⟩) ⟨0⟩ (by decide) (by decide) (by decide)
  rw [SignlessDoubleBracket.sizes_P2233] at hcard
  exact ⟨S, hS, by omega⟩

end SignlessSharpBracket
