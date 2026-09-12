import PartValueSingleton

/-!
# Every eigenvalue of `Q` on a complete multipartite graph, with a verdict attached

`SignlessSpectrumTrichotomy` proved that every eigenvalue is a part value, a pole or a secular
root, and said in its own header that read as a contrapositive it says *there is nothing else*.
**What it does not say is which candidates are eigenvalues**, and for eleven entries the chain has
answered that one graph at a time. Two units ago the part-value half became a characterisation
(`PartValueSingleton.part_value_isEigen_iff`); the pole half has been one since entry 174
(`SignlessSpectrumTrichotomy.pole_isEigen_iff`), stated **off** the part values. **This file puts
the two together**, and the coincidence that made that awkward turns out to be harmless.

**WHY THE COINCIDENCE IS HARMLESS.** `pole_isEigen_iff` refuses to speak when a pole is also a
part value. It does not have to: `part_value_isEigen_iff` speaks there instead, with **no**
hypothesis about poles, so the two overlap exactly where one of them is silent. The only care
needed is in the backward direction — a pole `N − 2nᵢ` that coincides with a part value has that
part of size `2nᵢ ≥ 2`, so it is an eigenvalue by the part-value route.

## What is proved

**`isEigen_iff`** — **the complete description.** For a complete multipartite graph with at least
two non-empty parts, `μ` is an eigenvalue of `Q` if and only if one of:

> * `μ = N − nⱼ` for a part with **`2 ≤ nⱼ`**;
> * `μ = N − 2nᵢ` for a part whose size is **shared by at least two parts**;
> * `μ` is **neither** a part value nor a pole, and `secularSum μ = −1`.

The third clause keeps its guards, and that is not tidiness. At a pole one denominator of the
secular sum vanishes, so `secularSum μ = −1` there is a statement about Lean's value for division
by zero; and it is not idle, because a pole whose size is **not** shared is not an eigenvalue no
matter what the sum reads. `isEigenvalue_signless_iff_secular` carries the non-vanishing
hypothesis for exactly this reason, and no statement in this chain had drawn the conclusion.

**`bigSizes`, `repSizes`** — the two families the first two clauses range over, as computable
`Finset ℕ`s: the sizes of at least two vertices, and the sizes shared by at least two parts.

**`card_spectrum_le_refined`** — **and the upper bound `3s` improves to `#bigSizes + #repSizes +
s`.** Both new summands are at most `s`, so this is never worse; it is strictly better as soon as
some part is a singleton or some size is unrepeated. It **subsumes**
`PartValueSingleton.card_spectrum_lt_three_mul_of_singleton` — and that is a theorem here
(`card_spectrum_lt_three_mul_of_singleton'`, three lines from the bound) rather than a remark —
and it equals `3s` exactly when every size is at least two and repeated — which is the hypothesis
pair `SignlessSharpBracket` and `SecularPositivePart` both take for their sharp counts. **The
bound and the sharpness conditions finally have the same shape.**

**`refined_P1122`, `refined_Part133`** — the bound at the two graphs known to sit below `3s`: `5`
at `K_{1,1,2,2}` (whose count is `4`) and `4` at `K_{1,3,3}` (whose count is `3`), against `3s = 6`
for both.

## What is NOT here

* **THE BOUND IS NOT SHOWN TIGHT, AND IT IS NOT.** At `K_{1,1,2,2}` it gives `5` against a true
  count of `4`, and at `K_{1,3,3}` it gives `4` against `3`. The slack is the root family, counted
  at its maximum `s` because nothing here bounds the number of secular roots better. Improving
  that is the obvious next question and is **not attempted** (`ERRATUM 246`).
* **NO MULTIPLICITIES.** `isEigen_iff` is about the eigenvalue **set**; the dimension theorems it
  is built from carry multiplicities and this statement discards them.
* **NO DECISION PROCEDURE.** The third clause quantifies over the reals, so the criterion is not a
  computation; what is computable is the first two families and the bound.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `∀ i, Nonempty (V i)` and
`2 ≤ Fintype.card ι`, and nothing else — no condition on the sizes anywhere. **No mass, no
propagator, no metric.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessSpectrumComplete

open Matrix Finset SimpleGraph LaplacianSignless SignlessSpectrumTrichotomy
open SignlessDoubleBracket PartValueSingleton SecularRootExact SecularRootCount
open SignlessDoublingFails
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. The complete description -/

/-- **EVERY EIGENVALUE OF `Q`, WITH A VERDICT.** -/
theorem isEigen_iff (hne : ∀ i, Nonempty (V i)) (htwo : 2 ≤ Fintype.card ι) (μ : ℝ) :
    IsEigen V μ ↔
      (∃ j : ι, μ = (Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V j)
          ∧ 2 ≤ Fintype.card (V j))
      ∨ (∃ i : ι, μ = (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)
          ∧ 2 ≤ Fintype.card {k : ι // 2 * Fintype.card (V k) = 2 * Fintype.card (V i)})
      ∨ ((∀ j : ι, μ ≠ (Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V j))
          ∧ (∀ i : ι, μ ≠ (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i))
          ∧ secularSum (V := V) μ = -1) := by
  classical
  have hι : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  constructor
  · intro hx
    by_cases hval : ∃ j : ι, μ = (Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V j)
    · obtain ⟨j, rfl⟩ := hval
      exact Or.inl ⟨j, rfl, (part_value_isEigen_iff (V := V) hne htwo j).mp hx⟩
    by_cases hpole : ∃ i : ι, μ = (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)
    · obtain ⟨i, rfl⟩ := hpole
      refine Or.inr (Or.inl ⟨i, rfl, ?_⟩)
      have hcast : ((2 * Fintype.card (V i) : ℕ) : ℝ) = 2 * (Fintype.card (V i) : ℝ) := by
        push_cast; ring
      refine (pole_isEigen_iff (V := V) (n := 2 * Fintype.card (V i)) hne i rfl ?_).mp ?_
      · intro k hk
        exact hval ⟨k, by rw [hcast] at hk; linarith⟩
      · rw [hcast]; exact hx
    · simp only [not_exists] at hval hpole
      refine Or.inr (Or.inr ⟨hval, hpole, ?_⟩)
      rcases eigenvalue_trichotomy (V := V) hne (Classical.choice hι) hx with ⟨j, h⟩ | ⟨i, h⟩ | h
      · exact absurd h.symm (hval j)
      · exact absurd h.symm (hpole i)
      · exact h
  · rintro (⟨j, rfl, h2⟩ | ⟨i, rfl, h2⟩ | ⟨hval, hpole, hs⟩)
    · exact (part_value_isEigen_iff (V := V) hne htwo j).mpr h2
    · by_cases hd : ∃ k : ι, Fintype.card (V k) = 2 * Fintype.card (V i)
      · obtain ⟨k, hk⟩ := hd
        have hval : ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i))
            = (Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V k) := by
          rw [hk]; push_cast; ring
        rw [hval]
        refine (part_value_isEigen_iff (V := V) hne htwo k).mpr ?_
        have := Fintype.card_pos_iff.mpr (hne i)
        omega
      · simp only [not_exists] at hd
        exact isEigen_pole (V := V) hne i (by simpa using h2) (fun k => hd k)
    · exact (isEigenvalue_signless_iff_secular (V := V) hne (Classical.choice hι)
        (fun i => Ne.symm (hval i)) (fun i => sub_ne_zero_of_ne (Ne.symm (hpole i)))).mpr hs

/-! ## 2. The two families the verdicts range over -/

/-- The distinct part sizes of at least two vertices. -/
def bigSizes (V : ι → Type*) [Fintype ι] [∀ i, Fintype (V i)] : Finset ℕ :=
  (Finset.univ.image (fun i : ι => Fintype.card (V i))).filter (fun n => 2 ≤ n)

/-- The distinct part sizes shared by at least two parts. -/
def repSizes (V : ι → Type*) [Fintype ι] [DecidableEq ι] [∀ i, Fintype (V i)] : Finset ℕ :=
  (Finset.univ.image (fun i : ι => Fintype.card (V i))).filter
    (fun n => 2 ≤ (Finset.univ.filter (fun i : ι => Fintype.card (V i) = n)).card)

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem mem_bigSizes {j : ι} (h2 : 2 ≤ Fintype.card (V j)) :
    Fintype.card (V j) ∈ bigSizes V :=
  Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ j), h2⟩

omit [∀ i, DecidableEq (V i)] in
theorem mem_repSizes {i : ι}
    (h2 : 2 ≤ Fintype.card {k : ι // 2 * Fintype.card (V k) = 2 * Fintype.card (V i)}) :
    Fintype.card (V i) ∈ repSizes V := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), ?_⟩
  have hset : (Finset.univ.filter (fun k : ι => Fintype.card (V k) = Fintype.card (V i)))
      = (Finset.univ.filter (fun k : ι => 2 * Fintype.card (V k)
          = 2 * Fintype.card (V i))) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  rw [hset, ← Fintype.card_subtype]
  exact h2

/-! ## 3. So the bracket's top improves, in general -/

/-- **`3s` BECOMES `#bigSizes + #repSizes + s`.** -/
theorem card_spectrum_le_refined (hne : ∀ i, Nonempty (V i)) (htwo : 2 ≤ Fintype.card ι) :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen V μ)
      ∧ S.card ≤ (bigSizes V).card + (repSizes V).card
          + (Finset.univ.image (fun i : ι => Fintype.card (V i))).card := by
  classical
  have hι : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨S, hS, -, -⟩ := exists_spectrum_bracket (V := V) hne hι
  obtain ⟨R, hRcard, hR⟩ := exists_roots_finset_exact (V := V) hne hι
  refine ⟨S, hS, ?_⟩
  set N : ℝ := (Fintype.card (Σ i, V i) : ℝ) with hN
  set P := (bigSizes V).image (fun n : ℕ => N - n) with hP
  set Q := (repSizes V).image (fun n : ℕ => N - 2 * n) with hQ
  have hsub : S ⊆ P ∪ Q ∪ R := by
    intro μ hμ
    rcases (isEigen_iff (V := V) hne htwo μ).mp ((hS μ).mp hμ) with
      ⟨j, rfl, h2⟩ | ⟨i, rfl, h2⟩ | ⟨hval, hpole, hs⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (mem_bigSizes (V := V) h2)))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (mem_repSizes (V := V) h2)))
    · exact Finset.mem_union_right _ ((hR _).mpr ⟨hs, fun k => sub_ne_zero_of_ne
        (Ne.symm (hpole k))⟩)
  have hcard := Finset.card_le_card hsub
  have h1 : P.card ≤ (bigSizes V).card := Finset.card_image_le
  have h2 : Q.card ≤ (repSizes V).card := Finset.card_image_le
  have h3 : (P ∪ Q ∪ R).card ≤ (P ∪ Q).card + R.card := Finset.card_union_le _ _
  have h4 : (P ∪ Q).card ≤ P.card + Q.card := Finset.card_union_le _ _
  omega

/-- **AND IT SUBSUMES THE SINGLETON BOUND**, which is now a corollary rather than a sibling: a
part of one vertex keeps `1` out of `bigSizes`, so the first summand is short of `s`. -/
theorem card_spectrum_lt_three_mul_of_singleton' (hne : ∀ i, Nonempty (V i))
    (htwo : 2 ≤ Fintype.card ι) {j : ι} (h1 : Fintype.card (V j) = 1) :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen V μ)
      ∧ S.card < 3 * (Finset.univ.image (fun k : ι => Fintype.card (V k))).card := by
  classical
  obtain ⟨S, hS, hcard⟩ := card_spectrum_le_refined (V := V) hne htwo
  refine ⟨S, hS, ?_⟩
  set sizes := Finset.univ.image (fun k : ι => Fintype.card (V k)) with hsizes
  have hbig : bigSizes V ⊂ sizes := by
    refine ⟨Finset.filter_subset _ _, fun hcon => ?_⟩
    have hmem : (1 : ℕ) ∈ sizes := by
      rw [hsizes, ← h1]; exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
    have := Finset.mem_filter.mp (hcon hmem)
    omega
  have hrep : repSizes V ⊆ sizes := Finset.filter_subset _ _
  have h1' : (bigSizes V).card < sizes.card := Finset.card_lt_card hbig
  have h2' : (repSizes V).card ≤ sizes.card := Finset.card_le_card hrep
  omega

/-! ## 4. The two graphs known to sit below `3s` -/

theorem refined_P1122 :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen P1122 μ) ∧ S.card ≤ 5 := by
  obtain ⟨S, hS, hcard⟩ := card_spectrum_le_refined (V := P1122) (fun _ => ⟨0⟩) (by decide)
  refine ⟨S, hS, ?_⟩
  rw [show (bigSizes P1122).card = 1 from by decide,
    show (repSizes P1122).card = 2 from by decide, sizes_P1122] at hcard
  omega

theorem refined_Part133 :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen SecularRootAtPartValue.Part133 μ)
      ∧ S.card ≤ 4 := by
  obtain ⟨S, hS, hcard⟩ := card_spectrum_le_refined (V := SecularRootAtPartValue.Part133)
    (fun _ => ⟨0⟩) (by decide)
  refine ⟨S, hS, ?_⟩
  rw [show (bigSizes SecularRootAtPartValue.Part133).card = 1 from by decide,
    show (repSizes SecularRootAtPartValue.Part133).card = 1 from by decide,
    show (Finset.univ.image (fun i : Fin 3 =>
      Fintype.card (SecularRootAtPartValue.Part133 i))).card = 2 from by decide] at hcard
  omega

end SignlessSpectrumComplete
