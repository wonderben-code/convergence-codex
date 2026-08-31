import TorusGenericCount

/-!
# `2^d · d!` is not tight, and the witness is generic

`TorusHyperoctahedral` proves `2^d · d! ≤ dim` at a generic frequency and
`TorusGenericFrequency` shows the bound is attained at `d = 1`. The obvious question is whether it
is attained at `d = 2`, and the previous units left it open with one piece of evidence that does
**not** settle it: `TorusNonReflectionCollision`'s pair `(2, 3)`, `(0, 4)` at side `12` is a
collision outside the signed permutations, but `(0, 4)` is **not generic** — its first coordinate is
at rest — so it says nothing about the multiplicity at a generic frequency.

**Here is a pair that does.** At side `24`, the frequencies `(1, 6)` and `(3, 5)` are **both
generic**, share an eigenvalue, and are not related by any reflection-and-permutation.

> **`cos_pi_div_four_add`** — the analytic content, and it is one identity:
> `cos(π/4) + cos(5π/12) = cos(π/12)`. By `Real.cos_add_cos`, the sum is
> `2 · cos(π/3) · cos(π/12)`, and `cos(π/3) = ½`. **No special value of `cos(π/12)` is needed** —
> it cancels — which is why this pair and not another.
>
> **`eight_generic`, `eight_generic'`** — both frequencies satisfy `TorusGenericCount.Generic`.
>
> **`nuR_eight_eq`** — they share an eigenvalue.
>
> **`eight_ne_signed_perm`** — and no `reflectAxes S ∘ σ` carries one to the other: the eight images
> have first coordinate in `{1, 6, 18, 23}` and this one has `3`.
>
> **`nine_le_finrank_eight`** — hence **`9 ≤ dim` where `2^2 · 2! = 8`**. The bound is not tight,
> proved rather than observed.

## The landscape this sits in, MEASURED OUTSIDE LEAN AND LABELLED AS SUCH

None of the following is proved here or anywhere in this estate. It is a direct enumeration, run
before the witness was chosen, and it is recorded because choosing a witness without it would have
been choosing one at random.

* **At every odd side length from `5` to `45`, the bound is exact at every generic frequency** —
  21 of 21. **That is a conjecture with 21 data points and no proof**, and it is the sharpest form
  the open question now takes.
* **At every even side length from `6` to `44`, it fails** — 20 of 20.
* The failure has two mechanisms. At `6` and `8` the extra members of the class are **not generic**:
  the at-rest and halfway frequencies join it, which the hypotheses exclude from the count but not
  from the eigenspace. From `10` upward there are classes containing **more than eight generic
  frequencies**, which is the mechanism this file exhibits.
* **The smallest generic-versus-generic witness is side `10`, `(1, 4)` against `(2, 3)` — and it is
  a worse witness than the one below**, because both cosine sums are **zero**: each frequency is a
  `{θ, π − θ}` pair and cancels on its own. A reader could dismiss it as an artefact of the value
  `0`. The pair used here has common value `cos(π/12)`, which is not `0`, so the coincidence is a
  coincidence.

## What is NOT here

**No exact multiplicity, at side `24` or anywhere else above one dimension.** `9 ≤ dim` is what is
proved; the true value at this frequency is not computed and is not guessed (`ERRATUM 246`). The
`2^d · d!` bound stays a lower bound and this says only that it is sometimes strict.

**No characterisation of the side lengths where it is tight.** *For which `n` is the bound attained
at every generic frequency at `d = 2`?* is the question this makes precise and does not answer. It
is a question about when `cos(2πa/n) + cos(2πb/n)` collides — cyclotomic arithmetic — and **nothing
here touches it**.

**One witness, at one side length, in one dimension.** No family is claimed and it is not claimed
smallest.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusEightNotTight

open Matrix GraphLaplacian SimpleGraph Finset BoxGraph TorusReflection
open MassiveTorusSpectrum TorusRealMultiplicity TorusReflectionCount TorusHyperoctahedral
open TorusGenericCount

/-! ## 1. The identity -/

/-- **`cos(π/4) + cos(5π/12) = cos(π/12)`.** `Real.cos_add_cos` turns the sum into
`2 · cos(π/3) · cos(π/12)` and `cos(π/3) = ½` finishes it. The value of `cos(π/12)` is never
needed. -/
theorem cos_pi_div_four_add :
    Real.cos (Real.pi / 4) + Real.cos (5 * Real.pi / 12) = Real.cos (Real.pi / 12) := by
  rw [Real.cos_add_cos]
  have h1 : (Real.pi / 4 + 5 * Real.pi / 12) / 2 = Real.pi / 3 := by ring
  have h2 : (Real.pi / 4 - 5 * Real.pi / 12) / 2 = -(Real.pi / 12) := by ring
  rw [h1, h2, Real.cos_neg, Real.cos_pi_div_three]
  ring

/-! ## 2. Two generic frequencies at side `24` -/

/-- The frequency `(1, 6)` at side `24`. -/
def fA : Site 2 (21 + 3) := ![⟨1, by omega⟩, ⟨6, by omega⟩]

/-- The frequency `(3, 5)` at side `24`. -/
def fB : Site 2 (21 + 3) := ![⟨3, by omega⟩, ⟨5, by omega⟩]

theorem fA_generic : Generic fA := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [fA]
  · intro i; fin_cases i <;> simp [fA]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [fA]

theorem fB_generic : Generic fB := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [fB]
  · intro i; fin_cases i <;> simp [fB]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [fB]

/-- **THEY SHARE AN EIGENVALUE**, on §1's identity and `cos(π/2) = 0`. -/
theorem nuR_eight_eq (m : ℝ) : nuR 21 m fA = nuR 21 m fB := by
  have e1 : (2 : ℝ) * Real.pi / 24 = Real.pi / 12 := by ring
  have e6 : (2 : ℝ) * Real.pi * 6 / 24 = Real.pi / 2 := by ring
  have e3 : (2 : ℝ) * Real.pi * 3 / 24 = Real.pi / 4 := by ring
  have e5 : (2 : ℝ) * Real.pi * 5 / 24 = 5 * Real.pi / 12 := by ring
  simp only [nuR, Fin.sum_univ_two, fA, fB, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num
  rw [e1, e6, e3, e5, Real.cos_pi_div_two, ← cos_pi_div_four_add]
  ring

/-- **AND NO SIGNED PERMUTATION RELATES THEM.** The first coordinate again: every
`reflectAxes S (1, 6) ∘ σ` has `1`, `6`, `18` or `23` there, and `(3, 5)` has `3`. -/
theorem eight_ne_signed_perm (S : Finset (Fin 2)) (σ : Equiv.Perm (Fin 2)) :
    fB ≠ signedPerm S σ fA := by
  intro h
  have h0 := congrArg Fin.val (congrFun h 0)
  have hB : (fB (0 : Fin 2)).val = 3 := by simp [fB]
  have hA : ∀ j : Fin 2, (fA j).val = 1 ∨ (fA j).val = 6 := by
    intro j; fin_cases j <;> simp [fA]
  rw [hB] at h0
  by_cases hS : σ (0 : Fin 2) ∈ S
  · rw [signedPerm] at h0
    have := reflectAxes_val_of_mem (N := 21) (S := S) (k := fA) hS
    simp only [Function.comp] at h0
    rw [this] at h0
    rcases hA (σ 0) with hh | hh <;> rw [hh] at h0 <;> omega
  · rw [signedPerm] at h0
    have := reflectAxes_of_not_mem (N := 21) (S := S) (k := fA) hS
    simp only [Function.comp] at h0
    rw [this] at h0
    rcases hA (σ 0) with hh | hh <;> omega

/-! ## 3. Hence the bound is strict here -/

/-- **`9 ≤ dim` WHERE `2^2 · 2! = 8`.** The eight signed permutations of `(1, 6)` are distinct and
all share its eigenvalue; `(3, 5)` shares it too and is none of them. **So the hyperoctahedral bound
is not tight at `d = 2`**, proved rather than observed. -/
theorem nine_le_finrank_eight (m : ℝ) :
    9 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (massive (torusGraph 2 (21 + 3)) m) - (nuR 21 m fA) • LinearMap.id)) := by
  classical
  rw [finrank_eigenspace_massive_real 21 m (nuR 21 m fA)]
  have hcard : Nat.card {k' : Site 2 (21 + 3) // nuR 21 m k' = nuR 21 m fA}
      = (Finset.univ.filter fun k' : Site 2 (21 + 3) => nuR 21 m k' = nuR 21 m fA).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  set orbit := Finset.univ.image
    fun p : Finset (Fin 2) × Equiv.Perm (Fin 2) => signedPerm p.1 p.2 fA with horbit
  have horbit_card : orbit.card = 8 := by
    rw [horbit, Finset.card_image_of_injective _
        (signedPerm_injective fA fA_generic.1 fA_generic.2.1 fA_generic.2.2),
      Finset.card_univ, Fintype.card_prod, Fintype.card_finset, Fintype.card_perm,
      Fintype.card_fin]
    norm_num
  have hnot : fB ∉ orbit := by
    rw [horbit]
    intro hx
    obtain ⟨p, _, hp⟩ := Finset.mem_image.1 hx
    exact eight_ne_signed_perm p.1 p.2 hp.symm
  have hsub : insert fB orbit
      ⊆ Finset.univ.filter fun k' : Site 2 (21 + 3) => nuR 21 m k' = nuR 21 m fA := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Finset.mem_insert.1 hx with rfl | hx'
    · exact (nuR_eight_eq m).symm
    · rw [horbit] at hx'
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hx'
      exact nuR_signedPerm 21 m p.1 p.2 fA
  calc (9 : ℕ) = (insert fB orbit).card := by
        rw [Finset.card_insert_of_notMem hnot, horbit_card]
    _ ≤ _ := Finset.card_le_card hsub

end TorusEightNotTight
