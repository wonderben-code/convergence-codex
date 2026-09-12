import SignlessDoubleBracket

/-!
# The secular roots are never poles, which the estate had proved and thrown away

`SignlessDoubleBracket` doubled the bracket's lower bound to `2s` using the part values and the
poles, and named the last step to `3s`: *the `s` secular roots must be shown distinct from the `s`
part values and the `s` poles.* **Half of that is free and had been proved already.**

`SecularRootExact.exists_roots_finset_exact` characterises its root set by a **biconditional**:
`μ ∈ R` exactly when `secularSum μ = −1` **and** `N − 2nₖ − μ ≠ 0` for every `k`. The second clause
says in as many words that **`μ` is not a pole**. The very next theorem in that file,
`exists_eigenvalues_finset_exact`, uses both clauses to build an eigenvector and then returns only
*"every element of `R` is an eigenvalue"* — **the characterisation is discarded on the way
out**, and with it the disjointness. Nothing downstream could recover it. `ERRATUM 517`'s species,
one file along: a fact proved and not kept.

## What is proved

> **`exists_roots_finset_eigen`** — the same statement with the biconditional **retained** beside
> the eigenvalue conclusion. Four lines, all of them copied from the proof that threw it away.
>
> **`two_s_le_card_spectrum_poles_roots`** — **`2s ≤ #spec` again, on strictly weaker hypotheses.**
> The previous unit needed three conditions; this needs two, because the pole–root disjointness is
> free where the pole–part-value disjointness had to be bought. **`every part has at least two
> vertices` is gone**: parts of size one contribute no part value, and this route does not use the
> part values at all.
>
> **`P1133`, `four_le_card_spectrum_P1133`, `not_two_le_card_P1133`** — and the weakening bites:
> `K_{1,1,3,3}` has a part of size one, so `SignlessDoubleBracket.two_s_le_card_spectrum` **does not
> apply to it** (`not_two_le_card_P1133` says so by `decide`), and this theorem gives it at least
> four distinct eigenvalues all the same.

## What is NOT here

* **`3s` STILL DOES NOT FOLLOW, AND THE REMAINING HALF IS NOT A TECHNICALITY.** What is left is
  whether a **part value** can be a secular root, and **it can**:
  `SecularRootAtPartValue.part_value_eq_secular_root` exhibits `K_{1,3,3}`, where the part value
  `N − 3 = 4` satisfies the secular equation. So *"the roots avoid the other two families"* is
  **false in general**, and any proof of `3s` must use the hypotheses rather than the location
  results alone. **The entry-53 note that called this one step and the location results sufficient
  was half right**: the poles are free, the part values are not, and the estate contained the
  counterexample the whole time.
* **NO CLAIM THAT THE TWO CONDITIONS ARE NECESSARY**, and no claim that `K_{1,1,3,3}`'s bound is
  sharp — its ceiling is `3s = 6` and nothing here decides between four and six.
* **NO MULTIPLICITIES, NO CHARACTERISTIC POLYNOMIAL, NOTHING OVER `ℂ`.** The count is of
  **distinct** eigenvalues throughout.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances, `∀ i, Nonempty (V i)`, `Nonempty ι`, and the two arithmetic conditions — *every size
occurs at least twice* and *no size is twice another*. **No mass, no propagator, no metric.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SecularRootsOffPoles

open Matrix Finset SimpleGraph LaplacianSignless SignlessSpectrumTrichotomy
open UnbalancedMultipartite UnbalancedMultipartiteSecular SecularRootExact
open UnbalancedMultipartiteSecularEquation
open SignlessDoubleBracket

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. The characterisation the eigenvalue statement threw away -/

theorem exists_roots_finset_eigen (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) :
    ∃ R : Finset ℝ,
      R.card = (Finset.univ.image (fun i : ι => Fintype.card (V i))).card
        ∧ (∀ μ : ℝ, μ ∈ R ↔ secularSum (V := V) μ = -1
            ∧ ∀ k : ι, ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) - μ) ≠ 0)
        ∧ ∀ μ ∈ R, IsEigen V μ := by
  classical
  obtain ⟨R, hcard, hR⟩ := exists_roots_finset_exact (V := V) hne hι
  refine ⟨R, hcard, hR, fun μ hμ => ?_⟩
  obtain ⟨hs, hd⟩ := (hR μ).mp hμ
  obtain ⟨x, hx, hxp⟩ :=
    exists_eigenvector_of_mem_ker_secular hne (mem_ker_secularVec (V := V) hd hs)
  exact ⟨x, fun h0 => secularVec_ne_zero hne (Classical.choice hι) hd
    (by rw [← hxp, h0, map_zero]), hx⟩

/-! ## 2. So the poles and the secular roots never meet -/

theorem two_s_le_card_spectrum_poles_roots (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι)
    (htwice : ∀ i, 2 ≤ Fintype.card {j : ι // Fintype.card (V j) = Fintype.card (V i)})
    (hnodouble : ∀ i j : ι, Fintype.card (V i) ≠ 2 * Fintype.card (V j)) :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen V μ)
      ∧ 2 * (Finset.univ.image (fun i : ι => Fintype.card (V i))).card ≤ S.card := by
  classical
  obtain ⟨S, hS, -, -⟩ := exists_spectrum_bracket (V := V) hne hι
  obtain ⟨R, hRcard, hRchar, hRe⟩ := exists_roots_finset_eigen (V := V) hne hι
  refine ⟨S, hS, ?_⟩
  set N : ℝ := (Fintype.card (Σ i, V i) : ℝ) with hN
  set sizes := Finset.univ.image (fun i : ι => Fintype.card (V i)) with hsizes
  have hinjQ : Function.Injective (fun n : ℕ => N - 2 * n) := by
    intro a b h
    have h2 : (2 : ℝ) * a = 2 * b := by simp only at h; linarith
    have : (a : ℝ) = b := by linarith
    exact_mod_cast this
  have hQcard : (sizes.image (fun n : ℕ => N - 2 * n)).card = sizes.card :=
    Finset.card_image_of_injective _ hinjQ
  have hdisj : Disjoint (sizes.image (fun n : ℕ => N - 2 * n)) R := by
    rw [Finset.disjoint_left]
    rintro μ hμQ hμR
    simp only [hsizes, Finset.mem_image, Finset.mem_univ, true_and] at hμQ
    obtain ⟨a, ⟨i, rfl⟩, rfl⟩ := hμQ
    exact ((hRchar _).mp hμR).2 i (by ring)
  have hsub : (sizes.image (fun n : ℕ => N - 2 * n)) ∪ R ⊆ S := by
    intro μ hμ
    rw [Finset.mem_union] at hμ
    rcases hμ with h | h
    · simp only [hsizes, Finset.mem_image, Finset.mem_univ, true_and] at h
      obtain ⟨a, ⟨i, rfl⟩, rfl⟩ := h
      have htw : 2 ≤ Fintype.card {j : ι // 2 * Fintype.card (V j) = 2 * Fintype.card (V i)} := by
        have hequiv : {j : ι // 2 * Fintype.card (V j) = 2 * Fintype.card (V i)}
            ≃ {j : ι // Fintype.card (V j) = Fintype.card (V i)} :=
          Equiv.subtypeEquivRight (fun j => by constructor <;> intro h <;> omega)
        rw [Fintype.card_congr hequiv]
        exact htwice i
      exact (hS _).mpr (isEigen_pole hne i htw (fun j => hnodouble j i))
    · exact (hS _).mpr (hRe μ h)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hQcard, hRcard] at hcard
  omega

/-! ## 3. And the weakening bites: a graph the previous bound does not reach -/

/-- Two parts of one and two parts of three — **a size below two**, so
`SignlessDoubleBracket.two_s_le_card_spectrum` does not apply. -/
abbrev P1133 : Fin 4 → Type := fun i => Fin (1 + 2 * (i.1 / 2))

theorem card_P1133 (i : Fin 4) : Fintype.card (P1133 i) = 1 + 2 * (i.1 / 2) := by
  simp [P1133]

theorem sizes_P1133 :
    (Finset.univ.image (fun i : Fin 4 => Fintype.card (P1133 i))).card = 2 := by decide

theorem not_two_le_card_P1133 : ¬ (∀ i : Fin 4, 2 ≤ Fintype.card (P1133 i)) := by decide

theorem four_le_card_spectrum_P1133 :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen P1133 μ) ∧ 4 ≤ S.card := by
  obtain ⟨S, hS, hcard⟩ := two_s_le_card_spectrum_poles_roots (V := P1133) (fun _ => ⟨0⟩) ⟨0⟩
    (by decide) (by decide)
  rw [sizes_P1133] at hcard
  exact ⟨S, hS, by omega⟩

end SecularRootsOffPoles
