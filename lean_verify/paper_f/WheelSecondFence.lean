/-
  WheelSecondFence: the fence this cluster has named in six units, crossed — the wheel's `λ₂` IS
  `SignlessSecondEigen.secondEigen`, and both halves of the bridge were already in the estate

  **WHY THIS FILE EXISTS.** Six declarations-worth of this cluster end with the same sentence.
  Unit 83: *nothing connects to Mathlib's `IsHermitian.eigenvalues` indexing — the fence this
  cluster keeps meeting, untouched.* Unit 86: *the fence this cluster has met in every unit and has
  still not crossed.* Unit 88: *nothing about Mathlib's `IsHermitian.eigenvalues` indexing.* Unit
  89: *side-stepped rather than crossed.* Unit 93: *the route between them is named for the first
  time.* Unit 112: *the `IsHermitian.eigenvalues` fence is not crossed.* The fence is real: every
  `λ₂` statement in this cluster is an `IsGreatest` over vectors, while the estate's own second
  eigenvalue is `SignlessSecondEigen.secondEigen hA = (univ.erase (topIdx hA)).sup' hA.eigenvalues`,
  a supremum over Mathlib's ENUMERATION. A consumer who wants the estate's object gets nothing from
  six units of work. This file connects them.

  **AND THE BRIDGE WAS ALREADY IN THE ESTATE, IN TWO HALVES, AND ONLY ONE WAS EVER NAMED.**

  * `HermitianFibreCount.finrank_eigenspace_hermitian_eq_card_fibre` (2026-09-12) turns an
    eigenspace dimension into the size of the fibre `{i | eigenvalues i = μ}`. Unit 93 named this
    one. What unit 93 did not notice is that `ConeMultiplicity.coneEig G lam` is **defined** as
    exactly the kernel that theorem is stated about, so there is no bridge to build at all:
    `card_fibre_eq_finrank_coneEig` below is `rfl` composed with one `.symm`.
  * `HermitianCharpoly.mem_image_eigenvalues_iff` (2026-09-12) says `μ ∈ univ.image hA.eigenvalues
    ↔ ∃ x ≠ 0, A *ᵥ x = μ • x` — **the fence itself, as an iff, at every real Hermitian matrix.**
    **No fence sentence in this cluster names it.** It is what converts an index into an
    eigenvector and an eigenvector into an index, which is the whole content of the crossing.

  **SO THE FENCE WAS FOUR DAYS OLDER THAN THE FIRST UNIT THAT DECLARED IT**, and the estate had
  already said so in a ledger row: `SignlessMultipartiteDegeneracy`'s row (2026-09-13) records the
  multipartite chain meeting the same wall and reports *the step is one line and the bridge was
  already in the estate*, citing `mem_image_eigenvalues_iff` by name. Two chains met one fence;
  one crossed it and wrote down that it was cheap; the other declared it six times. This is
  recorded as an erratum rather than absorbed, because the mechanism — a fence phrased as a
  property of THIS file, copied forward until it reads as a property of the estate — is the same
  one `ERRATUM 620` diagnosed and `ERRATUM 621` and `ERRATUM 640` repeated.

  **WHAT IS PROVED.** `topEigen (wheelHerm n) = hubRootPlus (n+3) 2`: the estate's top eigenvalue
  IS unit 83's named root. The two fibre counts, `1` at the top and `2` at `λ₂`, straight off units
  86 and 107. `eigenvalues (topIdx) = hubRootPlus` and the uniqueness of that index. Then
  **`secondEigen_eq_rimVal_one`: `secondEigen (wheelHerm n) = 3 + 2cos(2π/N)` for every `n ≥ 1`** —
  unit 93's `λ₂`, now as a statement about the object the estate defines. And unit 112's bracket
  restated for it: `n − 1 < topEigen − secondEigen ≤ n − 1 + 8/n`, so `L38170`'s question is
  answered about `secondEigen` and not only about an `IsGreatest`.

  **WHAT IS NOT CLAIMED.** **Nothing at a graph that is not a wheel.** The general bridge is
  general — `exists_eigenvector_of_index` and `exists_index_of_eigenvector` hold at every real
  Hermitian matrix — but everything downstream of `wheelHerm` is the cone over a cycle, and
  `L38170`'s general question is untouched. **`secondEigen` is not shown to be the second eigenvalue
  of anything in the multiset sense**: its own docstring records that when the top has multiplicity
  two or more it EQUALS the top, and what makes it a genuine second value here is unit 86's simple
  top, which is why `card_fibre_hubRootPlus = 1` is proved and not assumed. **No new mathematics
  about the wheel**: every eigenvalue fact is imported, and what is new is only which object the
  facts are about. **No `Filter`, no `atTop`, no spectral theorem invoked here** — the spectral
  theorem is inside Mathlib's `eigenvalues` and inside the two bridge lemmas, and this file calls
  them rather than reproving anything.
-/

import ConeSpectralGap
import SignlessSecondEigen
import HermitianCharpoly

namespace WheelSecondFence

open Matrix Finset SimpleGraph LaplacianSignless
open ConeSignlessSpectrum ConeMultiplicity ConeMultiplicityExact ConeTopEigen
open WheelSpectrum WheelMultiplicity WheelTable WheelSecondEigen
open RayleighVariational SignlessSecondEigen ConeSpectralGap

/-! ## The crossing, stated once and generally

`HermitianCharpoly.mem_image_eigenvalues_iff` is an iff between membership in the image of
Mathlib's enumeration and the existence of an eigenvector. Read in each direction it is exactly
what a cluster working in eigenvector form needs in order to say anything about an index, and
conversely. Both directions are one line; they are named here so the fence sentences have
something to point at. -/

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **EVERY INDEX OF MATHLIB'S ENUMERATION CARRIES AN EIGENVECTOR.** The forward direction of
`mem_image_eigenvalues_iff`, applied at `hA.eigenvalues i`, which is in the image because `i` is in
`univ`. -/
theorem exists_eigenvector_of_index {A : Matrix V V ℝ} (hA : A.IsHermitian) (i : V) :
    ∃ x : V → ℝ, x ≠ 0 ∧ A *ᵥ x = hA.eigenvalues i • x :=
  (HermitianCharpoly.mem_image_eigenvalues_iff hA _).1
    (Finset.mem_image_of_mem _ (Finset.mem_univ i))

/-- **AND EVERY EIGENVECTOR IS CARRIED BY AN INDEX.** The backward direction, with the image
membership unpacked. -/
theorem exists_index_of_eigenvector {A : Matrix V V ℝ} (hA : A.IsHermitian) {mu : ℝ}
    {x : V → ℝ} (hx0 : x ≠ 0) (hx : A *ᵥ x = mu • x) :
    ∃ i, hA.eigenvalues i = mu := by
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1
    ((HermitianCharpoly.mem_image_eigenvalues_iff hA mu).2 ⟨x, hx0, hx⟩)
  exact ⟨i, hi⟩

/-- A supremum over the enumeration is bounded by any bound on every index. Unfolds `topEigen`
once; there is no `topEigen_le` in the estate and this is the shape the comparison needs. -/
theorem topEigen_le_of_forall [Nonempty V] {A : Matrix V V ℝ} (hA : A.IsHermitian) {c : ℝ}
    (h : ∀ i, hA.eigenvalues i ≤ c) : topEigen hA ≤ c :=
  Finset.sup'_le _ _ fun i _ => h i

end General

/-! ## The wheel's Hermitian witness, and its fibres -/

section Wheel

variable (n : ℕ)

/-- The wheel's signless Laplacian is Hermitian — unit 89's witness at the cycle. -/
theorem wheelHerm : (signlessLap (coneGraph (cycleGraph (n + 3)))).IsHermitian :=
  ConeDimensionSum.signlessLap_coneGraph_isHermitian _

/-- **THE STEP UNIT 93 CALLED A ROUTE IS `rfl`.** `coneEig` is *defined* as the kernel that
`finrank_eigenspace_hermitian_eq_card_fibre` is stated about, so the cluster's eigenspace dimension
and the size of Mathlib's fibre are the same number with no transfer lemma in between. -/
theorem card_fibre_eq_finrank_coneEig (lam : ℝ) :
    Fintype.card {i // (wheelHerm n).eigenvalues i = lam}
      = Module.finrank ℝ (coneEig (cycleGraph (n + 3)) lam) :=
  (HermitianFibreCount.finrank_eigenspace_hermitian_eq_card_fibre (wheelHerm n) lam).symm

/-- **EXACTLY ONE INDEX CARRIES THE TOP**, off unit 86's simple top. -/
theorem card_fibre_hubRootPlus :
    Fintype.card {i // (wheelHerm n).eigenvalues i = hubRootPlus (n + 3) 2} = 1 := by
  have hc : Fintype.card (Fin (n + 3)) = n + 3 := Fintype.card_fin _
  have h := ConeTopEigen.finrank_coneEig_hubRootPlus (cycleGraph (n + 3)) (cycle_reg n)
  rw [hc] at h
  rw [card_fibre_eq_finrank_coneEig, h]

/-- **AND EXACTLY TWO CARRY `λ₂`**, off unit 107's unconditional multiplicity. -/
theorem card_fibre_rimVal_one (hn : n ≠ 0) :
    Fintype.card {i // (wheelHerm n).eigenvalues i = rimVal n 1} = 2 := by
  rw [card_fibre_eq_finrank_coneEig,
    WheelCollision.finrank_coneEig_rimVal_one_of_ne_zero hn]

end Wheel

/-! ## The top, in the estate's own terms -/

section Top

variable (n : ℕ)

/-- **THE ESTATE'S TOP EIGENVALUE IS UNIT 83'S NAMED ROOT.** `≤` because every index carries an
eigenvector and unit 86 bounds the eigenvector-form spectrum; `≥` because `hubRootPlus` is an
eigenvalue and therefore carried by some index. Both directions go through the fence lemma. -/
theorem topEigen_eq_hubRootPlus : topEigen (wheelHerm n) = hubRootPlus (n + 3) 2 := by
  have hc : Fintype.card (Fin (n + 3)) = n + 3 := Fintype.card_fin _
  have hgreat := ConeTopEigen.isGreatest_coneSpectrum (cycleGraph (n + 3)) (cycle_reg n)
  rw [hc] at hgreat
  refine le_antisymm (topEigen_le_of_forall _ fun i => ?_) ?_
  · obtain ⟨x, hx0, hx⟩ := exists_eigenvector_of_index (wheelHerm n) i
    exact hgreat.2 ⟨x, hx0, hx⟩
  · obtain ⟨x, hx0, hx⟩ := hgreat.1
    obtain ⟨i, hi⟩ := exists_index_of_eigenvector (wheelHerm n) hx0 hx
    rw [← hi]
    exact SignlessPerronSimple.le_topEigen (wheelHerm n) i

/-- So `topIdx` — the estate's chosen index at the top — carries `hubRootPlus`. -/
theorem eigenvalues_topIdx_wheel :
    (wheelHerm n).eigenvalues (topIdx (wheelHerm n)) = hubRootPlus (n + 3) 2 :=
  (eigenvalues_topIdx (wheelHerm n)).trans (topEigen_eq_hubRootPlus n)

/-- **AND IT IS THE ONLY SUCH INDEX**, because the fibre has exactly one element. This is where
unit 86's simplicity is spent: without it `secondEigen` could equal the top, which its own
docstring warns is the multiset convention. -/
theorem eq_topIdx_of_eigenvalues_eq {i : Option (Fin (n + 3))}
    (hi : (wheelHerm n).eigenvalues i = hubRootPlus (n + 3) 2) : i = topIdx (wheelHerm n) := by
  have hcard := card_fibre_hubRootPlus n
  have hsub : Subsingleton {j // (wheelHerm n).eigenvalues j = hubRootPlus (n + 3) 2} :=
    Fintype.card_le_one_iff_subsingleton.1 (by rw [hcard])
  exact congrArg Subtype.val
    (hsub.elim (⟨i, hi⟩ : {j // (wheelHerm n).eigenvalues j = hubRootPlus (n + 3) 2})
      ⟨topIdx (wheelHerm n), eigenvalues_topIdx_wheel n⟩)

end Top

/-! ## The deliverable: the estate's second eigenvalue, evaluated -/

section Second

variable (n : ℕ)

/-- **THE WHEEL'S `SignlessSecondEigen.secondEigen` IS `3 + 2cos(2π/N)`.** `≤` because every index
other than `topIdx` carries an eigenvector whose eigenvalue is not the top (by uniqueness) and unit
107 bounds those by `rimVal n 1`; `≥` because the `λ₂` fibre has two elements, so one of them is
not `topIdx`. Six units of eigenvector-form statements, now about the object the estate defines. -/
theorem secondEigen_eq_rimVal_one (hn : 1 ≤ n) :
    secondEigen (wheelHerm n) = rimVal n 1 := by
  refine le_antisymm (Finset.sup'_le _ _ fun i hi => ?_) ?_
  · have hine : i ≠ topIdx (wheelHerm n) := (Finset.mem_erase.1 hi).1
    obtain ⟨x, hx0, hx⟩ := exists_eigenvector_of_index (wheelHerm n) i
    have hne : (wheelHerm n).eigenvalues i ≠ hubRootPlus (n + 3) 2 := fun h =>
      hine (eq_topIdx_of_eigenvalues_eq n h)
    exact WheelCollision.le_rimVal_one_of_eigen_of_ne_uncond hn hx0 hx hne
  · have hcard := card_fibre_rimVal_one n (by omega)
    have hone : 1 < Fintype.card {j // (wheelHerm n).eigenvalues j = rimVal n 1} := by
      rw [hcard]; norm_num
    obtain ⟨⟨j, hj⟩, ⟨k, hk⟩, hjk⟩ := Fintype.exists_pair_of_one_lt_card hone
    rcases eq_or_ne j (topIdx (wheelHerm n)) with rfl | hjt
    · have hkt : k ≠ topIdx (wheelHerm n) := by
        intro h
        exact hjk (by simp [h])
      rw [← hk]
      exact le_secondEigen_of_ne (wheelHerm n) hkt
    · rw [← hj]
      exact le_secondEigen_of_ne (wheelHerm n) hjt

/-- **AND `L38170`'S GAP, ABOUT THE ESTATE'S OWN TWO OBJECTS.** Unit 112's bracket with both sides
rewritten: `topEigen − secondEigen` is `n − 1 = N − 4` to within `8/n`. -/
theorem sub_one_lt_topEigen_sub_secondEigen (hn : 1 ≤ n) :
    (n : ℝ) - 1 < topEigen (wheelHerm n) - secondEigen (wheelHerm n) := by
  rw [topEigen_eq_hubRootPlus, secondEigen_eq_rimVal_one n hn]
  exact sub_one_lt_hubRootPlus_sub_rimVal_one n

theorem topEigen_sub_secondEigen_le (hn : 1 ≤ n) :
    topEigen (wheelHerm n) - secondEigen (wheelHerm n) ≤ (n : ℝ) - 1 + 8 / (n : ℝ) := by
  rw [topEigen_eq_hubRootPlus, secondEigen_eq_rimVal_one n hn]
  exact hubRootPlus_sub_rimVal_one_le_sub_one_add_eight_div n hn

end Second

end WheelSecondFence
