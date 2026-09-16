/-
  HermitianSignatureClassification: the classification as one BICONDITIONAL, and the
  ⋆-structures on `Mₙ(ℂ)` COUNTED up to conjugacy

  SPINE LINK L11 — `UNLOCK_WATCHLIST` line 39103, the last two clauses of item (1)'s residue.

  WHERE THIS PICKS UP. Unit 74 closed the residue's headline — equal signature gives conjugate
  ⋆-structures — and named two things it had not done, in its own *what is not claimed* list:
  the two directions were **not packaged as one `iff`**, because their hypotheses differ, and
  **nothing counted the ⋆-structures**, because no twist was exhibited beyond `±1` and
  `diag(1,-1)`. The watchlist entry says the same thing in its own words: *nothing counts the
  ⋆-structures on `Mₙ(ℂ)` up to conjugacy*. Both are closed here.

  WHAT IS PROVED.
  * **`signature_neg`** — the signature of `-P` is the signature of `P` with its halves
    exchanged, off unit 70's `signature_real_smul_neg` at `r = -1`. Small, and it is the whole
    reason the biconditional can be stated at all. **The companion fact that `-P` is Hermitian
    is unit 69's `StarStructureTwistFibre.neg_hermitian`, consumed and not re-proved** — this
    file's first draft re-proved it under the same name and `dupname_scan` and `newnames_scan`
    both caught it before the commit (`ERRATUM 614`).
  * **`conjugate_of_signature_swap`** — **THE MISSING HALF, and it is not bookkeeping.** Unit 74
    proved *equal signature ⇒ conjugate*; the converse it is paired with delivers *equal OR
    exchanged*, so an `iff` needs the EXCHANGED case of the forward direction too, and nothing
    proved it. It holds because unit 70's `hermitianStar_neg` makes `P` and `-P` present the
    same ⋆-structure while `signature_neg` exchanges the halves: run unit 74's theorem at `-P`
    and rewrite. **Unit 74 called this step bookkeeping and it is one theorem short of that** —
    the sign trick is the content, and without it the `iff` is false as stated for `P` alone.
  * **`conjugate_iff_signature`** — **THE BICONDITIONAL.** Two ⋆-structures presented by
    Hermitian units are conjugate **if and only if** their signatures are equal or exchanged.
    Both directions now have the same sides.
  * **`usignature` and `conjugate_iff_usignature`** — **the invariant in the form that makes it
    complete on the nose.** An unordered pair, `Sym2 ℕ`, is exactly the quotient the exchange
    forces; `Sym2.mk_eq_mk_iff` turns *equal or exchanged* into EQUALITY, and the classification
    becomes `Conjugate s t ↔ usignature = usignature`. `usignature_eq_of_star_eq` says the
    invariant is a function of the ⋆-STRUCTURE and not merely of the twist, which is what unit
    69's fibre computation was for. **This is the `ℝˣ`-orbit statement unit 74 deferred**, and
    the right target turned out to be `Sym2` rather than a quotient type.
  * **`setTwist` and `signature_setTwist`** — **a twist at EVERY signature, from a `Finset`.** The
    `±1` diagonal supported on `S` has signature `(2·#S, 2·#Sᶜ)`. Indexing by a SET rather than
    by a threshold is what makes the count free: the positive-entry filter IS `S`, by
    `by_cases` on membership, with no counting argument anywhere.
  * **`exists_twist_signature`** — every `(2p, 2(n-p))` with `p ≤ n` is achieved, via
    `Finset.exists_subset_card_eq`. **Before this the estate exhibited three signature values;
    now it exhibits all of them.**
  * **`mem_achievable_of_unit`** — and nothing else is achieved: an invertible Hermitian twist's
    signature is `(2p, 2(n-p))` for some `p ≤ n`, off unit 73's formula and `signature_add_of_unit`.
  * **`card_achievable`** — **THE COUNT: there are exactly `n/2 + 1` ⋆-structures on `Mₙ(ℂ)` up
    to conjugacy.** The achievable unordered signatures are `s(2p, 2(n-p))` for `p ≤ n`, the map
    collapses `p` with `n - p` and nothing else, and restricting to `p ≤ n/2` is injective. So
    `M₂(ℂ)` has two — which is unit 71's pair, and unit 71's inequivalence theorem is the `n = 2`
    case of a count rather than an isolated example. `M₄(ℂ)` has three.

  WHAT IS **NOT** CLAIMED.
  * **The count is of CONJUGACY classes, not of ⋆-structures.** There are infinitely many
    ⋆-structures on `Mₙ(ℂ)` for `n ≥ 2` — unit 69's fibre is an `ℝˣ`-orbit of twists and the
    twists themselves form a continuum. `n/2 + 1` counts them modulo conjugation by an algebra
    automorphism, which is the classification's own equivalence.
  * **No eigenvalue is EVALUATED anywhere, still.** `signature_setTwist` computes a signature
    without one, by the same two inequalities unit 73 used; the general formula continues to
    consume a noncomputable eigenvalue list. So the estate now exhibits every signature value
    and has evaluated no spectrum.
  * **Nothing over `ℝ` or `ℍ`.** The count `n/2 + 1` is the complex answer; the real and
    quaternionic classifications have different shapes and neither is touched.
  * **Nothing about the cascade is cut.** `a·b·c = 16` keeps every alternative
    (`ASSUMPTIONS_LEDGER` 5, 10, 11, 30, 35). **A COUNT of the ⋆-structures on `M₁₆(ℂ)` — nine of
    them — still prefers no factorisation**: knowing how many there are, and what separates
    them, says nothing about which one a cascade supplies. The residue is closed; the cascade
    question it was a residue OF is not, and never was going to be by this route.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import HermitianSignatureComplete

namespace HermitianSignatureClassification

open Matrix HermitianRealForm StarStructureTwistFibre StarStructureInequivalent
open HermitianSignatureEigenvalues HermitianSignatureComplete

noncomputable section

variable {n : ℕ}

/-! ### The negative twist

`-P` being Hermitian when `P` is comes from `StarStructureTwistFibre.neg_hermitian`, which unit
69 wrote for exactly this purpose — its docstring says it exists so that `hermitianStar_neg`'s
hypothesis can be met. **This file's first draft re-proved it under the same name**
(`ERRATUM 614`); the duplicate is deleted and the original consumed. -/

/-- Negating the twist EXCHANGES the two halves of the signature. -/
theorem signature_neg (P : Matrix (Fin n) (Fin n) ℂ) :
    signature (-P) = (signature P).swap := by
  have h : (-P) = ((-1 : ℝ) : ℂ) • P := by simp
  rw [h, signature_real_smul_neg P (by norm_num : (-1 : ℝ) < 0)]

/-! ### The biconditional -/

/-- **THE EXCHANGED CASE OF THE FORWARD DIRECTION.** If two signatures are exchanged rather
than equal, the ⋆-structures are still conjugate: `P` and `-P` present the same structure
(`hermitianStar_neg`) and negation exchanges the halves, so unit 74's theorem applies at `-P`. -/
theorem conjugate_of_signature_swap [NeZero n] (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ))
    (h : signature (Q : Matrix (Fin n) (Fin n) ℂ)
        = (signature (P : Matrix (Fin n) (Fin n) ℂ)).swap) :
    Conjugate (hermitianStar P hP) (hermitianStar Q hQ) := by
  have hnP := StarStructureTwistFibre.neg_hermitian P hP
  have hsig : signature (Q : Matrix (Fin n) (Fin n) ℂ)
      = signature ((-P : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Units.val_neg, signature_neg, h]
  have hconj := conjugate_of_signature_eq Q (-P) hQ hnP hsig
  rwa [hermitianStar_neg P hP hnP] at hconj

/-- **THE CLASSIFICATION AS ONE STATEMENT.** Two ⋆-structures on `Mₙ(ℂ)` presented by Hermitian
units are conjugate by an algebra automorphism **if and only if** their signatures are equal or
exchanged. The forward direction is unit 71's; the converse is unit 74's headline together with
`conjugate_of_signature_swap` above. -/
theorem conjugate_iff_signature [NeZero n] (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ)) :
    Conjugate (hermitianStar P hP) (hermitianStar Q hQ)
      ↔ signature (Q : Matrix (Fin n) (Fin n) ℂ) = signature (P : Matrix (Fin n) (Fin n) ℂ)
        ∨ signature (Q : Matrix (Fin n) (Fin n) ℂ)
            = (signature (P : Matrix (Fin n) (Fin n) ℂ)).swap := by
  refine ⟨signature_eq_or_swap_of_conjugate P Q hP hQ, ?_⟩
  rintro (h | h)
  · exact conjugate_of_signature_eq Q P hQ hP h
  · exact conjugate_of_signature_swap P Q hP hQ h

/-! ### The invariant as an unordered pair -/

/-- The signature as an UNORDERED pair. The exchange that `hermitianStar_neg` forces is exactly
the quotient `Sym2` takes, so this is the invariant in the form that is complete on the nose. -/
def usignature (P : Matrix (Fin n) (Fin n) ℂ) : Sym2 ℕ :=
  s((signature P).1, (signature P).2)

/-- Unordered-pair equality IS *equal or exchanged*. -/
theorem usignature_eq_iff (P Q : Matrix (Fin n) (Fin n) ℂ) :
    usignature P = usignature Q ↔ signature P = signature Q ∨ signature P = (signature Q).swap :=
  Sym2.mk_eq_mk_iff

/-- The unordered signature cannot see the sign of the twist. -/
theorem usignature_neg (P : Matrix (Fin n) (Fin n) ℂ) : usignature (-P) = usignature P := by
  rw [usignature_eq_iff]
  exact Or.inr (signature_neg P)

/-- The unordered signature is a function of the ⋆-STRUCTURE, not merely of the twist — which
is what unit 69's fibre computation was for. -/
theorem usignature_eq_of_star_eq [NeZero n] (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ))
    (h : hermitianStar P hP = hermitianStar Q hQ) :
    usignature (P : Matrix (Fin n) (Fin n) ℂ) = usignature (Q : Matrix (Fin n) (Fin n) ℂ) := by
  rw [usignature_eq_iff]
  exact signature_eq_or_swap_of_star_eq P Q hP hQ h

/-- **THE CLASSIFICATION, WITH BOTH SIDES AN EQUALITY.** -/
theorem conjugate_iff_usignature [NeZero n] (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ)) :
    Conjugate (hermitianStar P hP) (hermitianStar Q hQ)
      ↔ usignature (Q : Matrix (Fin n) (Fin n) ℂ)
          = usignature (P : Matrix (Fin n) (Fin n) ℂ) := by
  rw [conjugate_iff_signature P Q hP hQ, usignature_eq_iff]

/-! ### A twist at every signature -/

/-- The `±1` vector supported on a finite set of coordinates. -/
def setVec (S : Finset (Fin n)) : Fin n → ℝ := fun i => if i ∈ S then 1 else -1

theorem setVec_ne_zero (S : Finset (Fin n)) (i : Fin n) : ((setVec S i : ℝ) : ℂ) ≠ 0 := by
  rw [setVec]
  by_cases h : i ∈ S <;> simp [h]

/-- The `±1` diagonal twist supported on `S`. -/
def setTwist (S : Finset (Fin n)) : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  diagUnit (fun i => ((setVec S i : ℝ) : ℂ)) (setVec_ne_zero S)

theorem setTwist_val (S : Finset (Fin n)) :
    ((setTwist S : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = Matrix.diagonal fun i => ((setVec S i : ℝ) : ℂ) :=
  diagUnit_val _ _

theorem setTwist_hermitian (S : Finset (Fin n)) :
    ((setTwist S : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
      = ((setTwist S : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
  rw [setTwist_val, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp

/-- **A SIGNATURE COMPUTED WITHOUT A COUNTING ARGUMENT.** Indexing the sign pattern by a SET
rather than by a threshold makes the positive-entry filter literally `S`. -/
theorem signature_setTwist (S : Finset (Fin n)) :
    signature ((setTwist S : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = (2 * S.card, 2 * (n - S.card)) := by
  have hpos : (Finset.univ.filter fun i => 0 < setVec S i) = S := by
    ext i
    rw [Finset.mem_filter, setVec]
    by_cases h : i ∈ S <;> simp [h]
  have hneg : (Finset.univ.filter fun i => setVec S i < 0) = Sᶜ := by
    ext i
    rw [Finset.mem_filter, Finset.mem_compl, setVec]
    by_cases h : i ∈ S <;> simp [h]
  rw [setTwist_val, signature_diagonal, hpos, hneg]
  congr 1
  simpa using Finset.card_compl S

/-- **EVERY signature is achieved**, not just the three the estate had exhibited. -/
theorem exists_twist_signature (p : ℕ) (hp : p ≤ n) :
    ∃ (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
      (_ : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ)),
        signature (P : Matrix (Fin n) (Fin n) ℂ) = (2 * p, 2 * (n - p)) := by
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (n := p) (by simpa using hp)
  exact ⟨setTwist S, setTwist_hermitian S, by rw [signature_setTwist, hS]⟩

/-! ### The count -/

/-- The unordered signatures achievable on `Mₙ(ℂ)`. -/
def achievable (n : ℕ) : Finset (Sym2 ℕ) :=
  (Finset.range (n + 1)).image fun p => s(2 * p, 2 * (n - p))

/-- Nothing outside `achievable n` occurs: an invertible Hermitian twist's signature is
`(2p, 2(n-p))` for some `p ≤ n`, by unit 73's formula and `signature_add_of_unit`. -/
theorem mem_achievable_of_unit (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ).IsHermitian) :
    usignature (P : Matrix (Fin n) (Fin n) ℂ) ∈ achievable n := by
  have hsum := signature_add_of_unit P hP
  have hform := signature_isHermitian (P : Matrix (Fin n) (Fin n) ℂ) hP
  rw [achievable, Finset.mem_image]
  refine ⟨(Finset.univ.filter fun i => 0 < hP.eigenvalues i).card, ?_, ?_⟩
  · rw [Finset.mem_range]
    rw [hform] at hsum
    omega
  · rw [usignature, hform]
    rw [hform] at hsum
    have : 2 * (n - (Finset.univ.filter fun i => 0 < hP.eigenvalues i).card)
        = 2 * (Finset.univ.filter fun i => hP.eigenvalues i < 0).card := by omega
    rw [this]

/-- Every element of `achievable n` is achieved. -/
theorem exists_twist_usignature (u : Sym2 ℕ) (hu : u ∈ achievable n) :
    ∃ (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
      (_ : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ)),
        usignature (P : Matrix (Fin n) (Fin n) ℂ) = u := by
  rw [achievable, Finset.mem_image] at hu
  obtain ⟨p, hp, rfl⟩ := hu
  rw [Finset.mem_range] at hp
  obtain ⟨P, hP, hsig⟩ := exists_twist_signature (n := n) p (by omega)
  exact ⟨P, hP, by rw [usignature, hsig]⟩

/-- **THE COUNT.** There are exactly `n/2 + 1` ⋆-structures on `Mₙ(ℂ)` up to conjugacy. -/
theorem card_achievable : (achievable n).card = n / 2 + 1 := by
  have hset : achievable n = (Finset.range (n / 2 + 1)).image fun p => s(2 * p, 2 * (n - p)) := by
    apply Finset.Subset.antisymm
    · intro u hu
      rw [achievable, Finset.mem_image] at hu
      obtain ⟨p, hp, rfl⟩ := hu
      rw [Finset.mem_range] at hp
      rw [Finset.mem_image]
      by_cases hle : p ≤ n / 2
      · exact ⟨p, Finset.mem_range.2 (by omega), rfl⟩
      · have hbound : n - p < n / 2 + 1 := by omega
        have hnp : n - (n - p) = p := by omega
        refine ⟨n - p, Finset.mem_range.2 hbound, ?_⟩
        rw [hnp, Sym2.eq_swap]
    · intro u hu
      rw [Finset.mem_image] at hu
      obtain ⟨p, hp, rfl⟩ := hu
      rw [Finset.mem_range] at hp
      rw [achievable, Finset.mem_image]
      exact ⟨p, Finset.mem_range.2 (by omega), rfl⟩
  rw [hset, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb h
  rw [Finset.mem_coe, Finset.mem_range] at ha hb
  dsimp only at h
  rw [Sym2.eq_iff] at h
  omega

/-- `M₂(ℂ)` has exactly two ⋆-structures up to conjugacy — so unit 71's inequivalence is the
`n = 2` case of a count, not an isolated pair. -/
theorem card_achievable_two : (achievable 2).card = 2 := by
  rw [card_achievable]

/-- `M₄(ℂ)` has exactly three. -/
theorem card_achievable_four : (achievable 4).card = 3 := by
  rw [card_achievable]

end

end HermitianSignatureClassification
