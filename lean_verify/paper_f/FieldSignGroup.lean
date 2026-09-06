import FieldLineCount

/-!
# The `2^|V|` was a cardinality; this is the group — `(ℤ/2)^V` at a simple spectrum

⚠ **GENERALISED IN PLACE, 2026-09-06, together with `FieldLineCount` and
`FieldSimpleCriterion`.** This file was written for `boxGraph 1 (m+1)` — a line — and its group
section now takes an arbitrary finite graph whose propagator has a simple spectrum. **No proof
changed**; the line appeared only in the statements. `signMulEquivLine` recovers the original
theorem in one line. The original title read *"this is the group — `(ℤ/2)^(m+1)` on a line"*.

`FieldLineCount` counted the isometric symmetries of the Gaussian field at **exactly `2^|V|`**, and
fenced what it had not done, in these words: *no bundled `Subgroup`, and no group isomorphism —
`signEquiv` is a bijection of types and nothing checks that it carries `Finset` symmetric difference
to composition, which is what would make it `(ZMod 2)^(m+1)` as a group.* **All three are done
here.**

## What is proved

**`signIsometry_empty`, `signFlip_trans`, `signIsometry_symmDiff`, `signIsometry_mul`** — **THE
GROUP LAW IS SYMMETRIC DIFFERENCE.** Flipping the signs on `s` and then on `t` flips the signs on
`s ∆ t`, and the empty set is the identity. The proof goes through `FieldSignFlip.signFlip`, where
the statement is coordinatewise and a four-case split settles it; the eigenbasis conjugation on
either side cancels.

**`signIsometry_trans_self`** — **so every sign symmetry is an involution**: the group has exponent
two. One line from the two above, since `s ∆ s = ⊥`.

**`bits`, `bits_apply`, `bits_empty`, `bits_symmDiff`, `bitsEquiv`, `bitsEquiv_symm_add`,
`bitsEquiv_symm_zero`, `eq_zero_or_one`** — the indicator of a finite set as a function to
`ZMod 2`, a bijection `Finset V ≃ (V → ZMod 2)`, and **it carries symmetric difference to
addition**. `1 + 1 = 0` is exactly why the indicator of `s ∆ t` is the sum of the indicators.

**`symmetriesSubgroup`, `mem_symmetriesSubgroup`** — the isometric symmetries as a **`Subgroup`**,
on **any** finite graph, from `FieldLineCount`'s `refl_mem`, `trans_mem` and `symm_mem`. The group's
multiplication is `e₁ * e₂ = e₂.trans e₁`, which is why `mul_mem'` takes its two arguments the other
way round. **This needs neither a simple spectrum nor a non-zero mass.**

**`signHom`, `signHom_apply`, `signMulEquiv`** — **THE SYMMETRY GROUP OF A GAUSSIAN FIELD WHOSE
PROPAGATOR HAS A SIMPLE SPECTRUM IS `(ℤ/2)^V`**, on any finite graph, as a `MulEquiv` and not merely
a set of that size. Injectivity is `FieldLineCount.signIsometry_injective` through the two
bijections; surjectivity is `FieldSimpleCriterion.exists_signIsometry_eq`; `MulEquiv.ofBijective`
assembles them. **`signMulEquivLine`** is the line instance.

## What is NOT here

**THE EXPONENT IS THE VERTEX TYPE.** The group is `Multiplicative (V → ZMod 2)`, and for the line
`Site 1 (k + 1)`. That `Site 1 (k + 1)` has `k+1` elements is what
`FieldLineCount.card_symmetries_line` uses to reach `2^(k+1)`, and **no re-indexing to
`Fin (k+1) → ZMod 2` is constructed here**. Not attempted, no cost claimed (`ERRATUM 246`).

**ONLY AT A SIMPLE SPECTRUM, AND ONLY THE LINE DISCHARGES IT.** `signMulEquiv` takes
`Function.Injective hH.eigenvalues`, and `FieldSimpleCriterion.eigenvalues_injective_line` is still
the estate's **only** proof that any graph has one. For a box in two or more dimensions the symmetry
set is `Set.Infinite` (`FieldRotationCount`) and there is no group statement of any kind. **No
dichotomy is proved** — nothing here says a simple spectrum is the only case with a finite symmetry
group.

**ONLY ISOMETRIC SYMMETRIES**, inherited. `FieldSqrtConjugation.exists_nonIsometric` exhibits a
linear symmetry of the field that is not an isometry, so this group is a **proper** subgroup of the
linear symmetry group that `FieldSymmetryIso.conjSqEquiv` describes. **No relation between the two
is drawn here** — no inclusion of `symmetriesSubgroup` into `linSym`, and no index.
⚠ **PARTLY SUPERSEDED THE NEXT UNIT, kept as written** (`ERRATUM 94`):
`FieldSymmetryInclusion.symmetryMatrices_eq` draws the relation **at the level of matrices** —
`symmetryMatrices G m = {L ∈ linSym G m | Lᵀ L = 1}`, with no hypothesis on the mass — and
`symmetryMatrices_ssubset_linSym_line` makes the inclusion **strict** on a line. **The clause is
still true as stated**: `symmetriesSubgroup` is a group of *linear isometry equivalences* and
`linSymGL` a subgroup of `GL V ℝ`, and **no homomorphism between those two objects is
constructed**. **And there is still no index.**

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. A symmetry
group named exactly, in finite volume, is a shadow named exactly.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): a non-zero mass is taken by `signHom`,
`signHom_apply`, `signMulEquiv` and `signMulEquivLine` — **four of the nineteen** — and only because
`FieldLineCount.signIsometry_mem` needs it to know a sign isometry preserves the *measure*.
**Simplicity of the spectrum** is taken by `signMulEquiv` **alone**; `signMulEquivLine` does not
take it but **discharges** it, through `FieldSimpleCriterion.eigenvalues_injective_line`, and the
`Subgroup` needs neither it nor the mass. **The entire group law is free of both**:
`signIsometry_symmDiff`, `signIsometry_mul` and `signIsometry_trans_self` hold on **every** graph at
**every** mass, and take
only a Hermitian witness. **Eight** declarations mention no graph, no measure and no mass at all —
the **seven** of the `Bits` section plus `bitsEquiv_symm_zero`, which sits in the last section only
because that is where it is used. Five of the eight need `[DecidableEq V]` alone; `bitsEquiv`,
`bitsEquiv_symm_add` and `bitsEquiv_symm_zero` add `[Fintype V]`, because the inverse filters over
`Finset.univ`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldSignGroup

open Matrix GraphLaplacian BoxGraph FieldSimpleSpectrum FieldLineCount MeasureTheory

section Sign

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-- The empty sign set is the identity. -/
theorem signIsometry_empty (hH : (green G m).IsHermitian) :
    signIsometry hH (∅ : Finset V) = LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ V) := by
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply Module.Basis.ext hH.eigenvectorBasis.toBasis
  intro j
  simp [signIsometry_eigenvectorBasis]

/-- Composing two sign flips flips exactly the symmetric difference. -/
theorem signFlip_trans (s t : Finset V) :
    (FieldSignFlip.signFlip s).trans (FieldSignFlip.signFlip t)
      = FieldSignFlip.signFlip (symmDiff s t) := by
  refine LinearIsometryEquiv.ext fun x => ?_
  ext v
  simp only [LinearIsometryEquiv.trans_apply, FieldSignFlip.signFlip_apply]
  by_cases hs : v ∈ s <;> by_cases ht : v ∈ t <;> simp [Finset.mem_symmDiff, hs, ht]

/-- **THE GROUP LAW IS SYMMETRIC DIFFERENCE.** -/
theorem signIsometry_symmDiff (hH : (green G m).IsHermitian) (s t : Finset V) :
    signIsometry hH (symmDiff s t)
      = (signIsometry hH s).trans (signIsometry hH t) := by
  refine LinearIsometryEquiv.ext fun x => ?_
  simp only [signIsometry, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, ← signFlip_trans]

/-- The same, in the group's own multiplication (`e₁ * e₂ = e₂.trans e₁`). -/
theorem signIsometry_mul (hH : (green G m).IsHermitian) (s t : Finset V) :
    signIsometry hH s * signIsometry hH t = signIsometry hH (symmDiff s t) := by
  rw [symmDiff_comm, signIsometry_symmDiff]
  rfl

/-- **SO EVERY SIGN SYMMETRY IS AN INVOLUTION**: the group has exponent two. -/
theorem signIsometry_trans_self (hH : (green G m).IsHermitian) (s : Finset V) :
    (signIsometry hH s).trans (signIsometry hH s)
      = LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ V) := by
  rw [← signIsometry_symmDiff, symmDiff_self, Finset.bot_eq_empty, signIsometry_empty]

end Sign

/-! ## 2. `Finset V` and `V → ZMod 2`, symmetric difference to addition -/

section Bits

variable {V : Type*} [DecidableEq V]

/-- The indicator of a finite set, as a function to `ZMod 2`. -/
def bits (s : Finset V) : V → ZMod 2 := fun v => if v ∈ s then 1 else 0

theorem bits_apply (s : Finset V) (v : V) : bits s v = if v ∈ s then 1 else 0 := rfl

theorem eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide +kernel

/-- **THE INDICATOR CARRIES SYMMETRIC DIFFERENCE TO ADDITION.** -/
theorem bits_symmDiff (s t : Finset V) : bits (symmDiff s t) = bits s + bits t := by
  funext v
  rw [Pi.add_apply, bits_apply, bits_apply, bits_apply]
  by_cases hs : v ∈ s <;> by_cases ht : v ∈ t
  · rw [if_neg (by simp [Finset.mem_symmDiff, hs, ht]), if_pos hs, if_pos ht]
    decide +kernel
  · rw [if_pos (by simp [Finset.mem_symmDiff, hs, ht]), if_pos hs, if_neg ht]
    decide +kernel
  · rw [if_pos (by simp [Finset.mem_symmDiff, hs, ht]), if_neg hs, if_pos ht]
    decide +kernel
  · rw [if_neg (by simp [Finset.mem_symmDiff, hs, ht]), if_neg hs, if_neg ht]
    decide +kernel

/-- **AND IT IS A BIJECTION**, `Finset V ≃ (V → ZMod 2)`. -/
def bitsEquiv [Fintype V] : Finset V ≃ (V → ZMod 2) where
  toFun := bits
  invFun f := Finset.univ.filter (fun v => f v = 1)
  left_inv s := by
    ext v
    simp [bits_apply]
  right_inv f := by
    funext v
    rw [bits_apply]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases eq_zero_or_one (f v) with h | h <;> simp [h]

theorem bits_empty : bits (∅ : Finset V) = 0 := by
  funext v
  rw [bits_apply]
  simp

theorem bitsEquiv_symm_add [Fintype V] (f g : V → ZMod 2) :
    bitsEquiv.symm (f + g) = symmDiff (bitsEquiv.symm f) (bitsEquiv.symm g) := by
  refine bitsEquiv.injective ?_
  rw [Equiv.apply_symm_apply]
  change f + g = bits (symmDiff (bitsEquiv.symm f) (bitsEquiv.symm g))
  rw [bits_symmDiff]
  change f + g = bitsEquiv (bitsEquiv.symm f) + bitsEquiv (bitsEquiv.symm g)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end Bits

/-! ## 3. The symmetry group, bundled, at a simple spectrum -/

section Group

open BoxGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-- **THE ISOMETRIC SYMMETRIES AS A `Subgroup`**, on any finite graph. -/
def symmetriesSubgroup (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) :
    Subgroup (EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) where
  carrier := symmetries G m
  one_mem' := refl_mem
  mul_mem' ha hb := trans_mem hb ha
  inv_mem' h := symm_mem h

theorem mem_symmetriesSubgroup {T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V} :
    T ∈ symmetriesSubgroup G m ↔ T ∈ symmetries G m := Iff.rfl

theorem bitsEquiv_symm_zero {W : Type*} [Fintype W] [DecidableEq W] :
    bitsEquiv.symm (0 : W → ZMod 2) = (∅ : Finset W) := by
  rw [Equiv.symm_apply_eq]
  exact bits_empty.symm

/-- The sign group as a homomorphism into the symmetries. -/
noncomputable def signHom (hm : m ≠ 0) (hH : (green G m).IsHermitian) :
    Multiplicative (V → ZMod 2) →* symmetriesSubgroup G m where
  toFun f := ⟨signIsometry hH (bitsEquiv.symm (Multiplicative.toAdd f)),
    mem_symmetriesSubgroup.mpr (signIsometry_mem hm hH _)⟩
  map_one' := by
    refine Subtype.ext ?_
    have h1 : Multiplicative.toAdd (1 : Multiplicative (V → ZMod 2)) = 0 := rfl
    simp only [OneMemClass.coe_one, h1]
    rw [bitsEquiv_symm_zero, signIsometry_empty]
    rfl
  map_mul' f g := by
    refine Subtype.ext ?_
    have hfg : Multiplicative.toAdd (f * g)
        = Multiplicative.toAdd f + Multiplicative.toAdd g := rfl
    simp only [hfg]
    rw [bitsEquiv_symm_add, ← signIsometry_mul]
    rfl

theorem signHom_apply (hm : m ≠ 0) (hH : (green G m).IsHermitian)
    (f : Multiplicative (V → ZMod 2)) :
    ((signHom hm hH f : symmetriesSubgroup G m) :
        EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V)
      = signIsometry hH (bitsEquiv.symm (Multiplicative.toAdd f)) := rfl

/-- **THE SYMMETRY GROUP OF A GAUSSIAN FIELD WHOSE PROPAGATOR HAS A SIMPLE SPECTRUM IS
`(ℤ/2)^V`** — on any finite graph, and not merely a set of that size. -/
noncomputable def signMulEquiv (hm : m ≠ 0) (hH : (green G m).IsHermitian)
    (hsimple : Function.Injective hH.eigenvalues) :
    Multiplicative (V → ZMod 2) ≃* symmetriesSubgroup G m :=
  MulEquiv.ofBijective (signHom hm hH) (by
    constructor
    · intro f g hfg
      have h : signIsometry hH (bitsEquiv.symm (Multiplicative.toAdd f))
          = signIsometry hH (bitsEquiv.symm (Multiplicative.toAdd g)) := congrArg Subtype.val hfg
      exact Multiplicative.toAdd.injective
        (bitsEquiv.symm.injective (signIsometry_injective hH h))
    · rintro ⟨T, hT⟩
      obtain ⟨s, hs⟩ := FieldSimpleCriterion.exists_signIsometry_eq hH
        ((FieldSimpleCriterion.gaussianField_map_iff_signs hm hH hsimple T).mp
          (mem_symmetriesSubgroup.mp hT))
      refine ⟨Multiplicative.ofAdd (bits s), Subtype.ext ?_⟩
      have hoa : Multiplicative.toAdd (Multiplicative.ofAdd (bits s)) = bits s := rfl
      have hbs : bitsEquiv.symm (bits s) = s := bitsEquiv.symm_apply_apply s
      rw [signHom_apply, hoa, hbs, hs])

/-- **THE LINE IS THE INSTANCE.** -/
noncomputable def signMulEquivLine {k : ℕ} {mass : ℝ} (hmass : mass ≠ 0) :
    Multiplicative (Site 1 (k + 1) → ZMod 2)
      ≃* symmetriesSubgroup (boxGraph 1 (k + 1)) mass :=
  signMulEquiv hmass _
    (FieldSimpleCriterion.eigenvalues_injective_line hmass
      (green_posDef (boxGraph 1 (k + 1)) hmass).isHermitian)

end Group



end FieldSignGroup
