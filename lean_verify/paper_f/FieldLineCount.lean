import FieldSimpleCriterion

/-!
# The number: the Gaussian field on a line of `n` sites has exactly `2^n` isometric symmetries

`FieldSimpleCriterion` proved that the symmetries of the Gaussian field on `boxGraph 1 (m+1)` — a
line of sites — are **exactly** the `±1` patterns on the eigenbasis, as a biconditional. That is a
description; **this is the count.** `UNLOCK_WATCHLIST` has carried *no cardinality, only
`Set.Infinite`* since `FieldRotationCount`, and half of it closes here.

**The count is a bijection, not an estimate.** `FieldSimpleSpectrum.signIsometry` sends a `Finset`
of sites to a symmetry; it is injective because two different sign sets differ at some eigenvector,
and surjective by the biconditional. So the symmetries are in bijection with `Finset (Site 1 (m+1))`
and there are `2^(m+1)` of them.

## What is proved

**`symmetries`** — the isometries whose pushforward fixes the field, as a `Set`. By
`FieldInvarianceCommutes` this is the honest object: membership is being a symmetry, not being a
member of some set contained in the symmetries (`ERRATUM 456`).

**`signIsometry_mem`, `signIsometry_injective`** — the sign isometries are symmetries, and distinct
sign sets give distinct ones. Injectivity is `smul_left_injective` against a unit eigenvector: if
the scalars agree at every `j` then the sets agree, since `-1 ≠ 1`.

**`signEquiv`** — hence a bijection `Finset (Site 1 (m+1)) ≃ symmetries m mass`, built from
`FieldSimpleCriterion.exists_signIsometry_eq` for surjectivity.

**`card_symmetries`** — **so the Gaussian field on a line of `m+1` sites has exactly `2^(m+1)`
isometric symmetries.** The Hermitian witness is produced inside the proof, not carried as a
hypothesis: the statement does not mention it, so it should not appear in its binders.

**`refl_mem`, `trans_mem`, `symm_mem`** — **and the symmetries are a group under composition**, at
the level of isometries rather than of matrices. Each is two lines from `Measure.map_map`; the
identity, composites and inverses of measure-preserving maps are measure-preserving for reasons that
have nothing to do with this graph. `FieldSymmetryGroup` proves the corresponding statement for
`symmetryMatrices` and keeps its own proof (`ERRATUM 337`).

## What is NOT here

**NO GROUP ISOMORPHISM, and no bundled group at all.** The three closure lemmas are the group law;
they are **not** assembled into a `Subgroup`, and `symmetries m mass` is **not** identified with
`(ZMod 2)^(m+1)`. `signEquiv` is a bijection of types, not a group isomorphism — nothing here checks
that it carries `Finset` symmetric difference to composition. **The `UNLOCK_WATCHLIST` item loses
its cardinality half and keeps its isomorphism half.** Not attempted, no cost claimed
(`ERRATUM 246`).

**NOTHING ABOUT `d ≥ 2`.** There the count is `Set.Infinite` and no finer statement exists. **No
dichotomy is proved** — nothing here says `d = 1` is the only case with a finite symmetry group.

**Only isometries**, inherited: a measure-preserving map that is not a linear isometry is not
counted, so this is **not** the cardinality of the full automorphism group of the measure.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. A symmetry
group counted exactly in finite volume is a shadow counted exactly.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `mass ≠ 0` is taken by `signIsometry_mem`,
`signEquiv` and `card_symmetries`; it is **not** taken by `signIsometry_injective`, which is about
`signIsometry` alone, nor by `refl_mem`, `trans_mem` or `symm_mem`, which are about measure-
preserving maps and hold at every mass — at `mass = 0` they say the isometries preserving a point
mass are a group, which is true and empty (`FieldMassNecessity`).

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldLineCount

open Matrix GraphLaplacian BoxGraph FieldSimpleSpectrum FieldSimpleCriterion MeasureTheory

/-! ## 1. The sign sets and the symmetries are in bijection -/

variable {m : ℕ} {mass : ℝ}

/-- **THE ISOMETRIC SYMMETRIES OF THE GAUSSIAN FIELD ON A LINE.** -/
def symmetries (m : ℕ) (mass : ℝ) :
    Set (EuclideanSpace ℝ (Site 1 (m + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Site 1 (m + 1))) :=
  {T | Measure.map T (gaussianField (boxGraph 1 (m + 1)) mass)
        = gaussianField (boxGraph 1 (m + 1)) mass}

theorem signIsometry_mem (hmass : mass ≠ 0)
    (hH : (green (boxGraph 1 (m + 1)) mass).IsHermitian) (s : Finset (Site 1 (m + 1))) :
    signIsometry hH s ∈ symmetries m mass :=
  gaussianField_map_signIsometry hmass hH s

theorem signIsometry_injective (hH : (green (boxGraph 1 (m + 1)) mass).IsHermitian) :
    Function.Injective (fun s : Finset (Site 1 (m + 1)) => signIsometry hH s) := by
  intro s t hst
  have hst' : signIsometry hH s = signIsometry hH t := hst
  ext j
  have hb : (hH.eigenvectorBasis j) ≠ 0 := by
    intro hz
    have h1 : ‖hH.eigenvectorBasis j‖ = 1 := (hH.eigenvectorBasis).orthonormal.1 j
    rw [hz, norm_zero] at h1
    exact absurd h1 (by norm_num)
  have happ : (if j ∈ s then (-1:ℝ) else 1) • hH.eigenvectorBasis j
      = (if j ∈ t then (-1:ℝ) else 1) • hH.eigenvectorBasis j := by
    rw [← signIsometry_eigenvectorBasis hH s j, ← signIsometry_eigenvectorBasis hH t j, hst']
  have hsc := smul_left_injective ℝ hb happ
  constructor
  · intro hjs
    by_contra hjt
    rw [if_pos hjs, if_neg hjt] at hsc
    norm_num at hsc
  · intro hjt
    by_contra hjs
    rw [if_neg hjs, if_pos hjt] at hsc
    norm_num at hsc

/-- **THE SIGN SETS AND THE SYMMETRIES ARE IN BIJECTION.** -/
noncomputable def signEquiv (hmass : mass ≠ 0)
    (hH : (green (boxGraph 1 (m + 1)) mass).IsHermitian) :
    Finset (Site 1 (m + 1)) ≃ symmetries m mass :=
  Equiv.ofBijective (fun s => ⟨signIsometry hH s, signIsometry_mem hmass hH s⟩)
    ⟨fun _ _ h => signIsometry_injective hH (congrArg Subtype.val h),
     fun T => (exists_signIsometry_eq hH
       ((gaussianField_map_iff_signs_line hmass hH T.1).mp T.2)).imp
         fun _ hs => Subtype.ext hs⟩

/-- **THE GAUSSIAN FIELD ON A LINE OF `m+1` SITES HAS EXACTLY `2^(m+1)` ISOMETRIC SYMMETRIES.**
The Hermitian witness is produced inside, not carried: the statement does not mention it. -/
theorem card_symmetries (hmass : mass ≠ 0) :
    Nat.card (symmetries m mass) = 2 ^ (m + 1) := by
  rw [← Nat.card_congr (signEquiv hmass (green_posDef _ hmass).isHermitian),
    Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, pow_one]

/-! ## 2. And they are a group -/

theorem refl_mem : LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Site 1 (m + 1)))
    ∈ symmetries m mass := by
  simp [symmetries]

theorem trans_mem {S T : EuclideanSpace ℝ (Site 1 (m + 1)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Site 1 (m + 1))}
    (hS : S ∈ symmetries m mass) (hT : T ∈ symmetries m mass) :
    S.trans T ∈ symmetries m mass := by
  simp only [symmetries, Set.mem_setOf_eq] at hS hT ⊢
  rw [show (⇑(S.trans T)) = ⇑T ∘ ⇑S from rfl,
    ← Measure.map_map T.continuous.measurable S.continuous.measurable, hS, hT]

theorem symm_mem {T : EuclideanSpace ℝ (Site 1 (m + 1)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Site 1 (m + 1))}
    (hT : T ∈ symmetries m mass) : T.symm ∈ symmetries m mass := by
  have h1 : Measure.map (⇑T.symm) (Measure.map (⇑T)
        (gaussianField (boxGraph 1 (m + 1)) mass))
      = gaussianField (boxGraph 1 (m + 1)) mass := by
    rw [Measure.map_map T.symm.continuous.measurable T.continuous.measurable]
    simp
  rw [hT] at h1
  exact h1

end FieldLineCount
