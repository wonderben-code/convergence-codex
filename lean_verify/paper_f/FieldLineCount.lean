import FieldSimpleCriterion

/-!
# The number: a simple propagator spectrum gives exactly `2^|V|` isometric symmetries

⚠ **GENERALISED IN PLACE, 2026-09-06.** This file was written for `boxGraph 1 (m+1)` — a line — and
every declaration in it now takes an arbitrary finite graph. **Nothing in the proofs changed**: the
line appeared only in the statements, and the one place it did work — discharging the simplicity of
the spectrum — is now a hypothesis, with `card_symmetries_line` recovering the original theorem in
three rewrites. The original title read *"the Gaussian field on a line of `n` sites has exactly
`2^n` isometric symmetries"*, which is `card_symmetries_line`.

`FieldSimpleCriterion.gaussianField_map_iff_signs` proves that the symmetries of the Gaussian field
on a graph whose propagator has a **simple spectrum** are **exactly** the `±1` patterns on the
eigenbasis, as a biconditional. That is a description; **this is the count.** `UNLOCK_WATCHLIST` has
carried *no cardinality, only `Set.Infinite`* since `FieldRotationCount`, and half of it closes
here.

**The count is a bijection, not an estimate.** `FieldSimpleSpectrum.signIsometry` sends a `Finset`
of sites to a symmetry; it is injective because two different sign sets differ at some eigenvector,
and surjective by the biconditional. So the symmetries are in bijection with `Finset V` and there
are `2^|V|` of them.

## What is proved

**`symmetries`** — the isometries whose pushforward fixes the field, as a `Set`. By
`FieldInvarianceCommutes` this is the honest object: membership is being a symmetry, not being a
member of some set contained in the symmetries (`ERRATUM 456`).

**`signIsometry_mem`, `signIsometry_injective`** — the sign isometries are symmetries, and distinct
sign sets give distinct ones. Injectivity is `smul_left_injective` against a unit eigenvector: if
the scalars agree at every `j` then the sets agree, since `-1 ≠ 1`.

**`signEquiv`** — hence a bijection `Finset V ≃ symmetries G m`, built from
`FieldSimpleCriterion.exists_signIsometry_eq` for surjectivity, **at a simple spectrum**.

**`card_symmetries`** — **so a Gaussian field whose propagator has a simple spectrum has exactly
`2^|V|` isometric symmetries**, on any finite graph. **`card_symmetries_line`** — and the line is
the instance, at `2^(k+1)`, by counting `Site 1 (k+1)`.

**`refl_mem`, `trans_mem`, `symm_mem`** — **and the symmetries are a group under composition**, at
the level of isometries rather than of matrices. Each is two lines from `Measure.map_map`; the
identity, composites and inverses of measure-preserving maps are measure-preserving for reasons that
have nothing to do with this graph. `FieldSymmetryGroup` proves the corresponding statement for
`symmetryMatrices` and keeps its own proof (`ERRATUM 337`).

## What is NOT here

**NO GROUP ISOMORPHISM, and no bundled group at all.** The three closure lemmas are the group law;
they are **not** assembled into a `Subgroup`, and `symmetries G m` is **not** identified with
`(ZMod 2)^V`. `signEquiv` is a bijection of types, not a group isomorphism — nothing here checks
that it carries `Finset` symmetric difference to composition. **The `UNLOCK_WATCHLIST` item loses
its cardinality half and keeps its isomorphism half.** Not attempted, no cost claimed
(`ERRATUM 246`).
⚠ **SUPERSEDED 2026-09-05, kept as written** (`ERRATUM 94`): `FieldSignGroup` does all three, and
since this file's generalisation it does them on any graph with a simple spectrum.

**NOTHING WITHOUT A SIMPLE SPECTRUM.** `card_symmetries` and `signEquiv` both take
`Function.Injective hH.eigenvalues`, and **no graph other than the line is shown to satisfy it** —
`FieldSimpleCriterion.eigenvalues_injective_line` is still the only discharge in the estate. On a
box in two or more dimensions the count is `Set.Infinite` and no finer statement exists, and **no
dichotomy is proved**: nothing says a simple spectrum is the only case with a finite symmetry
group.

**Only isometries**, inherited: a measure-preserving map that is not a linear isometry is not
counted, so this is **not** the cardinality of the full automorphism group of the measure.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. A symmetry
group counted exactly in finite volume is a shadow counted exactly.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): a non-zero mass is taken by
`signIsometry_mem`, `signEquiv`, `card_symmetries` and `card_symmetries_line` — **four of the
nine**. It is **not** taken by `symmetries`, `signIsometry_injective` (which is about `signIsometry`
alone), `refl_mem`, `trans_mem` or `symm_mem`, which are about measure-preserving maps and hold at
every mass — at mass `0` they say the isometries preserving a point mass are a group, which is true
and empty (`FieldMassNecessity`). **Simplicity of the spectrum** is taken by `signEquiv` and
`card_symmetries` only; the group law needs neither it nor the mass.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldLineCount

open Matrix GraphLaplacian BoxGraph FieldSimpleSpectrum FieldSimpleCriterion MeasureTheory

/-! ## 1. The sign sets and the symmetries are in bijection -/

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-- **THE ISOMETRIC SYMMETRIES OF THE GAUSSIAN FIELD.** -/
def symmetries (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) :
    Set (EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) :=
  {T | Measure.map T (gaussianField G m) = gaussianField G m}

theorem signIsometry_mem (hm : m ≠ 0) (hH : (green G m).IsHermitian) (s : Finset V) :
    signIsometry hH s ∈ symmetries G m :=
  gaussianField_map_signIsometry hm hH s

theorem signIsometry_injective (hH : (green G m).IsHermitian) :
    Function.Injective (fun s : Finset V => signIsometry hH s) := by
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

/-- **THE SIGN SETS AND THE SYMMETRIES ARE IN BIJECTION**, at a simple spectrum. -/
noncomputable def signEquiv (hm : m ≠ 0) (hH : (green G m).IsHermitian)
    (hsimple : Function.Injective hH.eigenvalues) :
    Finset V ≃ symmetries G m :=
  Equiv.ofBijective (fun s => ⟨signIsometry hH s, signIsometry_mem hm hH s⟩)
    ⟨fun _ _ h => signIsometry_injective hH (congrArg Subtype.val h),
     fun T => (exists_signIsometry_eq hH
       ((gaussianField_map_iff_signs hm hH hsimple T.1).mp T.2)).imp
         fun _ hs => Subtype.ext hs⟩

/-- **A GAUSSIAN FIELD WHOSE PROPAGATOR HAS A SIMPLE SPECTRUM HAS EXACTLY `2^|V|` ISOMETRIC
SYMMETRIES**, on any finite graph. -/
theorem card_symmetries (hm : m ≠ 0)
    (hsimple : Function.Injective (green_posDef G hm).isHermitian.eigenvalues) :
    Nat.card (symmetries G m) = 2 ^ Fintype.card V := by
  rw [← Nat.card_congr (signEquiv hm (green_posDef G hm).isHermitian hsimple),
    Nat.card_eq_fintype_card, Fintype.card_finset]

/-- **THE LINE IS THE INSTANCE**: `2^(k+1)` on `boxGraph 1 (k+1)`. -/
theorem card_symmetries_line {k : ℕ} {mass : ℝ} (hmass : mass ≠ 0) :
    Nat.card (symmetries (boxGraph 1 (k + 1)) mass) = 2 ^ (k + 1) := by
  rw [card_symmetries hmass
      (eigenvalues_injective_line hmass (green_posDef (boxGraph 1 (k + 1)) hmass).isHermitian),
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_one]

/-! ## 2. And they are a group -/

theorem refl_mem : LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ V) ∈ symmetries G m := by
  simp [symmetries]

theorem trans_mem {S T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V}
    (hS : S ∈ symmetries G m) (hT : T ∈ symmetries G m) :
    S.trans T ∈ symmetries G m := by
  simp only [symmetries, Set.mem_setOf_eq] at hS hT ⊢
  rw [show (⇑(S.trans T)) = ⇑T ∘ ⇑S from rfl,
    ← Measure.map_map T.continuous.measurable S.continuous.measurable, hS, hT]

theorem symm_mem {T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V}
    (hT : T ∈ symmetries G m) : T.symm ∈ symmetries G m := by
  have h1 : Measure.map (⇑T.symm) (Measure.map (⇑T) (gaussianField G m))
      = gaussianField G m := by
    rw [Measure.map_map T.symm.continuous.measurable T.continuous.measurable]
    simp
  rw [hT] at h1
  exact h1

end FieldLineCount
