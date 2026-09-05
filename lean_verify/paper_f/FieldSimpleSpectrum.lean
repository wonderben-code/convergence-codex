import FieldInvarianceCommutes

/-!
# When the spectrum is simple the symmetries are EXACTLY the sign patterns

`FieldInvarianceCommutes` made *symmetry of the Gaussian field* and *commuting with the propagator*
the same thing for isometries, and `FieldCommutantSpectral` made commuting the same as preserving
every eigenspace. **Put the two together at a propagator whose eigenvalues are pairwise distinct**
and the eigenspaces are lines, so a symmetry can only scale each one — and being an isometry, only
by `±1`. Conversely every choice of signs **is** a symmetry, and a symmetry is determined by its
signs. That is a complete classification.

**This is the `∏ᵢ O(dᵢ)` shape the watchlist named, at all `dᵢ = 1`.** The general case, where the
multiplicities are not all one, is untouched.

**And it is the opposite pole from `FieldRotationCount`.** There the box in `d ≥ 2` was shown to
have **infinitely many** symmetries, because permuting two axes forces a degenerate eigenvalue.
Here a simple spectrum forces the symmetry group to be **as small as it can be**. The two results
are the same theory read at its two extremes, and each is what the other's hypothesis fails.

## What is proved

**`inner_eigenvectorBasis_eq_zero`** — if the eigenvalues are pairwise distinct and `T` commutes
with `green`, then `T (bⱼ)` is orthogonal to every other `b_k`. Two evaluations of
`⟪b_k, green (T bⱼ)⟫`: through `green`'s symmetry it is `μ_k ⟪b_k, T bⱼ⟫`, and through commuting it
is `μⱼ ⟪b_k, T bⱼ⟫`.

**`apply_eigenvectorBasis`** — hence `T (bⱼ)` is a multiple of `bⱼ`, by
`OrthonormalBasis.sum_repr'` and `Finset.sum_eq_single`. **`inner_eq_one_or_neg_one`** — and the
multiple is `±1`, because `T` is an isometry and `bⱼ` is a unit vector.

**`exists_signs`** — **so every symmetry of the Gaussian field is a sign pattern on the
eigenbasis**, stated from the measure through
`FieldInvarianceCommutes.gaussianField_map_iff_commutes`.

**`signIsometry`, `signIsometry_eigenvectorBasis`, `signIsometry_comm`,
`gaussianField_map_signIsometry`** — **and every sign pattern is one.** `FieldSignFlip.signFlip`
conjugated by the eigenbasis gives the isometry; it commutes with `green` because both sides are
linear and agree on the eigenbasis, which is `Module.Basis.ext` against
`Matrix.toEuclideanLin` — the same map as `RayleighMatrix.mv`, definitionally.

**`eq_of_signs`** — and **the symmetry is determined by its signs**: two isometries agreeing on the
eigenbasis are equal, symmetries in particular.

**AND ONE LEMMA IS NOT HERE THAT THE FIRST DRAFT WROTE** (`ERRATUM 457`): *`green` acts on the
eigenbasis by the eigenvalue, in `mv` form* is **`RayleighMatrix.mv_eigenvectorBasis`**, in this
estate since 30 August, with the same statement and the same three-line proof. `newnames_scan`
caught the duplicate. `RayleighMatrix` is this estate's spectral toolbox and it was not consulted.

**THE TWO HALVES NEED DIFFERENT HYPOTHESES, and that is the shape of the result.** Simplicity of the
spectrum is what makes signs the **only** option; **producing** the sign symmetries needs neither
simplicity nor `m ≠ 0`, so they are there on every graph — it is only their being *all* of the
symmetries that is special.

## What is NOT here

**NO GROUP ISOMORPHISM AND NO CARDINALITY.** The three theorems above are *every symmetry has
signs*, *every sign pattern is a symmetry*, and *signs determine the symmetry*. **They are not
assembled into an `≃*` with `(ZMod 2)^V`, and no `Finite` instance or `2^|V|` bound is proved.**
Not attempted, no cost claimed (`ERRATUM 246`).

**NO NAMED GRAPH WITH A SIMPLE SPECTRUM.** `Function.Injective hH.eigenvalues` is carried, not
discharged, so **this file exhibits no graph on which its conclusion bites.** The one-dimensional
box is the obvious candidate — a path's Laplacian eigenvalues `2 − 2cos(kπ/n)` are distinct because
`cos` is injective on `[0, π]` — **and that composition is not made here.** Naming the candidate is
not a claim that it is short (`ERRATUM 194`).

**Only isometries**, inherited from `FieldInvarianceCommutes`: a measure-preserving map that is not
a linear isometry is not covered.

**Nothing about the torus at `d > 1`.**
⚠ **SUPERSEDED 2026-09-05, kept as written** (`ERRATUM 94`, `ERRATUM 458`):
`FieldTorusRotation.exists_rotation_symmetry_torus` puts a rotation on the torus in **every**
dimension `d ≥ 1`, and needed no orbit bookkeeping at all —
`TorusEigenspaceLowerBound.two_pow_mul_multinomial_le_finrank`, in the estate since 2026-08-31,
bounds the degeneracy below with **no hypotheses**, and the all-ones frequency has every axis
interior. **The route this sentence names was never necessary.**

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. A symmetry
group that is *small* is no more a gap in an axiom than one that is large.

**THE HYPOTHESES, READ OFF THE BINDERS AND NOT FROM THE SUBJECT MATTER** (`ERRATUM 455` and its
addendum, whose species has now appeared in five consecutive units). `m ≠ 0` is taken by
`inner_eigenvectorBasis_eq_zero`, `apply_eigenvectorBasis`, `inner_eq_one_or_neg_one`,
`exists_signs` and `gaussianField_map_signIsometry`; it is **not** taken by `signIsometry`,
`signIsometry_eigenvectorBasis`, `signIsometry_comm` or `eq_of_signs`. Simplicity is taken by the
first four of that five and by nothing else.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldSimpleSpectrum

open Matrix GraphLaplacian FieldCommutant FieldOrthIsometry FieldRotationCount
open RayleighMatrix MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. A simple spectrum makes every eigenspace a line -/

theorem inner_eigenvectorBasis_eq_zero (hm : m ≠ 0) (hH : (green G m).IsHermitian)
    (hsimple : Function.Injective hH.eigenvalues)
    {T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V}
    (hT : ∀ x, mv (green G m) (T x) = T (mv (green G m) x)) {j k : V} (hjk : k ≠ j) :
    inner ℝ (hH.eigenvectorBasis k) (T (hH.eigenvectorBasis j)) = 0 := by
  have hgreen : mv (green G m) (T (hH.eigenvectorBasis j))
      = (hH.eigenvalues j) • T (hH.eigenvectorBasis j) := by
    rw [hT, mv_eigenvectorBasis hH j, map_smul]
  have h1 : inner ℝ (hH.eigenvectorBasis k) (mv (green G m) (T (hH.eigenvectorBasis j)))
      = (hH.eigenvalues j) * inner ℝ (hH.eigenvectorBasis k) (T (hH.eigenvectorBasis j)) := by
    rw [hgreen, real_inner_smul_right]
  have h2 : inner ℝ (hH.eigenvectorBasis k) (mv (green G m) (T (hH.eigenvectorBasis j)))
      = (hH.eigenvalues k) * inner ℝ (hH.eigenvectorBasis k) (T (hH.eigenvectorBasis j)) := by
    rw [inner_mv_comm _ (green_isSymm G hm), mv_eigenvectorBasis hH k, real_inner_smul_left]
  have hne : hH.eigenvalues k ≠ hH.eigenvalues j := fun h => hjk (hsimple h)
  have := h1.symm.trans h2
  rcases mul_eq_zero.mp (by linarith [this] :
      (hH.eigenvalues k - hH.eigenvalues j)
        * inner ℝ (hH.eigenvectorBasis k) (T (hH.eigenvectorBasis j)) = 0) with h | h
  · exact absurd (by linarith [h] : hH.eigenvalues k = hH.eigenvalues j) hne
  · exact h

theorem apply_eigenvectorBasis (hm : m ≠ 0) (hH : (green G m).IsHermitian)
    (hsimple : Function.Injective hH.eigenvalues)
    {T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V}
    (hT : ∀ x, mv (green G m) (T x) = T (mv (green G m) x)) (j : V) :
    T (hH.eigenvectorBasis j)
      = (inner ℝ (hH.eigenvectorBasis j) (T (hH.eigenvectorBasis j))) • hH.eigenvectorBasis j := by
  refine ((hH.eigenvectorBasis).sum_repr' (T (hH.eigenvectorBasis j))).symm.trans ?_
  refine Finset.sum_eq_single j (fun k _ hkj => ?_) (fun h => absurd (Finset.mem_univ j) h)
  exact smul_eq_zero.mpr (Or.inl (inner_eigenvectorBasis_eq_zero hm hH hsimple hT hkj))

/-! ## 2. And an isometry can only scale a unit vector by a sign -/

theorem inner_eq_one_or_neg_one (hm : m ≠ 0) (hH : (green G m).IsHermitian)
    (hsimple : Function.Injective hH.eigenvalues)
    {T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V}
    (hT : ∀ x, mv (green G m) (T x) = T (mv (green G m) x)) (j : V) :
    inner ℝ (hH.eigenvectorBasis j) (T (hH.eigenvectorBasis j)) = 1 ∨
      inner ℝ (hH.eigenvectorBasis j) (T (hH.eigenvectorBasis j)) = -1 := by
  have hunit : ‖hH.eigenvectorBasis j‖ = 1 := (hH.eigenvectorBasis).orthonormal.1 j
  have hnorm : ‖T (hH.eigenvectorBasis j)‖ = 1 := by rw [T.norm_map, hunit]
  rw [apply_eigenvectorBasis hm hH hsimple hT j, norm_smul, hunit, mul_one,
    Real.norm_eq_abs] at hnorm
  exact abs_eq (by norm_num) |>.mp hnorm

/-! ## 3. So a symmetry is a sign pattern -/

/-- **IF THE PROPAGATOR'S SPECTRUM IS SIMPLE, EVERY SYMMETRY OF THE GAUSSIAN FIELD IS A SIGN
PATTERN ON THE EIGENBASIS.** -/
theorem exists_signs (hm : m ≠ 0) (hH : (green G m).IsHermitian)
    (hsimple : Function.Injective hH.eigenvalues)
    {T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V}
    (hT : Measure.map T (gaussianField G m) = gaussianField G m) :
    ∃ ε : V → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ j, T (hH.eigenvectorBasis j) = ε j • hH.eigenvectorBasis j := by
  have hcomm := (FieldInvarianceCommutes.gaussianField_map_iff_commutes hm T).mp hT
  exact ⟨fun j => inner ℝ (hH.eigenvectorBasis j) (T (hH.eigenvectorBasis j)),
    fun j => inner_eq_one_or_neg_one hm hH hsimple hcomm j,
    fun j => apply_eigenvectorBasis hm hH hsimple hcomm j⟩

/-! ## 4. And every sign pattern is achieved -/

/-- The isometry that is `±1` on each eigenvector, by conjugating `FieldSignFlip.signFlip` with the
eigenbasis. -/
noncomputable def signIsometry (hH : (green G m).IsHermitian) (s : Finset V) :
    EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V :=
  (hH.eigenvectorBasis.repr).trans
    ((FieldSignFlip.signFlip s).trans (hH.eigenvectorBasis.repr).symm)

theorem signIsometry_eigenvectorBasis (hH : (green G m).IsHermitian) (s : Finset V) (j : V) :
    signIsometry hH s (hH.eigenvectorBasis j)
      = (if j ∈ s then (-1 : ℝ) else 1) • hH.eigenvectorBasis j := by
  have hflip : FieldSignFlip.signFlip s (EuclideanSpace.single j (1 : ℝ))
      = (if j ∈ s then (-1 : ℝ) else 1) • EuclideanSpace.single j (1 : ℝ) := by
    ext v
    rw [FieldSignFlip.signFlip_apply]
    by_cases hv : v = j <;> by_cases hj : j ∈ s <;> simp [hv, hj]
  rw [signIsometry]
  simp only [LinearIsometryEquiv.trans_apply, OrthonormalBasis.repr_self, hflip, map_smul,
    OrthonormalBasis.repr_symm_single]

/-- **AND IT COMMUTES WITH THE PROPAGATOR**, because both sides are linear and agree on the
eigenbasis. No mass hypothesis: this is diagonal-times-diagonal. -/
theorem signIsometry_comm (hH : (green G m).IsHermitian) (s : Finset V)
    (x : EuclideanSpace ℝ V) :
    mv (green G m) (signIsometry hH s x) = signIsometry hH s (mv (green G m) x) := by
  have key : (Matrix.toEuclideanLin (green G m)).comp
        (signIsometry hH s).toLinearEquiv.toLinearMap
      = (signIsometry hH s).toLinearEquiv.toLinearMap.comp
        (Matrix.toEuclideanLin (green G m)) := by
    refine (hH.eigenvectorBasis).toBasis.ext fun j => ?_
    change mv (green G m) (signIsometry hH s (hH.eigenvectorBasis j))
      = signIsometry hH s (mv (green G m) (hH.eigenvectorBasis j))
    rw [signIsometry_eigenvectorBasis, mv_smul, mv_eigenvectorBasis hH j, map_smul,
      signIsometry_eigenvectorBasis, smul_comm]
  exact LinearMap.congr_fun key x

/-- **SO EVERY SIGN PATTERN IS A SYMMETRY OF THE GAUSSIAN FIELD**, and with `exists_signs` and
`eq_of_signs` the classification at a simple spectrum is complete. -/
theorem gaussianField_map_signIsometry (hm : m ≠ 0) (hH : (green G m).IsHermitian)
    (s : Finset V) :
    Measure.map (signIsometry hH s) (gaussianField G m) = gaussianField G m :=
  (FieldInvarianceCommutes.gaussianField_map_iff_commutes hm _).mpr (signIsometry_comm hH s)

/-- **AND THE SYMMETRY IS DETERMINED BY ITS SIGNS.** -/
theorem eq_of_signs (hH : (green G m).IsHermitian)
    {T S : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V}
    (h : ∀ j, T (hH.eigenvectorBasis j) = S (hH.eigenvectorBasis j)) : T = S := by
  have : T.toLinearEquiv.toLinearMap = S.toLinearEquiv.toLinearMap :=
    (hH.eigenvectorBasis).toBasis.ext h
  exact LinearIsometryEquiv.toLinearEquiv_injective
    (LinearEquiv.toLinearMap_injective this)

end FieldSimpleSpectrum
