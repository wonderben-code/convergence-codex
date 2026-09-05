import FieldSimpleSpectrum

/-!
# The classification bites: the field on a LINE has exactly the sign symmetries

`FieldSimpleSpectrum` classified the symmetries at a propagator with pairwise-distinct eigenvalues
and **could not point at a graph**: its hypothesis `Function.Injective hH.eigenvalues` was carried
and never discharged, so the file exhibited nothing on which its conclusion bites. **This discharges
it on the one-dimensional box** — a line of sites, the graph `boxGraph 1 (m+1)`.

**The contrast is the point.** `FieldRotationCount.infinite_symmetryMatrices_box`: on a box in
`d ≥ 2` dimensions the Gaussian field has **infinitely many** symmetries, because permuting two axes
leaves the eigenvalue where it was and any rotation between the two frequencies is a symmetry.
`exists_signs_line`: on a line there are **no two axes to permute**, the spectrum is simple, and
every symmetry is a `±1` on each eigenvector. **The chain now has both poles on named graphs.**

## What is proved

**`massive_mulVec_of_green_mulVec`** — an eigenvector of `green` at `μ ≠ 0` is an eigenvector of
`massive` at `μ⁻¹`. `FieldSignReflection.green_mulVec_of_massive_mulVec` is the other direction and
keeps its own proof (`ERRATUM 337`); this one multiplies through by `massive` and uses
`GraphLaplacian.green_mul_massive`.

**`eigenvalues_injective_of_finrank_le_one`** — **if every eigenspace of `massive` is at most a
line, the propagator's spectrum is simple.** Two basis vectors at one eigenvalue would span a plane
inside a line: `Submodule.eq_of_le_of_finrank_le` forces the eigenspace to be the span of the first,
so the second is a multiple of it, and orthonormality then makes that multiple zero — contradicting
its being a unit vector.

**`mem_Icc_of_lt`, `boxLapEig_one_injective`** — on a line the frequencies `jπ/(m+1)` for `j ≤ m`
all lie in `[0, π]`, where `Real.injOn_cos` is injective, so **distinct frequencies give distinct
eigenvalues.** This is the whole of what fails in `d ≥ 2`, where two frequencies differing by a swap
of axes give the same eigenvalue.

**`finrank_le_one_line`** — hence, through `BoxEigenspaceDimension.finrank_eigenspace_massive_box`,
every eigenspace on a line has dimension at most one.

**`eigenvalues_injective_line`** — **the propagator on a line has a simple spectrum.**

**`exists_signs_line`** — **so every symmetry of the Gaussian field on a line is a sign pattern on
the eigenbasis**, and **`gaussianField_map_iff_signs_line`** is the biconditional: the converse
comes from `FieldSimpleSpectrum.gaussianField_map_signIsometry` and `eq_of_signs`, neither of which
needs simplicity. **The word *exactly* is a theorem here and not a composition left to the reader.**

## What is NOT here

**NO CARDINALITY**, still: **as of 2026-09-05** `2^(m+1)` is not proved anywhere in this estate,
and neither is a bundled group isomorphism. `FieldSimpleSpectrum`'s fence on that stands
unchanged, and both remain on `UNLOCK_WATCHLIST`.
**Not attempted, no cost claimed** (`ERRATUM 246`).

**NOTHING ABOUT `d ≥ 2` IS ADDED HERE.** The contrast above is between this file and
`FieldRotationCount`; neither says anything new about the other's case, and in particular **no
dichotomy is proved** — nothing here says the spectrum is simple *exactly when* `d = 1`, only that
it is simple when `d = 1`.

**Only isometries**, inherited from `FieldInvarianceCommutes`.

**Nothing about the torus at `d > 1`.**

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. A symmetry
group determined exactly on a line is a shadow determined exactly.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455` and its addendum). `m ≠ 0` — written
`hmass` in the line results — is taken by `massive_mulVec_of_green_mulVec`,
`eigenvalues_injective_of_finrank_le_one`, `eigenvalues_injective_line` and `exists_signs_line`; it
is **not** taken by `mem_Icc_of_lt`, `boxLapEig_one_injective` or `finrank_le_one_line`, which are
statements about the spectrum of `massive` and hold at every mass, `0` included.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldSimpleCriterion

open Matrix GraphLaplacian RayleighMatrix

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. An eigenvector of the propagator is one of the massive operator -/

theorem massive_mulVec_of_green_mulVec (hm : m ≠ 0) {x : V → ℝ} {μ : ℝ} (hμ : μ ≠ 0)
    (h : green G m *ᵥ x = μ • x) : massive G m *ᵥ x = μ⁻¹ • x := by
  have h1 : massive G m *ᵥ (green G m *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, mul_eq_one_comm.mp (green_mul_massive G hm), Matrix.one_mulVec]
  rw [h, Matrix.mulVec_smul] at h1
  have h2 := congrArg (fun y : V → ℝ => μ⁻¹ • y) h1
  simpa [smul_smul, inv_mul_cancel₀ hμ] using h2

/-! ## 2. A one-dimensional eigenspace everywhere forces a simple spectrum -/

theorem eigenvalues_injective_of_finrank_le_one (hm : m ≠ 0) (hH : (green G m).IsHermitian)
    (hdim : ∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (massive G m) - ν • LinearMap.id)) ≤ 1) :
    Function.Injective hH.eigenvalues := by
  intro i j hij
  by_contra hne
  set b := hH.eigenvectorBasis with hb
  have hpos : ∀ k, 0 < hH.eigenvalues k := fun k => (green_posDef G hm).eigenvalues_pos k
  set W := LinearMap.ker (Matrix.toLin' (massive G m)
      - (hH.eigenvalues i)⁻¹ • LinearMap.id) with hW
  have hmem : ∀ k : V, hH.eigenvalues k = hH.eigenvalues i → (⇑(b k) : V → ℝ) ∈ W := by
    intro k hk
    refine (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr ?_
    rw [← hk]
    exact massive_mulVec_of_green_mulVec hm (hpos k).ne' (hH.mulVec_eigenvectorBasis k)
  have hi := hmem i rfl
  have hj := hmem j hij.symm
  have hi0 : (⇑(b i) : V → ℝ) ≠ 0 := by
    intro hz
    have : ‖b i‖ = 1 := b.orthonormal.1 i
    rw [show (b i) = (0 : EuclideanSpace ℝ V) from by ext v; exact congrFun hz v] at this
    simp at this
  have hspan : Submodule.span ℝ {(⇑(b i) : V → ℝ)} = W := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hi
    · rw [finrank_span_singleton hi0]; exact hdim _
  have hjmem : (⇑(b j) : V → ℝ) ∈ Submodule.span ℝ {(⇑(b i) : V → ℝ)} := hspan ▸ hj
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hjmem
  have hcEuclid : b j = c • b i := by ext v; exact (congrFun hc v).symm
  have hortho : inner ℝ (b i) (b j) = 0 := b.orthonormal.2 hne
  rw [hcEuclid, real_inner_smul_right, real_inner_self_eq_norm_sq, b.orthonormal.1 i] at hortho
  have hc0 : c = 0 := by simpa using hortho
  have : ‖b j‖ = 1 := b.orthonormal.1 j
  rw [hcEuclid, hc0, zero_smul, norm_zero] at this
  exact absurd this (by norm_num)

/-! ## 3. The line: distinct frequencies give distinct eigenvalues -/

open BoxGraph BoxLapSpectrum BoxEigenspaceDimension

theorem mem_Icc_of_lt {m j : ℕ} (hj : j < m + 1) :
    (j : ℝ) * Real.pi / ((m : ℝ) + 1) ∈ Set.Icc 0 Real.pi := by
  have hpi := Real.pi_pos
  have hm : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have hjm : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hj
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hm]
  nlinarith [hpi, hjm, Nat.cast_nonneg (α := ℝ) j]

theorem boxLapEig_one_injective (m : ℕ) :
    Function.Injective (fun k : Site 1 (m + 1) => boxLapEig 1 (m + 1) (fun i => (k i).val)) := by
  intro k1 k2 h
  simp only [boxLapEig_eq, Fin.sum_univ_one] at h
  have hcos : Real.cos (((k1 0).val : ℝ) * Real.pi / ((m:ℝ)+1))
      = Real.cos (((k2 0).val : ℝ) * Real.pi / ((m:ℝ)+1)) := by linarith
  have heq := Real.injOn_cos (mem_Icc_of_lt (k1 0).isLt) (mem_Icc_of_lt (k2 0).isLt) hcos
  have hpi := Real.pi_pos
  have hm : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have hval : ((k1 0).val : ℝ) = ((k2 0).val : ℝ) := by
    have h2 := congrArg (fun t : ℝ => t * ((m:ℝ)+1)) heq
    simp only [div_mul_cancel₀ _ hm.ne'] at h2
    exact mul_right_cancel₀ hpi.ne' h2
  have hnat : (k1 0).val = (k2 0).val := Nat.cast_injective hval
  funext i
  rw [Subsingleton.elim i 0]
  exact Fin.ext hnat

theorem finrank_le_one_line (m : ℕ) (mass ν : ℝ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (massive (boxGraph 1 (m + 1)) mass) - ν • LinearMap.id)) ≤ 1 := by
  rw [finrank_eigenspace_massive_box, Finite.card_le_one_iff_subsingleton]
  refine ⟨fun a b => ?_⟩
  refine Subtype.ext (boxLapEig_one_injective m ?_)
  have := a.2.trans b.2.symm
  simpa using this

/-- **THE PROPAGATOR ON A LINE HAS A SIMPLE SPECTRUM.** -/
theorem eigenvalues_injective_line {m : ℕ} {mass : ℝ} (hmass : mass ≠ 0)
    (hH : (green (boxGraph 1 (m + 1)) mass).IsHermitian) :
    Function.Injective hH.eigenvalues :=
  eigenvalues_injective_of_finrank_le_one hmass hH (finrank_le_one_line m mass)

/-- **SO THE SYMMETRIES OF THE GAUSSIAN FIELD ON A LINE ARE EXACTLY THE SIGN PATTERNS.** -/
theorem exists_signs_line {m : ℕ} {mass : ℝ} (hmass : mass ≠ 0)
    (hH : (green (boxGraph 1 (m + 1)) mass).IsHermitian)
    {T : EuclideanSpace ℝ (Site 1 (m + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Site 1 (m + 1))}
    (hT : MeasureTheory.Measure.map T (gaussianField (boxGraph 1 (m + 1)) mass)
      = gaussianField (boxGraph 1 (m + 1)) mass) :
    ∃ ε : Site 1 (m + 1) → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ j, T (hH.eigenvectorBasis j) = ε j • hH.eigenvectorBasis j :=
  FieldSimpleSpectrum.exists_signs hmass hH (eigenvalues_injective_line hmass hH) hT

/-- **A SIGN PATTERN IS A `signIsometry`**, with the sign set read off as a `Finset`. Exposed
rather than inlined so that a count of the symmetries can reuse it. -/
theorem exists_signIsometry_eq {m : ℕ} {mass : ℝ}
    (hH : (green (boxGraph 1 (m + 1)) mass).IsHermitian)
    {T : EuclideanSpace ℝ (Site 1 (m + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Site 1 (m + 1))}
    (hsigns : ∃ ε : Site 1 (m + 1) → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ j, T (hH.eigenvectorBasis j) = ε j • hH.eigenvectorBasis j) :
    ∃ s : Finset (Site 1 (m + 1)), FieldSimpleSpectrum.signIsometry hH s = T := by
  classical
  obtain ⟨ε, hε, hTj⟩ := hsigns
  refine ⟨Finset.univ.filter (fun j => ε j = -1), FieldSimpleSpectrum.eq_of_signs hH fun j => ?_⟩
  rw [FieldSimpleSpectrum.signIsometry_eigenvectorBasis, hTj j]
  congr 1
  by_cases hj : ε j = -1
  · rw [if_pos (by simp [hj]), hj]
  · rcases hε j with h1 | h1
    · rw [if_neg (by simp [hj]), h1]
    · exact absurd h1 hj

/-- **AND THAT IS EXACTLY WHAT THE SYMMETRIES ARE**: a biconditional, so the word *exactly* is a
theorem here and not a composition left to the reader. -/
theorem gaussianField_map_iff_signs_line {m : ℕ} {mass : ℝ} (hmass : mass ≠ 0)
    (hH : (green (boxGraph 1 (m + 1)) mass).IsHermitian)
    (T : EuclideanSpace ℝ (Site 1 (m + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Site 1 (m + 1))) :
    MeasureTheory.Measure.map T (gaussianField (boxGraph 1 (m + 1)) mass)
        = gaussianField (boxGraph 1 (m + 1)) mass ↔
      ∃ ε : Site 1 (m + 1) → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
        ∀ j, T (hH.eigenvectorBasis j) = ε j • hH.eigenvectorBasis j := by
  refine ⟨fun hT => exists_signs_line hmass hH hT, ?_⟩
  intro hsigns
  obtain ⟨s, hs⟩ := exists_signIsometry_eq hH hsigns
  rw [← hs]
  exact FieldSimpleSpectrum.gaussianField_map_signIsometry hmass hH s

end FieldSimpleCriterion
