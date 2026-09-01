import EigenBasisDimension
import BoxMassiveSpectrum
import BoxLapMultiplicity

/-!
# The box's eigenspace dimensions, and the multinomial as a dimension bound

`BoxLapMultiplicity` bounds the set of frequency vectors sharing a box eigenvalue below by a
multinomial coefficient and fences: *"it is a fibre count, not an eigenspace dimension"*.
`EigenBasisDimension` lifted that fence in general. This joins them.

> **`finrank_eigenspace_massive_box`** — the eigenspace of `massive (boxGraph d n) m` at `μ` has
> dimension **exactly** the number of frequency vectors `k` with `∑ᵢ (2 − 2cos(kᵢπ/n)) + m² = μ`.
>
> **`finrank_eigenspace_lap_box`** — and the same for `L` itself, without the mass.
>
> **`multinomial_le_finrank`** — hence the degeneracy at any frequency is **at least** `d!/∏mᵢ!`,
> which is now a statement about a dimension rather than about a count of labels.

## What this is the box's version of

`TorusRealMultiplicity.finrank_eigenspace_massive_real` says exactly this for the **torus**, and
reaches it through `ℂ` and the characters. The box gets it over `ℝ` directly, because
`BoxLapBasis.boxLapBasis` is already a real basis of eigenvectors and `EigenBasisDimension` needs
nothing else. **So the two lattices now carry the same statement by different routes**, and the
box's is the shorter one.

## What this is NOT

**The bound is still not an equality.** `BoxLapMultiplicity.sporadic_eq` exhibits two frequency
vectors at `d = 2`, side `6` that share an eigenvalue with no permutation between them, so the fibre
— and now, provably, the dimension — can exceed the multinomial. **No formula and no upper bound**
(`ERRATUM 194`, `ERRATUM 246`).

**No orthogonality is used.** `EigenBasisDimension` asks only for a basis; that these modes are
orthogonal (`BoxLapModeOrthogonal`) is not needed here and is not used.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BoxEigenspaceDimension

open Finset Matrix BoxGraph BoxLapSpectrum BoxLapBasis GraphLaplacian

variable {d m : ℕ}

/-! ## 1. The dimension is the fibre's size -/

/-- **THE EIGENSPACE OF `−Δ + m²` ON THE BOX, MEASURED.** -/
theorem finrank_eigenspace_massive_box (d m : ℕ) (mass μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (massive (boxGraph d (m + 1)) mass) - μ • LinearMap.id))
      = Nat.card {k : Site d (m + 1) //
          boxLapEig d (m + 1) (fun i => (k i).val) + mass ^ 2 = μ} :=
  EigenBasisDimension.finrank_ker_sub_smul (boxLapBasis d m)
    (fun k => by
      rw [boxLapBasis_apply]
      exact BoxMassiveSpectrum.massive_mulVec_siteLapVec d m mass k) μ

/-- **AND THE SAME FOR `L` ITSELF.** -/
theorem finrank_eigenspace_lap_box (d m : ℕ) (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((boxGraph d (m + 1)).lapMatrix ℝ) - μ • LinearMap.id))
      = Nat.card {k : Site d (m + 1) // boxLapEig d (m + 1) (fun i => (k i).val) = μ} :=
  EigenBasisDimension.finrank_ker_sub_smul (boxLapBasis d m)
    (fun k => by
      rw [boxLapBasis_apply]
      exact lapMatrix_mulVec_siteLapVec d m k) μ

/-! ## 2. So the multinomial bounds a dimension -/

/-- **THE DEGENERACY IS AT LEAST `d!/∏mᵢ!`**, now as a dimension. -/
theorem multinomial_le_finrank (d m : ℕ) (k : Site d (m + 1)) :
    Nat.multinomial univ (fun a : Fin (m + 1) => Fintype.card {i // k i = a})
      ≤ Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' ((boxGraph d (m + 1)).lapMatrix ℝ)
            - (boxLapEig d (m + 1) (fun i => (k i).val)) • LinearMap.id)) := by
  classical
  rw [finrank_eigenspace_lap_box, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact BoxLapMultiplicity.multinomial_le_card_eigFibre d (m + 1) k

end BoxEigenspaceDimension
