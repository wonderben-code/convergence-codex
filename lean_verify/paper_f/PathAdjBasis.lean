import PathAdjSpectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# The path's sine vectors are a basis, because the eigenvalues are distinct

`PathAdjSpectrum` proves `A · v_k = 2 cos(kπ/(n+1)) · v_k` on `SimpleGraph.pathGraph n` and states
plainly that it is **not** a basis: spanning, independence and exhaustion were all unproved. This
file supplies them, and the route is the cheap one — **not** discrete orthogonality, which is a
genuine computation, but the observation that eigenvectors for **distinct** eigenvalues are
independent, and that `n` independent vectors in an `n`-dimensional space are a basis.

> **`pathVec_ne_zero`** — for `1 ≤ k ≤ n` the vector is nonzero, because its **first** entry is
> `sin(kπ/(n+1))` and that angle lies strictly inside `(0, π)`.
>
> **`angle_injective`** — `k ↦ kπ/(n+1)` is injective on `1 … n`, so `Real.injOn_cos` makes the
> eigenvalues distinct. This is where the range of `k` is spent: at `k = 0` the vector vanishes and
> at `k = n + 1` it vanishes again, which is the same pair of phantom zeros `PathAdjSpectrum` used.
>
> **`pathVec_linearIndependent`** — hence `Module.End.eigenvectors_linearIndependent'` applies.
>
> **`pathBasis`** — and `n` of them is `Module.finrank ℝ (Fin n → ℝ)`, so they are a **basis**.

## What this settles and what it does not

**Settled**: the `n` sine vectors are a basis of `Fin n → ℝ`, so the adjacency matrix of the path
is diagonalised by them and `2 cos(kπ/(n+1))`, `k = 1 … n`, is its **whole** spectrum with
multiplicity.

**NOT settled, and unchanged from `PathAdjSpectrum`**: this is the **adjacency** matrix. The
estate's `GraphLaplacian.massive` is `D − A + m²` with the true degree, which on a path is `1` at
the ends, so these are eigenvectors of `2I − A + m²` and **not** of `massive`. `UNLOCK_WATCHLIST`'s
box item is about the latter and does not move. **No orthogonality is proved** — independence here
comes from distinct eigenvalues, not from an inner product — and **the box product is untouched**.
No cost is offered for either (`ERRATUM 194`, `ERRATUM 246`).
-/

namespace PathAdjBasis

open Finset Matrix SimpleGraph PathAdjSpectrum

variable {n : ℕ}

/-! ## 1. The angle lies strictly inside `(0, π)` -/

theorem angle_pos {k : ℕ} (hk : 0 < k) : 0 < (k : ℝ) * Real.pi / ((n : ℝ) + 1) := by
  have h1 : (0 : ℝ) < k := by exact_mod_cast hk
  have h2 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  positivity

theorem angle_lt_pi {k : ℕ} (hk : k ≤ n) : (k : ℝ) * Real.pi / ((n : ℝ) + 1) < Real.pi := by
  have h2 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_lt_iff₀ h2]
  have hkn : (k : ℝ) < (n : ℝ) + 1 := by
    have : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
    linarith
  nlinarith [Real.pi_pos]

/-! ## 2. The vector is nonzero -/

/-- **THE FIRST ENTRY IS `sin` OF AN ANGLE STRICTLY INSIDE `(0, π)`**, hence positive. -/
theorem pathVec_ne_zero {k : ℕ} (hpos : 0 < k) (hle : k ≤ n) (hn : 0 < n) :
    pathVec n k ≠ 0 := by
  intro hcon
  have h0 : pathVec n k ⟨0, hn⟩ = 0 := by rw [hcon]; rfl
  rw [pathVec, svec] at h0
  have : Real.sin ((k : ℝ) * Real.pi / ((n : ℝ) + 1)) = 0 := by
    simpa using h0
  have hpos' := Real.sin_pos_of_pos_of_lt_pi (angle_pos (n := n) hpos) (angle_lt_pi hle)
  rw [this] at hpos'
  exact lt_irrefl 0 hpos'

/-! ## 3. Distinct eigenvalues -/

/-- No range restriction is needed: `π/(n+1)` is a nonzero scalar, so the map is injective on all
of `ℕ`. The first version carried `0 < a ≤ n` on both arguments and the linter found all four
unused, so they are removed rather than underscored. -/
theorem angle_injective {a b : ℕ}
    (h : (a : ℝ) * Real.pi / ((n : ℝ) + 1) = (b : ℝ) * Real.pi / ((n : ℝ) + 1)) : a = b := by
  have h2 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp at h
  exact_mod_cast h

/-- **THE EIGENVALUES ARE DISTINCT ACROSS `1 … n`**, by `Real.injOn_cos` on `[0, π]`. -/
theorem eigenvalue_injective (n : ℕ) :
    Function.Injective fun k : Fin n =>
      2 * Real.cos ((k.val + 1 : ℕ) * Real.pi / ((n : ℝ) + 1)) := by
  intro a b hab
  simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at hab
  have hA : (a.val + 1 : ℝ) * Real.pi / ((n : ℝ) + 1) ∈ Set.Icc 0 Real.pi := by
    refine ⟨le_of_lt ?_, le_of_lt ?_⟩
    · exact_mod_cast angle_pos (n := n) (k := a.val + 1) (Nat.succ_pos _)
    · exact_mod_cast angle_lt_pi (n := n) (k := a.val + 1) a.isLt
  have hB : (b.val + 1 : ℝ) * Real.pi / ((n : ℝ) + 1) ∈ Set.Icc 0 Real.pi := by
    refine ⟨le_of_lt ?_, le_of_lt ?_⟩
    · exact_mod_cast angle_pos (n := n) (k := b.val + 1) (Nat.succ_pos _)
    · exact_mod_cast angle_lt_pi (n := n) (k := b.val + 1) b.isLt
  have := Real.injOn_cos hA hB (by exact_mod_cast hab)
  have := angle_injective (n := n) (by exact_mod_cast this)
  exact Fin.ext (by omega)

/-! ## 4. Independence and the basis -/

theorem hasEigenvector_pathVec (n : ℕ) (k : Fin n) :
    Module.End.HasEigenvector (Matrix.mulVecLin ((pathGraph n).adjMatrix ℝ))
      (2 * Real.cos ((k.val + 1 : ℕ) * Real.pi / ((n : ℝ) + 1))) (pathVec n (k.val + 1)) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact adjMatrix_mulVec_pathVec n (k.val + 1)
  · refine pathVec_ne_zero (Nat.succ_pos _) k.isLt ?_
    exact Nat.pos_of_ne_zero (by rintro rfl; exact k.elim0)

/-- **THE `n` SINE VECTORS ARE LINEARLY INDEPENDENT.** -/
theorem pathVec_linearIndependent (n : ℕ) :
    LinearIndependent ℝ fun k : Fin n => pathVec n (k.val + 1) :=
  Module.End.eigenvectors_linearIndependent' _ _ (eigenvalue_injective n) _
    (hasEigenvector_pathVec n)

/-- **AND THEY ARE A BASIS**, because there are `n` of them in an `n`-dimensional space. -/
noncomputable def pathBasis (n : ℕ) [NeZero n] : Module.Basis (Fin n) ℝ (Fin n → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank (pathVec_linearIndependent n)
    (by simp)

end PathAdjBasis
