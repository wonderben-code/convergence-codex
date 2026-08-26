/-
  IsingSlabTransfer.lean — the transfer matrix over an arbitrary finite
  cross-section, and hence a spectral gap for the THREE-dimensional Ising slab.

  WHY. `PROOF_STRATEGY` §7 rule 3: take a result proved under a restrictive
  hypothesis and remove one, and **dimension** is the first fence it names. The
  whole W4 strip chain is stated at `IsingTransfer2D.Col n = Fin (n+1) → Bool`
  and reads as two-dimensional. **It is not.** Grepping the chain for any use of
  the column's own structure — the successor `i + 1` that makes a column a
  one-dimensional ring — finds it in exactly one place, inside `intra`. Every
  object built on top (`inter`, `transfer2`, `halfIntra`, `horiz`, `transferSym`)
  treats the column as an **opaque index type**, and every theorem about them
  (`transferSym_pos`, `transferSym_isHermitian`, and all of `PerronGap`) is
  already polymorphic in it.

  So the fence is one definition deep, and this file removes it.

  WHAT THIS FILE PROVES:
  1. **`transferG`** — the symmetrised transfer matrix for an arbitrary finite
     cross-section `V` and an arbitrary intra-section energy `E : (V → Bool) → ℝ`.
     `interG` is the bond energy between adjacent sections and is symmetric
     (`interG_comm`); `transferG_pos` and `transferG_isHermitian` follow, and
     their proofs are the two-dimensional ones with `Fin (n+1)` replaced by `V`.
  2. **`transferSym_eq_transferG`** — the estate's `transferSym β n` **is**
     `transferG` at `V = Fin (n+1)` and `E = intra`, by `rfl`. This is what makes
     the general object the same object rather than an analogy (`ERRATUM 201`),
     and it is why nothing downstream had to move.
  3. **`transferG_gap`** — for every cross-section, every eigenvalue off the top
     is strictly smaller in modulus. This is `PerronGap.abs_eigenvalues_lt_of_ne`
     instantiated: that theorem was **already** stated for an arbitrary index
     type, so the two-dimensional chain had been consuming a general result
     through a special-case interface.
  4. **`slabIntra` and `slab_gap`** — the payoff, and the reason this is not
     generalisation for its own sake. Take `V = Fin (a+1) × Fin (b+1)` with its
     nearest-neighbour energy: the cross-section is now a two-dimensional torus,
     the transfer direction is a third, and **`slab_gap` is a spectral gap for the
     THREE-DIMENSIONAL Ising slab.** The estate had no three-dimensional Ising
     object of any kind before this file.

  WHAT THIS IS NOT, AND THE WALL DOES NOT MOVE.
  **It is not a mass gap and it is not progress on `WALLS` §W4 item 3.** The
  cross-section is FIXED and finite; the gap is a gap for one finite matrix, as
  it was at `d = 2`, and the open question is unchanged — whether the sub-top
  ratio stays away from 1 as the cross-section GROWS
  (`IsingTopRatio.UniformSubTopRatio`, proved at no `β` but `0`; a route is recorded
  from 2026-08-26 — `SpectralEntryRatio` — and does not reach it, `ERRATUM 269`). What
  changes is that the question is now the same question in every dimension rather
  than a two-dimensional question, which is worth knowing before anyone attempts
  it in the belief that `d = 2` is special. **It is not: nothing in the chain ever
  used `d = 2`.**

  **AND THE DECAY CHAIN IS NOT TRANSPORTED.** `corr2Sep` and everything above it —
  the spectral formula, the length limit, the rate, the vanishing constant — are
  stated at `Col n` and are NOT restated here. Transporting them is mechanical in
  the same sense this file was mechanical, and it is not done; what is done is the
  base and the gap. Anyone continuing should expect the same result: the
  statements move and the proofs do not change.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingTopRatio

namespace IsingSlabTransfer

open Finset Matrix Real
open IsingTransfer2D IsingTransferSym

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The transfer matrix over an arbitrary cross-section -/

/-- A configuration of one cross-section. At `V = Fin (n+1)` this is
`IsingTransfer2D.Col n`, definitionally. -/
abbrev Cross (V : Type*) := V → Bool

/-- **The bonds between two adjacent cross-sections.** One bond per site, exactly as
`IsingTransfer2D.inter`, which is this at `V = Fin (n+1)`. -/
def interG (σ τ : Cross V) : ℝ := ∑ v : V, spin (σ v) * spin (τ v)

omit [DecidableEq V] in
theorem interG_comm (σ τ : Cross V) : interG σ τ = interG τ σ :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- Half of each cross-section's own weight, given to both sides. -/
noncomputable def halfIntraG (β : ℝ) (E : Cross V → ℝ) : Matrix (Cross V) (Cross V) ℝ :=
  Matrix.diagonal fun σ => exp (β * E σ / 2)

/-- The weight of the bonds between adjacent sections. -/
noncomputable def horizG (β : ℝ) : Matrix (Cross V) (Cross V) ℝ :=
  fun σ τ => exp (β * interG σ τ)

/-- **THE SYMMETRISED TRANSFER MATRIX OVER AN ARBITRARY CROSS-SECTION.** The energy `E` of a
section is a parameter: nothing below depends on how it is computed, which is precisely why the
two-dimensional chain never needed the column to be one-dimensional. -/
noncomputable def transferG (β : ℝ) (E : Cross V → ℝ) : Matrix (Cross V) (Cross V) ℝ :=
  halfIntraG β E * horizG β * halfIntraG β E

theorem transferG_apply (β : ℝ) (E : Cross V → ℝ) (σ τ : Cross V) :
    transferG β E σ τ = exp (β * E σ / 2) * exp (β * interG σ τ) * exp (β * E τ / 2) := by
  simp [transferG, halfIntraG, horizG, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem transferG_pos (β : ℝ) (E : Cross V → ℝ) (σ τ : Cross V) : 0 < transferG β E σ τ := by
  rw [transferG_apply]
  positivity

/-- **AND IT IS HERMITIAN**, because the bond energy between two sections does not care which is
which. The proof is `IsingTransferSym.transferSym_isHermitian` with `Fin (n+1)` erased. -/
theorem transferG_isHermitian (β : ℝ) (E : Cross V → ℝ) :
    Matrix.IsHermitian (transferG β E) := by
  ext σ τ
  simp only [Matrix.conjTranspose_apply, star_trivial, transferG_apply, interG_comm τ σ]
  ring

/-! ## 2. The two-dimensional chain is the instance

`ERRATUM 201`: a generalisation that is not instantiated is an assertion about usefulness. This is
the instantiation, and it is `rfl` — the general object is the same object, not a parallel one. -/

/-- **`IsingTransferSym.transferSym` IS `transferG`**, at `V = Fin (n+1)` and `E = intra`. -/
theorem transferSym_eq_transferG (β : ℝ) (n : ℕ) :
    transferSym β n = transferG β (intra (n := n)) := rfl

/-! ## 3. The gap, at every cross-section

`PerronGap.abs_eigenvalues_lt_of_ne` is stated for an arbitrary index type. The two-dimensional
chain has been consuming a general theorem through a special-case interface. -/

/-- **EVERY EIGENVALUE OFF THE TOP IS STRICTLY SMALLER IN MODULUS**, at every finite
cross-section and every intra-section energy. -/
theorem transferG_gap (β : ℝ) (E : Cross V → ℝ) {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β E).eigenvalues j
      ≤ (transferG_isHermitian β E).eigenvalues p₀) {q : Cross V}
    (hne : (transferG_isHermitian β E).eigenvalues q
      ≠ (transferG_isHermitian β E).eigenvalues p₀) :
    |(transferG_isHermitian β E).eigenvalues q|
      < (transferG_isHermitian β E).eigenvalues p₀ :=
  PerronGap.abs_eigenvalues_lt_of_ne _ (fun i j => transferG_pos β E i j) hp₀ hne

/-- The top eigenvalue is strictly positive, at every cross-section. -/
theorem transferG_top_pos (β : ℝ) (E : Cross V → ℝ) {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β E).eigenvalues j
      ≤ (transferG_isHermitian β E).eigenvalues p₀) :
    0 < (transferG_isHermitian β E).eigenvalues p₀ :=
  PerronGap.eigenvalue_max_pos _ (fun i j => transferG_pos β E i j) hp₀

/-! ## 4. The three-dimensional slab

A cross-section that is itself two-dimensional. Nothing above changes; only `V` does. -/

/-- **A TWO-DIMENSIONAL CROSS-SECTION'S OWN ENERGY** — nearest neighbours in both directions,
wrapping, exactly as `IsingTransfer2D.intra` does in one. -/
def slabIntra {a b : ℕ} (σ : Cross (Fin (a + 1) × Fin (b + 1))) : ℝ :=
  ∑ p : Fin (a + 1) × Fin (b + 1),
    (spin (σ p) * spin (σ (p.1 + 1, p.2)) + spin (σ p) * spin (σ (p.1, p.2 + 1)))

/-- **THE THREE-DIMENSIONAL ISING SLAB'S TRANSFER MATRIX.** Two dimensions in the cross-section,
one in the transfer direction. -/
noncomputable def slabTransfer (β : ℝ) (a b : ℕ) :
    Matrix (Cross (Fin (a + 1) × Fin (b + 1))) (Cross (Fin (a + 1) × Fin (b + 1))) ℝ :=
  transferG β slabIntra

theorem slabTransfer_pos (β : ℝ) (a b : ℕ) (σ τ : Cross (Fin (a + 1) × Fin (b + 1))) :
    0 < slabTransfer β a b σ τ :=
  transferG_pos β slabIntra σ τ

theorem slabTransfer_isHermitian (β : ℝ) (a b : ℕ) :
    Matrix.IsHermitian (slabTransfer β a b) :=
  transferG_isHermitian β slabIntra

/-- **A SPECTRAL GAP FOR THE THREE-DIMENSIONAL ISING SLAB.** The estate had no three-dimensional
Ising object at all before this file, and the proof is the two-dimensional one with the
cross-section's type changed — which is the finding, not the theorem. **This is not a mass gap**:
the cross-section is fixed and finite, and what is open is the same uniformity as at `d = 2`. -/
theorem slab_gap (β : ℝ) (a b : ℕ) {p₀ : Cross (Fin (a + 1) × Fin (b + 1))}
    (hp₀ : ∀ j, (slabTransfer_isHermitian β a b).eigenvalues j
      ≤ (slabTransfer_isHermitian β a b).eigenvalues p₀)
    {q : Cross (Fin (a + 1) × Fin (b + 1))}
    (hne : (slabTransfer_isHermitian β a b).eigenvalues q
      ≠ (slabTransfer_isHermitian β a b).eigenvalues p₀) :
    |(slabTransfer_isHermitian β a b).eigenvalues q|
      < (slabTransfer_isHermitian β a b).eigenvalues p₀ :=
  transferG_gap β slabIntra hp₀ hne

end IsingSlabTransfer
