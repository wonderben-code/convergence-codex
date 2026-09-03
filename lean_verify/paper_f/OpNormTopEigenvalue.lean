import RayleighAttainment

/-!
# The operator norm of a positive semidefinite matrix IS its greatest eigenvalue

`RayleighAttainment`'s header names exactly what it does not do, on the day it was written:

> *"It says nothing about existence. Whether some `v ≠ 0` attains the bound is exactly whether
> `‖A‖` is an eigenvalue, and this file supplies the equivalence, not the eigenvector.
> `RayleighMatrix.mv_eigenvectorBasis` is the estate's route to existence and is untouched here."*

This file takes that route. **`isGreatest_eigenvalue_opNorm`**: for a real matrix with `0 ≼ A` on a
nonempty finite type,

```
IsGreatest {μ | ∃ x ≠ 0, A *ᵥ x = μ • x} ‖A‖
```

— the operator norm is an eigenvalue, and no eigenvalue exceeds it.

## Why this was missing, measured rather than recalled

Probed 2026-09-03 across `paper_f/`: **every** `IsGreatest` or `IsLeast` about a spectrum in this
estate is about **one family** — `TorusSpectrumExtremes.isGreatest_spectrum_real_of_even`,
`isGreatest_signless_real`, `isLeast_signless_real_of_even` and
`MassiveTorusSpectrum.isLeast_spectrum_real`, all on the periodic lattice and all through the
Fourier characters — with `GreenDomainMonotone`'s variational `IsGreatest` the only other one and
about a different set. `spectralRadius` occurs in one file and only to record that Mathlib's is
about Banach algebras (`PerronBound`). **No general join between `‖·‖` and a spectrum existed.**

## What supplies each half

* **No eigenvalue exceeds `‖A‖`** — `GreenNormExact.abs_le_opNorm_of_mulVec_smul` (2026-09-03),
  which needs neither symmetry nor positivity, only `x ⬝ᵥ x ≠ 0`.
* **`‖A‖` is reached** — `le_smul_one_of_eigenvalues_le` below turns the eigenvalue ceiling into a
  Loewner ceiling, `OpNormLoewnerConverse.l2_opNorm_le_iff_le_smul_one` (2026-09-02) turns that
  into `‖A‖ ≤ max`, and the reverse inequality is the bullet above at the maximising eigenvector.
  So `‖A‖` **is** the maximum, and the eigenvector for it is `Matrix.IsHermitian.eigenvectorBasis`
  at the index where the maximum is attained.

**`le_smul_one_of_eigenvalues_le` is the general form of a lemma this estate had three times for
`massive`**: `CycleSpectralBound.massive_le_smul_one_of_eigenvalues_le` (through the cycle's
characters over `ℂ`), and the real spectral-theorem route inside
`LaplacianLoewnerConverse.exists_lt_massive_le_smul_one_of_eigenvalues_lt`, reused by
`LaplacianLoewnerDisconnected`. **The proof here is that route with `massive G m` replaced by `A`**;
nothing about it was specific to a graph, and `ERRATUM 337`'s remedy is to share rather than copy.
The three existing statements are **not** withdrawn — the cycle one is a different proof and the
`massive` ones are consumed under those names.

## What this is NOT

**Not a spectral theorem.** Mathlib's `Matrix.IsHermitian.spectral_theorem` does the work, through
`RayleighMatrix`; what is new is the identification of the maximum with the norm.

**Not the least eigenvalue.** `‖A‖` is a ceiling and says nothing about the bottom of the spectrum;
`MassiveTorusSpectrum.isLeast_spectrum_real` remains the estate's only `IsLeast` for a Laplacian
and is a statement about one family.

**Not a route to the periodic lattice's extremes.** `TorusSpectrumExtremes` computes which
frequency attains the top and crosses to `ℂ`; this does neither, and neither supersedes the other.

**No wall moves.** `W1` asks for a lower bound on the cross form (`WALLS.md` §W1.5), which is a
different object on a different operator.

**⚠ THE REASON THAT SENTENCE GIVES IS FALSE AND IT IS KEPT AS WRITTEN** (`ERRATUM 94`,
**`ERRATUM 441`**, 2026-09-03). *"No wall moves"* stands; what `W1` asks for does not.
`ReflectionPositive → hcross` has been a **theorem** since 2026-08-13 —
`ReflectionConverse.reflectionPositive_iff_hcross`, on every finite graph at every mass with no
fixed point — and with a fixed layer the converse is **refuted**
(`MirrorConverseFails.converse_fails_with_mirror`). `W1`'s open part is `OS0`/`OS1`/`OS4`, which is
what `W1`'s own row in `WALLS.md` says.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace OpNormTopEigenvalue

open Matrix Finset GraphLaplacian SimpleGraph
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] {A : Matrix V V ℝ}

/-! ## 1. An eigenvalue ceiling is a Loewner ceiling, for any real symmetric matrix -/

/-- **AN EIGENVALUE CEILING IS A LOEWNER CEILING.** The `massive`-specific form of this is inside
`LaplacianLoewnerConverse.exists_lt_massive_le_smul_one_of_eigenvalues_lt`; nothing in that proof
was about a graph. -/
theorem le_smul_one_of_eigenvalues_le (hA : A.IsHermitian) {M : ℝ}
    (hmax : ∀ j, hA.eigenvalues j ≤ M) :
    A ≤ M • (1 : Matrix V V ℝ) := by
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_))
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    refine Matrix.IsSymm.sub ?_ ?_
    · rw [Matrix.smul_one_eq_diagonal]
      exact Matrix.isSymm_diagonal _
    · rw [Matrix.IsSymm, ← Matrix.conjTranspose_eq_transpose_of_trivial]
      exact hA
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg]
    have h1 : x ⬝ᵥ (M • (1 : Matrix V V ℝ)) *ᵥ x = M * (x ⬝ᵥ x) := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    rw [h1]
    have h2 := RayleighMatrix.quadForm_le_of_eigenvalues_le hA hmax (WithLp.toLp 2 x)
    rwa [LaplacianLoewnerConverse.inner_mv_eq, LaplacianLoewnerConverse.inner_self_eq] at h2

/-! ## 2. The maximum is attained, by an eigenvector of the basis -/

/-- **THE GREATEST EIGENVALUE IS ATTAINED**, at the index where the eigenvalue family attains its
maximum. Stated in the plain matrix currency rather than on `EuclideanSpace`. -/
theorem exists_eigenvector_sup' [Nonempty V] (hA : A.IsHermitian) :
    ∃ x : V → ℝ, x ≠ 0 ∧
      A *ᵥ x = (Finset.univ.sup' Finset.univ_nonempty hA.eigenvalues) • x := by
  classical
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := V)) hA.eigenvalues
  refine ⟨WithLp.ofLp (hA.eigenvectorBasis j), ?_, ?_⟩
  · intro h0
    have h1 : ‖hA.eigenvectorBasis j‖ = 1 := (hA.eigenvectorBasis).orthonormal.1 j
    have h2 : (hA.eigenvectorBasis j : EuclideanSpace ℝ V) = 0 := by
      apply WithLp.ofLp_injective (p := 2)
      simpa using h0
    rw [h2, norm_zero] at h1
    exact absurd h1 (by norm_num)
  · have hmv := RayleighMatrix.mv_eigenvectorBasis hA j
    have := congrArg (WithLp.ofLp (p := 2)) hmv
    simpa [RayleighMatrix.mv, hj] using this

/-! ## 3. The identification -/

/-- **THE OPERATOR NORM IS THE GREATEST EIGENVALUE**, for `0 ≼ A` on a nonempty finite type — an
eigenvalue, and an upper bound for every eigenvalue. This is the existence statement
`RayleighAttainment`'s header declined to prove. -/
theorem isGreatest_eigenvalue_opNorm [Nonempty V] (hA : 0 ≤ A) :
    IsGreatest {μ : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ A *ᵥ x = μ • x} ‖A‖ := by
  classical
  have hps : A.PosSemidef := by simpa using Matrix.le_iff.mp hA
  set M := Finset.univ.sup' Finset.univ_nonempty hps.isHermitian.eigenvalues with hM
  have hle : ‖A‖ ≤ M :=
    (OpNormLoewnerConverse.l2_opNorm_le_iff_le_smul_one hA).mpr
      (le_smul_one_of_eigenvalues_le hps.isHermitian
        (fun j => Finset.le_sup' _ (Finset.mem_univ j)))
  obtain ⟨x, hx0, hx⟩ := exists_eigenvector_sup' (A := A) hps.isHermitian
  have hxx : x ⬝ᵥ x ≠ 0 := fun h => hx0 (dotProduct_self_eq_zero.1 h)
  have hge : M ≤ ‖A‖ := le_trans (le_abs_self M)
    (GreenNormExact.abs_le_opNorm_of_mulVec_smul hxx hx)
  have hnorm : ‖A‖ = M := le_antisymm hle hge
  refine ⟨⟨x, hx0, by rw [hnorm]; exact hx⟩, ?_⟩
  rintro μ ⟨y, hy0, hy⟩
  have hyy : y ⬝ᵥ y ≠ 0 := fun h => hy0 (dotProduct_self_eq_zero.1 h)
  exact le_trans (le_abs_self μ) (GreenNormExact.abs_le_opNorm_of_mulVec_smul hyy hy)

/-! ## 4. The general form of a statement this estate had for one family -/

/-- **THE MASSIVE LAPLACIAN'S GREATEST EIGENVALUE IS ITS NORM**, at every finite nonempty graph.
`TorusSpectrumExtremes.isGreatest_spectrum_real_of_even` and `MassiveTorusSpectrum
.isLeast_spectrum_real` are the periodic lattice's extremes and are **not** re-proved here: this is
the same set with `‖massive G m‖` in place of a computed frequency, and it drops the family. -/
theorem isGreatest_eigenvalue_massive [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {m : ℝ} (hm : m ≠ 0) :
    IsGreatest {μ : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ massive G m *ᵥ x = μ • x} ‖massive G m‖ :=
  isGreatest_eigenvalue_opNorm (massive_posDef G hm).posSemidef.nonneg

/-- **AND ON A REGULAR GRAPH THE GREATEST EIGENVALUE IS `2Δ + m²` EXACTLY WHEN SOME COMPONENT IS
TWO-COLOURABLE.** The periodic lattice's version of this needs `Even n` and the cosines; this needs
neither, and holds at every `Δ`-regular graph, connected or not. -/
theorem isGreatest_eigenvalue_massive_iff_colorable [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) {m : ℝ} (hm : m ≠ 0) :
    IsGreatest {μ : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ massive G m *ᵥ x = μ • x} (2 * (Δ : ℝ) + m ^ 2)
      ↔ ∃ C : G.ConnectedComponent, (G.induce C.supp).Colorable 2 := by
  constructor
  · intro hg
    refine (LaplacianNormSharp.norm_massive_eq_iff_exists_component_colorable G hreg hm).mp ?_
    exact (isGreatest_eigenvalue_massive G hm).unique hg
  · intro hcol
    have h := (LaplacianNormSharp.norm_massive_eq_iff_exists_component_colorable G hreg hm).mpr hcol
    exact h ▸ isGreatest_eigenvalue_massive G hm

end OpNormTopEigenvalue
