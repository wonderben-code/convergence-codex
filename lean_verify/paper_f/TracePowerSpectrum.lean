import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# `Tr(Aᵏ) = ∑ λᵢᵏ`, and no triangularisation anywhere

`UNLOCK_WATCHLIST`'s **TRACE-TO-SPECTRUM BRIDGE** (opened 12 August, `ERRATUM 141`) splits the
step from `SpectralAction` §§9-10's TRACE statements to SINGULAR-VALUE statements into three legs
and says of the first:

> "(i) `Tr(Aᵏ) = ∑ λᵢᵏ`, the roots taken with multiplicity. Mathlib has the `k = 1` case
> (`Matrix.trace_eq_sum_roots_charpoly`) and NOT the general one; **the gap is triangularisation
> over an algebraically closed field.** … Leg (i) is the one that is a project rather than a
> lemma."

**Leg (i) is proved here, for an arbitrary endomorphism of a finite-dimensional space over any
algebraically closed field, and the quoted reason is FALSE.** Nothing in this file triangularises
anything. `ERRATUM 179` records the claim; the proof is below.

## What is proved

* `restrict_sub_algebraMap_nilpotent`, `trace_restrict_pow` — on the generalised eigenspace at `μ`,
  the restriction is `μ` plus a nilpotent, so the `k`-th power of the restriction has trace
  `μᵏ · dim`;
* `trace_pow_eq_sum_over_eigen` — the generalised eigenspaces of `f` are independent and span, so
  `Tr(fᵏ)` is the sum of those over the finitely many `μ` with a nonzero eigenspace;
* `count_roots_charpoly`, `toFinset_eq` — that dimension IS the multiplicity of `μ` as a root of
  the characteristic polynomial, and the two index sets agree;
* **`trace_pow_eq_sum_roots_charpoly`** — hence `Tr(fᵏ) = ∑ λᵏ` over `charpoly.roots` with
  multiplicity, and **`Matrix.trace_pow_eq_sum_roots_charpoly`**, the same for a matrix. That is
  leg (i) as the item states it.
* `herm_trace_pow` — the Hermitian corollary, indexed by the eigenvalue function rather than by the
  root multiset;
* `trace_pow_mul_conjTranspose` — the corollary at `M * Mᴴ`, which is the matrix `SpectralAction`
  §§9-10 actually carry.

## Why triangularisation is not needed

The classical proof conjugates `A` to upper-triangular form and reads the diagonal. This one uses
the generalised eigenspace decomposition instead, and every ingredient was already in Mathlib:

* `Module.End.iSup_maxGenEigenspace_eq_top` — over an algebraically closed field the generalised
  eigenspaces span (`Eigenspace/Triangularizable.lean`, a file whose NAME is why a name-probe for
  `schurTriangulation` missed it);
* `Module.End.independent_maxGenEigenspace` — and they are independent, so the sum is direct;
* `LinearMap.trace_eq_sum_trace_restrict'` — the trace of an endomorphism of a direct sum is the
  sum of the traces of the restrictions;
* `LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent` — `Tr(g ∘ f) = μ · Tr(g)` when `g`
  commutes with `f` and `f - μ` is nilpotent. Iterating this IS the induction on `k`, and it is the
  step the triangular proof spends a basis on;
* `LinearMap.finrank_maxGenEigenspace_eq` — the dimension of the generalised eigenspace at `μ` is
  the multiplicity of `μ` as a root of the characteristic polynomial. This is the one that makes
  the bookkeeping come out, and it is the one nobody looked for.

**So the blocker was not that the mathematics was hard; it was that the sentence named the
textbook proof's ingredient and then nobody checked whether a different proof needed it.**
`ERRATA 163, 164, 165, 169, 172, 175, 178` are the same shape. This is the eighth.

## What this does NOT do, and why the item does not close

The item has three legs and this is one of them. Legs (ii) and (iii) — power sums determine the
elementary symmetric functions in characteristic zero, and equal characteristic polynomials give
the same root multiset — are **not** proved here, so the item's second clause, *"equal trace
moments imply the same eigenvalue multiset"*, is still not available. `SpectralAction` §10's
"THE ONE STEP THAT IS NOT PROVED HERE" paragraph therefore still stands as written, and no tag,
docstring or claim anywhere in the estate moves on the strength of this file.

**A second correction, `ERRATUM 180`.** The item's `STATUS 15 AUG 2026` entry dismissed the
Hermitian spectral theorem as unable to serve `SpectralAction` §§9-10 because *"its operator
`Dlin M` is not self-adjoint"*. The traces §§9-10 actually state are of `(M * Mᴴ) ^ k`
(`trace_pow_eq_spectralAction`, `moments_of_spectralAction_congr`,
`spectralAction_congr_tfae`), and `M * Mᴴ` **is** Hermitian
(`Matrix.isHermitian_mul_conjTranspose_self`). The dismissal named the wrong matrix. It is moot
for the mathematics — the general theorem below covers both — but it is a false sentence in the
record and `trace_pow_mul_conjTranspose` is the one-line consequence it said was unavailable.
-/

namespace TracePowerSpectrum

open Module Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-! ## 1. On one generalised eigenspace -/

/-- **THE RESTRICTION IS `μ` PLUS A NILPOTENT.** Mathlib's
`isNilpotent_restrict_maxGenEigenspace_sub_algebraMap` states this for the restriction of the
DIFFERENCE `f - μ`; what the trace lemma below needs is the difference of the restrictions. The two
are equal, and `ext` is the whole proof — but the equality cannot be produced by `rw`, because
rewriting inside `LinearMap.restrict` moves a term the `Set.MapsTo` proof depends on. -/
theorem restrict_sub_algebraMap_nilpotent (f : Module.End K V) (μ : K)
    (h : Set.MapsTo f (f.maxGenEigenspace μ) (f.maxGenEigenspace μ)) :
    IsNilpotent (f.restrict h - algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) := by
  have hbase := f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
  have hEq : LinearMap.restrict (f - algebraMap K (Module.End K V) μ)
        (Module.End.mapsTo_maxGenEigenspace_of_comm
          ((Commute.refl f).sub_right (Algebra.commute_algebraMap_right μ f)) μ)
      = f.restrict h - algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ := by
    ext x
    simp [LinearMap.restrict_apply, Algebra.algebraMap_eq_smul_one]
  rw [← hEq]
  exact hbase

/-- **`Tr((f|_{V_μ})ᵏ) = μᵏ · dim V_μ`.** The induction is one application of
`trace_comp_eq_mul_of_commute_of_isNilpotent` per step: `Tr(Fᵐ ∘ F) = μ · Tr(Fᵐ)` because `F`
commutes with its own powers and `F - μ` is nilpotent. The base case is `Tr(id) = dim`.

**This is the step the textbook proof spends a triangularising basis on.** -/
theorem trace_restrict_pow (f : Module.End K V) (μ : K)
    (h : Set.MapsTo f (f.maxGenEigenspace μ) (f.maxGenEigenspace μ)) (k : ℕ) :
    LinearMap.trace K _ ((f.restrict h) ^ k)
      = μ ^ k * (finrank K (f.maxGenEigenspace μ) : K) := by
  have hnil := restrict_sub_algebraMap_nilpotent f μ h
  induction k with
  | zero => simp
  | succ m ih =>
      have hcomp : (f.restrict h) ^ (m + 1) = ((f.restrict h) ^ m) ∘ₗ (f.restrict h) := by
        rw [pow_succ]; rfl
      rw [hcomp, LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ
        ((Commute.refl (f.restrict h)).pow_left m) hnil, ih]
      ring

/-! ## 2. Summing over the decomposition -/

/-- Only finitely many `μ` have a nonzero generalised eigenspace — from independence alone, with no
algebraic closure and no counting. -/
theorem finite_ne_bot (f : Module.End K V) : {μ : K | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace

/-- **`Tr(fᵏ)` IS THE SUM OF THE EIGENSPACE CONTRIBUTIONS.** Algebraic closure enters exactly here
and nowhere else: it is what makes the generalised eigenspaces span. -/
theorem trace_pow_eq_sum_over_eigen [IsAlgClosed K] (f : Module.End K V) (k : ℕ) :
    LinearMap.trace K V (f ^ k)
      = ∑ μ ∈ (finite_ne_bot f).toFinset,
          μ ^ k * (finrank K (f.maxGenEigenspace μ) : K) := by
  classical
  have hds : DirectSum.IsInternal f.maxGenEigenspace :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      f.independent_maxGenEigenspace f.iSup_maxGenEigenspace_eq_top
  have hmaps : ∀ μ : K, Set.MapsTo (f ^ k)
      (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) := fun μ =>
    Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.pow_right rfl k) μ
  rw [LinearMap.trace_eq_sum_trace_restrict' hds (finite_ne_bot f) hmaps]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h1 : Set.MapsTo f (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) :=
    Module.End.mapsTo_maxGenEigenspace_of_comm rfl μ
  rw [← Module.End.pow_restrict (f' := f) k h1 (hmaps μ), trace_restrict_pow f μ h1 k]

/-! ## 3. The dimension is the root multiplicity -/

/-- **THE ONE NOBODY LOOKED FOR.** `LinearMap.finrank_maxGenEigenspace_eq` says the dimension of
the generalised eigenspace at `μ` is the multiplicity of `μ` as a root of the characteristic
polynomial; `Polynomial.count_roots` says that multiplicity is the multiset count. Together they
turn the eigenspace sum into a sum over the root multiset — with no hypothesis on `K` beyond being
a field, and no algebraic closure. -/
theorem count_roots_charpoly [DecidableEq K] (f : Module.End K V) (μ : K) :
    Multiset.count μ (LinearMap.charpoly f).roots = finrank K (f.maxGenEigenspace μ) := by
  classical
  rw [Polynomial.count_roots, LinearMap.finrank_maxGenEigenspace_eq]

/-- Hence the two index sets agree: a `μ` with a nonzero generalised eigenspace is exactly a root of
the characteristic polynomial. -/
theorem toFinset_eq [DecidableEq K] (f : Module.End K V) :
    (finite_ne_bot f).toFinset = (LinearMap.charpoly f).roots.toFinset := by
  classical
  ext μ
  rw [Set.Finite.mem_toFinset, Multiset.mem_toFinset, ← Multiset.count_ne_zero,
    count_roots_charpoly]
  exact not_congr Submodule.finrank_eq_zero.symm

/-! ## 4. Leg (i) -/

/-- **`Tr(fᵏ) = ∑ λᵢᵏ`, THE ROOTS OF THE CHARACTERISTIC POLYNOMIAL WITH MULTIPLICITY, FOR AN
ARBITRARY ENDOMORPHISM OVER AN ALGEBRAICALLY CLOSED FIELD.**

This is leg (i) of the `TRACE-TO-SPECTRUM BRIDGE`, which said the gap was triangularisation. There
is no triangularisation in the proof. Mathlib's `Matrix.trace_eq_sum_roots_charpoly` is the `k = 1`
case; nothing below specialises to it, since the two proofs share no step. -/
theorem trace_pow_eq_sum_roots_charpoly [IsAlgClosed K] (f : Module.End K V) (k : ℕ) :
    LinearMap.trace K V (f ^ k)
      = ((LinearMap.charpoly f).roots.map (fun z => z ^ k)).sum := by
  classical
  rw [trace_pow_eq_sum_over_eigen f k, Finset.sum_multiset_map_count, toFinset_eq]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [count_roots_charpoly, nsmul_eq_mul, mul_comm]

end TracePowerSpectrum

namespace Matrix

open TracePowerSpectrum

/-- **THE SAME FOR A MATRIX**, which is the form the watchlist item states. `Matrix.toLin'` carries
powers to powers, traces to traces and the characteristic polynomial to the characteristic
polynomial, so the endomorphism statement transports with three rewrites. -/
theorem trace_pow_eq_sum_roots_charpoly {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    [IsAlgClosed K] (A : Matrix n n K) (k : ℕ) :
    (A ^ k).trace = (A.charpoly.roots.map (fun z => z ^ k)).sum := by
  rw [← Matrix.trace_toLin'_eq (A ^ k), Matrix.toLin'_pow,
    TracePowerSpectrum.trace_pow_eq_sum_roots_charpoly, Matrix.charpoly_toLin']

/-- **THE HERMITIAN COROLLARY**, indexed by the eigenvalue function rather than by the root
multiset, and with the eigenvalues real. Derived from the general theorem above, NOT from the
spectral theorem: `IsHermitian.roots_charpoly_eq_eigenvalues` is the only extra step. -/
theorem herm_trace_pow {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, ((hA.eigenvalues i : ℂ)) ^ k := by
  rw [Matrix.trace_pow_eq_sum_roots_charpoly A k, hA.roots_charpoly_eq_eigenvalues,
    Multiset.map_map]
  rfl

/-- **THE MOMENTS `SpectralAction` §§9-10 CARRY.** Their statements are about `((M * Mᴴ) ^ k).trace`
and `M * Mᴴ` is Hermitian, so those moments are power sums of a family of REAL eigenvalues.

`UNLOCK_WATCHLIST`'s `STATUS 15 AUG 2026` said the Hermitian case could not serve §§9-10 because
`Dlin M` is not self-adjoint; §§9-10 never take a trace of `Dlin M` alone. `ERRATUM 180`. -/
theorem trace_pow_mul_conjTranspose {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (k : ℕ) :
    ((M * Mᴴ) ^ k).trace
      = ∑ i, (((Matrix.isHermitian_mul_conjTranspose_self M).eigenvalues i : ℂ)) ^ k :=
  herm_trace_pow (Matrix.isHermitian_mul_conjTranspose_self M) k

/-! ## 5. That the statement is the right one, and not vacuous

Two checks, both of which a mis-stated theorem would fail.

The first is agreement with Mathlib where Mathlib has an answer. The second is the case the
watchlist item said needed triangularisation: **a matrix no basis diagonalises.** The Jordan block
at `2` has a one-dimensional eigenspace and a two-dimensional generalised one, which is exactly the
configuration the proof above handles by the nilpotent shift rather than by a triangularising
basis. -/

/-- **AGREEMENT AT `k = 1`.** `Matrix.trace_eq_sum_roots_charpoly` is Mathlib's `k = 1` case; the
general theorem specialises to it. The two proofs share no step, so this is a check and not a
tautology. -/
theorem trace_eq_sum_roots_charpoly_of_pow {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    [IsAlgClosed K] (A : Matrix n n K) : A.trace = A.charpoly.roots.sum := by
  simpa using Matrix.trace_pow_eq_sum_roots_charpoly A 1

/-- The Jordan block at `2`. Its eigenspace at `2` is a line and its generalised eigenspace is the
plane, so it is not diagonalisable over any field. -/
noncomputable def jordanTwo : Matrix (Fin 2) (Fin 2) ℂ := !![2, 1; 0, 2]

/-- Its characteristic polynomial is `(X - 2)²` — a repeated root, which is the whole point. -/
theorem charpoly_jordanTwo : jordanTwo.charpoly = (Polynomial.X - Polynomial.C 2) ^ 2 := by
  rw [Matrix.charpoly_fin_two]
  simp [jordanTwo]
  ring

/-- So its root multiset is `{2, 2}`: one root, counted twice. -/
theorem roots_charpoly_jordanTwo : jordanTwo.charpoly.roots = {2, 2} := by
  rw [charpoly_jordanTwo, Polynomial.roots_pow, Polynomial.roots_X_sub_C]
  rfl

/-- **AND THE THEOREM READS `Tr(Jᵏ) = 2ᵏ + 2ᵏ` OFF A NON-DIAGONALISABLE MATRIX.** No triangular
form was constructed to get here. -/
theorem trace_pow_jordanTwo (k : ℕ) : (jordanTwo ^ k).trace = 2 ^ k + 2 ^ k := by
  rw [Matrix.trace_pow_eq_sum_roots_charpoly, roots_charpoly_jordanTwo]
  simp

end Matrix
