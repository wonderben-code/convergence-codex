/-
  AdjEigenvectorBound: the maximum degree bounds an adjacency eigenvalue — in EIGENVECTOR form,
  at every finite graph, and without an operator norm

  WHY THIS FILE EXISTS. `RE-SWEEP #60` (2026-09-16) tried to price a ceiling on the second
  eigenvalue of the cone's signless Laplacian, found that unit 80's `eigenvalue_dichotomy`
  reduces it to a degree bound on the rim's adjacency eigenvalues, and then found **the shape was
  missing**. What the estate holds is two things, neither of them usable there:

  * `AdjSpectrumBracket.abs_eigenvalues_adjMatrix_le` — general, and stated about
    `IsHermitian.eigenvalues j`. That is the INDEXING form, and joining it to a statement about
    an eigenVECTOR is the fence this whole cluster keeps meeting. Its proof goes through
    `topEigen`, `NonnegPerronNorm` and the symmetric operator norm.
  * `BoxSpectrumComplete.abs_le_of_eigenvalue` — eigenvector form, and **only for the box**.

  Checked by query before writing, not recalled: over the 14440-statement index, no statement
  outside the box, torus and massive families takes *a nonzero eigenvector of the adjacency
  matrix* as a hypothesis and concludes a bound. `PROOF_STRATEGY` §7 item 3 — *remove one
  restrictive hypothesis* — and the hypothesis removed here is **the family**.

  **AND THE GENERAL STATEMENT IS CHEAPER THAN THE SPECIAL ONE.** This file imports one Mathlib
  module and uses no operator norm, no Perron theory, no spectral theorem and no Hermitian
  structure: pick the coordinate of largest modulus, and the eigenvector equation at that
  coordinate is the whole proof. The estate's existing general bound needs
  `NonnegPerronNorm` + `FrobeniusTopBound` + `SymmetricOpNorm` because it is answering a harder
  question — where an eigenvalue sits in an ENUMERATION — and that is worth saying plainly
  rather than reading as a redundancy.

  WHAT IS PROVED.

  * **`exists_abs_max`** — a nonzero vector on a `Fintype` has a coordinate of maximal modulus,
    and that modulus is positive. Stated separately because it is the only thing the argument
    needs that is not the eigenvector equation.
  * **`abs_le_of_mulVec_eq_smul`** — if `A_G *ᵥ x = μ • x` with `x ≠ 0` and every degree is at
    most `Δ`, then `|μ| ≤ Δ`. At every finite graph, with no regularity, no connectivity and no
    bound on the number of vertices.
  * **`mem_Icc_of_mulVec_eq_smul`** — the same, bracketed on both sides.
  * **`abs_le_of_regular`** — the corollary this was built for: on a `d`-regular graph every
    adjacency eigenvalue carried by an eigenvector satisfies `|μ| ≤ d`.
  * **`abs_le_maxDegree_of_mulVec_eq_smul`** — and with Mathlib's `SimpleGraph.maxDegree` in
    place of an abstract `Δ`, so a consumer with no `Δ` in hand can still use it.

  WHAT IS **NOT** CLAIMED.

  * **NOTHING ABOUT SHARPNESS.** `|μ| ≤ Δ` is attained on a `Δ`-regular graph by the constant
    vector and is far from attained on a star, and **this file proves neither**. The estate's
    `AdjNormSqrtDegree.sqrt_degree_le_norm_adjMatrix` is the nearest lower bound and is about a
    norm rather than an eigenvector.
  * **NO BRIDGE TO `IsHermitian.eigenvalues`.** The two forms still are not joined; this file
    adds the eigenvector side and says nothing about the indexing. A bridge would be a theorem
    about Mathlib's enumeration and is not attempted here.
  * **NOTHING ABOUT THE SIGNLESS LAPLACIAN OR THE CONE.** The consumer this was written for is
    the next unit; this file names no cone and no `Q`.
  * **NOTHING ABOUT THE CASCADE, THE SPINE OR ANY WALL.**

  **AND THE SECTION CARRIES NO `DecidableEq V`**, which is worth one line because the cone chain
  spent five, twelve and seven warnings learning to write sections small. `adjMatrix` needs
  `DecidableRel G.Adj` and `neighborFinset` needs the `Fintype` that follows from it; a decidable
  equality on vertices is never used, and the linter said so on the first check — **before the
  file entered `paper_f`**, which is `ERRATUM 618`'s point.

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace AdjEigenvectorBound

open SimpleGraph Matrix Finset

/-! ## The maximal coordinate -/

section MaxCoord

variable {V : Type*} [Finite V]

/-- A nonzero vector on a finite type has a coordinate of maximal modulus, and that modulus is
strictly positive. **The only ingredient of the bound below that is not the eigenvector
equation.**

**AND IT TAKES `[Finite V]`, NOT `[Fintype V]`, BECAUSE MATHLIB'S OWN LINTER ASKED FOR IT.**
The first version took `[Fintype V]`; `linter.unusedFintypeInType` pointed out that the
statement never mentions it and suggested exactly this — `Finite` in the type,
`Fintype.ofFinite` in the proof. **That is `PROOF_STRATEGY` §7 item 3 handed over by a
checker**, and it is the only warning this file ever had. It fired under `lake build` and not
under `lake env lean`, which is `ERRATUM 618`'s division holding up on a new instance. -/
theorem exists_abs_max {x : V → ℝ} (hx : x ≠ 0) :
    ∃ i : V, 0 < |x i| ∧ ∀ j : V, |x j| ≤ |x i| := by
  have : Fintype V := Fintype.ofFinite V
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 hx
  rw [Pi.zero_apply] at hj₀
  have hne : (Finset.univ : Finset V).Nonempty := ⟨j₀, Finset.mem_univ j₀⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset V) (fun j => |x j|) hne
  refine ⟨i, ?_, fun j => hi j (Finset.mem_univ j)⟩
  exact lt_of_lt_of_le (abs_pos.2 hj₀) (hi j₀ (Finset.mem_univ j₀))

end MaxCoord

/-! ## The bound -/

section Bound

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **THE MAXIMUM DEGREE BOUNDS AN ADJACENCY EIGENVALUE, IN EIGENVECTOR FORM.** At the
coordinate of largest modulus the eigenvector equation reads `μ * x i = ∑_{j ∼ i} x j`, and the
sum has `G.degree i` terms each of modulus at most `|x i|`. No regularity, no connectivity, no
bound on the number of vertices, and no operator norm. -/
theorem abs_le_of_mulVec_eq_smul {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ)
    {μ : ℝ} {x : V → ℝ} (hx : x ≠ 0) (hxe : G.adjMatrix ℝ *ᵥ x = μ • x) :
    |μ| ≤ Δ := by
  obtain ⟨i, hipos, himax⟩ := exists_abs_max hx
  have hrow : ∑ j ∈ G.neighborFinset i, x j = μ * x i := by
    have h := congrFun hxe i
    rwa [adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] at h
  have hstep : |μ| * |x i| ≤ (G.degree i : ℝ) * |x i| := by
    calc |μ| * |x i| = |μ * x i| := (abs_mul _ _).symm
      _ = |∑ j ∈ G.neighborFinset i, x j| := by rw [hrow]
      _ ≤ ∑ j ∈ G.neighborFinset i, |x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ G.neighborFinset i, |x i| := Finset.sum_le_sum fun j _ => himax j
      _ = (G.degree i : ℝ) * |x i| := by
          rw [Finset.sum_const, nsmul_eq_mul,
            show (G.neighborFinset i).card = G.degree i from rfl]
  have hle : |μ| * |x i| ≤ Δ * |x i| :=
    hstep.trans (mul_le_mul_of_nonneg_right (hΔ i) (abs_nonneg _))
  exact le_of_mul_le_mul_right hle hipos

/-- **BRACKETED ON BOTH SIDES.** -/
theorem mem_Icc_of_mulVec_eq_smul {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ)
    {μ : ℝ} {x : V → ℝ} (hx : x ≠ 0) (hxe : G.adjMatrix ℝ *ᵥ x = μ • x) :
    μ ∈ Set.Icc (-Δ) Δ := by
  have h := abs_le_of_mulVec_eq_smul G hΔ hx hxe
  exact ⟨neg_le_of_abs_le h, le_of_abs_le h⟩

/-- **THE REGULAR CASE, which is what this file was written for.** On a `d`-regular graph every
adjacency eigenvalue carried by a nonzero eigenvector satisfies `|μ| ≤ d`. -/
theorem abs_le_of_regular {d : ℕ} (hreg : ∀ i : V, G.degree i = d)
    {μ : ℝ} {x : V → ℝ} (hx : x ≠ 0) (hxe : G.adjMatrix ℝ *ᵥ x = μ • x) :
    |μ| ≤ (d : ℝ) :=
  abs_le_of_mulVec_eq_smul G (fun p => by rw [hreg p]) hx hxe

/-- **AND WITH MATHLIB'S `maxDegree` IN PLACE OF AN ABSTRACT `Δ`**, so a consumer holding no
bound of its own can still use the statement. -/
theorem abs_le_maxDegree_of_mulVec_eq_smul {μ : ℝ} {x : V → ℝ} (hx : x ≠ 0)
    (hxe : G.adjMatrix ℝ *ᵥ x = μ • x) :
    |μ| ≤ (G.maxDegree : ℝ) :=
  abs_le_of_mulVec_eq_smul G (fun p => Nat.cast_le.2 (G.degree_le_maxDegree p)) hx hxe

end Bound

end AdjEigenvectorBound
