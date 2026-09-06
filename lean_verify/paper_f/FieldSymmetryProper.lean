import FieldSymmetryInclusion

/-!
# When are the two symmetry groups the same? Exactly when the propagator has one eigenvalue

`FieldSymmetryInclusion` showed the isometric symmetries are the orthogonal elements of the linear
ones, and that the inclusion is **strict on a line**, fencing that *the strictness is only on a
line — `exists_nonIsometric` needs two eigenvectors at distinct eigenvalues, which the line
supplies; no strictness is proved on any other graph.* **The real hypothesis was never the line.**

## What is proved

**`exists_nonIsometric_of_eigenvalues_ne`** — on **any** finite graph, two **distinct eigenvalues**
of the propagator give a linear symmetry that is not an isometry.
`FieldSqrtConjugation.exists_nonIsometric_line`'s proof is generic apart from two lines that
produce the distinct eigenvalues on a line; everything else — the orthonormality of
`eigenvectorBasis`, the transfer from `inner` to `⬝ᵥ`, the eigenvector equations — never mentions
the graph. **The line was scaffolding, not a hypothesis.**

**`symmetryMatrices_ssubset_linSym`** — so **the inclusion is strict whenever the propagator has
two distinct eigenvalues**, on any graph.

**`orthogonal_of_mem_linSym_scalar`, `symmetryMatrices_eq_linSym_of_scalar`** — and when the
propagator is `c • 1` with `c ≠ 0` the two coincide: `L (c • 1) Lᵀ = c • 1` is `L Lᵀ = 1` once `c`
is cancelled, so every linear symmetry is orthogonal, and the commuting condition is automatic.

**`green_eq_scalar_of_eigenvalues_const`** — a Hermitian matrix whose eigenvalues are all `c` **is**
`c • 1`, by `Matrix.IsHermitian.spectral_theorem`: the diagonal matrix of a constant is `c • 1`, and
the conjugating map is a `⋆`-algebra automorphism, so it fixes it.

**`symmetryMatrices_eq_linSym_iff`** — **THE DICHOTOMY.** On a non-empty graph, the isometric
symmetries are **all** of the linear symmetries **if and only if** the propagator has a single
eigenvalue. Everywhere else — which is every graph whose propagator is not a multiple of the
identity — the isometric symmetries are a **proper** part.

## What is NOT here

**NO GRAPH-THEORETIC READING OF THE DEGENERATE CASE.** `green G m = c • 1` should be equivalent to
`G` having **no edges** — the Laplacian's off-diagonal entries are the negated adjacency, so a
scalar Laplacian forces every degree to zero — and **that equivalence is not proved here**. Nothing
in this file says which graphs fall on which side of the dichotomy; it says only what the condition
on the propagator is. Not attempted, no cost claimed (`ERRATUM 246`).

**`[Nonempty V]` IS TAKEN, and only by the dichotomy.** With `V` empty every matrix is equal to
every other and both sides are everything; the statement is true there too but the proof would be a
separate `Subsingleton` argument, and **it is not made.** The strictness and scalar theorems take
no such hypothesis.

**STILL THE MATRIX LEVEL.** `FieldSignGroup.symmetriesSubgroup` and
`FieldSymmetryInclusion.linSymGL` are group objects over different ambient types, and **no
homomorphism between them is constructed here either.** **And still no index.**

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `m ≠ 0` is taken by
`exists_nonIsometric_of_eigenvalues_ne`, `symmetryMatrices_ssubset_linSym`,
`green_eq_scalar_of_eigenvalues_const` and `symmetryMatrices_eq_linSym_iff` — **four of the six**,
and in every case because the statement mentions `green_posDef`'s eigenvalues, which need it. The
two scalar theorems take **no mass hypothesis at all**: they are algebra about a matrix that happens
to be `c • 1`, and `c ≠ 0` is carried explicitly rather than derived. `[Nonempty V]` is taken by
`symmetryMatrices_eq_linSym_iff` alone.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldSymmetryProper

open Matrix GraphLaplacian FieldSymmetryIso FieldRotationCount FieldSqrtConjugation
  FieldSymmetryInclusion

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Two distinct eigenvalues give a non-isometric symmetry, on any graph -/

theorem exists_nonIsometric_of_eigenvalues_ne (hm : m ≠ 0)
    {i j : V} (hne : (green_posDef G hm).isHermitian.eigenvalues i
      ≠ (green_posDef G hm).isHermitian.eigenvalues j) :
    ∃ L : Matrix V V ℝ, L * green G m * Lᵀ = green G m ∧ Lᵀ * L ≠ 1 := by
  classical
  set hH := (green_posDef G hm).isHermitian with hHdef
  set b := hH.eigenvectorBasis with hb
  have hij : i ≠ j := fun h => hne (by rw [h])
  have hinner : ∀ x y : EuclideanSpace ℝ V, (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp y) = inner ℝ x y := by
    intro x y
    rw [RayleighMatrix.inner_expand]
    rfl
  have hii : (WithLp.ofLp (b i)) ⬝ᵥ (WithLp.ofLp (b i)) = 1 := by
    rw [hinner, real_inner_self_eq_norm_sq, b.orthonormal.1 i]
    norm_num
  have hjj : (WithLp.ofLp (b j)) ⬝ᵥ (WithLp.ofLp (b j)) = 1 := by
    rw [hinner, real_inner_self_eq_norm_sq, b.orthonormal.1 j]
    norm_num
  have hijz : (WithLp.ofLp (b i)) ⬝ᵥ (WithLp.ofLp (b j)) = 0 := by
    rw [hinner]; exact b.orthonormal.2 hij
  have hj0 : (WithLp.ofLp (b j) : V → ℝ) ≠ 0 := by
    intro hz
    rw [hz] at hjj
    simp at hjj
  exact exists_nonIsometric hm one_ne_zero hii hjj hijz hj0
    (hH.mulVec_eigenvectorBasis i) (hH.mulVec_eigenvectorBasis j) hne

/-- **THE INCLUSION IS STRICT WHENEVER THE PROPAGATOR HAS TWO DISTINCT EIGENVALUES**, on any
graph. -/
theorem symmetryMatrices_ssubset_linSym (hm : m ≠ 0)
    {i j : V} (hne : (green_posDef G hm).isHermitian.eigenvalues i
      ≠ (green_posDef G hm).isHermitian.eigenvalues j) :
    symmetryMatrices G m ⊂ (linSym G m : Set (Matrix V V ℝ)) := by
  refine ⟨symmetryMatrices_subset_linSym, fun hsub => ?_⟩
  obtain ⟨L, hL, hnO⟩ := exists_nonIsometric_of_eigenvalues_ne hm hne
  exact hnO (hsub (mem_linSym.mpr hL)).1

/-! ## 2. And they coincide when the propagator is a multiple of the identity -/

theorem orthogonal_of_mem_linSym_scalar {c : ℝ} (hc : c ≠ 0)
    (hgreen : green G m = c • (1 : Matrix V V ℝ)) {L : Matrix V V ℝ} (hL : L ∈ linSym G m) :
    Lᵀ * L = 1 := by
  have h := mem_linSym.mp hL
  rw [hgreen] at h
  have h2 : c • (L * Lᵀ) = c • (1 : Matrix V V ℝ) := by
    rw [← h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  exact mul_eq_one_comm.mp (smul_right_injective _ hc h2)

theorem symmetryMatrices_eq_linSym_of_scalar {c : ℝ} (hc : c ≠ 0)
    (hgreen : green G m = c • (1 : Matrix V V ℝ)) :
    symmetryMatrices G m = (linSym G m : Set (Matrix V V ℝ)) := by
  rw [symmetryMatrices_eq]
  ext L
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  exact ⟨fun h => h.1, fun h => ⟨h, orthogonal_of_mem_linSym_scalar hc hgreen h⟩⟩

/-- A Hermitian matrix all of whose eigenvalues are `c` is `c • 1`. -/
theorem green_eq_scalar_of_eigenvalues_const (hm : m ≠ 0) {c : ℝ}
    (hconst : ∀ i, (green_posDef G hm).isHermitian.eigenvalues i = c) :
    green G m = c • (1 : Matrix V V ℝ) := by
  have hH := (green_posDef G hm).isHermitian
  have hdiag : (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) : Matrix V V ℝ)
      = c • (1 : Matrix V V ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, hconst]
  rw [hH.spectral_theorem, hdiag, map_smul, map_one]

/-! ## 3. The dichotomy -/

/-- **THE TWO SYMMETRY GROUPS COINCIDE EXACTLY WHEN THE PROPAGATOR HAS A SINGLE EIGENVALUE.**
Everywhere else the isometric symmetries are a **proper** part of the linear ones. -/
theorem symmetryMatrices_eq_linSym_iff [Nonempty V] (hm : m ≠ 0) :
    symmetryMatrices G m = (linSym G m : Set (Matrix V V ℝ)) ↔
      ∀ i j : V, (green_posDef G hm).isHermitian.eigenvalues i
        = (green_posDef G hm).isHermitian.eigenvalues j := by
  constructor
  · intro heq i j
    by_contra hne
    exact (symmetryMatrices_ssubset_linSym hm hne).ne heq
  · intro hall
    obtain ⟨i0⟩ := ‹Nonempty V›
    have hc : (green_posDef G hm).isHermitian.eigenvalues i0 ≠ 0 :=
      ((green_posDef G hm).eigenvalues_pos i0).ne'
    exact symmetryMatrices_eq_linSym_of_scalar hc
      (green_eq_scalar_of_eigenvalues_const hm fun i => hall i i0)

end FieldSymmetryProper
