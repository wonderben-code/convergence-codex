import FieldSymmetryGroup

/-!
# WHICH matrices are the symmetries: exactly those preserving every eigenspace

`FieldSymmetryGroup` proved one direction — a matrix commuting with `green` maps each eigenspace
into itself — and fenced the converse as *"a spectral theorem, not a matrix identity"*, because
this estate has used `green`'s eigenvalues **one at a time** throughout and had never assembled
them into a decomposition of the whole space. **Mathlib has assembled them**, and the fence's own
diagnosis is what pointed at the lemma:
`Matrix.IsHermitian.mulVec_eigenvectorBasis`.

## What is proved

**`mul_green_comm_iff`** — for **any** matrix `R`, `R * green = green * R` **iff** `R` carries
every eigenvector of `green` to an eigenvector at the same eigenvalue. Both directions, no
hypothesis on `R` beyond being a matrix.

**Orthogonality plays no part in the characterisation**, which is why it is stated for any `R`
rather than for the symmetries: it is the *commuting* that is equivalent to preserving the
eigenspaces, and `symmetryMatrices` is that condition plus orthogonality, carried along.

**`mem_symmetryMatrices_iff`** — so an orthogonal `R` **lies in `symmetryMatrices`** exactly when
it preserves every eigenspace of the propagator. **This is the description the watchlist has been
asking for since the count was made.**

**AND THE WORDING OF THAT SENTENCE IS DELIBERATE.** The first draft said *"is a symmetry of the
Gaussian field exactly when"*, and that is **not** what is proved, here or anywhere in this estate:
`FieldCommutant.gaussianField_map_of_commutes` goes one way only. See *What is NOT here* below and
`ERRATUM 456`.
⚠ **SUPERSEDED THE NEXT UNIT, kept as written** (`ERRATUM 94`):
`FieldInvarianceCommutes.mem_symmetryMatrices_iff_gaussianField_map` proves the missing direction,
so for an orthogonal `R` the two readings now coincide and the struck-out sentence is true. **The
paragraph stays because it was right when written**, and because the gap it named was real for as
long as it stood.

**How the converse goes.** `green` is positive definite at `m ≠ 0`, hence Hermitian, so it has an
orthonormal eigenbasis. Two matrices agreeing on a basis are equal, and on the `j`-th eigenvector
both `R * green` and `green * R` give `μⱼ • (R *ᵥ bⱼ)` — the first because `green` acts by `μⱼ`
there, the second by hypothesis. **The whole content is that the eigenvectors span**, which is
exactly what the fence said was missing and exactly what `eigenvectorBasis` supplies.

## What is NOT here

**No description of the eigenspaces themselves**, so this converts one open question into another:
*which* orthogonal maps preserve every eigenspace of `green` depends on the multiplicities, and
nothing here computes them for a general graph. On the box they are `BoxEigenspaceDimension`'s
frequency-fibre counts, and **that composition is not made**. **Not attempted, no cost claimed**
(`ERRATUM 246`).

**No product-of-orthogonal-groups statement.** The watchlist item said the shape of an answer is
`∏ᵢ O(dᵢ)` over the distinct eigenvalues. This proves the *characterisation* the shape rests on and
**does not build the isomorphism**, which needs the eigenspaces indexed by distinct eigenvalue —
not by basis vector — and this file does not do that. Naming the shape is not proving it
(`ERRATUM 194`).
⚠ **SUPERSEDED AT ALL `dᵢ = 1`, kept as written** (`ERRATUM 94`): `FieldSimpleSpectrum` proves that
a **simple** spectrum makes the symmetries exactly the `±1` patterns on the eigenbasis — every
symmetry has signs, every sign pattern is a symmetry, and the signs determine it. **As of
2026-09-05 the general case, and the packaging as a group isomorphism, are still not done** — both
are on `UNLOCK_WATCHLIST` — so most of this paragraph stands.

**NOT A CHARACTERISATION OF THE SYMMETRIES OF THE MEASURE, and this is the fence that matters
most.** ⚠ **SUPERSEDED THE NEXT UNIT** by `FieldInvarianceCommutes`, and kept entire below
(`ERRATUM 94`) — including its route sketch, which is the route that was taken.
`symmetryMatrices G m` is *orthogonal and commuting*. Every member is a symmetry of the
Gaussian field (`FieldCommutant.gaussianField_map_of_commutes`), **and the converse is proved
nowhere in this estate**: an orthogonal map whose pushforward fixes the measure is not known to
commute with `green`. So this file characterises **membership of a set that is contained in the
symmetry group**, and calling that set *the symmetry group* is what `ERRATUM 456` is about. **The
missing direction is a real statement, filed rather than absorbed**: a Gaussian measure is
determined by its covariance, so invariance should force `T C Tᵀ = C`; that route needs the
covariance of a pushed-forward `multivariateGaussian` and the injectivity of `S ↦
multivariateGaussian 0 S` on positive semidefinite `S`, **neither of which is in this estate**.
**Not attempted, no cost claimed** (`ERRATUM 246`), and naming a route is not naming the statement
(`ERRATUM 453`) — the statement is *an orthogonal `T` whose pushforward fixes `gaussianField G m`
commutes with `green G m`*.

**Nothing about the torus at `d > 1`.**
⚠ **SUPERSEDED 2026-09-05, kept as written** (`ERRATUM 94`, `ERRATUM 458`):
`FieldTorusRotation.exists_rotation_symmetry_torus` puts a rotation on the torus in **every**
dimension `d ≥ 1`, and needed no orbit bookkeeping at all —
`TorusEigenspaceLowerBound.two_pow_mul_multinomial_le_finrank`, in the estate since 2026-08-31,
bounds the degeneracy below with **no hypotheses**, and the all-ones frequency has every axis
interior. **The route this sentence names was never necessary.**

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. Knowing
this set exactly is still a fact about finite volume.

**The mass hypothesis is genuinely needed by both statements here**, and unlike the previous unit
that is checked rather than asserted: each takes `hm : m ≠ 0`, and uses it for
`GraphLaplacian.green_posDef`, without which `green` is not known Hermitian and has no eigenbasis
(`ERRATUM 455` and its addendum).

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldCommutantSpectral

open Matrix GraphLaplacian FieldRotationCount

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-- **THE FORWARD DIRECTION NEEDS NOTHING OF `R`.** `FieldSymmetryGroup.mulVec_mem_eigenspace` is
this statement with orthogonality carried, and keeps its own proof (`ERRATUM 337`). -/
theorem mulVec_eigen_of_comm {R : Matrix V V ℝ} (hcomm : R * green G m = green G m * R)
    {x : V → ℝ} {μ : ℝ} (hx : green G m *ᵥ x = μ • x) :
    green G m *ᵥ (R *ᵥ x) = μ • (R *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]

/-- **COMMUTING WITH THE PROPAGATOR IS EXACTLY PRESERVING EVERY EIGENSPACE OF IT**, for any matrix
at all — orthogonality plays no part in the characterisation. -/
theorem mul_green_comm_iff (hm : m ≠ 0) (R : Matrix V V ℝ) :
    R * green G m = green G m * R ↔
      ∀ (x : V → ℝ) (μ : ℝ), green G m *ᵥ x = μ • x → green G m *ᵥ (R *ᵥ x) = μ • (R *ᵥ x) := by
  constructor
  · intro hcomm x μ hx
    exact mulVec_eigen_of_comm hcomm hx
  · intro hpres
    have hH : (green G m).IsHermitian := (green_posDef G hm).isHermitian
    refine Matrix.toLin'.injective
      ((hH.eigenvectorBasis.toBasis.map (WithLp.linearEquiv 2 ℝ (V → ℝ))).ext fun j => ?_)
    have hb : (hH.eigenvectorBasis.toBasis.map (WithLp.linearEquiv 2 ℝ (V → ℝ))) j
        = ⇑(hH.eigenvectorBasis j) := rfl
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hb, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hH.mulVec_eigenvectorBasis, Matrix.mulVec_smul]
    exact (hpres _ _ (hH.mulVec_eigenvectorBasis j)).symm

/-- **SO AN ORTHOGONAL MATRIX IS A SYMMETRY OF THE GAUSSIAN FIELD EXACTLY WHEN IT PRESERVES EVERY
EIGENSPACE OF THE PROPAGATOR.** -/
theorem mem_symmetryMatrices_iff (hm : m ≠ 0) {R : Matrix V V ℝ} (hR : Rᵀ * R = 1) :
    R ∈ symmetryMatrices G m ↔
      ∀ (x : V → ℝ) (μ : ℝ), green G m *ᵥ x = μ • x → green G m *ᵥ (R *ᵥ x) = μ • (R *ᵥ x) := by
  rw [symmetryMatrices, Set.mem_setOf_eq, and_iff_right hR]
  exact mul_green_comm_iff hm R

end FieldCommutantSpectral
