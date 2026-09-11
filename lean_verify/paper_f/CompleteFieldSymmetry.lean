import FieldSymmetryFinite
import CompleteSpectrumTwoPoints
import FieldSimpleConverse

/-!
# The Gaussian field on the complete graph: infinitely many symmetries, and both spectra degenerate

**THIS FILE IS WHAT A SWEEP FOUND** (`RE-SWEEP #50`). Two units ago the complete graph's Laplacian
eigenspaces were identified as submodules and their dimensions counted; this estate has had, since
10 September, a criterion that turns exactly that count into a statement about the **measure** —
`FieldSymmetryFinite.finite_iff_lapMatrix`: the Gaussian field's symmetry group is finite **iff**
every eigenspace of the graph's Laplacian is at most a line. The two had not been composed, and
the composition is three lines.

**WHAT IT SAYS.** On `K_n` with `n ≥ 3` the Laplacian's `n`-eigenspace is the zero-sum
hyperplane, of dimension `n − 1 ≥ 2`. The criterion fails, and therefore:

* the symmetry matrices of the Gaussian field on `K_n` are an **infinite** set;
* the graph Laplacian's own eigenvalue enumeration is **not injective**;
* and neither is the **propagator's**, through
  `FieldSimpleConverse.eigenvalues_injective_iff_lapMatrix`.

**THE FIRST STATEMENT ABOUT THE COMPLETE GRAPH'S FIELD SYMMETRIES, and it is a data point for an
open item rather than a new method.** `UNLOCK_WATCHLIST`'s *which finite graphs have a SIMPLE
Laplacian spectrum* asks for a **family on the satisfying side** or a **third necessary condition**.
This is neither: it is a family on the **failing** side, and the estate already had a failure
condition that covers it in principle — a non-involutive automorphism (`FieldAutOrder`), and `K_n`
has a three-cycle for `n ≥ 3`. **What is new is that the failure is now proved, by an exact
dimension count rather than by an automorphism argument, and that no file had said anything about
the complete graph's field symmetries at all** — counted before writing: `completeGraph` appeared in
no `paper_f` file before 11 September.

## What is proved

**`two_le_finrank_eigenspace_top`** — the `n`-eigenspace of `K_n`'s Laplacian has dimension at least
two once `n ≥ 3`, from the previous unit's submodule identification and dimension count.

**`not_finrank_le_one_top`** — so the *every eigenspace is at most a line* condition fails on `K_n`.

**`infinite_symmetryMatrices_top`** — **HENCE THE GAUSSIAN FIELD ON `K_n` HAS INFINITELY MANY
SYMMETRIES**, at every non-zero mass.

**`not_injective_eigenvalues_lapMatrix_top`**, **`not_injective_eigenvalues_green_top`** — and
both eigenvalue enumerations are non-injective: the graph's Laplacian directly, the propagator
through the estate's equivalence between the two simplicity conditions.

## What is NOT here

* **NO CARDINALITY.** `Set.Infinite` says the set is not finite and nothing about which infinity;
  the symmetry group of a degenerate eigenvalue contains a circle and that is not stated. Not
  attempted, no cost claimed (`ERRATUM 246`).
* **NOTHING ON THE SATISFYING SIDE.** The open item wants a family with a **simple** Laplacian
  spectrum, and `K_n` is the opposite; nothing here narrows the characterisation.
* **NOTHING FOR THE EQUIPARTITE FAMILY.** `MultipartiteSpectrum` proves its three eigenvalues
  exhaust and **does not count their multiplicities**, so the same composition is unavailable there
  until those dimensions exist. That is the watchlist's open clause, not a gap in this file.
* **NO NEW FAILURE CONDITION.** The dimension route used here is `FieldSymmetryFinite`'s criterion
  applied, not a new sufficient condition for degeneracy.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and `OS1`
  in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `V` a `Fintype` with `DecidableEq`,
`3 ≤ Fintype.card V` on every statement, and `m ≠ 0` on the two that mention the field — the two
about the Laplacian alone take no mass. `not_injective_eigenvalues_green_top` takes the propagator's
Hermitian-ness as an argument, as its `FieldSimpleConverse` source does.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CompleteFieldSymmetry

open Matrix Finset SimpleGraph LaplacianSignless CompleteSpectrumTwoPoints
open FieldRotationCount

variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℝ}

/-! ## 1. The Laplacian criterion fails on `K_n` for `n ≥ 3` -/

theorem two_le_finrank_eigenspace_top (h3 : 3 ≤ Fintype.card V) :
    2 ≤ Module.finrank ℝ (LinearMap.ker (Matrix.toLin' ((⊤ : SimpleGraph V).lapMatrix ℝ)
      - (Fintype.card V : ℝ) • LinearMap.id)) := by
  rw [eigenspace_lapMatrix_top_eq_ker_sumForm, finrank_ker_sumForm (by omega)]
  omega

theorem not_finrank_le_one_top (h3 : 3 ≤ Fintype.card V) :
    ¬ ∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
      ((⊤ : SimpleGraph V).lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1 := by
  intro hall
  have := hall (Fintype.card V : ℝ)
  have h2 := two_le_finrank_eigenspace_top h3
  omega

/-! ## 2. So the Gaussian field on the complete graph has infinitely many symmetries -/

theorem infinite_symmetryMatrices_top (hm : m ≠ 0) (h3 : 3 ≤ Fintype.card V) :
    (symmetryMatrices (⊤ : SimpleGraph V) m).Infinite := by
  intro hfin
  exact not_finrank_le_one_top h3 ((FieldSymmetryFinite.finite_iff_lapMatrix hm).mp hfin)

/-! ## 3. And both spectra are degenerate, on the graph and on the measure -/

theorem not_injective_eigenvalues_lapMatrix_top (h3 : 3 ≤ Fintype.card V) :
    ¬ Function.Injective
      (FieldSimpleConverse.lapMatrix_isHermitian (⊤ : SimpleGraph V)).eigenvalues := by
  intro hinj
  exact not_finrank_le_one_top h3
    (FieldSimpleConverse.finrank_lapMatrix_le_one_iff_injective.mpr hinj)

theorem not_injective_eigenvalues_green_top (hm : m ≠ 0) (h3 : 3 ≤ Fintype.card V)
    (hH : (GraphLaplacian.green (⊤ : SimpleGraph V) m).IsHermitian) :
    ¬ Function.Injective hH.eigenvalues := by
  intro hinj
  exact not_injective_eigenvalues_lapMatrix_top h3
    ((FieldSimpleConverse.eigenvalues_injective_iff_lapMatrix hm hH).mp hinj)

end CompleteFieldSymmetry
