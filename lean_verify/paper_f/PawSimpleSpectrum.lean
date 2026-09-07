import FieldSimpleConverse
import EigenBasisDimension

/-!
# A second graph with a simple Laplacian spectrum: the paw

The watchlist item *a graph OTHER than the line whose propagator has a simple spectrum, so that
the `2^|V|` count and the `(ℤ/2)^V` group bite somewhere else* was filed when the three symmetry
files were generalised in place, and every unit that touched it since recorded the same sentence:
**`eigenvalues_injective_line` is still the estate's only discharge of that hypothesis.** The
failing side of the scoreboard grew across those units — disconnected graphs and every periodic
lattice (`FieldSimpleConnected`), every box in `d ≥ 2` (`FieldSimpleBox`), the complete graph on
three or more vertices and every graph with a non-involutive automorphism (`FieldAutOrder`), any
graph with two twin pairs at one degree (`LaplacianTwins`), an eight-vertex tree
(`FieldTwinSpectrum`) — and the satisfying side never gained a second graph. This file adds one,
chosen to be as unlike the path as four vertices allow.

**The paw**: a triangle `0 – 1 – 2` with a pendant `3` hanging off `0`. Degrees `3, 2, 2, 1`, so it
is not a path, not a cycle, not regular and not a tree; and it has a non-trivial automorphism, the
swap of the two far corners of the triangle, so the involution theorem has content on it.

## What is proved

**`lapMatrix_pawGraph`** — its Laplacian is the explicit `4 × 4` matrix, entry by entry.

**`pawLap_mulVec`, `pawEig_injective`** — four explicit integer eigenvectors with eigenvalues
`0, 3, 1, 4`, pairwise distinct. **`pawVec_linearIndependent`, `pawBasis`** — they are a basis of
`ℝ⁴`, by solving the four linear equations rather than by a determinant.

**`finrank_eigenspace_paw`** — so every eigenspace of the paw's Laplacian is exactly the fibre of
the eigenvalue map (`EigenBasisDimension.finrank_ker_sub_smul`, the estate's own lemma for a
basis of eigenvectors), and **`finrank_lapMatrix_le_one_paw`** — hence at most a line.

**`eigenvalues_injective_paw`, `card_symmetries_paw`, `graphAut_involutive_paw`** — through the
door `FieldLaplacianSimple` built: the paw's Laplacian spectrum is simple, the Gaussian field on
it has exactly `2 ^ 4 = 16` symmetries, and every graph automorphism of it is an involution.

**`isGraphAut_swap`, `pawGraph_aut`** — **and the involution theorem has something to say here.**
The swap `(1 2)` is a graph automorphism, and enumerating all `24` permutations shows the
automorphism group is exactly `{1, (1 2)}`. So on this graph the theorem is checked by two
independent routes — the spectral one above and brute enumeration — and they agree.

## What is NOT here

**ONE GRAPH, NOT A FAMILY, AND NOT A CHARACTERISATION.** The path is a family in `k`; this is four
vertices. Nothing here says which other graphs satisfy the condition, nothing is said about any
other four-vertex graph, and the version of the item its own `LIKELY OUTCOME` calls the
interesting one — *which graphs have a simple propagator spectrum* — is exactly as open as
before, with one more data point.

**NOTHING ABOUT THE INVOLUTION CONVERSE.** That *every automorphism is an involution* does not
force a simple spectrum is already settled, disconnected (`FieldInvolutionConverse`) and connected
(`FieldTwinSpectrum.twinGraph`). The paw's automorphism group is `ℤ/2` and its spectrum is simple,
which is exactly what `FieldSimpleAut.graphAut_involutive` forces and no more: an instance of the
theorem, not evidence about its converse.

**THE EIGENVECTORS WERE FOUND BY HAND.** Nothing here computes a spectrum; the four vectors are
written down and checked. A graph whose eigenvectors are not integer vectors would need a
different method, and none is offered.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): every theorem about the graph and its
Laplacian takes **nothing at all**; `card_symmetries_paw` and `graphAut_involutive_paw` take
**`m ≠ 0`**, because the Gaussian field needs a positive-definite propagator, exactly as the path
versions do.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace PawSimpleSpectrum

open Matrix GraphLaplacian FieldSimpleCriterion FieldLaplacianSimple FieldLineCount
open FieldAutInvariance FieldSimpleConverse SimpleGraph

/-! ## 1. The paw: a triangle with a pendant -/

/-- Adjacency of the paw: the triangle `0 – 1 – 2` and the pendant edge `0 – 3`. -/
def pawAdj : Fin 4 → Fin 4 → Bool
  | 0, 1 => true | 1, 0 => true
  | 0, 2 => true | 2, 0 => true
  | 1, 2 => true | 2, 1 => true
  | 0, 3 => true | 3, 0 => true
  | _, _ => false

def pawGraph : SimpleGraph (Fin 4) where
  Adj p q := pawAdj p q = true
  symm := by intro p q h; revert p q; decide
  loopless := ⟨by intro p h; revert p; decide⟩

instance : DecidableRel pawGraph.Adj := fun p q =>
  inferInstanceAs (Decidable (pawAdj p q = true))

theorem pawGraph_adj (p q : Fin 4) : pawGraph.Adj p q ↔ pawAdj p q = true := Iff.rfl

theorem pawGraph_degree : ∀ v : Fin 4, pawGraph.degree v = ![3, 2, 2, 1] v := by decide

/-- The paw is not a path and not a cycle: it has a vertex of degree three. -/
theorem pawGraph_degree_zero : pawGraph.degree 0 = 3 := by decide

/-! ## 2. Its Laplacian, and four eigenvectors with four different eigenvalues -/

def pawLap : Matrix (Fin 4) (Fin 4) ℝ :=
  !![3, -1, -1, -1; -1, 2, -1, 0; -1, -1, 2, 0; -1, 0, 0, 1]

theorem lapMatrix_pawGraph : pawGraph.lapMatrix ℝ = pawLap := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix, pawLap,
      pawGraph_adj, pawAdj, pawGraph_degree]

/-- The eigenvectors, as rows: the constant, the triangle's antisymmetric mode, the mode that
weighs the pendant against the two far corners, and the mode that weighs the hub against the
rest. -/
def pawVec : Fin 4 → (Fin 4 → ℝ) :=
  ![![1, 1, 1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![-3, 1, 1, 1]]

def pawEig : Fin 4 → ℝ := ![0, 3, 1, 4]

theorem pawLap_mulVec (k : Fin 4) : pawLap *ᵥ pawVec k = pawEig k • pawVec k := by
  fin_cases k <;> ext v <;> fin_cases v <;>
    simp [pawLap, pawVec, pawEig, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> norm_num

theorem pawEig_injective : Function.Injective pawEig := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [pawEig] at h ⊢

/-! ## 3. They are a basis -/

theorem pawVec_linearIndependent : LinearIndependent ℝ pawVec := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  have h3 := congrFun hc 3
  simp [pawVec, Fin.sum_univ_four] at h0 h1 h2 h3
  fin_cases k <;> simp <;> linarith

noncomputable def pawBasis : Module.Basis (Fin 4) ℝ (Fin 4 → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank pawVec_linearIndependent (by simp)

theorem pawBasis_apply (k : Fin 4) : pawBasis k = pawVec k :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) k

/-! ## 4. So every eigenspace of the paw's Laplacian is a line -/

theorem finrank_eigenspace_paw (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (pawGraph.lapMatrix ℝ) - μ • LinearMap.id))
      = Nat.card {k : Fin 4 // pawEig k = μ} :=
  EigenBasisDimension.finrank_ker_sub_smul pawBasis
    (fun k => by rw [pawBasis_apply, lapMatrix_pawGraph]; exact pawLap_mulVec k) μ

theorem finrank_lapMatrix_le_one_paw (ν : ℝ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (pawGraph.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1 := by
  rw [finrank_eigenspace_paw, Finite.card_le_one_iff_subsingleton]
  exact ⟨fun a b => Subtype.ext (pawEig_injective (a.2.trans b.2.symm))⟩

/-! ## 5. Through the door -/

theorem eigenvalues_injective_paw :
    Function.Injective (lapMatrix_isHermitian pawGraph).eigenvalues :=
  finrank_lapMatrix_le_one_iff_injective.mp finrank_lapMatrix_le_one_paw

theorem card_symmetries_paw {m : ℝ} (hm : m ≠ 0) :
    Nat.card (symmetries pawGraph m) = 2 ^ 4 :=
  card_symmetries_of_lapMatrix hm finrank_lapMatrix_le_one_paw

theorem graphAut_involutive_paw {m : ℝ} (hm : m ≠ 0) {θ : Fin 4 ≃ Fin 4}
    (hθ : IsGraphAut pawGraph θ) (p : Fin 4) : θ (θ p) = p :=
  graphAut_involutive_of_lapMatrix hm finrank_lapMatrix_le_one_paw hθ p

/-! ## 6. And the involution theorem has something to say here -/

/-- `IsGraphAut` is a `def`, so instance search will not unfold it. The same line, for the same
reason, is `AsymmetricGraph.decidableAut` on `asymGraph`; this is its instance on the paw. -/
instance decidableAutPaw (θ : Equiv.Perm (Fin 4)) : Decidable (IsGraphAut pawGraph θ) :=
  inferInstanceAs (Decidable (∀ p q, pawGraph.Adj (θ p) (θ q) ↔ pawGraph.Adj p q))

/-- The swap of the two far corners of the triangle is a graph automorphism of the paw. -/
theorem isGraphAut_swap : IsGraphAut pawGraph (Equiv.swap 1 2) := by decide

theorem swap_ne_refl : (Equiv.swap (1 : Fin 4) 2) ≠ Equiv.refl _ := by decide

/-- **THE PAW'S AUTOMORPHISM GROUP IS EXACTLY `{1, (1 2)}`**, by enumerating all `24` permutations.
So the involution theorem is checked here by a second, independent route on a graph where it has
something to say. -/
theorem pawGraph_aut (θ : Equiv.Perm (Fin 4)) (h : IsGraphAut pawGraph θ) :
    θ = Equiv.refl _ ∨ θ = Equiv.swap 1 2 := by
  revert θ
  decide

end PawSimpleSpectrum
