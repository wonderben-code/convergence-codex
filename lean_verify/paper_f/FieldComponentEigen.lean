import FieldOrthIsometry
import FieldSignReflection
import FieldSignFlip

/-!
# Two orthogonal eigenvectors at one eigenvalue, which is what the rotations were waiting for

`FieldReflectionCount` separates reflections **by eigenvalue** and is blind inside one eigenspace;
`FieldOrthIsometry` removed the packaging obstruction to a rotation. Both closed on the same
remaining item, in the same words: **nothing in this estate produces two orthogonal eigenvectors of
`green` at a single eigenvalue.**

**On a disconnected graph the indicators of two components are such a pair**, and neither the
statement nor the proof needs anything the estate did not already have.

`PROOF_STRATEGY` §6 question 3 again: the previous unit was a `B` and this is the retry.

## Why the indicator is an eigenvector

The graph Laplacian kills it. At a vertex **inside** the set, every neighbour is reachable and so
also inside, and *degree minus that many ones* is zero; at a vertex **outside**, the value and every
neighbouring value are zero. So `massive *ᵥ 1_s = m² · 1_s` and, through
`FieldSignReflection.green_mulVec_of_massive_mulVec`, `green *ᵥ 1_s = m⁻² · 1_s` — **the same
eigenvalue for every component**, which is exactly the degeneracy a rotation needs.

## What is proved

**`indicator`** and **`massive_mulVec_indicator`** — the indicator of a component-closed set is an
eigenvector of `massive` at `m²`, at every finite graph, with `FieldSignFlip.IsComponentClosed` the
only hypothesis.

**`green_mulVec_indicator`** — hence of `green` at `m⁻²`.

**`dotProduct_indicator_of_disjoint`** — indicators of **disjoint** sets are orthogonal, and
**`dotProduct_indicator_self`** — the self-product is the set's size, so a nonempty set gives a
nonzero vector.

**`exists_orthogonal_eigenpair_of_not_reachable`** — **so a disconnected graph carries two
orthogonal, non-zero eigenvectors of `green` at the same eigenvalue `m⁻²`**: the component of `p`
and its complement, which `FieldSignFlip`'s own construction already shows are component-closed.

## What is NOT here

**No rotation is built.** Both obstructions the chain named are now gone — the packaging
(`FieldOrthIsometry.orthIsometry`) and the pair (here) — and **assembling them is a third thing**:
a rotation matrix in the plane of `u` and `v` has to be written down and its orthogonality and
commutation proved, neither of which follows from the existence of the pair. **Not attempted, no
cost claimed** (`ERRATUM 246`), and the fact that its two ingredients now exist is **not** a claim
that it is easy — `ERRATUM 194`.

**Nothing on a connected graph.** There `m⁻²`'s eigenspace is the constants alone, and the
degeneracies live at other eigenvalues whose eigenvectors are the **complex** characters. The
connected case is untouched and this file does not approach it.

**No new symmetry.** This unit exhibits vectors, not maps.

**Not OS3 and not any OS axiom. No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldComponentEigen

open Matrix GraphLaplacian FieldSignFlip FieldSignReflection

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The indicator of a union of components -/

/-- The indicator vector of a set of vertices. -/
def indicator (s : Finset V) : V → ℝ := fun v => if v ∈ s then 1 else 0

/-- **THE LAPLACIAN KILLS A COMPONENT'S INDICATOR**, so `massive` scales it by `m²`. -/
theorem massive_mulVec_indicator {s : Finset V} (hs : IsComponentClosed G s) (m : ℝ) :
    massive G m *ᵥ indicator s = (m ^ 2) • indicator s := by
  funext v
  rw [GraphGreenPositive.massive_mulVec_apply]
  by_cases hv : v ∈ s
  · have hnb : ∀ u ∈ G.neighborFinset v, indicator s u = 1 := by
      intro u hu
      have hadj : G.Adj v u := (SimpleGraph.mem_neighborFinset _ _ _).mp hu
      have : u ∈ s := (hs v u hadj.reachable).mp hv
      simp [indicator, this]
    rw [Finset.sum_congr rfl hnb, Finset.sum_const, nsmul_eq_mul, mul_one,
      SimpleGraph.card_neighborFinset_eq_degree]
    simp [indicator, hv]
  · have hnb : ∀ u ∈ G.neighborFinset v, indicator s u = 0 := by
      intro u hu
      have hadj : G.Adj v u := (SimpleGraph.mem_neighborFinset _ _ _).mp hu
      have : u ∉ s := fun h => hv ((hs v u hadj.reachable).mpr h)
      simp [indicator, this]
    rw [Finset.sum_congr rfl hnb, Finset.sum_const_zero]
    simp [indicator, hv]

/-- **AND SO `green` SCALES IT BY `m⁻²`** — the same eigenvalue at every component. -/
theorem green_mulVec_indicator {s : Finset V} (hs : IsComponentClosed G s) (hm : m ≠ 0) :
    green G m *ᵥ indicator s = (m ^ 2)⁻¹ • indicator s :=
  green_mulVec_of_massive_mulVec hm (pow_ne_zero 2 hm) (massive_mulVec_indicator hs m)

/-! ## 2. Disjoint sets give orthogonal indicators -/

omit [DecidableRel G.Adj] in
theorem dotProduct_indicator_of_disjoint {s t : Finset V} (h : Disjoint s t) :
    (indicator s : V → ℝ) ⬝ᵥ indicator t = 0 := by
  rw [dotProduct]
  refine Finset.sum_eq_zero fun v _ => ?_
  by_cases hv : v ∈ s
  · have : v ∉ t := Finset.disjoint_left.mp h hv
    simp [indicator, this]
  · simp [indicator, hv]

omit [DecidableRel G.Adj] in
theorem dotProduct_indicator_self (s : Finset V) :
    (indicator s : V → ℝ) ⬝ᵥ indicator s = (s.card : ℝ) := by
  rw [dotProduct]
  rw [Finset.sum_congr rfl (fun v _ => by
    by_cases hv : v ∈ s <;> simp [indicator, hv] :
    ∀ v ∈ Finset.univ, indicator s v * indicator s v = if v ∈ s then (1 : ℝ) else 0)]
  simp [Finset.sum_ite_mem]

/-! ## 3. So a disconnected graph carries the pair -/

/-- **TWO ORTHOGONAL NON-ZERO EIGENVECTORS OF `green` AT THE SAME EIGENVALUE**, on any graph with a
pair of vertices not joined by a path. This is the object `FieldReflectionCount` and
`FieldOrthIsometry` both name as missing. -/
theorem exists_orthogonal_eigenpair_of_not_reachable (hm : m ≠ 0) {p q : V}
    (hpq : ¬ G.Reachable p q) :
    ∃ u v : V → ℝ, u ⬝ᵥ u ≠ 0 ∧ v ⬝ᵥ v ≠ 0 ∧ u ⬝ᵥ v = 0 ∧
      green G m *ᵥ u = (m ^ 2)⁻¹ • u ∧ green G m *ᵥ v = (m ^ 2)⁻¹ • v := by
  classical
  set s : Finset V := Finset.univ.filter fun w => G.Reachable p w with hsdef
  have hclosed : IsComponentClosed G s := by
    intro a b hab
    simp only [hsdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.trans hab, fun h => h.trans hab.symm⟩
  have hcompl : IsComponentClosed G sᶜ := by
    intro a b hab
    simp only [Finset.mem_compl]
    exact not_congr (hclosed a b hab)
  have hps : p ∈ s := by simp [hsdef]
  have hqs : q ∈ sᶜ := by simp [hsdef, hpq]
  refine ⟨indicator s, indicator sᶜ, ?_, ?_, ?_,
    green_mulVec_indicator hclosed hm, green_mulVec_indicator hcompl hm⟩
  · rw [dotProduct_indicator_self]
    exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem hps)
  · rw [dotProduct_indicator_self]
    exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem hqs)
  · exact dotProduct_indicator_of_disjoint (disjoint_compl_right)

end FieldComponentEigen
