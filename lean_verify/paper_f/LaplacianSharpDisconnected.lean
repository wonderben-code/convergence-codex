import LaplacianSharpEquality

/-!
# Which regular graphs attain the degree bound: exactly those with a two-colourable component

`LaplacianSharpEquality` characterised attainment for **connected** regular graphs — some `x ≠ 0`
has `xᵀLx = 2Δ‖x‖²` exactly when the graph is two-colourable — and said in the same breath that
connectivity is not slack, because `C₃ ⊔ C₄` is 2-regular, attains on its `C₄`, and is not
two-colourable. **This file removes the hypothesis**, and the counterexample turns out to be the
general shape rather than an obstruction:

> **`exists_quadForm_eq_iff_exists_component_colorable`** — a `Δ`-regular graph, connected or not,
> has some `x ≠ 0` with `xᵀLx = 2Δ‖x‖²` **iff some connected component of it is two-colourable**.

So the watch-list question *which regular graphs attain `LaplacianDegreeBound`'s constant* now has
its full answer, with no side condition left.

**BOTH DIRECTIONS ARE THE PREVIOUS UNIT'S EQUALITY CASE PLUS ONE FACT ABOUT COMPONENTS.**
`quadForm_eq_iff_neg_adj` already says, over any regular graph and with no further hypothesis, that
equality holds exactly when `x` flips sign across every edge. What a component adds is that
**adjacency cannot leave it** (`mem_supp_of_adj`), so a sign-flipping vector supported on one
component is sign-flipping on the whole graph — every edge either lies inside the component, where
the flip is the component's own colouring, or misses it entirely, where both ends are zero and
`0 = −0`.

* **⇐** `extendComp` extends a component's `±1` colouring by zero. It is non-zero because a
  component contains the vertex that generated it.
* **⇒** the flip plus `LaplacianSharpEquality.ne_zero_of_walk` makes `x` nowhere zero on the
  component of any site where it does not vanish, and its sign is then a proper two-colouring of
  that component.

**THE CONNECTED CASE IS RECOVERED, NOT MERELY IMPLIED** (`ERRATUM 201`): the `example` below
derives `LaplacianSharpEquality.exists_quadForm_eq_iff_colorable` from this one through Mathlib's
`induceUnivIso`, so the generalisation is instantiated at the statement it generalises.

## What this does NOT do

**It does not say the whole graph is two-colourable, and that is the point.** One component suffices
and the rest of the graph is unconstrained — `C₃ ⊔ C₄` attains, and its triangle needs three
colours. **The `C₃ ⊔ C₄` example is still not formalised**; what is formalised is the theorem that
makes it unsurprising (`ERRATUM 246`: no cost is claimed for the instance either).

**It is still about a supplied vector, not an eigenvalue list**, and it does **not** carry the
Loewner-order form. `LaplacianLoewnerConverse.massive_le_smul_one_iff_colorable` keeps its
connectivity hypothesis, and nothing here removes it: that argument needs every eigenvalue strictly
below the constant, and a graph whose components disagree is not covered by anything proved here.
**No cost is claimed for that gap** (`ERRATUM 246`).

**Regularity is not removed either.** `RegularBipartiteSharp` only has the averaged statement
without it, and this file inherits `quadForm_eq_iff_neg_adj`'s hypothesis unchanged.

**This is a statement about a matrix.** No measure appears, nothing in the OS chain changes, and no
published tag is touched.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LaplacianSharpDisconnected

open Matrix GraphLaplacian SimpleGraph LaplacianSharpEquality

variable {V : Type*} (G : SimpleGraph V)

/-! ## 1. Adjacency does not leave a component -/

/-- **AN EDGE CANNOT LEAVE A COMPONENT.** The one fact about components this file needs. -/
theorem mem_supp_of_adj {C : G.ConnectedComponent} {u v : V} (h : G.Adj u v)
    (hu : u ∈ C.supp) : v ∈ C.supp := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hu ⊢
  rw [← SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h]
  exact hu

/-! ## 2. A two-colourable component gives a sign-flipping vector on the whole graph -/

/-- A function on one component, extended by zero to the whole vertex set. The membership test is
classical: a `ConnectedComponent.supp` carries no decidable membership predicate, and nothing
here needs one. -/
noncomputable def extendComp (C : G.ConnectedComponent) (σ : C.supp → ℝ) : V → ℝ :=
  fun v => haveI := Classical.propDecidable (v ∈ C.supp); if h : v ∈ C.supp then σ ⟨v, h⟩ else 0

theorem extendComp_of_mem (C : G.ConnectedComponent) (σ : C.supp → ℝ) {v : V}
    (h : v ∈ C.supp) : extendComp G C σ v = σ ⟨v, h⟩ := by
  simp [extendComp, h]

theorem extendComp_of_not_mem (C : G.ConnectedComponent) (σ : C.supp → ℝ) {v : V}
    (h : v ∉ C.supp) : extendComp G C σ v = 0 := by
  simp [extendComp, h]

/-- **A TWO-COLOURABLE COMPONENT SUPPLIES A SIGN FLIP ACROSS EVERY EDGE OF THE GRAPH.** -/
theorem exists_neg_adj_of_component_colorable (C : G.ConnectedComponent)
    (hc : (G.induce C.supp).Colorable 2) :
    ∃ x : V → ℝ, x ≠ 0 ∧ ∀ u v : V, G.Adj u v → x v = - x u := by
  classical
  obtain ⟨σ, hσ⟩ := RegularBipartiteSharp.exists_signColouring_of_colorable hc
  refine ⟨extendComp G C σ, ?_, ?_⟩
  · obtain ⟨v₀, hv₀⟩ := C.exists_rep
    have hmem : v₀ ∈ C.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]; exact hv₀
    intro hzero
    have hval : extendComp G C σ v₀ = 0 := by rw [hzero]; rfl
    rw [extendComp_of_mem G C σ hmem] at hval
    rcases hσ.1 ⟨v₀, hmem⟩ with h1 | h1 <;> rw [hval] at h1 <;> norm_num at h1
  · intro u v huv
    by_cases hu : u ∈ C.supp
    · have hv : v ∈ C.supp := mem_supp_of_adj G huv hu
      have hadj : (G.induce C.supp).Adj ⟨u, hu⟩ ⟨v, hv⟩ := huv
      rw [extendComp_of_mem G C σ hu, extendComp_of_mem G C σ hv, hσ.2 _ _ hadj]
      ring
    · have hv : v ∉ C.supp := fun hv => hu (mem_supp_of_adj G huv.symm hv)
      rw [extendComp_of_not_mem G C σ hu, extendComp_of_not_mem G C σ hv]
      ring

/-! ## 3. And conversely -/

/-- **A SIGN-FLIPPING VECTOR TWO-COLOURS ITS OWN COMPONENT AT EVERY VERTEX WHERE IT DOES NOT
VANISH.** Generalised in place 2026-08-30 (`ERRATUM 337`: extract, do not copy) from the existential
below, which supplied the vertex by choice and then discarded it. The decomposition of the signless
Laplacian's kernel needs the component named, not merely known to exist. -/
theorem component_colorable_of_ne_zero {x : V → ℝ}
    (hflip : ∀ u v : V, G.Adj u v → x v = - x u) {v₀ : V} (hv₀ : x v₀ ≠ 0) :
    (G.induce (G.connectedComponentMk v₀).supp).Colorable 2 := by
  classical
  have hne : ∀ w : (G.connectedComponentMk v₀).supp, x (w : V) ≠ 0 := by
    rintro ⟨w, hw⟩
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq] at hw
    obtain ⟨p⟩ := hw.symm
    exact ne_zero_of_walk G hflip p hv₀
  refine ⟨SimpleGraph.Coloring.mk (fun w => if 0 < x (w : V) then (0 : Fin 2) else 1) ?_⟩
  intro a b hab
  have hadj : G.Adj (a : V) (b : V) := hab
  have hvu : x (b : V) = - x (a : V) := hflip _ _ hadj
  rcases lt_trichotomy (x (a : V)) 0 with h | h | h
  · have ha : ¬ (0 < x (a : V)) := not_lt.mpr h.le
    have hb : 0 < x (b : V) := by rw [hvu]; exact neg_pos.mpr h
    simp only [if_neg ha, if_pos hb]
    decide
  · exact absurd h (hne a)
  · have hb : ¬ (0 < x (b : V)) := by
      rw [hvu]
      exact not_lt.mpr (neg_nonpos.mpr h.le)
    simp only [if_pos h, if_neg hb]
    decide

/-- **A SIGN-FLIPPING VECTOR TWO-COLOURS THE COMPONENT WHERE IT DOES NOT VANISH**, which is the
statement above with the vertex existentially quantified. Its statement is unchanged and nothing is
withdrawn. -/
theorem exists_component_colorable_of_neg_adj {x : V → ℝ} (hx : x ≠ 0)
    (hflip : ∀ u v : V, G.Adj u v → x v = - x u) :
    ∃ C : G.ConnectedComponent, (G.induce C.supp).Colorable 2 := by
  classical
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, x v₀ ≠ 0 := by
    by_contra hc
    exact hx (funext fun w => not_not.mp fun h => hc ⟨w, h⟩)
  exact ⟨G.connectedComponentMk v₀, component_colorable_of_ne_zero G hflip hv₀⟩

/-! ## 4. The characterisation, with no connectivity hypothesis -/

/-- **WHICH REGULAR GRAPHS ATTAIN `LaplacianDegreeBound`'s CONSTANT: EXACTLY THOSE WITH A
TWO-COLOURABLE COMPONENT.** No connectivity, and the whole graph need not be two-colourable. -/
theorem exists_quadForm_eq_iff_exists_component_colorable [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) :
    (∃ x : V → ℝ, x ≠ 0 ∧ x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x = 2 * (Δ : ℝ) * (x ⬝ᵥ x))
      ↔ ∃ C : G.ConnectedComponent, (G.induce C.supp).Colorable 2 := by
  constructor
  · rintro ⟨x, hx, heq⟩
    exact exists_component_colorable_of_neg_adj G hx ((quadForm_eq_iff_neg_adj G hreg x).mp heq)
  · rintro ⟨C, hc⟩
    obtain ⟨x, hx, hflip⟩ := exists_neg_adj_of_component_colorable G C hc
    exact ⟨x, hx, (quadForm_eq_iff_neg_adj G hreg x).mpr hflip⟩

/-- **THE CONNECTED CASE IS RECOVERED FROM THE GENERAL ONE**, so the generalisation is
instantiated at the statement it generalises rather than merely asserted to specialise
(`ERRATUM 201`). The bridge is Mathlib's `induceUnivIso`. -/
example [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nonempty V] {Δ : ℕ}
    (hreg : G.IsRegularOfDegree Δ) (hG : G.Connected) :
    (∃ x : V → ℝ, x ≠ 0 ∧ x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x = 2 * (Δ : ℝ) * (x ⬝ᵥ x))
      ↔ G.Colorable 2 := by
  rw [exists_quadForm_eq_iff_exists_component_colorable G hreg]
  constructor
  · rintro ⟨C, hc⟩
    have hsupp : C.supp = Set.univ := by
      obtain ⟨v₀, hv₀⟩ := C.exists_rep
      subst hv₀
      ext v
      simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, Set.mem_univ, iff_true]
      exact SimpleGraph.ConnectedComponent.sound (hG.preconnected v v₀)
    rw [hsupp] at hc
    exact SimpleGraph.Colorable.of_hom (SimpleGraph.induceUnivIso G).symm.toHom hc
  · intro hc
    obtain ⟨v₀⟩ := ‹Nonempty V›
    exact ⟨G.connectedComponentMk v₀,
      SimpleGraph.Colorable.of_hom (SimpleGraph.Embedding.induce _).toHom hc⟩

end LaplacianSharpDisconnected
