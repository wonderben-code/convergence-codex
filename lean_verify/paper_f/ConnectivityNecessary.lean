import LaplacianSharpDisconnected

/-!
# Connectivity is necessary, and the witness the estate has been describing is built

`LaplacianSharpEquality.exists_quadForm_eq_iff_colorable` characterises attainment of the degree
bound on a **connected** regular graph, and its own fence says why the hypothesis is there:

> *"**dropping connectivity makes the statement false** (`C₃ ⊔ C₄` is 2-regular, attains on its
> `C₄`, and is not two-colourable), which is stated and **not formalised** (`ERRATUM 246`)."*

**This file formalises it.** The estate's own transferable rule, recorded at `RE-SWEEP` round 21, is
*"when a header states a limitation, ask whether the limitation is itself provable. A stated caveat
that could be a theorem is an unfinished one."* This is one of those, named in three files and left
as prose for a day.

> **`cycThreeFour_isRegular`** — the seven-vertex graph is `2`-regular.
> **`cycThreeFour_attains`** — it attains `xᵀLx = 2·2·‖x‖²` at a non-zero vector.
> **`cycThreeFour_not_colorable`** — and it is not two-colourable.
> **`connectivity_necessary`** — hence no version of `exists_quadForm_eq_iff_colorable` with the
> connectivity hypothesis deleted can be true.

**THE WITNESS IS NOT A DISJOINT UNION IN THE TYPE, BECAUSE MATHLIB HAS NONE.** Probed by shape
(`ERRATUM 42`): there is no `SimpleGraph` construction on a sum type in Mathlib v4.29.1 — `sum`
appears only as pattern-match auxiliaries, and `boxProd` is the Cartesian product, not the disjoint
union. So the graph is built on `Fin 7` by `fromRel`, with `{0,1,2}` a triangle and `{3,4,5,6}` a
four-cycle and no edge between the blocks. **That is `C₃ ⊔ C₄` up to isomorphism and the file does
not claim more**: no isomorphism with `cycleGraph 3` or `cycleGraph 4` is constructed, because
nothing here needs one.

**WHY THE ATTAINING VECTOR NEEDS NO CONNECTIVITY ARGUMENT.**
`LaplacianSharpEquality.quadForm_eq_iff_neg_adj` already says attainment is exactly *`x` flips sign
across every edge*, **with no connectivity and no non-vanishing**. So the witness vector is
exhibited rather than constructed: `0` on the triangle, alternating `±1` on the four-cycle. It
vanishes on half the graph, which is precisely what a connected graph forbids
(`ne_zero_of_connected`) and what makes the counterexample possible.

## What this does NOT do

**It does not weaken `LaplacianSharpDisconnected`.** That file already removed connectivity by
changing the *conclusion* — some component is two-colourable, rather than the whole graph. This
witness is why the conclusion had to change, and the two statements are consistent: the
witness's `C₄` component **is** two-colourable, and its `C₃` component is not.

**It builds no general theory of disjoint unions.** One graph, on `Fin 7`, for one purpose.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace ConnectivityNecessary

open Matrix SimpleGraph LaplacianSharpEquality

/-! ## 1. The graph -/

/-- **`C₃ ⊔ C₄` ON `Fin 7`**: a triangle on `{0,1,2}`, a four-cycle on `{3,4,5,6}`, nothing
between. Built by `fromRel` because Mathlib has no disjoint-union construction for graphs.

**Named `cycThreeFour` and not `witness`**: `DualDegreeWitness.witness` is this estate's chosen
Ising configuration, a different object under a name generic enough that a third namespace holding
it would invite the collision again (`newnames_scan`). -/
def cycThreeFour : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun a b =>
    (a.val < 3 ∧ b.val < 3) ∨
    (3 ≤ a.val ∧ b.val = a.val + 1 ∧ b.val ≤ 6) ∨
    (a.val = 3 ∧ b.val = 6))

/-- Decidability through `fromRel_adj`, so that `decide` reduces. Named rather than anonymous so
`--axioms` can audit it. -/
instance instDecidableCycThreeFourAdj : DecidableRel cycThreeFour.Adj := fun a b =>
  decidable_of_iff _ (SimpleGraph.fromRel_adj _ a b).symm

theorem cycThreeFour_isRegular : cycThreeFour.IsRegularOfDegree 2 := by
  intro v
  fin_cases v <;> decide

/-! ## 2. It attains the bound -/

/-- Zero on the triangle, alternating on the four-cycle. -/
def wvec : Fin 7 → ℝ := ![0, 0, 0, 1, -1, 1, -1]

theorem wvec_ne_zero : wvec ≠ 0 := by
  intro h
  have := congrFun h 3
  simp [wvec] at this

theorem wvec_flip : ∀ u v : Fin 7, cycThreeFour.Adj u v → wvec v = - wvec u := by
  intro u v h
  fin_cases u <;> fin_cases v <;>
    first
      | exact absurd h (by decide)
      | norm_num [wvec]

/-- **THE WITNESS ATTAINS THE DEGREE BOUND**, by
`LaplacianSharpEquality.quadForm_eq_iff_neg_adj`, which needs no connectivity. -/
theorem cycThreeFour_attains :
    ∃ x : Fin 7 → ℝ, x ≠ 0 ∧
      x ⬝ᵥ (cycThreeFour.lapMatrix ℝ) *ᵥ x = 2 * ((2 : ℕ) : ℝ) * (x ⬝ᵥ x) :=
  ⟨wvec, wvec_ne_zero,
    (quadForm_eq_iff_neg_adj cycThreeFour cycThreeFour_isRegular wvec).mpr wvec_flip⟩

/-! ## 3. It is not two-colourable -/

/-- The triangle forces three colours: `{0,1,2}` are pairwise adjacent, and `Fin 2` has no three
pairwise-distinct elements. No clique API is needed for this. -/
theorem cycThreeFour_not_colorable : ¬ cycThreeFour.Colorable 2 := by
  rintro ⟨C⟩
  have h01 : (C 0).val ≠ (C 1).val :=
    fun h => C.valid (by decide : cycThreeFour.Adj 0 1) (Fin.ext h)
  have h02 : (C 0).val ≠ (C 2).val :=
    fun h => C.valid (by decide : cycThreeFour.Adj 0 2) (Fin.ext h)
  have h12 : (C 1).val ≠ (C 2).val :=
    fun h => C.valid (by decide : cycThreeFour.Adj 1 2) (Fin.ext h)
  have b0 := (C 0).isLt
  have b1 := (C 1).isLt
  have b2 := (C 2).isLt
  omega

/-! ## 4. So the hypothesis cannot be deleted -/

/-- **CONNECTIVITY IS NECESSARY IN `exists_quadForm_eq_iff_colorable`.** The statement with the
hypothesis removed is refuted by one graph. -/
theorem connectivity_necessary :
    ¬ ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
        (_ : DecidableRel G.Adj) (Δ : ℕ) (_ : G.IsRegularOfDegree Δ),
        (∃ x : V → ℝ, x ≠ 0 ∧
          x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x = 2 * (Δ : ℝ) * (x ⬝ᵥ x)) → G.Colorable 2 := by
  intro h
  exact cycThreeFour_not_colorable
    (h (Fin 7) inferInstance inferInstance cycThreeFour inferInstance 2 cycThreeFour_isRegular
      cycThreeFour_attains)

/-- **AND `LaplacianSharpDisconnected`'s CONCLUSION IS THE ONE THAT SURVIVES**, checked on the
cycThreeFour rather than asserted: it has a two-colourable component. -/
theorem cycThreeFour_has_colorable_component :
    ∃ C : cycThreeFour.ConnectedComponent, (cycThreeFour.induce C.supp).Colorable 2 :=
  LaplacianSharpDisconnected.exists_component_colorable_of_neg_adj cycThreeFour
    wvec_ne_zero wvec_flip

end ConnectivityNecessary
