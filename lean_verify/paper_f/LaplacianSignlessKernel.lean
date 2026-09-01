import LaplacianSignlessDefinite

/-!
# The kernel of `D + A`, and its dimension: the number of two-colourable components

`LaplacianSignlessDefinite` proved the dichotomy — `Q = D + A` is positive definite exactly when no
connected component of `G` is two-colourable — and fenced itself there:

> *"IT DOES NOT COUNT THE KERNEL'S DIMENSION. … What is proved here is the `0`-versus-positive
> dichotomy — whether that multiplicity is zero — and nothing about its value when it is not."*

**That fence is closed here, and the route is the one the fence named.** Mathlib carries the count
for the ordinary Laplacian `L = D − A` — `lapMatrix_ker_basis_aux` sends a component to its
indicator, two lemmas make those a basis, and `card_connectedComponent_eq_finrank_ker_toLin'_-
lapMatrix` is the theorem. This file is that chain for `Q`, **indexed by the two-colourable
components** and with **the sign colouring in place of the indicator**.

> **`card_bipartiteComponent_eq_finrank_ker`** — `Fintype.card {C // (G.induce C.supp).Colorable 2}
> = finrank ℝ (ker (toLin' (signlessLap G)))`. For every finite graph, with no hypothesis.
>
> **`finrank_ker_eq_zero_iff_posDef`** — and the previous unit's dichotomy is this count's **zero
> case**, so the two files are checked against each other rather than left to agree.

**WHY THE INDEX SET IS SMALLER THAN MATHLIB'S, AND WHY THAT IS THE WHOLE DIFFICULTY.** Every
component contributes to `L`'s kernel, because a constant is always a solution of `xᵢ = xⱼ` across
edges. Only a **bipartite** component contributes to `Q`'s, because `xⱼ = −xᵢ` around an odd cycle
forces `x = −x`. So Mathlib's spanning step is `Quot.lift` — a kernel vector of `L` literally *is* a
function on components — and no such factorisation exists here. What replaces it is §2.

## The four steps, and what each needed

**§1 is one hypothesis moved.** `LaplacianSharpDisconnected.exists_component_colorable_of_neg_adj`
said *some* component is two-colourable; the decomposition needs *this vertex's* component. That
lemma chose a vertex and then discarded it, so the general statement was inside its own proof:
`component_colorable_of_ne_zero` is it, generalised in place with the existential re-derived in
three lines and its statement unchanged (`ERRATUM 337`: extract, do not copy).

**§2 IS THE STEP WITH NO MATHLIB COUNTERPART AND IT IS FOUR LINES.** If `x` and `y` both flip sign
across every edge, then `x a · y b = x b · y a` for every walk `a → b` — **an induction that needs
neither to be non-zero**, because an edge negates both factors on each side at once. Two sign-flips
on a connected piece are therefore proportional, which is what makes the kernel one-dimensional
there. The first draft of this file tried to get the same fact by transitivity of `x u / y u`, which
needs `y` nowhere-zero and a division; the walk induction needs neither.

**§3 names the basis vector.** `compSign C hc` is the sign colouring of a two-colourable component,
extended by zero — `LaplacianSharpDisconnected.extendComp` applied to
`RegularBipartiteSharp.exists_signColouring_of_colorable`. It is `±1` on the component and `0`
off it, so it is non-zero exactly where the component is, which is what §4 needs twice.

**§4 is the count.** Linear independence is disjointness of supports rather than Mathlib's
`sum_ite_eq`; spanning is §2 at each vertex, with §1 killing the vertices whose component is not
two-colourable.

## What this does NOT do

**It computes no eigenvalue of `D + A`.** The multiplicity of `0` is the whole of what is counted;
nothing here says anything about any other point of the spectrum, and the estate has no eigenvalue
of `Q` anywhere.

**⚠ THE SECOND HALF WAS FALSE EIGHT HOURS AND TWENTY-THREE MINUTES LATER. Annotated 1 September
2026** (`ERRATUM 94`, `ERRATUM 392`). This file was committed at **2026-08-30 05:43**.
`SignlessTorusSpectrum` was committed at **14:06 the same day**: `nuQ` is the signless Laplacian's
eigenvalue on the torus and `cx_signlessLap_mulVec_chiD` is the eigenvector equation, with
`nuQ_eq_real` and `nuQ_real_nonneg` beside it; `SignlessTorusComplete.eigenvalue_iff` (14:38) makes
it a biconditional, and `TorusMultiplicity` and `TorusTopSimple` (22:01, 22:11) count the
degeneracies. **The first half stands and is this file's own scope**: nothing *here* computes an
eigenvalue, and the multiplicity of `0` is still the whole of what is counted.

**It is a statement about a matrix.** No measure appears, nothing in the OS chain changes, and no
published tag is touched.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LaplacianSignlessKernel

open Matrix SimpleGraph LaplacianSignless LaplacianSharpDisconnected
open LaplacianSharpEquality LaplacianSignlessDefinite

section Bare

variable {V : Type*} (G : SimpleGraph V)

/-! ## 1. Where a sign flip vanishes, and where it does not -/

/-- The contrapositive of `LaplacianSharpDisconnected.component_colorable_of_ne_zero`: a sign flip
vanishes at every vertex whose component is not two-colourable. -/
theorem eq_zero_of_component_not_colorable {x : V → ℝ}
    (hflip : ∀ u v : V, G.Adj u v → x v = - x u) {v : V}
    (h : ¬ (G.induce (G.connectedComponentMk v).supp).Colorable 2) : x v = 0 :=
  not_not.mp fun hne => h (component_colorable_of_ne_zero G hflip hne)

/-! ## 2. Two sign flips are proportional along a walk -/

/-- **THE STEP MATHLIB'S `L` VERSION DOES NOT NEED.** If `x` and `y` both flip sign across every
edge then `x a * y b = x b * y a` whenever `a` and `b` are joined by a walk. **Neither vector is
assumed non-zero**: a single edge negates `x` on one side and `y` on the other, and the two
negations cancel. -/
theorem flip_cross_of_walk {x y : V → ℝ}
    (hx : ∀ u v : V, G.Adj u v → x v = - x u) (hy : ∀ u v : V, G.Adj u v → y v = - y u)
    {a b : V} (w : G.Walk a b) : x a * y b = x b * y a := by
  induction w with
  | nil => ring
  | @cons u v c hadj p ih =>
      rw [hx u v hadj, hy u v hadj] at ih
      linear_combination -ih

/-- The same for reachability, which is what a component supplies. -/
theorem flip_cross_of_reachable {x y : V → ℝ}
    (hx : ∀ u v : V, G.Adj u v → x v = - x u) (hy : ∀ u v : V, G.Adj u v → y v = - y u)
    {a b : V} (h : G.Reachable a b) : x a * y b = x b * y a := by
  obtain ⟨w⟩ := h
  exact flip_cross_of_walk G hx hy w

/-! ## 3. The sign colouring of a two-colourable component, extended by zero -/

/-- **THE BASIS VECTOR**, where Mathlib's `L` version uses the indicator of a component. -/
noncomputable def compSign (C : G.ConnectedComponent)
    (hc : (G.induce C.supp).Colorable 2) : V → ℝ :=
  extendComp G C (Classical.choose (RegularBipartiteSharp.exists_signColouring_of_colorable hc))

theorem compSign_of_not_mem (C : G.ConnectedComponent)
    (hc : (G.induce C.supp).Colorable 2) {v : V} (h : v ∉ C.supp) :
    compSign G C hc v = 0 :=
  extendComp_of_not_mem G C _ h

/-- On its own component the sign colouring is `±1`, so it never vanishes there. -/
theorem compSign_ne_zero_of_mem (C : G.ConnectedComponent)
    (hc : (G.induce C.supp).Colorable 2) {v : V} (h : v ∈ C.supp) :
    compSign G C hc v ≠ 0 := by
  rw [compSign, extendComp_of_mem G C _ h]
  rcases (Classical.choose_spec
      (RegularBipartiteSharp.exists_signColouring_of_colorable hc)).1 ⟨v, h⟩ with h1 | h1 <;>
    rw [h1] <;> norm_num

/-- **AND IT FLIPS SIGN ACROSS EVERY EDGE OF THE WHOLE GRAPH**, not merely of its component: off
the component both ends are `0`, and an edge cannot leave a component. -/
theorem compSign_flip (C : G.ConnectedComponent) (hc : (G.induce C.supp).Colorable 2) :
    ∀ u v : V, G.Adj u v → compSign G C hc v = - compSign G C hc u := by
  intro u v huv
  by_cases hu : u ∈ C.supp
  · have hv : v ∈ C.supp := mem_supp_of_adj G huv hu
    have hadj : (G.induce C.supp).Adj ⟨u, hu⟩ ⟨v, hv⟩ := huv
    rw [compSign, extendComp_of_mem G C _ hu, extendComp_of_mem G C _ hv,
      (Classical.choose_spec
        (RegularBipartiteSharp.exists_signColouring_of_colorable hc)).2 _ _ hadj]
    ring
  · have hv : v ∉ C.supp := fun hv => hu (mem_supp_of_adj G huv.symm hv)
    rw [compSign_of_not_mem G C hc hu, compSign_of_not_mem G C hc hv]
    ring

/-! ## 3b. The two-colourable components, and a representative of each -/

/-- **THE INDEX SET**, where Mathlib's `L` version is indexed by all of `ConnectedComponent`. -/
abbrev BipComp := {C : G.ConnectedComponent // (G.induce C.supp).Colorable 2}

/-- A representative vertex of a two-colourable component. **Named `compRep` and not `rep`**:
`BlockDimension.rep` is the estate's chosen representative of a *block class*, the same idea on a
different index type, and a third namespace holding the bare name would invite the collision again
(`newnames_scan`). -/
noncomputable def compRep (C : BipComp G) : V := Classical.choose C.1.exists_rep

theorem connectedComponentMk_compRep (C : BipComp G) :
    G.connectedComponentMk (compRep G C) = C.1 :=
  Classical.choose_spec C.1.exists_rep

theorem compRep_mem_supp (C : BipComp G) : compRep G C ∈ C.1.supp :=
  (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr (connectedComponentMk_compRep G C)

/-- Off its own component the basis vector vanishes, which is both halves of §4. -/
theorem compSign_eq_zero_of_ne {C : BipComp G} {v : V}
    (h : G.connectedComponentMk v ≠ C.1) : compSign G C.1 C.2 v = 0 :=
  compSign_of_not_mem G C.1 C.2
    (fun hm => h ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hm))

end Bare

section Count


variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 4. The basis, and the count -/

/-- Two-colourability is not decidable, so the index set is finite by `Finite` and not by a
computable predicate. Named rather than anonymous so `--axioms` can audit it. -/
noncomputable instance instFintypeBipComp : Fintype (BipComp G) := Fintype.ofFinite _

theorem compSign_mem_ker (C : BipComp G) :
    compSign G C.1 C.2 ∈ LinearMap.ker (Matrix.toLin' (signlessLap G)) := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply]
  exact (signlessLap_mulVec_eq_zero_iff G _).mpr (compSign_flip G C.1 C.2)

/-- The family Mathlib calls `lapMatrix_ker_basis_aux`, for `Q` and over the two-colourable
components only. -/
noncomputable def kerBasisAux (C : BipComp G) :
    LinearMap.ker (Matrix.toLin' (signlessLap G)) :=
  ⟨compSign G C.1 C.2, compSign_mem_ker G C⟩

/-- Evaluating a combination of the family at a vertex leaves at most one term: the one whose
component is the vertex's. **Disjointness of supports is what Mathlib gets from `sum_ite_eq`.** -/
theorem sum_kerBasisAux_apply (g : BipComp G → ℝ) (v : V) :
    (∑ C, g C • kerBasisAux G C).val v
      = ∑ C : BipComp G, g C * compSign G C.1 C.2 v := by
  rw [AddSubmonoid.coe_finset_sum]
  simp [kerBasisAux]

theorem sum_kerBasisAux_apply_of_mem (g : BipComp G → ℝ) {C₀ : BipComp G} {v : V}
    (hv : G.connectedComponentMk v = C₀.1) :
    (∑ C, g C • kerBasisAux G C).val v = g C₀ * compSign G C₀.1 C₀.2 v := by
  rw [sum_kerBasisAux_apply G g v]
  refine Finset.sum_eq_single C₀ (fun D _ hD => ?_) (fun h => absurd (Finset.mem_univ _) h)
  have hne : G.connectedComponentMk v ≠ D.1 := by
    rw [hv]
    exact fun hc => hD (Subtype.ext hc.symm)
  rw [compSign_eq_zero_of_ne G (C := D) (v := v) hne, mul_zero]

theorem linearIndependent_kerBasisAux : LinearIndependent ℝ (kerBasisAux G) := by
  rw [Fintype.linearIndependent_iff]
  intro g h0 C
  have hval : (∑ D, g D • kerBasisAux G D).val (compRep G C) = 0 := by
    rw [h0]; rfl
  rw [sum_kerBasisAux_apply_of_mem G g (connectedComponentMk_compRep G C)] at hval
  exact (mul_eq_zero.mp hval).resolve_right
    (compSign_ne_zero_of_mem G C.1 C.2 (compRep_mem_supp G C))

theorem top_le_span_range_kerBasisAux :
    ⊤ ≤ Submodule.span ℝ (Set.range (kerBasisAux G)) := by
  intro x _
  rw [Submodule.mem_span_range_iff_exists_fun]
  have hflip : ∀ u v : V, G.Adj u v → x.val v = - x.val u := by
    refine (signlessLap_mulVec_eq_zero_iff G x.val).mp ?_
    have := x.2
    rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
  refine ⟨fun C => x.val (compRep G C) / compSign G C.1 C.2 (compRep G C), ?_⟩
  ext v
  by_cases hcol : (G.induce (G.connectedComponentMk v).supp).Colorable 2
  · set C₀ : BipComp G := ⟨G.connectedComponentMk v, hcol⟩ with hC₀
    rw [sum_kerBasisAux_apply_of_mem G _ (C₀ := C₀) rfl]
    have hne : compSign G C₀.1 C₀.2 (compRep G C₀) ≠ 0 :=
      compSign_ne_zero_of_mem G C₀.1 C₀.2 (compRep_mem_supp G C₀)
    have hreach : G.Reachable (compRep G C₀) v := by
      have := connectedComponentMk_compRep G C₀
      rw [hC₀] at this
      exact SimpleGraph.ConnectedComponent.exact this
    have hcross := flip_cross_of_reachable G hflip (compSign_flip G C₀.1 C₀.2) hreach
    field_simp
    linarith [hcross]
  · have hz : ∀ C : BipComp G, compSign G C.1 C.2 v = 0 := by
      intro C
      refine compSign_eq_zero_of_ne G (C := C) (v := v) (fun hc => hcol ?_)
      rw [hc]; exact C.2
    rw [sum_kerBasisAux_apply G _ v]
    simp only [hz, mul_zero, Finset.sum_const_zero]
    exact (eq_zero_of_component_not_colorable G hflip hcol).symm

/-- **THE BASIS**, the shape of Mathlib's `lapMatrix_ker_basis`. -/
noncomputable def kerBasis :=
  Module.Basis.mk (linearIndependent_kerBasisAux G) (top_le_span_range_kerBasisAux G)

/-- **THE COUNT: THE DIMENSION OF `Q`'s KERNEL IS THE NUMBER OF TWO-COLOURABLE COMPONENTS.** The
statement `LaplacianSignlessDefinite` fenced itself against, at the generality it fenced at — every
finite graph, no hypothesis. -/
theorem card_bipartiteComponent_eq_finrank_ker :
    Fintype.card (BipComp G)
      = Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G))) := by
  rw [Module.finrank_eq_card_basis (kerBasis G)]

/-- **AND THE PREVIOUS UNIT'S DICHOTOMY IS THIS COUNT'S ZERO CASE.**
`LaplacianSignlessDefinite.signlessLap_posDef_iff` said `Q ≻ 0` iff no component is
two-colourable; that is the index set being empty, hence the dimension being `0`. Stated so the
two files are checked against each other rather than left to agree. -/
theorem finrank_ker_eq_zero_iff_posDef :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G))) = 0
      ↔ (signlessLap G).PosDef := by
  rw [← card_bipartiteComponent_eq_finrank_ker G, Fintype.card_eq_zero_iff,
    signlessLap_posDef_iff G]
  exact isEmpty_subtype _

end Count

end LaplacianSignlessKernel
