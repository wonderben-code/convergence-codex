import LaplacianSignlessKernel
import RayleighAttainment

/-!
# The top eigenspace of a regular graph's Laplacian, and its dimension

`RayleighAttainment` §4 identified *a vector attains the degree bound* with *`2Δ` is an eigenvalue*
on any regular graph, as an **existence** statement. This file makes it pointwise and then counts.

**THE ESTATE ALREADY HAD THE HARD HALF, IN ANOTHER CURRENCY, AND THE GREP FOUND IT BEFORE ANYTHING
WAS WRITTEN** (`ERRATUM 436`'s rule, working). `LaplacianSignless.signlessLap` is `Q = D + A`;
`LaplacianSignlessDefinite.signlessLap_mulVec_eq_zero_iff` says `Q x = 0` **iff `x` flips sign
across every edge**, at every finite graph; and
`LaplacianSignlessKernel.card_bipartiteComponent_eq_finrank_ker` says **`dim ker Q` is the number
of two-colourable components**, also with no hypothesis. On a
`Δ`-regular graph `D = Δ • 1`, so `Q = 2Δ • 1 − L` and those are statements about `L`'s **top
eigenspace**. Nothing here re-proves any of them.

> **`signlessLap_eq_of_regular`** — `Q = 2Δ • 1 − L` on a `Δ`-regular graph, which is the whole
> join.
>
> **`mulVec_eq_top_smul_iff_neg_adj`** — `L x = 2Δ • x` **iff** `x` flips sign across every edge.
> Pointwise, and with **no connectivity**.
>
> **`card_bipartiteComponent_eq_finrank_top_eigenspace`** — **the multiplicity of `2Δ` as an
> eigenvalue of `L` is the number of two-colourable connected components.**

## What that adds and what it does not

**It is a currency change and it says so.** Every mathematical step is `LaplacianSignless*`'s; what
is new is that those statements are read on `L` rather than on `Q`, which is where the rest of this
estate's Laplacian work lives — `LaplacianDegreeBound`, `LaplacianSharpEquality`,
`LaplacianLoewnerConverse`, `LaplacianNormSharp` and `RayleighAttainment` all speak about `L` and
none of them mentions `Q`.

**IT MAKES THE DAY'S EXISTENCE RESULTS QUANTITATIVE.**
`RayleighAttainment.exists_eigenvector_top_iff_exists_quadForm_eq` and
`LaplacianNormSharp.norm_lapMatrix_eq_iff_exists_component_colorable` both say *there is such a
vector iff some component is two-colourable*; this says **how many** independent ones there are, and
the two are consistent by construction — the count is positive exactly when the index type is
non-empty.

**It computes no other multiplicity.** `2Δ` is the only eigenvalue this reaches, because `Q`'s
kernel is the only fibre `LaplacianSignlessKernel` counts. The open item about eigenvalue fibres of
the massive torus Laplacian asks about **every** fibre and is untouched.

**No wall moves**, and nothing consumes this. **AND SIMPLICITY OF A TOP EIGENVALUE IS NOT NEW HERE**
— `TorusTopSimple`, `TorusRealMultiplicity` and `PerronSimple` all have it, for one family and one
matrix class; §4 records what this adds over them (`ERRATUM 438`).

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LaplacianTopEigenspace

open Matrix SimpleGraph LaplacianSignless

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. On a regular graph the signless Laplacian is the degree bound minus the Laplacian -/

/-- **`D = Δ • 1` ON A `Δ`-REGULAR GRAPH.** -/
theorem degMatrix_eq_of_regular {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) :
    G.degMatrix ℝ = (Δ : ℝ) • (1 : Matrix V V ℝ) := by
  ext u v
  rw [SimpleGraph.degMatrix, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
  by_cases h : u = v <;> simp [h, hreg u]

/-- **`Q = 2Δ • 1 − L`**, which is the whole join: everything `LaplacianSignless*` proves about
`Q`'s kernel is a statement about `L`'s top eigenspace. -/
theorem signlessLap_eq_of_regular {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) :
    signlessLap G = (2 * (Δ : ℝ)) • (1 : Matrix V V ℝ) - G.lapMatrix ℝ := by
  rw [signlessLap, SimpleGraph.lapMatrix, degMatrix_eq_of_regular G hreg]
  ext u v
  simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> ring

/-! ## 2. The eigenspace, pointwise -/

/-- **`L x = 2Δ • x` IFF `x` FLIPS SIGN ACROSS EVERY EDGE**, on a `Δ`-regular graph, **pointwise and
with no connectivity**. `LaplacianSignlessDefinite.signlessLap_mulVec_eq_zero_iff` read on `L`. -/
theorem mulVec_eq_top_smul_iff_neg_adj {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (x : V → ℝ) :
    G.lapMatrix ℝ *ᵥ x = (2 * (Δ : ℝ)) • x ↔ ∀ u v : V, G.Adj u v → x v = - x u := by
  rw [← LaplacianSignlessDefinite.signlessLap_mulVec_eq_zero_iff G x,
    signlessLap_eq_of_regular G hreg, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    sub_eq_zero]
  exact eq_comm

/-! ## 3. And its dimension -/

/-- **THE MULTIPLICITY OF `2Δ` AS AN EIGENVALUE OF `L` IS THE NUMBER OF TWO-COLOURABLE CONNECTED
COMPONENTS**, on a `Δ`-regular graph.
`LaplacianSignlessKernel.card_bipartiteComponent_eq_finrank_ker` read on `L`. -/
theorem card_bipartiteComponent_eq_finrank_top_eigenspace {Δ : ℕ}
    (hreg : G.IsRegularOfDegree Δ) :
    Fintype.card (LaplacianSignlessKernel.BipComp G)
      = Module.finrank ℝ
          (LinearMap.ker (Matrix.toLin' ((2 * (Δ : ℝ)) • (1 : Matrix V V ℝ) - G.lapMatrix ℝ))) := by
  rw [← signlessLap_eq_of_regular G hreg]
  exact LaplacianSignlessKernel.card_bipartiteComponent_eq_finrank_ker G

/-! ## 4. On a connected graph the count is `1` or `0`, so the top eigenvalue is simple or absent -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **ON A CONNECTED GRAPH A COMPONENT IS TWO-COLOURABLE EXACTLY WHEN THE GRAPH IS.** The
`induceUnivIso` bridge, **extracted rather than inlined a fourth time** (`ERRATUM 337`: the estate's
recurring defect is re-proving what it already has, and a shared proof is the structural answer).
`LaplacianLoewnerDisconnected` has it inside an `example` and `CycleNormFromColouring` inside a
proof term; neither exports it. -/
theorem induce_colorable_iff_of_connected (hG : G.Connected) (C : G.ConnectedComponent) :
    (G.induce C.supp).Colorable 2 ↔ G.Colorable 2 := by
  have hsupp : C.supp = Set.univ := by
    obtain ⟨v₀, hv₀⟩ := C.exists_rep
    subst hv₀
    ext v
    simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, Set.mem_univ, iff_true]
    exact SimpleGraph.ConnectedComponent.sound (hG.preconnected v v₀)
  constructor
  · intro h
    rw [hsupp] at h
    exact SimpleGraph.Colorable.of_hom (SimpleGraph.induceUnivIso G).symm.toHom h
  · intro h
    exact SimpleGraph.Colorable.of_hom (SimpleGraph.Embedding.induce _).toHom h

/-- **THE TOP EIGENVALUE IS SIMPLE ON A CONNECTED TWO-COLOURABLE REGULAR GRAPH.** One component, and
it is two-colourable, so the count of §3 is `1`.

**⚠ SIMPLICITY IS NOT NEW IN THIS ESTATE AND THE FIRST DRAFT OF THIS UNIT SAID IT WAS**
(`ERRATUM 438`). Three earlier results give it: `TorusTopSimple.top_eigenvalue_simple` and
`TorusRealMultiplicity.top_eigenvalue_simple_real` — `finrank = 1` at `4d + m²` on the even periodic
lattice, over `ℂ` and over `ℝ` — and `PerronSimple`, simplicity of the top eigenvalue of a strictly
positive matrix, written for `WALLS` §W4.0 §6 item 2.
**`RealComplexKernel.card_bipComp_eq_finrank_ker_cx` is the same count as §3 against the
complexified kernel**, and `torus_card_bipComp_eq_one` is the
torus case of it.
**WHAT IS ACTUALLY NEW HERE, MEASURED**: those are **one family and one matrix class**; this is
**every connected regular graph**, with the dichotomy — simple when two-colourable, **not an
eigenvalue at all** otherwise — and stated on `L` rather than on `Q` or on a complexification.
Neither direction subsumes the other: `TorusTopSimple` identifies the frequency and crosses to `ℂ`,
which this does not. -/
theorem finrank_top_eigenspace_eq_one [Nonempty V] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hG : G.Connected) (hcol : G.Colorable 2) :
    Module.finrank ℝ
        (LinearMap.ker (Matrix.toLin' ((2 * (Δ : ℝ)) • (1 : Matrix V V ℝ) - G.lapMatrix ℝ)))
      = 1 := by
  rw [← card_bipartiteComponent_eq_finrank_top_eigenspace G hreg]
  refine Fintype.card_eq_one_iff.mpr ?_
  obtain ⟨v₀⟩ := ‹Nonempty V›
  refine ⟨⟨G.connectedComponentMk v₀, (induce_colorable_iff_of_connected G hG _).mpr hcol⟩,
    fun C => Subtype.ext ?_⟩
  obtain ⟨w, hw⟩ := C.1.exists_rep
  rw [← hw]
  exact SimpleGraph.ConnectedComponent.sound (hG.preconnected w v₀)

/-- **AND IT IS NOT AN EIGENVALUE AT ALL OTHERWISE.** No component is two-colourable, so the count
is `0`, which is `LaplacianLoewnerConverse.eigenvalues_massive_lt_of_not_colorable` in the dimension
currency. -/
theorem finrank_top_eigenspace_eq_zero {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hG : G.Connected) (hcol : ¬ G.Colorable 2) :
    Module.finrank ℝ
        (LinearMap.ker (Matrix.toLin' ((2 * (Δ : ℝ)) • (1 : Matrix V V ℝ) - G.lapMatrix ℝ)))
      = 0 := by
  rw [← card_bipartiteComponent_eq_finrank_top_eigenspace G hreg]
  refine Fintype.card_eq_zero_iff.mpr ⟨fun C => ?_⟩
  exact hcol ((induce_colorable_iff_of_connected G hG C.1).mp C.2)

end LaplacianTopEigenspace
