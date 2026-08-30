import LaplacianSignless
import LaplacianSharpDisconnected

/-!
# `D + A` is positive definite exactly when no component is two-colourable

`LaplacianSignless` named the signless Laplacian `Q = D + A`, computed its quadratic form as
`½ Σᵢ Σⱼ [i ∼ j] (xᵢ + xⱼ)²`, and characterised where that form vanishes. It stopped one step short
of the matrix statements those facts are worth, and **its header promised one of them by name**
(`ERRATUM 343`). This file supplies them.

> **`signlessLap_posSemidef`** — the name `LaplacianSignless`'s header cited and the file did not
> contain. `Q` is positive semidefinite for **every** finite graph.
>
> **`signlessLap_mulVec_eq_zero_iff`** — `Q x = 0` **iff `x` flips sign across every edge**. This is
> the *kernel of the matrix*, where `dotProduct_signlessLap_eq_zero_iff` gave only the zero set of
> the form; positive semidefiniteness is exactly what closes the gap between them.
>
> **`signlessLap_posDef_iff`** — `Q` is positive **definite** iff **no connected component of `G` is
> two-colourable**. No regularity, no connectivity, no hypothesis on the graph at all.
>
> **`signlessLap_posDef_iff_of_connected`** — and on a connected graph that reads `Q ≻ 0 ↔ G` is not
> two-colourable.
>
> **`quadForm_lt_iff_no_component_colorable`** — and on a regular graph the criterion is the
> **strict** degree bound: `xᵀLx < 2Δ‖x‖²` at every `x ≠ 0` iff no component is two-colourable.

**THE CRITERION IS SHOWN TO DISCRIMINATE ON THIS PROJECT'S OWN LATTICE, IN BOTH DIRECTIONS.** The
periodic lattice has `Q ≻ 0` at every odd side length `≥ 3` and `Q ⊁ 0` at every even side length
`≥ 2`, in every dimension `≥ 1` in both cases, from `torus_not_colorable_two_of_odd` and
`TorusBipartite` respectively. A
one-directional criterion could be vacuous; this one is exhibited separating two families of graphs
the estate already builds.

**AND `Q` IS NOT A NEW MATRIX, WHICH §6 MAKES A THEOREM RATHER THAN A REMARK.** `L = D − A` and
`Q = D + A`, so `signlessLap_add_lapMatrix` says `Q + L = 2D` for every finite graph, and on a
`Δ`-regular one `dotProduct_signlessLap_of_regular` reads `xᵀQx = 2Δ‖x‖² − xᵀLx`. Hence
`posDef_iff_quadForm_lt`: **positive definiteness of `Q` IS the degree bound holding strictly**. The
bound meant is the one at `deg ≡ Δ`, which is what `sum_adj_add_sq` supplies and what
`LaplacianSharpEquality`'s own `example` re-derives — **not** `LaplacianDegreeBound`'s full
`deg ≤ Δ` statement, a distinction that file already had to make (`ERRATUM 201`).

Composed with the criterion above, that is
`quadForm_lt_iff_no_component_colorable` — the strict companion to
`LaplacianSharpDisconnected.exists_quadForm_eq_iff_exists_component_colorable`, which says when the
bound is *attained*. **The two files' answers are complementary because they are the same fact
subtracted from `2Δ‖x‖²`**, and that is now checked rather than observed.

**WHY POSITIVE DEFINITENESS AND NOT AN EIGENVALUE.** `Matrix.PosDef` is `IsHermitian` together with
`0 < xᵀQx` at every `x ≠ 0` — a quantifier over vectors, needing no spectrum. Every ingredient
was already
here: `dotProduct_signlessLap_nonneg` gives `≤`, `dotProduct_signlessLap_eq_zero_iff` says when the
form is `0`, and `LaplacianSharpDisconnected` §§2–3 turn "flips sign across every edge" into "some
component is two-colourable" and back. **Those two sections carry no `Fintype`, no regularity and
no matrix** — they were written that way in the previous unit and this is the first thing to use
them at that generality.

**ONE `example` IS PROMOTED TO A THEOREM AND GENERALISED.** `LaplacianSharpDisconnected` closed with
an unnamed `example` recovering the connected case, so the bridge inside it — that a connected
graph has one component and it is everything — was proved and then thrown away. It is
`exists_component_colorable_iff_colorable` here, and it is strictly more general: the `example`
carried `[Fintype V]`, `[DecidableEq V]`, `[DecidableRel G.Adj]` and `IsRegularOfDegree`, and the
bridge needs none of the four.

**ABSENT FROM MATHLIB FOR `Q`, AND THE ROUTE USED HERE IS MATHLIB'S OWN FOR `L`** (`ERRATUM 194`,
by shape rather than by name per `ERRATUM 42`). Re-measured for this file rather than inherited:
`signless` matches **0** Mathlib files and `degMatrix.*+.*adjMatrix` **0** lines, so `Q` is not in
the library under any spelling. **But the twin matrix is, in full**, and the correspondence is
worth stating exactly because it is the map for what is still missing:

Everything below is in `Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean` for `L`, against what
this estate has for `Q`:

* positive semidefinite — `posSemidef_lapMatrix` / `signlessLap_posSemidef`, §2.
* the **form**'s zero set — `lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj` /
  `LaplacianSignless.dotProduct_signlessLap_eq_zero_iff`.
* the **kernel** — `lapMatrix_mulVec_eq_zero_iff_forall_adj` / `signlessLap_mulVec_eq_zero_iff`, §3.
* the kernel's **dimension** — `lapMatrix_ker_basis` and
  `card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix` / **nothing, see below**.

**So §3 did not invent its route.** Mathlib gets from its form statement to its kernel statement by
`posSemidef_lapMatrix` and `PosSemidef.toLinearMap₂'_zero_iff`; §3 gets from ours to ours by
`signlessLap_posSemidef` and `PosSemidef.dotProduct_mulVec_zero_iff`. **No difficulty is inferred
from the absence** — the proofs are short, and they are short because they are transplants.

## What this does NOT do

**IT DOES NOT COUNT THE KERNEL'S DIMENSION.** The classical statement is that the multiplicity of
`0` as an eigenvalue of `Q` equals the number of **bipartite** connected components. What is proved
here is the `0`-versus-positive dichotomy — whether that multiplicity is zero — and nothing about
its value when it is not.

**AND THE HONEST FORM OF THAT FENCE NAMES A TEMPLATE RATHER THAN A VOID**, which a first draft of
this header got wrong by saying only that the statement "is not in Mathlib for `Q`". **Mathlib has
it for `L`, worked in full**: `lapMatrix_ker_basis_aux` sends a connected component to its
indicator, `linearIndependent_lapMatrix_ker_basis_aux` and
`top_le_span_range_lapMatrix_ker_basis_aux` make those a basis of the kernel, and
`card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix` is the count. The `Q` version would
index by the **bipartite** components and use the sign colouring where Mathlib uses the
indicator. `LaplacianSharpDisconnected.extendComp` is already the **extension half** of that map,
with `RegularBipartiteSharp.exists_signColouring_of_colorable` supplying what it extends — one
choice per bipartite component, which is where the assembly would begin rather than end.
**So the gap is that nobody has assembled it, not that the pattern is unknown** — `ERRATUM 340`'s
distinction, applied here to this file's own fence, and no cost is claimed for it (`ERRATUM 246`).

**It computes no eigenvalue of `D + A`**, here or anywhere in this estate. `TorusLaplacianSpectrum`
diagonalises the *massive* Laplacian on the periodic lattice and says nothing about `Q`.

**It does not remove regularity from the Loewner statements.** `LaplacianSignless` explained why it
cannot — without regularity the degree-weighted sum does not collapse to a single constant — and
nothing here changes that. What generalises is still the equality case, not the order statement.

**It is a statement about a matrix.** No measure appears, nothing in the OS chain changes, and no
published tag is touched.

**AND IT DOES NOT REACH THE LOEWNER ORDER.** §6 relates the two quadratic FORMS; turning
`posDef_iff_quadForm_lt` into a statement about `massive ≼ c·1` needs the eigenvalue machinery
`LaplacianLoewnerConverse` carries, and that composition is not made here.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LaplacianSignlessDefinite

open Matrix SimpleGraph BoxGraph TorusReflection LaplacianSignless
open LaplacianSharpDisconnected LaplacianSharpEquality

section Component

variable {V : Type*} (G : SimpleGraph V)

/-! ## 1. Connectivity collapses the component quantifier -/

/-- **A CONNECTED GRAPH HAS ONE COMPONENT AND IT IS EVERYTHING**, so quantifying over components is
quantifying over the graph. Promoted from the closing `example` of `LaplacianSharpDisconnected`,
which proved it inside a statement about regular graphs and matrices; it needs neither. -/
theorem exists_component_colorable_iff_colorable [Nonempty V] (hG : G.Connected) :
    (∃ C : G.ConnectedComponent, (G.induce C.supp).Colorable 2) ↔ G.Colorable 2 := by
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

end Component

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 2. `D + A` is Hermitian and positive semidefinite -/

/-- Over `ℝ` this is the sum of two of Mathlib's own facts about `D` and `A`. -/
theorem signlessLap_isHermitian : (signlessLap G).IsHermitian :=
  (G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)

/-- **THE NAME `LaplacianSignless`'s HEADER PROMISED** (`ERRATUM 343`). `Q = D + A` is positive
semidefinite for every finite graph, because its quadratic form is a sum of squares. -/
theorem signlessLap_posSemidef : (signlessLap G).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (signlessLap_isHermitian G) fun x => ?_
  rw [star_trivial]
  exact dotProduct_signlessLap_nonneg G x

/-! ## 3. The kernel of the matrix, not merely the zero set of its form -/

/-- **`Q x = 0` IFF `x` FLIPS SIGN ACROSS EVERY EDGE.** `dotProduct_signlessLap_eq_zero_iff` said
this of the *number* `xᵀQx`; a vector can annihilate a quadratic form without being in the kernel,
and what rules that out is positive semidefiniteness. -/
theorem signlessLap_mulVec_eq_zero_iff (x : V → ℝ) :
    (signlessLap G) *ᵥ x = 0 ↔ ∀ u v : V, G.Adj u v → x v = - x u := by
  rw [← (signlessLap_posSemidef G).dotProduct_mulVec_zero_iff x, star_trivial]
  exact dotProduct_signlessLap_eq_zero_iff G x

/-! ## 4. Positive definiteness, with no hypothesis on the graph -/

/-- **`D + A` IS POSITIVE DEFINITE EXACTLY WHEN NO COMPONENT IS TWO-COLOURABLE.** Neither
regularity nor connectivity appears, and the graph is otherwise arbitrary. -/
theorem signlessLap_posDef_iff :
    (signlessLap G).PosDef ↔ ∀ C : G.ConnectedComponent, ¬ (G.induce C.supp).Colorable 2 := by
  constructor
  · intro hpd C hc
    obtain ⟨x, hx, hflip⟩ := exists_neg_adj_of_component_colorable G C hc
    have hzero : x ⬝ᵥ (signlessLap G) *ᵥ x = 0 :=
      (dotProduct_signlessLap_eq_zero_iff G x).mpr hflip
    have hpos := hpd.dotProduct_mulVec_pos hx
    rw [star_trivial, hzero] at hpos
    exact lt_irrefl 0 hpos
  · intro hno
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (signlessLap_isHermitian G) fun x hx => ?_
    rw [star_trivial]
    refine lt_of_le_of_ne (dotProduct_signlessLap_nonneg G x) fun heq => ?_
    obtain ⟨C, hc⟩ := exists_component_colorable_of_neg_adj G hx
      ((dotProduct_signlessLap_eq_zero_iff G x).mp heq.symm)
    exact hno C hc

/-- **THE CONNECTED CASE**, where the component quantifier collapses. -/
theorem signlessLap_posDef_iff_of_connected [Nonempty V] (hG : G.Connected) :
    (signlessLap G).PosDef ↔ ¬ G.Colorable 2 := by
  rw [signlessLap_posDef_iff G, ← not_exists]
  exact not_congr (exists_component_colorable_iff_colorable G hG)

/-! ## 5. The criterion separating two families this project already builds -/

/-- **THE ODD CYCLE.** -/
theorem odd_cycle_signlessLap_posDef (M : ℕ) :
    (signlessLap (cycleGraph (2 * M + 3))).PosDef := by
  haveI : Nonempty (Fin (2 * M + 3)) := ⟨⟨0, by omega⟩⟩
  have hconn : (cycleGraph (2 * M + 3)).Connected := by
    have := SimpleGraph.cycleGraph_connected (n := 2 * M + 2)
    simpa using this
  rw [signlessLap_posDef_iff_of_connected _ hconn]
  intro hcol
  have hchi : (cycleGraph (2 * M + 3)).chromaticNumber = 3 :=
    chromaticNumber_cycleGraph_of_odd (2 * M + 3) (by omega) ⟨M + 1, by ring⟩
  have hle := hcol.chromaticNumber_le
  rw [hchi] at hle
  norm_num at hle

/-- **THE PERIODIC LATTICE AT ODD SIDE LENGTH, IN EVERY DIMENSION.** -/
theorem torus_odd_signlessLap_posDef {d n : ℕ} (hodd : Odd (n + 1)) (h3 : 3 ≤ n + 1) :
    (signlessLap (torusGraph (d + 1) (n + 1))).PosDef := by
  haveI : Nonempty (Site (d + 1) (n + 1)) := ⟨fun _ => ⟨0, by omega⟩⟩
  rw [signlessLap_posDef_iff_of_connected _
    (TorusDecay.torusGraph_connected (d + 1) (by omega))]
  exact torus_not_colorable_two_of_odd hodd h3

/-- **AND NOT AT EVEN SIDE LENGTH**, which is what makes the criterion a criterion rather than a
one-directional sufficient condition. `TorusBipartite` supplies the colouring. -/
theorem torus_even_not_signlessLap_posDef {d n : ℕ} (hn : Even n) (h2 : 2 ≤ n) :
    ¬ (signlessLap (torusGraph (d + 1) n)).PosDef := by
  haveI : Nonempty (Site (d + 1) n) := ⟨fun _ => ⟨0, by omega⟩⟩
  rw [signlessLap_posDef_iff_of_connected _
    (TorusDecay.torusGraph_connected (d + 1) (by omega))]
  exact not_not.mpr (TorusBipartite.torusGraph_colorable_two hn)

/-! ## 6. `Q` and `L` are one matrix apart, so the two criteria are one criterion -/

/-- **`Q + L = 2D`, for every finite graph.** `L = D − A` and `Q = D + A`, so the adjacency
cancels. Stated nowhere in this estate before, and nowhere in Mathlib, which has no `Q`. -/
theorem signlessLap_add_lapMatrix : signlessLap G + G.lapMatrix ℝ = (2 : ℝ) • G.degMatrix ℝ := by
  rw [signlessLap, SimpleGraph.lapMatrix]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- **AND ON A REGULAR GRAPH THE FORMS ARE ONE SUBTRACTION APART.** Read off the previous unit's
`sum_adj_add_sq` rather than from the matrix identity, which is shorter. -/
theorem dotProduct_signlessLap_of_regular {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (x : V → ℝ) :
    x ⬝ᵥ (signlessLap G) *ᵥ x
      = 2 * (Δ : ℝ) * (x ⬝ᵥ x) - x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x := by
  rw [dotProduct_signlessLap G x, sum_adj_add_sq G hreg x]
  ring

/-- **SO `Q ≻ 0` IS EXACTLY THE STRICT DEGREE BOUND.** `LaplacianDegreeBound` gives `xᵀLx ≤
2Δ‖x‖²`; this says positive definiteness of `Q` is that inequality being STRICT at every non-zero
vector. -/
theorem posDef_iff_quadForm_lt {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) :
    (signlessLap G).PosDef ↔
      ∀ x : V → ℝ, x ≠ 0 → x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x < 2 * (Δ : ℝ) * (x ⬝ᵥ x) := by
  constructor
  · intro hpd x hx
    have hp := hpd.dotProduct_mulVec_pos hx
    rw [star_trivial, dotProduct_signlessLap_of_regular G hreg x] at hp
    linarith
  · intro h
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (signlessLap_isHermitian G) fun x hx => ?_
    rw [star_trivial, dotProduct_signlessLap_of_regular G hreg x]
    linarith [h x hx]

/-- **THE STRICT COMPANION TO `LaplacianSharpDisconnected`.** That file says when the degree bound
is ATTAINED; this says when it is strict everywhere, and the two answers are complementary as they
must be. Obtained by composing the previous two results, so the agreement is a theorem rather than
an observation. -/
theorem quadForm_lt_iff_no_component_colorable {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) :
    (∀ x : V → ℝ, x ≠ 0 → x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x < 2 * (Δ : ℝ) * (x ⬝ᵥ x))
      ↔ ∀ C : G.ConnectedComponent, ¬ (G.induce C.supp).Colorable 2 :=
  (posDef_iff_quadForm_lt G hreg).symm.trans (signlessLap_posDef_iff G)

end LaplacianSignlessDefinite
