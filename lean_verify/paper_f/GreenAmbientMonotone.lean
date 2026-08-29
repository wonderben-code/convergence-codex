import GreenDomainMonotone
import BoxGraph

/-!
# The other variation: growing the AMBIENT graph, which moves the propagator the other way

`GreenDomainMonotone` proved what happens when the **domain** grows inside a fixed ambient graph:
`greenDirichlet_mono`, cutting less gives more. **This file is the other variation** — a fixed
window, and the graph around it grows — and the answer is the opposite: **more ambient graph gives
less propagator**, because the window's sites acquire more neighbours to be killed at.

That is worth having on its own, and it is also the sentence `ERRATUM 335` turns on. The
monotone-plus-bounded route to `G_n(x,y) → G(x,y)` needs the domains to grow inside one fixed
ambient object; **growing the ambient graph instead is not a substitute, because it moves the
propagator the wrong way**, and that is now a theorem rather than a paragraph.

## What is proved

* `submatrix_le_submatrix` — cutting to a subdomain preserves the Loewner order;
* **`massive_le_submatrix_of_adj_iff`** — `GreenDomainMonotone.massive_comap_le_submatrix` with
  `K.comap e` replaced by the property that characterises it, so the conclusion can be stated
  about a graph the estate already has rather than about a `comap` of one. The `comap` case is
  instantiated immediately below it, as the statement it generalises;
* **`greenDirichlet_le_of_adj_iff`** — hence the window's Dirichlet propagator computed in the
  **larger** graph is the **smaller** matrix;
* `siteIncl`, `siteIncl_injective`, `siteIncl_comp`, **`boxGraph_adj_incl`** and
  **`comap_boxGraph`** — the estate's box graphs nest: the induced subgraph of the big box on the
  small box is not merely a graph on the right vertex set, it is `boxGraph d n` itself;
* **`greenDirichlet_box_antitone`** — so on a fixed window the Dirichlet propagator is antitone in
  the side length of the ambient box;
* **`tendsto_greenDirichlet_box`** — antitone and bounded below by zero, so **each diagonal entry
  converges.**

## What the last one is, and what it is not

**`WALLS.md` §W2.1 §4 says of step 1b:** *"Nothing in this estate is a statement about a sequence
of Green functions converging; `GreenDecay` and `TorusDecay` bound them uniformly, which is a
different quantifier."* **That sentence is false as written once this file exists**, and it is
annotated where it stands rather than edited (`ERRATUM 94`). It was true when it was written and
this is not an erratum.

**And the step does not move, because this is a different sequence.** Four differences, each of
which alone is enough:

* §W2.1 asks about the **free** box propagator `green (boxGraph d n) m`; this is the **Dirichlet**
  propagator of a window, a different matrix — `GreenDomainMonotone`'s header records that nothing
  in the estate's field chain uses it;
* there the **domain** grows; here the domain is **fixed** and the **ambient box** grows;
* there the family is expected to increase to its limit; here it **decreases**;
* and **the limit is not identified.** `⨅` is a definition, not a name for anything. No `ℤ^d`
  propagator `G` is defined in this estate, and this file defines none.

**The content is the antitonicity, not the convergence.** `tendsto_greenDirichlet_box` is
`tendsto_atTop_ciInf` applied to `greenDirichlet_box_antitone` and the non-negativity of a
positive-definite matrix's diagonal. What took proving is that the boxes nest as graphs and that
the Dirichlet operator grows with the ambient graph.

## What this is NOT

**No measure is built, `OS4` does not move, no spectral gap is claimed, and no published tag or
website page moves.** Nothing here is about `gaussianField`, whose covariance is the free
propagator of the graph itself.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace GreenAmbientMonotone

open Matrix GraphLaplacian GreenDomainMonotone BoxGraph
open scoped MatrixOrder

variable {V W W' : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable [Fintype W'] [DecidableEq W']

/-! ## 1. A principal submatrix is order-preserving -/

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
/-- Cutting to a subdomain preserves the Loewner order. -/
theorem submatrix_le_submatrix {A B : Matrix V V ℝ} (h : A ≤ B) (e : W → V) :
    A.submatrix e e ≤ B.submatrix e e := by
  have hsub : B.submatrix e e - A.submatrix e e = (B - A).submatrix e e := by
    ext i j
    simp
  rw [Matrix.le_iff, hsub]
  exact (Matrix.le_iff.mp h).submatrix e

/-! ## 2. Growing the ambient graph -/

/-- **THE DIRICHLET OPERATOR OF A SUBGRAPH SITS BELOW THE AMBIENT ONE'S PRINCIPAL SUBMATRIX**,
for any graph `J` whose adjacency is the ambient adjacency read through `e`. This is
`GreenDomainMonotone.massive_comap_le_submatrix` with `K.comap e` replaced by the property that
characterises it, which is what lets the conclusion be stated about a graph the estate already
has rather than about a `comap` of one. -/
theorem massive_le_submatrix_of_adj_iff {J : SimpleGraph W} [DecidableRel J.Adj]
    (K : SimpleGraph V) [DecidableRel K.Adj] {e : W → V} (he : Function.Injective e)
    (hJ : ∀ a b, J.Adj a b ↔ K.Adj (e a) (e b)) (m : ℝ) :
    massive J m ≤ (massive K m).submatrix e e := by
  have hdeg : ∀ w : W, J.degree w ≤ K.degree (e w) := by
    intro w
    classical
    rw [SimpleGraph.degree, SimpleGraph.degree]
    refine Finset.card_le_card_of_injOn e (fun w' hw' => ?_) he.injOn
    simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw' ⊢
    exact (hJ w w').mp hw'
  have hdiff : (massive K m).submatrix e e - massive J m
      = Matrix.diagonal (fun w => (K.degree (e w) : ℝ) - (J.degree w : ℝ)) := by
    ext a b
    rw [Matrix.sub_apply, Matrix.submatrix_apply, massive_apply, massive_apply,
      Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab, he.ne hab, hJ a b]
  rw [Matrix.le_iff, hdiff]
  refine Matrix.posSemidef_diagonal_iff.mpr fun w => ?_
  rw [sub_nonneg, Nat.cast_le]
  exact hdeg w

/-- The `comap` case, so the generalisation is instantiated at the statement it generalises. -/
example (K : SimpleGraph V) [DecidableRel K.Adj] {e : W → V} (he : Function.Injective e) (m : ℝ) :
    massive (K.comap e) m ≤ (massive K m).submatrix e e :=
  massive_le_submatrix_of_adj_iff K he (fun _ _ => Iff.rfl) m

/-- **GROWING THE AMBIENT GRAPH LOWERS THE DIRICHLET PROPAGATOR.** The window `W` is placed in the
intermediate graph `J` by `e₁` and `J` sits inside `K` by `e₂`; computing the Dirichlet propagator
of the window in the LARGER graph gives the SMALLER matrix, because the larger graph gives the
window's sites more neighbours to be killed at. -/
theorem greenDirichlet_le_of_adj_iff {J : SimpleGraph W'} [DecidableRel J.Adj]
    (K : SimpleGraph V) [DecidableRel K.Adj] {e₁ : W → W'} {e₂ : W' → V}
    (he₁ : Function.Injective e₁) (he₂ : Function.Injective e₂)
    (hJ : ∀ a b, J.Adj a b ↔ K.Adj (e₂ a) (e₂ b)) {m : ℝ} (hm : m ≠ 0) :
    greenDirichlet K m (e₂ ∘ e₁) ≤ greenDirichlet J m e₁ := by
  have hle : (massive J m).submatrix e₁ e₁
      ≤ (massive K m).submatrix (e₂ ∘ e₁) (e₂ ∘ e₁) := by
    have h := submatrix_le_submatrix (massive_le_submatrix_of_adj_iff K he₂ hJ m) e₁
    rwa [Matrix.submatrix_submatrix] at h
  exact MatrixLoewner.posDef_inv_le_inv (posDef_submatrix he₁ (massive_posDef J hm)) hle

/-! ## 3. The box, where the ambient graph is the one that grows -/

section Box

variable (d : ℕ) {m : ℝ}

/-- The inclusion of a smaller box into a larger one, coordinatewise. -/
def siteIncl {n N : ℕ} (h : n ≤ N) (p : Site d n) : Site d N := fun i => (p i).castLE h

theorem siteIncl_injective {n N : ℕ} (h : n ≤ N) : Function.Injective (siteIncl d h) := by
  intro p q hpq
  funext i
  have hi := congrFun hpq i
  exact Fin.ext (by simpa [siteIncl] using congrArg Fin.val hi)

theorem siteIncl_comp {n N M : ℕ} (h₁ : n ≤ N) (h₂ : N ≤ M) :
    siteIncl d h₂ ∘ siteIncl d h₁ = siteIncl d (h₁.trans h₂) := rfl

/-- **THE BIG BOX'S ADJACENCY, READ THROUGH THE INCLUSION, IS THE SMALL BOX'S.** -/
theorem boxGraph_adj_incl {n N : ℕ} (h : n ≤ N) (p q : Site d n) :
    (boxGraph d N).Adj (siteIncl d h p) (siteIncl d h q) ↔ (boxGraph d n).Adj p q := by
  simp only [boxGraph_adj, BoxGraph.adj, siteIncl, Fin.val_castLE]
  constructor
  · rintro ⟨i, h1, h2⟩
    exact ⟨i, fun j hj => Fin.ext (by simpa using congrArg Fin.val (h1 j hj)), h2⟩
  · rintro ⟨i, h1, h2⟩
    exact ⟨i, fun j hj => by rw [h1 j hj], h2⟩

/-- **SO THE INDUCED SUBGRAPH OF THE BIG BOX ON THE SMALL BOX IS THE SMALL BOX** — not merely a
graph on the right vertex set, but the estate's own `boxGraph`. -/
theorem comap_boxGraph {n N : ℕ} (h : n ≤ N) :
    (boxGraph d N).comap (siteIncl d h) = boxGraph d n := by
  ext p q
  exact boxGraph_adj_incl d h p q

/-- **THE DIRICHLET PROPAGATOR ON A FIXED WINDOW IS ANTITONE IN THE AMBIENT BOX.** -/
theorem greenDirichlet_box_antitone {n N M : ℕ} (h₁ : n ≤ N) (h₂ : N ≤ M) (hm : m ≠ 0) :
    greenDirichlet (boxGraph d M) m (siteIncl d (h₁.trans h₂))
      ≤ greenDirichlet (boxGraph d N) m (siteIncl d h₁) := by
  have h := greenDirichlet_le_of_adj_iff (boxGraph d M) (siteIncl_injective d h₁)
    (siteIncl_injective d h₂) (fun a b => (boxGraph_adj_incl d h₂ a b).symm) hm
  rwa [siteIncl_comp] at h

/-- Every diagonal entry of a Dirichlet propagator is non-negative. -/
theorem greenDirichlet_diag_nonneg {n N : ℕ} (h : n ≤ N) (hm : m ≠ 0) (p : Site d n) :
    0 ≤ greenDirichlet (boxGraph d N) m (siteIncl d h) p p :=
  (greenDirichlet_posDef _ (siteIncl_injective d h) hm).posSemidef.diag_nonneg

/-- **A SEQUENCE OF GREEN FUNCTIONS THAT CONVERGES.** -/
theorem tendsto_greenDirichlet_box (n : ℕ) (hm : m ≠ 0) (p : Site d n) :
    Filter.Tendsto
      (fun k => greenDirichlet (boxGraph d (n + k)) m (siteIncl d (Nat.le_add_right n k)) p p)
      Filter.atTop
      (nhds (⨅ k, greenDirichlet (boxGraph d (n + k)) m
        (siteIncl d (Nat.le_add_right n k)) p p)) := by
  refine tendsto_atTop_ciInf (fun k k' hkk => ?_) ⟨0, ?_⟩
  · exact diag_le_of_le (greenDirichlet_box_antitone d (Nat.le_add_right n k)
      (Nat.add_le_add_left hkk n) hm) p
  · rintro _ ⟨k, rfl⟩
    exact greenDirichlet_diag_nonneg d _ hm p

end Box

end GreenAmbientMonotone
