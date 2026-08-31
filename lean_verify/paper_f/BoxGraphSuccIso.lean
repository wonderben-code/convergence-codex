import BoxGraphPath
import GraphIsoSpectrum

/-!
# The estate's box IS an iterated box product: `boxGraph (d+1) n ≃g pathGraph n □ boxGraph d n`

`BoxGraphPath` proved that `(boxGraph d n).Adj` is the per-axis `pathGraph` condition, and then
said in its own closing section that it **does not** exhibit the box as an iterated
`SimpleGraph.boxProd` — *"`boxProd` is binary on `α × β` and `Site d n` is a function type; the
transport needs `(Fin (d + 1) → Fin n) ≃ Fin n × (Fin d → Fin n)` and an induction, and is not
done here."* `BoxProdAdjSpectrum` repeated the same sentence, and `GraphIsoSpectrum` was built to
supply the transport's missing prerequisite while recording that **the transport itself was still
not done**. This file does the one step those three files each named.

> **`consSite`** — the equivalence `Fin n × Site d n ≃ Site (d + 1) n`, which is Mathlib's
> `Fin.consEquiv` at the constant family. (`Equiv.piFinSucc` **does not exist** under that name;
> probed against the pinned dump.)
>
> **`adj_cons`** — `boxGraph (d + 1) n` relates `Fin.cons a b` and `Fin.cons c e` exactly when
> either `a` and `c` are `pathGraph`-adjacent with `b = e`, or `b` and `e` are box-adjacent with
> `a = c`. That is `SimpleGraph.boxProd_adj` verbatim.
>
> **`boxGraph_succ_iso`** — hence `pathGraph n □ boxGraph d n ≃g boxGraph (d + 1) n`, as a
> `SimpleGraph.Iso`.

## What this is, exactly

One induction step, not the induction. The isomorphism peels **one** axis: it says the `d + 1`
dimensional box is a path times the `d` dimensional box. Iterating it — to say `boxGraph d n` is
a `d`-fold product of paths in the associated sense — is **not done here**, and neither is any
spectral consequence. What the step buys is that `BoxProdAdjSpectrum.adjMatrix_mulVec_prodVec`
and `GraphIsoSpectrum.mulVec_smul_iso` now have a graph in this estate to act on: composing them
along this isomorphism carries an eigenvector of `pathGraph n □ boxGraph d n` to one of
`boxGraph (d + 1) n`. **That composition is not performed in this file** and no cost is offered
for it (`ERRATUM 194`, `ERRATUM 246`).

## What it does NOT do, and the reason is unchanged

**It is the ADJACENCY matrix.** `UNLOCK_WATCHLIST`'s *a BOX is not a circulant* item is blocked on
the estate's `GraphLaplacian.massive`, which is `D − A + m²` with the **true** degree, and
`PathDegreeBoundary.pathGraph_degree` shows that degree is `1` at the two ends of a path and `2`
inside. An isomorphism of graphs carries the degree function along with it, so this file changes
nothing about that: **the box item does not move**, exactly as `BoxProdAdjSpectrum` already
recorded. Naming the box as a product does not make its degree constant.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BoxGraphSuccIso

open SimpleGraph BoxGraph BoxGraphPath

variable {d n : ℕ}

/-! ## 1. Splitting off the first axis -/

/-- **`Fin n × Site d n ≃ Site (d + 1) n`** — Mathlib's `Fin.consEquiv` at the constant family
`fun _ => Fin n`, where the dependent product `α 0 × ∀ i, α i.succ` is the plain pair. -/
def consSite (d n : ℕ) : Fin n × Site d n ≃ Site (d + 1) n :=
  Fin.consEquiv fun _ : Fin (d + 1) => Fin n

@[simp] theorem consSite_apply (x : Fin n × Site d n) (i : Fin (d + 1)) :
    consSite d n x i = Fin.cons (α := fun _ : Fin (d + 1) => Fin n) x.1 x.2 i := rfl

@[simp] theorem consSite_symm_apply (p : Site (d + 1) n) :
    (consSite d n).symm p = (p 0, Fin.tail p) := rfl

/-! ## 2. The adjacency, split the same way -/

/-- **THE STEP.** Two sites of the `d + 1` dimensional box, written with their first coordinate
split off, are adjacent exactly on `SimpleGraph.boxProd_adj`'s disjunction. -/
theorem adj_cons (a c : Fin n) (b e : Site d n) :
    (boxGraph (d + 1) n).Adj (Fin.cons (α := fun _ : Fin (d + 1) => Fin n) a b)
        (Fin.cons (α := fun _ : Fin (d + 1) => Fin n) c e) ↔
      ((pathGraph n).Adj a c ∧ b = e) ∨ ((boxGraph d n).Adj b e ∧ a = c) := by
  rw [boxGraph_adj_pathGraph]
  constructor
  · rintro ⟨i, hoff, hon⟩
    induction i using Fin.cases with
    | zero =>
        refine Or.inl ⟨by simpa using hon, ?_⟩
        funext j
        have := hoff j.succ (Fin.succ_ne_zero j)
        simpa using this
    | succ i₀ =>
        refine Or.inr ⟨?_, ?_⟩
        · rw [boxGraph_adj_pathGraph]
          refine ⟨i₀, fun j hj => ?_, by simpa using hon⟩
          have := hoff j.succ fun hcon => hj (Fin.succ_injective _ hcon)
          simpa using this
        · have := hoff 0 (Fin.succ_ne_zero i₀).symm
          simpa using this
  · rintro (⟨hac, rfl⟩ | ⟨hbe, rfl⟩)
    · refine ⟨0, fun j hj => ?_, by simpa using hac⟩
      induction j using Fin.cases with
      | zero => exact absurd rfl hj
      | succ j₀ => simp
    · rw [boxGraph_adj_pathGraph] at hbe
      obtain ⟨i₀, hoff, hon⟩ := hbe
      refine ⟨i₀.succ, fun j hj => ?_, by simpa using hon⟩
      induction j using Fin.cases with
      | zero => simp
      | succ j₀ =>
          have := hoff j₀ fun hcon => hj (by rw [hcon])
          simpa using this

/-! ## 3. Hence the isomorphism -/

/-- **THE `d + 1` DIMENSIONAL BOX IS A PATH TIMES THE `d` DIMENSIONAL BOX.** -/
def boxGraph_succ_iso (d n : ℕ) : pathGraph n □ boxGraph d n ≃g boxGraph (d + 1) n where
  toEquiv := consSite d n
  map_rel_iff' := by
    intro x y
    rw [show (consSite d n) x = Fin.cons (α := fun _ : Fin (d + 1) => Fin n) x.1 x.2 from rfl,
      show (consSite d n) y = Fin.cons (α := fun _ : Fin (d + 1) => Fin n) y.1 y.2 from rfl,
      adj_cons, boxProd_adj]

end BoxGraphSuccIso
