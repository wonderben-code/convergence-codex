import BoxProdAdjSpectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Pi

/-!
# Pointwise products of independent families are independent

`BoxAdjSpectrum` exhibits `n^d` explicit eigenvectors of the `d`-dimensional box's adjacency matrix
and fences on the one thing that would make them the **whole** spectrum: their independence. That
file also records why the cheap route is closed — `PathAdjBasis` got independence for free from
`Module.End.eigenvectors_linearIndependent'` **because the path's eigenvalues are distinct**, and
in two or more dimensions they are not: `(1, 2)` and `(2, 1)` give the same sum of cosines. So
independence has to come from the product structure instead, and this file supplies it.

> **`prodVec_linearIndependent`** — if `b : ι → (α → ℝ)` and `c : κ → (β → ℝ)` are each linearly
> independent, then the `|ι| · |κ|` pointwise products `(a, y) ↦ bᵢ(a)·c_j(y)` are linearly
> independent in `α × β → ℝ`.
>
> **`linearIndependent_comp_equiv`** — and relabelling the **domain** by an equivalence preserves
> independence, which is how a family on `α × β` is carried to one on a type merely equivalent to
> it.
>
> **`prodBasis`** — hence two bases of `α → ℝ` and `β → ℝ` give a basis of `α × β → ℝ`.

## The argument, and why it is not a tensor-product argument

Two nested applications of `Fintype.linearIndependent_iff`. Suppose `∑_{i,j} g(i,j)·bᵢ⊗c_j = 0`.
Evaluate at a **fixed** first coordinate `x` and read what is left as a relation among the `c_j`
with coefficients `∑ᵢ g(i,j)·bᵢ(x)`; independence of `c` kills each of those, and then — with `x`
now free again — independence of `b` kills each `g(i,j)`. Nothing is tensored: `α × β → ℝ` is
handled directly as a function type, which is what the estate's objects are.

**Mathlib has `Module.Basis.tensorProduct`** — a basis of `M ⊗ N` indexed by `ι × κ` — and it is
not this. Using it here would mean transporting along `(α → ℝ) ⊗ (β → ℝ) ≃ (α × β → ℝ)`, which is
a theorem about finite-dimensional tensor products rather than the two-line evaluation argument
above. **`Module.Basis.prod` is also not this**: its index type is the **sum** `ι ⊕ ι'`, because it
is a basis of the direct sum `M × M'` — checked at `Module.Basis.prod_repr_inl`.

Probed against the pinned dump on 31 August 2026, and the count is reported rather than a bare
*"nothing"* (`ERRATUM 42`, `ERRATUM 378`): **51** names pair `linearIndependent` with `prod`, `mul`
or `tensor`, and **not one is the pointwise product of two families on function types** — they are
`LinearDisjoint` multiplication maps, `tmul` over flat modules, Nöbeling's *good products*, and
scalar multiplication. `prodBasis` and `basisPiProd`: **0 names each**.

## What this is NOT

**No graph, no spectrum, and no box.** This is linear algebra over `ℝ`; the only thing it borrows
from the estate is the name `BoxProdAdjSpectrum.prodVec`, reused rather than redefined. Applying it
to `BoxAdjSpectrum.boxVec` needs an induction on the dimension, which is **not done here** and for
which no cost is offered (`ERRATUM 194`, `ERRATUM 246`).

**It is stated over `ℝ` and not over a general field.** Nothing in the argument uses more than a
division ring, and the restriction is to match the estate's other spectral files rather than
because a general version is hard; as of 31 Aug 2026 no general version is written here.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace ProdVecIndependent

open Finset BoxProdAdjSpectrum

variable {ι κ α β : Type*}

/-! ## 1. The evaluation form of a vanishing combination -/

/-- A vanishing linear combination of pointwise products, read at one point. -/
theorem sum_prodVec_apply [Fintype ι] [Fintype κ] {b : ι → (α → ℝ)} {c : κ → (β → ℝ)}
    {g : ι × κ → ℝ}
    (hg : ∑ p : ι × κ, g p • prodVec (b p.1) (c p.2) = 0) (x : α) (y : β) :
    ∑ j : κ, (∑ i : ι, g (i, j) * b i x) * c j y = 0 := by
  have h := congrFun hg (x, y)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, prodVec] at h
  rw [Fintype.sum_prod_type] at h
  rw [Finset.sum_comm] at h
  refine h ▸ Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## 2. Independence -/

/-- **THE PRODUCTS OF TWO INDEPENDENT FAMILIES ARE INDEPENDENT.** -/
theorem prodVec_linearIndependent [Finite ι] [Finite κ] {b : ι → (α → ℝ)} {c : κ → (β → ℝ)}
    (hb : LinearIndependent ℝ b) (hc : LinearIndependent ℝ c) :
    LinearIndependent ℝ fun p : ι × κ => prodVec (b p.1) (c p.2) := by
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype κ := Fintype.ofFinite κ
  rw [Fintype.linearIndependent_iff] at hb hc ⊢
  intro g hg
  have hcoeff : ∀ (x : α) (j : κ), ∑ i : ι, g (i, j) * b i x = 0 := by
    intro x j
    refine hc (fun j' => ∑ i : ι, g (i, j') * b i x) ?_ j
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact sum_prodVec_apply hg x y
  rintro ⟨i, j⟩
  refine hb (fun i' => g (i', j)) ?_ i
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  exact hcoeff x j

/-! ## 3. Relabelling the domain -/

/-- **INDEPENDENCE SURVIVES A RELABELLING OF THE DOMAIN.** -/
theorem linearIndependent_comp_equiv {v : ι → (α → ℝ)} (e : β ≃ α)
    (hv : LinearIndependent ℝ v) : LinearIndependent ℝ fun i => v i ∘ e := by
  have h := hv.map' (LinearEquiv.funCongrLeft ℝ ℝ e).toLinearMap
    (LinearEquiv.ker (LinearEquiv.funCongrLeft ℝ ℝ e))
  exact h

/-! ## 4. And so a basis -/

/-- **TWO BASES GIVE A BASIS OF THE PRODUCT**, indexed by the product of the index types. -/
noncomputable def prodBasis [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    [Nonempty ι] [Nonempty κ]
    (B : Module.Basis ι ℝ (α → ℝ)) (C : Module.Basis κ ℝ (β → ℝ)) :
    Module.Basis (ι × κ) ℝ (α × β → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank
    (prodVec_linearIndependent B.linearIndependent C.linearIndependent)
    (by
      have hι : Fintype.card ι = Fintype.card α := by
        simpa using (Module.finrank_eq_card_basis B).symm
      have hκ : Fintype.card κ = Fintype.card β := by
        simpa using (Module.finrank_eq_card_basis C).symm
      simp [Fintype.card_prod, hι, hκ])

end ProdVecIndependent
