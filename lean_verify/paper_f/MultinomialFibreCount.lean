import FibrewiseStabiliser

/-!
# The multinomial coefficient counts the functions with prescribed fibre sizes

`UNLOCK_WATCHLIST`'s multinomial item asks for *the multinomial coefficient counts the arrangements
of a multiset*, and records orbit–stabiliser as the route: the functions with prescribed fibre
sizes are one orbit of `Equiv.Perm ι` acting by precomposition, the stabiliser is a product of
permutation groups on the fibres, and the two cancel against `Nat.multinomial_spec`.
`FibrewiseStabiliser` built the stabiliser. This file is the other two pieces and the conclusion.

> **`exists_perm_comp`** — **transitivity.** Two functions with the same fibre cardinalities differ
> by a permutation of the domain. `Equiv.ofFiberEquiv` glues the per-fibre bijections, which
> `Fintype.equivOfCardEq` supplies, and `Equiv.ofFiberEquiv_map` is the statement that the glued
> permutation matches the fibres up.
>
> **`card_comp_fibre`** — every fibre of `σ ↦ f₀ ∘ σ` has the size of the stabiliser, by
> translation.
>
> **`card_matching_mul_prod`** — hence the number of functions with `f₀`'s fibre sizes, times
> `∏ₐ (mₐ)!`, is `(card ι)!`.
>
> **`card_matching`** — and against `Nat.multinomial_spec`, which says
> `(∏ₐ (mₐ)!) · multinomial = (∑ₐ mₐ)!` with the same right-hand side, the product cancels:
> **the number of such functions is `Nat.multinomial univ m`.**

## What this settles

`Multiset.countPerms` is *defined* in Mathlib as the multinomial coefficient and its docstring says
*"The number of permutations of a given multiset"* — and **nothing in Mathlib proves that
docstring**: its whole API is one recursion and the empty case, and its only consumer uses it as a
coefficient (probed 2026-08-31, `UNLOCK_WATCHLIST`'s item). This file proves the statement that
docstring asserts, in the prescribed-fibre form its intended consumer here wants.

## What this does NOT settle

**The torus orbit count is still not proved, as of 31 August 2026.**
`TorusOrbitCharacterisation.mem_orbit_iff` says the
hyperoctahedral orbits are the fibres of the multiset of mirror pairs, and the general size is
`2^s · d! / (m₁! ⋯ m_r!)`. This supplies the `d! / (m₁! ⋯ m_r!)` factor **as a count of functions**;
transporting it along `mem_orbit_iff` and multiplying by the `2^s` sign choices is a separate step,
not attempted here, and no cost is offered for it (`ERRATUM 194`, `ERRATUM 246`).
-/

namespace MultinomialFibreCount

open Equiv Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-! ## 1. Transitivity -/

omit [DecidableEq ι] [Fintype α] in
/-- **TWO FUNCTIONS WITH THE SAME FIBRE CARDINALITIES DIFFER BY A PERMUTATION.** -/
theorem exists_perm_comp {f g : ι → α}
    (h : ∀ a, Fintype.card {i // f i = a} = Fintype.card {i // g i = a}) :
    ∃ σ : Perm ι, ∀ i, g (σ i) = f i :=
  ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (h c),
    Equiv.ofFiberEquiv_map fun c => Fintype.equivOfCardEq (h c)⟩

/-! ## 2. Every fibre of `σ ↦ f₀ ∘ σ` is a translate of the stabiliser -/

omit [Fintype α] in
/-- The permutations carrying `f₀` to a given `g` are as many as those fixing `f₀`, when there is
one at all: right translation by it is the bijection. -/
theorem card_comp_fibre (f₀ : ι → α) {τ : Perm ι} :
    (univ.filter fun σ : Perm ι => (fun i => f₀ (σ i)) = (fun i => f₀ (τ i))).card
      = (univ.filter fun ρ : Perm ι => ∀ i, f₀ (ρ i) = f₀ i).card := by
  refine Finset.card_nbij' (fun σ => σ * τ⁻¹) (fun ρ => ρ * τ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hσ ⊢
    intro i
    have : f₀ (σ (τ⁻¹ i)) = f₀ (τ (τ⁻¹ i)) := congrFun hσ (τ⁻¹ i)
    simpa using this
  · intro ρ hρ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hρ ⊢
    funext i
    simpa using hρ (τ i)
  · intro σ _; simp
  · intro ρ _; simp

/-! ## 3. The count -/

/-- **THE COUNT, BEFORE THE DIVISION.** -/
theorem card_matching_mul_prod (f₀ : ι → α) :
    (univ.filter fun g : ι → α =>
        ∀ a, Fintype.card {i // g i = a} = Fintype.card {i // f₀ i = a}).card
      * ∏ a : α, Nat.factorial (Fintype.card {i // f₀ i = a})
      = Nat.factorial (Fintype.card ι) := by
  classical
  have hstab : (univ.filter fun ρ : Perm ι => ∀ i, f₀ (ρ i) = f₀ i).card
      = ∏ a : α, Nat.factorial (Fintype.card {i // f₀ i = a}) := by
    rw [← FibrewiseStabiliser.card_stab f₀, Fintype.card_subtype]
  have himg : (univ.image fun σ : Perm ι => fun i => f₀ (σ i))
      = univ.filter fun g : ι → α =>
          ∀ a, Fintype.card {i // g i = a} = Fintype.card {i // f₀ i = a} := by
    ext g
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨σ, -, rfl⟩ a
      exact Fintype.card_congr (Equiv.subtypeEquiv σ fun i => by simp)
    · intro hg
      obtain ⟨σ, hσ⟩ := exists_perm_comp (f := g) (g := f₀) hg
      exact ⟨σ, funext fun i => hσ i⟩
  have hsum := Finset.card_eq_sum_card_fiberwise
    (f := fun σ : Perm ι => fun i => f₀ (σ i))
    (s := (univ : Finset (Perm ι)))
    (t := univ.image fun σ : Perm ι => fun i => f₀ (σ i))
    (fun σ hσ => Finset.mem_image_of_mem _ hσ)
  rw [Finset.card_univ, Fintype.card_perm] at hsum
  have hconst : ∀ g ∈ univ.image fun σ : Perm ι => fun i => f₀ (σ i),
      (univ.filter fun σ : Perm ι => (fun i => f₀ (σ i)) = g).card
        = ∏ a : α, Nat.factorial (Fintype.card {i // f₀ i = a}) := by
    intro g hg
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hg
    rw [← hstab]
    exact card_comp_fibre f₀
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, himg] at hsum
  exact hsum.symm

/-- **THE MULTINOMIAL COEFFICIENT COUNTS THEM.** -/
theorem card_matching (f₀ : ι → α) :
    (univ.filter fun g : ι → α =>
        ∀ a, Fintype.card {i // g i = a} = Fintype.card {i // f₀ i = a}).card
      = Nat.multinomial univ fun a => Fintype.card {i // f₀ i = a} := by
  have hsum : ∑ a : α, Fintype.card {i // f₀ i = a} = Fintype.card ι := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv f₀)
  have hspec := Nat.multinomial_spec (univ : Finset α) fun a => Fintype.card {i // f₀ i = a}
  rw [hsum] at hspec
  have hpos : 0 < ∏ a : α, Nat.factorial (Fintype.card {i // f₀ i = a}) :=
    Finset.prod_pos fun a _ => Nat.factorial_pos _
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [card_matching_mul_prod f₀, ← hspec, Nat.mul_comm]

/-! ## 4. The same thing said about the fibre sizes rather than about a function -/

/-- **THE COUNT, INDEXED BY THE SIZES THEMSELVES.** A consumer holds a size function `m` and some
function realising it, which is the shape `UNLOCK_WATCHLIST`'s multinomial item asks for. -/
theorem card_matching_of_sizes (m : α → ℕ) (f₀ : ι → α)
    (hf₀ : ∀ a, Fintype.card {i // f₀ i = a} = m a) :
    (univ.filter fun g : ι → α => ∀ a, Fintype.card {i // g i = a} = m a).card
      = Nat.multinomial univ m := by
  have hset : (univ.filter fun g : ι → α => ∀ a, Fintype.card {i // g i = a} = m a)
      = univ.filter fun g : ι → α =>
          ∀ a, Fintype.card {i // g i = a} = Fintype.card {i // f₀ i = a} := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hf₀]
  rw [hset, card_matching f₀]
  exact Nat.multinomial_congr fun a _ => hf₀ a

/-!
**WHAT IS STILL MISSING, AND IT IS ONE CONSTRUCTION.** `card_matching_of_sizes` needs an `f₀`
realising `m`. Every `m` with `∑ₐ mₐ = Fintype.card ι` is realised — index `ι` by
`Σ a, Fin (m a)` — but **that construction is not built here**, so the theorem is stated with the
witness as a hypothesis rather than with the sum condition. As of 31 August 2026 nothing in this
estate builds it, and no cost is offered (`ERRATUM 194`, `ERRATUM 246`).
-/

end MultinomialFibreCount
