import SeriesBound

/-!
# Conditioning: the energy injection, inside the `+` class

Everything from `ContourSubtract` onwards has carried the same caveat — the numerator counts
`+`-boundary configurations and the denominator counts all of them, so the ratio is *not* a
conditional probability. The obstruction was structural: `ContourSubtract`'s injection
removes a contour, a contour determines its configuration only up to a global flip, and
nothing said the removal could be done **without leaving the `+` class**. This file removes
the obstruction.

## The map, and why it needs no choice

`CircuitCut` already builds a configuration `τ` whose contour is exactly the circuit's
bonds. The injection is then **pointwise exclusive-or with `τ`**:

* **`contour_xor`** — the contour of `σ ⊕ τ` is the symmetric difference of the two
  contours. One `Bool` case-split per adjacent pair.
* `⊕ τ` is an **involution**, so injectivity is free — no choice function, no picking a
  representative out of a flip-pair.

## Why it stays inside the `+` class

`σ ⊕ τ` is `+` on the boundary exactly when `τ` is `false` there, and
**`tau_boundary_false`** says it is. `τ p` is the crossing parity of the leftward ray from
`p`, so:

* on the **left** edge the ray is empty;
* on the **bottom** and **top** edges the ray runs along an outer row of the box, whose
  bonds join two boundary sites and are never broken under `+` boundary conditions;
* on the **right** edge the ray runs the **whole** row, and its parity is even by
  `RowParity.even_row`.

The right edge is the one with content: nothing local makes that ray even. What makes it
even is that a circuit meets every horizontal line an even number of times — proved five
units ago, for the enclosure step, and reused here for a different purpose.

## What this gives, and what it does not

**`gibbs_plus_bound`** — the energy estimate with `+`-boundary configurations on **both**
sides. That is the conditioning step, and it is the whole of this file's content.

**It is not yet the conditional Peierls bound.** That needs the union bound of
`PeierlsUnion` re-run against `+`-boundary denominators — the same fibrewise argument with
this theorem in place of `ContourSubtract.gibbs_bound_of_subset`, plus positivity of the
`+`-boundary partition function. **Not done here.**

And `IsingBoundaryField.MagnetisationBound` remains further off still: it is stated for the
boundary-**field** measure over **all** configurations, and three things beyond conditioning
separate the two — the `h → 0⁺` limit, all sites rather than interior sites, and the passage
to `∫ magnetisation`. Untouched.
-/

namespace PlusCondition

open IsingFiniteVolume IsingContourEnergy IsingContourSeparation IsingContourClosed
open IsingContourPlaquette IsingBoundaryField IsingContourInvariant
open DualObstruction PlaquetteLattice DualGraph DualBonds RowParity RayWalk CircuitCut
open SimpleGraph

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. Exclusive-or of configurations, and its contour -/

/-- Pointwise exclusive-or of two configurations. -/
def xorC (σ τ : Config n) : Config n := fun p => xor (σ p) (τ p)

theorem xorC_involutive (τ : Config n) : Function.Involutive (fun σ : Config n => xorC σ τ) := by
  intro σ
  funext p
  simp [xorC]

/-- **The contour of an exclusive-or is the symmetric difference of the contours.** -/
theorem contour_xor (σ τ : Config n) :
    contour (xorC σ τ) = (contour σ ∪ contour τ) \ (contour σ ∩ contour τ) := by
  ext e
  induction e using Sym2.ind with
  | _ p q =>
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, mem_contour, xorC]
    constructor
    · rintro ⟨hadj, hne⟩
      refine ⟨?_, ?_⟩
      · by_cases h1 : σ p = σ q
        · exact Or.inr ⟨hadj, fun h2 => hne (by rw [h1, h2])⟩
        · exact Or.inl ⟨hadj, h1⟩
      · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
        exact hne (by cases hp : σ p <;> cases hq : σ q <;> simp_all)
    · rintro ⟨hor, hnand⟩
      have hadj : adj p q := by rcases hor with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h
      refine ⟨hadj, ?_⟩
      cases hp : σ p <;> cases hq : σ q <;> cases hp' : τ p <;> cases hq' : τ q <;> simp_all

/-- When one contour sits inside the other, the symmetric difference is the difference. -/
theorem contour_xor_of_subset {σ τ : Config n} (h : contour τ ⊆ contour σ) :
    contour (xorC σ τ) = contour σ \ contour τ := by
  rw [contour_xor, Finset.union_eq_left.mpr h, Finset.inter_eq_right.mpr h]

/-! ## 2. The cut configuration is `false` on the boundary

Four edges. Three are "the ray never meets a broken bond"; the fourth is `even_row`. -/

theorem sideU_notMem_bonds {σ : Config n} (hσ : PlusBoundary σ) (H : SimpleGraph (Plaq n))
    {P : Plaq n} (h : P.j + 2 = n) : sideU P ∉ bonds σ H :=
  fun hc => sideU_notMem_contour hσ P h (bonds_subset σ H hc)

/-- Left edge: the ray from column zero is the empty walk. -/
theorem crossings_col_zero (γ : Finset (Sym2 (Site n))) (b : Fin n) {k : ℕ} (hk : k < n)
    (h : k = 0) : crossings γ (leftRay b k hk) = 0 := by
  subst h
  rfl

/-- Bottom edge: every bond of row zero joins two boundary sites. -/
theorem crossings_row_zero {σ : Config n} (hσ : PlusBoundary σ) (H : SimpleGraph (Plaq n))
    (b : Fin n) (hb : b.val = 0) (hj : b.val + 1 < n) (k : ℕ) (hk : k < n) :
    crossings (bonds σ H) (leftRay b k hk) = 0 := by
  rw [crossings_ray_eq_cntD σ H b hj k hk]
  exact Finset.sum_eq_zero fun m _ => if_neg (sideD_notMem_bonds hσ H hb)

/-- Top edge: every bond of the topmost row joins two boundary sites. -/
theorem crossings_row_top {σ : Config n} (hσ : PlusBoundary σ) (H : SimpleGraph (Plaq n))
    (b : Fin n) (hj : b.val + 1 < n) (htop : b.val + 2 = n) (k : ℕ) (hk : k < n) :
    crossings (bonds σ H) (leftRay (⟨b.val + 1, by omega⟩ : Fin n) k hk) = 0 := by
  rw [crossings_ray_succ_eq_cntU σ H b hj k hk]
  exact Finset.sum_eq_zero fun m _ => if_neg (sideU_notMem_bonds hσ H htop)

/-- Right edge: the ray runs the whole row, and `RowParity.even_row` says that is even. -/
theorem even_crossings_col_top {σ : Config n} (hσ : PlusBoundary σ)
    {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) (b : Fin n)
    (hj : b.val + 1 < n) {k : ℕ} (hk : k < n) (hr : k + 1 = n) :
    Even (crossings (bonds σ H) (leftRay b k hk)) := by
  rw [crossings_ray_eq_cntD σ H b hj k hk, show k = n - 1 from by omega]
  exact Nat.even_iff.mpr (even_row hσ hle hcyc b.val hj)

/-- **The cut configuration is `false` at every boundary site.** -/
theorem tau_boundary_false {σ : Config n} (hσ : PlusBoundary σ) {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) {p : Site n}
    (hp : isBoundary p = true) : tau σ H p = false := by
  classical
  have hp1 := p.1.isLt
  have hp2 := p.2.isLt
  simp only [isBoundary, decide_eq_true_eq] at hp
  have key : Even (crossings (bonds σ H) (leftRay p.2 p.1.val p.1.isLt)) := by
    by_cases h0 : p.1.val = 0
    · rw [crossings_col_zero _ _ _ h0]
      exact ⟨0, rfl⟩
    by_cases hb : p.2.val = 0
    · rw [crossings_row_zero hσ H p.2 hb (by omega) _ p.1.isLt]
      exact ⟨0, rfl⟩
    by_cases htop : p.2.val + 1 = n
    · -- top edge: read `p.2` as one row above `n - 2`
      have hb2 : (p.2 : Fin n) = ⟨(n - 2) + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [hb2, crossings_row_top hσ H ⟨n - 2, by omega⟩ (by simp; omega) (by simp; omega)
        _ p.1.isLt]
      exact ⟨0, rfl⟩
    · -- not the left, bottom or top edge, so `isBoundary` leaves the right edge
      exact even_crossings_col_top hσ hle hcyc p.2 (by omega) p.1.isLt (by omega)
  simp only [tau, decide_eq_false_iff_not, not_not]
  exact key

/-! ## 3. So the injection stays in the `+` class -/

theorem plusBoundary_xor {σ' : Config n} (hσ' : PlusBoundary σ') {σ : Config n}
    (hσ : PlusBoundary σ) {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ)
    (hcyc : IsCycleGraph H) : PlusBoundary (xorC σ' (tau σ H)) := by
  intro p hp
  simp only [xorC, hσ' p hp, tau_boundary_false hσ hle hcyc hp]
  rfl

/-- **THE CONDITIONING STEP.** The energy estimate with `+`-boundary configurations on both
sides: the weight of the `+`-boundary configurations whose contour contains a circuit's
bonds is at most `exp (-4β L)` times the weight of **all** `+`-boundary configurations,
where `L` is the number of those bonds.

The injection is exclusive-or with the cut configuration — explicit, involutive, and `+` on
the boundary because the cut configuration is `false` there. -/
theorem gibbs_plus_bound {σ : Config n} (hσ : PlusBoundary σ) {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) (β : ℝ) :
    ∑ σ' ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ' => PlusBoundary σ' ∧ bonds σ H ⊆ contour σ'), Real.exp (-β * isingH n σ') ≤
      Real.exp (-(4 * β) * ((bonds σ H).card : ℝ)) *
        ∑ σ' ∈ (Finset.univ : Finset (Config n)).filter (fun σ' => PlusBoundary σ'),
          Real.exp (-β * isingH n σ') := by
  classical
  set τ : Config n := tau σ H with hτdef
  have hcon : contour τ = bonds σ H := contour_tau hσ hle hcyc
  set A := (Finset.univ : Finset (Config n)).filter
    (fun σ' => PlusBoundary σ' ∧ bonds σ H ⊆ contour σ') with hA
  -- each weight factorises through the removal
  have hfac : ∀ σ' ∈ A, Real.exp (-β * isingH n σ') =
      Real.exp (-(4 * β) * ((bonds σ H).card : ℝ)) *
        Real.exp (-β * isingH n (xorC σ' τ)) := by
    intro σ' hσ'
    obtain ⟨-, -, hsub⟩ := Finset.mem_filter.mp hσ'
    have hsub' : contour τ ⊆ contour σ' := hcon ▸ hsub
    have hcard : ((contour (xorC σ' τ)).card : ℝ) =
        ((contour σ').card : ℝ) - ((bonds σ H).card : ℝ) := by
      rw [contour_xor_of_subset hsub', Finset.card_sdiff, Finset.inter_eq_left.mpr hsub',
        hcon, Nat.cast_sub (Finset.card_le_card hsub)]
    rw [IsingContourGibbs.peierls_weight n β σ', IsingContourGibbs.peierls_weight n β
      (xorC σ' τ), hcard]
    simp only [← Real.exp_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
  -- the map is injective, and lands among the `+`-boundary configurations
  have hinj : ∀ a ∈ A, ∀ b ∈ A, xorC a τ = xorC b τ → a = b := fun a _ b _ hEq => by
    have := congrArg (fun c => xorC c τ) hEq
    simpa [xorC_involutive τ a, xorC_involutive τ b] using this
  rw [← Finset.sum_image (f := fun c : Config n => Real.exp (-β * isingH n c)) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Real.exp_nonneg _
  intro c hc
  obtain ⟨σ', hσ'A, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨-, hplus, -⟩ := Finset.mem_filter.mp hσ'A
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, plusBoundary_xor hplus hσ hle hcyc⟩

end PlusCondition
