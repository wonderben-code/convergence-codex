/-
  IsingSlabFerro.lean — the estate's own slab energy IS of Griffiths shape, so the non-negativity
  is about the slab and not only about a parameter.

  WHY. `IsingSlabGriffiths` left exactly two things: the strictness, and *"that the estate's own
  `slabIntra` is of that shape — nearest-neighbour pairs inside a cross-section, each with coupling
  `1` — is a separate check and is not made here."* **This is that check.**

  WHAT IT COMES TO. `slabIntraAniso Ja Jb` sums, over each site `p` of the cross-section, a
  horizontal bond `Ja · σ_p σ_{p+ê₁}` and a vertical one `Jb · σ_p σ_{p+ê₂}`. Written in Griffiths
  shape that is two interaction terms per site, on the two-element sets `{p, p+ê₁}` and
  `{p, p+ê₂}`, with couplings `Ja` and `Jb`.

  **AND `1 ≤ a`, `1 ≤ b` APPEAR FOR THE SAME REASON THE LENGTH HYPOTHESIS DID.** In `Fin (a+1)` the
  successor of `i` is `i` again when `a = 0`, so a cross-section one site wide has no horizontal
  bond and `{p, p+ê₁}` is a singleton while the term is `spin²`. The one-site-wide slab is not a
  counterexample to anything — it is `IsingFieldFactorises`' uncoupled case, already settled — but
  it is not this theorem, and the hypothesis says so.

  WHAT IS PROVED. **`slabIntraAniso_eq_intraOf`** — the identity — and hence
  **`expectG_slab_nonneg`**: for `0 ≤ β`, `0 ≤ h`, `0 ≤ Ja`, `0 ≤ Jb`, a cross-section at least two
  sites wide in each direction and a slab at least two slices long, **the magnetisation of this
  estate's three-dimensional Ising slab in a non-negative field is non-negative**, at every site.
  (The two width conditions were removed the same day; see the second addendum below.)
  `expectG_slab_nonneg_iso` is the isotropic case, where `slabIntraAniso 1 1` is `slabIntra` by
  `IsingSlabAniso.slabIntraAniso_one_one`.

  WHAT IS STILL NOT PROVED, AND IT IS NOW ONE THING. Strictness. `≥ 0` is not `> 0`, the route is
  the one `IsingSlabGriffiths` records, and nothing here approaches it.

  ADDENDUM 2026-08-23, SECOND — **`1 ≤ a` AND `1 ≤ b` ARE GONE, AND THE PARAGRAPH ABOVE THAT
  DEFENDED THEM CONTAINS A CLAIM THAT IS FALSE** (`ERRATUM 251`). Both are kept (`ERRATUM 94`).

  * The FALSE claim: *"The one-site-wide slab … is `IsingFieldFactorises`' uncoupled case, already
    settled."* **It is not.** At `a = 0` with `b ≥ 1` the VERTICAL bonds are all still there with
    coupling `Jb`, so the model is coupled; and even at `a = b = 0` the energy is `fieldE h` plus
    the constant `Ja + Jb`, which is not `fieldE h` and which `IsingFieldFactorises` says nothing
    about. The sentence was written to justify excluding a case, and excluding a case is exactly
    when a justification goes unchecked.
  * What was true in it: the degenerate geometry is real. At `a = 0` the successor of `i` in
    `Fin 1` is `i`, so the "horizontal bond" is a site paired with itself and its term is
    `Ja · spin² = Ja`, a CONSTANT.
  * **And a constant is Griffiths-shaped**, which is what the exclusion missed. `bondSet` now
    returns `∅` on the degenerate side; `∏` over `∅` is `1`, so the term is the constant `Ja`, with
    coupling `Ja ≥ 0` exactly as before. `prod_bondSet_inl` and `prod_bondSet_inr` handle the case
    instead of assuming it away, and **`slabIntraAniso_eq_intraOf`, `expectG_slab_nonneg` and
    `expectG_slab_nonneg_iso` now hold for EVERY `a` and `b`**, including the one-site
    cross-section. `1 ≤ M` is untouched and is still real: it is about the bond along the LENGTH,
    which has no constant to degenerate into — `energyG` sums it once per slice either way.

  ADDENDUM 2026-08-23 — "WHAT IS STILL NOT PROVED, AND IT IS NOW ONE THING" IS NOW NOTHING, and the
  paragraph is kept (`ERRATUM 94`) and corrected here where the claim was made (`ERRATUM 226`).
  `IsingGriffiths.griffiths_pos` proved the strict inequality abstractly and
  **`IsingSlabStrict.expectG_slab_pos`** carries it to this file's own theorem: for `0 < β` and
  `0 < h`, with the same `1 ≤ M`, `1 ≤ a`, `1 ≤ b`, **the magnetisation of this estate's
  three-dimensional Ising slab in a strictly positive field is STRICTLY POSITIVE.** The route this
  file pointed at was taken unchanged; it cost no new mathematics.

  `expectG_slab_nonneg` below is NOT superseded — it holds at `β = 0` and `h = 0`, where the strict
  statement is false, and `IsingSlabStrict.expectG_slab_eq_zero_of_no_field` proves it false there.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingSlabGriffiths
import IsingSlabAniso

namespace IsingSlabFerro

open Finset Real
open IsingTransfer2D IsingSlabTransfer IsingSlabConfig IsingSlabField IsingSlabAniso
open IsingSlabGriffiths

noncomputable section

variable {a b : ℕ}

/-! ## 1. The cross-section's bonds as interaction sets -/

/-- One horizontal and one vertical bond per site of the cross-section. -/
abbrev BondIdx (a b : ℕ) := (Fin (a + 1) × Fin (b + 1)) ⊕ (Fin (a + 1) × Fin (b + 1))

/-- Their sites. -/
def bondSet (a b : ℕ) : BondIdx a b → Finset (Fin (a + 1) × Fin (b + 1))
  | Sum.inl p => if a = 0 then ∅ else {p, (p.1 + 1, p.2)}
  | Sum.inr p => if b = 0 then ∅ else {p, (p.1, p.2 + 1)}

/-- Their couplings. -/
def bondCoup (a b : ℕ) (Ja Jb : ℝ) : BondIdx a b → ℝ
  | Sum.inl _ => Ja
  | Sum.inr _ => Jb

theorem bondCoup_nonneg {Ja Jb : ℝ} (hJa : 0 ≤ Ja) (hJb : 0 ≤ Jb) :
    ∀ k : BondIdx a b, 0 ≤ bondCoup a b Ja Jb k := by
  rintro (p | p) <;> assumption

theorem prod_bondSet_inl (p : Fin (a + 1) × Fin (b + 1))
    (σ : Cross (Fin (a + 1) × Fin (b + 1))) :
    ∏ v ∈ bondSet a b (Sum.inl p), spin (σ v) = spin (σ p) * spin (σ (p.1 + 1, p.2)) := by
  by_cases ha : a = 0
  · subst ha
    have hz : ∀ x : Fin (0 + 1), x = 0 := fun x => Fin.ext (Nat.lt_one_iff.mp x.isLt)
    have h1 : p.1 + 1 = p.1 := by rw [hz (p.1 + 1), hz p.1]
    rw [bondSet, if_pos rfl, Finset.prod_empty, h1]
    simp [spin_sq]
  · obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
    have hne : p ≠ ((p.1 + 1, p.2) : Fin (m + 1 + 1) × Fin (b + 1)) := by
      intro hcon
      have hj : p.1 = p.1 + 1 := congrArg Prod.fst hcon
      have hj0 : p.1 + 0 = p.1 + 1 := by simp only [add_zero]; exact hj
      have h1 : (0 : Fin (m + 2)) = 1 := add_left_cancel hj0
      simpa using congrArg Fin.val h1
    rw [bondSet, if_neg (Nat.succ_ne_zero m), Finset.prod_pair hne]

theorem prod_bondSet_inr (p : Fin (a + 1) × Fin (b + 1))
    (σ : Cross (Fin (a + 1) × Fin (b + 1))) :
    ∏ v ∈ bondSet a b (Sum.inr p), spin (σ v) = spin (σ p) * spin (σ (p.1, p.2 + 1)) := by
  by_cases hb : b = 0
  · subst hb
    have hz : ∀ x : Fin (0 + 1), x = 0 := fun x => Fin.ext (Nat.lt_one_iff.mp x.isLt)
    have h1 : p.2 + 1 = p.2 := by rw [hz (p.2 + 1), hz p.2]
    rw [bondSet, if_pos rfl, Finset.prod_empty, h1]
    simp [spin_sq]
  · obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
    have hne : p ≠ ((p.1, p.2 + 1) : Fin (a + 1) × Fin (m + 1 + 1)) := by
      intro hcon
      have hj : p.2 = p.2 + 1 := congrArg Prod.snd hcon
      have hj0 : p.2 + 0 = p.2 + 1 := by simp only [add_zero]; exact hj
      have h1 : (0 : Fin (m + 2)) = 1 := add_left_cancel hj0
      simpa using congrArg Fin.val h1
    rw [bondSet, if_neg (Nat.succ_ne_zero m), Finset.prod_pair hne]

/-! ## 2. The identity -/

/-- **THE SLAB'S CROSS-SECTION ENERGY IS OF GRIFFITHS SHAPE.** -/
theorem slabIntraAniso_eq_intraOf (Ja Jb : ℝ)
    (σ : Cross (Fin (a + 1) × Fin (b + 1))) :
    slabIntraAniso Ja Jb σ = intraOf (bondCoup a b Ja Jb) (bondSet a b) σ := by
  rw [intraOf, Fintype.sum_sum_type, slabIntraAniso, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [bondCoup, bondCoup, prod_bondSet_inl p σ, prod_bondSet_inr p σ]

/-! ## 3. The slab's magnetisation -/

/-- **THE MAGNETISATION OF THIS ESTATE'S THREE-DIMENSIONAL ISING SLAB, IN A NON-NEGATIVE FIELD AND
WITH FERROMAGNETIC COUPLINGS, IS NON-NEGATIVE.** -/
theorem expectG_slab_nonneg {M : ℕ} (hM : 1 ≤ M)
    {β h Ja Jb : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) (hJa : 0 ≤ Ja) (hJb : 0 ≤ Jb)
    (v₀ : Fin (a + 1) × Fin (b + 1)) :
    0 ≤ expectG β (fun σ => slabIntraAniso Ja Jb σ + fieldE h σ) M (fun σ => spin (σ v₀)) := by
  have hE : (fun σ : Cross (Fin (a + 1) × Fin (b + 1)) => slabIntraAniso Ja Jb σ + fieldE h σ)
      = fun σ => intraOf (bondCoup a b Ja Jb) (bondSet a b) σ + fieldE h σ := by
    funext σ
    rw [slabIntraAniso_eq_intraOf Ja Jb σ]
  rw [hE]
  exact expectG_nonneg hM hβ hh (bondCoup_nonneg hJa hJb) (bondSet a b) v₀

/-- The isotropic case, where the energy is the estate's own `slabIntra`. -/
theorem expectG_slab_nonneg_iso {M : ℕ} (hM : 1 ≤ M)
    {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) (v₀ : Fin (a + 1) × Fin (b + 1)) :
    0 ≤ expectG β (fun σ => slabIntra σ + fieldE h σ) M (fun σ => spin (σ v₀)) := by
  have hE : (fun σ : Cross (Fin (a + 1) × Fin (b + 1)) => slabIntra σ + fieldE h σ)
      = fun σ => slabIntraAniso 1 1 σ + fieldE h σ := by
    funext σ
    rw [slabIntraAniso_one_one]
  rw [hE]
  exact expectG_slab_nonneg hM hβ hh zero_le_one zero_le_one v₀

end

end IsingSlabFerro
