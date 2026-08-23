/-
  IsingSlabGriffiths.lean — the bridge: the slab IS an Ising model on space-time, so Griffiths
  applies to it.

  WHY. `IsingGriffiths` proved Griffiths' first inequality for an arbitrary finite Ising model and
  named what stood between it and this estate's slab, in two steps and with the word *unprobed*:
  reindex `Fin (M+1) → Cross V` as `(Fin (M+1) × V) → Bool`, and exhibit `β · energyG` as a sum of
  interaction terms with non-negative couplings. **Both are done here.**

  WHAT THE SLAB'S ENERGY IS, WRITTEN OUT. Three families of interaction terms on the site set
  `Fin (M+1) × V`:

  * the intra energy, one term per slice and per interaction set of the cross-section, on
    `{j} ×ˢ B k`, with coupling `β · c k`;
  * the field, one term per site, on `{(j, v)}`, with coupling `β · h`;
  * the bond along the length, one term per site, on `{(j, v), (j+1, v)}`, with coupling `β`.

  **AND THE THIRD FAMILY IS WHY `1 ≤ M` APPEARS.** In `Fin (M+1)` the successor of `j` is `j` again
  when `M = 0`, so the bond degenerates to `spin²` — which is `1`, not a product over a two-element
  set. A slab one slice long has no bonds along its length, and the hypothesis says so rather than
  hiding it. At `M = 1` the two slices are joined twice, which Griffiths does not mind: two terms on
  one set are two terms.

  WHAT IS PROVED. **`expectG_nonneg`** — for a ferromagnetic intra energy (`0 ≤ c k`), a
  non-negative field and `0 ≤ β`, the Gibbs expectation of a spin in the slab is **non-negative**,
  at every cross-section, every site and every length `≥ 2` slices.

  WHAT THIS IS NOT, AND IT IS THE ITEM'S ACTUAL QUESTION. `≥ 0` is not `> 0`. Griffiths' first
  inequality gives non-negativity and nothing more; the watchlist item asks whether the
  magnetisation **fails to vanish**. **The route to strictness is visible and is not taken here**:
  in the expansion the term for `T = {the field term at the observed site}` should have coefficient
  `sinh (β h) · ∏ cosh > 0` and configuration sum `2 ^ |sites|` — the multiplicity at the observed
  site being `1 + 1` and `0` everywhere else — so a single term would already be strictly positive.
  **That arithmetic is by hand and not in Lean**, and extracting one term from a sum of non-negative
  terms needs it identified inside the `Finset.prod_add` expansion, which **has not been
  attempted** (`ERRATUM 204`: a route recorded as a route).

  A SECOND THING NOT DONE: `intraOf` is the intra energy as a PARAMETER in Griffiths shape. That the
  estate's own `slabIntra` is of that shape — nearest-neighbour pairs inside a cross-section, each
  with coupling `1` — is a separate check and is not made here.

  ADDENDUM 2026-08-23 — BOTH "NOT DONE" PARAGRAPHS ABOVE ARE NOW DONE, AND ARE KEPT (`ERRATUM 94`),
  corrected here where the claims were made and not only where the news was announced
  (`ERRATUM 226`).

  * *"That arithmetic is by hand and not in Lean … has not been attempted."* It was attempted the
    same day and the route above was right in every particular. `IsingGriffiths.griffiths_pos` is
    the strict inequality, and `IsingSlabStrict.expectG_pos` carries it across this file's own
    transport: **for `0 < β` and `0 < h`, the slab magnetisation is strictly positive.** The single
    obstacle was that the expansion lived as a `have` inside `griffiths_nonneg` and could not be
    referred to; hoisting it to `IsingGriffiths.boltzmann_expansion` made the strict half three
    lines. Nothing about the estimate above turned out to be wrong — only the assumption that it
    would be expensive.
  * *"That the estate's own `slabIntra` is of that shape … is a separate check and is not made
    here."* It is made, in `IsingSlabFerro.slabIntraAniso_eq_intraOf`.

  `expectG_nonneg` below is NOT superseded: it holds at `β = 0` and `h = 0`, where the strict
  statement is false — `IsingSlabStrict.expectG_slab_eq_zero_of_no_field` proves the magnetisation
  is exactly `0` at zero field. The two are the right statements for their own hypotheses.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingGriffiths
import IsingFieldFactorises

namespace IsingSlabGriffiths

open Finset Real
open IsingTransfer2D IsingSlabTransfer IsingSlabConfig IsingSlabField IsingGriffiths

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {K : Type*} [Fintype K]

/-! ## 1. The intra energy, in Griffiths shape -/

/-- An intra-cross-section energy given by interaction sets `B k` with couplings `c k`. -/
def intraOf (c : K → ℝ) (B : K → Finset V) (σ : Cross V) : ℝ :=
  ∑ k : K, c k * ∏ v ∈ B k, spin (σ v)

/-! ## 2. Space-time as a site set -/

/-- A path of cross-sections is a configuration on space-time. -/
def pathEquiv (M : ℕ) (V : Type*) :
    (Fin (M + 1) → Cross V) ≃ ((Fin (M + 1) × V) → Bool) :=
  (Equiv.curry (Fin (M + 1)) V Bool).symm

omit [Fintype V] [DecidableEq V] [Fintype K] in
@[simp] theorem pathEquiv_apply (M : ℕ) (s : Fin (M + 1) → Cross V) (j : Fin (M + 1)) (v : V) :
    pathEquiv M V s (j, v) = s j v := rfl

/-- The three families of interaction terms. -/
abbrev Idx (M : ℕ) (V K : Type*) :=
  (Fin (M + 1) × K) ⊕ (Fin (M + 1) × V) ⊕ (Fin (M + 1) × V)

/-- Their sites. -/
def sset (M : ℕ) (B : K → Finset V) : Idx M V K → Finset (Fin (M + 1) × V)
  | Sum.inl (j, k) => {j} ×ˢ B k
  | Sum.inr (Sum.inl (j, v)) => {(j, v)}
  | Sum.inr (Sum.inr (j, v)) => {(j, v), (j + 1, v)}

/-- Their couplings. **All non-negative exactly when `β`, `h` and the `c k` are.** -/
def coup (M : ℕ) (β h : ℝ) (c : K → ℝ) : Idx M V K → ℝ
  | Sum.inl (_, k) => β * c k
  | Sum.inr (Sum.inl _) => β * h
  | Sum.inr (Sum.inr _) => β

omit [Fintype V] [DecidableEq V] [Fintype K] in
theorem coup_nonneg {M : ℕ} {β h : ℝ} {c : K → ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hc : ∀ k, 0 ≤ c k) : ∀ i : Idx M V K, 0 ≤ coup M β h c i := by
  rintro (⟨j, k⟩ | ⟨j, v⟩ | ⟨j, v⟩)
  · exact mul_nonneg hβ (hc k)
  · exact mul_nonneg hβ hh
  · exact hβ

/-! ## 3. The energy, term by term -/

omit [Fintype V] [Fintype K] in
theorem prod_sset_inl (M : ℕ) (B : K → Finset V) (j : Fin (M + 1)) (k : K)
    (τ : (Fin (M + 1) × V) → Bool) :
    ∏ w ∈ sset M B (Sum.inl (j, k)), spin (τ w) = ∏ v ∈ B k, spin (τ (j, v)) := by
  rw [sset, Finset.prod_product, Finset.prod_singleton]

omit [Fintype V] [Fintype K] in
theorem prod_sset_field (M : ℕ) (B : K → Finset V) (j : Fin (M + 1)) (v : V)
    (τ : (Fin (M + 1) × V) → Bool) :
    ∏ w ∈ sset M B (Sum.inr (Sum.inl (j, v))), spin (τ w) = spin (τ (j, v)) := by
  rw [sset, Finset.prod_singleton]

omit [Fintype V] [Fintype K] in
theorem prod_sset_bond {M : ℕ} (hM : 1 ≤ M) (B : K → Finset V) (j : Fin (M + 1)) (v : V)
    (τ : (Fin (M + 1) × V) → Bool) :
    ∏ w ∈ sset M B (Sum.inr (Sum.inr (j, v))), spin (τ w)
      = spin (τ (j, v)) * spin (τ (j + 1, v)) := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hne : ((j, v) : Fin (m + 1 + 1) × V) ≠ (j + 1, v) := by
    intro hcon
    have hj : j = j + 1 := congrArg Prod.fst hcon
    have hj0 : j + 0 = j + 1 := by simp only [add_zero]; exact hj
    have h1 : (0 : Fin (m + 2)) = 1 := add_left_cancel hj0
    simpa using congrArg Fin.val h1
  rw [sset, Finset.prod_pair hne]

/-- **THE SLAB'S ENERGY IS AN ISING ENERGY ON SPACE-TIME.** -/
theorem energy_eq {M : ℕ} (hM : 1 ≤ M) (β h : ℝ) (c : K → ℝ) (B : K → Finset V)
    (s : Fin (M + 1) → Cross V) :
    ∑ i : Idx M V K, coup M β h c i * ∏ w ∈ sset M B i, spin (pathEquiv M V s w)
      = β * energyG (fun σ => intraOf c B σ + fieldE h σ) M s := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  simp only [coup, prod_sset_inl, prod_sset_field, prod_sset_bond hM, pathEquiv_apply]
  have h1 : ∀ j : Fin (M + 1), ∑ k : K, β * c k * ∏ v ∈ B k, spin (s j v)
      = β * intraOf c B (s j) := by
    intro j
    rw [intraOf, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h2 : ∀ j : Fin (M + 1), ∑ v : V, β * h * spin (s j v) = β * fieldE h (s j) := by
    intro j
    rw [fieldE, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have h3 : ∀ j : Fin (M + 1), ∑ v : V, β * (spin (s j v) * spin (s (j + 1) v))
      = β * interG (s j) (s (j + 1)) := by
    intro j
    rw [interG, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_congr rfl fun j _ => h2 j,
    Finset.sum_congr rfl fun j _ => h3 j, energyG, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ## 4. Griffiths, applied -/

/-- **THE SLAB MAGNETISATION IS NON-NEGATIVE**, for a ferromagnetic intra energy, a non-negative
field and a non-negative inverse temperature, at every cross-section, every site and every length of
at least two slices. -/
theorem expectG_nonneg {M : ℕ} (hM : 1 ≤ M) {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h)
    {c : K → ℝ} (hc : ∀ k, 0 ≤ c k) (B : K → Finset V) (v₀ : V) :
    0 ≤ expectG β (fun σ => intraOf c B σ + fieldE h σ) M (fun σ => spin (σ v₀)) := by
  rw [expectG]
  refine div_nonneg ?_ ?_
  · have hg := griffiths_site_nonneg (V := Fin (M + 1) × V) (I := Idx M V K)
      (sset M B) (coup M β h c) (coup_nonneg hβ hh hc) ((0 : Fin (M + 1)), v₀)
    have htr := Fintype.sum_equiv (pathEquiv M V)
      (fun s : Fin (M + 1) → Cross V => spin (s 0 v₀)
        * exp (β * energyG (fun σ => intraOf c B σ + fieldE h σ) M s))
      (fun τ : (Fin (M + 1) × V) → Bool => spin (τ ((0 : Fin (M + 1)), v₀))
        * exp (∑ i : Idx M V K, coup M β h c i * ∏ w ∈ sset M B i, spin (τ w)))
      (fun s => by dsimp only [pathEquiv_apply]; rw [energy_eq hM β h c B s])
    rw [htr]
    exact hg
  · rw [partitionG]
    exact Finset.sum_nonneg fun s _ => (exp_pos _).le

end

end IsingSlabGriffiths
