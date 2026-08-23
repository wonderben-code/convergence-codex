/-
  IsingFieldFactorises.lean — with the sites uncoupled, the magnetisation at ANY cross-section is
  the one-site magnetisation, and so is strictly positive in a field.

  WHY. `IsingFieldPositive` bounded the one-site magnetisation away from zero and said exactly why
  its induction stops there: at one site `spin` separates the only two configurations, so the
  numerator is a difference of two diagonal entries, and at more sites it is a signed sum over
  `2^k`. The watchlist item asks about a cross-section of size **two or more**.

  **THIS SETTLES THE CASE THE ITEM'S OWN PHRASING MAKES LOOK HARDEST FOR THE WRONG REASON.** With
  no intra-cross-section energy — `E = fieldE h`, the field and nothing else — the model is a
  product of one-site chains: the bond term `interG` couples the SAME site at successive slices and
  the field term is a sum over sites, so nothing at all couples two different sites. The
  configuration sum factorises, and **the magnetisation at any site of any cross-section equals the
  one-site magnetisation exactly** — not approximately, not in a limit.

  So the answer to *"does it fail to vanish at a cross-section of size two or more?"* is **yes, when
  the sites are uncoupled**, and the obstruction the item is really about is the intra energy, not
  the size of the cross-section. That is a sharper statement of the open problem than the item had.

  WHAT IS PROVED.

  * `col` and **`colEquiv`** — a configuration path on `Cross V` is exactly a `V`-indexed family of
    one-site paths, as an equivalence;
  * **`energyG_eq_sum_col`** — the energy is the sum of the columns' energies. This is where the
    hypothesis `E = fieldE h` is spent, and it is the only place;
  * **`sum_prod_col`** — the configuration sum of a product over sites factorises
    (`Fintype.prod_sum` through `colEquiv`);
  * **`expectG_eq_one_site`** — the expectation of `spin (· v₀)` on `Cross V` equals the one-site
    expectation, at every `β`, every `h`, every length and every site;
  * **`expectG_field_pos_cross`** — hence strictly positive for `β, h > 0`, at every cross-section.

  WHAT IS STILL OPEN, AND IT IS NOW SAID IN ONE LINE. The item's question with the intra energy
  switched on. Nothing here touches it: `energyG_eq_sum_col` is false the moment `E` couples two
  sites, and every line below rests on it.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingFieldPositive

namespace IsingFieldFactorises

open Finset Real
open IsingTransfer2D IsingSlabTransfer IsingSlabFlip IsingSlabConfig IsingSlabField
open IsingFieldPositive

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. A path is a family of columns -/

/-- The `v`-th column of a configuration path, read as a one-site path. -/
def col (M : ℕ) (s : Fin (M + 1) → Cross V) (v : V) : Fin (M + 1) → Cross (Fin 1) :=
  fun j _ => s j v

/-- **AND THAT READING IS A BIJECTION.** -/
def colEquiv (V : Type*) [Fintype V] [DecidableEq V] (M : ℕ) :
    (Fin (M + 1) → Cross V) ≃ (V → Fin (M + 1) → Cross (Fin 1)) where
  toFun s := col M s
  invFun G := fun j v => G v j 0
  left_inv _ := rfl
  right_inv G := by
    funext v j u
    fin_cases u
    rfl

/-! ## 2. The energy splits, and this is the only place the hypothesis is spent -/

omit [DecidableEq V] in
/-- **THE ENERGY IS THE SUM OF THE COLUMNS' ENERGIES**, when the only site term is the field. The
bond term couples one site to itself at the next slice, and the field term is a sum over sites, so
nothing couples two different sites. -/
theorem energyG_eq_sum_col (h : ℝ) (M : ℕ) (s : Fin (M + 1) → Cross V) :
    energyG (fieldE h) M s = ∑ v : V, energyG (fieldE (V := Fin 1) h) M (col M s v) := by
  have hR : ∀ v : V, energyG (fieldE (V := Fin 1) h) M (col M s v)
      = ∑ j : Fin (M + 1), (h * spin (s j v) + spin (s j v) * spin (s (j + 1) v)) := by
    intro v
    simp [energyG, fieldE, interG, col]
  simp only [hR]
  rw [Finset.sum_comm]
  simp only [energyG, fieldE, interG]
  exact Finset.sum_congr rfl fun j _ => (Finset.sum_add_distrib).symm

/-! ## 3. The configuration sum factorises -/

theorem sum_prod_col (M : ℕ) (F : V → (Fin (M + 1) → Cross (Fin 1)) → ℝ) :
    ∑ s : Fin (M + 1) → Cross V, ∏ v : V, F v (col M s v)
      = ∏ v : V, ∑ t : Fin (M + 1) → Cross (Fin 1), F v t := by
  rw [Fintype.prod_sum]
  exact Fintype.sum_equiv (colEquiv V M) _ _ fun _ => rfl

omit [DecidableEq V] in
/-- The Boltzmann weight of a path is the product of its columns' weights. -/
theorem exp_energyG_eq_prod_col (β h : ℝ) (M : ℕ) (s : Fin (M + 1) → Cross V) :
    exp (β * energyG (fieldE h) M s)
      = ∏ v : V, exp (β * energyG (fieldE (V := Fin 1) h) M (col M s v)) := by
  rw [energyG_eq_sum_col h M s, Finset.mul_sum, Real.exp_sum]

/-! ## 4. The two sums -/

/-- The one-site partition function is positive, which is what the division below needs. -/
theorem partitionG_one_pos (β h : ℝ) (M : ℕ) :
    0 < partitionG β (fieldE (V := Fin 1) h) M := by
  refine Finset.sum_pos (fun t _ => exp_pos _) ?_
  exact Finset.univ_nonempty

theorem partitionG_eq_prod (β h : ℝ) (M : ℕ) :
    partitionG β (fieldE (V := V) h) M
      = ∏ _v : V, partitionG β (fieldE (V := Fin 1) h) M := by
  simp only [partitionG]
  rw [← sum_prod_col M fun _ t => exp (β * energyG (fieldE (V := Fin 1) h) M t)]
  exact Finset.sum_congr rfl fun s _ => exp_energyG_eq_prod_col β h M s

/-- The numerator factorises with one factor replaced. -/
theorem sum_spin_eq_prod (β h : ℝ) (M : ℕ) (v₀ : V) :
    ∑ s : Fin (M + 1) → Cross V, spin (s 0 v₀) * exp (β * energyG (fieldE h) M s)
      = (∑ t : Fin (M + 1) → Cross (Fin 1),
            spin (t 0 0) * exp (β * energyG (fieldE (V := Fin 1) h) M t))
        * ∏ _v ∈ Finset.univ.erase v₀, partitionG β (fieldE (V := Fin 1) h) M := by
  classical
  set g : (Fin (M + 1) → Cross (Fin 1)) → ℝ :=
    fun t => exp (β * energyG (fieldE (V := Fin 1) h) M t) with hgdef
  set F : V → (Fin (M + 1) → Cross (Fin 1)) → ℝ :=
    fun v t => if v = v₀ then spin (t 0 0) * g t else g t with hFdef
  have hFv0 : ∀ t, F v₀ t = spin (t 0 0) * g t := fun t => by simp [hFdef]
  have hFne : ∀ v t, v ≠ v₀ → F v t = g t := fun v t hv => by simp [hFdef, hv]
  have hsplit : ∀ c : V → (Fin (M + 1) → Cross (Fin 1)),
      ∏ v : V, F v (c v) = spin (c v₀ 0 0) * ∏ v : V, g (c v) := by
    intro c
    have hprod : ∏ v ∈ Finset.univ.erase v₀, F v (c v)
        = ∏ v ∈ Finset.univ.erase v₀, g (c v) :=
      Finset.prod_congr rfl fun v hv => hFne v (c v) (Finset.mem_erase.mp hv).1
    rw [← Finset.mul_prod_erase Finset.univ (fun v => F v (c v)) (Finset.mem_univ v₀),
      ← Finset.mul_prod_erase Finset.univ (fun v => g (c v)) (Finset.mem_univ v₀),
      hFv0, hprod, mul_assoc]
  have hlhs : ∀ s : Fin (M + 1) → Cross V,
      spin (s 0 v₀) * exp (β * energyG (fieldE h) M s) = ∏ v : V, F v (col M s v) := by
    intro s
    rw [hsplit (col M s), exp_energyG_eq_prod_col β h M s]
    rfl
  rw [Finset.sum_congr rfl fun s _ => hlhs s, sum_prod_col M F,
    ← Finset.mul_prod_erase Finset.univ (fun v => ∑ t, F v t) (Finset.mem_univ v₀)]
  congr 1
  · exact Finset.sum_congr rfl fun t _ => hFv0 t
  · refine Finset.prod_congr rfl fun v hv => ?_
    rw [partitionG]
    exact Finset.sum_congr rfl fun t _ => hFne v t (Finset.mem_erase.mp hv).1

/-! ## 5. The two statements -/

/-- **THE MAGNETISATION AT ANY SITE OF ANY CROSS-SECTION IS THE ONE-SITE MAGNETISATION**, exactly,
when the only site energy is the field. -/
theorem expectG_eq_one_site (β h : ℝ) (M : ℕ) (v₀ : V) :
    expectG β (fieldE (V := V) h) M (fun σ => spin (σ v₀))
      = expectG β (fieldE (V := Fin 1) h) M (fun σ => spin (σ 0)) := by
  classical
  have hZ : (0 : ℝ) < partitionG β (fieldE (V := Fin 1) h) M := partitionG_one_pos β h M
  have hP : (0 : ℝ) < ∏ _v ∈ Finset.univ.erase v₀, partitionG β (fieldE (V := Fin 1) h) M :=
    Finset.prod_pos fun _ _ => hZ
  rw [expectG, expectG, sum_spin_eq_prod β h M v₀, partitionG_eq_prod (V := V) β h M,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ v₀)]
  rw [mul_div_mul_right _ _ hP.ne']

/-- **AND SO IT IS STRICTLY POSITIVE IN A FIELD, AT EVERY CROSS-SECTION AND EVERY FINITE LENGTH.**
The case the watchlist item asks about, with the intra energy switched off. -/
theorem expectG_field_pos_cross {β h : ℝ} (hβ : 0 < β) (hh : 0 < h) (M : ℕ) (v₀ : V) :
    0 < expectG β (fieldE (V := V) h) M (fun σ => spin (σ v₀)) := by
  rw [expectG_eq_one_site β h M v₀]
  exact expectG_field_pos hβ hh M

end

end IsingFieldFactorises
