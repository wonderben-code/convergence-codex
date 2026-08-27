import PairWeightRep

/-!
# The term a ladder rung carries, and its recursion

`PairingRecursion` closed the pairing side of `WickPairings.IsserlisGeneral`, leaving **one** thing
between it and the theorem: the Gaussian integral obeys no proved recursion at general order. That
is `LatticeSteinTwo`'s ladder, whose rung `k` is

```
T_k(a₁,…,a_k; f) = ∫ ∏ᵢ⟪aᵢ,ω⟫·exp⟪f,ω⟫ dμ,
```

and whose closed form is a sum over the **involutions** of `{1,…,k}` — the pairs contracted with
each other, the fixed points contracted with `f`. `LatticeSteinMajorant` paid the analytic half of
the rung step at every order. This file is the other half's algebra: **the term, and how the sum
of it over `involutions (Option α)` breaks up.**

## Why the fixed points make it a different statement

`PairWeightRep` handled `perfectMatchings`, where there are no fixed points and every index is
paired. An involution has both, and the two behave differently under the split:

* when the new index is **fixed**, it contributes `U none` and the rest is the same sum;
* when it is **paired with `b`**, it contributes `W none (some b)` — and `b` is used up, so the
  surviving involution's fixed-point product must run over `fix g` **without** `b`.

That last clause is why this is not `PairWeightRep` with a factor bolted on. It is also exactly
the shape `Involutions.numInvolutions`'s recurrence has, `I(n+2) = I(n+1) + (n+1)·I(n)`: one term
where the new point is alone, `n+1` where it is paired.

## What is proved

* `steinTerm` — the pair weight over a representative set times the fixed-point weight;
* `steinTerm_repSet_eq` — it does not depend on the representative set, for symmetric `w`;
* `fixedPoints_optionCongr`, `fixedPoints_opt` — where an involution of `Option α` is fixed, in
  the two branches of the split;
* `steinTerm_optionCongr`, `steinTerm_opt` — the two factorisations;
* **`sum_steinTerm_option`** — the recursion;
* `card_involutions_option_of_steinTerm` — the recursion specialised back to
  `Involutions.card_involutions_option`, which it has to reproduce. **That check is weight-blind**:
  at `W = U = 1` every term is `1`, so it sees the SIZES of the two branches and nothing about
  which factor either carries — in particular nothing about the `i ≠ b` clause, the one part of §3
  not forced by the shapes of the types;
* `sum_steinTerm_option_derangement` — **so a second specialisation is here that does see it.** At
  `U ≡ 0` the fixed-point product is `1` exactly on the involutions with no fixed point at all, the
  `U none` branch vanishes, and the identity becomes: *the fixed-point-free involutions of
  `Option α` are counted, for each `b`, by those of `α` whose only fixed point is `b`.* **Drop the
  `i ≠ b` and the right-hand side is identically zero**, because `b` is a fixed point of every `g`
  in that fibre — so this check fails loudly on the one clause the first check cannot see.

**WHAT IS NOT HERE.** No measure, integral, derivative or test function. The rung step needs this
sum **differentiated** in the test function and matched against the integral's derivative, and
neither of those is here. **Not costed** (`ERRATUM 194`).
-/

namespace SteinSumRecursion

open Equiv Function Involutions PairWeightRep

variable {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [CommMonoid M]

/-! ## 1. The term -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The term an involution contributes to a rung: the pair weight over a representative set,
times the fixed-point weight over the points it leaves alone. -/
def steinTerm (w : ι → ι → M) (u : ι → M) (S : Finset ι) (σ : Equiv.Perm ι) : M :=
  (∏ i ∈ S, w i (σ i)) * ∏ i ∈ Finset.univ.filter (fun i => σ i = i), u i

/-- And it does not depend on the representative set, by `PairWeightRep.prod_repSet_eq`. The
fixed-point half never depended on one. -/
theorem steinTerm_repSet_eq {σ : Equiv.Perm ι} (hσ : σ ∈ involutions ι) {w : ι → ι → M}
    (hw : ∀ i j, w i j = w j i) (u : ι → M) {S T : Finset ι}
    (hS : IsRepSet σ S) (hT : IsRepSet σ T) :
    steinTerm w u S σ = steinTerm w u T σ := by
  unfold steinTerm
  rw [prod_repSet_eq hσ hw hS hT]

/-! ## 2. Where an involution of `Option α` is fixed -/

/-- `optionCongr g` fixes `none` and exactly the fixed points of `g`. -/
theorem fixedPoints_optionCongr (g : Equiv.Perm α) :
    (Finset.univ.filter (fun x : Option α => Equiv.optionCongr g x = x))
      = insert none ((Finset.univ.filter (fun i => g i = i)).image some) := by
  ext x
  rcases x with - | i
  · simp
  · simp [Equiv.optionCongr_apply]

/-- And `swap none (some b) * optionCongr g` fixes the fixed points of `g` **other than `b`** —
`none` goes to `some b`, and `some b` goes to `none`. -/
theorem fixedPoints_opt {b : α} {g : Equiv.Perm α} (hg : g ∈ involutions α) (hgb : g b = b) :
    (Finset.univ.filter (fun x : Option α => opt b g x = x))
      = ((Finset.univ.filter (fun i => g i = i ∧ i ≠ b)).image some) := by
  ext x
  rcases x with - | i
  · simp
  · by_cases hib : i = b
    · subst hib
      rw [Finset.mem_filter, opt_some_self hgb]
      simp
    · rw [Finset.mem_filter, opt_some_of_ne hg hgb hib]
      simp only [Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_filter,
        Option.some.injEq]
      constructor
      · intro h
        exact ⟨i, ⟨h, hib⟩, rfl⟩
      · rintro ⟨j, ⟨hj, -⟩, rfl⟩
        rw [hj]

/-! ## 3. The two factorisations -/

variable {W : Option α → Option α → M} {U : Option α → M}

omit [Fintype α] in
/-- The representative set for `optionCongr g`: the same one, relabelled. `none` is fixed and so
belongs to no pair. -/
theorem isRepSet_optionCongr {g : Equiv.Perm α} {S : Finset α} (hS : IsRepSet g S) :
    IsRepSet (Equiv.optionCongr g) (S.image some) := by
  constructor
  · intro x hx
    obtain ⟨i, hiS, rfl⟩ := Finset.mem_image.mp hx
    rw [Equiv.optionCongr_apply]
    simpa using hS.ne hiS
  · intro x hmv
    rcases x with - | i
    · exact absurd (by simp) hmv
    · rw [Equiv.optionCongr_apply] at hmv ⊢
      have hgi : g i ≠ i := by
        intro hc
        exact hmv (by simp [hc])
      have hmem : ∀ j : α, (some j ∈ S.image some) ↔ j ∈ S := by intro j; simp
      simpa [Option.map_some, hmem] using hS.2 i hgi

/-- **THE NEW INDEX ALONE.** `optionCongr g` leaves `none` fixed, so the term is `U none` times
the term of `g`. -/
theorem steinTerm_optionCongr {g : Equiv.Perm α} {S : Finset α} :
    steinTerm W U (S.image some) (Equiv.optionCongr g)
      = U none * steinTerm (fun i j => W (some i) (some j)) (fun i => U (some i)) S g := by
  unfold steinTerm
  rw [fixedPoints_optionCongr g,
    Finset.prod_insert (by simp),
    Finset.prod_image (fun x _ y _ h => Option.some_injective _ h),
    Finset.prod_image (fun x _ y _ h => Option.some_injective _ h)]
  simp only [Equiv.optionCongr_apply, Option.map_some]
  exact mul_left_comm _ _ _

/-- **THE NEW INDEX PAIRED WITH `b`.** The pair contributes `W none (some b)`, and **`b` is used
up**: the surviving fixed-point product runs over the fixed points of `g` other than `b`. -/
theorem steinTerm_opt {b : α} {g : Equiv.Perm α} (hg : g ∈ involutions α) (hgb : g b = b)
    {S : Finset α} (hS : IsRepSet g S) :
    steinTerm W U (insert none (S.image some)) (opt b g)
      = W none (some b)
        * ((∏ i ∈ S, W (some i) (some (g i)))
          * ∏ i ∈ Finset.univ.filter (fun i => g i = i ∧ i ≠ b), U (some i)) := by
  unfold steinTerm
  rw [prod_repSet_option hg hgb hS W, fixedPoints_opt hg hgb,
    Finset.prod_image (fun x _ y _ h => Option.some_injective _ h), mul_assoc]

/-! ## 4. The recursion -/

/-- **THE RUNG TERM'S RECURSION.** A rung's sum over the involutions of `Option α` splits into the
branch where the new index is alone — contributing `U none` times the whole sum one order down —
and, for each `b`, the branch where it is paired with `b`, contributing `W none (some b)` times a
sum in which **`b` no longer contributes a fixed-point factor**.

`InvolutionSums.sum_involutions_option` supplies the index split and §3 the factorisations; §1 is
what lets the caller's representative choices be replaced by the structured ones. -/
theorem sum_steinTerm_option {R : Type*} [CommSemiring R]
    (W : Option α → Option α → R) (U : Option α → R)
    (hW : ∀ x y, W x y = W y x)
    (rep : Equiv.Perm (Option α) → Finset (Option α))
    (hrep : ∀ σ ∈ involutions (Option α), IsRepSet σ (rep σ))
    (repα : Equiv.Perm α → Finset α)
    (hrepα : ∀ g ∈ involutions α, IsRepSet g (repα g)) :
    ∑ σ : ↑(involutions (Option α)), steinTerm W U (rep σ.1) σ.1
      = U none * ∑ g : ↑(involutions α),
          steinTerm (fun i j => W (some i) (some j)) (fun i => U (some i)) (repα g.1) g.1
        + ∑ b : α, W none (some b)
            * ∑ g : {f : Equiv.Perm α // f ∈ involutions α ∧ f b = b},
                ((∏ i ∈ repα g.1, W (some i) (some (g.1 i)))
                  * ∏ i ∈ Finset.univ.filter (fun i => g.1 i = i ∧ i ≠ b), U (some i)) := by
  rw [InvolutionSums.sum_involutions_option (fun σ => steinTerm W U (rep σ) σ)]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hgi : g.1 ∈ involutions α := g.2
    have hoc : Equiv.optionCongr g.1 ∈ involutions (Option α) := by
      intro x
      cases x with
      | none => simp
      | some y => simp [Equiv.optionCongr_apply, hgi y]
    rw [steinTerm_repSet_eq hoc hW U (hrep _ hoc)
        (isRepSet_optionCongr (hrepα g.1 hgi)),
      steinTerm_optionCongr]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hgi : g.1 ∈ involutions α := g.2.1
    have hgb : g.1 b = b := g.2.2
    have hopt : opt b g.1 ∈ involutions (Option α) :=
      (involutive_swap_optionCongr_iff (some b) g.1).mpr
        ⟨hgi, fun c hc => by cases Option.some_injective _ hc; exact hgb⟩
    rw [steinTerm_repSet_eq hopt hW U (hrep _ hopt)
        (isRepSet_option hgi hgb (hrepα g.1 hgi)),
      steinTerm_opt hgi hgb (hrepα g.1 hgi)]

/-! ## 5. The recursion specialised back to the count it generalises -/

/-- **`Involutions.card_involutions_option` IS THE CASE `W = U = 1`**, as it must be: a weighted
recursion that did not reproduce the count would be a different statement wearing its name.

**AND WHAT THIS CHECK CANNOT SEE.** At `W = U = 1` every term is `1`, so the identity reduces to a
statement about the SIZES of the two branches, and those are fixed by
`InvolutionSums.sum_involutions_option` alone. **Nothing here tests which factor each branch
carries**, and in particular nothing tests the `i ≠ b` clause of `steinTerm_opt`. That is what the
next theorem is for. -/
theorem card_involutions_option_of_steinTerm
    (rep : Equiv.Perm (Option α) → Finset (Option α))
    (hrep : ∀ σ ∈ involutions (Option α), IsRepSet σ (rep σ))
    (repα : Equiv.Perm α → Finset α)
    (hrepα : ∀ g ∈ involutions α, IsRepSet g (repα g)) :
    Fintype.card ↑(involutions (Option α))
      = Fintype.card ↑(involutions α)
        + ∑ b : α, Fintype.card {f : Equiv.Perm α // f ∈ involutions α ∧ f b = b} := by
  have h := sum_steinTerm_option (α := α) (R := ℕ) (fun _ _ => 1) (fun _ => 1)
    (fun _ _ => rfl) rep hrep repα hrepα
  simpa only [steinTerm, Finset.prod_const_one, one_mul, mul_one, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] using h

omit [DecidableEq α] in
/-- `∏ 0` over a filtered set is the indicator that the filter is empty. -/
theorem prod_zero_filter (p : α → Prop) [DecidablePred p] :
    (∏ _i ∈ Finset.univ.filter p, (0 : ℕ)) = if (∀ x, ¬ p x) then 1 else 0 := by
  rw [Finset.prod_const]
  by_cases h : ∀ x, ¬ p x
  · rw [if_pos h, Finset.filter_eq_empty_iff.mpr (fun x _ => h x), Finset.card_empty, pow_zero]
  · rw [if_neg h]
    push Not at h
    obtain ⟨x, hx⟩ := h
    exact zero_pow (Finset.card_pos.mpr ⟨x, by simp [hx]⟩).ne'

/-- **THE CHECK THAT SEES THE `i ≠ b` CLAUSE.** At `U ≡ 0` the fixed-point product is `1` exactly
on the involutions with no fixed point, and the `U none` branch vanishes outright. What is left
says: *the fixed-point-free involutions of `Option α` are counted, for each `b : α`, by the
involutions of `α` whose only fixed point is `b`* — `Involutions.card_perfectMatchings_option` in
indicator form.

**And it fails loudly without the clause.** Drop the `i ≠ b` from `steinTerm_opt` and the
right-hand side becomes identically zero, since `b` is a fixed point of every `g` in that fibre,
while the left-hand side counts real pairings. That is the discrimination
`card_involutions_option_of_steinTerm` cannot supply. -/
theorem sum_steinTerm_option_derangement
    (rep : Equiv.Perm (Option α) → Finset (Option α))
    (hrep : ∀ σ ∈ involutions (Option α), IsRepSet σ (rep σ))
    (repα : Equiv.Perm α → Finset α)
    (hrepα : ∀ g ∈ involutions α, IsRepSet g (repα g)) :
    ∑ σ : ↑(involutions (Option α)), (if (∀ x, σ.1 x ≠ x) then 1 else 0 : ℕ)
      = ∑ b : α, ∑ g : {f : Equiv.Perm α // f ∈ involutions α ∧ f b = b},
          (if (∀ i, g.1 i = i → i = b) then 1 else 0 : ℕ) := by
  have hL : ∀ σ : Equiv.Perm (Option α),
      (∏ _i ∈ Finset.univ.filter (fun x : Option α => σ x = x), (0 : ℕ))
        = if (∀ x, σ x ≠ x) then 1 else 0 := by
    intro σ
    simpa using prod_zero_filter (α := Option α) (fun x => σ x = x)
  have hR : ∀ (b : α) (g : Equiv.Perm α),
      (∏ _i ∈ Finset.univ.filter (fun i => g i = i ∧ i ≠ b), (0 : ℕ))
        = if (∀ i, g i = i → i = b) then 1 else 0 := by
    intro b g
    have hiff : (∀ x, ¬(g x = x ∧ x ≠ b)) ↔ (∀ i, g i = i → i = b) := by
      constructor
      · intro h i hi
        by_contra hc
        exact h i ⟨hi, hc⟩
      · rintro h i ⟨hi, hib⟩
        exact hib (h i hi)
    rw [prod_zero_filter (fun i => g i = i ∧ i ≠ b)]
    simp only [hiff]
  have h := sum_steinTerm_option (α := α) (R := ℕ) (fun _ _ => 1) (fun _ => 0)
    (fun _ _ => rfl) rep hrep repα hrepα
  simpa only [steinTerm, Finset.prod_const_one, one_mul, zero_mul, zero_add, hL, hR] using h

end SteinSumRecursion
