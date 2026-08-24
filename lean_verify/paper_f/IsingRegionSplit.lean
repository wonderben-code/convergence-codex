/-
  IsingRegionSplit.lean — **deleting the interaction terms that live entirely outside a region
  changes no correlation inside it.** This is the assembly the last three units were building
  towards, and it is stated with no type surgery at all: same site type, same index type, same
  `part`/`num`, only the couplings change.

  WHY THIS SHAPE. The obvious route was to carve the site type into two and the index type to match,
  then quote `IsingSumModel.expect_sum`. That works and it costs two `Equiv`s and a pile of `Finset`
  image manipulation at every use site. The cheaper route is to notice that **switching a coupling
  off is already expressible in the model** — `keep P J` is a perfectly good coupling function — so
  the theorem can compare two models of exactly the same type and never mention a sum type in its
  statement. `Equiv.sumCompl` appears only inside the proof, where it belongs.

  THE HYPOTHESES ARE THE HONEST ONES. `P` picks out a set of indices; every term it picks must
  have all its sites inside the region, and every term it does not pick must have all its sites
  outside it. Terms whose
  sites straddle the boundary are not permitted — and that is not a limitation dodged but the reason
  `IsingSupportModel` was proved first: in the intended application the straddling terms are exactly
  the ones whose coupling is zero, and they are removed before this theorem is applied.

  STRUCTURE. `expect_eq_left` factorises a correlation into "the region's half" over the region's
  configurations alone, and is the only real work. `expect_drop_outside` then applies it **twice** —
  once to `J`, once to `keep P J` — and the two right-hand sides are visibly equal because
  `keep P (keep P J) = keep P J`. That is why the outside half never has to be computed.

  WHAT REMAINS. Instantiating this at the box needs the walk's sites named as a region and the
  surviving terms of `IsingPathComparison.pathCoup` checked against the two purity hypotheses. Not
  attempted here and its cost is not claimed (`ERRATUM 246`). **No wall moves, and nothing here is
  a bound on anything.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingSupportModel

namespace IsingRegionSplit

open Finset Real
open IsingTransfer2D IsingGriffithsMono

variable {V : Type*} [Fintype V] [DecidableEq V] {I : Type*} [Fintype I]
variable {Q : V → Prop} [DecidablePred Q]

/-! ## 1. Switching a set of terms off, and reading a configuration off the two halves -/

/-- Keep the couplings `P` picks out, switch the rest off. -/
def keep (P : I → Prop) [DecidablePred P] (J : I → ℝ) : I → ℝ :=
  fun i => if P i then J i else 0

/-- Switch off the couplings `P` picks out, keep the rest. -/
def drop (P : I → Prop) [DecidablePred P] (J : I → ℝ) : I → ℝ :=
  fun i => if P i then 0 else J i

omit [Fintype I] in
theorem keep_keep (P : I → Prop) [DecidablePred P] (J : I → ℝ) : keep P (keep P J) = keep P J := by
  funext i
  by_cases hi : P i <;> simp [keep, hi]

omit [Fintype I] in
theorem keep_add_drop (P : I → Prop) [DecidablePred P] (J : I → ℝ) (i : I) :
    keep P J i + drop P J i = J i := by
  by_cases hi : P i <;> simp [keep, drop, hi]

/-- A configuration of the region and one of its complement, read as a configuration of `V`. -/
def glue (τ : ({v // Q v} ⊕ {v // ¬ Q v}) → Bool) : V → Bool :=
  fun v => τ ((Equiv.sumCompl Q).symm v)

omit [Fintype V] [DecidableEq V] in
theorem glue_pos {v : V} (h : Q v) (τ : ({v // Q v} ⊕ {v // ¬ Q v}) → Bool) :
    glue τ v = τ (Sum.inl ⟨v, h⟩) := by
  rw [glue, Equiv.sumCompl_symm_apply_of_pos h]

omit [Fintype V] [DecidableEq V] in
theorem glue_neg {v : V} (h : ¬ Q v) (τ : ({v // Q v} ⊕ {v // ¬ Q v}) → Bool) :
    glue τ v = τ (Sum.inr ⟨v, h⟩) := by
  rw [glue, Equiv.sumCompl_symm_apply_of_neg h]

omit [Fintype V] [DecidableEq V] in
/-- A product over sites **inside** the region sees only the region's half of the configuration. -/
theorem prod_congr_left (T : Finset V) (hT : ∀ v ∈ T, Q v)
    (τ τ' : ({v // Q v} ⊕ {v // ¬ Q v}) → Bool) (h : ∀ x, τ (Sum.inl x) = τ' (Sum.inl x)) :
    ∏ v ∈ T, spin (glue τ v) = ∏ v ∈ T, spin (glue τ' v) :=
  Finset.prod_congr rfl fun v hv => by rw [glue_pos (hT v hv), glue_pos (hT v hv), h]

omit [Fintype V] [DecidableEq V] in
/-- And a product over sites **outside** it sees only the complement's half. -/
theorem prod_congr_right (T : Finset V) (hT : ∀ v ∈ T, ¬ Q v)
    (τ τ' : ({v // Q v} ⊕ {v // ¬ Q v}) → Bool) (h : ∀ x, τ (Sum.inr x) = τ' (Sum.inr x)) :
    ∏ v ∈ T, spin (glue τ v) = ∏ v ∈ T, spin (glue τ' v) :=
  Finset.prod_congr rfl fun v hv => by rw [glue_neg (hT v hv), glue_neg (hT v hv), h]

/-- `IsingModelSplit.sum_relabel` restated with `glue`, which it equals definitionally. Without
this the rewrites below produce an un-beta-reduced application and no pattern matches. -/
theorem sum_glue (f : (V → Bool) → ℝ) :
    ∑ τ : ({v // Q v} ⊕ {v // ¬ Q v}) → Bool, f (glue τ) = ∑ υ : V → Bool, f υ :=
  IsingModelSplit.sum_relabel (Equiv.sumCompl Q) f

/-! ## 2. The two halves of the energy -/

/-- The region's energy, as a function of the region's configuration alone. -/
def eL (S : I → Finset V) (J : I → ℝ) (P : I → Prop) [DecidablePred P]
    (a : {v // Q v} → Bool) : ℝ :=
  ∑ i : I, keep P J i * ∏ v ∈ S i, spin (glue (Sum.elim a (fun _ => true)) v)

/-- The complement's energy, as a function of the complement's configuration alone. -/
def eR (S : I → Finset V) (J : I → ℝ) (P : I → Prop) [DecidablePred P]
    (b : {v // ¬ Q v} → Bool) : ℝ :=
  ∑ i : I, drop P J i * ∏ v ∈ S i, spin (glue (Sum.elim (fun _ => true) b) v)

omit [Fintype V] [DecidableEq V] in
/-- **THE ENERGY SPLITS.** Every term is pure, so every term lands in exactly one half. -/
theorem energy_glue (S : I → Finset V) (J : I → ℝ) (P : I → Prop) [DecidablePred P]
    (hL : ∀ i, P i → ∀ v ∈ S i, Q v) (hLc : ∀ i, ¬ P i → ∀ v ∈ S i, ¬ Q v)
    (τ : ({v // Q v} ⊕ {v // ¬ Q v}) → Bool) :
    ∑ i : I, J i * ∏ v ∈ S i, spin (glue τ v)
      = eL S J P (fun x => τ (Sum.inl x)) + eR S J P (fun x => τ (Sum.inr x)) := by
  rw [eL, eR, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : P i
  · have h1 : keep P J i = J i := by simp [keep, hi]
    have h2 : drop P J i = 0 := by simp [drop, hi]
    rw [h1, h2, zero_mul, add_zero]
    exact congrArg _ (prod_congr_left (S i) (hL i hi) _ _ (fun _ => rfl))
  · have h1 : keep P J i = 0 := by simp [keep, hi]
    have h2 : drop P J i = J i := by simp [drop, hi]
    rw [h1, h2, zero_mul, zero_add]
    exact congrArg _ (prod_congr_right (S i) (hLc i hi) _ _ (fun _ => rfl))

/-! ## 3. The factorisation -/

/-- The region's partition function, over the region's configurations alone. -/
noncomputable def partL (Q : V → Prop) [DecidablePred Q] (S : I → Finset V) (J : I → ℝ)
    (P : I → Prop) [DecidablePred P] : ℝ :=
  ∑ a : {v // Q v} → Bool, exp (eL S J P a)

/-- The region's numerator, over the region's configurations alone. -/
noncomputable def numL (Q : V → Prop) [DecidablePred Q] (S : I → Finset V) (J : I → ℝ)
    (P : I → Prop) [DecidablePred P] (A : Finset V) : ℝ :=
  ∑ a : {v // Q v} → Bool,
    (∏ v ∈ A, spin (glue (Sum.elim a (fun _ => true)) v)) * exp (eL S J P a)

/-- The complement's partition function. It is never computed; it cancels. -/
noncomputable def partR (Q : V → Prop) [DecidablePred Q] (S : I → Finset V) (J : I → ℝ)
    (P : I → Prop) [DecidablePred P] : ℝ :=
  ∑ b : {v // ¬ Q v} → Bool, exp (eR S J P b)

theorem partR_pos (Q : V → Prop) [DecidablePred Q] (S : I → Finset V) (J : I → ℝ)
    (P : I → Prop) [DecidablePred P] :
    0 < partR Q S J P :=
  Finset.sum_pos (fun _ _ => exp_pos _) ⟨fun _ => true, Finset.mem_univ _⟩

theorem part_factor (S : I → Finset V) (J : I → ℝ) (P : I → Prop) [DecidablePred P]
    (hL : ∀ i, P i → ∀ v ∈ S i, Q v) (hLc : ∀ i, ¬ P i → ∀ v ∈ S i, ¬ Q v) :
    part S J = partL Q S J P * partR Q S J P := by
  rw [part, ← sum_glue (Q := Q) (fun υ : V → Bool => exp (∑ i : I, J i * ∏ v ∈ S i, spin (υ v))),
      partL, partR,
      ← IsingModelSplit.sum_split (fun a => exp (eL S J P a)) (fun b => exp (eR S J P b))]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Real.exp_add, energy_glue S J P hL hLc τ]

theorem num_factor (S : I → Finset V) (J : I → ℝ) (P : I → Prop) [DecidablePred P]
    (hL : ∀ i, P i → ∀ v ∈ S i, Q v) (hLc : ∀ i, ¬ P i → ∀ v ∈ S i, ¬ Q v)
    (A : Finset V) (hA : ∀ v ∈ A, Q v) :
    num S J A = numL Q S J P A * partR Q S J P := by
  rw [num, ← sum_glue (Q := Q) (fun υ : V → Bool =>
          (∏ v ∈ A, spin (υ v)) * exp (∑ i : I, J i * ∏ v ∈ S i, spin (υ v))),
      numL, partR,
      ← IsingModelSplit.sum_split
        (fun a => (∏ v ∈ A, spin (glue (Sum.elim a (fun _ => true)) v)) * exp (eL S J P a))
        (fun b => exp (eR S J P b))]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [prod_congr_left A hA τ (Sum.elim (fun x => τ (Sum.inl x)) (fun _ => true)) (fun _ => rfl),
      energy_glue S J P hL hLc τ, Real.exp_add]
  ring

/-- **A CORRELATION INSIDE THE REGION IS COMPUTED BY THE REGION ALONE.** The complement's partition
function divides out; it is never evaluated and nothing is assumed about it. -/
theorem expect_eq_left (S : I → Finset V) (J : I → ℝ) (P : I → Prop) [DecidablePred P]
    (hL : ∀ i, P i → ∀ v ∈ S i, Q v) (hLc : ∀ i, ¬ P i → ∀ v ∈ S i, ¬ Q v)
    (A : Finset V) (hA : ∀ v ∈ A, Q v) :
    num S J A / part S J = numL Q S J P A / partL Q S J P := by
  rw [num_factor S J P hL hLc A hA, part_factor S J P hL hLc,
      mul_div_mul_right _ _ (ne_of_gt (partR_pos Q S J P))]

/-! ## 4. The consequence -/

omit [DecidablePred Q] in
/-- **DELETING THE TERMS THAT LIVE ENTIRELY OUTSIDE A REGION CHANGES NO CORRELATION INSIDE IT.**
Proved by applying `expect_eq_left` twice — to `J` and to `keep P J` — whose right-hand sides
coincide because `keep P (keep P J) = keep P J`. The outside half is therefore never computed.

The region's decidability is not a hypothesis of the statement — nothing in it mentions `Q` outside
the purity clauses — so it is supplied by `classical` in the proof rather than demanded of every
caller. -/
theorem expect_drop_outside (S : I → Finset V) (J : I → ℝ) (P : I → Prop) [DecidablePred P]
    (hL : ∀ i, P i → ∀ v ∈ S i, Q v) (hLc : ∀ i, ¬ P i → ∀ v ∈ S i, ¬ Q v)
    (A : Finset V) (hA : ∀ v ∈ A, Q v) :
    num S J A / part S J = num S (keep P J) A / part S (keep P J) := by
  classical
  rw [expect_eq_left S J P hL hLc A hA, expect_eq_left S (keep P J) P hL hLc A hA]
  simp only [numL, partL, eL, keep_keep]

/-- **THE SAME, WITH THE TWO PURITY CLAUSES PACKAGED AS THE ONE CONDITION A READER WOULD STATE.**
The review of the theorem above found no defect in it but an awkwardness: a caller must invent the
index predicate `P` and then discharge two clauses about it, when the only real assumption is that
**no interaction term straddles the region's boundary**. Given that, `P` is forced — it is *the
term lies inside* — so it is chosen here instead of asked for, and both clauses follow. -/
theorem expect_drop_outside_of_pure (S : I → Finset V) (J : I → ℝ)
    (hpure : ∀ i, (∀ v ∈ S i, Q v) ∨ (∀ v ∈ S i, ¬ Q v))
    (A : Finset V) (hA : ∀ v ∈ A, Q v) :
    num S J A / part S J
      = num S (keep (fun i => ∀ v ∈ S i, Q v) J) A / part S (keep (fun i => ∀ v ∈ S i, Q v) J) :=
  expect_drop_outside S J (fun i => ∀ v ∈ S i, Q v) (fun _ h => h)
    (fun i hi => (hpure i).resolve_left hi) A hA

end IsingRegionSplit
