import GreenExpansion

/-!
# A symmetric 0/1 matrix positive semidefinite on the sum-zero subspace is positive semidefinite

This finishes the chain `GreenExpansion` §9 left at B, and the leg was written down in
`UNLOCK_WATCHLIST` as a self-contained matrix question. It is answered here, and the answer is
**yes**.

## Why the wall wanted it

On §9's class, reflection positivity at `c` is `crossForm c ≤ (γ/m²)(∑_H c)²`, while the coupling
hypothesis `hcross` is `crossForm c ≤ 0`. Writing `C` for the cross matrix, those read
`C + t·J ≽ 0` and `C ≽ 0`. **The all-ones matrix `J` vanishes on the sum-zero subspace**, so
reflection positivity forces `C ≽ 0` there — and this file shows that is already enough.

**So the wall's converse holds on the whole of §9's class**
(`reflectionPositive_iff_hcross_of_adjSq`): reflection positivity and the coupling hypothesis are
EQUIVALENT there, which makes `GraphMirrorReflection.reflectionPositive_mirror` a
characterisation and not merely an implication. §6 of `GreenExpansion` had this for perfect
matchings; the class is now every regular graph whose `A²` lies in the span of `1`, `A` and `J`,
and it contains `K₂,₂`.

**The slack the previous unit pointed at is therefore not usable, and that is the answer rather
than a failure to find a counterexample.** The address was correct — a counterexample had to use
the slack — and the answer is that on this class nothing can.

## The three steps, and where the `0/1` hypothesis is spent

`e_p − e_q` has zero sum, so `C p p − 2 C p q + C q q ≥ 0`. **With entries in `{0,1}` that says
`C p q = 1 → C p p = 1 ∧ C q q = 1`** (`diag_eq_one_of_offDiag`) — the first place the hypothesis
is spent, and it confines `C` to the block where the diagonal is `1`.

`e_p + e_r − 2 e_q` also has zero sum, and on three indices with `C p q = C q r = 1` and
`C p r = 0` it gives `6 − 8 = −2 < 0`. So that configuration is impossible
(`offDiag_trans`) — the relation `C · · = 1` is **transitive**, hence an equivalence on the block.

Then `C` is a sum of one rank-one projection per class, **written without any quotient**:

    C i j = ∑_{k} (card of k's class)⁻¹ · [C k i = 1] · [C k j = 1]

— each class is counted once per member and weighted by the reciprocal of its size
(`sum_class_eq`). Positive semidefiniteness is then a swap of two sums.

## THE `0/1` HYPOTHESIS IS NOT DECORATION, AND A COUNTEREXAMPLE SAYS SO

`ERRATUM 144`. For merely **nonnegative** entries the statement is **false**:

    C = !![0, 1; 1, 5]

is symmetric with nonnegative entries, has value `0 − 2 + 5 = 3 > 0` on the sum-zero direction
`(1, −1)`, and has determinant `−1`, so it is not positive semidefinite
(`nonneg_counterexample`). **That is exhibited here rather than asserted**, because the watchlist
previously carried an argument — *"if `C` were strictly positive on the sum-zero subspace then
`1ᵀC1 < 0`, which nonnegative entries forbid"* — which this matrix refutes: `1ᵀC1 = 7`. The
argument confused the Euclidean normal of the hyperplane with its `C`-orthogonal complement, and
they are different vectors.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CrossPosSemidef

open Matrix

set_option linter.style.openClassical false
open scoped Classical

variable {V : Type*}

section Abstract

variable {C : Matrix V V ℝ} {H : Finset V}

/-- The hypothesis reflection positivity supplies: nonnegative on vectors that live on the half
and sum to zero there. -/
def ZeroSumNonneg (C : Matrix V V ℝ) (H : Finset V) : Prop :=
  ∀ c : V → ℝ, (∀ i, i ∉ H → c i = 0) → (∑ i ∈ H, c i) = 0 →
    0 ≤ ∑ i ∈ H, ∑ j ∈ H, c i * c j * C i j

/-- Evaluating the form at a vector supported on a subset of the half. -/
theorem form_of_support {c : V → ℝ} {T : Finset V} (hT : T ⊆ H)
    (hc : ∀ i, i ∉ T → c i = 0) :
    ∑ i ∈ H, ∑ j ∈ H, c i * c j * C i j = ∑ i ∈ T, ∑ j ∈ T, c i * c j * C i j := by
  classical
  rw [← Finset.sum_subset hT fun i _ hi =>
    Finset.sum_eq_zero fun j _ => by rw [hc i hi]; ring]
  exact Finset.sum_congr rfl fun i _ =>
    (Finset.sum_subset hT fun j _ hj => by rw [hc j hj]; ring).symm

/-- **THE PAIR STEP.** `e_p − e_q` sums to zero, so `C p p − 2 C p q + C q q ≥ 0`; with entries in
`{0, 1}` an off-diagonal `1` forces both diagonal entries to be `1`. -/
theorem diag_eq_one_of_offDiag (h01 : ∀ i j, C i j = 0 ∨ C i j = 1)
    (hz : ZeroSumNonneg C H) {p q : V} (hp : p ∈ H) (hq : q ∈ H) (hpq : p ≠ q)
    (hC : C p q = 1) (hsym : C q p = C p q) : C p p = 1 ∧ C q q = 1 := by
  classical
  have hsub : ({p, q} : Finset V) ⊆ H := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hpnq : p ∉ ({q} : Finset V) := by simpa using hpq
  set c : V → ℝ := fun x => if x = p then 1 else if x = q then -1 else 0 with hcdef
  have hsupp : ∀ i, i ∉ ({p, q} : Finset V) → c i = 0 := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [hcdef]; simp [hi.1, hi.2]
  have hzero : (∑ i ∈ H, c i) = 0 := by
    rw [← Finset.sum_subset hsub (fun i _ hi => hsupp i hi)]
    simp only [Finset.sum_insert hpnq, Finset.sum_singleton, hcdef]
    simp [Ne.symm hpq]
  have key := hz c (fun i hi => hsupp i fun hc => hi (hsub hc)) hzero
  rw [form_of_support hsub hsupp] at key
  simp only [Finset.sum_insert hpnq, Finset.sum_singleton, hcdef, if_neg hpq,
    if_neg (Ne.symm hpq)] at key
  rw [hsym, hC] at key
  rcases h01 p p with h1 | h1 <;> rcases h01 q q with h2 | h2
  · rw [h1, h2] at key; norm_num at key
  · rw [h1, h2] at key; norm_num at key
  · rw [h1, h2] at key; norm_num at key
  · exact ⟨h1, h2⟩

/-- **THE TRIPLE STEP.** `e_p + e_r − 2 e_q` sums to zero and, on three indices with `C p q =
C q r = 1` and `C p r = 0`, gives `6 − 8 = −2`. So the relation is transitive. -/
theorem offDiag_trans (h01 : ∀ i j, C i j = 0 ∨ C i j = 1) (hz : ZeroSumNonneg C H)
    (hsym : ∀ i j, C i j = C j i)
    {p q r : V} (hp : p ∈ H) (hq : q ∈ H) (hr : r ∈ H)
    (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    (h1 : C p q = 1) (h2 : C q r = 1) : C p r = 1 := by
  classical
  rcases h01 p r with hpr0 | hpr1
  swap
  · exact hpr1
  exfalso
  obtain ⟨hpp, hqq⟩ := diag_eq_one_of_offDiag h01 hz hp hq hpq h1 (hsym q p)
  obtain ⟨-, hrr⟩ := diag_eq_one_of_offDiag h01 hz hq hr hqr h2 (hsym r q)
  set c : V → ℝ := fun x => if x = p then 1 else if x = q then -2 else if x = r then 1 else 0
    with hcdef
  set T : Finset V := {p, q, r} with hTdef
  have hsub : T ⊆ H := by
    intro x hx
    simp only [hTdef, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hsupp : ∀ i, i ∉ T → c i = 0 := by
    intro i hi
    simp only [hTdef, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [hcdef]; simp [hi.1, hi.2.1, hi.2.2]
  have hqp : q ≠ p := Ne.symm hpq
  have hrp : r ≠ p := Ne.symm hpr
  have hrq : r ≠ q := Ne.symm hqr
  have hzero : (∑ i ∈ H, c i) = 0 := by
    rw [(Finset.sum_subset hsub (fun i _ hi => hsupp i hi)).symm, hTdef,
      Finset.sum_insert (by simp [hpq, hpr]), Finset.sum_insert (by simp [hqr]),
      Finset.sum_singleton, hcdef]
    simp [hqp, hrp, hrq]
    ring
  have key := hz c (fun i hi => hsupp i fun hc => hi (hsub hc)) hzero
  rw [form_of_support hsub hsupp, hTdef] at key
  simp only [Finset.sum_insert (show p ∉ ({q, r} : Finset V) by simp [hpq, hpr]),
    Finset.sum_insert (show q ∉ ({r} : Finset V) by simp [hqr]), Finset.sum_singleton] at key
  simp only [hcdef, if_pos rfl, if_neg hqp, if_neg hrp, if_neg hrq] at key
  rw [hpp, hqq, hrr, h1, h2, hpr0, hsym q p, h1, hsym r q, h2, hsym r p, hpr0] at key
  norm_num at key

end Abstract

/-! ## The rank-one decomposition, written without a quotient -/

section Decomp

variable {C : Matrix V V ℝ} {H : Finset V}

/-- The indices carrying a `1` on the diagonal — the only ones `C` can be nonzero on. -/
noncomputable def blk (C : Matrix V V ℝ) (H : Finset V) : Finset V :=
  H.filter fun i => C i i = 1

/-- The class of `k`: everything the relation joins it to. -/
noncomputable def cls (C : Matrix V V ℝ) (H : Finset V) (k : V) : Finset V :=
  (blk C H).filter fun i => C k i = 1

theorem mem_blk {i : V} (h : i ∈ blk C H) : i ∈ H ∧ C i i = 1 := by
  simpa [blk] using h

theorem self_mem_cls {k : V} (hk : k ∈ blk C H) : k ∈ cls C H k := by
  simp only [cls, Finset.mem_filter]
  exact ⟨hk, (mem_blk hk).2⟩

theorem cls_nonempty {k : V} (hk : k ∈ blk C H) : (cls C H k).Nonempty :=
  ⟨k, self_mem_cls hk⟩
theorem cls_card_pos {k : V} (hk : k ∈ blk C H) : 0 < (cls C H k).card :=
  Finset.card_pos.mpr (cls_nonempty hk)

variable (hsym : ∀ i j, C i j = C j i)
  (htrans : ∀ i ∈ blk C H, ∀ j ∈ blk C H, ∀ l ∈ blk C H, C i j = 1 → C j l = 1 → C i l = 1)

include hsym htrans in
/-- Related indices have the same class — the relation is an equivalence on the block. -/
theorem cls_eq_of_rel {k i : V} (hk : k ∈ blk C H) (hi : i ∈ blk C H) (hki : C k i = 1) :
    cls C H k = cls C H i := by
  ext j
  simp only [cls, Finset.mem_filter]
  refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
  · exact htrans i hi k hk j h.1 (by rw [hsym i k]; exact hki) h.2
  · exact htrans k hk i hi j h.1 hki h.2

include hsym htrans in
/-- **THE DECOMPOSITION, WITHOUT A QUOTIENT.** Each class is counted once per member and weighted
by the reciprocal of its size, so the weights add to one per class. -/
theorem sum_class_eq (h01 : ∀ i j, C i j = 0 ∨ C i j = 1)
    (hoff : ∀ i j, C i j = 1 → i ∈ blk C H ∧ j ∈ blk C H) (i j : V) :
    ∑ k ∈ blk C H, ((cls C H k).card : ℝ)⁻¹
        * (if C k i = 1 then (1 : ℝ) else 0) * (if C k j = 1 then (1 : ℝ) else 0)
      = C i j := by
  classical
  have hclssub : cls C H i ⊆ blk C H := Finset.filter_subset _ _
  by_cases hij : C i j = 1
  · obtain ⟨hiB, hjB⟩ := hoff i j hij
    have step : ∀ k ∈ blk C H,
        ((cls C H k).card : ℝ)⁻¹ * (if C k i = 1 then (1 : ℝ) else 0)
            * (if C k j = 1 then (1 : ℝ) else 0)
          = if k ∈ cls C H i then ((cls C H i).card : ℝ)⁻¹ else 0 := by
      intro k hk
      by_cases hki : C k i = 1
      · have hkcls : k ∈ cls C H i := by
          simp only [cls, Finset.mem_filter]
          exact ⟨hk, by rw [hsym i k]; exact hki⟩
        have hkj : C k j = 1 := htrans k hk i hiB j hjB hki hij
        rw [if_pos hki, if_pos hkj, if_pos hkcls, cls_eq_of_rel hsym htrans hk hiB hki]
        ring
      · have hnot : k ∉ cls C H i := by
          simp only [cls, Finset.mem_filter, not_and]
          exact fun _ hc => hki (by rw [hsym k i]; exact hc)
        rw [if_neg hki, if_neg hnot]
        ring
    rw [Finset.sum_congr rfl step, Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr hclssub, Finset.sum_const, nsmul_eq_mul, hij]
    exact mul_inv_cancel₀ (Nat.cast_pos.mpr (cls_card_pos hiB)).ne'
  · rw [(h01 i j).resolve_right hij]
    refine Finset.sum_eq_zero fun k hk => ?_
    by_cases hki : C k i = 1
    · by_cases hkj : C k j = 1
      · exact absurd (htrans i (hoff k i hki).2 k hk j (hoff k j hkj).2
          (by rw [hsym i k]; exact hki) hkj) hij
      · rw [if_neg hkj]; ring
    · rw [if_neg hki]; ring

include hsym htrans in
/-- **THE FORM IS A SUM OF SQUARES**, one per index of the block, weighted by the reciprocal of
its class size. Swapping the two sums is the whole proof. -/
theorem form_eq_sum_sq [Fintype V] (h01 : ∀ i j, C i j = 0 ∨ C i j = 1)
    (hoff : ∀ i j, C i j = 1 → i ∈ blk C H ∧ j ∈ blk C H) (c : V → ℝ) :
    ∑ i, ∑ j, c i * c j * C i j
      = ∑ k ∈ blk C H, ((cls C H k).card : ℝ)⁻¹
          * (∑ i, c i * (if C k i = 1 then (1 : ℝ) else 0)) ^ 2 := by
  classical
  have expand : ∀ k : V, ((cls C H k).card : ℝ)⁻¹
      * (∑ i, c i * (if C k i = 1 then (1 : ℝ) else 0)) ^ 2
      = ∑ i, ∑ j, c i * c j * (((cls C H k).card : ℝ)⁻¹
          * (if C k i = 1 then (1 : ℝ) else 0) * (if C k j = 1 then (1 : ℝ) else 0)) := by
    intro k
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  have hRHS : ∑ k ∈ blk C H, ((cls C H k).card : ℝ)⁻¹
        * (∑ i, c i * (if C k i = 1 then (1 : ℝ) else 0)) ^ 2
      = ∑ k ∈ blk C H, ∑ i, ∑ j, c i * c j * (((cls C H k).card : ℝ)⁻¹
          * (if C k i = 1 then (1 : ℝ) else 0) * (if C k j = 1 then (1 : ℝ) else 0)) :=
    Finset.sum_congr rfl fun k _ => expand k
  rw [hRHS]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, sum_class_eq hsym htrans h01 hoff i j]

include hsym htrans in
/-- **THE THEOREM.** A symmetric `0/1` matrix, supported on the half, that is nonnegative on the
sum-zero vectors of that half is positive semidefinite. -/
theorem form_nonneg [Fintype V] (h01 : ∀ i j, C i j = 0 ∨ C i j = 1)
    (hoff : ∀ i j, C i j = 1 → i ∈ blk C H ∧ j ∈ blk C H) (c : V → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * C i j := by
  rw [form_eq_sum_sq hsym htrans h01 hoff c]
  refine Finset.sum_nonneg fun k hk => ?_
  have : (0 : ℝ) ≤ ((cls C H k).card : ℝ)⁻¹ := by positivity
  positivity

end Decomp

/-! ## Assembling the hypotheses: the two steps supply exactly what the decomposition wants -/

section Main

variable {C : Matrix V V ℝ} {H : Finset V}

/-- Off the block, `C` vanishes — the pair step, restated as the decomposition needs it. -/
theorem mem_blk_of_offDiag (h01 : ∀ i j, C i j = 0 ∨ C i j = 1) (hsym : ∀ i j, C i j = C j i)
    (hz : ZeroSumNonneg C H) (hsupp : ∀ i j, C i j = 1 → i ∈ H ∧ j ∈ H)
    (i j : V) (hij : C i j = 1) : i ∈ blk C H ∧ j ∈ blk C H := by
  classical
  obtain ⟨hiH, hjH⟩ := hsupp i j hij
  by_cases h : i = j
  · subst h
    exact ⟨by simp only [blk, Finset.mem_filter]; exact ⟨hiH, hij⟩,
      by simp only [blk, Finset.mem_filter]; exact ⟨hiH, hij⟩⟩
  · obtain ⟨hii, hjj⟩ := diag_eq_one_of_offDiag h01 hz hiH hjH h hij (hsym j i)
    exact ⟨by simp only [blk, Finset.mem_filter]; exact ⟨hiH, hii⟩,
      by simp only [blk, Finset.mem_filter]; exact ⟨hjH, hjj⟩⟩

/-- Transitivity on the block — the triple step, restated. The `i = l` and coincidence cases are
where the diagonal being `1` on the block is used. -/
theorem trans_on_blk (h01 : ∀ i j, C i j = 0 ∨ C i j = 1) (hsym : ∀ i j, C i j = C j i)
    (hz : ZeroSumNonneg C H) :
    ∀ i ∈ blk C H, ∀ j ∈ blk C H, ∀ l ∈ blk C H, C i j = 1 → C j l = 1 → C i l = 1 := by
  intro i hi j hj l hl hij hjl
  obtain ⟨hiH, hii⟩ := mem_blk hi
  obtain ⟨hjH, -⟩ := mem_blk hj
  obtain ⟨hlH, hll⟩ := mem_blk hl
  by_cases hil : i = l
  · subst hil; exact hii
  by_cases hij' : i = j
  · subst hij'; exact hjl
  by_cases hjl' : j = l
  · subst hjl'; exact hij
  exact offDiag_trans h01 hz hsym hiH hjH hlH hij' hjl' hil hij hjl

/-- **THE MAIN THEOREM.** Positive semidefinite on the sum-zero vectors of the half, plus
symmetry and `0/1` entries, gives positive semidefinite. -/
theorem posSemidef_of_zeroSum [Fintype V] (h01 : ∀ i j, C i j = 0 ∨ C i j = 1)
    (hsym : ∀ i j, C i j = C j i)
    (hsupp : ∀ i j, C i j = 1 → i ∈ H ∧ j ∈ H) (hz : ZeroSumNonneg C H) (c : V → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * C i j :=
  form_nonneg hsym (trans_on_blk h01 hsym hz) h01
    (mem_blk_of_offDiag h01 hsym hz hsupp) c

end Main

/-! ## The `0/1` hypothesis is not decoration -/

/-- **A NONNEGATIVE COUNTEREXAMPLE.** `!![0,1;1,5]` is symmetric with nonnegative entries and is
positive on the sum-zero direction `(1,−1)`, yet its determinant is `−1`, so it is not positive
semidefinite. Its value on the all-ones vector is `7`, which refutes the argument the watchlist
carried before `ERRATUM 144` — that a strictly positive restriction would force `1ᵀC1 < 0`. -/
theorem nonneg_counterexample :
    (∀ i j, (0 : ℝ) ≤ !![(0 : ℝ), 1; 1, 5] i j)
      ∧ (0 : ℝ) < ∑ i, ∑ j, (![1, -1] i) * (![1, -1] j) * !![(0 : ℝ), 1; 1, 5] i j
      ∧ (∑ i, ∑ j, (![1, 1] i) * (![1, 1] j) * !![(0 : ℝ), 1; 1, 5] i j) = 7
      ∧ (!![(0 : ℝ), 1; 1, 5]).det = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num
  · norm_num [Fin.sum_univ_succ]
  · norm_num [Fin.sum_univ_succ]
  · norm_num [Matrix.det_fin_two_of]

/-! ## The payoff: the wall's converse, on the whole of `GreenExpansion` §9's class -/

section Wall

open GreenExpansion GraphReflection GraphMirrorReflection CrossFormMatrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}
variable {d : ℕ}

omit [Fintype V] in
theorem crossMatrix_entries (i j : V) :
    crossMatrix G θ H i j = 0 ∨ crossMatrix G θ H i j = 1 := by
  rw [crossMatrix]
  by_cases hm : i ∈ H ∧ j ∈ H
  · rw [if_pos hm, crossAdj]
    by_cases ha : G.Adj i (θ j)
    · exact Or.inr (if_pos ha)
    · exact Or.inl (if_neg ha)
  · exact Or.inl (if_neg hm)

omit [Fintype V] in
theorem crossMatrix_symm (h : IsRefl G θ) (i j : V) :
    crossMatrix G θ H i j = crossMatrix G θ H j i := by
  rw [crossMatrix, crossMatrix]
  by_cases hij : i ∈ H ∧ j ∈ H
  · rw [if_pos hij, if_pos ⟨hij.2, hij.1⟩, crossAdj_comm h i j]
  · rw [if_neg hij, if_neg fun hc => hij ⟨hc.2, hc.1⟩]

omit [Fintype V] in
theorem crossMatrix_apply_of_mem {i j : V} (hi : i ∈ H) (hj : j ∈ H) :
    crossMatrix G θ H i j = crossAdj G θ i j :=
  if_pos ⟨hi, hj⟩

omit [Fintype V] in
theorem crossMatrix_support {i j : V} (hij : crossMatrix G θ H i j = 1) : i ∈ H ∧ j ∈ H := by
  by_contra hc
  rw [crossMatrix, if_neg hc] at hij
  exact absurd hij (by norm_num)

/-- The form this file uses and the dot product `CrossFormMatrix` uses are the same thing. -/
theorem form_eq_dotProduct (w : V → ℝ) :
    ∑ i, ∑ j, w i * w j * crossMatrix G θ H i j = w ⬝ᵥ (crossMatrix G θ H *ᵥ w) := by
  rw [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **REFLECTION POSITIVITY SUPPLIES THE HYPOTHESIS.** On §9's class the slack term is a multiple
of `(∑_H c)²`, so it vanishes on exactly the vectors this file tests with. -/
theorem zeroSumNonneg_of_reflectionPositive (hd : G.IsRegularOfDegree d)
    (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0) {α β γ : ℝ}
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V)
    (hK : 0 < ((d : ℝ) + m ^ 2) ^ 2 - α - β * ((d : ℝ) + m ^ 2))
    (hrp : GraphReflection.ReflectionPositive G m θ H) :
    ZeroSumNonneg (crossMatrix G θ H) H := by
  intro c hcs hsum
  have hslack := (reflectionPositive_iff_slack hd hM h hm hA hK).mp hrp c hcs
  rw [hsum] at hslack
  have hcf : crossForm G m θ H c ≤ 0 := by simpa using hslack
  rw [crossForm_eq_neg_adj hM m c] at hcf
  have : (0 : ℝ) ≤ ∑ p ∈ H, ∑ q ∈ H, c p * c q * (if G.Adj p (θ q) then 1 else 0) := by
    linarith
  refine le_trans this (le_of_eq ?_)
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
  rw [crossMatrix_apply_of_mem hp hq, crossAdj]

/-- **THE WALL'S CONVERSE, ON THE WHOLE OF §9's CLASS.** Reflection positivity implies the
coupling hypothesis. Together with `GreenExpansion.reflectionPositive_iff_slack` and
`slack_of_hcross` the two are therefore EQUIVALENT there — so
`GraphMirrorReflection.reflectionPositive_mirror` is a characterisation on this class and not
merely an implication. -/
theorem hcross_of_reflectionPositive (hd : G.IsRegularOfDegree d)
    (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0) {α β γ : ℝ}
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V)
    (hK : 0 < ((d : ℝ) + m ^ 2) ^ 2 - α - β * ((d : ℝ) + m ^ 2))
    (hrp : GraphReflection.ReflectionPositive G m θ H) (w : V → ℝ) :
    crossForm G m θ H w ≤ 0 := by
  have hz := zeroSumNonneg_of_reflectionPositive hd hM h hm hA hK hrp
  have hpsd := posSemidef_of_zeroSum (C := crossMatrix G θ H) (H := H)
    crossMatrix_entries (crossMatrix_symm h) (fun i j hij => crossMatrix_support hij) hz w
  rw [form_eq_dotProduct w, dotProduct_crossMatrix hM m w] at hpsd
  linarith

/-- **AND SO IT IS AN EQUIVALENCE.** -/
theorem reflectionPositive_iff_hcross_of_adjSq (hd : G.IsRegularOfDegree d)
    (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0) {α β γ : ℝ}
    (hγ : 0 ≤ γ)
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V)
    (hK : 0 < ((d : ℝ) + m ^ 2) ^ 2 - α - β * ((d : ℝ) + m ^ 2)) :
    GraphReflection.ReflectionPositive G m θ H ↔ ∀ w : V → ℝ, crossForm G m θ H w ≤ 0 := by
  refine ⟨fun hrp => hcross_of_reflectionPositive hd hM h hm hA hK hrp, fun hc => ?_⟩
  exact (reflectionPositive_iff_slack hd hM h hm hA hK).mpr
    fun c _ => slack_of_hcross (γ := γ) (θ := θ) (H := H) hγ hm hc c

end Wall

end CrossPosSemidef
