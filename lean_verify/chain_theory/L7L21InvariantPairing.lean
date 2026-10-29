import Mathlib

/-!
# The invariant pairings of Mₙ, and the commutant of the matchings (L7 and L21)

Two gaps of the Tree of Reality close on one theorem.

* **L7 (the three lineages).** `R8KnownGivesPairing` proved that the only linear functional that every
  matching (conjugation) fixes is the trace. Here is the next order. A bilinear form on Mₙ(K) that is
  invariant under every matching, in the infinitesimal form B([A,X],Y) + B(X,[A,Y]) = 0, is
  α·tr(XY) + β·tr(X)·tr(Y) (`invariant_bilinear_classification`). So the pairing is not only
  forced but **unique up to these two terms**. The higher orders (the First Fundamental Theorem for
  matrices) remain cited.

* **L21 (the Born rule).** An operator φ on the GNS space L²(Mₙ) that commutes with every matching,
  φ([A,X]) = [A, φ(X)], is α·X + β·tr(X)·1 (`equivariant_classification`). On L²(Mₙ),
  X ↦ tr(X)·1/n is the projection onto the GNS vector Ω = 1/√n, which is the maximally entangled
  pair. So the commutant of the matchings is span{1, |Ω⟩⟨Ω|}, and twirling a vector state leaves
  weight |⟨Ω, x⟩|² on Ω: the Born square (checked numerically in
  `scripts/chain_theory/r5_born_circle.py`).

The proof works on matrix units: invariance gives a linear relation among b(i,j,k,l) =
B(Eᵢⱼ, Eₖₗ); diagonal choices kill every b outside the two patterns (i=j, k=l) and (i=l, j=k), and
off-diagonal choices force the survivors to two constants.

Genuine Mathlib proofs; no `sorry`, no `native_decide`, no new axioms. Characteristic zero; n ≥ 2.
-/

open Matrix

namespace ChainTheory.Pairing

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) K

/-- Product of matrix units. -/
lemma su (a b c d : Fin n) :
    single a b (1 : K) * single c d 1 = if b = c then single a d 1 else 0 := by
  split_ifs with h
  · subst h; rw [single_mul_single_same, one_mul]
  · simp [h]

/-- Linearity on matrix units: g X = Σᵢⱼ Xᵢⱼ • g(Eᵢⱼ). -/
lemma lin_expand {N : Type*} [AddCommGroup N] [Module K N] (g : M →ₗ[K] N) (X : M) :
    g X = ∑ i, ∑ j, X i j • g (single i j (1 : K)) := by
  conv_lhs => rw [matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show single i j (X i j) = X i j • single i j (1 : K) by
    rw [smul_single, smul_eq_mul, mul_one], map_smul]

section Bilinear

/-- The values on matrix units, b(i,j,k,l) = B(Eᵢⱼ, Eₖₗ). -/
def unitVal (B : M →ₗ[K] M →ₗ[K] K) (i j k l : Fin n) : K := B (single i j (1 : K)) (single k l 1)

/-- Invariance under every matching, in infinitesimal form. -/
def IsInvariant (B : M →ₗ[K] M →ₗ[K] K) : Prop :=
  ∀ A X Y : M, B (A * X - X * A) Y + B X (A * Y - Y * A) = 0


/-- The invariance relation on matrix units. -/
lemma unit_relation {B : M →ₗ[K] M →ₗ[K] K} (hB : IsInvariant B) (p q i j k l : Fin n) :
    (if q = i then unitVal B p j k l else (0 : K)) - (if j = p then unitVal B i q k l else 0)
      + (if q = k then unitVal B i j p l else 0) - (if l = p then unitVal B i j k q else 0) = (0 : K) := by
  have h := hB (single p q 1) (single i j 1) (single k l 1)
  rw [su, su, su, su] at h
  simp only [map_sub, LinearMap.sub_apply] at h
  unfold unitVal
  split_ifs at h ⊢ <;> (try simp only [map_zero, LinearMap.zero_apply, sub_zero, zero_sub] at h ⊢) <;>
    linear_combination h

/-- Diagonal matchings: (δ_pi − δ_jp + δ_pk − δ_lp) · b(i,j,k,l) = 0. -/
lemma diag_relation {B : M →ₗ[K] M →ₗ[K] K} (hB : IsInvariant B) (i j k l p : Fin n) :
    ((if p = i then 1 else 0) - (if j = p then 1 else 0) + (if p = k then 1 else 0)
      - (if l = p then 1 else 0) : K) * unitVal B i j k l = 0 := by
  have r := unit_relation hB p p i j k l
  split_ifs at r ⊢ <;> subst_vars <;> linear_combination r

/-- Diagonal matchings: b vanishes outside the two patterns. -/
lemma weight {B : M →ₗ[K] M →ₗ[K] K} (hB : IsInvariant B) (i j k l : Fin n)
    (h : ¬ ((i = j ∧ k = l) ∨ (i = l ∧ j = k))) : unitVal B i j k l = (0 : K) := by
  -- choose a diagonal matching whose coefficient is nonzero
  have key : ∃ p : Fin n, ((if p = i then 1 else 0) - (if j = p then 1 else 0)
      + (if p = k then 1 else 0) - (if l = p then 1 else 0) : K) ≠ 0 := by
    by_cases hij : i = j
    · subst hij
      by_cases hkl : k = l
      · exact absurd (Or.inl ⟨rfl, hkl⟩) h
      by_cases hik : i = k
      · subst hik; exact ⟨l, by simp [hkl, Ne.symm hkl]⟩
      · exact ⟨k, by simp [hik, Ne.symm hik, Ne.symm hkl]⟩
    · by_cases hil : i = l
      · subst hil
        by_cases hjk : j = k
        · exact absurd (Or.inr ⟨rfl, hjk⟩) h
        by_cases hki : k = i
        · subst hki; exact ⟨j, by simp [hij, Ne.symm hij]⟩
        · exact ⟨k, by simp [hki, Ne.symm hki, hjk, Ne.symm hjk]⟩
      · by_cases hik : i = k
        · subst hik; exact ⟨i, by simp [hij, hil, Ne.symm hij, Ne.symm hil]⟩
        · exact ⟨i, by simp [hij, hil, hik, Ne.symm hij, Ne.symm hil, Ne.symm hik]⟩
  obtain ⟨p, hp⟩ := key
  exact (mul_eq_zero.mp (diag_relation hB i j k l p)).resolve_left hp

/-- Off-diagonal matchings: the four relations among α_pq, β_pq, γ_p (p ≠ q). -/
lemma rel_pq {B : M →ₗ[K] M →ₗ[K] K} (hB : IsInvariant B) (p q : Fin n) (hpq : p ≠ q) :
    unitVal B p p q q + unitVal B q p p q = unitVal B q q q q ∧
    unitVal B p q q p + unitVal B q q p p = unitVal B q q q q ∧
    unitVal B p q q p + unitVal B p p q q = unitVal B p p p p ∧
    unitVal B q p p q + unitVal B q q p p = unitVal B p p p p := by
  have r1 := unit_relation hB p q q p q q
  have r2 := unit_relation hB p q q q q p
  have r4 := unit_relation hB p q p p q p
  have r3 := unit_relation hB p q q p p p
  simp [hpq, Ne.symm hpq] at r1 r2 r3 r4
  refine ⟨?_, ?_, ?_, ?_⟩
  · first | linear_combination r1 | linear_combination -r1
  · first | linear_combination r2 | linear_combination -r2
  · first | linear_combination r4 | linear_combination -r4
  · first | linear_combination r3 | linear_combination -r3

/-- The symmetric parts: α_pq = α_qp and β_pq = β_qp. -/
lemma symm_pq {B : M →ₗ[K] M →ₗ[K] K} (hB : IsInvariant B) (p q : Fin n) (hpq : p ≠ q) :
    unitVal B p q q p = unitVal B q p p q ∧ unitVal B p p q q = unitVal B q q p p := by
  obtain ⟨r1, r2, r4, r3⟩ := rel_pq hB p q hpq
  have two : (2 : K) ≠ 0 := two_ne_zero
  have hβ : unitVal B p p q q = unitVal B q q p p := by
    have : (2 : K) * (unitVal B p p q q - unitVal B q q p p) = 0 := by linear_combination r1 - r2 + r4 - r3
    have := (mul_eq_zero.mp this).resolve_left two
    linear_combination this
  refine ⟨?_, hβ⟩
  linear_combination r4 - r3 - hβ

/-- A third index: α_pr = α_qr and β_pr = β_qr for distinct p, q, r. -/
lemma cross {B : M →ₗ[K] M →ₗ[K] K} (hB : IsInvariant B) (p q r : Fin n) (hpq : p ≠ q) (hrp : r ≠ p) (hrq : r ≠ q) :
    unitVal B p r r p = unitVal B q r r q ∧ unitVal B p p r r = unitVal B q q r r := by
  have ra := unit_relation hB p q q r r p
  have rb := unit_relation hB p q q p r r
  simp [hpq, Ne.symm hpq, hrp, hrq, Ne.symm hrp, Ne.symm hrq] at ra rb
  exact ⟨by linear_combination ra, by linear_combination rb⟩

end Bilinear

section Classification

variable (hn : 2 ≤ n)
include hn

/-- **The classification.** For n ≥ 2 (characteristic zero), a bilinear form on Mₙ(K) invariant
under every matching is α·tr(XY) + β·tr(X)·tr(Y). -/
theorem invariant_bilinear_classification (B : M →ₗ[K] M →ₗ[K] K) (hB : IsInvariant B) :
    ∃ α β : K, ∀ X Y : M, B X Y = α * (X * Y).trace + β * (X.trace * Y.trace) := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let j0 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ j0 := by simp [i0, j0, Fin.ext_iff]
  set α := unitVal B i0 j0 j0 i0 with hα
  set β := unitVal B i0 i0 j0 j0 with hβ
  -- α and β are constant over every pair of distinct indices
  have αc : ∀ i j : Fin n, i ≠ j → unitVal B i j j i = α := by
    -- every α_ij equals α_{i0 j0}: move one index at a time with `cross`, flip with `symm_pq`
    have to0 : ∀ i : Fin n, i ≠ i0 → unitVal B i i0 i0 i = α := by
      intro i hi
      by_cases hij : i = j0
      · subst hij; exact ((symm_pq hB i0 j0 h01).1).symm
      · rw [(cross hB i j0 i0 hij (Ne.symm hi) h01).1]
        exact ((symm_pq hB i0 j0 h01).1).symm
    intro i j hij
    by_cases hi : i = i0
    · subst hi
      rw [(symm_pq hB i0 j hij).1]; exact to0 j (Ne.symm hij)
    · by_cases hj : j = i0
      · subst hj; exact to0 i hi
      · rw [(cross hB i i0 j hi (Ne.symm hij) hj).1, (symm_pq hB i0 j (Ne.symm hj)).1]
        exact to0 j hj
  have βc : ∀ i j : Fin n, i ≠ j → unitVal B i i j j = β := by
    have to0 : ∀ i : Fin n, i ≠ i0 → unitVal B i i i0 i0 = β := by
      intro i hi
      by_cases hij : i = j0
      · subst hij; exact ((symm_pq hB i0 j0 h01).2).symm
      · rw [(cross hB i j0 i0 hij (Ne.symm hi) h01).2]
        exact ((symm_pq hB i0 j0 h01).2).symm
    intro i j hij
    by_cases hi : i = i0
    · subst hi
      rw [(symm_pq hB i0 j hij).2]; exact to0 j (Ne.symm hij)
    · by_cases hj : j = i0
      · subst hj; exact to0 i hi
      · rw [(cross hB i i0 j hi (Ne.symm hij) hj).2, (symm_pq hB i0 j (Ne.symm hj)).2]
        exact to0 j hj
  have γc : ∀ i : Fin n, unitVal B i i i i = α + β := by
    intro i
    obtain ⟨j, hj⟩ : ∃ j : Fin n, i ≠ j := by
      by_cases h : i = i0
      · exact ⟨j0, h ▸ h01⟩
      · exact ⟨i0, h⟩
    have := (rel_pq hB i j hj).2.2.1
    rw [← this, αc i j hj, βc i j hj]
  -- the values on matrix units
  have formula : ∀ i j k l : Fin n, unitVal B i j k l
      = α * (if j = k ∧ l = i then 1 else 0) + β * (if i = j ∧ k = l then 1 else 0) := by
    intro i j k l
    by_cases p1 : i = j ∧ k = l
    · obtain ⟨rfl, rfl⟩ := p1
      by_cases hik : i = k
      · subst hik; simp [γc]
      · simp [hik, Ne.symm hik, βc i k hik]
    · by_cases p2 : i = l ∧ j = k
      · obtain ⟨rfl, rfl⟩ := p2
        have hij : i ≠ j := fun h => p1 ⟨h, h.symm⟩
        simp [hij, Ne.symm hij, αc i j hij]
      · rw [weight hB i j k l (by tauto)]
        have a1 : ¬ (j = k ∧ l = i) := fun h => p2 ⟨h.2.symm, h.1⟩
        simp [a1, p1]
  refine ⟨α, β, fun X Y => ?_⟩
  -- expand both arguments on matrix units
  have expand : B X Y = ∑ i, ∑ j, ∑ k, ∑ l, X i j * Y k l * unitVal B i j k l := by
    rw [lin_expand B X, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, smul_eq_mul, lin_expand (B (single i j (1 : K))) Y, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_eq_mul, unitVal]
    ring
  rw [expand]
  simp only [formula, mul_add, Finset.sum_add_distrib]
  congr 1
  · -- the tr(XY) part
    rw [trace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [diag_apply, mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j, Finset.sum_eq_single i]
    · simp; ring
    · intro l _ hl; simp [hl, Ne.symm hl]
    · simp
    · intro k _ hk
      refine Finset.sum_eq_zero fun l _ => ?_
      simp [hk, Ne.symm hk]
    · simp
  · -- the tr(X) tr(Y) part
    rw [trace, trace, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [diag_apply, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single k]
      · simp [diag_apply]; ring
      · intro l _ hl; simp [hl, Ne.symm hl]
      · simp
    · intro j _ hj
      refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
      simp [hj, Ne.symm hj]
    · simp

/-- **The commutant of the matchings.** For n ≥ 2, a linear map φ of Mₙ(K) commuting with every
matching (φ(AX − XA) = A·φ(X) − φ(X)·A) is α·X + β·tr(X)·1. On the GNS space L²(Mₙ), with
Ω = 1/√n, the map X ↦ tr(X)·1/n is |Ω⟩⟨Ω|: the commutant is span{1, |Ω⟩⟨Ω|}. -/
theorem equivariant_classification (φ : M →ₗ[K] M)
    (hφ : ∀ A X : M, φ (A * X - X * A) = A * φ X - φ X * A) :
    ∃ α β : K, ∀ X : M, φ X = α • X + (β * X.trace) • (1 : M) := by
  let B : M →ₗ[K] M →ₗ[K] K :=
    LinearMap.mk₂ K (fun X Y => (φ X * Y).trace)
      (fun X X' Y => by simp only [map_add, add_mul, trace_add])
      (fun c X Y => by simp only [map_smul, smul_mul_assoc, trace_smul, smul_eq_mul])
      (fun X Y Y' => by simp only [mul_add, trace_add])
      (fun c X Y => by simp only [mul_smul_comm, trace_smul, smul_eq_mul])
  have hB : IsInvariant B := by
    intro A X Y
    simp only [B, LinearMap.mk₂_apply, hφ]
    rw [sub_mul, mul_sub, trace_sub, trace_sub]
    simp only [mul_assoc]
    rw [trace_mul_comm A (φ X * Y), mul_assoc]
    ring
  obtain ⟨α, β, h⟩ := invariant_bilinear_classification hn B hB
  refine ⟨α, β, fun X => ?_⟩
  rw [ext_iff_trace_mul_right]
  intro Y
  have := h X Y
  simp only [B, LinearMap.mk₂_apply] at this
  rw [this, add_mul, trace_add, smul_mul_assoc, trace_smul, smul_mul_assoc, one_mul, trace_smul,
    smul_eq_mul, smul_eq_mul]
  ring

end Classification

end ChainTheory.Pairing
