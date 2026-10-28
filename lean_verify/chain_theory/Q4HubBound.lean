import Mathlib

/-!
# Q4 · Does Chain Theory's hub bound transfer to M₄?

Chain Theory (Wissner-Gross, compendium release 0.1, 23 Oct 2026), Theorem 197.3:
"A hub assembly is a ququart carrying a qubit pair among its qubit legs; the pair takes two of
its four ends and every move applies at a site with spare alone, so a hub assembly admits at
most the third generation at the hub dimension four."

The bound rests on the *valence law*, "at most d pairs at a qudit of dimension d", which
Chain Theory reads off Definition 1.5: a read gives the qudit its only basis, "one direction
for each pair the qudit meets". Shared qudits are carried "one copy per pair" (Definition 1.3
as glossed in the compendium's introduction), so monogamy is never violated.

This file asks which reading of "a ququart has four ends" the Tree's M₄ supports.

* **Additive reading (ends = directions of a frame).** A pair at a site takes a direction:
  a nonzero idempotent, pairwise orthogonal to the others. Theorem A: in Mₙ(K) there are at
  most n of them. This is the valence law, and it holds in M₄ as a theorem of linear algebra.
  Theorem B: an in-leg plus three legs saturate M₄ (no spare direction is left). Theorem C:
  at a qutrit carrying two core links there is at most one spare direction, so three core
  sites admit at most three attachments in total.

* **Multiplicative reading (ends = tensor factors).** A leg of dimension d is a unital copy of
  M_d inside the site's algebra. Theorem D: a unital algebra map M_m(K) → M_n(K) exists only
  if m ∣ n. So M₄ carries no qutrit tensor factor (3 ∤ 4) and no three-qubit factor (8 ∤ 4);
  the qubit pair alone (M₂ ⊗ M₂ ≅ M₄) exhausts it.

Verdict recorded in `docs/chain-theory/09_results_second_pass.md`: the counting behind 197.3
is a theorem about frames of M₄ and M₃ (additive), not about tensor factorisations of M₄
(multiplicative). A qutrit fits inside a ququart only as a corner, the 3 ⊕ 1 split of the
Tree's L13, never as a tensor factor.

Genuine Mathlib proofs; no `sorry`, no `native_decide`, no new axioms.
-/

open Matrix

namespace ChainTheory.Q4

variable {K : Type*} [Field K]

/-- A matrix that kills every vector is zero. -/
private lemma eq_zero_of_mulVec_eq_zero {n : ℕ} {P : Matrix (Fin n) (Fin n) K}
    (h : ∀ w : Fin n → K, P *ᵥ w = 0) : P = 0 := by
  classical
  ext a b
  have := congrFun (h (Pi.single b 1)) a
  simpa [mulVec_single_one] using this

/-- **Theorem A (the valence law, additive reading).** Nonzero idempotents of Mₙ(K) that are
pairwise orthogonal (`P i * P j = 0` for `i ≠ j`) number at most `n`. Read: a site of
dimension `n` has at most `n` ends. -/
theorem card_le_of_orthogonal_idempotents {n : ℕ} {ι : Type*} [Fintype ι]
    (P : ι → Matrix (Fin n) (Fin n) K)
    (hidem : ∀ i, P i * P i = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0)
    (hne : ∀ i, P i ≠ 0) :
    Fintype.card ι ≤ n := by
  classical
  have hw : ∀ i, ∃ w : Fin n → K, P i *ᵥ w ≠ 0 := by
    intro i
    by_contra h
    push Not at h
    exact hne i (eq_zero_of_mulVec_eq_zero h)
  choose w hw using hw
  -- one nonzero vector in the range of each idempotent
  let v : ι → (Fin n → K) := fun i => P i *ᵥ w i
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 : P j *ᵥ (∑ i, g i • v i) = g j • v j := by
      rw [mulVec_sum, Finset.sum_eq_single j]
      · simp only [v, mulVec_smul, mulVec_mulVec, hidem]
      · intro i _ hij
        simp only [v, mulVec_smul, mulVec_mulVec, horth j i (Ne.symm hij), zero_mulVec,
          smul_zero]
      · simp
    rw [hg, mulVec_zero] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right (hw j)
  simpa using hli.fintype_card_le_finrank

/-- **Theorem B (the hub is saturated).** At a ququart, an in-leg (`none`) and three legs
(`some i`) taking pairwise orthogonal nonzero idempotent ends leave no spare: no further
nonzero idempotent is orthogonal to all four. Read: no move applies at a full hub. -/
theorem hub_saturated (P : Option (Fin 3) → Matrix (Fin 4) (Fin 4) K)
    (hidem : ∀ i, P i * P i = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0)
    (hne : ∀ i, P i ≠ 0) :
    ¬ ∃ Q : Matrix (Fin 4) (Fin 4) K, Q * Q = Q ∧ Q ≠ 0 ∧
        ∀ i, Q * P i = 0 ∧ P i * Q = 0 := by
  rintro ⟨Q, hQ, hQne, hQorth⟩
  let R : Option (Option (Fin 3)) → Matrix (Fin 4) (Fin 4) K := fun o => o.elim Q P
  have h := card_le_of_orthogonal_idempotents R
    (by rintro (_ | i) <;> simp [R, hQ, hidem])
    (by
      rintro (_ | i) (_ | j) hij
      · exact absurd rfl hij
      · exact (hQorth j).1
      · exact (hQorth i).2
      · exact horth i j (fun h => hij (by rw [h])))
    (by rintro (_ | i) <;> simp [R, hQne, hne])
  simp at h

/-- **Theorem B′ (the hub's legs).** At a ququart carrying an in-leg, at most three legs fit. -/
theorem hub_legs_le_three {ι : Type*} [Fintype ι]
    (P : Option ι → Matrix (Fin 4) (Fin 4) K)
    (hidem : ∀ i, P i * P i = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0)
    (hne : ∀ i, P i ≠ 0) :
    Fintype.card ι ≤ 3 := by
  have := card_le_of_orthogonal_idempotents P hidem horth hne
  simp at this
  omega

/-- **Theorem C (core room).** At a qutrit carrying two core links (`Sum.inl`), at most one
further end (`Sum.inr`) fits. -/
theorem core_spare_le_one {A : Type*} [Fintype A]
    (P : Fin 2 ⊕ A → Matrix (Fin 3) (Fin 3) K)
    (hidem : ∀ i, P i * P i = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0)
    (hne : ∀ i, P i ≠ 0) :
    Fintype.card A ≤ 1 := by
  have := card_le_of_orthogonal_idempotents P hidem horth hne
  simp at this
  omega

/-- **Theorem C′ (the count of three).** Three core qutrits, each carrying its two links of
the closed triangle, admit at most three attachments in total. -/
theorem core_attachments_le_three (A : Fin 3 → Type*) [∀ s, Fintype (A s)]
    (P : ∀ s, Fin 2 ⊕ A s → Matrix (Fin 3) (Fin 3) K)
    (hidem : ∀ s i, P s i * P s i = P s i)
    (horth : ∀ s i j, i ≠ j → P s i * P s j = 0)
    (hne : ∀ s i, P s i ≠ 0) :
    ∑ s, Fintype.card (A s) ≤ 3 := by
  have h : ∀ s, Fintype.card (A s) ≤ 1 := fun s =>
    core_spare_le_one (P s) (hidem s) (horth s) (hne s)
  calc ∑ s, Fintype.card (A s) ≤ ∑ _s : Fin 3, 1 := Finset.sum_le_sum fun s _ => h s
    _ = 3 := by simp

/-- The hypotheses of `hub_saturated` are met: the four diagonal matrix units of M₄ are an
in-leg and three legs. (A guard against a vacuous theorem.) -/
theorem hub_hypotheses_satisfiable :
    ∃ P : Option (Fin 3) → Matrix (Fin 4) (Fin 4) ℂ,
      (∀ i, P i * P i = P i) ∧ (∀ i j, i ≠ j → P i * P j = 0) ∧ (∀ i, P i ≠ 0) := by
  classical
  let f : Option (Fin 3) → Fin 4 := fun o => o.elim 0 Fin.succ
  have hf : Function.Injective f := by
    rintro (_ | a) (_ | b) h <;> simp_all [f, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]
  refine ⟨fun o => Matrix.single (f o) (f o) 1, ?_, ?_, ?_⟩
  · intro i; simp [Matrix.single_mul_single_same]
  · intro i j hij
    exact Matrix.single_mul_single_of_ne (h := hf.ne hij) ..
  · intro i h
    have := congrFun (congrFun h (f i)) (f i)
    simp at this

/-! ### The multiplicative reading -/

/-- The trace of an idempotent matrix is the dimension of its range. -/
private lemma trace_idempotent_eq_finrank {n : ℕ} {E : Matrix (Fin n) (Fin n) K}
    (hE : E * E = E) :
    E.trace = (Module.finrank K (LinearMap.range (Matrix.toLin' E)) : K) := by
  have hproj : IsIdempotentElem (Matrix.toLin' E) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hE]
  rw [← Matrix.trace_toLin'_eq]
  exact (LinearMap.IsIdempotentElem.isProj_range _ hproj).trace

/-- **Theorem D (the multiplicative valence).** Over a field of characteristic zero, a unital
algebra map M_m(K) → M_n(K) exists only if `m ∣ n`. -/
theorem dvd_of_unital_algHom [CharZero K] {m n : ℕ}
    (φ : Matrix (Fin m) (Fin m) K →ₐ[K] Matrix (Fin n) (Fin n) K) : m ∣ n := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    -- M₀ is the zero ring, so φ 1 = φ 0 forces 1 = 0 in Mₙ, i.e. n = 0
    have h10 : (1 : Matrix (Fin 0) (Fin 0) K) = 0 := Subsingleton.elim _ _
    have : (1 : Matrix (Fin n) (Fin n) K) = 0 := by
      rw [← map_one φ, h10, map_zero]
    have hn : n = 0 := by
      by_contra hn
      have := congrFun (congrFun this ⟨0, Nat.pos_of_ne_zero hn⟩) ⟨0, Nat.pos_of_ne_zero hn⟩
      simp at this
    simp [hn]
  -- the images of the diagonal matrix units
  let i0 : Fin m := ⟨0, hm⟩
  let E : Fin m → Matrix (Fin n) (Fin n) K := fun i => φ (Matrix.single i i 1)
  have hE : ∀ i, E i * E i = E i := by
    intro i
    simp only [E, ← map_mul, Matrix.single_mul_single_same, mul_one]
  -- all have the same trace, by moving through the off-diagonal units
  have htr : ∀ i, (E i).trace = (E i0).trace := by
    intro i
    have h1 : Matrix.single i i (1 : K) = Matrix.single i i0 1 * Matrix.single i0 i 1 := by
      rw [Matrix.single_mul_single_same, mul_one]
    have h2 : Matrix.single i0 i0 (1 : K) = Matrix.single i0 i 1 * Matrix.single i i0 1 := by
      rw [Matrix.single_mul_single_same, mul_one]
    simp only [E, h1, h2, map_mul]
    exact Matrix.trace_mul_comm _ _
  -- they sum to the identity
  have hsum : ∑ i, E i = 1 := by
    simp only [E, ← map_sum]
    rw [Matrix.sum_single_one, map_one]
  -- so m · tr(E i0) = n, and tr(E i0) is a natural number
  have key : (m : K) * (E i0).trace = n := by
    have : ∑ i, (E i).trace = (n : K) := by
      rw [← Matrix.trace_sum, hsum, Matrix.trace_one, Fintype.card_fin]
    simpa [htr, Finset.sum_const, nsmul_eq_mul] using this
  rw [trace_idempotent_eq_finrank (hE i0)] at key
  have : m * Module.finrank K (LinearMap.range (Matrix.toLin' (E i0))) = n := by
    exact_mod_cast key
  exact ⟨_, this.symm⟩

/-- A ququart carries no qutrit as a tensor factor: there is no unital algebra map
M₃(ℂ) → M₄(ℂ). (As a corner, the 3 ⊕ 1 split, it fits; see Theorem A.) -/
theorem no_qutrit_factor_in_ququart :
    IsEmpty (Matrix (Fin 3) (Fin 3) ℂ →ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ) :=
  ⟨fun φ => absurd (dvd_of_unital_algHom φ) (by decide)⟩

/-- A ququart carries no three qubits as tensor factors: there is no unital algebra map
M₈(ℂ) → M₄(ℂ). -/
theorem no_three_qubit_factor_in_ququart :
    IsEmpty (Matrix (Fin 8) (Fin 8) ℂ →ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ) :=
  ⟨fun φ => absurd (dvd_of_unital_algHom φ) (by decide)⟩

end ChainTheory.Q4
