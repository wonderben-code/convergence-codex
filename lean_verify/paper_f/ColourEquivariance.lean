/-
  ColourEquivariance: 4 → 3₁ ⊕ 1₋₃ as a Statement about an ACTION
  ==============================================================

  `RepDecomposition.lean` proves the Pati-Salam colour decomposition at the
  level of vector spaces: (Fin 3 → ℂ) × (Fin 1 → ℂ) ≃ₗ[ℂ] (Fin 4 → ℂ), plus
  the dimension counts. The Phase-0 audit graded it GENUINE and recorded one
  overclaim: its docstring says the split is "equivariant", and **no group or
  algebra action appears anywhere in the file**, so the word was carrying no
  content. A splitting of ℂ⁴ into a 3 and a 1 is not physics; a splitting
  INTO SUBREPRESENTATIONS, with charges, is.

  This file supplies the action and makes the claim a theorem.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `emb` — the block embedding of 3×3 matrices into (3+1)×(3+1) matrices,
     X ↦ [[X,0],[0,0]], is an embedding of ALGEBRAS and of LIE ALGEBRAS:
     `emb_add`, `emb_smul`, `emb_mul`, `emb_bracket`, `emb_injective`, and
     `trace_emb` (so traceless goes to traceless — su(3) really lands inside
     su(4)).
  2. `quarkSub`, `leptonSub` — the colour triplet and the lepton singlet as
     honest `Submodule`s, with `isCompl_quark_lepton`: they are complementary,
     so ℂ⁴ = 3 ⊕ 1 as an internal direct sum and not merely up to an
     isomorphism chosen by hand.
  3. **`quark_invariant`, `lepton_invariant`** — both are INVARIANT under the
     embedded su(3): the splitting is a splitting into subrepresentations.
     This is the content the word "equivariant" was claiming. (In fact
     `emb_mulVec_mem_quark` is stronger: the embedded algebra maps EVERYTHING
     into the triplet.)
  4. `lepton_trivial` — su(3) acts as ZERO on the singlet, so it is the
     trivial representation, not merely an invariant line.
  5. `quark_faithful` — su(3) acts non-trivially on the triplet, so the two
     summands are genuinely different representations.
  6. **`charge_quark`, `charge_lepton`** — the U(1) generator
     B−L = diag(1,1,1,−3) is traceless (`trace_bMinusL`), commutes with the
     embedded su(3) (`bMinusL_comm`), and acts as **+1 on the triplet and −3
     on the singlet**. Those two eigenvalues are the subscripts in "3₁ ⊕ 1₋₃";
     until now they appeared only in prose.
  7. **`quark_irreducible`** — the triplet is IRREDUCIBLE under the traceless
     matrices: every nonzero invariant subspace is everything. So 3 ⊕ 1 is the
     decomposition into irreducibles, not just some invariant splitting. The
     proof is the elementary-matrix argument: `single i j 1` is traceless for
     i ≠ j and moves any nonzero coordinate onto any basis vector.

  NOT proven here:

  * Anything at GROUP level. This is the Lie-algebra action (matrices acting
    by multiplication); SU(3) and U(1) as groups, and the exponential map
    between the two pictures, do not appear.
  * That su(3) ⊕ u(1) is the FULL stabiliser of the splitting, or that this
    embedding is the unique one up to conjugacy.
  * Any connection to the cascade: `Fin 3 ⊕ Fin 1` here is an index type, and
    nothing identifies it with a cascade level. `RepDecomposition`'s
    identification of the 4 with a cascade Hilbert space is unchanged and is
    not strengthened by anything here.
  * The physical reading of B−L, and the normalisation of the charges: the
    generator diag(1,1,1,−3) is traceless and that pins its RATIO of
    eigenvalues, not its scale.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Order.Disjoint

open Matrix

noncomputable section

namespace ColourEquivariance

/-- The colour index: three quark colours and one lepton "colour". -/
abbrev Col := Fin 3 ⊕ Fin 1

/-! ## 1. su(3) ↪ su(4) as a block embedding -/

/-- The embedding X ↦ [[X, 0], [0, 0]]. -/
def emb (X : Matrix (Fin 3) (Fin 3) ℂ) : Matrix Col Col ℂ :=
  Matrix.fromBlocks X 0 0 0

theorem emb_add (X Y : Matrix (Fin 3) (Fin 3) ℂ) : emb (X + Y) = emb X + emb Y := by
  unfold emb
  ext i j
  cases i <;> cases j <;> simp

theorem emb_sub (X Y : Matrix (Fin 3) (Fin 3) ℂ) : emb (X - Y) = emb X - emb Y := by
  unfold emb
  ext i j
  cases i <;> cases j <;> simp

theorem emb_smul (c : ℂ) (X : Matrix (Fin 3) (Fin 3) ℂ) : emb (c • X) = c • emb X := by
  unfold emb
  ext i j
  cases i <;> cases j <;> simp

theorem emb_mul (X Y : Matrix (Fin 3) (Fin 3) ℂ) : emb (X * Y) = emb X * emb Y := by
  unfold emb
  rw [Matrix.fromBlocks_multiply]
  simp

/-- **The embedding preserves the Lie bracket**, so it embeds su(3) as a Lie
    subalgebra and not merely as a set of matrices. -/
theorem emb_bracket (X Y : Matrix (Fin 3) (Fin 3) ℂ) :
    emb (X * Y - Y * X) = emb X * emb Y - emb Y * emb X := by
  rw [emb_sub, emb_mul, emb_mul]

/-- **It preserves the trace**, so traceless matrices go to traceless
    matrices: su(3) lands inside su(4). -/
@[simp] theorem trace_emb (X : Matrix (Fin 3) (Fin 3) ℂ) :
    (emb X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, emb]
  rw [Fintype.sum_sum_type]
  simp

theorem emb_injective {X Y : Matrix (Fin 3) (Fin 3) ℂ} (h : emb X = emb Y) : X = Y := by
  ext i j
  have := congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  simpa [emb] using this

/-! ## 2. The two subspaces, and that they split ℂ⁴ -/

/-- The colour triplet: vectors supported on the three quark colours. -/
def quarkSub : Submodule ℂ (Col → ℂ) where
  carrier := {v | v (Sum.inr 0) = 0}
  add_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq] at *; simp [ha, hb]
  zero_mem' := by simp
  smul_mem' := by intro c a ha; simp only [Set.mem_setOf_eq] at *; simp [ha]

/-- The lepton singlet: vectors supported on the fourth index. -/
def leptonSub : Submodule ℂ (Col → ℂ) where
  carrier := {v | ∀ i : Fin 3, v (Sum.inl i) = 0}
  add_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq] at *; intro i; simp [ha i, hb i]
  zero_mem' := by simp
  smul_mem' := by intro c a ha; simp only [Set.mem_setOf_eq] at *; intro i; simp [ha i]

theorem mem_quarkSub {v : Col → ℂ} : v ∈ quarkSub ↔ v (Sum.inr 0) = 0 := Iff.rfl

theorem mem_leptonSub {v : Col → ℂ} : v ∈ leptonSub ↔ ∀ i : Fin 3, v (Sum.inl i) = 0 :=
  Iff.rfl

/-- **ℂ⁴ = 3 ⊕ 1 as an internal direct sum.** -/
theorem isCompl_quark_lepton : IsCompl quarkSub leptonSub := by
  constructor
  · rw [disjoint_iff]
    ext v
    simp only [Submodule.mem_inf, Submodule.mem_bot]
    constructor
    · rintro ⟨hq, hl⟩
      funext i
      cases i with
      | inl a => simpa using hl a
      | inr b =>
          have : b = 0 := Subsingleton.elim _ _
          subst this
          simpa using hq
    · rintro rfl
      exact ⟨by simp, by simp⟩
  · rw [codisjoint_iff]
    ext v
    simp only [Submodule.mem_top, iff_true]
    have hsplit : v = (fun i => if i = Sum.inr 0 then 0 else v i)
        + (fun i => if i = Sum.inr 0 then v i else 0) := by
      funext i
      by_cases h : i = Sum.inr 0 <;> simp [h]
    rw [hsplit]
    refine Submodule.add_mem_sup ?_ ?_
    · simp [mem_quarkSub]
    · intro i
      simp

/-! ## 3. The splitting is a splitting into SUBREPRESENTATIONS -/

/-- In fact the embedded su(3) maps EVERYTHING into the triplet — its image
    is annihilated on the lepton line. Invariance of the triplet is the
    special case. -/
theorem emb_mulVec_mem_quark (X : Matrix (Fin 3) (Fin 3) ℂ) (v : Col → ℂ) :
    emb X *ᵥ v ∈ quarkSub := by
  have h : (emb X *ᵥ v) (Sum.inr 0) = 0 := by
    simp [emb, Matrix.mulVec, dotProduct]
  exact h

/-- **The triplet is invariant** under the embedded su(3). -/
theorem quark_invariant (X : Matrix (Fin 3) (Fin 3) ℂ) {v : Col → ℂ}
    (_hv : v ∈ quarkSub) : emb X *ᵥ v ∈ quarkSub :=
  emb_mulVec_mem_quark X v

/-- **su(3) acts as ZERO on the singlet**: it is the trivial representation.
    (`lepton_invariant` follows, but the stronger statement is the one that
    says "1" and not merely "an invariant line".) -/
theorem lepton_trivial (X : Matrix (Fin 3) (Fin 3) ℂ) {v : Col → ℂ}
    (hv : v ∈ leptonSub) : emb X *ᵥ v = 0 := by
  funext i
  cases i with
  | inl a =>
      simp only [emb, Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [Fintype.sum_sum_type]
      simp [mem_leptonSub.mp hv]
  | inr b =>
      simp [emb, Matrix.mulVec, dotProduct]

theorem lepton_invariant (X : Matrix (Fin 3) (Fin 3) ℂ) {v : Col → ℂ}
    (hv : v ∈ leptonSub) : emb X *ᵥ v ∈ leptonSub := by
  rw [lepton_trivial X hv]
  exact Submodule.zero_mem _

/-- Non-vacuity: su(3) does NOT act as zero on the triplet, so the two
    summands are genuinely different representations and the invariance above
    is not the trivial statement that everything is invariant. -/
theorem quark_faithful :
    ∃ (X : Matrix (Fin 3) (Fin 3) ℂ) (v : Col → ℂ),
      X.trace = 0 ∧ v ∈ quarkSub ∧ emb X *ᵥ v ≠ 0 := by
  refine ⟨Matrix.single 0 1 1, Sum.elim ![0, 1, 0] ![0], ?_, ?_, ?_⟩
  · exact Matrix.trace_single_eq_of_ne 0 1 1 (by decide)
  · simp [mem_quarkSub]
  · intro h
    have h1 := congrFun h (Sum.inl 0)
    simp [emb, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.single] at h1

/-! ## 4. The U(1) charges: the subscripts in 3₁ ⊕ 1₋₃ -/

/-- The B−L generator, normalised to be traceless. -/
def bMinusL : Matrix Col Col ℂ :=
  Matrix.fromBlocks 1 0 0 ((-3 : ℂ) • 1)

@[simp] theorem trace_bMinusL : bMinusL.trace = 0 := by
  simp only [Matrix.trace, Matrix.diag, bMinusL]
  rw [Fintype.sum_sum_type]
  simp

/-- The U(1) commutes with the embedded su(3), so the two act simultaneously
    — which is what makes "3₁" a single label rather than two. -/
theorem bMinusL_comm (X : Matrix (Fin 3) (Fin 3) ℂ) :
    bMinusL * emb X = emb X * bMinusL := by
  unfold bMinusL emb
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- **Charge +1 on the colour triplet.** -/
theorem charge_quark {v : Col → ℂ} (hv : v ∈ quarkSub) : bMinusL *ᵥ v = v := by
  funext i
  cases i with
  | inl a =>
      simp only [bMinusL, Matrix.mulVec, dotProduct]
      rw [Fintype.sum_sum_type]
      simp [Matrix.one_apply]
  | inr b =>
      have hb : b = 0 := Subsingleton.elim _ _
      subst hb
      simp only [bMinusL, Matrix.mulVec, dotProduct]
      rw [Fintype.sum_sum_type]
      simp [mem_quarkSub.mp hv]

/-- **Charge −3 on the lepton singlet.** The ratio 1 : (−3) is forced by
    tracelessness, and it is exactly the Pati-Salam assignment. -/
theorem charge_lepton {v : Col → ℂ} (hv : v ∈ leptonSub) :
    bMinusL *ᵥ v = (-3 : ℂ) • v := by
  funext i
  cases i with
  | inl a =>
      simp only [bMinusL, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [Fintype.sum_sum_type]
      simp [Matrix.one_apply, mem_leptonSub.mp hv]
  | inr b =>
      have hb : b = 0 := Subsingleton.elim _ _
      subst hb
      simp only [bMinusL, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      rw [Fintype.sum_sum_type]
      simp [Matrix.one_apply]

/-! ## 5. The triplet is irreducible -/

/-- **The colour triplet is IRREDUCIBLE** under the traceless 3×3 matrices:
    any invariant subspace containing a nonzero vector is everything. So
    3 ⊕ 1 is the decomposition into irreducibles.

    The proof is the elementary-matrix argument: `single i j 1` is traceless
    for i ≠ j and carries the j-th coordinate onto the i-th basis vector. -/
theorem quark_irreducible (W : Submodule ℂ (Fin 3 → ℂ)) (hne : W ≠ ⊥)
    (hinv : ∀ X : Matrix (Fin 3) (Fin 3) ℂ, X.trace = 0 → ∀ v ∈ W, X *ᵥ v ∈ W) :
    W = ⊤ := by
  obtain ⟨v, hvW, hv0⟩ := (Submodule.ne_bot_iff W).mp hne
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, v j ≠ 0 := by
    by_contra hc
    rw [not_exists] at hc
    exact hv0 (funext fun j => not_not.mp (hc j))
  -- every basis vector e i with i ≠ j lies in W
  have hbasis : ∀ i : Fin 3, i ≠ j → (Pi.single i 1 : Fin 3 → ℂ) ∈ W := by
    intro i hij
    have hmem := hinv (Matrix.single i j (v j)⁻¹) ?_ v hvW
    · have hval : Matrix.single i j (v j)⁻¹ *ᵥ v = Pi.single i (1 : ℂ) := by
        rw [Matrix.single_mulVec, inv_mul_cancel₀ hj]
        funext k
        by_cases hk : k = i <;> simp [Function.update, Pi.single_apply, hk]
      rwa [hval] at hmem
    · exact Matrix.trace_single_eq_of_ne i j _ hij
  -- and so does e j, by moving one of them back
  have hj' : (Pi.single j 1 : Fin 3 → ℂ) ∈ W := by
    obtain ⟨i, hij⟩ : ∃ i : Fin 3, i ≠ j := by
      fin_cases j
      exacts [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]
    have hmem := hinv (Matrix.single j i 1) (Matrix.trace_single_eq_of_ne j i 1
      (fun h => hij h.symm)) _ (hbasis i hij)
    have hval : Matrix.single j i (1 : ℂ) *ᵥ (Pi.single i 1 : Fin 3 → ℂ)
        = (Pi.single j 1 : Fin 3 → ℂ) := by
      rw [Matrix.single_mulVec]
      funext k
      by_cases hk : k = j <;> simp [Function.update, Pi.single_apply, hk]
    rwa [hval] at hmem
  -- the basis vectors span
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ i : Fin 3, w i • (Pi.single i 1 : Fin 3 → ℂ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hw]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  by_cases hij : i = j
  · subst hij; exact hj'
  · exact hbasis i hij

end ColourEquivariance
