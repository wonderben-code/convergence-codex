/-
  IdempotentRankInvariant.lean — M₂(ℍ) ≇ M₄(ℝ), and with it
  Cl(1,3;ℝ) ≇ Cl(3,1;ℝ): the two Minkowski conventions give genuinely
  different algebras.

  `CliffordRealMinkowski` proved Cl(1,3;ℝ) ≅ M₂(ℍ) and
  `CliffordRealMajorana` proved Cl(3,1;ℝ) ≅ M₄(ℝ). Both files say, in
  their headers, that having the two isomorphisms does NOT prove the
  two Clifford algebras inequivalent — that needs M₂(ℍ) ≇ M₄(ℝ), which
  neither file verifies. WALLS.md W7 carried it as residue and named
  two candidate invariants. This file supplies one of them and closes
  the residue.

  THE INVARIANT: how many pairwise-orthogonal nonzero idempotents
  summing to 1 an algebra admits. M₄(ℝ) admits four (the diagonal
  matrix units). M₂(ℍ) admits at most two. Since the count transports
  along any ring isomorphism, the two are not isomorphic — not even as
  rings, let alone as ℝ-algebras.

  WHY THE M₂(ℍ) BOUND IS THE WORK, AND HOW IT IS DONE HERE. The
  textbook argument counts ℍ-dimensions of a direct-sum decomposition
  of ℍ², which needs rank additivity for modules over a NONCOMMUTATIVE
  division ring — exactly what W7 flagged as the uncertain Mathlib
  dependency. This file avoids that entirely and works over ℝ
  throughout:

  * M₂(ℍ) acts on ℍ² by `mulVec`, ℝ-linearly (`leftMulVec`), and the
    action is multiplicative, so an idempotent matrix gives an
    idempotent ℝ-endomorphism of an 8-dimensional real space.
  * For an idempotent ℝ-endomorphism, Mathlib's `IsProj.trace` gives
    trace = finrank of the range. Traces add, and the idempotents sum
    to 1, so the ranges' dimensions sum to exactly 8.
  * The one genuinely quaternionic step: the range of a NONZERO such
    endomorphism has real dimension at least 4. Reason: the range
    contains some v ≠ 0, and it is stable under RIGHT multiplication
    by quaternions (which commutes with the left matrix action), so it
    contains the image of the injective ℝ-linear map q ↦ v·q from a
    4-dimensional space.
  * Four nonzero orthogonal idempotents would then need 16 ≤ 8.

  WHAT THIS FILE PROVES (exactly this, nothing more):
  1. `HasOrthIdem` — the invariant, and `HasOrthIdem.of_ringEquiv`:
     it transports along any ring isomorphism.
  2. `matrix4R_hasOrthIdem_four` — M₄(ℝ) admits four.
  3. `cliffordMajorana_hasOrthIdem_four` — hence so does Cl(3,1;ℝ),
     transported through `cliffordMajoranaEquiv`.
  4. **`orthIdem_card_le`** — the counting principle both bounds are
     instances of, stated for an arbitrary ring represented on a
     finite-dimensional REAL space: if every nonzero idempotent acts
     with range of dimension ≥ d, the family is capped by
     `n * d ≤ finrank V`. Neither bound below repeats the argument.
  5. `four_le_finrank_range` — the quaternionic dimension step above,
     which is `d = 4` for M₂(ℍ) on ℍ²; and `one_le_finrank_range4`,
     which is the same slot for M₄(ℝ) on ℝ⁴ and is the triviality that
     a nonzero matrix acts nontrivially.
  6. Both values PINNED, each with a witness and a matching bound:
     `matrix2H_orthIdem_le_two` + `matrix2H_hasOrthIdem_two` (exactly
     two — the second added folding review round 13, which asked
     precisely whether the bounded family was empty), and
     `matrix4R_orthIdem_le_four` + `matrix4R_hasOrthIdem_four` (exactly
     four). `orthIdem_values_pinned` states both together. The
     inequivalence needs only 4 > 2 and would survive with one side
     unpinned; knowing the values is what makes the invariant reusable.
  7. **`matrix2H_not_ringEquiv_matrix4R`** — M₂(ℍ) ≇ M₄(ℝ).
  8. **`clifford13_not_ringEquiv_clifford31`** — Cl(1,3;ℝ) ≇ Cl(3,1;ℝ),
     and `clifford13_not_algEquiv_clifford31` for the ℝ-algebra form.

  NOT proven here: the mod-8 periodicity table (this settles one pair
  of its entries, not the table); any spin-group statement; any
  physics; and no claim that this is the only or the best invariant —
  the Brauer-class route named in W7 is untouched.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import CliffordRealMinkowski
import CliffordRealMajorana

open Matrix
open scoped Quaternion

noncomputable section

namespace IdempotentRankInvariant

/-! ## 1. The invariant, and that it transports -/

/-- `HasOrthIdem A n`: the ring `A` contains `n` pairwise-orthogonal
NONZERO idempotents summing to `1`. Every clause matters — dropping
"nonzero" makes the property monotone in `n` and useless, and dropping
"summing to 1" loses the link to the identity that the trace argument
needs. -/
def HasOrthIdem (A : Type*) [Ring A] (n : ℕ) : Prop :=
  ∃ e : Fin n → A, (∀ i, e i * e i = e i) ∧ (∀ i j, i ≠ j → e i * e j = 0)
    ∧ (∀ i, e i ≠ 0) ∧ ∑ i, e i = 1

/-- **The invariant transports along a ring isomorphism** — which is
    what makes it usable as an obstruction. -/
theorem HasOrthIdem.of_ringEquiv {A B : Type*} [Ring A] [Ring B]
    (φ : A ≃+* B) {n : ℕ} (h : HasOrthIdem A n) : HasOrthIdem B n := by
  obtain ⟨e, hsq, horth, hne, hsum⟩ := h
  refine ⟨fun i => φ (e i), fun i => ?_, fun i j hij => ?_, fun i => ?_, ?_⟩
  · rw [← map_mul, hsq]
  · rw [← map_mul, horth i j hij, map_zero]
  · intro hc
    apply hne i
    have h1 : φ.symm (φ (e i)) = φ.symm 0 := congrArg φ.symm hc
    simpa using h1
  · rw [← map_sum, hsum, map_one]

/-! ## 2. The counting principle both bounds share

Both upper bounds — four for M₄(ℝ), two for M₂(ℍ) — are the same
argument at different parameters, and the argument is not about matrices
at all. Represent the ring on a finite-dimensional REAL space by a
multiplicative additive map; an idempotent then acts as an idempotent
endomorphism, whose trace is the dimension of its range; traces add and
the idempotents sum to 1, so the range dimensions total the dimension of
the space. If every nonzero idempotent's range has dimension at least
`d`, that caps the family at `finrank V / d`. -/

/-- An idempotent endomorphism of a finite-dimensional real space has
    trace equal to the dimension of its range. Stated abstractly so the
    freeness instances `IsProj.trace` needs are found in the general
    setting rather than at a concrete space (where instance search does
    not get there on its own). -/
private theorem trace_of_idempotent {V : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (f : V →ₗ[ℝ] V) (hf : IsIdempotentElem f) :
    LinearMap.trace ℝ V f = (Module.finrank ℝ (LinearMap.range f) : ℝ) :=
  ((LinearMap.isProj_range_iff_isIdempotentElem f).mpr hf).trace

/-- **The counting principle.** A ring represented on a
    finite-dimensional real space, multiplicatively and unitally, in
    which every nonzero idempotent acts with range of dimension at
    least `d`, admits at most `finrank V / d` pairwise-orthogonal
    nonzero idempotents summing to 1 — stated as `n * d ≤ finrank V` to
    keep it division-free. -/
theorem orthIdem_card_le
    {A : Type*} [Ring A] {V : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (ρ : A →+ (V →ₗ[ℝ] V))
    (hmul : ∀ x y : A, ρ (x * y) = ρ x ∘ₗ ρ y)
    (hone : ρ 1 = LinearMap.id) (d : ℕ)
    (hd : ∀ x : A, x * x = x → x ≠ 0 →
      d ≤ Module.finrank ℝ (LinearMap.range (ρ x)))
    {n : ℕ} (h : HasOrthIdem A n) :
    n * d ≤ Module.finrank ℝ V := by
  obtain ⟨e, hsq, _, hne, hsum⟩ := h
  have hidem : ∀ i, IsIdempotentElem (ρ (e i)) := by
    intro i
    change ρ (e i) * ρ (e i) = ρ (e i)
    rw [show ρ (e i) * ρ (e i) = ρ (e i) ∘ₗ ρ (e i) from rfl, ← hmul, hsq]
  have htr : ∀ i, LinearMap.trace ℝ V (ρ (e i))
      = (Module.finrank ℝ (LinearMap.range (ρ (e i))) : ℝ) :=
    fun i => trace_of_idempotent _ (hidem i)
  have htot : ∑ i, LinearMap.trace ℝ V (ρ (e i)) = (Module.finrank ℝ V : ℝ) := by
    rw [← map_sum, ← map_sum, hsum, hone, LinearMap.trace_id]
  have hge : ∀ i, (d : ℝ) ≤ LinearMap.trace ℝ V (ρ (e i)) := by
    intro i
    rw [htr i]
    exact_mod_cast hd _ (hsq i) (hne i)
  have hreal : ((n * d : ℕ) : ℝ) ≤ (Module.finrank ℝ V : ℝ) := by
    push_cast
    calc (n : ℝ) * (d : ℝ) = ∑ _i : Fin n, (d : ℝ) := by
          rw [Finset.sum_const]; simp [mul_comm]
      _ ≤ ∑ i, LinearMap.trace ℝ V (ρ (e i)) := Finset.sum_le_sum fun i _ => hge i
      _ = _ := htot
  exact_mod_cast hreal

/-! ## 3. M₄(ℝ) admits four -/

section Matrix4

/- The four diagonal matrix units share one uniform entrywise tactic;
the unused-argument linter is silenced for this block only. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-- The four diagonal matrix units of M₄(ℝ). -/
def P (i : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ := Matrix.single i i 1

theorem P_idem (i : Fin 4) : P i * P i = P i := by
  simp only [P]
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_four]

theorem P_orth (i j : Fin 4) (h : i ≠ j) : P i * P j = 0 := by
  simp only [P]
  ext a b
  fin_cases i <;> fin_cases j <;> simp_all

theorem P_ne_zero (i : Fin 4) : P i ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun h i) i
  simp [P, Matrix.single] at h1

theorem P_sum : ∑ i : Fin 4, P i = 1 := by
  simp only [P]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.single, Matrix.one_apply, Finset.sum_apply, Fin.sum_univ_four]

/-- **M₄(ℝ) admits four pairwise-orthogonal nonzero idempotents
    summing to 1.** -/
theorem matrix4R_hasOrthIdem_four :
    HasOrthIdem (Matrix (Fin 4) (Fin 4) ℝ) 4 :=
  ⟨P, P_idem, P_orth, P_ne_zero, P_sum⟩

end Matrix4

/-! ### …and at most four

The matching upper bound. Review round 13 left this open and named it
rather than implying it: the inequivalence only needs 4 > 2, so the
estate knew M₂(ℍ) admits exactly two but only that M₄(ℝ) admits at
LEAST four. With the counting principle factored out this costs one
instantiation at `d = 1` — over ℝ the quaternionic dimension step is
replaced by the triviality that a nonzero endomorphism has a nonzero
range. -/

section Matrix4Bound

/-- Left multiplication by a real matrix on ℝ⁴. -/
def leftMulVec4 (M : Matrix (Fin 4) (Fin 4) ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun v := M *ᵥ v
  map_add' x y := Matrix.mulVec_add M x y
  map_smul' c x := Matrix.mulVec_smul M c x

@[simp]
theorem leftMulVec4_apply (M : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    leftMulVec4 M v = M *ᵥ v := rfl

theorem leftMulVec4_mul (M N : Matrix (Fin 4) (Fin 4) ℝ) :
    leftMulVec4 (M * N) = leftMulVec4 M ∘ₗ leftMulVec4 N :=
  LinearMap.ext fun v => (Matrix.mulVec_mulVec v M N).symm

theorem leftMulVec4_one : leftMulVec4 1 = LinearMap.id :=
  LinearMap.ext fun v => Matrix.one_mulVec v

theorem leftMulVec4_add (M N : Matrix (Fin 4) (Fin 4) ℝ) :
    leftMulVec4 (M + N) = leftMulVec4 M + leftMulVec4 N :=
  LinearMap.ext fun v => Matrix.add_mulVec M N v

theorem leftMulVec4_zero : leftMulVec4 0 = 0 :=
  LinearMap.ext fun v => Matrix.zero_mulVec v

/-- The action bundled as an additive hom. -/
def leftMulVec4Hom :
    Matrix (Fin 4) (Fin 4) ℝ →+ ((Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) where
  toFun := leftMulVec4
  map_zero' := leftMulVec4_zero
  map_add' := leftMulVec4_add

theorem finrank_r4 : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by simp

/-- The real counterpart of `four_le_finrank_range`, and it is the easy
    one: a NONZERO matrix acts nontrivially (some column is nonzero), so
    its range is not the zero subspace. No idempotency is needed. -/
theorem one_le_finrank_range4 (e : Matrix (Fin 4) (Fin 4) ℝ) (h0 : e ≠ 0) :
    1 ≤ Module.finrank ℝ (LinearMap.range (leftMulVec4 e)) := by
  obtain ⟨i, j, hij⟩ : ∃ i j, e i j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (Matrix.ext fun a b => (hc a b).trans (Matrix.zero_apply a b).symm)
  have hv : leftMulVec4 e (Pi.single j 1) ≠ 0 := by
    intro hz
    apply hij
    have hzi := congrFun hz i
    rw [leftMulVec4_apply, Matrix.mulVec_single] at hzi
    simpa using hzi
  have hbot : LinearMap.range (leftMulVec4 e) ≠ ⊥ := by
    intro hb
    apply hv
    have hm : leftMulVec4 e (Pi.single j 1) ∈ LinearMap.range (leftMulVec4 e) :=
      LinearMap.mem_range_self _ _
    rw [hb, Submodule.mem_bot] at hm
    exact hm
  have hnz : Module.finrank ℝ (LinearMap.range (leftMulVec4 e)) ≠ 0 := fun hz =>
    hbot (Submodule.finrank_eq_zero.mp hz)
  omega

/-- **M₄(ℝ) admits at most four.** With `matrix4R_hasOrthIdem_four`
    this pins the invariant's value at M₄(ℝ) to exactly four. -/
theorem matrix4R_orthIdem_le_four {n : ℕ}
    (h : HasOrthIdem (Matrix (Fin 4) (Fin 4) ℝ) n) : n ≤ 4 := by
  have hb := orthIdem_card_le leftMulVec4Hom leftMulVec4_mul leftMulVec4_one 1
    (fun x _ h0 => one_le_finrank_range4 x h0) h
  rw [finrank_r4] at hb
  omega

end Matrix4Bound

/-- **Hence so does Cl(3,1;ℝ)** — pulled back through the Majorana
    isomorphism. A statement about the Clifford algebra itself,
    obtained as a payoff of having the isomorphism bundled. -/
theorem cliffordMajorana_hasOrthIdem_four :
    HasOrthIdem (CliffordAlgebra CliffordRealMajorana.Q₃₁) 4 :=
  HasOrthIdem.of_ringEquiv
    (CliffordRealMajorana.cliffordMajoranaEquiv.symm.toRingEquiv)
    matrix4R_hasOrthIdem_four

/-! ## 4. The quaternionic side: M₂(ℍ) admits at most two -/

section Matrix2H

/- Entrywise quaternion arithmetic again. Linters silenced for the
block, including `unreachableTactic`/`unnecessarySimpa`: the build's
option set lets `simp` finish two goals that bare `lake env lean`
cannot, so the closing `ring` and the `simpa` witness are load-bearing
under one configuration and flagged as redundant under the other. The
file must compile under BOTH, so they stay. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

/-- ℝ is central in ℍ, so the real scalar action commutes with
    quaternion multiplication. Mathlib does not find this by instance
    search here, and `Matrix.mulVec_smul` needs it. -/
instance smulCommRealQuaternion : SMulCommClass ℝ ℍ[ℝ] ℍ[ℝ] where
  smul_comm c p q := by
    change c • (p * q) = p * (c • q)
    ext <;> simp <;> ring

/-- Left multiplication by a quaternionic matrix on ℍ², as an ℝ-linear
    endomorphism of an 8-dimensional real space. The point of passing to
    ℝ is that all the dimension theory below is then over a FIELD. -/
def leftMulVec (M : Matrix (Fin 2) (Fin 2) ℍ[ℝ]) :
    (Fin 2 → ℍ[ℝ]) →ₗ[ℝ] (Fin 2 → ℍ[ℝ]) where
  toFun v := M *ᵥ v
  map_add' x y := Matrix.mulVec_add M x y
  map_smul' c x := Matrix.mulVec_smul M c x

@[simp]
theorem leftMulVec_apply (M : Matrix (Fin 2) (Fin 2) ℍ[ℝ]) (v : Fin 2 → ℍ[ℝ]) :
    leftMulVec M v = M *ᵥ v := rfl

theorem leftMulVec_mul (M N : Matrix (Fin 2) (Fin 2) ℍ[ℝ]) :
    leftMulVec (M * N) = leftMulVec M ∘ₗ leftMulVec N :=
  LinearMap.ext fun v => (Matrix.mulVec_mulVec v M N).symm

theorem leftMulVec_one : leftMulVec 1 = LinearMap.id :=
  LinearMap.ext fun v => Matrix.one_mulVec v

theorem leftMulVec_add (M N : Matrix (Fin 2) (Fin 2) ℍ[ℝ]) :
    leftMulVec (M + N) = leftMulVec M + leftMulVec N :=
  LinearMap.ext fun v => Matrix.add_mulVec M N v

theorem leftMulVec_zero : leftMulVec 0 = 0 :=
  LinearMap.ext fun v => Matrix.zero_mulVec v

/-- The action bundled as an additive hom, so `map_sum` is available. -/
def leftMulVecHom :
    Matrix (Fin 2) (Fin 2) ℍ[ℝ] →+ ((Fin 2 → ℍ[ℝ]) →ₗ[ℝ] (Fin 2 → ℍ[ℝ])) where
  toFun := leftMulVec
  map_zero' := leftMulVec_zero
  map_add' := leftMulVec_add

/-- ℍ² has real dimension 8. -/
theorem finrank_h2 : Module.finrank ℝ (Fin 2 → ℍ[ℝ]) = 8 := by
  rw [Module.finrank_pi_fintype]
  simp [Quaternion.finrank_eq_four]

instance : FiniteDimensional ℝ (Fin 2 → ℍ[ℝ]) :=
  FiniteDimensional.of_finrank_pos (by rw [finrank_h2]; norm_num)

/-- Right multiplication of a vector of quaternions by a quaternion.
    ℝ-linear because ℝ is central in ℍ, and the reason a nonzero range
    cannot be small. -/
def rightMul (v : Fin 2 → ℍ[ℝ]) : ℍ[ℝ] →ₗ[ℝ] (Fin 2 → ℍ[ℝ]) where
  toFun q := fun i => v i * q
  map_add' q r := funext fun i => by simp [mul_add]
  map_smul' c q := funext fun i => by simpa using mul_smul_comm c (v i) q

theorem rightMul_injective {v : Fin 2 → ℍ[ℝ]} (hv : v ≠ 0) :
    Function.Injective (rightMul v) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro q hq
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv (funext hc)
  have h1 : v i * q = 0 := congrFun hq i
  exact (mul_eq_zero_iff_left hi).mp h1

/-- **The quaternionic dimension step.** A nonzero idempotent matrix
    over ℍ has a range of real dimension at least 4 — the range contains
    some v ≠ 0 and is stable under RIGHT multiplication by quaternions,
    so it contains the image of the injective ℝ-linear map q ↦ v·q from
    a 4-dimensional space. This is the step the textbook argument does
    with ℍ-module rank; here it is ℝ-linear algebra plus the fact that
    ℍ has no zero divisors. -/
theorem four_le_finrank_range (e : Matrix (Fin 2) (Fin 2) ℍ[ℝ])
    (he : e * e = e) (h0 : e ≠ 0) :
    4 ≤ Module.finrank ℝ (LinearMap.range (leftMulVec e)) := by
  obtain ⟨i, j, hij⟩ : ∃ i j, e i j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (Matrix.ext fun a b => (hc a b).trans (Matrix.zero_apply a b).symm)
  set w : Fin 2 → ℍ[ℝ] := Pi.single j 1 with hw
  set v : Fin 2 → ℍ[ℝ] := e *ᵥ w with hv
  have hvi : v i = e i j := by
    rw [hv, hw, Matrix.mulVec_single]
    simp
  have hvne : v ≠ 0 := fun hc => hij (by rw [← hvi, hc]; rfl)
  have hev : e *ᵥ v = v := by
    rw [hv, Matrix.mulVec_mulVec, he]
  have hsub : LinearMap.range (rightMul v) ≤ LinearMap.range (leftMulVec e) := by
    rintro _ ⟨q, rfl⟩
    refine ⟨rightMul v q, funext fun a => ?_⟩
    have h1 : (e *ᵥ fun k => v k * q) a = (∑ k, e a k * v k) * q := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_mul, mul_assoc]
    have h2 : (∑ k, e a k * v k) = v a := by
      have h3 := congrFun hev a
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h3
    change (e *ᵥ fun k => v k * q) a = v a * q
    rw [h1, h2]
  have hrk : Module.finrank ℝ (LinearMap.range (rightMul v)) = 4 := by
    rw [LinearMap.finrank_range_of_inj (rightMul_injective hvne),
      Quaternion.finrank_eq_four]
  calc 4 = Module.finrank ℝ (LinearMap.range (rightMul v)) := hrk.symm
    _ ≤ Module.finrank ℝ (LinearMap.range (leftMulVec e)) :=
        Submodule.finrank_mono hsub

/-- **M₂(ℍ) admits at most two** pairwise-orthogonal nonzero
    idempotents summing to 1. -/
theorem matrix2H_orthIdem_le_two {n : ℕ}
    (h : HasOrthIdem (Matrix (Fin 2) (Fin 2) ℍ[ℝ]) n) : n ≤ 2 := by
  have hb := orthIdem_card_le leftMulVecHom leftMulVec_mul leftMulVec_one 4
    (fun x hx h0 => four_le_finrank_range x hx h0) h
  rw [finrank_h2] at hb
  omega

/-! ### The bound is attained -/

/-- The two diagonal matrix units of M₂(ℍ). -/
private def E2 : Fin 2 → Matrix (Fin 2) (Fin 2) ℍ[ℝ]
  | 0 => Matrix.single 0 0 1
  | 1 => Matrix.single 1 1 1

/-- **M₂(ℍ) does admit two** — so `matrix2H_orthIdem_le_two` is a SHARP
    bound, not a vacuous one. Without this the inequivalence proof would
    still go through, but nothing would rule out the possibility that the
    bound was accidentally bounding an empty family; review round 13
    flagged exactly that, and this is the answer. -/
theorem matrix2H_hasOrthIdem_two :
    HasOrthIdem (Matrix (Fin 2) (Fin 2) ℍ[ℝ]) 2 := by
  refine ⟨E2, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [E2, Matrix.single, Matrix.mul_apply, Fin.sum_univ_two]
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · ext a b <;> fin_cases a <;> fin_cases b <;>
        simp [E2, Matrix.single, Matrix.mul_apply, Fin.sum_univ_two]
    · ext a b <;> fin_cases a <;> fin_cases b <;>
        simp [E2, Matrix.single, Matrix.mul_apply, Fin.sum_univ_two]
    · exact absurd rfl hij
  · intro i; fin_cases i <;> intro hc <;>
      [(have := congrFun (congrFun hc 0) 0); (have := congrFun (congrFun hc 1) 1)] <;>
      simp [E2, Matrix.single] at this
  · refine Matrix.ext fun a b => ?_
    rw [Matrix.sum_apply, Fin.sum_univ_two]
    fin_cases a <;> fin_cases b <;> simp [E2, Matrix.single, Matrix.one_apply]

end Matrix2H

/-! ## 5. The obstruction, and the two Clifford algebras -/

/-- **M₂(ℍ) ≇ M₄(ℝ)** — two 16-dimensional real algebras that are not
    isomorphic even as rings. -/
theorem matrix2H_not_ringEquiv_matrix4R :
    IsEmpty (Matrix (Fin 2) (Fin 2) ℍ[ℝ] ≃+* Matrix (Fin 4) (Fin 4) ℝ) := by
  refine ⟨fun φ => ?_⟩
  have h4 : HasOrthIdem (Matrix (Fin 2) (Fin 2) ℍ[ℝ]) 4 :=
    HasOrthIdem.of_ringEquiv φ.symm matrix4R_hasOrthIdem_four
  have := matrix2H_orthIdem_le_two h4
  omega

/-- **Cl(1,3;ℝ) ≇ Cl(3,1;ℝ)** as rings: the two Minkowski sign
    conventions really do give different algebras. This is the fact
    both Clifford files had to state as a citation; it is now proven
    in the estate, and W7's residue item on it closes. -/
theorem clifford13_not_ringEquiv_clifford31 :
    IsEmpty (CliffordAlgebra CliffordRealMinkowski.Q₁₃ ≃+*
      CliffordAlgebra CliffordRealMajorana.Q₃₁) := by
  refine ⟨fun φ => ?_⟩
  exact matrix2H_not_ringEquiv_matrix4R.elim
    ((CliffordRealMinkowski.cliffordRealMinkowskiEquiv.symm.toRingEquiv.trans φ).trans
      CliffordRealMajorana.cliffordMajoranaEquiv.toRingEquiv)

/-- The ℝ-algebra form of the same statement. -/
theorem clifford13_not_algEquiv_clifford31 :
    IsEmpty (CliffordAlgebra CliffordRealMinkowski.Q₁₃ ≃ₐ[ℝ]
      CliffordAlgebra CliffordRealMajorana.Q₃₁) :=
  ⟨fun φ => clifford13_not_ringEquiv_clifford31.elim φ.toRingEquiv⟩

/-! ## 6. Both values pinned -/

/-- **The invariant is now known exactly on both algebras** — four for
    M₄(ℝ), two for M₂(ℍ), each with an explicit witness AND a matching
    bound. The inequivalence needed only 4 > 2 and would have survived
    with one side unpinned; this says what the invariant IS, which is
    what makes it reusable against other candidate algebras rather than
    a one-off separation of these two. -/
theorem orthIdem_values_pinned :
    (HasOrthIdem (Matrix (Fin 4) (Fin 4) ℝ) 4
        ∧ ∀ n, HasOrthIdem (Matrix (Fin 4) (Fin 4) ℝ) n → n ≤ 4)
      ∧ (HasOrthIdem (Matrix (Fin 2) (Fin 2) ℍ[ℝ]) 2
        ∧ ∀ n, HasOrthIdem (Matrix (Fin 2) (Fin 2) ℍ[ℝ]) n → n ≤ 2) :=
  ⟨⟨matrix4R_hasOrthIdem_four, fun _ h => matrix4R_orthIdem_le_four h⟩,
   ⟨matrix2H_hasOrthIdem_two, fun _ h => matrix2H_orthIdem_le_two h⟩⟩

end IdempotentRankInvariant
