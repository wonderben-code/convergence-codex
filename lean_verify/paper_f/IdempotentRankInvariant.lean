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
     `not_two_le_finrank_range4` and `not_five_le_finrank_range` then
     show the counting principle's `d`-slot has no slack on either side
     — strengthening either dimension lemma by one would contradict the
     corresponding witness (added folding review round 14, which asked
     whether the principle was over-strong).
  7. **`matrix2H_not_ringEquiv_matrix4R`** — M₂(ℍ) ≇ M₄(ℝ).
  8. **`clifford13_not_ringEquiv_clifford31`** — Cl(1,3;ℝ) ≇ Cl(3,1;ℝ),
     and `clifford13_not_algEquiv_clifford31` for the ℝ-algebra form.

  NOT proven here: the mod-8 periodicity table (this settles one pair
  of its entries, not the table); any spin-group statement; any
  physics; and no claim that this is the only or the best invariant —
  the Brauer-class route named in W7 is untouched.

  ---

  GENERALISED IN PLACE 2026-08-29 (`PROOF_STRATEGY` §7 rule 3).
  **THE LIST ABOVE IS KEPT UNCHANGED** (`ERRATUM 94`): every statement
  in it is still here and still true. What changed is that the ones
  written at `Fin 2` and `Fin 4` are now INSTANCES rather than the
  content (`ERRATUM 201`), and the header records that rather than
  leaving a reader to discover it from the code.

  * `P` and the four facts about diagonal matrix units are over an
    arbitrary nontrivial ring and an arbitrary finite index type, so
    **`matrix_hasOrthIdem_card`** — `Mₘ(α)` admits `card m` — replaces
    two separate `fin_cases` computations, and items 2 and 6's witness
    for M₂(ℍ) are both instances of it.
  * `leftMulVec`, `rightMul` and the dimension step carry an arbitrary
    finite index type in `Type`. **The `4` in the quaternionic step is
    `dim_ℝ ℍ` and never was about the index type**; the two entries of
    `Fin 2` were used only in a pair of `Fin.sum_univ_two` rewrites that
    `Finset.sum_mul` does at any size. The universe restriction to
    `Type` is inherited from `orthIdem_card_le`'s `V`, not new here.
  * **AND THEN THE BASE RING CAME OFF TOO, THE SAME DAY.** There were
    TWO actions — `leftMulVec4` over ℝ and `leftMulVec` over ℍ, five
    duplicated lemmas each — and neither used its base ring.
    **`finrank_le_finrank_range`** is the one dimension step, over any
    division algebra `D` that is finite-dimensional over a central ℝ:
    the range of a nonzero idempotent has real dimension at least
    `dim_ℝ D`. `four_le_finrank_range` is its `D = ℍ` instance and keeps
    its name because other files cite it. **`one_le_finrank_range4` is
    NOT an instance and says so**: over ℝ the same bound holds with no
    idempotency hypothesis, which is strictly stronger.
  * So **`matrixD_orthIdem_le_card`** caps `Mₘ(D)` at `card m` for every
    such `D`, and ℝ, ℂ and ℍ are three named instances. **The estate had
    the ℂ one nowhere**, and it is what makes the complex Clifford
    classification a classification rather than a list of isomorphisms.
  * **`card_eq_of_ringEquiv`** is the invariant as a size theorem: a
    RING isomorphism `Mₘ(D) ≃+* Mₘ'(D')` forces `card m = card m'`,
    across different division algebras and with nothing ℝ-linear
    assumed.
  * **AND THE SAME AT ONE LEVEL UP, ON PRODUCTS**, which the odd complex
    Clifford algebras need. `HasOrthIdem.prod`: `A × B` admits `p + q`.
    `HasOrthIdem.exists_split`: and at most that, **with no
    representation of `A × B` anywhere in it** — project a family to
    each component, discard the zeros, and what survives on each side is
    an orthogonal family of nonzero idempotents summing to `1` there,
    every index surviving somewhere because `(aᵢ, bᵢ) ≠ 0`. Pure ring
    theory, no trace and no dimension, which is not what the forecast
    for this step predicted. Hence `matrixProd_hasOrthIdem`,
    `matrixProd_orthIdem_le` and **`card_eq_of_ringEquiv_prod`**.
  * So **`matrixR_orthIdem_le_card`** and **`matrixH_orthIdem_le_card`**
    cap both families at `card m`, and **`orthIdem_card_pinned`** pins
    the invariant on EVERY real and quaternionic matrix algebra rather
    than on two. The two invariants agree on `Mₘ(ℝ)` and `Mₘ(ℍ)` and
    separate them only through the SIZE of the index type, which is why
    `M₂(ℍ)`/`M₄(ℝ)` came apart and `M₄(ℍ)`/`M₈(ℝ)` now do.
  * **`matrix4H_not_ringEquiv_matrix8R`** is what the generalisation was
    for: the rank-`6` row of `CentralIdemInvariant`'s mirror census,
    which neither invariant in that file can reach because NEITHER
    algebra splits. `M₈(ℝ)` admits eight, `M₄(ℍ)` at most four.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
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

/-! ## 3. The matrix units: `Mₘ(α)` admits `Fintype.card m`

**GENERALISED IN PLACE 2026-08-29** (`PROOF_STRATEGY` §7 rule 3; the original statement is kept
as an instance below, `ERRATUM 201`). The section proved `M₄(ℝ)` admits four, by `fin_cases` over
sixteen entries, and §4 proved `M₂(ℍ)` admits two by the same brute force over a different index
type and a different base ring. **Neither the index type nor the base ring was doing any work**:
the four facts about diagonal matrix units are `Matrix.single_mul_single_same`,
`Matrix.single_mul_single_of_ne`, one entry evaluation and `Matrix.sum_single_one`. So the two
blocks collapse to one theorem, both original statements become instances of it, and `M₈(ℝ)` —
which is what the mirror census at rank `6` needs — costs a third instance rather than a third
brute force. -/

section MatrixUnits

variable {α : Type*} [Ring α] {m : Type} [DecidableEq m]

/-- The diagonal matrix units of `Mₘ(α)`. -/
def P (α : Type*) [Ring α] {m : Type} [DecidableEq m] (i : m) : Matrix m m α :=
  Matrix.single i i 1

theorem P_idem [Fintype m] (i : m) : P α i * P α i = P α i := by
  simp [P]

theorem P_orth [Fintype m] (i j : m) (h : i ≠ j) : P α i * P α j = 0 := by
  rw [P, P, Matrix.single_mul_single_of_ne]
  exact h

theorem P_ne_zero [Nontrivial α] (i : m) : P α i ≠ 0 := by
  intro hc
  have h1 := congrFun (congrFun hc i) i
  simp [P] at h1

theorem P_sum [Fintype m] : ∑ i : m, P α i = 1 := Matrix.sum_single_one

/-- **`Mₘ(α)` ADMITS `card m` pairwise-orthogonal nonzero idempotents summing to `1`**, for every
nontrivial ring `α` and every finite index type. The re-indexing along `Fintype.equivFin` is the
only thing `HasOrthIdem`'s `Fin n` shape costs. -/
theorem matrix_hasOrthIdem_card [Nontrivial α] [Fintype m] :
    HasOrthIdem (Matrix m m α) (Fintype.card m) := by
  refine ⟨fun k => P α ((Fintype.equivFin m).symm k), fun k => P_idem _, ?_,
    fun k => P_ne_zero _, ?_⟩
  · intro k l hkl
    exact P_orth _ _ fun hc => hkl ((Fintype.equivFin m).symm.injective hc)
  · rw [Equiv.sum_comp (Fintype.equivFin m).symm (P α)]
    exact P_sum

/-- **M₄(ℝ) admits four** — the instance at `α = ℝ`, `m = Fin 4` (`ERRATUM 201`: the theorem this
section used to prove, now derived rather than left standing beside the general one). -/
theorem matrix4R_hasOrthIdem_four :
    HasOrthIdem (Matrix (Fin 4) (Fin 4) ℝ) 4 := by
  have h : HasOrthIdem (Matrix (Fin 4) (Fin 4) ℝ) (Fintype.card (Fin 4)) :=
    matrix_hasOrthIdem_card
  simpa using h

/-- **M₈(ℝ) admits eight** — the same theorem at `m = Fin 8`, and the half of the rank-`6` mirror
pair that needs a witness. -/
theorem matrix8R_hasOrthIdem_eight :
    HasOrthIdem (Matrix (Fin 8) (Fin 8) ℝ) 8 := by
  have h : HasOrthIdem (Matrix (Fin 8) (Fin 8) ℝ) (Fintype.card (Fin 8)) :=
    matrix_hasOrthIdem_card
  simpa using h

end MatrixUnits

/-! ### …and at most four

The matching upper bound. Review round 13 left this open and named it
rather than implying it: the inequivalence only needs 4 > 2, so the
estate knew M₂(ℍ) admits exactly two but only that M₄(ℝ) admits at
LEAST four. With the counting principle factored out this costs one
instantiation at `d = 1` — over ℝ the quaternionic dimension step is
replaced by the triviality that a nonzero endomorphism has a nonzero
range. -/

/-! ## 4. The action, and the dimension step over any real division algebra -/

section MatrixDBound

/- Entrywise quaternion arithmetic in one instance below. Linters silenced for
the block, including `unreachableTactic`/`unnecessarySimpa`: the build's option
set lets `simp` finish goals that bare `lake env lean` cannot, so the closing
`ring` and the `simpa` witnesses are load-bearing under one configuration and
flagged as redundant under the other. The file must compile under BOTH, so they
stay. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

/-- ℝ is central in ℍ, so the real scalar action commutes with
    quaternion multiplication. Kept although `Algebra.to_smulCommClass` now
    supplies it for every base below, because it was written when instance
    search did not reach it here and removing it changes which instance the
    elaborator picks. -/
instance smulCommRealQuaternion : SMulCommClass ℝ ℍ[ℝ] ℍ[ℝ] where
  smul_comm c p q := by
    change c • (p * q) = p * (c • q)
    ext <;> simp <;> ring

variable {D : Type} [DivisionRing D] [Algebra ℝ D] {m : Type} [Fintype m]

/-- Left multiplication by a matrix over `D` on `m → D`, as an ℝ-linear
    endomorphism. **The point of passing to ℝ is that all the dimension theory
    below is then over a FIELD** — which is what lets `D` itself be
    noncommutative.

    **GENERALISED IN THE BASE RING 2026-08-29.** This was two definitions,
    `leftMulVec4` over ℝ and `leftMulVec` over ℍ, with five duplicated lemmas
    each. Nothing in either used its base ring. -/
def leftMulVec (M : Matrix m m D) : (m → D) →ₗ[ℝ] (m → D) where
  toFun v := M *ᵥ v
  map_add' x y := Matrix.mulVec_add M x y
  map_smul' c x := Matrix.mulVec_smul M c x

@[simp]
theorem leftMulVec_apply (M : Matrix m m D) (v : m → D) :
    leftMulVec M v = M *ᵥ v := rfl

theorem leftMulVec_mul (M N : Matrix m m D) :
    leftMulVec (M * N) = leftMulVec M ∘ₗ leftMulVec N :=
  LinearMap.ext fun v => (Matrix.mulVec_mulVec v M N).symm

theorem leftMulVec_one [DecidableEq m] : leftMulVec (1 : Matrix m m D) = LinearMap.id :=
  LinearMap.ext fun v => Matrix.one_mulVec v

theorem leftMulVec_add (M N : Matrix m m D) :
    leftMulVec (M + N) = leftMulVec M + leftMulVec N :=
  LinearMap.ext fun v => Matrix.add_mulVec M N v

theorem leftMulVec_zero : leftMulVec (0 : Matrix m m D) = 0 :=
  LinearMap.ext fun v => Matrix.zero_mulVec v

/-- The action bundled as an additive hom, so `map_sum` is available. -/
def leftMulVecHom :
    Matrix m m D →+ ((m → D) →ₗ[ℝ] (m → D)) where
  toFun := leftMulVec
  map_zero' := leftMulVec_zero
  map_add' := leftMulVec_add

/-- `Dᵐ` has real dimension `(dim_ℝ D) * card m`. -/
theorem finrank_pi_div [FiniteDimensional ℝ D] :
    Module.finrank ℝ (m → D) = Module.finrank ℝ D * Fintype.card m := by
  rw [Module.finrank_pi_fintype]
  simp [mul_comm]

/-- ℍ² has real dimension 8 — the instance at `D = ℍ`, `m = Fin 2`. -/
theorem finrank_h2 : Module.finrank ℝ (Fin 2 → ℍ[ℝ]) = 8 := by
  rw [finrank_pi_div]
  simp [Quaternion.finrank_eq_four]

/-- ℝ⁴ has real dimension 4 — the instance at `D = ℝ`, `m = Fin 4`. -/
theorem finrank_r4 : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by simp

/-- Right multiplication of a vector over `D` by an element of `D`.
    ℝ-linear because ℝ is central, and the reason a nonzero range cannot be
    small. -/
def rightMul (v : m → D) : D →ₗ[ℝ] (m → D) where
  toFun q := fun i => v i * q
  map_add' q r := funext fun i => by simp [mul_add]
  map_smul' c q := funext fun i => by simpa using mul_smul_comm c (v i) q

omit [Fintype m] in
theorem rightMul_injective {v : m → D} (hv : v ≠ 0) :
    Function.Injective (rightMul v) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro q hq
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv (funext hc)
  have h1 : v i * q = 0 := congrFun hq i
  exact (mul_eq_zero_iff_left hi).mp h1

/-- **THE DIMENSION STEP.** A nonzero idempotent matrix over a finite-dimensional
    real division algebra `D` has a range of real dimension at least `dim_ℝ D` —
    the range contains some `v ≠ 0` and is stable under RIGHT multiplication by
    `D`, so it contains the image of the injective ℝ-linear map `q ↦ v·q` from a
    `dim_ℝ D`-dimensional space. This is the step the textbook argument does with
    module rank over a noncommutative division ring; here it is ℝ-linear algebra
    plus the fact that a division ring has no zero divisors.

    **TWO HYPOTHESES CAME OFF ON 2026-08-29** (`PROOF_STRATEGY` §7 rule 3), and
    the second is the interesting one. The index type was `Fin 2`, used only in a
    pair of `Fin.sum_univ_two` rewrites that `Finset.sum_mul` does at any size.
    **And the base ring was ℍ, with the `4` written as a literal** — it is
    `dim_ℝ ℍ`, and the argument needs of ℍ only that it is a division ring,
    finite-dimensional over ℝ, with ℝ central. So ℝ, ℂ and ℍ are three instances
    of one theorem, and the estate had the first two nowhere. -/
theorem finrank_le_finrank_range [FiniteDimensional ℝ D]
    (e : Matrix m m D) (he : e * e = e) (h0 : e ≠ 0) :
    Module.finrank ℝ D ≤ Module.finrank ℝ (LinearMap.range (leftMulVec e)) := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, e i j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (Matrix.ext fun a b => (hc a b).trans (Matrix.zero_apply a b).symm)
  set w : m → D := Pi.single j 1 with hw
  set v : m → D := e *ᵥ w with hv
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
      simp [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
    have h2 : (∑ k, e a k * v k) = v a := by
      have h3 := congrFun hev a
      simpa [Matrix.mulVec, dotProduct] using h3
    change (e *ᵥ fun k => v k * q) a = v a * q
    rw [h1, h2]
  have hrk : Module.finrank ℝ (LinearMap.range (rightMul v)) = Module.finrank ℝ D :=
    LinearMap.finrank_range_of_inj (rightMul_injective hvne)
  calc Module.finrank ℝ D = Module.finrank ℝ (LinearMap.range (rightMul v)) := hrk.symm
    _ ≤ Module.finrank ℝ (LinearMap.range (leftMulVec e)) :=
        Submodule.finrank_mono hsub

/-- **The quaternionic step, at `D = ℍ`.** The statement this file carried before
    the base ring came off, kept as the instance it now is (`ERRATUM 201`) and
    because other files cite it by name. -/
theorem four_le_finrank_range (e : Matrix m m ℍ[ℝ])
    (he : e * e = e) (h0 : e ≠ 0) :
    4 ≤ Module.finrank ℝ (LinearMap.range (leftMulVec e)) := by
  have h := finrank_le_finrank_range e he h0
  rwa [Quaternion.finrank_eq_four] at h

/-- The real counterpart, and it is the easy one: a NONZERO matrix acts
    nontrivially (some column is nonzero), so its range is not the zero
    subspace. **No idempotency is needed, which is why this is NOT the instance
    of `finrank_le_finrank_range` at `D = ℝ`** — it is a strictly stronger
    statement in the one place the general theorem is weakest. -/
theorem one_le_finrank_range4 (e : Matrix m m ℝ) (h0 : e ≠ 0) :
    1 ≤ Module.finrank ℝ (LinearMap.range (leftMulVec e)) := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, e i j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (Matrix.ext fun a b => (hc a b).trans (Matrix.zero_apply a b).symm)
  have hv : leftMulVec e (Pi.single j 1) ≠ 0 := by
    intro hz
    apply hij
    have hzi := congrFun hz i
    rw [leftMulVec_apply, Matrix.mulVec_single] at hzi
    simpa using hzi
  have hbot : LinearMap.range (leftMulVec e) ≠ ⊥ := by
    intro hb
    apply hv
    have hm : leftMulVec e (Pi.single j 1) ∈ LinearMap.range (leftMulVec e) :=
      LinearMap.mem_range_self _ _
    rw [hb, Submodule.mem_bot] at hm
    exact hm
  have hnz : Module.finrank ℝ (LinearMap.range (leftMulVec e)) ≠ 0 := fun hz =>
    hbot (Submodule.finrank_eq_zero.mp hz)
  omega

/-- **`Mₘ(D)` ADMITS AT MOST `card m`**, for every finite-dimensional real
    division algebra `D`. The two `dim_ℝ D` factors cancel: the family costs
    `n * dim_ℝ D` and the space has `dim_ℝ D * card m`. -/
theorem matrixD_orthIdem_le_card [DecidableEq m] [FiniteDimensional ℝ D] {n : ℕ}
    (h : HasOrthIdem (Matrix m m D) n) : n ≤ Fintype.card m := by
  have hb := orthIdem_card_le (leftMulVecHom (m := m) (D := D)) leftMulVec_mul leftMulVec_one
    (Module.finrank ℝ D) (fun x hx h0 => finrank_le_finrank_range x hx h0) h
  rw [finrank_pi_div] at hb
  have hpos : 0 < Module.finrank ℝ D := Module.finrank_pos
  calc n = n * Module.finrank ℝ D / Module.finrank ℝ D := by
        rw [Nat.mul_div_cancel _ hpos]
    _ ≤ Module.finrank ℝ D * Fintype.card m / Module.finrank ℝ D := Nat.div_le_div_right hb
    _ = Fintype.card m := by
        rw [Nat.mul_div_cancel_left _ hpos]

/-- **`Mₘ(ℝ)` admits at most `card m`** — the instance at `D = ℝ`. -/
theorem matrixR_orthIdem_le_card [DecidableEq m] {n : ℕ}
    (h : HasOrthIdem (Matrix m m ℝ) n) : n ≤ Fintype.card m :=
  matrixD_orthIdem_le_card h

/-- **`Mₘ(ℂ)` admits at most `card m`** — the instance at `D = ℂ`, which this
    estate did not have and which the complex classification needs. -/
theorem matrixC_orthIdem_le_card [DecidableEq m] {n : ℕ}
    (h : HasOrthIdem (Matrix m m ℂ) n) : n ≤ Fintype.card m :=
  matrixD_orthIdem_le_card h

/-- **`Mₘ(ℍ)` admits at most `card m`** — the instance at `D = ℍ`. -/
theorem matrixH_orthIdem_le_card [DecidableEq m] {n : ℕ}
    (h : HasOrthIdem (Matrix m m ℍ[ℝ]) n) : n ≤ Fintype.card m :=
  matrixD_orthIdem_le_card h

/-- **M₄(ℝ) admits at most four.** With `matrix4R_hasOrthIdem_four`
    this pins the invariant's value at M₄(ℝ) to exactly four. -/
theorem matrix4R_orthIdem_le_four {n : ℕ}
    (h : HasOrthIdem (Matrix (Fin 4) (Fin 4) ℝ) n) : n ≤ 4 := by
  simpa using matrixR_orthIdem_le_card h

/-- **M₂(ℍ) admits at most two** — the instance at `m = Fin 2`. -/
theorem matrix2H_orthIdem_le_two {n : ℕ}
    (h : HasOrthIdem (Matrix (Fin 2) (Fin 2) ℍ[ℝ]) n) : n ≤ 2 := by
  simpa using matrixH_orthIdem_le_card h

/-- **M₄(ℍ) admits at most four** — the instance at `m = Fin 4`, and the half of the rank-`6`
mirror pair that needs a bound. -/
theorem matrix4H_orthIdem_le_four {n : ℕ}
    (h : HasOrthIdem (Matrix (Fin 4) (Fin 4) ℍ[ℝ]) n) : n ≤ 4 := by
  simpa using matrixH_orthIdem_le_card h

/-! ### The bounds are attained -/

/-- **M₂(ℍ) does admit two** — so `matrix2H_orthIdem_le_two` is a SHARP
    bound, not a vacuous one. Without this the inequivalence proof would
    still go through, but nothing would rule out the possibility that the
    bound was accidentally bounding an empty family; review round 13
    flagged exactly that, and this is the answer.

    **It is now the instance of `matrix_hasOrthIdem_card` at `α = ℍ`, `m = Fin 2`** rather than a
    second `fin_cases` computation (`ERRATUM 201`); the diagonal matrix units never cared which
    ring they were over. -/
theorem matrix2H_hasOrthIdem_two :
    HasOrthIdem (Matrix (Fin 2) (Fin 2) ℍ[ℝ]) 2 := by
  have h : HasOrthIdem (Matrix (Fin 2) (Fin 2) ℍ[ℝ]) (Fintype.card (Fin 2)) :=
    matrix_hasOrthIdem_card
  simpa using h

end MatrixDBound

/-! ## 5. Products, and why they need no new representation theory

The invariant is defined for any ring, so `A × B` is in scope, but neither the counting principle
nor any dimension lemma above says anything about one. **Both clauses turn out to be pure ring
theory** — no action on a vector space, no trace, no dimension. The witness is the obvious family;
the bound comes from projecting a family in `A × B` to its two components and throwing away the
zeros, which is why it needs `A` and `B`'s own bounds and nothing else. -/

section Products

variable {A B : Type*} [Ring A] [Ring B]

/-- **A PRODUCT ADMITS THE SUM.** `(eᵢ, 0)` and `(0, fⱼ)`, indexed through `Fin.addCases`. -/
theorem HasOrthIdem.prod {p q : ℕ} (hA : HasOrthIdem A p) (hB : HasOrthIdem B q) :
    HasOrthIdem (A × B) (p + q) := by
  obtain ⟨a, hasq, haorth, hane, hasum⟩ := hA
  obtain ⟨b, hbsq, hborth, hbne, hbsum⟩ := hB
  refine ⟨Fin.addCases (fun i => (a i, 0)) (fun j => (0, b j)), ?_, ?_, ?_, ?_⟩
  · intro k
    induction k using Fin.addCases with
    | left i => simp [hasq i]
    | right j => simp [hbsq j]
  · intro k l hkl
    induction k using Fin.addCases with
    | left i =>
        induction l using Fin.addCases with
        | left i' =>
            have hii : i ≠ i' := fun hc => hkl (by rw [hc])
            simp [haorth i i' hii]
        | right j' => simp
    | right j =>
        induction l using Fin.addCases with
        | left i' => simp
        | right j' =>
            have hjj : j ≠ j' := fun hc => hkl (by rw [hc])
            simp [hborth j j' hjj]
  · intro k
    induction k using Fin.addCases with
    | left i =>
        simp only [Fin.addCases_left]
        exact fun hc => hane i (by simpa using congrArg Prod.fst hc)
    | right j =>
        simp only [Fin.addCases_right]
        exact fun hc => hbne j (by simpa using congrArg Prod.snd hc)
  · rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    rw [Prod.ext_iff]
    constructor
    · simpa [Prod.fst_sum] using hasum
    · simpa [Prod.snd_sum] using hbsum

/-- **AND AT MOST THE SUM OF THE TWO BOUNDS.** Project a family in `A × B` to each component and
discard the zeros: what survives on the left is an orthogonal family of NONZERO idempotents summing
to `1` in `A`, likewise on the right, and every index survives on at least one side because
`(aᵢ, bᵢ) ≠ 0`. **No representation of `A × B` is needed**, which is the point — the counting
principle is about a ring acting on a space and this argument never leaves the ring. -/
theorem HasOrthIdem.exists_split {n : ℕ} (h : HasOrthIdem (A × B) n) :
    ∃ p q : ℕ, n ≤ p + q ∧ HasOrthIdem A p ∧ HasOrthIdem B q := by
  classical
  obtain ⟨e, hsq, horth, hne, hsum⟩ := h
  set SA : Finset (Fin n) := Finset.univ.filter fun i => (e i).1 ≠ 0 with hSA
  set SB : Finset (Fin n) := Finset.univ.filter fun i => (e i).2 ≠ 0 with hSB
  have hcover : (Finset.univ : Finset (Fin n)) ⊆ SA ∪ SB := by
    intro i _
    by_cases hzA : (e i).1 = 0
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      intro hzB
      exact hne i (by simp [Prod.ext_iff, hzA, hzB])
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzA⟩)
  refine ⟨SA.card, SB.card, ?_, ?_, ?_⟩
  · calc n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ (SA ∪ SB).card := Finset.card_le_card hcover
      _ ≤ SA.card + SB.card := Finset.card_union_le _ _
  · refine ⟨fun k => (e ((SA.orderIsoOfFin rfl k : Fin n))).1, fun k => congrArg Prod.fst (hsq _),
      ?_, ?_, ?_⟩
    · intro k l hkl
      have hne' : ((SA.orderIsoOfFin rfl k : Fin n)) ≠ ((SA.orderIsoOfFin rfl l : Fin n)) :=
        fun hc => hkl ((SA.orderIsoOfFin rfl).injective (Subtype.ext hc))
      exact congrArg Prod.fst (horth _ _ hne')
    · intro k
      exact (Finset.mem_filter.mp (SA.orderIsoOfFin rfl k).2).2
    · have h1 : ∑ k : Fin SA.card, (e ((SA.orderIsoOfFin rfl k : Fin n))).1
          = ∑ x : SA, (e (x : Fin n)).1 :=
        Equiv.sum_comp (SA.orderIsoOfFin rfl).toEquiv fun x : SA => (e (x : Fin n)).1
      have h2 : ∑ x : SA, (e (x : Fin n)).1 = ∑ i ∈ SA, (e i).1 :=
        Finset.sum_coe_sort SA fun i => (e i).1
      have h3 : ∑ i ∈ SA, (e i).1 = ∑ i, (e i).1 := by
        refine Finset.sum_subset (Finset.subset_univ SA) fun i _ hi => ?_
        by_contra hc
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
      rw [h1, h2, h3, ← Prod.fst_sum, hsum]
      rfl
  · refine ⟨fun k => (e ((SB.orderIsoOfFin rfl k : Fin n))).2, fun k => congrArg Prod.snd (hsq _),
      ?_, ?_, ?_⟩
    · intro k l hkl
      have hne' : ((SB.orderIsoOfFin rfl k : Fin n)) ≠ ((SB.orderIsoOfFin rfl l : Fin n)) :=
        fun hc => hkl ((SB.orderIsoOfFin rfl).injective (Subtype.ext hc))
      exact congrArg Prod.snd (horth _ _ hne')
    · intro k
      exact (Finset.mem_filter.mp (SB.orderIsoOfFin rfl k).2).2
    · have h1 : ∑ k : Fin SB.card, (e ((SB.orderIsoOfFin rfl k : Fin n))).2
          = ∑ x : SB, (e (x : Fin n)).2 :=
        Equiv.sum_comp (SB.orderIsoOfFin rfl).toEquiv fun x : SB => (e (x : Fin n)).2
      have h2 : ∑ x : SB, (e (x : Fin n)).2 = ∑ i ∈ SB, (e i).2 :=
        Finset.sum_coe_sort SB fun i => (e i).2
      have h3 : ∑ i ∈ SB, (e i).2 = ∑ i, (e i).2 := by
        refine Finset.sum_subset (Finset.subset_univ SB) fun i _ hi => ?_
        by_contra hc
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
      rw [h1, h2, h3, ← Prod.snd_sum, hsum]
      rfl

/-- **The bound in the form a caller uses**: two bounds in, one bound out. -/
theorem orthIdem_prod_le {bA bB : ℕ}
    (hA : ∀ p, HasOrthIdem A p → p ≤ bA) (hB : ∀ q, HasOrthIdem B q → q ≤ bB)
    {n : ℕ} (h : HasOrthIdem (A × B) n) : n ≤ bA + bB := by
  obtain ⟨p, q, hn, hp, hq⟩ := h.exists_split
  have h1 := hA p hp
  have h2 := hB q hq
  omega

end Products

/-- **THE INVARIANT AS A SIZE THEOREM: A RING ISOMORPHISM BETWEEN MATRIX ALGEBRAS OVER REAL
    DIVISION ALGEBRAS FORCES THE INDEX TYPES TO HAVE THE SAME SIZE.** The two bases need not be the
    same division algebra, and nothing here is ℝ-linear: `Mₘ(ℝ) ≃+* Mₘ'(ℍ)` already forces
    `card m = card m'`. Both directions of `matrix_hasOrthIdem_card` are used, transported across
    the isomorphism and back, against `matrixD_orthIdem_le_card` on each side. -/
theorem card_eq_of_ringEquiv {D D' : Type} [DivisionRing D] [Algebra ℝ D] [FiniteDimensional ℝ D]
    [DivisionRing D'] [Algebra ℝ D'] [FiniteDimensional ℝ D']
    {m m' : Type} [Fintype m] [Fintype m']
    (φ : Matrix m m D ≃+* Matrix m' m' D') : Fintype.card m = Fintype.card m' := by
  classical
  have h1 : HasOrthIdem (Matrix m' m' D') (Fintype.card m) :=
    HasOrthIdem.of_ringEquiv φ matrix_hasOrthIdem_card
  have h2 : HasOrthIdem (Matrix m m D) (Fintype.card m') :=
    HasOrthIdem.of_ringEquiv φ.symm matrix_hasOrthIdem_card
  exact Nat.le_antisymm (matrixD_orthIdem_le_card h1) (matrixD_orthIdem_le_card h2)

/-- **`Mₘ(D) × Mₘ(D)` ADMITS EXACTLY `2 · card m`**, witness and bound, for every real division
    algebra `D`. Both halves are instances of the product clause. -/
theorem matrixProd_hasOrthIdem {D : Type} [DivisionRing D] [Algebra ℝ D]
    {m : Type} [Fintype m] [DecidableEq m] :
    HasOrthIdem (Matrix m m D × Matrix m m D) (Fintype.card m + Fintype.card m) :=
  HasOrthIdem.prod matrix_hasOrthIdem_card matrix_hasOrthIdem_card

theorem matrixProd_orthIdem_le {D : Type} [DivisionRing D] [Algebra ℝ D] [FiniteDimensional ℝ D]
    {m : Type} [Fintype m] [DecidableEq m] {n : ℕ}
    (h : HasOrthIdem (Matrix m m D × Matrix m m D) n) :
    n ≤ Fintype.card m + Fintype.card m :=
  orthIdem_prod_le (fun _ hp => matrixD_orthIdem_le_card hp)
    (fun _ hq => matrixD_orthIdem_le_card hq) h

/-- **THE SIZE THEOREM FOR SPLIT ALGEBRAS.** A ring isomorphism
    `Mₘ(D) × Mₘ(D) ≃+* Mₘ'(D') × Mₘ'(D')` forces `card m = card m'`. Same argument as
    `card_eq_of_ringEquiv`, one level up, and it is what the odd complex Clifford algebras need. -/
theorem card_eq_of_ringEquiv_prod {D D' : Type} [DivisionRing D] [Algebra ℝ D]
    [FiniteDimensional ℝ D] [DivisionRing D'] [Algebra ℝ D'] [FiniteDimensional ℝ D']
    {m m' : Type} [Fintype m] [Fintype m']
    (φ : (Matrix m m D × Matrix m m D) ≃+* (Matrix m' m' D' × Matrix m' m' D')) :
    Fintype.card m = Fintype.card m' := by
  classical
  have h1 : HasOrthIdem (Matrix m' m' D' × Matrix m' m' D') (Fintype.card m + Fintype.card m) :=
    HasOrthIdem.of_ringEquiv φ matrixProd_hasOrthIdem
  have h2 : HasOrthIdem (Matrix m m D × Matrix m m D) (Fintype.card m' + Fintype.card m') :=
    HasOrthIdem.of_ringEquiv φ.symm matrixProd_hasOrthIdem
  have b1 := matrixProd_orthIdem_le h1
  have b2 := matrixProd_orthIdem_le h2
  omega

/-! ## 6. The obstruction, and the two Clifford algebras -/

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

/-- **M₄(ℍ) ≇ M₈(ℝ)** — two 64-dimensional real algebras, the rank-`6` mirror pair of the
    Clifford census, which the central-idempotent invariant cannot reach because NEITHER of them
    splits. Here the counts differ: `M₈(ℝ)` admits eight orthogonal nonzero idempotents and
    `M₄(ℍ)` at most four. -/
theorem matrix4H_not_ringEquiv_matrix8R :
    IsEmpty (Matrix (Fin 4) (Fin 4) ℍ[ℝ] ≃+* Matrix (Fin 8) (Fin 8) ℝ) := by
  refine ⟨fun φ => ?_⟩
  have h8 : HasOrthIdem (Matrix (Fin 4) (Fin 4) ℍ[ℝ]) 8 :=
    HasOrthIdem.of_ringEquiv φ.symm matrix8R_hasOrthIdem_eight
  have := matrix4H_orthIdem_le_four h8
  omega

/-! ## 7. The dimension hypotheses are at their sharp values

Review round 14 attacked `orthIdem_card_le` by asking whether its
`d`-slot was slack — a principle that let you plug in a larger `d` than
the truth would be silently over-strong, and both published bounds now
depend on it. It is not slack, and that is provable from what is already
here rather than by inspection: strengthening either dimension lemma by
one would contradict the corresponding attained witness. -/

/-- `one_le_finrank_range4` cannot be strengthened to 2: the principle
    would then give 4·2 ≤ 4 against `matrix4R_hasOrthIdem_four`. -/
theorem not_two_le_finrank_range4 :
    ¬ (∀ x : Matrix (Fin 4) (Fin 4) ℝ, x * x = x → x ≠ 0 →
      2 ≤ Module.finrank ℝ (LinearMap.range (leftMulVec x))) := by
  intro hd
  have hb := orthIdem_card_le (leftMulVecHom (m := Fin 4) (D := ℝ)) leftMulVec_mul
    leftMulVec_one 2 hd matrix4R_hasOrthIdem_four
  rw [finrank_r4] at hb
  omega

/-- `four_le_finrank_range` cannot be strengthened to 5: the principle
    would then give 2·5 ≤ 8 against `matrix2H_hasOrthIdem_two`. So the
    quaternionic step is at the sharp value too, and the whole argument
    has no slack anywhere. -/
theorem not_five_le_finrank_range :
    ¬ (∀ x : Matrix (Fin 2) (Fin 2) ℍ[ℝ], x * x = x → x ≠ 0 →
      5 ≤ Module.finrank ℝ (LinearMap.range (leftMulVec x))) := by
  intro hd
  have hb := orthIdem_card_le (leftMulVecHom (m := Fin 2) (D := ℍ[ℝ])) leftMulVec_mul
    leftMulVec_one 5 hd matrix2H_hasOrthIdem_two
  rw [finrank_h2] at hb
  omega

/-! ## 8. Both values pinned -/

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

/-- **AND THE VALUE IS NOW KNOWN ON EVERY REAL AND QUATERNIONIC MATRIX ALGEBRA, NOT TWO.**
`card m` on both sides — for `Mₘ(ℝ)` because a nonzero idempotent has a nonzero range, for
`Mₘ(ℍ)` because it has one of real dimension at least `dim_ℝ ℍ = 4` and the whole space has
`4 * card m`. **The two invariants therefore agree on `Mₘ(ℝ)` and `Mₘ(ℍ)` and separate them only
through the SIZE of the index type**, which is why `M₄(ℍ)` and `M₈(ℝ)` come apart and `M₂(ℍ)` and
`M₄(ℝ)` did. -/
theorem orthIdem_card_pinned {m : Type} [Fintype m] [DecidableEq m] :
    (HasOrthIdem (Matrix m m ℝ) (Fintype.card m)
        ∧ ∀ n, HasOrthIdem (Matrix m m ℝ) n → n ≤ Fintype.card m)
      ∧ (HasOrthIdem (Matrix m m ℍ[ℝ]) (Fintype.card m)
        ∧ ∀ n, HasOrthIdem (Matrix m m ℍ[ℝ]) n → n ≤ Fintype.card m) :=
  ⟨⟨matrix_hasOrthIdem_card, fun _ h => matrixR_orthIdem_le_card h⟩,
   ⟨matrix_hasOrthIdem_card, fun _ h => matrixH_orthIdem_le_card h⟩⟩

end IdempotentRankInvariant
