/-
  PatiSalamUnbrokenSplit.lean — the unbroken group of the two-stage Pati–Salam breaking is
  `(SU(3)_c × U(1)_Q) ⧸ ℤ₃`. The map `SU(3) × U(1) → U(3)`, `(A, λ) ↦ λ · A`, is a surjective group
  homomorphism whose kernel has exactly three elements (`splitHom_surjective`,
  `card_ker_splitHom`); composed with unit 199's `stabilizerPairEquivU3` it identifies the quotient
  with the stabiliser of both vacua (`unbrokenEquiv`). Its `SU(3)` factor acts as `diag(A, 1)` on
  `SU(4)` and trivially on both `SU(2)`s — COLOUR (`colour_components`) — and its `U(1)` factor is
  the electric charge's one-parameter subgroup (`splitHom_charge`).

  SPINE link L15 (Higgs sector, PARTIAL) — the rest of the splitting that units 199 and 200 left
  as NOT PROVED: unit 199 computed the unbroken group as `U(3)`, unit 200 identified its centre with
  the charge, and neither wrote `U(3)` as `SU(3) × U(1)` modulo `ℤ₃`. Hardening unit 201,
  2026-09-25.

  WHAT IS PROVED.
  (1) `splitHom : SU(3) × U(1) →* U(3)`, `(A, λ) ↦ λ · A` (`smul_mem_unitary`).
  (2) **`splitHom_surjective`**: for `U ∈ U(3)` take `λ = (det U)^{1/3}`
      (`Complex.cpow_nat_inv_pow`); `|λ| = 1` because `|det U| = 1`, and `λ̄ · U` has determinant
      `λ̄³ λ³ = 1`.
  (3) **`mem_ker_splitHom_iff`**: `(A, λ)` is in the kernel iff `A = λ̄ · 1` and `λ³ = 1`; and
      **`card_ker_splitHom : Nat.card splitHom.ker = 3`**, through an explicit bijection with the
      cube roots of unity (`rootsToKer`, `kerToRoots`, `Complex.card_rootsOfUnity`); it is cyclic,
      being of prime order (`ker_isCyclic`).
  (4) **`unbrokenEquiv : (SU(3) × U(1)) ⧸ splitHom.ker ≃* MulAction.stabilizer
      (SU(4) × SU(2)_L × SU(2)_R) (vac, vacEW)`** — `QuotientGroup.quotientKerEquivOfSurjective`
      followed by the inverse of `stabilizerPairEquivU3`.
  (5) **`colour_components`**: the image of `(A, 1)` is `(diag(A, 1), 1, 1)` — the `SU(3)` factor
      moves the three colour coordinates of the `SU(4)` factor and nothing else.
  (6) **`splitHom_charge`**: the image of `(1, e^{it})` is the charge's `stabilizerPairEquivU3`
      image at `t` (unit 200's `stabilizerPairEquivU3_charge`).

  NOT PROVED, said exactly.
  • The kernel is cyclic of order three (`ker_isCyclic`), and no explicit
    `≃* Multiplicative (ZMod 3)` is written.
  • The charge's scale (`qFull = 6i · Q`), topology (all `≃*` are of abstract groups), and the
    vacua (still chosen, `ASSUMPTIONS_LEDGER` 60) — unchanged from units 199–200.
    ⚠ 25 September 2026 (hardening unit 209): topology is supplied —
    `PatiSalamTopologicalCopies.unbrokenContinuousEquiv`: with the quotient topology,
    `(SU(3) × U(1)) ⧸ ker splitHom` is homeomorphic to the unbroken group. The charge's scale and
    the vacua stand. Kept as written (`ERRATUM 94`).
  • Still no potential, no masses, no gauge bosons as objects.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `smul_mem_unitary` takes `A` unitary and
  `star c * c = 1`; `norm_eq_one_of_pow_three` takes `z ^ 3 = 1`; `star_mul_self_of_norm` takes
  `‖z‖ = 1`. Nothing else is assumed.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 18 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list: none is taken.

  0 sorry. 0 new axioms. `#print axioms` on all 18 declarations below: each is
  `[propext, Classical.choice, Quot.sound]`.
-/

import PatiSalamChargeCentre
import Mathlib.RingTheory.RootsOfUnity.Complex

open Matrix PatiSalamStabiliserGroup

namespace PatiSalamUnbrokenSplit

abbrev SU3 := Matrix.specialUnitaryGroup (Fin 3) ℂ

theorem unit_star_mul (l : unitary ℂ) : star (l : ℂ) * l = 1 :=
  Unitary.star_mul_self_of_mem l.2
theorem unit_mul_star (l : unitary ℂ) : (l : ℂ) * star (l : ℂ) = 1 :=
  Unitary.mul_star_self_of_mem l.2

theorem smul_mem_unitary {A : Matrix (Fin 3) (Fin 3) ℂ} (hA : A ∈ unitaryGroup (Fin 3) ℂ)
    {c : ℂ} (hc : star c * c = 1) : c • A ∈ unitaryGroup (Fin 3) ℂ := by
  rw [mem_unitaryGroup_iff', star_smul, smul_mul_smul_comm, mem_unitaryGroup_iff'.mp hA, hc,
    one_smul]

/-- `(A, λ) ↦ λ • A`, from `SU(3) × U(1)` to `U(3)`. -/
noncomputable def splitHom : SU3 × unitary ℂ →* GroupU3 where
  toFun p := ⟨(p.2 : ℂ) • (p.1 : Matrix (Fin 3) (Fin 3) ℂ),
    smul_mem_unitary (mem_specialUnitaryGroup_iff.mp p.1.2).1 (unit_star_mul p.2)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' p q := by
    apply Subtype.ext
    simp only [Prod.fst_mul, Prod.snd_mul, Submonoid.coe_mul]
    rw [smul_mul_smul_comm]

theorem splitHom_val (p : SU3 × unitary ℂ) :
    ((splitHom p : GroupU3) : Matrix (Fin 3) (Fin 3) ℂ)
      = (p.2 : ℂ) • (p.1 : Matrix (Fin 3) (Fin 3) ℂ) :=
  rfl

theorem splitHom_surjective : Function.Surjective splitHom := by
  intro U
  set l := (U : Matrix (Fin 3) (Fin 3) ℂ).det ^ ((3 : ℕ)⁻¹ : ℂ) with hl0
  have hl : l ^ 3 = (U : Matrix (Fin 3) (Fin 3) ℂ).det :=
    Complex.cpow_nat_inv_pow _ (by norm_num)
  have hdU : star (U : Matrix (Fin 3) (Fin 3) ℂ).det * (U : Matrix (Fin 3) (Fin 3) ℂ).det = 1 :=
    Unitary.star_mul_self_of_mem (det_of_mem_unitary U.2)
  have hn : ‖l‖ = 1 := by
    have h1 : ‖(U : Matrix (Fin 3) (Fin 3) ℂ).det‖ = 1 := by
      have := Complex.mul_conj (U : Matrix (Fin 3) (Fin 3) ℂ).det
      rw [show (starRingEnd ℂ) (U : Matrix (Fin 3) (Fin 3) ℂ).det
        = star (U : Matrix (Fin 3) (Fin 3) ℂ).det from rfl, mul_comm, hdU] at this
      have h2 : Complex.normSq (U : Matrix (Fin 3) (Fin 3) ℂ).det = 1 := by exact_mod_cast this.symm
      rw [Complex.normSq_eq_norm_sq] at h2
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
    rw [← hl, Complex.norm_pow] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h1
  have hll : star l * l = 1 := by
    rw [show star l = (starRingEnd ℂ) l from rfl, mul_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hn]; norm_num
  have hll' : l * star l = 1 := by rw [mul_comm]; exact hll
  have hlU : l ∈ unitary ℂ := Unitary.mem_iff.mpr ⟨hll, hll'⟩
  have hA : star l • (U : Matrix (Fin 3) (Fin 3) ℂ) ∈ specialUnitaryGroup (Fin 3) ℂ := by
    refine mem_specialUnitaryGroup_iff.mpr
      ⟨smul_mem_unitary U.2 (by rw [star_star]; exact hll'), ?_⟩
    rw [det_smul, Fintype.card_fin, ← hl, ← mul_pow, hll, one_pow]
  refine ⟨(⟨_, hA⟩, ⟨l, hlU⟩), Subtype.ext ?_⟩
  rw [splitHom_val]
  change l • (star l • (U : Matrix (Fin 3) (Fin 3) ℂ)) = U
  rw [smul_smul, hll', one_smul]

theorem mem_ker_splitHom_iff (p : SU3 × unitary ℂ) :
    p ∈ splitHom.ker ↔
      (p.1 : Matrix (Fin 3) (Fin 3) ℂ) = star (p.2 : ℂ) • 1 ∧ (p.2 : ℂ) ^ 3 = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have e : (p.2 : ℂ) • (p.1 : Matrix (Fin 3) (Fin 3) ℂ) = 1 := congrArg Subtype.val h
    have hA : (p.1 : Matrix (Fin 3) (Fin 3) ℂ) = star (p.2 : ℂ) • 1 := by
      rw [← e, smul_smul, unit_star_mul, one_smul]
    refine ⟨hA, ?_⟩
    have hdet := (mem_specialUnitaryGroup_iff.mp p.1.2).2
    rw [hA, det_smul, Fintype.card_fin, det_one, mul_one] at hdet
    have : ((p.2 : ℂ) * star (p.2 : ℂ)) ^ 3 = (p.2 : ℂ) ^ 3 := by rw [mul_pow, hdet, mul_one]
    rw [unit_mul_star, one_pow] at this
    exact this.symm
  · rintro ⟨hA, -⟩
    apply Subtype.ext
    change (p.2 : ℂ) • (p.1 : Matrix (Fin 3) (Fin 3) ℂ) = 1
    rw [hA, smul_smul, unit_mul_star, one_smul]

theorem norm_eq_one_of_pow_three {z : ℂ} (h : z ^ 3 = 1) : ‖z‖ = 1 := by
  have := congrArg norm h
  rw [Complex.norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this

theorem star_mul_self_of_norm {z : ℂ} (h : ‖z‖ = 1) : star z * z = 1 := by
  rw [show star z = (starRingEnd ℂ) z from rfl, mul_comm, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, h]
  norm_num

/-- The kernel, element by element: a cube root of unity `ω` and `ω̄ · 1`. -/
noncomputable def rootsToKer (w : rootsOfUnity 3 ℂ) : splitHom.ker := by
  have hw : ((w : ℂˣ) : ℂ) ^ 3 = 1 := by
    have h := congrArg Units.val ((mem_rootsOfUnity 3 (w : ℂˣ)).mp w.2)
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h
  have hn := norm_eq_one_of_pow_three hw
  have hs := star_mul_self_of_norm hn
  have hs' : ((w : ℂˣ) : ℂ) * star ((w : ℂˣ) : ℂ) = 1 := by rw [mul_comm]; exact hs
  refine ⟨(⟨star ((w : ℂˣ) : ℂ) • 1, mem_specialUnitaryGroup_iff.mpr
    ⟨smul_mem_unitary (one_mem _) (by rw [star_star]; exact hs'), ?_⟩⟩,
    ⟨(w : ℂˣ), Unitary.mem_iff.mpr ⟨hs, hs'⟩⟩), ?_⟩
  · rw [det_smul, Fintype.card_fin, det_one, mul_one, ← star_pow, hw, star_one]
  · rw [mem_ker_splitHom_iff]; exact ⟨rfl, hw⟩

noncomputable def kerToRoots (p : splitHom.ker) : rootsOfUnity 3 ℂ :=
  ⟨⟨((p : SU3 × unitary ℂ).2 : ℂ), star ((p : SU3 × unitary ℂ).2 : ℂ), unit_mul_star _,
      unit_star_mul _⟩,
    (mem_rootsOfUnity 3 _).mpr (Units.ext (by simpa using ((mem_ker_splitHom_iff _).mp p.2).2))⟩

/-- **The kernel of `SU(3) × U(1) → U(3)` has exactly three elements.** -/
theorem card_ker_splitHom : Nat.card splitHom.ker = 3 := by
  have e : splitHom.ker ≃ rootsOfUnity 3 ℂ :=
    { toFun := kerToRoots
      invFun := rootsToKer
      left_inv := by
        intro p
        apply Subtype.ext
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext rfl)
        exact ((mem_ker_splitHom_iff _).mp p.2).1.symm
      right_inv := by
        intro w
        apply Subtype.ext
        apply Units.ext
        rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Complex.card_rootsOfUnity]

/-- The kernel is cyclic — a group of prime order `3`, so `ℤ₃`. -/
theorem ker_isCyclic : IsCyclic splitHom.ker := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact isCyclic_of_prime_card card_ker_splitHom

open PatiSalamVacuumStabiliser ElectroweakVacuumStabiliser PatiSalamGaugeAction in
/-- **The unbroken group is `(SU(3) × U(1)) ⧸ ℤ₃`.** -/
noncomputable def unbrokenEquiv :
    (SU3 × unitary ℂ) ⧸ splitHom.ker ≃* MulAction.stabilizer FullGroup (vac, vacEW) :=
  (QuotientGroup.quotientKerEquivOfSurjective splitHom splitHom_surjective).trans
    stabilizerPairEquivU3.symm

open PatiSalamVacuumStabiliser ElectroweakVacuumStabiliser PatiSalamGaugeAction
  PatiSalamTwoStageStabiliser SkewAdjointExponential PatiSalamChargeCentre

/-- **The `SU(3)` factor is colour**: it acts as `diag(A, 1)` on the `SU(4)` factor and trivially on
both `SU(2)`s. -/
theorem colour_components (A : SU3) :
    ((u3ToFull (splitHom (A, 1))).1 : Matrix (Fin 4) (Fin 4) ℂ) = blockDiag4 A 1 ∧
      (u3ToFull (splitHom (A, 1))).2.1 = 1 ∧ (u3ToFull (splitHom (A, 1))).2.2 = 1 := by
  have hdet : (A : Matrix (Fin 3) (Fin 3) ℂ).det = 1 := (mem_specialUnitaryGroup_iff.mp A.2).2
  have hv : ((splitHom (A, 1) : GroupU3) : Matrix (Fin 3) (Fin 3) ℂ) = A := by
    rw [splitHom_val]; simp
  refine ⟨?_, Subtype.ext ?_, Subtype.ext ?_⟩
  · change blockDiag4 _ (star (splitHom (A, 1) : Matrix (Fin 3) (Fin 3) ℂ).det) = _
    rw [hv, hdet, star_one]
  · change diagConj2 (splitHom (A, 1) : Matrix (Fin 3) (Fin 3) ℂ).det = 1
    rw [hv, hdet, diagConj2_one]
  · change diagConj2 (splitHom (A, 1) : Matrix (Fin 3) (Fin 3) ℂ).det = 1
    rw [hv, hdet, diagConj2_one]

theorem exp_mem_unitary (t : ℝ) : Complex.exp (t * Complex.I) ∈ unitary ℂ := by
  have hn : ‖Complex.exp (t * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I t
  have hs := star_mul_self_of_norm hn
  exact Unitary.mem_iff.mpr ⟨hs, by rw [mul_comm]; exact hs⟩

/-- **The `U(1)` factor is the electric charge.** -/
theorem splitHom_charge (t : ℝ) :
    splitHom (1, ⟨Complex.exp (t * Complex.I), exp_mem_unitary t⟩)
      = stabilizerPairEquivU3 ⟨expFull (t • qFull), charge_mem t⟩ := by
  apply Subtype.ext
  rw [splitHom_val, stabilizerPairEquivU3_charge]
  rfl

end PatiSalamUnbrokenSplit
