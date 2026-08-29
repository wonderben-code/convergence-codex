import CentralIdemInvariant
import CliffordCenter
import Mathlib.Data.Real.Hom

/-!
# ℝ, ℂ and ℍ told apart: the Brauer-type invariant two files have named and neither built

**WHERE THE PHRASE COMES FROM, CHECKED RATHER THAN RECALLED** (`ERRATUM 259`; a first draft of this
sentence attributed it to `W7`'s residue list, which does not contain it, and the review caught
that before the commit). `IdempotentRankInvariant.lean`'s *"NOT proven here"* list ends with
*"the Brauer-class route named in W7 is untouched"*, and what `W7` actually says, in a 4 August
paragraph, is that separating `M₂(ℍ)` from `M₄(ℝ)` *"needs its own argument (orthogonal-idempotent
count **or a Brauer-class invariant**)"*. The count was built; the invariant was not.

This is that invariant, in the only form this estate needs it: **matrix algebras over the three
real division algebras are pairwise non-isomorphic AS RINGS**, at every pair of nonempty finite
index types.

`IdempotentRankInvariant.card_eq_of_ringEquiv` already forces the index types to have the same
size, so what is missing is the base. Two invariants supply it, and they split the work exactly
along the line the classical theory does.

## The two invariants

* **`HasCentralSqrtNegOne`** — a central `z` with `z * z = -1`. `Mₙ(ℂ)` has one, the scalar matrix
  `i`; `Mₙ(ℝ)` and `Mₙ(ℍ)` do not, since a central element of either is a REAL scalar and `r² = -1`
  has no real solution. **That is the ℂ column of the table**, and it is purely ring-theoretic: no
  dimension, no linearity, no base field visible in the statement.
* **`CentreIsReal` and the rigidity lemma.** `Mₙ(ℝ)` and `Mₙ(ℍ)` are not separated by the first
  invariant — both have centre exactly ℝ — and the orthogonal-idempotent count does not separate
  them either, since it is `card n` on both. What separates them is **real dimension, which is a
  RING invariant here and not merely a linear one**.

## Why dimension is a ring invariant between these algebras, which is the one real idea

A ring isomorphism need not respect any base field, and everywhere else in this estate that is the
whole reason the invariants are built ring-theoretically. **Here it does respect one, and the
reason is a fact about ℝ rather than about the algebras**: `Real.RingHom.unique` says the only ring
endomorphism of ℝ is the identity.

So if `φ : A ≃+* B` and both centres are exactly the real scalars, `φ` carries the centre of `A`
onto the centre of `B` — centre membership passes along any ring isomorphism — hence induces a ring
endomorphism of ℝ, hence the identity, hence **`φ (algebraMap ℝ A r) = algebraMap ℝ B r`**
(`map_algebraMap`). Then `φ (r • a) = φ (algebraMap r * a) = algebraMap r * φ a = r • φ a`, so `φ`
is an ℝ-linear equivalence (`toLinearEquiv`) and `finrank_eq_of_ringEquiv` follows.

**`Mₘ(ℝ)` has real dimension `|m|²` and `Mₙ(ℍ)` has `4|n|²`**, and the size theorem already forces
`|m| = |n|`, so an isomorphism would give `c² = 4c²` and `c = 0`.

## What this does and does not settle

**Settled**: the three families are pairwise distinct as rings, so the eight-fold table's entries
are distinguished by their *type* and not only by their size. With
`IdempotentRankInvariant.card_eq_of_ringEquiv` this is the full statement for matrix algebras over
the three division algebras.

**And the dimension half is stated at the generality its proof has**, not at the two algebras it
was built for: **`card_and_finrank_eq_of_ringEquiv`** says that for **any** finite-dimensional real
division algebras `D`, `D'` whose centre is the real scalars, a ring isomorphism `Mₘ(D) ≃+* Mₙ(D')`
forces `card m = card n` **and** `dim_ℝ D = dim_ℝ D'`. `ℝ` and `ℍ` are instances; `ℂ` deliberately
is not, since its centre is itself — **so the file's two invariants divide the work exactly along
the line "is the centre bigger than `ℝ`", and neither is doing the other's job.** The two ad-hoc
centre computations collapse the same way: `centreIsReal_matrix` carries a real centre from any
base to its matrix algebras, and `centreIsReal_matrixR` / `centreIsReal_matrixH` are its instances
at `ℝ` and `ℍ` (`ERRATUM 201`).

**NOT settled, and it is the natural next sentence a reader will want**: that `ℝ`, `ℂ` and `ℍ` are
the ONLY finite-dimensional real division algebras. That is Frobenius's theorem, and **it is absent
from this Mathlib — probed by shape rather than by name** (`ERRATUM 42`): the 37 files matching
`Frobenius` are the characteristic-`p` endomorphism, the Frobenius number and Frobenius elements in
Galois theory, `DivisionAlgebra` occurs only as a section name, and `frobenius_theorem` is zero.
**So this file distinguishes three algebras; it does not say they exhaust anything**, and every
statement here is about the three named families only.

**Not settled, and not claimed**: this says nothing about *split* algebras — products — beyond what
`CentralIdemInvariant` already proves, and it is not a classification of real Clifford algebras.
Turning it into one needs every `Cl(p,q;ℝ)` identified as a named matrix algebra or a product of
two, which the estate has on the diagonals and through `clifford_reduce_named` only when
`p − q ≡ 0 (mod 8)`. **That is named as the missing step and is not attempted here; no cost is
claimed** (`ERRATUM 246`).

**The rigidity lemma is about ℝ specifically and does not generalise to ℂ — and that is a theorem
here, not an aside.** `exists_ne_id_ringHom_complex` exhibits conjugation, so the step that
`Real.RingHom.unique` licenses is simply false over a complex base. **A first draft asserted this in
the file's own voice without proving it**, which is `ERRATUM 46`'s defect exactly — an external fact
stated among machine-checked neighbours — and the review turned it into four lines instead. It is
also why the complex classification in `CentralIdemInvariant` had to be done without dimension at
all.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RealDivisionTrichotomy

open scoped Quaternion

/-! ## 1. Centre membership passes along a ring isomorphism -/

/-- **CENTRE MEMBERSHIP PASSES ALONG ANY RING ISOMORPHISM.** `CliffordCenter.mem_center_congr` is
the `AlgEquiv` form; this is the `RingEquiv` one, which is what everything below consumes and what
`CentralIdemInvariant.OnlyTrivialCentralIdem.of_ringEquiv` had inlined. -/
theorem mem_center_ringEquiv {A B : Type*} [Ring A] [Ring B] (f : A ≃+* B) {x : A} :
    x ∈ Set.center A ↔ f x ∈ Set.center B := by
  simp only [Semigroup.mem_center_iff]
  constructor
  · intro h b
    obtain ⟨a, rfl⟩ := f.surjective b
    rw [← map_mul, ← map_mul, h a]
  · intro h a
    exact f.injective (by rw [map_mul, map_mul, h (f a)])

/-! ## 2. A central square root of `-1`, and who has one -/

/-- **THE ℂ-COLUMN INVARIANT.** A ring with a central `z` satisfying `z * z = -1`. -/
def HasCentralSqrtNegOne (A : Type*) [Ring A] : Prop :=
  ∃ z : A, z ∈ Set.center A ∧ z * z = -1

theorem HasCentralSqrtNegOne.of_ringEquiv {A B : Type*} [Ring A] [Ring B] (f : A ≃+* B)
    (h : HasCentralSqrtNegOne A) : HasCentralSqrtNegOne B := by
  obtain ⟨z, hz, hsq⟩ := h
  exact ⟨f z, (mem_center_ringEquiv f).mp hz, by rw [← map_mul, hsq, map_neg, map_one]⟩

/-- **THE CENTRE IS NO BIGGER THAN THE REAL SCALARS.** The hypothesis both halves of the
trichotomy's ℝ/ℍ side rest on. -/
def CentreIsReal (A : Type*) [Ring A] [Algebra ℝ A] : Prop :=
  Set.center A ⊆ Set.range (algebraMap ℝ A)

/-- **AN ALGEBRA WITH REAL CENTRE HAS NO CENTRAL SQUARE ROOT OF `-1`**, because `r * r = -1` has no
real solution. -/
theorem not_hasCentralSqrtNegOne {A : Type*} [Ring A] [Algebra ℝ A] [Nontrivial A]
    (h : CentreIsReal A) : ¬ HasCentralSqrtNegOne A := by
  rintro ⟨z, hz, hsq⟩
  obtain ⟨r, rfl⟩ := h hz
  have heq : algebraMap ℝ A (r * r) = algebraMap ℝ A (-1) := by
    rw [map_mul, hsq, map_neg, map_one]
  have hr : r * r = -1 := (algebraMap ℝ A).injective heq
  nlinarith [mul_self_nonneg r]

/-- **HAVING A REAL CENTRE PASSES TO MATRIX ALGEBRAS**, over any base. Mathlib's
`Matrix.center_eq_scalar_image` computes the centre over a **non-commutative** base as the scalar
image of the base's centre, so nothing here asks the base to be commutative — which is what makes
`ℍ` an instance rather than a separate computation. -/
theorem centreIsReal_matrix {D : Type*} [Ring D] [Algebra ℝ D] {n : Type*} [Fintype n]
    [DecidableEq n] (h : CentreIsReal D) : CentreIsReal (Matrix n n D) := by
  intro x hx
  rw [Matrix.center_eq_scalar_image] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  obtain ⟨r, rfl⟩ := h hc
  exact ⟨r, (CliffordCenter.algebraMap_eq_scalar r).symm⟩

/-- `ℝ` has real centre, trivially: it is commutative and `algebraMap ℝ ℝ` is the identity. -/
theorem centreIsReal_real : CentreIsReal ℝ := fun r _ => ⟨r, rfl⟩

/-- `ℍ` has real centre — `QuaternionCenter.center_eq_range`, the statement Mathlib does not
carry because its matrix-centre theorem for a commutative base cannot see it. -/
theorem centreIsReal_quaternion : CentreIsReal ℍ[ℝ] := by
  intro x hx
  rw [QuaternionCenter.center_eq_range] at hx
  exact hx

/-- `Mₙ(ℝ)` has real centre — the instance at `D = ℝ` (`ERRATUM 201`). -/
theorem centreIsReal_matrixR {n : Type*} [Fintype n] [DecidableEq n] :
    CentreIsReal (Matrix n n ℝ) :=
  centreIsReal_matrix centreIsReal_real

/-- `Mₙ(ℍ)` has real centre — the instance at `D = ℍ`. -/
theorem centreIsReal_matrixH {n : Type*} [Fintype n] [DecidableEq n] :
    CentreIsReal (Matrix n n ℍ[ℝ]) :=
  centreIsReal_matrix centreIsReal_quaternion

/-- `Mₙ(ℂ)` DOES have one: the scalar matrix `i`. -/
theorem hasCentralSqrtNegOne_matrixC {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    HasCentralSqrtNegOne (Matrix n n ℂ) := by
  refine ⟨Matrix.scalar n Complex.I, ?_, ?_⟩
  · rw [Matrix.center_eq_range]
    exact ⟨Complex.I, rfl⟩
  · rw [← map_mul, Complex.I_mul_I, map_neg, map_one]

/-! ## 3. Rigidity: over ℝ, a ring isomorphism of central algebras is ℝ-linear -/

/-- **A RING ISOMORPHISM BETWEEN REAL-CENTRED ℝ-ALGEBRAS FIXES THE SCALARS.** The centre of `A`
goes to the centre of `B`; both are the real scalars; so `φ` induces a ring endomorphism of `ℝ`,
and `Real.RingHom.unique` says that is the identity. **This is a fact about ℝ, not about the
algebras**, and it is false over ℂ. -/
theorem map_algebraMap {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]
    [Nontrivial B] (hB : CentreIsReal B) (φ : A ≃+* B) (r : ℝ) :
    φ (algebraMap ℝ A r) = algebraMap ℝ B r := by
  classical
  have hcen : ∀ s : ℝ, algebraMap ℝ A s ∈ Set.center A := fun s =>
    Semigroup.mem_center_iff.2 fun a => (Algebra.commutes s a).symm
  have hmem : ∀ s : ℝ, φ (algebraMap ℝ A s) ∈ Set.range (algebraMap ℝ B) := fun s =>
    hB ((mem_center_ringEquiv φ).mp (hcen s))
  set g : ℝ → ℝ := fun s => Classical.choose (hmem s) with hgdef
  have hg : ∀ s : ℝ, algebraMap ℝ B (g s) = φ (algebraMap ℝ A s) := fun s =>
    Classical.choose_spec (hmem s)
  have hinj := (algebraMap ℝ B).injective
  have hone : g 1 = 1 := hinj (by rw [hg]; simp)
  have hzero : g 0 = 0 := hinj (by rw [hg]; simp)
  have hmul : ∀ s t, g (s * t) = g s * g t := fun s t =>
    hinj (by rw [hg, map_mul, map_mul, ← hg, ← hg, map_mul])
  have hadd : ∀ s t, g (s + t) = g s + g t := fun s t =>
    hinj (by rw [hg, map_add, map_add, ← hg, ← hg, map_add])
  let G : ℝ →+* ℝ := ⟨⟨⟨g, hone⟩, hmul⟩, hzero, hadd⟩
  have hGid : G = RingHom.id ℝ := Subsingleton.elim _ _
  have : g r = r := congrFun (congrArg (fun h : ℝ →+* ℝ => (h : ℝ → ℝ)) hGid) r
  rw [← hg, this]

/-- The same isomorphism as an `ℝ`-linear equivalence. -/
def toLinearEquiv {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]
    [Nontrivial B] (hB : CentreIsReal B) (φ : A ≃+* B) : A ≃ₗ[ℝ] B where
  toFun := φ
  map_add' := map_add φ
  map_smul' := fun r a => by
    simp only [RingHom.id_apply, Algebra.smul_def, map_mul, map_algebraMap hB φ r]
  invFun := φ.symm
  left_inv := φ.left_inv
  right_inv := φ.right_inv

/-- **HENCE REAL DIMENSION IS A RING INVARIANT BETWEEN REAL-CENTRED ℝ-ALGEBRAS.** -/
theorem finrank_eq_of_ringEquiv {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]
    [Nontrivial B] (hB : CentreIsReal B) (φ : A ≃+* B) :
    Module.finrank ℝ A = Module.finrank ℝ B :=
  (toLinearEquiv hB φ).finrank_eq

/-- **AND THE SAME ARGUMENT IS FALSE OVER ℂ**, which is why `map_algebraMap` is stated over ℝ and
why `CentralIdemInvariant`'s complex classification uses no dimension anywhere. Conjugation is a
ring endomorphism of `ℂ` other than the identity, so `Subsingleton (ℂ →+* ℂ)` fails and the step
`Real.RingHom.unique` licenses has no complex analogue. -/
theorem exists_ne_id_ringHom_complex : ∃ f : ℂ →+* ℂ, f ≠ RingHom.id ℂ := by
  refine ⟨starRingEnd ℂ, fun h => ?_⟩
  have h1 : (starRingEnd ℂ) Complex.I = Complex.I := by rw [h]; rfl
  rw [Complex.conj_I] at h1
  exact Complex.I_ne_zero (by linear_combination (-1 / 2 : ℂ) * h1)

/-! ## 4. The trichotomy -/

variable {m n : Type} [Fintype m] [Nonempty m] [Fintype n] [Nonempty n]

/- The three statements below are about `RingEquiv`s, which see only `Mul` and `Add`, so no
`DecidableEq` appears in any of their types; the unit matrix inside each proof needs one and gets
it from `classical`. Same reading as `CentralIdemInvariant.isEmpty_ringEquiv_matrix_of_prod`. -/

/-- **`Mₘ(ℝ) ≇ Mₙ(ℂ)`**, at every pair of nonempty finite index types. -/
theorem matrixR_not_ringEquiv_matrixC : IsEmpty (Matrix m m ℝ ≃+* Matrix n n ℂ) := by
  classical
  exact ⟨fun φ => not_hasCentralSqrtNegOne centreIsReal_matrixR
    (HasCentralSqrtNegOne.of_ringEquiv φ.symm hasCentralSqrtNegOne_matrixC)⟩

/-- **`Mₘ(ℍ) ≇ Mₙ(ℂ)`**, at every pair of nonempty finite index types. -/
theorem matrixH_not_ringEquiv_matrixC : IsEmpty (Matrix m m ℍ[ℝ] ≃+* Matrix n n ℂ) := by
  classical
  exact ⟨fun φ => not_hasCentralSqrtNegOne centreIsReal_matrixH
    (HasCentralSqrtNegOne.of_ringEquiv φ.symm hasCentralSqrtNegOne_matrixC)⟩

omit [Nonempty m] in
/-- **THE DIMENSION HALF AT ITS PROPER GENERALITY.** For finite-dimensional real division algebras
whose centre is the real scalars, a **ring** isomorphism `Mₘ(D) ≃+* Mₙ(D')` forces both the index
size and the base's real dimension to agree.

`ℝ` and `ℍ` are the instances; **`ℂ` is deliberately not one**, because its centre is itself, and
that case is what `HasCentralSqrtNegOne` is for. So the trichotomy's two invariants divide the work
exactly along the line "is the centre bigger than `ℝ`", and neither is doing the other's job. -/
theorem card_and_finrank_eq_of_ringEquiv {D D' : Type} [DivisionRing D] [Algebra ℝ D]
    [FiniteDimensional ℝ D] [DivisionRing D'] [Algebra ℝ D'] [FiniteDimensional ℝ D']
    (hD' : CentreIsReal D') (φ : Matrix m m D ≃+* Matrix n n D') :
    Fintype.card m = Fintype.card n ∧ Module.finrank ℝ D = Module.finrank ℝ D' := by
  classical
  have hcard : Fintype.card m = Fintype.card n :=
    IdempotentRankInvariant.card_eq_of_ringEquiv φ
  refine ⟨hcard, ?_⟩
  have hdim := finrank_eq_of_ringEquiv (centreIsReal_matrix hD') φ
  rw [Module.finrank_matrix, Module.finrank_matrix, hcard] at hdim
  have hpos : 0 < Fintype.card n := Fintype.card_pos
  have hne : Fintype.card n * Fintype.card n ≠ 0 := by positivity
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) hdim

omit [Nonempty m] in
/-- **`Mₘ(ℝ) ≇ Mₙ(ℍ)`**, at every pair of nonempty finite index types — the case neither the
central-square-root invariant nor the orthogonal-idempotent count reaches, since both algebras have
real centre and both admit exactly `card` orthogonal idempotents. **Dimension does it, and
`finrank_eq_of_ringEquiv` is what makes dimension available to a RING isomorphism.** -/
theorem matrixR_not_ringEquiv_matrixH : IsEmpty (Matrix m m ℝ ≃+* Matrix n n ℍ[ℝ]) := by
  classical
  refine ⟨fun φ => ?_⟩
  have h := (card_and_finrank_eq_of_ringEquiv centreIsReal_quaternion φ).2
  rw [Module.finrank_self, Quaternion.finrank_eq_four] at h
  exact absurd h (by norm_num)

/-- **AND IT SUBSUMES THE ESTATE'S FIRST SEPARATION OF THIS KIND**, which is the instantiation
`ERRATUM 201` asks for rather than a second proof. `IdempotentRankInvariant.
matrix2H_not_ringEquiv_matrix4R` is the case `m = Fin 4`, `n = Fin 2` — and there the
orthogonal-idempotent count settles it on its own, since `4 ≠ 2`, so **the dimension half of this
file is not what that theorem needed**. The original is kept and is not deleted: other files cite it
by name, and its proof is the specific one. -/
theorem matrix2H_not_ringEquiv_matrix4R_of_trichotomy :
    IsEmpty (Matrix (Fin 2) (Fin 2) ℍ[ℝ] ≃+* Matrix (Fin 4) (Fin 4) ℝ) :=
  ⟨fun φ => (matrixR_not_ringEquiv_matrixH (m := Fin 4) (n := Fin 2)).elim φ.symm⟩

end RealDivisionTrichotomy
