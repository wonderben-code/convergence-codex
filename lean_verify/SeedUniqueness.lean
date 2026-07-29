/-
  SeedUniqueness: M₂(ℂ) Is Forced — the Wedderburn–Artin Route
  ============================================================

  Addresses: the seed-uniqueness gap (tree §3, published tag [META, OPEN];
  old gap list #1). The published claim: among algebras satisfying the four
  seed constraints (minimal, non-commutative, finite-dimensional,
  trace-faithful), M₂(ℂ) is the unique choice. Previously nothing beyond
  small type-theory facts (SeedForced.lean) existed in Lean.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  Working over ℂ with the constraints modelled as: finite-dimensional +
  semisimple + non-commutative ℂ-algebra —

  1. `seed_dim_lower_bound` — every non-commutative finite-dimensional
     semisimple ℂ-algebra has dimension ≥ 4. (Wedderburn–Artin over ℂ
     decomposes A ≅ Π Mₙᵢ(ℂ); all nᵢ = 1 forces commutativity; hence some
     nᵢ ≥ 2 and dim = Σ nᵢ² ≥ 4.)
  2. `seed_unique_dim_four` — every non-commutative finite-dimensional
     semisimple ℂ-algebra of dimension exactly 4 is isomorphic to M₂(ℂ)
     as a ℂ-algebra. (Σ nᵢ² = 4 with some nᵢ ≥ 2 forces a single factor
     with n = 2.)
  3. `seed_forced` — the package: dim ≥ 4 always, with dim = 4 realised
     exactly by M₂(ℂ). "The minimal non-commutative semisimple algebra
     over ℂ is M₂(ℂ), uniquely" is therefore a THEOREM.
  4. Non-vacuity: `m2_noncommutative`, `m2_finrank` — M₂(ℂ) itself
     satisfies the constraints at dimension 4 (semisimplicity of matrix
     algebras is a Mathlib instance), so the characterised class is
     inhabited and the bound is sharp.

  MODELLING NOTE (the honest joints): the narrative's "trace-faithful C⋆"
  constraint is modelled as SEMISIMPLICITY — for finite-dimensional complex
  algebras this is the standard equivalence (a f.d. C⋆-algebra is semisimple;
  conversely every f.d. semisimple ℂ-algebra carries a C⋆ structure by
  Wedderburn–Artin) — CITED, not formalised; formalising "f.d. C⋆ ⇒
  semisimple" would need Mathlib C⋆-algebra radical theory. "Minimal" is
  rendered as the two theorems: nothing non-commutative exists below
  dimension 4, and dimension 4 is uniquely M₂(ℂ). NOT proven: that physics
  requires these constraints (interpretive, the paper's §3 argument); any
  connection to D = (D→D) (that is L2/L3 of the spine, separate).

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

open Module

noncomputable section

namespace SeedUniqueness

/-- 1×1 matrix algebras (index type with a unique element) are commutative. -/
theorem matrix_unique_comm {m : Type*} [Fintype m] [Unique m]
    (a b : Matrix m m ℂ) : a * b = b * a := by
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_unique, Fintype.sum_unique,
    Unique.eq_default j, Unique.eq_default k, mul_comm]

/-- If every Wedderburn block has size 1, the product algebra is commutative. -/
theorem pi_matrix_comm {n : ℕ} (d : Fin n → ℕ) (h1 : ∀ i, d i = 1)
    (x y : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) : x * y = y * x := by
  funext i
  haveI : Unique (Fin (d i)) := by rw [h1 i]; infer_instance
  exact matrix_unique_comm (x i) (y i)

/-- Transfer of commutativity along an algebra equivalence. -/
theorem comm_of_algEquiv {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A]
    [Algebra ℂ B] (e : A ≃ₐ[ℂ] B) (hB : ∀ x y : B, x * y = y * x)
    (a b : A) : a * b = b * a := by
  have h := hB (e a) (e b)
  rw [← map_mul, ← map_mul] at h
  exact e.injective h

/-- The dimension of the Wedderburn decomposition: finrank A = Σ (d i)². -/
theorem finrank_pi_matrix {n : ℕ} (d : Fin n → ℕ) :
    finrank ℂ (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) = ∑ i, (d i) ^ 2 := by
  rw [Module.finrank_pi_fintype]
  congr 1
  funext i
  rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one, sq]

/-- **The seed dimension bound**: every non-commutative finite-dimensional
    semisimple ℂ-algebra has dimension at least 4. -/
theorem seed_dim_lower_bound (A : Type*) [Ring A] [Algebra ℂ A]
    [FiniteDimensional ℂ A] [IsSemisimpleRing A]
    (hnc : ∃ a b : A, a * b ≠ b * a) : 4 ≤ finrank ℂ A := by
  obtain ⟨n, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ A
  have hrank : finrank ℂ A = ∑ i, (d i) ^ 2 := by
    rw [e.toLinearEquiv.finrank_eq, finrank_pi_matrix]
  by_cases h2 : ∃ i, 2 ≤ d i
  · obtain ⟨i, hi⟩ := h2
    have hle : (d i) ^ 2 ≤ ∑ j, (d j) ^ 2 :=
      Finset.single_le_sum (f := fun j => (d j) ^ 2)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have : 4 ≤ (d i) ^ 2 := by nlinarith
    omega
  · exfalso
    push Not at h2
    have h1 : ∀ i, d i = 1 := fun i => by
      have := (hd i).one_le
      have := h2 i
      omega
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (comm_of_algEquiv e (pi_matrix_comm d h1) a b)

/-- Algebra equivalence over a Pi type with a unique index: the product IS
    its single factor. -/
def piUniqueAlgEquiv {ι : Type*} [Unique ι] (f : ι → Type*)
    [∀ i, Ring (f i)] [∀ i, Algebra ℂ (f i)] :
    (Π i, f i) ≃ₐ[ℂ] f default where
  toFun x := x default
  invFun x := fun i => (Unique.eq_default i).symm ▸ x
  left_inv x := by
    funext i
    have h : i = default := Unique.eq_default i
    subst h
    rfl
  right_inv x := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- **Seed uniqueness at dimension 4**: every non-commutative
    finite-dimensional semisimple ℂ-algebra of dimension 4 is isomorphic to
    M₂(ℂ). -/
theorem seed_unique_dim_four (A : Type*) [Ring A] [Algebra ℂ A]
    [FiniteDimensional ℂ A] [IsSemisimpleRing A]
    (hnc : ∃ a b : A, a * b ≠ b * a) (hdim : finrank ℂ A = 4) :
    Nonempty (A ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨n, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ A
  have hrank : (∑ i, (d i) ^ 2) = 4 := by
    rw [← finrank_pi_matrix, ← e.toLinearEquiv.finrank_eq, hdim]
  -- some block has size ≥ 2, else A is commutative
  have h2 : ∃ i, 2 ≤ d i := by
    by_contra h2
    push Not at h2
    have h1 : ∀ i, d i = 1 := fun i => by
      have := (hd i).one_le
      have := h2 i
      omega
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (comm_of_algEquiv e (pi_matrix_comm d h1) a b)
  obtain ⟨i₀, hi₀⟩ := h2
  -- that block has size exactly 2, and is the only block
  have hle : (d i₀) ^ 2 ≤ 4 := hrank ▸
    Finset.single_le_sum (f := fun j => (d j) ^ 2)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i₀)
  have hd2 : d i₀ = 2 := by nlinarith
  have hrest : ∑ j ∈ Finset.univ.erase i₀, (d j) ^ 2 = 0 := by
    have hsplit := Finset.add_sum_erase Finset.univ (fun j => (d j) ^ 2)
      (Finset.mem_univ i₀)
    beta_reduce at hsplit
    rw [hrank, hd2] at hsplit
    omega
  have hempty : Finset.univ.erase i₀ = (∅ : Finset (Fin n)) := by
    by_contra hne
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hj1 : 1 ≤ (d j) ^ 2 := by
      have := (hd j).one_le
      nlinarith
    have : 1 ≤ ∑ k ∈ Finset.univ.erase i₀, (d k) ^ 2 :=
      le_trans hj1 (Finset.single_le_sum (f := fun k => (d k) ^ 2)
        (fun k _ => Nat.zero_le _) hj)
    omega
  -- so the index type has a unique element i₀
  haveI : Unique (Fin n) := by
    refine ⟨⟨i₀⟩, fun j => ?_⟩
    by_contra hji
    have : j ∈ Finset.univ.erase i₀ := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
    rw [hempty] at this
    exact absurd this (Finset.notMem_empty j)
  -- collapse the product and reindex the block to Fin 2
  have hdd : d default = 2 := by
    have : (default : Fin n) = i₀ := Unique.eq_default i₀ ▸ rfl
    rw [show (default : Fin n) = i₀ from (Unique.eq_default i₀).symm, hd2]
  exact ⟨e.trans ((piUniqueAlgEquiv _).trans
    (Matrix.reindexAlgEquiv ℂ ℂ (finCongr hdd)))⟩

/-- **The seed is forced** (the package): a non-commutative finite-dimensional
    semisimple ℂ-algebra has dimension ≥ 4, and dimension 4 is realised
    uniquely by M₂(ℂ). -/
theorem seed_forced (A : Type*) [Ring A] [Algebra ℂ A]
    [FiniteDimensional ℂ A] [IsSemisimpleRing A]
    (hnc : ∃ a b : A, a * b ≠ b * a) :
    4 ≤ finrank ℂ A ∧
      (finrank ℂ A = 4 → Nonempty (A ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)) :=
  ⟨seed_dim_lower_bound A hnc, seed_unique_dim_four A hnc⟩

/-! ## Non-vacuity: M₂(ℂ) itself satisfies the constraints -/

/-- M₂(ℂ) is non-commutative (witness: the two nilpotent shift matrices). -/
theorem m2_noncommutative :
    ∃ a b : Matrix (Fin 2) (Fin 2) ℂ, a * b ≠ b * a := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], fun h => ?_⟩
  have h00 := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_succ] at h00

/-- dim M₂(ℂ) = 4. -/
theorem m2_finrank : finrank ℂ (Matrix (Fin 2) (Fin 2) ℂ) = 4 := by
  rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self]

end SeedUniqueness
