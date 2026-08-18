import CliffordRealTwoZero
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# `ℍ ⊗[ℝ] ℍ ≅ M₄(ℝ)`

**Not available off the shelf** (`ERRATUM 211`'s wording, and it is the strongest the count
supports). Eight Mathlib files mention `Quaternion`; **none of them contains a `⊗`**, and none
mentions `Matrix (Fin 4)`. So the library has no statement tensoring quaternions with anything, and
this file supplies the one the eight-fold periodicity needs.

> **`equivM4`** — `ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] M₄(ℝ)`.

## The map

`q ⊗ r ↦ (x ↦ q · x · star r)`, acting on `ℍ` seen as a four-dimensional real space. Two facts
make it an algebra map out of the **ordinary** tensor product:

* `x ↦ x · star r` is a homomorphism, not an anti-homomorphism, because `star` already reverses:
  `(x · star r₂) · star r₁ = x · star (r₁ · r₂)`;
* left and right multiplication commute, which is associativity and nothing more.

`Algebra.TensorProduct.lift` consumes exactly that pair, and this is the whole of why the
construction is short. The graded tensor product — the only Clifford decomposition Mathlib carries
— is not involved anywhere.

## Surjectivity without sixteen matrix units

The classical route exhibits sixteen matrix units. This one exhibits **four** elements, because the
range of an algebra map is closed under multiplication and one distinguished element does the work:

`t₀ = ¼ (1⊗1 + i⊗i + j⊗j + k⊗k)`  maps to  `x ↦ (re x : ℍ)`,

the projection onto the real line. Since `re (star (e b) * x)` is the `b`-th coordinate of `x`, the
element `(f (e b) ⊗ 1) · t₀ · (star (e b) ⊗ 1)` maps to `x ↦ f (e b) · xᵦ` — a rank-one map whose
image already carries an arbitrary quaternion. Summing over the four basis vectors reconstructs an
arbitrary endomorphism, so the preimage of `f` is a four-term sum written down directly.

Injectivity is then free: both sides have real dimension `16`.
-/

namespace QuaternionTensor

open scoped Quaternion TensorProduct

noncomputable section

/-- `x ↦ x * star r`, as a real-linear endomorphism of `ℍ`. -/
def rmulStarLin (r : ℍ[ℝ]) : Module.End ℝ ℍ[ℝ] where
  toFun x := x * star r
  map_add' _ _ := add_mul _ _ _
  map_smul' c x := by simp

@[simp]
theorem rmulStarLin_apply (r x : ℍ[ℝ]) : rmulStarLin r x = x * star r := rfl

/-- Right multiplication by `star r`.  A homomorphism, not an anti-homomorphism, because `star`
reverses the order and the two reversals cancel. -/
def rmulStar : ℍ[ℝ] →ₐ[ℝ] Module.End ℝ ℍ[ℝ] where
  toFun := rmulStarLin
  map_one' := by refine LinearMap.ext fun x => ?_; simp
  map_mul' r₁ r₂ := by
    refine LinearMap.ext fun x => ?_
    simp [Module.End.mul_apply, star_mul, mul_assoc]
  map_zero' := by refine LinearMap.ext fun x => ?_; simp
  map_add' r₁ r₂ := by refine LinearMap.ext fun x => ?_; simp [mul_add]
  commutes' c := by
    refine LinearMap.ext fun x => ?_
    simp [Algebra.algebraMap_eq_smul_one]

@[simp]
theorem rmulStar_apply (r x : ℍ[ℝ]) : rmulStar r x = x * star r := rfl

/-- Associativity, and nothing more. -/
theorem commute_lmul_rmulStar (q r : ℍ[ℝ]) :
    Commute (Algebra.lmul ℝ ℍ[ℝ] q) (rmulStar r) := by
  change Algebra.lmul ℝ ℍ[ℝ] q * rmulStar r = rmulStar r * Algebra.lmul ℝ ℍ[ℝ] q
  refine LinearMap.ext fun x => ?_
  simp [Module.End.mul_apply, mul_assoc]

/-- `ℍ ⊗ ℍ → End ℝ ℍ`, `q ⊗ r ↦ (x ↦ q · x · star r)`. -/
def hMap : ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] →ₐ[ℝ] Module.End ℝ ℍ[ℝ] :=
  Algebra.TensorProduct.lift (Algebra.lmul ℝ ℍ[ℝ]) rmulStar commute_lmul_rmulStar

@[simp]
theorem hMap_tmul (q r x : ℍ[ℝ]) : hMap (q ⊗ₜ[ℝ] r) x = q * x * star r := by
  simp [hMap, Algebra.TensorProduct.lift_tmul, Module.End.mul_apply, mul_assoc]

/-- The standard basis `1, i, j, k`. -/
def e : Fin 4 → ℍ[ℝ] := ![1, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

/-- Every quaternion is its own coordinate expansion in `e`, with coordinates read off by
`x ↦ re (star (e b) * x)`. -/
theorem sum_coord (x : ℍ[ℝ]) : ∑ b : Fin 4, ((star (e b) * x).re) • e b = x := by
  simp [Fin.sum_univ_four, e, Quaternion.ext_iff]

/-- The element whose image is the projection onto the real line. -/
def t₀ : ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] := (4⁻¹ : ℝ) • ∑ b : Fin 4, e b ⊗ₜ[ℝ] e b

theorem hMap_t₀ (x : ℍ[ℝ]) : hMap t₀ x = (x.re : ℝ) • (1 : ℍ[ℝ]) := by
  simp [t₀, Fin.sum_univ_four, e, Quaternion.ext_iff]
  ring

/-- **The rank-one map, named rather than left inside a proof.** `t₀` is the projection onto the
real line and the range of an algebra map is closed under multiplication, so conjugating it moves
an arbitrary quaternion into the image: this element maps to `x ↦ xᵦ • q`, the matrix unit of the
`(q, b)` slot. -/
theorem hMap_rankOne (q : ℍ[ℝ]) (b : Fin 4) (x : ℍ[ℝ]) :
    hMap ((q ⊗ₜ[ℝ] (1 : ℍ[ℝ])) * t₀ * (star (e b) ⊗ₜ[ℝ] (1 : ℍ[ℝ]))) x
      = ((star (e b) * x).re) • q := by
  rw [map_mul, map_mul]
  simp [Module.End.mul_apply, hMap_t₀]

/-- **Surjectivity, in four terms rather than sixteen.** Summing the rank-one maps of `hMap_rankOne`
over the basis rebuilds an arbitrary endomorphism. -/
theorem hMap_surjective : Function.Surjective hMap := by
  intro f
  refine ⟨∑ b : Fin 4, (f (e b) ⊗ₜ[ℝ] (1 : ℍ[ℝ])) * t₀ * (star (e b) ⊗ₜ[ℝ] (1 : ℍ[ℝ])), ?_⟩
  refine LinearMap.ext fun x => ?_
  have hx : f x = ∑ b : Fin 4, ((star (e b) * x).re) • f (e b) := by
    conv_lhs => rw [← sum_coord x]
    rw [map_sum]
    simp
  rw [map_sum, LinearMap.sum_apply, hx]
  exact Finset.sum_congr rfl fun b _ => hMap_rankOne (f (e b)) b x

theorem finrank_quatTensor : Module.finrank ℝ (ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]) = 16 := by
  rw [Module.finrank_tensorProduct, Quaternion.finrank_eq_four]

theorem finrank_quatEnd : Module.finrank ℝ (Module.End ℝ ℍ[ℝ]) = 16 := by
  change Module.finrank ℝ (ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ]) = 16
  rw [Module.finrank_linearMap, Quaternion.finrank_eq_four]

/-- Injectivity is free: both sides are `16`-dimensional over `ℝ`. -/
theorem hMap_injective : Function.Injective hMap :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (V := ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]) (V₂ := Module.End ℝ ℍ[ℝ])
    (by rw [finrank_quatTensor, finrank_quatEnd])).2 hMap_surjective

/-- `ℍ ⊗[ℝ] ℍ ≃ₐ[ℝ] End ℝ ℍ`. -/
def equivEnd : ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] Module.End ℝ ℍ[ℝ] :=
  AlgEquiv.ofBijective hMap ⟨hMap_injective, hMap_surjective⟩

/-- The canonical basis `1, i, j, k`, so the matrix realisation below is a computation in a named
basis rather than in an arbitrary one. -/
def quatBasis : Module.Basis (Fin 4) ℝ ℍ[ℝ] :=
  QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1)

@[simp]
theorem equivEnd_apply (t : ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]) (x : ℍ[ℝ]) : equivEnd t x = hMap t x := rfl

theorem equivEnd_tmul (q r x : ℍ[ℝ]) : equivEnd (q ⊗ₜ[ℝ] r) x = q * x * star r := by
  simp

/-- **`ℍ ⊗[ℝ] ℍ ≃ₐ[ℝ] M₄(ℝ)`.** Not available off the shelf; see the header. -/
def equivM4 : ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
  equivEnd.trans (algEquivMatrix quatBasis)

end

end QuaternionTensor
