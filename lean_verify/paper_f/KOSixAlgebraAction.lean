/-
  KOSixAlgebraAction: the KO-6 triple's "algebra representation" is NOT a representation
  of the algebra, and here is the one that is

  SPINE LINK L18 ("Spectral triple"), and the L6 connection it was supposed to carry.

  THE FINDING, AND IT IS MACHINE-CHECKED. `KOSixSpectralTriple` is the estate's best
  spectral-triple file and its header says, at item 5:

  > *"The algebra. `piRep` is a unital *-representation of Mₙ(ℂ): `piRep_one`,
  > `piRep_mul`, `piRep_add`, `piRep_smul`, `piRep_adjoint` … and `piRep_injective`."*

  **`piRep` is not a representation of the algebra.** Its definition is

  > `piRep a v = ((a *ᵥ v.1.1, a *ᵥ v.1.2), (v.2.1, v.2.2))`

  — the two antiparticle blocks are returned **unchanged**, i.e. acted on by the identity
  matrix whatever `a` is. So `piRep` is `(a ⊕ a) ⊕ (1 ⊕ 1)`: unital and multiplicative,
  and **not additive in `a`**. `piRep_not_additive_in_matrix` proves the negation
  outright, with an explicit witness; `piRep_additive_iff_antiparticle_zero` gives the
  sharp statement — additivity at `v` holds **exactly** when `v`'s antiparticle part
  vanishes, so the failure is not an edge case but the generic one.

  **The two theorems the header cites as evidence are about a different variable.**
  `piRep_add` says `piRep a (u + v) = piRep a u + piRep a v` and `piRep_smul` says
  `piRep a (c • v) = c • piRep a v`. Both are linearity in the VECTOR, which is what a
  representation needs of each operator; neither says anything about additivity in the
  ALGEBRA ELEMENT, which is what makes a family of operators a representation of a ring.
  `piRep_vector_linear_not_algebra_linear` puts the two side by side so the distinction
  is a theorem rather than a reading.

  WHY THIS MATTERS RATHER THAN BEING A NAMING QUIBBLE. Three things rest on it.
  * **The commutant and order-one conditions of that file are stated for a map that is
    not linear in `a`.** They are true as stated — nothing here withdraws them — but they
    are weaker than "the algebra and its opposite commute", because there is no algebra
    action to commute.
  * **`StarRepSemisimple` cannot be applied to this triple**, and my own file said so for
    the wrong reason. `StarRepSemisimple`'s §1 records the obstacle as *"`Hf n` carries a
    bespoke sesquilinear form `ip` and no Mathlib `InnerProductSpace` instance, so the
    theorem cannot be applied to it without building that instance"* — true, and
    **incomplete**: the theorem takes a `RingHom`, and `piRep` is not one, so building the
    inner-product instance would not have been enough. That sentence is annotated in place
    (`ERRATUM 565`); it named one obstacle when there were two, and the second is the
    harder one.
  * **In Connes' formalism the antiparticle blocks carry the OPPOSITE algebra**, through
    `J π(b) J⁻¹` — which this estate has, as `piOp`. Acting by the identity there instead
    is what makes `piRep` unital on the whole four-block space at the cost of linearity.
    A correct model either acts by `0` on the antiparticles (a non-unital ring hom) or
    puts the algebra on a tensor factor. **Which one the cascade's triple should use is an
    author's decision, not a proof gap**, and it is named in `UNLOCK_WATCHLIST` rather
    than chosen here.

  THE REPRESENTATION THAT IS ONE. `double a = a ⊕ a` on the doubled index type
  `Fin n ⊕ Fin n` — the particle sector's two chiralities, which is the part of the
  estate's geometry where the algebra genuinely acts — is a unital, injective ⋆-ring
  homomorphism (`double_one`, `double_mul`, `double_add`, `double_star`,
  `double_injective`), and `particleRep` composes it with
  `StarRepSemisimple.matrixRep` to land in `Module.End ℂ (EuclideanSpace ℂ (Fin n ⊕ Fin n))`
  with `particleRep_star` the ⋆-condition against Mathlib's inner product. So
  `matrix_isSemisimple_via_particleRep` is `StarRepSemisimple`'s theorem applied to the
  estate's own particle sector: **the shape was right, and it is the four-block extension
  that breaks it.**

  WHAT IS **NOT** CLAIMED.
  * **Nothing is withdrawn from `KOSixSpectralTriple`.** Every theorem in it is true as
    stated (`ERRATUM 94`); what is filed is that its header's item 5 claims more than its
    theorems say, and that two of the five theorems it cites are about the wrong variable.
  * **This is not the cascade's triple either.** `particleRep` is a representation of
    `Mₙ(ℂ)` on a `2n`-dimensional space; no theorem here connects it to `CascadeHilbert`,
    `CascadeAlgebra` or the 96, which is L18's standing residue and unchanged.
  * **No KO-dimension is claimed for `particleRep`.** The doubled space has no `J`, no
    grading and no `D` in this file; the point is the algebra action alone.
  * **The three KO-dimensions (0, 2, 6) still stand as declared data**, and
    `toy_triple_is_kosix_at_one` — the coordinate permutation that would retire the KO-0
    record as an object — is still unbuilt.
    ⚠ BUILT 2026-09-20 (hardening unit 155, `paper_f/ToyTripleIsKOSixAtOne.lean`); the bullet
    is kept as written (`ERRATUM 94`). `toToy : Hf 1 → (Fin 4 → ℂ)` carries `gamma`, `D` and
    `J` onto `chiralityOp`, `diracOp m` (real `m`) and an antidiagonal conjugation `Jtoy`; the
    KO-0 record is now the sign table of a defined map (`Jzero`) on the same two operators.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import KOSixSpectralTriple
import StarRepSemisimple

namespace KOSixAlgebraAction

open Matrix KOSixSpectralTriple
open scoped InnerProductSpace

noncomputable section

variable {n : ℕ}

/-! ## 1. `piRep` is not additive in the algebra element -/

/-- The diagnosis: `piRep a` is `(a ⊕ a)` on the particle blocks and the IDENTITY on the
antiparticle blocks. Stated so the next two theorems read as consequences rather than
as computations. -/
theorem piRep_eq_particle_and_identity (a : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) :
    piRep a v = ((a *ᵥ v.1.1, a *ᵥ v.1.2), (v.2.1, v.2.2)) := rfl

/-- **THE REFUTATION.** `piRep` is not additive in the matrix argument, so it is not a
representation of `Mₙ(ℂ)`. The witness is the simplest possible: `a = b = 0` and a vector
supported on one antiparticle coordinate, where the left side keeps the coordinate and the
right side doubles it. -/
theorem piRep_not_additive_in_matrix :
    ¬ (∀ (a b : Matrix (Fin 1) (Fin 1) ℂ) (v : Hf 1),
        piRep (a + b) v = piRep a v + piRep b v) := by
  intro h
  have hv := h 0 0 (((0, 0), (fun _ => 1, 0)) : Hf 1)
  have h1 := congrFun (congrArg Prod.fst (congrArg Prod.snd hv)) 0
  simp [piRep] at h1

/-- **THE SHARP STATEMENT.** Additivity at a vector `v` holds **exactly** when `v`'s
antiparticle part vanishes. So the failure is the generic case, not an edge case: it is
the whole antiparticle sector. -/
theorem piRep_additive_iff_antiparticle_zero (a b : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) :
    piRep (a + b) v = piRep a v + piRep b v ↔ v.2 = 0 := by
  constructor
  · intro h
    have h2 := congrArg Prod.snd h
    simp only [piRep_eq_particle_and_identity] at h2
    have hz : v.2 = v.2 + v.2 := h2
    have h3 : v.2 + v.2 = v.2 + 0 := by rw [add_zero]; exact hz.symm
    exact add_left_cancel h3
  · intro h
    simp only [piRep_eq_particle_and_identity, Prod.mk_add_mk, Matrix.add_mulVec]
    rw [show v.2.1 = 0 from congrArg Prod.fst h, show v.2.2 = 0 from congrArg Prod.snd h]
    simp

/-- **THE TWO THEOREMS THE HEADER CITES ARE ABOUT A DIFFERENT VARIABLE**, and here they
are side by side with the one it needs. `piRep_add` and `piRep_smul` give linearity in the
VECTOR — which every operator in a representation must have — and additivity in the
ALGEBRA ELEMENT, which is what makes a family of operators a representation of a ring,
fails. -/
theorem piRep_vector_linear_not_algebra_linear :
    (∀ (a : Matrix (Fin 1) (Fin 1) ℂ) (u v : Hf 1),
        piRep a (u + v) = piRep a u + piRep a v)
    ∧ (∀ (a : Matrix (Fin 1) (Fin 1) ℂ) (c : ℂ) (v : Hf 1),
        piRep a (c • v) = c • piRep a v)
    ∧ ¬ (∀ (a b : Matrix (Fin 1) (Fin 1) ℂ) (v : Hf 1),
        piRep (a + b) v = piRep a v + piRep b v) :=
  ⟨fun a u v => piRep_add a u v, fun a c v => piRep_smul a c v,
   piRep_not_additive_in_matrix⟩

/-! ## 2. The representation that IS one: the particle sector's two chiralities -/

/-- `a ↦ a ⊕ a` on the doubled index type. This is the particle sector of the estate's
four-block space — the part where the algebra genuinely acts. -/
def double (a : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := fromBlocks a 0 0 a

theorem double_one : double (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  simp [double, ← fromBlocks_one]

theorem double_mul (a b : Matrix (Fin n) (Fin n) ℂ) :
    double (a * b) = double a * double b := by
  simp [double, fromBlocks_multiply]

/-- **The clause `piRep` lacks.** -/
theorem double_add (a b : Matrix (Fin n) (Fin n) ℂ) :
    double (a + b) = double a + double b := by
  ext i j
  cases i <;> cases j <;> simp [double]

theorem double_star (a : Matrix (Fin n) (Fin n) ℂ) : double aᴴ = (double a)ᴴ := by
  simp [double, fromBlocks_conjTranspose]

theorem double_injective : Function.Injective (double (n := n)) := by
  intro a b h
  have := congrArg (fun M => M.toBlocks₁₁) h
  simpa [double] using this

/-- The doubling, bundled as a ring homomorphism. -/
def doubleHom (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ where
  toFun := double
  map_one' := double_one
  map_mul' := double_mul
  map_zero' := by simp [double, ← fromBlocks_zero]
  map_add' := double_add

/-- The doubled matrix algebra acting on the doubled Euclidean space. The `Fin n`-indexed
version is `StarRepSemisimple.matrixRep`; this is the same construction at the index type
the particle sector actually has. -/
def sumRep (n : ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ →+*
      Module.End ℂ (EuclideanSpace ℂ (Fin n ⊕ Fin n)) where
  toFun A := (Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℂ) A : _ →ₗ[ℂ] _)
  map_one' := by simp
  map_mul' _ _ := by simp
  map_zero' := by simp
  map_add' _ _ := by simp

/-- **THE GENUINE UNITAL ⋆-REPRESENTATION** of `Mₙ(ℂ)` on the particle sector, as a ring
homomorphism into the endomorphisms of a Mathlib inner-product space. -/
def particleRep (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ →+* Module.End ℂ (EuclideanSpace ℂ (Fin n ⊕ Fin n)) :=
  (sumRep n).comp (doubleHom n)

theorem particleRep_injective (n : ℕ) : Function.Injective (particleRep n) := by
  intro a b h
  refine double_injective ?_
  have : Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℂ) (double a)
      = Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℂ) (double b) :=
    ContinuousLinearMap.coe_injective h
  simpa using this

/-- The ⋆-condition against Mathlib's inner product, in exactly the shape
`StarRepSemisimple.isSemisimpleRing_of_faithful_star_rep_complex` takes. -/
theorem particleRep_star (n : ℕ) (a : Matrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n ⊕ Fin n)) :
    ⟪particleRep n a u, v⟫_ℂ = ⟪u, particleRep n (star a) v⟫_ℂ := by
  have h : Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℂ) (double (star a))
      = ContinuousLinearMap.adjoint
        (Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℂ) (double a)) := by
    rw [show double (star a) = star (double a) from double_star a, map_star]; rfl
  change ⟪Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℂ) (double a) u, v⟫_ℂ
      = ⟪u, Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℂ) (double (star a)) v⟫_ℂ
  rw [h, ContinuousLinearMap.adjoint_inner_right]

/-- **`StarRepSemisimple`'s THEOREM, APPLIED TO THE ESTATE'S OWN PARTICLE SECTOR.** So the
shape was right and it is the four-block extension that breaks it: the same argument that
`piRep` cannot supply, `particleRep` supplies. -/
theorem matrix_isSemisimple_via_particleRep (n : ℕ) :
    IsSemisimpleRing (Matrix (Fin n) (Fin n) ℂ) :=
  StarRepSemisimple.isSemisimpleRing_of_faithful_star_rep_complex (𝕜 := ℂ)
    (H := EuclideanSpace ℂ (Fin n ⊕ Fin n)) (particleRep n) (particleRep_injective n)
    (particleRep_star n)

end

end KOSixAlgebraAction
