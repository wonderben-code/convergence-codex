import PatiSalamRightSector

/-!
# The commutant of colour in `M₄(ℂ)` is abelian, so no `su(2)` hides inside it

`SMEmbeddingHonest` proves that the estate's three-factor assembly `su(3) ⊕ su(2) ⊕ u(1) → sl₄(ℂ)`
is not an embedding, and is careful to say what it does **not** prove:

> The full nonexistence theorem — NO faithful embedding exists by ANY maps, not just these. The
> load-bearing argument over `ℂ` is representation-theoretic: a 4-dimensional representation of
> `sl₃ ⊕ sl₂` faithful on both factors does not exist (a faithful `sl₃`-summand is a **3** or
> **3̄**, whose **commutant in `ℂ⁴` is abelian**). … Neither argument is formalised — both need
> representation/Cartan theory the estate does not have.

**The clause in bold is now proved, for the estate's own colour embedding, and it needs no
representation theory.** `PatiSalamRightSector.eq_diag_of_commutes` computes the commutant of two
colour rotations by fourteen entry equations; this file reads that as a statement about `su(3)`.

## What is proved

> **`mem_colourCommutant_iff`** — `N` commutes with `su3EmbedFn X` for **every** `X` if and only if
> `N = diag(a, a, a, d)`. Both directions; the forward one needs only two `X`.
>
> **`finrank_colourCommutant = 2`** — as a subspace of `M₄(ℂ)` over `ℂ`.
>
> **`colourCommutant_comm`** — any two of them commute. **The commutant is abelian.**
>
> **`bracket_eq_zero_of_mem`** and **`no_sl2_triple`** — a bracket of two elements is zero, so an
> `sl₂` triple `[E, F] = H` inside the commutant forces `H = 0`. **No `su(2)` acts on `ℂ⁴`
> commuting with this colour, by any maps at all.**

## What this does NOT prove, and the gap is named precisely

**It is not `SMEmbeddingHonest`'s nonexistence theorem, and it is not advertised as one.** That
theorem quantifies over *all* faithful `sl₃`-actions on `ℂ⁴`; this file fixes **one** — the block
embedding `su3EmbedFn`, the one the estate actually uses. The missing step is exactly the one that
file names: **that every faithful 4-dimensional representation of `sl₃` is a `3` or a `3̄` plus a
singlet**, which is representation theory this estate still does not have and this file does not
begin. What is closed is the clause that argument *invokes* once it has that step, not the step.

**No Schur-type argument is used or supplied.** `AlgebraicCurvature` records twice that this estate
has no such argument; none is needed here. The commutant is computed from entries: two brackets,
fourteen equations, `diag(a,a,a,d)` left over.

**Nothing about groups.** `su3EmbedFn`'s image is a set of matrices. No exponential, no Lie group,
no manifold.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace ColourCommutant

open Matrix PatiSalamRightSector

/-! ## 1. The two rotations are colour -/

/-- `E₀₁ − E₁₀` as a `3 × 3` matrix. -/
def rotA : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0

/-- `E₀₂ − E₂₀` as a `3 × 3` matrix. -/
def rotB : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun i j => if i = 0 ∧ j = 2 then 1 else if i = 2 ∧ j = 0 then -1 else 0

theorem so3A_eq : so3A = su3EmbedFn rotA := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [so3A, su3EmbedFn, rotA, Matrix.of_apply]

theorem so3B_eq : so3B = su3EmbedFn rotB := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [so3B, su3EmbedFn, rotB, Matrix.of_apply]

/-! ## 2. The block-scalar matrices, as a two-dimensional subspace -/

/-- `(a, d) ↦ diag(a, a, a, d)`, linearly. -/
noncomputable def blockScalarMap : (ℂ × ℂ) →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ where
  toFun p := Matrix.diagonal ![p.1, p.1, p.1, p.2]
  map_add' p q := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_smul' c p := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

@[simp] theorem blockScalarMap_apply (a d : ℂ) :
    blockScalarMap (a, d) = Matrix.diagonal ![a, a, a, d] := rfl

/-- **THE COMMUTANT OF COLOUR**, as a subspace: the image of `blockScalarMap`.
`mem_colourCommutant_iff` below is the reason the name is earned. -/
noncomputable def colourCommutant : Submodule ℂ (Matrix (Fin 4) (Fin 4) ℂ) :=
  LinearMap.range blockScalarMap

theorem blockScalarMap_injective : Function.Injective blockScalarMap := by
  intro p q h
  have h0 := congrFun (congrFun h 0) 0
  have h3 := congrFun (congrFun h 3) 3
  simp only [blockScalarMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.diagonal_apply_eq] at h0 h3
  exact Prod.ext (by simpa using h0) (by simpa using h3)

/-- **TWO DIMENSIONS**, over `ℂ`: one for the colour block, one for the fourth slot. -/
theorem finrank_colourCommutant : Module.finrank ℂ colourCommutant = 2 := by
  rw [colourCommutant, LinearMap.finrank_range_of_inj blockScalarMap_injective,
    Module.finrank_prod, Module.finrank_self]

/-! ## 3. It really is the commutant -/

/-- **EVERY BLOCK-SCALAR COMMUTES WITH EVERY COLOUR MATRIX.** The colour block is scaled by `a` on
both sides and the fourth slot is never reached. -/
theorem blockScalar_comm (a d : ℂ) (X : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix.diagonal ![a, a, a, d] * su3EmbedFn X
      = su3EmbedFn X * Matrix.diagonal ![a, a, a, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, su3EmbedFn, Matrix.diagonal_apply, mul_comm]

/-- **AND NOTHING ELSE DOES.** The forward direction needs only `rotA` and `rotB`, so the
characterisation is genuinely a computation and not a quantifier trick: two colour matrices already
pin `N` down, and the remaining ones are then free. -/
theorem mem_colourCommutant_iff (N : Matrix (Fin 4) (Fin 4) ℂ) :
    (∀ X : Matrix (Fin 3) (Fin 3) ℂ, N * su3EmbedFn X = su3EmbedFn X * N)
      ↔ N ∈ colourCommutant := by
  constructor
  · intro h
    refine ⟨(N 0 0, N 3 3), ?_⟩
    have hA : N * so3A = so3A * N := by rw [so3A_eq]; exact h rotA
    have hB : N * so3B = so3B * N := by rw [so3B_eq]; exact h rotB
    exact (eq_diag_of_commutes hA hB).symm
  · rintro ⟨⟨a, d⟩, rfl⟩ X
    exact blockScalar_comm a d X

/-! ## 4. Abelian, and therefore no `su(2)` -/

/-- **THE COMMUTANT IS ABELIAN.** Two diagonal matrices commute; that is the whole proof, and it is
the clause `SMEmbeddingHonest` names as load-bearing. -/
theorem colourCommutant_comm {N M : Matrix (Fin 4) (Fin 4) ℂ}
    (hN : N ∈ colourCommutant) (hM : M ∈ colourCommutant) : N * M = M * N := by
  obtain ⟨⟨a, d⟩, rfl⟩ := hN
  obtain ⟨⟨b, e⟩, rfl⟩ := hM
  simp only [blockScalarMap_apply, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem bracket_eq_zero_of_mem {N M : Matrix (Fin 4) (Fin 4) ℂ}
    (hN : N ∈ colourCommutant) (hM : M ∈ colourCommutant) : N * M - M * N = 0 :=
  sub_eq_zero.mpr (colourCommutant_comm hN hM)

/-- **NO `sl₂` TRIPLE LIVES IN THE COMMUTANT OF COLOUR.** If `E` and `F` both commute with the
colour block then their bracket is zero, so the Cartan element of any `sl₂` triple built from them
is zero — and a triple with `H = 0` is not faithful.

**This is the upgrade over `SMEmbeddingHonest`.** That file refutes *the three particular maps* it
assembles. This refutes **every** `su(2)` that commutes with this colour, by any maps whatever: the
obstruction is not a property of the maps but of the commutant. What is still missing for the full
nonexistence theorem is the other half — that a faithful `sl₃` on `ℂ⁴` must look like this one. -/
theorem no_sl2_triple {E F H : Matrix (Fin 4) (Fin 4) ℂ}
    (hE : E ∈ colourCommutant) (hF : F ∈ colourCommutant)
    (hEF : E * F - F * E = H) : H = 0 := by
  rw [← hEF]
  exact bracket_eq_zero_of_mem hE hF

/-- The same statement in the form the refutation is usually quoted in: a nonzero Cartan is
impossible. -/
theorem no_sl2_triple' {E F H : Matrix (Fin 4) (Fin 4) ℂ}
    (hE : E ∈ colourCommutant) (hF : F ∈ colourCommutant)
    (hEF : E * F - F * E = H) (hH : H ≠ 0) : False :=
  hH (no_sl2_triple hE hF hEF)

end ColourCommutant
