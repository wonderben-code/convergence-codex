/-
  KOSixInnerProduct: the four-block space with an inner product, and the estate's first
  genuine ⋆-algebra action on it

  SPINE LINK L18 — the Caesar order's item 5, and after the previous unit **the whole
  remaining gap**. `UNLOCK_WATCHLIST` 261's REVISIT line, rewritten yesterday, says it in one
  sentence: *"`piRepC` is the right kind of map and still cannot fill a `Triple`'s `π` field,
  because `Triple` needs `[NormedAddCommGroup H] [InnerProductSpace 𝕜 H]` and `Hf n` is a bare
  product of four `Fin n → ℂ` with no inner-product instance."*

  **THE FIX IS TO CHANGE THE MODEL, NOT TO ADD INSTANCES TO IT.** `KOSixSpectralTriple.Hf n` is
  `((Fin n → ℂ) × (Fin n → ℂ)) × ((Fin n → ℂ) × (Fin n → ℂ))`, and giving *that* an inner
  product means four `WithLp` wrappers and a product-of-products norm, which is where
  `Herm4Gaussian` learned the `def`-not-`abbrev` lesson the hard way — an `abbrev` inherits the
  subtype or product topology and it then competes with the norm topology, and
  `SecondCountableTopology` goes missing while `BorelSpace` succeeds. Re-indexing avoids the
  whole fight: the four blocks of length `n` are one index set `Fin n × Fin 4`, and

  > `HfE n := EuclideanSpace ℂ (Fin n × Fin 4)`

  arrives with `NormedAddCommGroup`, `InnerProductSpace ℂ`, `FiniteDimensional` and
  `CompleteSpace` already in place. **Nothing had to be constructed; the space had to be
  spelled differently.**

  AND THE ACTION IS A BLOCK-DIAGONAL MATRIX, WHICH MAKES EVERY OBLIGATION A MATHLIB LEMMA.
  The repaired action of the previous unit is `a` on the two particle blocks and the entrywise
  conjugate `ā` on the two antiparticle blocks. On the re-indexed space that is exactly

  > `fourBlock a = Matrix.blockDiagonal (fun b => if b.val < 2 then a else mbar a)`

  and then `Matrix.blockDiagonal_mul`, `blockDiagonal_one`, `blockDiagonal_add`,
  `blockDiagonal_smul` and `blockDiagonal_conjTranspose` discharge the homomorphism, unit,
  additivity, real-linearity and ⋆-conditions **one lemma each** — against the previous unit,
  where each had to be proved by hand on a nested product. That is the same species of finding
  as this campaign's other Mathlib imports nobody noticed: the work was in the indexing.

  WHAT IS PROVED.
  * **`HfE`** — the inner-product model, with `finrank_HfE : dim = 4n`.
  * **`fourBlock`**, with `fourBlock_one`, `fourBlock_add`, `fourBlock_mul`, `fourBlock_zero`,
    `fourBlock_real_smul` and **`fourBlock_conjTranspose`** — one Mathlib `blockDiagonal`
    lemma each, against the previous unit where each had to be proved by hand on a nested
    product.
  * **`piRepRing : Matrix (Fin n) (Fin n) ℂ →+* Module.End ℂ (HfE n)`** — a genuine unital
    ring homomorphism, which `KOSixSpectralTriple.piRep` is not (`ERRATUM 565`) and which its
    shape cannot be (`ERRATUM 570`).
  * **`piRepRing_star`** — the ⋆-condition against the inner product, in exactly the shape
    `SpectralTripleBimodule.Triple.star_π` and `StarRepSemisimple`'s theorems ask for.
  * **`piRepRing_injective`**, and **`isSemisimple_via_piRepRing`** applying rung 1 to it. A
    small conclusion — `Mₙ(ℂ)` was never in doubt — but it is the first time
    `StarRepSemisimple`'s theorem has been fed a representation on the KO-6 geometry rather
    than on a synthetic space, and it is the check that the two hypotheses above are in the
    shapes that theorem actually consumes.

  WHAT IS **NOT** CLAIMED, and a `Triple` is still not assembled.
  * **THE BLOCKER HAS MOVED, NOT GONE, AND HERE IS EXACTLY WHERE IT IS NOW.** The inner
    product is no longer the obstacle — that part of `UNLOCK_WATCHLIST` 261's REVISIT line is
    discharged. What blocks a `Triple ℝ ℂ (Mₙ(ℂ)) (HfE n)` is an **instance diamond**:
    `Triple` carries `[Module 𝕂 H] [IsScalarTower 𝕂 𝕜 H]`, and at `𝕂 = ℝ`, `𝕜 = ℂ`,
    `H = EuclideanSpace ℂ ι` the first resolves and **`IsScalarTower ℝ ℂ H` does not** —
    probed, and `Algebra ℝ (Module.End ℂ H)` resolves while the tower does not. The statement
    is TRUE and cheap: the remaining goal after `ext` is `↑x * y * z i = ↑x * (y * z i)`, i.e.
    `mul_assoc`. But supplying it by hand produces an instance that instance search then does
    not use, because `EuclideanSpace ℂ ι` has two `Module ℝ` paths — one through
    `Algebra ℝ ℂ` and one through the norm — and they are not syntactically the same. **So
    this is the `Herm4Gaussian` diamond again in a new place**, and it is named rather than
    fought here.
  * **`piRepRing` is a `RingHom`, not an `ℝ`-`AlgHom`**, for the same reason. `ℝ`-linearity
    IS available one level down, as `fourBlock_real_smul`; lifting it through
    `OrderOneNontrivial.matAlg` needs `map_smul` at an `ℝ` scalar on a `ℂ`-`AlgHom` and hits
    the same diamond. **None of the conclusions above need the algebra packaging**, which is
    why they are stated for a `RingHom` — `StarRepSemisimple`'s theorems take one.
  * **`πOp`, `D`, `J` and `γ` are not built on `HfE n`.** A `Triple` has five fields and this
    unit supplies the material for one of them plus its ⋆-condition. **Neither order condition
    is proved**, so the sentence *"the estate's own triple now instantiates the structure"* is
    false and is not being made.
  * **No equivalence to `Hf n` is proved.** `HfE n` is `EuclideanSpace ℂ (Fin n × Fin 4)` and
    `Hf n` is a nested product; they are abstractly isomorphic and **the isomorphism is not
    constructed**, so nothing in `KOSixSpectralTriple` is transported or superseded. The
    agreement with `piRepC` is at the level of the definition — `a` on blocks 0 and 1, `ā` on
    blocks 2 and 3 — and is stated in this comment rather than as a theorem, deliberately,
    because the theorem needs that isomorphism.
  * **`J` is antilinear** and `Module.End ℂ (HfE n)` cannot hold it; a real structure needs a
    conjugate-linear map, which `SpectralTripleBimodule`'s header records as a weakening and
    which no unit has addressed.
  * **No KO-dimension claim, no grading, no connection to `CascadeHilbert`, `CascadeAlgebra`
    or the 96** — L18's standing residue.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import KOSixRepairedAction
import OrderOneNontrivial
import StarRepSemisimple

namespace KOSixInnerProduct

open Matrix ComplexConjugate KOSixSpectralTriple

noncomputable section

variable (n : ℕ)

/-! ## 1. The inner-product model -/

/-- **The four-block space, re-indexed.** One index set `Fin n × Fin 4` instead of a nested
product of four `Fin n → ℂ`, so `EuclideanSpace` supplies every instance a `Triple` needs. -/
abbrev HfE : Type := EuclideanSpace ℂ (Fin n × Fin 4)

theorem finrank_HfE : Module.finrank ℂ (HfE n) = 4 * n := by
  rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  ring

/-! ## 2. The action, as a block-diagonal matrix -/

variable {n}

/-- `a` on the two particle blocks, the entrywise conjugate `ā` on the two antiparticle
blocks — the previous unit's repair, written as a block-diagonal matrix. -/
def fourBlock (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℂ :=
  Matrix.blockDiagonal fun b => if b.val < 2 then a else mbar a

theorem fourBlock_one : fourBlock (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  have h : (fun b : Fin 4 => if b.val < 2 then (1 : Matrix (Fin n) (Fin n) ℂ)
      else mbar 1) = 1 := by
    funext b
    simp only [Pi.one_apply]
    by_cases hb : b.val < 2
    · rw [if_pos hb]
    · rw [if_neg hb, KOSixRepairedAction.mbar_one]
  rw [fourBlock, h, Matrix.blockDiagonal_one]

theorem fourBlock_add (a c : Matrix (Fin n) (Fin n) ℂ) :
    fourBlock (a + c) = fourBlock a + fourBlock c := by
  rw [fourBlock, fourBlock, fourBlock, ← Matrix.blockDiagonal_add]
  congr 1
  funext b
  simp only [Pi.add_apply]
  by_cases hb : b.val < 2
  · rw [if_pos hb, if_pos hb, if_pos hb]
  · rw [if_neg hb, if_neg hb, if_neg hb, KOSixRepairedAction.mbar_add]

theorem fourBlock_mul (a c : Matrix (Fin n) (Fin n) ℂ) :
    fourBlock (a * c) = fourBlock a * fourBlock c := by
  rw [fourBlock, fourBlock, fourBlock, ← Matrix.blockDiagonal_mul]
  congr 1
  funext b
  by_cases hb : b.val < 2
  · rw [if_pos hb, if_pos hb, if_pos hb]
  · rw [if_neg hb, if_neg hb, if_neg hb, KOSixRepairedAction.mbar_mul]

theorem mbar_real_smul (r : ℝ) (a : Matrix (Fin n) (Fin n) ℂ) :
    mbar (r • a) = r • mbar a := by
  ext i j
  simp only [mbar, Matrix.map_apply, Matrix.smul_apply, Complex.real_smul]
  rw [map_mul, Complex.conj_ofReal]

theorem fourBlock_real_smul (r : ℝ) (a : Matrix (Fin n) (Fin n) ℂ) :
    fourBlock (r • a) = r • fourBlock a := by
  have hf : (fun b : Fin 4 => if b.val < 2 then r • a else mbar (r • a))
      = r • (fun b : Fin 4 => if b.val < 2 then a else mbar a) := by
    funext b
    simp only [Pi.smul_apply]
    by_cases hb : b.val < 2
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb, mbar_real_smul]
  rw [fourBlock, hf, fourBlock]
  exact Matrix.blockDiagonal_smul r _

/-- **The ⋆-condition at matrix level.** The particle blocks give `aᴴ`; the antiparticle
blocks give `(mbar a)ᴴ = aᵀ`, and `mbar (aᴴ) = aᵀ` too — `KOSixSpectralTriple`'s
`mbar_conjTranspose`, one of the four identities that file has. -/
theorem fourBlock_conjTranspose (a : Matrix (Fin n) (Fin n) ℂ) :
    (fourBlock a)ᴴ = fourBlock aᴴ := by
  rw [fourBlock, Matrix.blockDiagonal_conjTranspose, fourBlock]
  congr 1
  funext b
  by_cases hb : b.val < 2
  · rw [if_pos hb, if_pos hb]
  · rw [if_neg hb, if_neg hb, mbar_conjTranspose]
    ext i j
    simp [mbar, Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply]

/-! ## 3. The action as an `ℝ`-algebra map on the inner-product model -/

theorem fourBlock_zero : fourBlock (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  have h : fourBlock (0 : Matrix (Fin n) (Fin n) ℂ) + fourBlock 0 = fourBlock 0 := by
    rw [← fourBlock_add, add_zero]
  exact add_left_cancel (a := fourBlock (0 : Matrix (Fin n) (Fin n) ℂ))
    (by rw [add_zero]; exact h)

/-- **THE ACTION.** `Mₙ(ℂ)` acting on an inner-product model of the four-block space, as a
genuine unital ring homomorphism into `Module.End ℂ (HfE n)` — which `KOSixSpectralTriple.piRep`
is not (`ERRATUM 565`) and which its shape cannot be (`ERRATUM 570`).

**A `RingHom` and not an `ℝ`-`AlgHom`, deliberately** — see the header's third disclaimer: the
`ℝ`-algebra packaging runs into an instance diamond on `EuclideanSpace ℂ ι` that is not worth
fighting for the conclusions below, none of which need it. -/
def piRepRing : Matrix (Fin n) (Fin n) ℂ →+* Module.End ℂ (HfE n) where
  toFun a := OrderOneNontrivial.matAlg (Fin n × Fin 4) (fourBlock a)
  map_one' := by rw [fourBlock_one, map_one]
  map_mul' a c := by rw [fourBlock_mul, map_mul]
  map_zero' := by rw [fourBlock_zero, map_zero]
  map_add' a c := by rw [fourBlock_add, map_add]

@[simp]
theorem piRepRing_apply (a : Matrix (Fin n) (Fin n) ℂ) :
    piRepRing a = OrderOneNontrivial.matAlg (Fin n × Fin 4) (fourBlock a) := rfl

/-- **The ⋆-condition against the inner product**, in exactly the shape
`SpectralTripleBimodule.Triple.star_π` and `StarRepSemisimple`'s theorems ask for. -/
theorem piRepRing_star (a : Matrix (Fin n) (Fin n) ℂ) (u v : HfE n) :
    inner ℂ (piRepRing a u) v = inner ℂ u (piRepRing (star a) v) := by
  rw [piRepRing_apply, piRepRing_apply, Matrix.star_eq_conjTranspose, ← fourBlock_conjTranspose]
  exact OrderOneNontrivial.matAlg_star (Fin n × Fin 4) (fourBlock a) u v

theorem fourBlock_injective : Function.Injective (fourBlock (n := n)) := by
  intro a c h
  ext i j
  have := congrFun (congrFun h (i, 0)) (j, 0)
  simpa [fourBlock, Matrix.blockDiagonal_apply] using this

/-- **Faithful**, so the rung-1 theorem applies to it. -/
theorem piRepRing_injective : Function.Injective (piRepRing (n := n)) := fun a c h =>
  fourBlock_injective (OrderOneNontrivial.matAlg_injective (Fin n × Fin 4) (by
    simpa [piRepRing_apply] using h))

/-- **And rung 1 applies.** A small conclusion — `Mₙ(ℂ)` was never in doubt — but it is the
first time `StarRepSemisimple`'s theorem has been fed a representation on the KO-6 geometry
rather than on a synthetic space, and it is the check that the ⋆-condition and faithfulness
above are in the shapes that theorem actually consumes. -/
theorem isSemisimple_via_piRepRing (n : ℕ) :
    IsSemisimpleRing (Matrix (Fin n) (Fin n) ℂ) :=
  StarRepSemisimple.isSemisimpleRing_of_faithful_star_rep_complex
    (𝕜 := ℂ) (H := HfE n) (piRepRing (n := n)) piRepRing_injective piRepRing_star

end

end KOSixInnerProduct
