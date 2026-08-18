import CliffordRealSignatures
import CliffordDimension

/-!
# `Cl(1,0;ℝ) ≅ ℝ × ℝ` — a base case on a diagonal the wall said had none

`WALLS §W7.2` and its watchlist items record the real classification's wall as **four residue
classes with no base case at all**: `p − q ≡ 1, 3, 4, 5 (mod 8)`. That statement is **too strong**,
and running `ERRATUM 204`'s check — *ask what this estate already has* — on the wall account itself
is what found it.

> **`equivSplit`** — `Cl(1,0;ℝ) ≃ₐ[ℝ] ℝ × ℝ`. Signature `(1,0)`, so **`p − q = 1`**.

The algebra is `ℝ[e]/(e² − 1)`, the split-complex numbers, and the isomorphism is the
elementary one: `e ↦ (1, −1)`. **This estate has had the construction since
`CliffordOddLadder`**, where `cl1Map` sends a generator to `(v, −v)` to build
`Cl(Rf 1) ≅ ℂ × ℂ` over `ℂ`. Nothing about that map is
complex — it works over any commutative ring — and it was never pointed at `ℝ`.

## What this does to the wall

**Four missing classes become three.** With `Cl(1,0)` on the diagonal, the hyperbolic step
(`periodicityEquivHyp`, which `SignatureArithmetic.sigPos_sub_sigNeg_QextHyp` proves preserves
`p − q`) walks the whole of `p − q ≡ 1`: `Cl(2,1) ≅ M₂(ℝ × ℝ)`, `Cl(3,2)`, and upward.
`clifford_iso_split_of_sig` states it over **every** nondegenerate real form of dimension 1 and
`sigPos 1`, not just the named one.

**The remaining wall is `p − q ≡ 3, 4, 5`.** Those are `Cl(3,0) ≅ M₂(ℂ)`, `Cl(4,0) ≅ M₂(ℍ)` and
`Cl(0,3) ≅ ℍ ⊕ ℍ` in the standard table, and none of the three is a one-generator algebra — each
needs a genuine construction rather than a splitting, which is why this file does not reach them.

## Why the wall account was wrong, stated plainly

The account was written from *"which base cases does Mathlib supply?"* — and Mathlib supplies three
(`ℝ`, `ℂ`, `ℍ`) sitting on `p − q ≡ 0, −1, −2`. The question it never asked is the one `ERRATUM 204`
names: **which base cases can this estate build with what it already has?** One of them was a
seven-line linear map written for a different field three weeks ago. `ERRATUM 211` records it.

**No published tag moves.** The correction is to the *estate's own wall account*, not to a
paper.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordRealSplit

open QuadraticForm QuadraticMap CliffordAlgebra SignatureArithmetic

noncomputable section

/-- signature `(1,0)`: `Q(x) = x²` on the line. -/
abbrev Q₁₀ : QuadraticForm ℝ ℝ := QuadraticMap.sq

/-- The generator goes to `(1, −1)`. Over `ℂ` this is `CliffordOddLadder.cl1Map`; nothing in it
is complex. -/
def splitMap : ℝ →ₗ[ℝ] ℝ × ℝ where
  toFun v := (v, -v)
  map_add' x y := by simp; ring
  map_smul' c x := by simp

@[simp] theorem splitMap_apply (v : ℝ) : splitMap v = (v, -v) := rfl

theorem splitMap_sq (v : ℝ) :
    splitMap v * splitMap v = algebraMap ℝ (ℝ × ℝ) (Q₁₀ v) := by
  simp [QuadraticMap.sq, Prod.algebraMap_apply]

/-- The algebra map out of the Clifford algebra. -/
def toSplit : CliffordAlgebra Q₁₀ →ₐ[ℝ] ℝ × ℝ :=
  CliffordAlgebra.lift Q₁₀ ⟨splitMap, splitMap_sq⟩

@[simp] theorem toSplit_ι (v : ℝ) : toSplit (ι Q₁₀ v) = (v, -v) :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-- **Surjective**, by solving the two-by-two system: `(a,b)` is `(a+b)/2` times the identity plus
`(a−b)/2` times the generator. -/
theorem toSplit_surjective : Function.Surjective toSplit := by
  rintro ⟨a, b⟩
  refine ⟨algebraMap ℝ _ ((a + b) / 2) + ((a - b) / 2) • ι Q₁₀ 1, ?_⟩
  simp [Prod.ext_iff, Prod.algebraMap_apply]
  constructor <;> ring

/-- **`Cl(1,0;ℝ) ≅ ℝ × ℝ`.** Surjectivity plus the dimension formula, which is exactly the shape
`CliffordDimension.cliffordAlgEquivOfSurjective` was written for. -/
def equivSplit : CliffordAlgebra Q₁₀ ≃ₐ[ℝ] ℝ × ℝ := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  exact CliffordDimension.cliffordAlgEquivOfSurjective ℝ ℝ Q₁₀ toSplit toSplit_surjective (by simp)

/-! ## Its signature — the point of the file -/

theorem sigPos_Q₁₀ : sigPos Q₁₀ = 1 := by
  have h : Q₁₀ = (1 : ℝ) • QuadraticMap.sq := by rw [one_smul]
  rw [h, sigPos_smul_sq]; norm_num

theorem sigNeg_Q₁₀ : sigNeg Q₁₀ = 0 := by
  have h : Q₁₀ = (1 : ℝ) • QuadraticMap.sq := by rw [one_smul]
  rw [h, sigNeg_smul_sq]; norm_num

/-- **`p − q = 1`**, the diagonal the wall account said had no base case. Stated as `sigPos = 1` and
`sigNeg = 0` rather than as a difference, for the reason `sigPos_sub_sigNeg_QextHyp` gives. -/
theorem diagonal_one : sigPos Q₁₀ = 1 ∧ sigNeg Q₁₀ = 0 := ⟨sigPos_Q₁₀, sigNeg_Q₁₀⟩

theorem sep_Q₁₀ : (QuadraticMap.associated (R := ℝ) Q₁₀).SeparatingLeft :=
  CliffordRealSignatures.separatingLeft_of_sig (by rw [sigPos_Q₁₀, sigNeg_Q₁₀]; simp)

/-- **Every** nondegenerate real form of dimension 1 with `sigPos = 1` gives the split-complex
numbers. -/
theorem clifford_iso_split_of_sig {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V)
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hdim : Module.finrank ℝ V = 1) (hsig : sigPos Q = 1) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] ℝ × ℝ) := by
  obtain ⟨e⟩ := CliffordRealQuantified.cliffordEquiv_of_sigPos_eq hQ sep_Q₁₀
    (by simp [hdim]) (by rw [hsig, sigPos_Q₁₀])
  exact ⟨e.trans equivSplit⟩

/-! ## Walking the diagonal -/

/-- signature `(2,1)`: `Q₁₀` with a hyperbolic plane adjoined. -/
abbrev Q₂₁ : QuadraticForm ℝ (ℝ × (ℝ × ℝ)) :=
  CliffordPeriodicityHyperbolic.QextHyp Q₁₀

/-- **`Cl(2,1;ℝ) ≅ M₂(ℝ × ℝ)`** — the next rung of the newly opened diagonal, and the witness that
the step really does traverse it. -/
def equivM2Split : CliffordAlgebra Q₂₁ ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) (ℝ × ℝ) := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  exact (CliffordPeriodicityHyperbolic.periodicityEquivHyp Q₁₀).trans
    (AlgEquiv.mapMatrix equivSplit)

theorem sigPos_Q₂₁ : sigPos Q₂₁ = 2 := by rw [Q₂₁, sigPos_QextHyp, sigPos_Q₁₀]
theorem sigNeg_Q₂₁ : sigNeg Q₂₁ = 1 := by rw [Q₂₁, sigNeg_QextHyp, sigNeg_Q₁₀]

end

end CliffordRealSplit
