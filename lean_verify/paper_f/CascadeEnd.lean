/-
  CascadeEnd.lean — `End(M_b(ℂ))` IS `M_b ⊗ M_b`, and IS `M_{b²}`: the cascade's
  defining operation identified with its matrix step, for every `b`, and
  `F1_6`'s constraints C2 and C3 turned from FIELDS into THEOREMS.

  WHY THIS FILE EXISTS — SPINE LINKS L4 AND L11. The cascade is End-iteration:
  `ℂ² → End(ℂ²) = M₂ → End(M₂) = M₄ → End(M₄) = M₁₆`. That sentence is in the
  header of `F4_1a_TensorProductIsomorphism` (link L4, rated GENUINE) and in the
  header of `F1_6_PatiSalamForced` (link L11), and **in neither file does
  `Module.End` of a matrix algebra appear in a single Lean statement.** What is
  proved there is the Kronecker step `M_b ⊗ M_c ≃ₐ M_{bc}`, a true and useful
  theorem about tensor products that says nothing about endomorphisms. Checked
  by query, not recalled: no `AlgEquiv` in `paper_f` or the root has
  `Module.End ℂ (Matrix …)` on either side (`EmergenceTheorem.lean`'s private `E_M16_End` is
  End of the COLUMN `ℂ¹⁶`, a different object). The word *End* in the cascade was
  prose over a Kronecker product.

  **AND THE MISSING THEOREM IS A MATHLIB IMPORT NOBODY NOTICED** — `PROOF_STRATEGY`
  §1's second Caesar source. `F1_6` says its constraint C3 rests on *"the Azumaya
  decomposition `End(D₁) ≅ D₁ ⊗ D₁ᵒᵖ`"* and that Azumaya uniqueness is *"not yet
  in Mathlib"*. Mathlib v4.29.1 has `IsAzumaya.matrix` — every matrix algebra
  over a commutative ring is Azumaya — and `IsAzumaya.AlgHom.mulLeftRight_bij`,
  which is exactly `A ⊗ Aᵐᵒᵖ ≃ₐ End A`, the decomposition C3 names. The estate
  used none of it: `grep -rl IsAzumaya paper_f *.lean` is empty.

  WHAT THIS FILE PROVES, for every `b` (with `b ≠ 0` where Azumaya needs it).

  1. **`azumayaEquiv`** — `M_b(ℂ) ⊗[ℂ] M_b(ℂ)ᵐᵒᵖ ≃ₐ[ℂ] End_ℂ(M_b(ℂ))`, the
     Azumaya decomposition, sending `x ⊗ op y` to `m ↦ x * m * y`
     (`azumayaEquiv_tmul`).
  2. **`endTensorSq`** — `End_ℂ(M_b(ℂ)) ≃ₐ[ℂ] M_b(ℂ) ⊗[ℂ] M_b(ℂ)`: the
     opposite algebra is the transpose (`Matrix.transposeAlgEquiv`), so both
     tensor factors are LITERALLY `M_b`. **This is C3 as a theorem**: the two
     subfactors of the decomposed endomorphism algebra are the same algebra.
  3. **`endMatrixEquiv`** — `End_ℂ(M_b(ℂ)) ≃ₐ[ℂ] M_{b·b}(ℂ)`, through the
     standard basis of `M_b` (`algEquivMatrix (Matrix.stdBasis …)`) and a
     reindex. **This is C2 as a theorem**: End of `M_b` is a matrix algebra of
     size `b²`. At `b = 2`, `endM2` is `End(M₂) ≃ₐ M₄` — the D₁ → D₂ step of the
     cascade, WITH the End in it, for the first time in this estate.
  4. **THE CONVERSES, WHICH ARE THE CONSTRAINTS THEMSELVES.** C2 and C3 in
     `F1_6` are statements about NUMBERS: `a = b²` and `c = b`. Those follow from
     ANY identification, not only the ones built here: `size_eq_of_end_equiv` —
     if `End(M_b) ≃ₐ M_a` then `a = b²`; `factor_eq_of_end_equiv_tensor` — if
     `End(M_b) ≃ₐ M_b ⊗ M_c` then `c = b`. Both by `finrank`, which an algebra
     equivalence preserves. **`cascadeConstraints_of_end`** then assembles
     `CascadeConstraints a b c` (from `F1_6_PatiSalamForced`) from the two
     identifications plus the two constraints this file does NOT derive (C1, C4), and
     `cascadeConstraints_four_two_two` instantiates it at `b = 2` with the
     identifications supplied by §2–§3, so `F1_6_PatiSalamForced`'s `cascade_unique_solution`
     has its hypothesis REACHED rather than assumed at `(4, 2, 2)`.

  WHAT THIS DOES NOT DO, AND THE LINK'S RATING TURNS ON IT (as of 2026-09-14).
  **C1 and C4 stay hypotheses.** C1 (`a·b·c = 16`) reads the three gauge-factor sizes as
  multiplying to the fermion column's dimension, and C4 (`2 ≤ b`) is the seed;
  neither is a fact about `End`, and this file takes both as `F1_6` does. **And
  the identification of the gauge factors `SU(a)×SU(b)×SU(c)` with the tensor
  factors of `End(M_b)` is the physics reading** — `F1_6` Part 5's assembly —
  which no theorem here touches. What moved is exactly this: two of the four
  constraints were posited and are now proved; the remaining two and the
  reading are where L11's PARTIAL lives. **`F1_6` is not withdrawn**: its
  arithmetic core `cascade_unique_solution` is unchanged and is what §4 feeds;
  its `constraint_C3_justified`, which proves `finrank M₂ = finrank M₂` by
  `rfl`, is annotated in place (`ERRATUM 94`) and not edited. **No agreement is
  asserted, as of 2026-09-14, between the two routes from `End(M₂)` to `M₄`** — `endMatrixEquiv 2`
  and `endTensorSq 2` composed with `F4_1a_TensorProductIsomorphism`'s `cascadeD1toD2` —
  because a comparison between two isomorphisms is a theorem (`ERRATUM 548`) and it is not proved.
  **SUPERSEDED THE SAME DAY, and the sentence above is kept as written (`ERRATUM 94`):**
  `SkolemNoether.endMatrixEquiv_routes_agree` proves the comparison for every `b`, and
  `endM2_routes_agree` is this line's case. It is *up to conjugation by a single unit* —
  the two routes choose different bases, so equality is false and conjugacy is the
  strongest true statement — and it rests on `SkolemNoether.skolemNoether`, gap N5,
  which was not in the estate when the line above was written.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import F4_1a_TensorProductIsomorphism
import F1_6_PatiSalamForced
import Mathlib.Algebra.Azumaya.Matrix
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace CascadeEnd

open scoped TensorProduct
open Matrix MulOpposite

noncomputable section

/-- `M_b(ℂ)`, abbreviated so the statements below read as the cascade reads. -/
abbrev Mb (b : ℕ) := Matrix (Fin b) (Fin b) ℂ

/-! ## 1. The Azumaya decomposition — a Mathlib import -/

/-- **`M_b ⊗ M_bᵐᵒᵖ ≃ₐ End(M_b)`**, the decomposition `F1_6` names as the source
of its constraint C3. `IsAzumaya.matrix` is the Mathlib theorem; the estate had
never imported it. `b ≠ 0` because an empty matrix ring is not Azumaya. -/
def azumayaEquiv (b : ℕ) [NeZero b] :
    Mb b ⊗[ℂ] (Mb b)ᵐᵒᵖ ≃ₐ[ℂ] Module.End ℂ (Mb b) :=
  haveI : Nonempty (Fin b) := ⟨0⟩
  haveI : IsAzumaya ℂ (Mb b) := IsAzumaya.matrix ℂ (Fin b)
  AlgEquiv.ofBijective (AlgHom.mulLeftRight ℂ (Mb b))
    (IsAzumaya.AlgHom.mulLeftRight_bij ℂ (Mb b))

/-- The decomposition sends `x ⊗ op y` to left-times-`x`, right-times-`y`. -/
theorem azumayaEquiv_tmul (b : ℕ) [NeZero b] (x y m : Mb b) :
    azumayaEquiv b (x ⊗ₜ[ℂ] op y) m = x * m * y := by
  simp [azumayaEquiv, AlgHom.mulLeftRight_apply]

/-! ## 2. Both tensor factors are `M_b` — C3 as a theorem -/

/-- **`End(M_b) ≃ₐ M_b ⊗ M_b`.** The opposite of a matrix algebra over a
commutative ring is the matrix algebra itself, by transpose. -/
def endTensorSq (b : ℕ) [NeZero b] :
    Module.End ℂ (Mb b) ≃ₐ[ℂ] Mb b ⊗[ℂ] Mb b :=
  (azumayaEquiv b).symm.trans
    (Algebra.TensorProduct.congr AlgEquiv.refl
      (transposeAlgEquiv (R := ℂ) (m := Fin b) (α := ℂ)).symm)

/-! ## 3. `End(M_b)` is a matrix algebra of size `b²` — C2 as a theorem -/

/-- **`End(M_b) ≃ₐ M_{b·b}`**, through the standard basis of `M_b` and the
reindexing `Fin b × Fin b ≃ Fin (b·b)`. No Azumaya here: this is the
finite-free-module identification of endomorphisms with matrices. -/
def endMatrixEquiv (b : ℕ) :
    Module.End ℂ (Mb b) ≃ₐ[ℂ] Matrix (Fin (b * b)) (Fin (b * b)) ℂ :=
  (algEquivMatrix (Matrix.stdBasis ℂ (Fin b) (Fin b))).trans
    (reindexAlgEquiv ℂ ℂ finProdFinEquiv)

/-- **The D₁ → D₂ step of the cascade, with the `End` in it**: `End(M₂) ≃ₐ M₄`. -/
def endM2 : Module.End ℂ (Mb 2) ≃ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ :=
  endMatrixEquiv 2

/-- **The D₂ → D₃ step**: `End(M₄) ≃ₐ M₁₆`. -/
def endM4 : Module.End ℂ (Mb 4) ≃ₐ[ℂ] Matrix (Fin 16) (Fin 16) ℂ :=
  endMatrixEquiv 4

/-! ## 4. The constraints as consequences of ANY identification -/

theorem finrank_Mb (b : ℕ) : Module.finrank ℂ (Mb b) = b * b := by
  simp [Mb, Module.finrank_matrix]

theorem finrank_end_Mb (b : ℕ) :
    Module.finrank ℂ (Module.End ℂ (Mb b)) = (b * b) * (b * b) := by
  rw [Module.finrank_linearMap, finrank_Mb]

theorem finrank_Mb_tensor (b c : ℕ) :
    Module.finrank ℂ (Mb b ⊗[ℂ] Mb c) = (b * b) * (c * c) := by
  rw [Module.finrank_tensorProduct, finrank_Mb, finrank_Mb]

/-- **C2, FROM ANY IDENTIFICATION.** If `End(M_b)` is presented as a matrix
algebra of size `a`, then `a = b²`. -/
theorem size_eq_of_end_equiv {a b : ℕ}
    (e : Module.End ℂ (Mb b) ≃ₐ[ℂ] Matrix (Fin a) (Fin a) ℂ) : a = b * b := by
  have h := e.toLinearEquiv.finrank_eq
  rw [finrank_end_Mb] at h
  have ha : Module.finrank ℂ (Matrix (Fin a) (Fin a) ℂ) = a * a := by
    simp [Module.finrank_matrix]
  rw [ha] at h
  exact Nat.mul_self_inj.mp h.symm

/-- **C3, FROM ANY IDENTIFICATION.** If `End(M_b)` is presented as `M_b ⊗ M_c`,
then `c = b`: the two factors have the same size. -/
theorem factor_eq_of_end_equiv_tensor {b c : ℕ} [NeZero b]
    (e : Module.End ℂ (Mb b) ≃ₐ[ℂ] Mb b ⊗[ℂ] Mb c) : c = b := by
  have h := e.toLinearEquiv.finrank_eq
  rw [finrank_end_Mb, finrank_Mb_tensor] at h
  have hb : 0 < b * b := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne b))
    (Nat.pos_of_ne_zero (NeZero.ne b))
  have h2 : c * c = b * b := (Nat.eq_of_mul_eq_mul_left hb h).symm
  exact Nat.mul_self_inj.mp h2

/-- **`F1_6`'s constraint system, with C2 and C3 DERIVED.** C1 and C4 are taken
as hypotheses, exactly as `F1_6` takes them; the other two come from the
identifications. -/
theorem cascadeConstraints_of_end {a b c : ℕ} [NeZero b]
    (hab : Module.End ℂ (Mb b) ≃ₐ[ℂ] Matrix (Fin a) (Fin a) ℂ)
    (hbc : Module.End ℂ (Mb b) ≃ₐ[ℂ] Mb b ⊗[ℂ] Mb c)
    (hprod : a * b * c = 16) (hnt : 2 ≤ b) :
    CascadeConstraints a b c :=
  { product := hprod
    squared := by rw [size_eq_of_end_equiv hab, sq]
    symmetric := (factor_eq_of_end_equiv_tensor hbc).symm
    nontrivial := hnt }

/-- **At `b = 2` the identifications are supplied by §2 and §3**, so
`CascadeConstraints 4 2 2` follows from C1 and C4 alone — and then
`cascade_unique_solution` gives `(4, 2, 2)` from a hypothesis this file
REACHES instead of assuming. -/
theorem cascadeConstraints_four_two_two :
    CascadeConstraints 4 2 2 :=
  cascadeConstraints_of_end (b := 2) endM2 (endTensorSq 2) (by norm_num) (le_refl 2)

/-- And the uniqueness, routed through the derived constraints rather than
through `F1_6_PatiSalamForced`'s `cascade_solution_exists`, which posits them. -/
theorem four_two_two_unique :
    ∀ a c : ℕ, (Module.End ℂ (Mb 2) ≃ₐ[ℂ] Matrix (Fin a) (Fin a) ℂ) →
      (Module.End ℂ (Mb 2) ≃ₐ[ℂ] Mb 2 ⊗[ℂ] Mb c) →
      a * 2 * c = 16 → a = 4 ∧ c = 2 := by
  intro a c hab hbc hprod
  have h := cascade_unique_solution a 2 c
    (cascadeConstraints_of_end hab hbc hprod (le_refl 2))
  exact ⟨h.1, h.2.2⟩

/-! ## 5. Review round 73 — the ways this could be hollow

**"§1 is one Mathlib lemma."** It is, and that is the finding, not a weakness:
`PROOF_STRATEGY` §1 names *a Mathlib import nobody noticed* as the cheapest
conquest there is, and `F1_6` had written *"not yet in Mathlib"* over a theorem
that is. What the file adds around it is the identification of the factors
(§2), the matrix presentation (§3), and the converses (§4), none of which is a
one-liner in the estate.

**"§4's converses are dimension counting."** Yes. C2 and C3 are equations
between natural numbers, and an equation between natural numbers that follows
from an algebra isomorphism follows through an invariant; `finrank` is the
invariant. The point is not the depth of the argument but its DIRECTION: `F1_6`
stated `a = b²` and `b = c` as fields to be assumed, and the estate now proves
them from any identification whatever. `size_eq_of_end_equiv` does not know
which iso it is handed.

**"The cascade step existed already, in `F4_1a`."** The Kronecker step
`M_b ⊗ M_c ≃ M_{bc}` existed. The END step did not: `grep 'Module.End ℂ (Matrix'
paper_f/*.lean` returns hypotheses in `F2_3` and one `→ₐ` (left
multiplication), and no equivalence. `F4_1a`'s header says *"End(M₂(ℂ)) ≅
M₂ ⊗ M₂ ≅ M₄"* and its Lean proves the second `≅`; this file proves the first,
and §3 proves the composite directly.

**"So L4 and L11 are now GENUINE."** No. L4's headline is End-iteration and
now has the End in it, which is a sharpening the recompute will weigh; the
cascade's DEPTH is a postulate (`DECISIONS NEEDED`). L11's headline is that the
decomposition FORCES `(4,2,2)`, and two of its four constraints plus the
reading of gauge factors as tensor factors are untouched here — the header
says which. **What this file claims is that two posits became theorems and
that a word in two headers now has a statement behind it.**

**"The two routes to `M₄` should agree."** They may; it is not proved, and
saying so without proof is exactly what `ERRATUM 548` was.
**They do, up to conjugation, and it is now proved** — `SkolemNoether.endM2_routes_agree`,
the same day, off Skolem–Noether. The paragraph is kept as written: the discipline it
states is right, and what changed is that somebody did the proof.
-/

end

end CascadeEnd
