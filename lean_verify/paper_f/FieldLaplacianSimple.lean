import FieldSimpleAut

/-!
# The door: a hypothesis about the graph's Laplacian, and the whole chain runs on it

An hour ago `FieldSimpleAut` proved a fact about **graphs** — at a simple spectrum every
automorphism is an involution — and fenced the thing that stopped it being usable: the hypothesis
was about the **propagator's** spectrum, where a reader's graph-theory facts are about the
**Laplacian's**. The item filed for it called this *the door*. **This is the door.**

## What is proved

**`toLin'_massive`** — `massive G m` is the Laplacian plus `m²` times the identity, as a linear
map. **`ker_massive_eq`** — **so the two operators have literally the same eigenspaces**, at
eigenvalues shifted by `m²`: `ker (massive − ν) = ker (lapMatrix − (ν − m²))`. Not isomorphic
subspaces — the same subspace.

**`eigenvalues_injective_of_lapMatrix`** — **THE DOOR.** A hypothesis stated entirely about the
graph's Laplacian — *every eigenspace is at most a line* — delivers
`Function.Injective hH.eigenvalues` for the propagator, which is what the whole symmetry chain runs
on. **No index-matching is done**, and none is needed:
`FieldSimpleCriterion.eigenvalues_injective_of_finrank_le_one` already takes its hypothesis as a
statement about `massive`'s eigenspaces rather than about anybody's enumeration of eigenvalues, so
`ker_massive_eq` is the entire bridge. **That is the second time this chain has gone around the
index-matching instead of through it** — the first was entry 17 of 2026-09-05.

**`card_symmetries_of_lapMatrix`, `signMulEquiv_of_lapMatrix`,
`graphAut_involutive_of_lapMatrix`** — the count `2^|V|`, the group `(ℤ/2)^V` and the involution
theorem, each restated with the graph-only hypothesis. **The last one is now entirely in graph
vocabulary**: *if every eigenspace of the Laplacian is at most a line, every automorphism of the
graph is an involution.*

## What is NOT here

**THE DOOR IS OPEN AND NOTHING HAS BEEN CARRIED THROUGH IT.** **No graph is shown to satisfy the
Laplacian hypothesis** — not even the line. `FieldSimpleCriterion.eigenvalues_injective_line` still
discharges simplicity on the **propagator** side by its own route, and **this file does not
re-derive it through the Laplacian.** So every theorem here is conditional and, as of now, is
conditional on something nothing in the estate supplies. Not attempted, no cost claimed
(`ERRATUM 246`).

**"EVERY EIGENSPACE IS AT MOST A LINE" IS NOT PROVED EQUIVALENT TO "`|V|` DISTINCT EIGENVALUES".**
For a symmetric matrix they are the same condition, because the eigenspaces span; **that argument is
not made here**, so a reader holding the classical statement in the counting form has one more step
to take. It is the mirror of the step this file avoids on the other side.

**NOTHING IS SAID ABOUT WHICH GRAPHS THESE ARE.** The item this file answers asked for a
**characterisation**; this is not one, and opening a door is not walking through it.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `m ≠ 0` is taken by
`eigenvalues_injective_of_lapMatrix`, `card_symmetries_of_lapMatrix`, `signMulEquiv_of_lapMatrix`
and `graphAut_involutive_of_lapMatrix` — **four of the six**. `toLin'_massive` and `ker_massive_eq`
take **no hypothesis on the mass at all**: they are the identity `massive = lapMatrix + m² · 1` read
two ways, and hold at `m = 0`, where they say the massive operator *is* the Laplacian.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldLaplacianSimple

open Matrix GraphLaplacian FieldSimpleCriterion FieldLineCount FieldSignGroup FieldSimpleAut
  MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The massive operator is the Laplacian shifted -/

theorem toLin'_massive (m : ℝ) :
    Matrix.toLin' (massive G m)
      = Matrix.toLin' (G.lapMatrix ℝ) + (m ^ 2) • (LinearMap.id : (V → ℝ) →ₗ[ℝ] (V → ℝ)) := by
  rw [massive, map_add]
  congr 1
  have hd : (Matrix.diagonal (fun _ : V => m ^ 2)) = (m ^ 2) • (1 : Matrix V V ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hd, map_smul, Matrix.toLin'_one]

/-- **SO THE EIGENSPACES ARE THE SAME SUBSPACES**, at shifted eigenvalues. -/
theorem ker_massive_eq (m ν : ℝ) :
    LinearMap.ker (Matrix.toLin' (massive G m) - ν • LinearMap.id)
      = LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - (ν - m ^ 2) • LinearMap.id) := by
  congr 1
  rw [toLin'_massive]
  ext x
  simp only [LinearMap.coe_comp, LinearMap.coe_single, Function.comp_apply, LinearMap.sub_apply,
    LinearMap.add_apply, toLin'_apply, mulVec_single, MulOpposite.op_one, one_smul,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq, Pi.sub_apply, Pi.add_apply, col_apply,
    Pi.smul_apply, smul_eq_mul, sub_smul]
  ring

/-! ## 2. So a simple Laplacian spectrum is a simple propagator spectrum -/

/-- **THE DOOR.** A hypothesis stated entirely about the graph's Laplacian — no mass, no
propagator — delivers the simplicity the symmetry chain runs on. -/
theorem eigenvalues_injective_of_lapMatrix (hm : m ≠ 0) (hH : (green G m).IsHermitian)
    (hdim : ∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) :
    Function.Injective hH.eigenvalues :=
  eigenvalues_injective_of_finrank_le_one hm hH fun ν => by
    rw [ker_massive_eq]
    exact hdim _

/-! ## 3. The chain, restated with a hypothesis about the graph alone -/

/-- **THE COUNT.** -/
theorem card_symmetries_of_lapMatrix (hm : m ≠ 0)
    (hdim : ∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) :
    Nat.card (symmetries G m) = 2 ^ Fintype.card V :=
  card_symmetries hm
    (eigenvalues_injective_of_lapMatrix hm (green_posDef G hm).isHermitian hdim)

/-- **THE GROUP.** -/
noncomputable def signMulEquiv_of_lapMatrix (hm : m ≠ 0)
    (hdim : ∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) :
    Multiplicative (V → ZMod 2) ≃* symmetriesSubgroup G m :=
  signMulEquiv hm (green_posDef G hm).isHermitian
    (eigenvalues_injective_of_lapMatrix hm (green_posDef G hm).isHermitian hdim)

/-- **AND THE INVOLUTION THEOREM, ENTIRELY IN GRAPH VOCABULARY**: if every eigenspace of the
Laplacian is at most a line, every automorphism of the graph is an involution. -/
theorem graphAut_involutive_of_lapMatrix (hm : m ≠ 0)
    (hdim : ∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1)
    {θ : V ≃ V} (hθ : FieldAutInvariance.IsGraphAut G θ) (p : V) : θ (θ p) = p :=
  graphAut_involutive hm (green_posDef G hm).isHermitian
    (eigenvalues_injective_of_lapMatrix hm (green_posDef G hm).isHermitian hdim) hθ p

end FieldLaplacianSimple
