import FieldRotationCount

/-!
# The symmetries form a GROUP, and each one preserves every eigenspace of the propagator

`FieldRotationCount` counted `symmetryMatrices G m` and fenced two things off: that the set is
closed under multiplication (*"true and easy, and still not proved, so not claimed"*) and that
nothing describes which matrices are in it. **This proves the first and takes the forward half of
the second.** `PROOF_STRATEGY` §7 rule 2 — *finish every part of the scope* — applied to a fence
that admitted in its own sentence that it was cheap.

## What is proved

**`one_mem`, `mul_mem`, `mul_transpose_self`, `transpose_mem`** — the identity is a symmetry, a
product of symmetries is one, an orthogonal matrix's transpose is its two-sided inverse, and the
transpose of a symmetry is a symmetry. Together: **the symmetries are a group under matrix
multiplication, with inverse the transpose.**

**`symmetrySubmonoid`** — that group law bundled as far as the ambient type allows: `Matrix V V ℝ`
is a monoid, so the bundled object is a `Submonoid`, and `transpose_mem` with
`mul_transpose_self` supply the inverses on top of it.

**`infinite_symmetrySubmonoid_box`** — so on `boxGraph d (n+1)` at every `2 ≤ d`, side length `≥ 2`
and `mass ≠ 0`, the Gaussian field's symmetries are an **infinite group**, not merely an infinite
set. That is the sharpening the previous unit's headline was one lemma short of.

**`mulVec_mem_eigenspace`** — **every symmetry maps each eigenspace of `green` into itself**: if
`green *ᵥ x = μ • x` then `green *ᵥ (R *ᵥ x) = μ • (R *ᵥ x)`. This is the direction of the
commutant description that is short, and it is the useful direction for a reader who has a symmetry
and wants to know what it does.

**`mulVec_ne_zero`** — and it does not collapse the eigenspace: an orthogonal matrix is injective,
so a non-zero eigenvector maps to a non-zero eigenvector.

## What is NOT here

**NOT the commutant.** The converse — *an orthogonal matrix preserving every eigenspace commutes
with `green`* — is **not proved**, and it is the half that needs the eigenspaces assembled into a
decomposition of the whole space, which this estate has never done: it has used `green`'s
eigenvalues one at a time throughout. **Not attempted, no cost claimed** (`ERRATUM 246`), and
saying which half is short is not a claim that the other half is (`ERRATUM 194`).

**No bundled `Subgroup`.** `Matrix V V ℝ` is a monoid, not a group, so `Submonoid` is what bundles
here; carrying the symmetries into `Matrix.GeneralLinearGroup` and building a `Subgroup` there is
not done. The group law is nonetheless **completely proved** as the four lemmas above — the gap is
packaging, and it is named rather than left for a reader to notice.

**No cardinality**, only `Set.Infinite`, exactly as in the previous unit.

**Nothing about the torus at `d > 1`.**
⚠ **SUPERSEDED 2026-09-05, kept as written** (`ERRATUM 94`, `ERRATUM 458`):
`FieldTorusRotation.exists_rotation_symmetry_torus` puts a rotation on the torus in **every**
dimension `d ≥ 1`, and needed no orbit bookkeeping at all —
`TorusEigenspaceLowerBound.two_pow_mul_multinomial_le_finrank`, in the estate since 2026-08-31,
bounds the degeneracy below with **no hypotheses**, and the all-ones frequency has every axis
interior. **The route this sentence names was never necessary.**

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. An
infinite symmetry **group** in finite volume is still a wider shadow of an axiom and not a smaller
gap in it, and the word *group* does not change that by one comma.

**THE MASS HYPOTHESIS IS PART OF THE BOX CLAIM ONLY, AND SAYING OTHERWISE WOULD BE `ERRATUM 455`
BACKWARDS.** The first draft of this paragraph said the hypothesis was part of *every* claim below.
It is not: `one_mem`, `mul_mem`, `mul_transpose_self`, `transpose_mem`, `mulVec_mem_eigenspace` and
`mulVec_ne_zero` hold **at every `m`**, `m = 0` included, where `green G 0 = 0`
(`FieldMassNecessity.green_zero`) and the statement degenerates to *the orthogonal group is a
group*. Only `infinite_symmetrySubmonoid_box` needs `mass ≠ 0`, and it needs it because at
`mass = 0` the field is a point mass whose symmetries are the whole orthogonal group — infinite for
no interesting reason. **`ERRATUM 455` was about dropping a hypothesis a theorem has; this is the
mirror, asserting one it does not, and it is the same failure to read the summary against the
binders.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldSymmetryGroup

open Matrix GraphLaplacian FieldRotationCount BoxGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The group law -/

theorem one_mem : (1 : Matrix V V ℝ) ∈ symmetryMatrices G m := by
  refine ⟨by simp, by simp⟩

theorem mul_mem {R S : Matrix V V ℝ} (hR : R ∈ symmetryMatrices G m)
    (hS : S ∈ symmetryMatrices G m) : R * S ∈ symmetryMatrices G m := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᵀ, hR.1, Matrix.one_mul, hS.1]
  · rw [Matrix.mul_assoc, hS.2, ← Matrix.mul_assoc, hR.2, Matrix.mul_assoc]

/-- **THE TRANSPOSE IS A TWO-SIDED INVERSE**, by `mul_eq_one_comm` on the finite square matrix. -/
theorem mul_transpose_self {R : Matrix V V ℝ} (hR : R ∈ symmetryMatrices G m) : R * Rᵀ = 1 :=
  mul_eq_one_comm.mp hR.1

theorem transpose_mem {R : Matrix V V ℝ} (hR : R ∈ symmetryMatrices G m) :
    Rᵀ ∈ symmetryMatrices G m := by
  have hRRt : R * Rᵀ = 1 := mul_transpose_self hR
  refine ⟨by rw [Matrix.transpose_transpose]; exact hRRt, ?_⟩
  have key : Rᵀ * (R * green G m) * Rᵀ = Rᵀ * (green G m * R) * Rᵀ := by rw [hR.2]
  rw [← Matrix.mul_assoc Rᵀ R, hR.1, Matrix.one_mul, ← Matrix.mul_assoc Rᵀ (green G m) R,
    Matrix.mul_assoc (Rᵀ * green G m) R Rᵀ, hRRt, Matrix.mul_one] at key
  exact key.symm

/-- The group law, bundled as far as `Matrix V V ℝ` allows: it is a monoid, so this is a
`Submonoid`, and `transpose_mem` supplies the inverses on top of it. -/
def symmetrySubmonoid (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) :
    Submonoid (Matrix V V ℝ) where
  carrier := symmetryMatrices G m
  mul_mem' := mul_mem
  one_mem' := one_mem

@[simp] theorem mem_symmetrySubmonoid {R : Matrix V V ℝ} :
    R ∈ symmetrySubmonoid G m ↔ R ∈ symmetryMatrices G m := Iff.rfl

/-- **AN INFINITE GROUP OF SYMMETRIES ON THE BOX**, at every `2 ≤ d`, side length `≥ 2` and
`mass ≠ 0` — the physical `d = 4` included. -/
theorem infinite_symmetrySubmonoid_box {d n : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n) {mass : ℝ}
    (hmass : mass ≠ 0) :
    (symmetrySubmonoid (boxGraph d (n + 1)) mass :
      Set (Matrix (Site d (n + 1)) (Site d (n + 1)) ℝ)).Infinite :=
  infinite_symmetryMatrices_box hd hn hmass

/-! ## 2. Every symmetry preserves every eigenspace -/

/-- **A SYMMETRY MAPS EACH EIGENSPACE OF THE PROPAGATOR INTO ITSELF.** -/
theorem mulVec_mem_eigenspace {R : Matrix V V ℝ} (hR : R ∈ symmetryMatrices G m) {x : V → ℝ}
    {μ : ℝ} (hx : green G m *ᵥ x = μ • x) :
    green G m *ᵥ (R *ᵥ x) = μ • (R *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, ← hR.2, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]

/-- **AND IT DOES NOT COLLAPSE IT**: an orthogonal matrix is injective on vectors. -/
theorem mulVec_ne_zero {R : Matrix V V ℝ} (hR : R ∈ symmetryMatrices G m) {x : V → ℝ}
    (hx : x ≠ 0) : R *ᵥ x ≠ 0 := by
  intro hzero
  refine hx ?_
  have := congrArg (fun y : V → ℝ => Rᵀ *ᵥ y) hzero
  simpa [Matrix.mulVec_mulVec, hR.1] using this

end FieldSymmetryGroup
