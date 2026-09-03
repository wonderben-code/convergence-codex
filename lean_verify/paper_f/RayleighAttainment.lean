import GreenLoewnerFloorSharp

/-!
# A symmetric matrix's quadratic form attains its bound exactly at an eigenvector

`TorusAttainmentBridge` joins two characterisations of *the degree bound is reached* on the periodic
lattice — one by a supplied vector, one by an eigenvalue — and its *What this is NOT* section names
the general theorem it had to work around:

> *"**THIS IS NOT THE RAYLEIGH STATEMENT.** A symmetric matrix's quadratic form attains its upper
> bound exactly when that bound is an eigenvalue is a general theorem about symmetric matrices.
> **It is not proved here and it is not used here.**"*

That file's biconditional is a **one-family** result, available only because both sides happened to
reduce to the same third condition (`Even n`). **The general statement is proved here**, and it
needs no spectral theorem, no eigenbasis and no positivity:

> **`quadForm_eq_opNorm_iff_mulVec`** — for a symmetric real matrix `A` and **any** vector `v`,
> `v ⬝ᵥ A *ᵥ v = ‖A‖ · (v ⬝ᵥ v)` **iff** `A *ᵥ v = ‖A‖ • v`.

## The proof is one observation

`OpNormLoewnerConverse.le_smul_one_of_opNorm_le` at `r = ‖A‖` gives `A ≼ ‖A‖ • 1` for **any**
symmetric `A` — that direction carries no positivity hypothesis and no `Nonempty V`. So
`P = ‖A‖ • 1 − A` is positive semidefinite, and `Matrix.PosSemidef.dotProduct_mulVec_zero_iff` says
a positive semidefinite matrix's form vanishes at `v` exactly when it **annihilates** `v`. The
quadratic form of `P` at `v` is `‖A‖·(v ⬝ᵥ v) − v ⬝ᵥ A *ᵥ v`, so *attaining the bound* and
*being an eigenvector at `‖A‖`* are the same equation read twice.

**This is the same shape as `LaplacianSharpEquality`'s own headline** — *the inequality was an
identity all along, and equality forces every summand to vanish* — with the sum of squares replaced
by a positive semidefinite form. That file needed the graph; this needs nothing.

## What it is and is not

* **It is stated at `‖A‖`, not at an arbitrary upper bound.** For `r` with `A ≼ r • 1` and `r > ‖A‖`
  the form is never attained, which is `LaplacianNormSharp.opNorm_eq_iff_min_smul_one` and not this.
  **⚠ BOTH HALVES OF THAT BULLET ARE WRONG AND IT IS KEPT AS WRITTEN** (`ERRATUM 94`, the same day).
  §1's proof uses `A ≼ ‖A‖ • 1` and **nothing else about `‖A‖`**, so the theorem holds at *any*
  ceiling: **`quadForm_eq_iff_mulVec_of_le`**, which now leads §1 with the norm version as its
  corollary. **Symmetry comes off too** — `Matrix.le_iff` makes `r • 1 − A` positive semidefinite,
  which carries the Hermitian property. And the second sentence is false: at `A = (−10) • 1` and
  `r = 0` the form IS attained with `r > ‖A‖`, which is why `opNorm_eq_of_quadForm_eq` in §4 needs
  `0 ≼ A`. `PROOF_STRATEGY` §7 rule 3, applied to a theorem an hour old, and the hypotheses removed
  are **the norm and the symmetry**.
* **It says nothing about existence.** Whether some `v ≠ 0` attains the bound is exactly whether
  `‖A‖` is an eigenvalue, and this file supplies the equivalence, not the eigenvector.
  `RayleighMatrix.mv_eigenvectorBasis` is the estate's route to existence and is untouched here.
* **`TorusAttainmentBridge` is not superseded and nothing there is edited.** Its biconditional is
  between the quadratic-form condition and `4d + m²` being an eigenvalue **of a specific family**,
  and it is proved through `Even n` rather than through this; that route also yields
  `quadForm_attained_iff_isGreatest`, which this file does not. What changes is that the general
  statement its header calls absent is no longer absent.
* **No wall moves.** `W1` asks for a lower bound on the cross form (`WALLS.md` §W1.5).

## §3 — and the eigenvalue currency, for every connected regular graph

`LaplacianLoewnerConverse.eigenvalues_massive_lt_of_not_colorable` already had one direction: on a
connected regular graph that is **not** two-colourable, every eigenvalue of `massive` is strictly
below `2Δ + m²`. The converse — *two-colourable, therefore `2Δ` really is an eigenvalue* — was
available only on the periodic lattice (`TorusSpectrumExtremes.mem_spectrum_top_iff_even`, by parity
of cosines). §1 supplies it in general, because
`LaplacianSharpEquality.exists_quadForm_eq_of_colorable` produces a vector attaining the bound and
`LaplacianNormSharp.norm_lapMatrix_eq_iff_colorable` says that bound **is** `‖L‖` there:

> **`exists_eigenvector_top_iff_colorable`** — on a connected `Δ`-regular graph, `2Δ` is an
> eigenvalue of `G.lapMatrix ℝ` **iff** `G.Colorable 2`;
> **`exists_eigenvector_massive_iff_colorable`** is the same at `massive` and `2Δ + m²`.

**§4 THEN TAKES CONNECTIVITY OFF THE HALF THAT NEVER NEEDED IT.**
**`exists_eigenvector_top_iff_exists_quadForm_eq`**: on **any** `Δ`-regular graph, *some vector
attains the degree bound* and *`2Δ` is an eigenvalue* are the same statement — no connectivity, no
`Nonempty V`, no norm. §3's route through `LaplacianNormSharp` needed both, and §3's proof no longer
uses it.

**The easy direction is easy and the hard one is §1**: an eigenvector attains the form by one line,
and attaining forces an eigenvector only because the bound is the norm.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RayleighAttainment

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **ATTAINING *ANY* LOEWNER CEILING FORCES AN EIGENVECTOR AT IT.** §1 was stated at `r = ‖A‖` and
asked for symmetry; **neither is needed**. The proof of §1 uses `A ≼ ‖A‖ • 1` and nothing else about
`‖A‖`, and `Matrix.le_iff` makes `r • 1 − A` positive semidefinite, which carries the Hermitian
property with it. So the hypothesis is exactly *a ceiling*, and the conclusion is *an eigenvector at
that ceiling*.

**THIS IS THE FORM THE ESTATE'S CONSUMERS ARE IN**: `LaplacianSharpEquality` and
`LaplacianLoewnerConverse` attain at the **specific** constant `2Δ + m²`, not at a norm, and
`LaplacianDegreeBound.massive_le_smul_one` is exactly the ceiling. §3 went through
`LaplacianNormSharp` to identify that constant with `‖L‖` first; with this it does not have to.
`PROOF_STRATEGY` §7 rule 3, applied to a theorem an hour old. -/
theorem quadForm_eq_iff_mulVec_of_le {A : Matrix V V ℝ} {r : ℝ}
    (hr : A ≤ r • (1 : Matrix V V ℝ)) (v : V → ℝ) :
    v ⬝ᵥ A *ᵥ v = r * (v ⬝ᵥ v) ↔ A *ᵥ v = r • v := by
  have hps : (r • (1 : Matrix V V ℝ) - A).PosSemidef := Matrix.le_iff.mp hr
  have hquad : v ⬝ᵥ (r • (1 : Matrix V V ℝ) - A) *ᵥ v = r * (v ⬝ᵥ v) - v ⬝ᵥ A *ᵥ v := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul]
  have hzero := hps.dotProduct_mulVec_zero_iff v
  rw [star_trivial, hquad] at hzero
  constructor
  · intro h
    have h0 : (r • (1 : Matrix V V ℝ) - A) *ᵥ v = 0 := hzero.mp (by rw [h]; ring)
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    exact h0.symm
  · intro h
    have h0 : (r • (1 : Matrix V V ℝ) - A) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h, sub_self]
    have := hzero.mpr h0
    linarith

/-- **ATTAINING THE OPERATOR-NORM BOUND IS BEING AN EIGENVECTOR AT IT.** For a symmetric real
matrix and any vector, `v ⬝ᵥ A *ᵥ v = ‖A‖ · (v ⬝ᵥ v)` **iff** `A *ᵥ v = ‖A‖ • v`. **No positivity,
no `Nonempty V`, no spectral theorem and no eigenbasis** — `‖A‖ • 1 − A` is positive semidefinite
because `‖A‖ ≤ ‖A‖`, and a positive semidefinite form vanishes exactly where its matrix annihilates.
-/
theorem quadForm_eq_opNorm_iff_mulVec {A : Matrix V V ℝ} (hT : Aᵀ = A) (v : V → ℝ) :
    v ⬝ᵥ A *ᵥ v = ‖A‖ * (v ⬝ᵥ v) ↔ A *ᵥ v = ‖A‖ • v :=
  quadForm_eq_iff_mulVec_of_le (OpNormLoewnerConverse.le_smul_one_of_opNorm_le hT le_rfl) v

/-- **HENCE THE EXISTENCE FORMS AGREE**: some non-zero vector attains the bound **iff** `‖A‖` is an
eigenvalue. This is the statement `TorusAttainmentBridge` had to reach through `Even n` for one
family. -/
theorem exists_quadForm_eq_opNorm_iff {A : Matrix V V ℝ} (hT : Aᵀ = A) :
    (∃ v : V → ℝ, v ≠ 0 ∧ v ⬝ᵥ A *ᵥ v = ‖A‖ * (v ⬝ᵥ v))
      ↔ ∃ v : V → ℝ, v ≠ 0 ∧ A *ᵥ v = ‖A‖ • v := by
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, (quadForm_eq_opNorm_iff_mulVec hT v).mp h⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, (quadForm_eq_opNorm_iff_mulVec hT v).mpr h⟩

/-- **AND THE PROPAGATOR'S CASE IS THE CONSTANT FIELD**, which `GreenNormExact` computed directly:
`‖green G m‖ = (m²)⁻¹` and the all-ones vector is an eigenvector there, so the bound is attained at
every finite graph. Read here through the general statement rather than through the norm. -/
theorem quadForm_green_eq_opNorm [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℝ}
    (hm : m ≠ 0) :
    (fun _ : V => (1 : ℝ)) ⬝ᵥ GraphLaplacian.green G m *ᵥ (fun _ : V => (1 : ℝ))
      = ‖GraphLaplacian.green G m‖ * ((fun _ : V => (1 : ℝ)) ⬝ᵥ (fun _ : V => (1 : ℝ))) := by
  have hT : (GraphLaplacian.green G m)ᵀ = GraphLaplacian.green G m :=
    GraphLaplacian.green_isSymm G hm
  refine (quadForm_eq_opNorm_iff_mulVec hT _).mpr ?_
  rw [GreenNormExact.norm_green_eq G hm, GreenExpansion.green_mulVec_one (G := G) hm]
  ext p; simp

/-! ## 3. The eigenvalue currency, for every connected regular graph -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **`2Δ` IS AN EIGENVALUE OF THE LAPLACIAN IFF THE GRAPH IS TWO-COLOURABLE**, on a connected
`Δ`-regular graph. `LaplacianLoewnerConverse` had *not colourable ⇒ every eigenvalue strictly
below*; the converse existed only on the periodic lattice, by parity of cosines. -/
theorem exists_eigenvector_top_iff_colorable [Nonempty V] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hG : G.Connected) :
    (∃ v : V → ℝ, v ≠ 0 ∧ (G.lapMatrix ℝ) *ᵥ v = (2 * (Δ : ℝ)) • v) ↔ G.Colorable 2 := by
  have hT : (G.lapMatrix ℝ)ᵀ = G.lapMatrix ℝ := G.isSymm_lapMatrix (R := ℝ)
  constructor
  · rintro ⟨v, hv, hev⟩
    refine (LaplacianSharpEquality.exists_quadForm_eq_iff_colorable G hreg hG).mp ⟨v, hv, ?_⟩
    rw [hev, dotProduct_smul, smul_eq_mul]
  · intro hcol
    obtain ⟨x, hx, hq⟩ := LaplacianSharpEquality.exists_quadForm_eq_of_colorable G hreg hcol
    have hdeg : ∀ p : V, (G.degree p : ℝ) ≤ (Δ : ℝ) := fun p => by rw [hreg p]
    exact ⟨x, hx,
      (quadForm_eq_iff_mulVec_of_le (LaplacianDegreeBound.lapMatrix_le_smul_one G hdeg) x).mp hq⟩

/-- **THE SAME AT `massive`**: `2Δ + m²` is an eigenvalue of `massive G m` iff `G.Colorable 2`.
`massive` is `lapMatrix` plus `m²` on the diagonal, so the eigenvectors are the same and the
eigenvalues shift. -/
theorem exists_eigenvector_massive_iff_colorable [Nonempty V] {Δ : ℕ}
    (hreg : G.IsRegularOfDegree Δ) (hG : G.Connected) (m : ℝ) :
    (∃ v : V → ℝ, v ≠ 0 ∧ GraphLaplacian.massive G m *ᵥ v = (2 * (Δ : ℝ) + m ^ 2) • v)
      ↔ G.Colorable 2 := by
  rw [← exists_eigenvector_top_iff_colorable G hreg hG]
  have hshift : ∀ v : V → ℝ, GraphLaplacian.massive G m *ᵥ v
      = (G.lapMatrix ℝ) *ᵥ v + (m ^ 2) • v := by
    intro v
    rw [GraphLaplacian.massive, Matrix.add_mulVec]
    congr 1
    ext p
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal, mul_comm]
  constructor
  · rintro ⟨v, hv, hev⟩
    refine ⟨v, hv, ?_⟩
    rw [hshift v] at hev
    have : (G.lapMatrix ℝ) *ᵥ v = (2 * (Δ : ℝ) + m ^ 2) • v - (m ^ 2) • v := by
      rw [← hev]; abel
    rw [this, ← sub_smul]
    congr 1
    ring
  · rintro ⟨v, hv, hev⟩
    refine ⟨v, hv, ?_⟩
    rw [hshift v, hev, ← add_smul]

/-! ## 4. The symmetry and the norm were both unnecessary -/

/-- **AND A POSITIVE SEMIDEFINITE CEILING THAT IS ATTAINED IS THE NORM.** So `‖A‖` never has to be
identified in advance: exhibiting one vector does it.

**`0 ≼ A` IS NOT DECORATION AND THE FIRST DRAFT OF THIS STATEMENT OMITTED IT AND WAS FALSE.** A
ceiling bounds `A` from above only; at `A = (−10) • 1` and `r = 0` the all-ones vector attains
`v ⬝ᵥ A *ᵥ v = 0 = r · (v ⬝ᵥ v)`, and `‖A‖ = 10 ≠ 0`. What the eigenvector gives is `|r| ≤ ‖A‖`
(`GreenNormExact.abs_le_opNorm_of_mulVec_smul`); the other direction needs the norm to be controlled
by the ceiling, which is `OpNormLoewnerConverse`'s positive-semidefinite case. -/
theorem opNorm_eq_of_quadForm_eq [Nonempty V] {A : Matrix V V ℝ} (hA : 0 ≤ A) {r : ℝ}
    (hr : A ≤ r • (1 : Matrix V V ℝ)) {v : V → ℝ} (hv : v ≠ 0)
    (h : v ⬝ᵥ A *ᵥ v = r * (v ⬝ᵥ v)) : ‖A‖ = r := by
  have hvv : 0 < v ⬝ᵥ v := by
    obtain ⟨p, hp⟩ : ∃ p, v p ≠ 0 := by
      by_contra hc
      exact hv (funext fun w => not_not.mp fun h' => hc ⟨w, h'⟩)
    rw [dotProduct]
    exact Finset.sum_pos' (fun i _ => mul_self_nonneg (v i))
      ⟨p, Finset.mem_univ p, mul_self_pos.mpr hp⟩
  refine le_antisymm ((OpNormLoewnerConverse.l2_opNorm_le_iff_le_smul_one hA).mpr hr) ?_
  have hev := (quadForm_eq_iff_mulVec_of_le hr v).mp h
  exact le_trans (le_abs_self r)
    (GreenNormExact.abs_le_opNorm_of_mulVec_smul (ne_of_gt hvv) hev)

/-- **AND AT THE GRAPH LAPLACIAN THE EQUIVALENCE NEEDS ONLY REGULARITY.** On a `Δ`-regular graph
`LaplacianDegreeBound.lapMatrix_le_smul_one` supplies the ceiling `2Δ`, so *some vector attains the
degree bound* and *`2Δ` is an eigenvalue* are the same statement — **with no connectivity, no
`Nonempty V` and no norm**. §3 reached this only through `LaplacianNormSharp`, which needs both. -/
theorem exists_eigenvector_top_iff_exists_quadForm_eq {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) :
    (∃ v : V → ℝ, v ≠ 0 ∧ (G.lapMatrix ℝ) *ᵥ v = (2 * (Δ : ℝ)) • v)
      ↔ ∃ x : V → ℝ, x ≠ 0 ∧ x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x = 2 * (Δ : ℝ) * (x ⬝ᵥ x) := by
  have hdeg : ∀ p : V, (G.degree p : ℝ) ≤ (Δ : ℝ) := fun p => by rw [hreg p]
  have hle := LaplacianDegreeBound.lapMatrix_le_smul_one G hdeg
  constructor
  · rintro ⟨v, hv, hev⟩
    exact ⟨v, hv, (quadForm_eq_iff_mulVec_of_le hle v).mpr hev⟩
  · rintro ⟨x, hx, hq⟩
    exact ⟨x, hx, (quadForm_eq_iff_mulVec_of_le hle x).mp hq⟩

end RayleighAttainment
