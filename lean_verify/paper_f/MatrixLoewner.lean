/-
  MatrixLoewner.lean — the Loewner antitonicity of the matrix inverse, which
  this project recorded three times as absent from Mathlib and which is
  three lines from a theorem Mathlib has.

  WHY, AND THIS FILE IS PRIMARILY A CORRECTION. `UNLOCK_WATCHLIST`'s
  reflection-positivity ladder records two Mathlib gaps, "both checked by
  reading rather than recalled":

  > G1. There is no Loewner order on matrices in Mathlib.
  > G2. There is no operator antitonicity of the inverse.

  **BOTH ARE FALSE.** `Mathlib/Analysis/Matrix/Order.lean` defines
  `Matrix.instPartialOrder`, `A ≤ B := (B − A).PosSemidef`, scoped to
  `MatrixOrder`, together with `Matrix.instStarOrderedRing`; and
  `CStarAlgebra.inv_le_inv` proves exactly G2 in any unital C⋆-algebra.
  `GraphLaplacian` §7 already corrected G1 once and **got the correction
  wrong**, saying the order exists on operators but not on `Matrix`. It
  exists on `Matrix`. Three probes, three misses, each looking in a file
  named `Analysis/Matrix.lean` or `LinearAlgebra/Matrix/PosDef.lean` and
  never at `Analysis/Matrix/Order.lean`. See ERRATUM 62.

  WHAT THIS FILE PROVES, correcting by proving rather than by editing prose:
  1. **`instCStarAlgebra`** — Mathlib does not declare
     `CStarAlgebra (Matrix n n ℂ)`, but all five parent instances synthesise
     once `Matrix.Norms.L2Operator` is open, so the instance is one line. It
     is `scoped` so no other file inherits a norm choice.
  2. **`posDef_inv_le_inv_complex`** — G2 over `ℂ`, five lines from
     `CStarAlgebra.inv_le_inv`.
  3. **`cx` and the transfer** — complexification of a real matrix, with
     `cx_posSemidef` (via the Gram factorisation `A = √A ᴴ √A`, `CFC.sqrt`
     being available on real matrices), its converse `posSemidef_of_cx`,
     `cx_le_iff`, and `cx_inv`.
  4. **`posDef_inv_le_inv`** — **G2 OVER `ℝ`, WHICH IS RUNG 2 OF W1'S
     REFLECTION-POSITIVITY LADDER.** `0 ≺ A ≼ B ⟹ B⁻¹ ≼ A⁻¹`.
  5. **`lapMatrix_le`, `massive_le`** — `GraphLaplacian`'s monotonicity
     restated in Mathlib's actual order on `Matrix`, replacing two detours
     around an order that was there all along.
  6. **`green_antitone`** — and the immediate application, which is the
     remaining leg `GraphLaplacian` §7 wrote down and could not walk:
     **adding edges to a graph LOWERS its Green function in the Loewner
     order.** `green_antitone_broken` instantiates it at W3's contour graph.

  WHAT THIS DOES NOT DO. **It is not reflection positivity.** Rung 2 of the
  ladder is now available; rungs 1, 3 and 4 are not. R1 is the block
  decomposition of `massive` by the reflection into `A ∓ B` on the two
  eigenspaces, together with the identification of the reflected form with
  the off-diagonal block `½[(A−B)⁻¹ − (A+B)⁻¹]`; **none of that is here, and
  it is the bulk of the classical proof.** R3, positivity of the
  cross-coupling `B`, is free for even `n` and unproved. Nothing in this
  file mentions `refl`, `ReflectionPositive`, or a half of a box.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import GraphLaplacian
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

namespace MatrixLoewner

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## 1. The instance Mathlib has the parts for but does not assemble

All five parents — `NormedRing`, `CStarRing`, `CompleteSpace`,
`NormedAlgebra ℂ` and `StarModule ℂ` — synthesise for `Matrix n n ℂ` once
`Matrix.Norms.L2Operator` is open. Mathlib declines to bundle them because
that would fix a norm on `Matrix` globally. Kept `scoped` here for the same
reason.
-/

noncomputable scoped instance instCStarAlgebra : CStarAlgebra (Matrix n n ℂ) where

/-! ## 2. Antitonicity over `ℂ` -/

/-- **G2 OVER `ℂ`.** Nothing here is this project's mathematics: it is
    `CStarAlgebra.inv_le_inv` with the units packaged. -/
theorem posDef_inv_le_inv_complex {A B : Matrix n n ℂ} (hA : A.PosDef)
    (hab : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  have hAu : IsUnit A := hA.isUnit
  lift A to (Matrix n n ℂ)ˣ using hAu with A' hA'
  have hBu : IsUnit B := by
    have hBA : (B - A').PosSemidef := Matrix.le_iff.mp hab
    have hB : (B : Matrix n n ℂ).PosDef := by
      have hsplit : B = (B - (A' : Matrix n n ℂ)) + A' := by abel
      rw [hsplit]
      exact Matrix.PosDef.posSemidef_add hBA hA
    exact hB.isUnit
  lift B to (Matrix n n ℂ)ˣ using hBu with B' hB'
  have := CStarAlgebra.inv_le_inv (a := A') (b := B') hA.posSemidef.nonneg hab
  simpa [← Units.val_inv_eq_inv_val] using this

/-! ## 3. Complexification

Real matrices are not a C⋆-algebra — `CStarAlgebra` demands a `ℂ`-algebra —
so §2 has to be transported. The one step with content is `cx_posSemidef`,
and it goes through the Gram factorisation: `CFC.sqrt` is available on real
matrices, so a positive semidefinite `A` is `SᴴS` with `S` real, and the
complexification of `SᴴS` is `(cx S)ᴴ(cx S)`.

**THE PARAGRAPH ABOVE DESCRIBES A PROOF THIS FILE NO LONGER USES** (`ERRATUM 274`,
26 August 2026). It is kept because it is the honest record of how the section was
first built, and because the route it describes is correct — it is simply not the
cheapest one, and its cost was a hypothesis.

The Gram route needs `[Fintype n]` and `[DecidableEq n]`: `CFC.sqrt` and the matrix
product both do. `Matrix.PosSemidef` and `Matrix.PosDef` need **neither** — each is a
condition on finitely-supported vectors `x : n →₀ R`. So the instances were the
PROOF's hypothesis sitting in the statement, and four theorems here were stated for
an arbitrary index type and proved only for a finite decidable one.

`cx_form_eq` replaces the factorisation with a splitting that uses no finiteness at
all: write `z : n →₀ ℂ` as `u + iv`, and the form becomes
`∑∑ Aᵢⱼ(uᵢuⱼ + vᵢvⱼ) + i·∑∑ Aᵢⱼ(uᵢvⱼ − vᵢuⱼ)`, whose real part is two applications of
the real hypothesis and whose imaginary part cancels under `i ↔ j` because `A` is
symmetric. `cx_posSemidef`, `posSemidef_of_cx`, `cx_le_iff` and `cx_posDef` all follow
from it and all `omit` both instances. `cx_inv` keeps them, and irreducibly: it is
about `det` and `A⁻¹`.
-/

/-- A real matrix read as a complex one. -/
def cx (A : Matrix n n ℝ) : Matrix n n ℂ := A.map (fun r => (r : ℂ))

omit [Fintype n] [DecidableEq n] in
@[simp] theorem cx_apply (A : Matrix n n ℝ) (i j : n) : cx A i j = (A i j : ℂ) := rfl

omit [Fintype n] [DecidableEq n] in
theorem cx_injective : Function.Injective (cx (n := n)) := by
  intro A B h
  ext i j
  have hij : (A i j : ℂ) = (B i j : ℂ) := by
    simpa using congrArg (fun M : Matrix n n ℂ => M i j) h
  exact_mod_cast hij

omit [DecidableEq n] in
@[simp] theorem cx_mul (A B : Matrix n n ℝ) : cx (A * B) = cx A * cx B := by
  ext i j
  simp only [cx_apply, Matrix.mul_apply]
  push_cast
  rfl

omit [Fintype n] in
@[simp] theorem cx_one : cx (1 : Matrix n n ℝ) = 1 := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

omit [Fintype n] [DecidableEq n] in
@[simp] theorem cx_sub (A B : Matrix n n ℝ) : cx (A - B) = cx A - cx B := by
  ext i j; simp [Matrix.sub_apply]

omit [Fintype n] [DecidableEq n] in
@[simp] theorem cx_conjTranspose (A : Matrix n n ℝ) : (cx A)ᴴ = cx Aᴴ := by
  ext i j; simp [Matrix.conjTranspose_apply]

omit [Fintype n] [DecidableEq n] in
/-- A double `Finsupp.sum` against a fixed kernel, pushed through `mapRange`. Used in both
    directions of the complexification: `ℂ → ℝ` taking real and imaginary parts, and `ℝ → ℂ`
    embedding. Stated once rather than inlined twice (`ERRATUM 271`). -/
private theorem sum_pair_mapRange {R S : Type*} [Zero R] [NonUnitalNonAssocSemiring S]
    [StarRing S] (f : R → S) (hf : f 0 = 0) (x : n →₀ R) (B : n → n → S) :
    ((Finsupp.mapRange f hf x).sum fun i a =>
        (Finsupp.mapRange f hf x).sum fun j b => star a * B i j * b)
      = x.sum fun i a => x.sum fun j b => star (f a) * B i j * f b := by
  rw [Finsupp.sum_mapRange_index (by intro a; simp)]
  refine Finsupp.sum_congr fun i _ => ?_
  rw [Finsupp.sum_mapRange_index (by intro a; simp)]

omit [Fintype n] [DecidableEq n] in
/-- **THE COMPLEX FORM OF A REAL SYMMETRIC MATRIX IS THE SUM OF TWO REAL FORMS.** Split
    `z : n →₀ ℂ` into real and imaginary parts `u, v`; then
    `∑∑ z̄ᵢAᵢⱼzⱼ = ∑∑ Aᵢⱼ(uᵢuⱼ + vᵢvⱼ) + i·∑∑ Aᵢⱼ(uᵢvⱼ − vᵢuⱼ)`, and the imaginary part
    vanishes because `A` is symmetric, by relabelling `i ↔ j`. **No finiteness of `n` is used
    anywhere**, which is the whole point: `Matrix.PosSemidef` and `Matrix.PosDef` are conditions
    on finitely-supported vectors, and it is the GRAM route through `CFC.sqrt` — not the
    statement — that needs `[Fintype n]`. -/
private theorem cx_form_eq {A : Matrix n n ℝ} (hA : A.IsHermitian) (z : n →₀ ℂ) :
    (z.sum fun i zi => z.sum fun j zj => star zi * cx A i j * zj)
      = ((((Finsupp.mapRange Complex.re Complex.zero_re z).sum fun i a =>
              (Finsupp.mapRange Complex.re Complex.zero_re z).sum fun j b => star a * A i j * b)
          + ((Finsupp.mapRange Complex.im Complex.zero_im z).sum fun i a =>
              (Finsupp.mapRange Complex.im Complex.zero_im z).sum fun j b =>
                star a * A i j * b) : ℝ) : ℂ) := by
  have hsymm : ∀ i j, A j i = A i j := fun i j => by
    have := congrArg (fun M : Matrix n n ℝ => M i j) (hA : Aᴴ = A)
    simpa [Matrix.conjTranspose_apply] using this
  rw [sum_pair_mapRange Complex.re Complex.zero_re z A,
    sum_pair_mapRange Complex.im Complex.zero_im z A]
  simp only [Finsupp.sum, star_trivial]
  have hcross : (∑ i ∈ z.support, ∑ j ∈ z.support, (z i).im * A i j * (z j).re)
      = ∑ i ∈ z.support, ∑ j ∈ z.support, (z i).re * A i j * (z j).im := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsymm a b]; ring
  have hre_eq : (∑ i ∈ z.support, ∑ j ∈ z.support, star (z i) * cx A i j * z j).re
      = (∑ i ∈ z.support, ∑ j ∈ z.support, (z i).re * A i j * (z j).re)
        + ∑ i ∈ z.support, ∑ j ∈ z.support, (z i).im * A i j * (z j).im := by
    rw [← Finset.sum_add_distrib]
    simp only [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [cx_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have him_eq : (∑ i ∈ z.support, ∑ j ∈ z.support, star (z i) * cx A i j * z j).im = 0 := by
    have hsplit : (∑ i ∈ z.support, ∑ j ∈ z.support, star (z i) * cx A i j * z j).im
        = (∑ i ∈ z.support, ∑ j ∈ z.support, (z i).re * A i j * (z j).im)
          - ∑ i ∈ z.support, ∑ j ∈ z.support, (z i).im * A i j * (z j).re := by
      rw [← Finset.sum_sub_distrib]
      simp only [Complex.im_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [cx_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    rw [hsplit, hcross, sub_self]
  exact Complex.ext (by rw [Complex.ofReal_re]; exact hre_eq)
    (by rw [Complex.ofReal_im]; exact him_eq)

omit [Fintype n] [DecidableEq n] in
/-- **The complexification of a positive semidefinite real matrix is positive semidefinite, at
    ANY index type.** The hypothesis the Gram route needed was the PROOF's, not the statement's;
    `cx_form_eq` is the proof that does without it. -/
theorem cx_posSemidef {A : Matrix n n ℝ} (h : A.PosSemidef) : (cx A).PosSemidef := by
  refine ⟨(cx_conjTranspose A).trans (congrArg cx (h.isHermitian : Aᴴ = A)), fun z => ?_⟩
  rw [cx_form_eq h.isHermitian z]
  exact_mod_cast add_nonneg (h.2 _) (h.2 _)


omit [Fintype n] [DecidableEq n] in
/-- And back, and also at any index type: a real vector is a complex one whose imaginary part
    is zero, so the complex condition RESTRICTS. Same route as `cx_posSemidef` and the same
    `sum_pair_mapRange`, run in the other direction. -/
theorem posSemidef_of_cx {A : Matrix n n ℝ} (h : (cx A).PosSemidef) : A.PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · have h1 : (cx A)ᴴ = cx A := h.isHermitian
    rw [cx_conjTranspose] at h1
    exact cx_injective h1
  · have hc := h.2 (Finsupp.mapRange (fun r : ℝ => (r : ℂ)) Complex.ofReal_zero x)
    rw [sum_pair_mapRange (fun r : ℝ => (r : ℂ)) Complex.ofReal_zero x (cx A)] at hc
    have hcast : (x.sum fun i a => x.sum fun j b =>
          star ((a : ℂ)) * cx A i j * (b : ℂ))
        = (((x.sum fun i a => x.sum fun j b => star a * A i j * b) : ℝ) : ℂ) := by
      simp only [Finsupp.sum, Complex.ofReal_sum, cx_apply, Complex.star_def,
        Complex.conj_ofReal, star_trivial]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      ring
    rw [hcast] at hc
    exact_mod_cast hc

omit [Fintype n] [DecidableEq n] in
theorem cx_le_iff {A B : Matrix n n ℝ} : cx A ≤ cx B ↔ A ≤ B := by
  rw [Matrix.le_iff, Matrix.le_iff, ← cx_sub]
  exact ⟨posSemidef_of_cx, cx_posSemidef⟩

theorem cx_inv {A : Matrix n n ℝ} (h : IsUnit A.det) : cx A⁻¹ = (cx A)⁻¹ :=
  (Matrix.inv_eq_right_inv (by rw [← cx_mul, Matrix.mul_nonsing_inv _ h, cx_one])).symm

omit [Fintype n] [DecidableEq n] in
/-- **And positive DEFINITE, also at any index type.** The determinant route this file used
    before genuinely needs `[Fintype n]` and `[DecidableEq n]` — `det` and `A⁻¹` do — but
    `Matrix.PosDef`, like `PosSemidef`, is a condition on finitely-supported vectors, so the
    same splitting works: a nonzero `z` has a nonzero real or imaginary part, that part
    contributes strictly, and the other contributes at least zero. -/
theorem cx_posDef {A : Matrix n n ℝ} (h : A.PosDef) : (cx A).PosDef := by
  refine ⟨(cx_conjTranspose A).trans (congrArg cx (h.isHermitian : Aᴴ = A)), fun z hz => ?_⟩
  rw [cx_form_eq h.isHermitian z]
  have hne : Finsupp.mapRange Complex.re Complex.zero_re z ≠ 0
      ∨ Finsupp.mapRange Complex.im Complex.zero_im z ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hz (Finsupp.ext fun i => ?_)
    have h1 : (z i).re = 0 := by
      have := Finsupp.ext_iff.mp hc.1 i; simpa using this
    have h2 : (z i).im = 0 := by
      have := Finsupp.ext_iff.mp hc.2 i; simpa using this
    simpa [Complex.ext_iff] using ⟨h1, h2⟩
  rcases hne with hne | hne
  · exact_mod_cast add_pos_of_pos_of_nonneg (h.2 hne) (h.posSemidef.2 _)
  · exact_mod_cast add_pos_of_nonneg_of_pos (h.posSemidef.2 _) (h.2 hne)

/-! ## 4. Antitonicity over `ℝ` — rung 2 of the ladder -/

/-- **THE LOEWNER ANTITONICITY OF THE MATRIX INVERSE**, over `ℝ`:
    `0 ≺ A ≼ B ⟹ B⁻¹ ≼ A⁻¹`.

    **This is gap G2 of `UNLOCK_WATCHLIST`'s reflection-positivity ladder,
    and rung 2 of that ladder is the whole theorem given rung 1.** Recorded
    three times as absent from Mathlib; present, in a file none of the three
    probes opened. -/
theorem posDef_inv_le_inv {A B : Matrix n n ℝ} (hA : A.PosDef) (hab : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  have hBA : (B - A).PosSemidef := Matrix.le_iff.mp hab
  have hB : B.PosDef := by
    have hsplit : B = (B - A) + A := by abel
    rw [hsplit]; exact Matrix.PosDef.posSemidef_add hBA hA
  have hdA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hdB : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit
  have hcomplex := posDef_inv_le_inv_complex (cx_posDef hA) (cx_le_iff.mpr hab)
  rw [← cx_inv hdA, ← cx_inv hdB] at hcomplex
  exact cx_le_iff.mp hcomplex

/-! ## 5. The application `GraphLaplacian` §7 wrote down and could not walk

That file proved `G ≤ G' → L_G ≼ L_{G'}` and then said, verbatim: *"The
statement a physicist wants is the reverse order on GREEN FUNCTIONS — more
edges, faster decay — and that needs operator antitonicity of the inverse …
So §4's remaining leg is written down here and not attempted."* §4 above is
that leg.
-/

section Graphs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **ADDING EDGES LOWERS THE GREEN FUNCTION.** More connections, faster
    decay — the ordering the physics reads off, now in Mathlib's own Loewner
    order on matrices. -/
theorem green_antitone {G G' : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (h : G ≤ G') {m : ℝ} (hm : m ≠ 0) :
    GraphLaplacian.green G' m ≤ GraphLaplacian.green G m :=
  posDef_inv_le_inv (GraphLaplacian.massive_posDef G hm)
    (Matrix.le_iff.mpr (GraphLaplacian.massive_sub_posSemidef h m))

/-- **`GraphLaplacian`'s monotonicity, in Mathlib's actual order on
    `Matrix`.** That file could only state it as `PosSemidef` of a difference
    or, after its own half-correction, as a `≤` between `toEuclideanLin`
    images. Both were detours around an order that was there. -/
theorem lapMatrix_le {G G' : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (h : G ≤ G') : G.lapMatrix ℝ ≤ G'.lapMatrix ℝ :=
  Matrix.le_iff.mpr (GraphLaplacian.lapMatrix_sub_posSemidef h)

theorem massive_le {G G' : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (h : G ≤ G') (m : ℝ) : GraphLaplacian.massive G m ≤ GraphLaplacian.massive G' m :=
  Matrix.le_iff.mpr (GraphLaplacian.massive_sub_posSemidef h m)

open IsingFiniteVolume IsingContourSeparation IsingContourEnergy in
/-- Instantiated at the two graphs the estate already had on the same sites:
    a configuration's broken-bond graph sits inside the lattice, so its Green
    function dominates the lattice's. -/
theorem green_antitone_broken (n : ℕ) (σ : Config n) {m : ℝ} (hm : m ≠ 0) :
    GraphLaplacian.green (latticeGraph n) m
      ≤ GraphLaplacian.green (brokenGraph σ) m :=
  green_antitone (GraphLaplacian.brokenGraph_le n σ) hm

end Graphs

/-! ## 6. Review round 78 — the ways this could be hollow

**"Almost none of this is new mathematics."** Correct, and that is the
finding. §2 is `CStarAlgebra.inv_le_inv` with units packaged; §1 is a
one-line instance whose five parents Mathlib already provides. The only
mathematics this project supplies is §3, the transfer from `ℂ` to `ℝ`, and
even there `cx_posSemidef` is the standard Gram-factorisation argument.
**The value of the file is that it replaces three recorded "Mathlib does not
have this" claims with a theorem**, and the correct response to that is
embarrassment plus ERRATUM 62, not a claim of difficulty.

**"Was G2 really recorded as absent three times?"** Yes, and here they are so
a reader can check: the `LatticeReflection` ladder entry in
`UNLOCK_WATCHLIST` ("G2. There is no operator antitonicity of the inverse.
No `inv_le_inv` for `PosDef`"), commit `a03c666`'s message ("rung two needs
operator antitonicity of matrix inversion, which Mathlib does not have"), and
`GraphLaplacian` §7 ("that needs operator antitonicity of the inverse … A
grep for that shape across `Mathlib/LinearAlgebra/Matrix/` and
`Mathlib/Analysis/` returns nothing"). **The third of those was written while
correcting the first**, which is what makes this worth an erratum rather than
a fix.

**"§5 could be a rename of §4."** It is one application of it, and the
header says so. What makes it worth stating is that `GraphLaplacian` §7
explicitly wrote this down as its unwalked remaining leg, which is the
`PROOF_STRATEGY` §3 discipline working as intended: the leg was recorded,
and the recording is what made it obvious what to do the moment the gap
turned out not to be a gap.

**"This could be claimed as reflection positivity."** It is rung 2 of four
and the header lists the other three. R1 — block-diagonalising `massive` by
the reflection and identifying the reflected form with the off-diagonal
block of the Green function — is the bulk of the classical proof and is
entirely absent; **no theorem in this file mentions `refl`,
`ReflectionPositive`, or a half of a box.** R3, positivity of the
cross-coupling, is free for even `n` and also absent. A rung is not a
ladder.

**"The `scoped instance` could leak a norm choice."** It is `scoped` to
`MatrixLoewner` precisely so it does not; Mathlib declines to declare it
globally for the same reason, and this file inherits that judgement rather
than overriding it. Any file wanting §2 must opt in.

**"`cx_le_iff` could be doing the work in one direction only."** Both
directions are used and both are proved: `mpr` (real `≤` to complex) carries
the hypothesis of §4 across, `mp` (complex back to real) carries the
conclusion back, and they rest on `cx_posSemidef` and `posSemidef_of_cx`
respectively, which are genuinely different arguments — a factorisation one
way, a restriction to real vectors the other.
-/

end MatrixLoewner
