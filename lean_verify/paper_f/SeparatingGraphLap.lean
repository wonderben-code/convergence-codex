import PawSignlessSpectrum
import EigenBasisDimension

/-!
# A graph whose Laplacian spectrum is simple: the six-vertex witness

`SignlessTwins` ended the search through the estate's existing graphs. It proved that two twin pairs
degenerate **both** operators, eliminated four of the six families the separation item names, read
the odd cycle off two proved formulas, and left the item with **no candidate in the estate**: a
separating graph would have to be built. **This is the first half of building one.**

## What the search found, and it is worth recording before the file starts

**AN EXHAUSTIVE MACHINE SEARCH OVER EVERY CONNECTED GRAPH ON AT MOST SIX VERTICES**, run outside
Lean before a line of this was written. On **three, four and five** vertices — 4, 38 and 728
connected graphs — the two answers **never differ**. On **six** they differ, in **twelve**
isomorphism classes: **seven** with `L` simple and `Q` degenerate, **five** the other way round.
**Six vertices is the smallest place this question has an answer**, and that is a fact about graphs
which no theorem in this estate proves — ⚠ **the search is not formalised and is not claimed as
one** (`ERRATUM 246`). What is formalised is one witness.

## The witness

Vertices `Fin 6`, edges `0–3, 0–5, 1–2, 1–3, 1–4, 2–3, 2–4`: a **diamond** `1–2–3` with `1–2`,
`1–3`, `2–3` and the extra vertices hung off it — `4` joined to both `1` and `2`, `0` joined to `3`,
and a pendant `5` on `0`. Degrees `2, 3, 3, 3, 2, 1`. It contains the triangle `1–2–3`, so it is
**not two-colourable**; and it has exactly **one** closed twin pair, `1` and `2`, where
`SignlessTwins` needs **two** — which is why that file's theorem does not exclude it and is the
reason it was worth looking here.

## What is proved

**`sepGraph`, `sepGraph_degree`, `lapMatrix_sepGraph`** — the graph, its degrees, and its Laplacian
as an explicit `6 × 6` matrix.

**`sepLap_mulVec`, `sepLap_mulVec_surd`** — six eigenvectors. Four are integral and their
eigenvalues are `0`, `2`, `3`, `4`; the other two are **one parametric vector**
`(1 − λ, −λ, −λ, 2λ − 1, λ − 1, 1)` evaluated at the two roots of `λ² − 5λ + 2`, which is
`(5 ± √17)/2`. **The parametric form is the whole trick**: `√17 = 5 − 2λ` at either root, so every
surd in the eigenvector is a linear polynomial in the eigenvalue and the verification is one
polynomial identity reduced modulo `λ² − 5λ + 2`, done once rather than twice.

**AND `√17` IS ALREADY IN THE ESTATE**, with the bounds this file needs:
`PawSignlessSpectrum.sq_sqrt17`, `four_lt_sqrt17` and `sqrt17_lt_five` were written for the paw's
**signless** spectrum, whose quadratic factor is `λ² − 5λ + 2` — **the same polynomial**. Two
unrelated graphs, one surd, and the second one pays nothing for it.

**`sepEig_injective`, `sepBasis`, `finrank_eigenspace_sep`, `finrank_lapMatrix_le_one_sep`** — the
six eigenvalues are pairwise distinct, so the six vectors are a basis, so every eigenspace is a
line: **`L` is simple on this graph.**

## What is NOT here

* **NOTHING ABOUT `Q`.** This file computes the **Laplacian** and nothing else; the signless
  operator is the next unit's, and the separation claim belongs there. **Half a witness is not a
  witness**, and this file makes no claim about the open item.
* **NO CHARACTERISTIC POLYNOMIAL.** The route is six eigenvectors and a basis, as in
  `PawSimpleSpectrum`; `L`'s charpoly factors as `λ(λ−2)(λ−3)(λ−4)(λ²−5λ+2)` and **that
  factorisation is not proved here**, being unnecessary.
* **NOTHING ABOUT MINIMALITY IN LEAN.** That six vertices is the smallest is a search result, stated
  above and fenced there.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): none. Every statement is about one explicit
graph on `Fin 6`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SeparatingGraphLap

open Matrix SimpleGraph FieldSimpleConverse

/-! ## 1. The graph -/

/-- Adjacency of the witness: `0–3, 0–5, 1–2, 1–3, 1–4, 2–3, 2–4`. -/
def sepAdj : Fin 6 → Fin 6 → Bool
  | 0, 3 => true | 3, 0 => true
  | 0, 5 => true | 5, 0 => true
  | 1, 2 => true | 2, 1 => true
  | 1, 3 => true | 3, 1 => true
  | 1, 4 => true | 4, 1 => true
  | 2, 3 => true | 3, 2 => true
  | 2, 4 => true | 4, 2 => true
  | _, _ => false

def sepGraph : SimpleGraph (Fin 6) where
  Adj p q := sepAdj p q = true
  symm := by intro p q h; revert p q; decide
  loopless := ⟨by intro p h; revert p; decide⟩

instance : DecidableRel sepGraph.Adj := fun p q =>
  inferInstanceAs (Decidable (sepAdj p q = true))

theorem sepGraph_adj (p q : Fin 6) : sepGraph.Adj p q ↔ sepAdj p q = true := Iff.rfl

theorem sepGraph_degree : ∀ v : Fin 6, sepGraph.degree v = ![2, 3, 3, 3, 2, 1] v := by decide

/-- **IT CONTAINS A TRIANGLE**, so it is not two-colourable — which is what puts it outside the
transfer this whole chain rests on. -/
theorem sepGraph_triangle : sepGraph.Adj 1 2 ∧ sepGraph.Adj 2 3 ∧ sepGraph.Adj 1 3 := by decide

/-- **AND IT HAS EXACTLY ONE CLOSED TWIN PAIR**, so `SignlessTwins`' theorem — which needs two —
does not exclude it. -/
theorem sepGraph_closed_twin :
    insert (1 : Fin 6) (sepGraph.neighborFinset 1)
      = insert (2 : Fin 6) (sepGraph.neighborFinset 2) := by decide

/-! ## 2. Its Laplacian -/

def sepLap : Matrix (Fin 6) (Fin 6) ℝ :=
  !![2, 0, 0, -1, 0, -1;
     0, 3, -1, -1, -1, 0;
     0, -1, 3, -1, -1, 0;
     -1, -1, -1, 3, 0, 0;
     0, -1, -1, 0, 2, 0;
     -1, 0, 0, 0, 0, 1]

theorem lapMatrix_sepGraph : sepGraph.lapMatrix ℝ = sepLap := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix, sepLap,
      sepGraph_adj, sepAdj, sepGraph_degree]

/-! ## 3. Four integral eigenvectors, and one parametric pair -/

def sepVecInt : Fin 4 → (Fin 6 → ℝ) :=
  ![![1, 1, 1, 1, 1, 1], ![-1, 0, 0, -1, 1, 1], ![-2, 1, 1, 1, -2, 1], ![0, -1, 1, 0, 0, 0]]

def sepEigInt : Fin 4 → ℝ := ![0, 2, 3, 4]

theorem sepLap_mulVec (k : Fin 4) : sepLap *ᵥ sepVecInt k = sepEigInt k • sepVecInt k := by
  fin_cases k <;> ext v <;> fin_cases v <;>
    simp [sepLap, sepVecInt, sepEigInt, Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> norm_num

/-- The parametric eigenvector. **`√17 = 5 − 2λ` at either root**, so every surd is a linear
polynomial in the eigenvalue and one identity does both modes. -/
def surdVec (l : ℝ) : Fin 6 → ℝ := ![1 - l, -l, -l, 2 * l - 1, l - 1, 1]

/-- **ONE VERIFICATION FOR BOTH MODES.** -/
theorem sepLap_mulVec_surd {l : ℝ} (hl : l ^ 2 = 5 * l - 2) :
    sepLap *ᵥ surdVec l = l • surdVec l := by
  ext v
  fin_cases v <;>
    simp [sepLap, surdVec, Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> nlinarith [hl]

/-! ## 4. The six eigenvalues, and the six eigenvectors as one family -/

open PawSignlessSpectrum in
/-- The two roots of `λ² − 5λ + 2`, which is **the paw's signless quadratic**, so `√17` and its
bounds are cited rather than re-derived. -/
noncomputable def sepEig : Fin 6 → ℝ :=
  ![0, 2, 3, 4, (5 + Real.sqrt 17) / 2, (5 - Real.sqrt 17) / 2]

noncomputable def sepVec : Fin 6 → (Fin 6 → ℝ) :=
  ![sepVecInt 0, sepVecInt 1, sepVecInt 2, sepVecInt 3,
    surdVec ((5 + Real.sqrt 17) / 2), surdVec ((5 - Real.sqrt 17) / 2)]

open PawSignlessSpectrum in
theorem sq_root_add : ((5 + Real.sqrt 17) / 2) ^ 2 = 5 * ((5 + Real.sqrt 17) / 2) - 2 := by
  nlinarith [sq_sqrt17]

open PawSignlessSpectrum in
theorem sq_root_sub : ((5 - Real.sqrt 17) / 2) ^ 2 = 5 * ((5 - Real.sqrt 17) / 2) - 2 := by
  nlinarith [sq_sqrt17]

theorem sepLap_mulVec_all (k : Fin 6) : sepLap *ᵥ sepVec k = sepEig k • sepVec k := by
  fin_cases k
  · exact sepLap_mulVec 0
  · exact sepLap_mulVec 1
  · exact sepLap_mulVec 2
  · exact sepLap_mulVec 3
  · exact sepLap_mulVec_surd sq_root_add
  · exact sepLap_mulVec_surd sq_root_sub

open PawSignlessSpectrum in
theorem sepEig_injective : Function.Injective sepEig := by
  have h4 := four_lt_sqrt17
  have h5 := sqrt17_lt_five
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [sepEig] at h ⊢ <;> linarith

open PawSignlessSpectrum in
theorem sepVec_ne_zero (k : Fin 6) : sepVec k ≠ 0 := by
  have h4 := four_lt_sqrt17
  have h5 := sqrt17_lt_five
  fin_cases k
  · intro h; have := congrFun h 0; simp [sepVec, sepVecInt] at this
  · intro h; have := congrFun h 0; simp [sepVec, sepVecInt] at this
  · intro h; have := congrFun h 0; simp [sepVec, sepVecInt] at this
  · intro h; have := congrFun h 1; simp [sepVec, sepVecInt] at this
  · intro h; have := congrFun h 5; simp [sepVec, surdVec] at this
  · intro h; have := congrFun h 5; simp [sepVec, surdVec] at this

theorem hasEigenvector_sep (k : Fin 6) :
    Module.End.HasEigenvector (Matrix.mulVecLin sepLap) (sepEig k) (sepVec k) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact sepLap_mulVec_all k
  · exact sepVec_ne_zero k

theorem sepVec_linearIndependent : LinearIndependent ℝ sepVec :=
  Module.End.eigenvectors_linearIndependent' _ _ sepEig_injective _ hasEigenvector_sep

noncomputable def sepBasis : Module.Basis (Fin 6) ℝ (Fin 6 → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank sepVec_linearIndependent (by simp)

theorem sepBasis_apply (k : Fin 6) : sepBasis k = sepVec k :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) k

/-! ## 5. So every eigenspace of this graph's Laplacian is a line -/

theorem finrank_eigenspace_sep (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (sepGraph.lapMatrix ℝ) - μ • LinearMap.id))
      = Nat.card {k : Fin 6 // sepEig k = μ} :=
  EigenBasisDimension.finrank_ker_sub_smul sepBasis
    (fun k => by rw [sepBasis_apply, lapMatrix_sepGraph]; exact sepLap_mulVec_all k) μ

/-- **THE LAPLACIAN OF THE WITNESS IS SIMPLE.** -/
theorem finrank_lapMatrix_le_one_sep (ν : ℝ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (sepGraph.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1 := by
  rw [finrank_eigenspace_sep, Finite.card_le_one_iff_subsingleton]
  exact ⟨fun a b => Subtype.ext (sepEig_injective (a.2.trans b.2.symm))⟩

end SeparatingGraphLap
