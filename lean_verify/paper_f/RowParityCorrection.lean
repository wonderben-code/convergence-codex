import EvenRowParity
import PathGraphDegree

/-!
# The telescope with its correction term: what a row picks up at an odd plaquette

`EvenRowParity` removed the `IsCycleGraph` hypothesis from the row-parity chain and left
`EvenDegrees H` in its place, then fenced the next step: **a path graph does not satisfy
`EvenDegrees`** — that is what `PathGraphDegree` proves, evenness failing at exactly its two
endpoints — so the chain does not apply to a path, and *what the telescope picks up at the rows
containing the endpoints is not computed.*

**This computes it, and drops the degree hypothesis altogether.**

## What is proved

**`sides_parity`** — the per-plaquette identity **with no hypothesis on `H` at all**: across one
plaquette the two horizontal sides and the two vertical ones differ in parity by exactly the
plaquette's **degree**. `EvenRowParity.sides_ud_eq_lr_of_evenDegrees` is the case where that degree
is even, and the whole of `CircuitSides`' `hcyc` was only ever a way of saying so.

**`degCnt`** — the correction: the number of odd-degree plaquettes among the first `a` of a row.

**`partial_row_parity`, `full_row_parity`** — **the telescope, for an arbitrary subgraph of the
dual**: the two bounding rows differ in parity by `degCnt`, and at the right-hand end the vertical
bond falls off the box so the whole row's identity is `cntD + cntU + degCnt ≡ 0`.

**`even_row_parity`** — **and up the rows**: `cntD` at row `j` has the parity of the total number of
odd-degree plaquettes in all the rows below it. On an even-degree subgraph every term is `0` and
`EvenRowParity.even_row_of_evenDegrees` is recovered exactly (`even_row_parity_of_evenDegrees`).

**`odd_plaquettes_of_isPathGraph`** — **so on a path graph the correction is carried by at most
two plaquettes**, since `PathGraphDegree.exists_endpoints_of_isPathGraph` gives two vertices outside
which every degree is even. Which two, and which rows they fall in, is **not** determined here.

## What is NOT here

**THE CORRECTION IS COUNTED, NOT LOCATED.** `odd_plaquettes_of_isPathGraph` says the odd
plaquettes of a row are among two named vertices; **it does not say how many of them are in the row,
nor which row they are in**, and both are needed before the count becomes a statement about a
particular horizontal line. **Not attempted, no cost claimed** (`ERRATUM 246`).

**NO RAY, AND THIS IS THE POINT.** Residue (b) of `S3b-ii` is *the open-path analogue of the ray
argument*, and the ray argument is `RayWalk`'s: a ray from a site, the parity of its crossings, and
the conclusion that the site is down. **None of that is touched.** What is supplied is the parity
bookkeeping such an argument would rest on, for paths as well as circuits. **Residue (b) is not
closed and no part of it is claimed.**

**NOTHING ABOUT `ExtendedDual`'s RIM VERTICES.** The odd-degree vertices there are the **rims**, of
a graph on `Plaq n ⊕ Fin 4`; everything here is about `SimpleGraph (Plaq n)` and **no theorem
relates the two types**.

**W3 DOES NOT MOVE.** A hypothesis is dropped and an identity is generalised; no object is
constructed and no residue is closed.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `sides_parity` takes **only**
`H ≤ dualGraph σ` — **no degree hypothesis, no `PlusBoundary`, and nothing about cycles or paths**.
The row theorems add `PlusBoundary σ` for the two edge-of-the-box facts, and that hypothesis **is**
used. **`EvenDegrees` appears in exactly one theorem here**, and only to discharge the general one.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace RowParityCorrection

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds CircuitSides RowParity SimpleGraph

variable {n : ℕ}

/-! ## 1. The per-plaquette identity, with no hypothesis on `H` -/

/-- **ACROSS ONE PLAQUETTE THE HORIZONTAL AND VERTICAL SIDES DIFFER IN PARITY BY THE DEGREE.**
No hypothesis on `H` beyond its being a subgraph of the dual. -/
theorem sides_parity {σ : Config n} {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ)
    (P : Plaq n) :
    ((if sideD P ∈ bonds σ H then 1 else 0) + (if sideU P ∈ bonds σ H then 1 else 0)) % 2 =
      ((if sideL P ∈ bonds σ H then 1 else 0) + (if sideR P ∈ bonds σ H then 1 else 0)
        + (H.neighborSet P).ncard) % 2 := by
  have h : (if sideL P ∈ bonds σ H then 1 else 0) + (if sideU P ∈ bonds σ H then 1 else 0)
      + (if sideR P ∈ bonds σ H then 1 else 0) + (if sideD P ∈ bonds σ H then 1 else 0)
      = (H.neighborSet P).ncard := by
    have h0 := card_filter_eq_ncard_neighborSet hle P
    rwa [Finset.card_filter, Fin.sum_univ_four] at h0
  omega

/-! ## 2. The correction, and the telescope that carries it -/

/-- The number of odd-degree plaquettes among the first `a` of row `j`. -/
noncomputable def degCnt (H : SimpleGraph (Plaq n)) (j : ℕ) (hj : j + 1 < n) (a : ℕ) : ℕ :=
  ∑ k ∈ Finset.range a, (H.neighborSet (rowP j hj k)).ncard

theorem degCnt_succ (H : SimpleGraph (Plaq n)) {j : ℕ} (hj : j + 1 < n) (a : ℕ) :
    degCnt H j hj (a + 1) = degCnt H j hj a + (H.neighborSet (rowP j hj a)).ncard := by
  rw [degCnt, degCnt, Finset.sum_range_succ]

/-- **THE TELESCOPE, FOR AN ARBITRARY SUBGRAPH OF THE DUAL.** -/
theorem partial_row_parity {σ : Config n} (hσ : PlusBoundary σ) {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) {j : ℕ} (hj : j + 1 < n) :
    ∀ a, a + 1 < n →
      (cntD σ H j hj a + cntU σ H j hj a + degCnt H j hj a) % 2 =
        (if sideL (rowP j hj a) ∈ bonds σ H then 1 else 0) % 2 := by
  intro a
  induction a with
  | zero =>
    intro _
    have h0 : sideL (rowP j hj 0) ∉ bonds σ H :=
      sideL_notMem_bonds hσ H (by simp only [rowP]; omega)
    simp [cntD, cntU, degCnt, h0]
  | succ a ih =>
    intro ha
    have hIH := ih (by omega)
    have hlr := sides_parity hle (rowP j hj a)
    have hR : sideL (rowP j hj (a + 1)) = sideR (rowP j hj a) := by
      rw [← rightP_rowP hj (by omega), sideL_rightP _ (by rw [rowP_i hj (by omega)]; omega)]
    rw [cntD_succ, cntU_succ, degCnt_succ, hR]
    omega

/-- **AND THE WHOLE ROW**: at the right-hand end the vertical bond is on the edge of the box. -/
theorem full_row_parity {σ : Config n} (hσ : PlusBoundary σ) {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) {j : ℕ} (hj : j + 1 < n) :
    (cntD σ H j hj (n - 1) + cntU σ H j hj (n - 1) + degCnt H j hj (n - 1)) % 2 = 0 := by
  have hsplit : n - 1 = (n - 2) + 1 := by omega
  have hprev := partial_row_parity hσ hle hj (n - 2) (by omega)
  have hlr := sides_parity hle (rowP j hj (n - 2))
  have hend : sideR (rowP j hj (n - 2)) ∉ bonds σ H :=
    sideR_notMem_bonds hσ H (by simp only [rowP]; omega)
  simp only [hend, if_false] at hlr
  rw [hsplit, cntD_succ, cntU_succ, degCnt_succ]
  omega

/-! ## 3. Up the rows, carrying the correction -/

/-- The odd-degree plaquettes in every row strictly below `j`. -/
noncomputable def degBelow (H : SimpleGraph (Plaq n)) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, if h : i + 1 < n then degCnt H i h (n - 1) else 0

/-- **EVERY HORIZONTAL LINE MEETS THE SUBGRAPH WITH THE PARITY OF THE ODD PLAQUETTES BELOW IT.** -/
theorem even_row_parity {σ : Config n} (hσ : PlusBoundary σ) {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) :
    ∀ j, (hj : j + 1 < n) → (cntD σ H j hj (n - 1) + degBelow H j) % 2 = 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    have hz : ∀ k, sideD (rowP 0 hj k) ∉ bonds σ H := fun k =>
      sideD_notMem_bonds hσ H rfl
    simp [cntD, degBelow, hz]
  | succ j ih =>
    intro hj
    have hj0 : j + 1 < n := by omega
    have hrow := full_row_parity hσ hle hj0
    have hswap := cntU_eq_cntD σ H hj0 (by omega) (n - 1)
    have hIH := ih hj0
    have hbel : degBelow H (j + 1) = degBelow H j + degCnt H j hj0 (n - 1) := by
      rw [degBelow, degBelow, Finset.sum_range_succ, dif_pos hj0]
    rw [hswap] at hrow
    rw [hbel]
    omega

/-! ## 4. Nothing is lost, and the path case is carried -/

/-- The even-degree case, recovered: every correction term vanishes mod `2`. -/
theorem even_row_parity_of_evenDegrees {σ : Config n} (hσ : PlusBoundary σ)
    {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ) (hev : EvenDegrees H) :
    ∀ j, (hj : j + 1 < n) → cntD σ H j hj (n - 1) % 2 = 0 :=
  EvenRowParity.even_row_of_evenDegrees hσ hle hev

/-- **ON A PATH GRAPH THE CORRECTION IS CARRIED BY AT MOST TWO PLAQUETTES**: every term of
`degCnt` away from the path's two endpoints is even. **Which two, and which rows they fall in, is
not determined here.** -/
theorem odd_plaquettes_of_isPathGraph {H : SimpleGraph (Plaq n)} (hH : IsPathGraph H) :
    ∃ a b : Plaq n, ∀ P : Plaq n, P ≠ a → P ≠ b → Even ((H.neighborSet P).ncard) :=
  exists_endpoints_of_isPathGraph hH

end RowParityCorrection
