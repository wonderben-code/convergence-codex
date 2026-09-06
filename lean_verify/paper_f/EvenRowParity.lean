import RowParity
import DualDegreeExact

/-!
# The row-parity argument never needed a circuit; it needed even degrees

`CircuitSides` and `RowParity` build the crossing-parity argument the Peierls chain runs on: across
one plaquette the two horizontal sides carry the same parity as the two vertical ones, so summing
along a row telescopes, and **every horizontal line of the box meets the subgraph an even number of
times**. Both files carry `IsCycleGraph H` from top to bottom — sixteen occurrences between them.

**It is used in exactly one place.** `CircuitSides.even_card_sides` ends `exact hcyc.evenDegrees P`,
and nothing else in either chain looks at `hcyc` again. So the hypothesis those ten theorems carry
is not the hypothesis they use, and the argument holds for **any** subgraph of the dual with even
degrees — which is `ERRATUM 455`'s species found in the Peierls corner rather than the field one.

**The originals are not edited.** They are pushed records and they are correct; this adds.

## What is proved

**`even_card_sides_of_evenDegrees`, `even_sides_of_evenDegrees`,
`sides_ud_eq_lr_of_evenDegrees`** — the per-plaquette identity from `EvenDegrees H` alone.

**`partial_row_of_evenDegrees`, `full_row_of_evenDegrees`, `even_row_of_evenDegrees`,
`even_row_top_of_evenDegrees`** — the telescope and the induction up the rows, likewise. Every proof
is the original's with `hcyc.evenDegrees` replaced by the hypothesis itself.

**`even_row_isCycleGraph`** — and the old case falls out, by `IsCycleGraph.evenDegrees`. **Nothing
is lost.**

**`even_row_dualGraph`, `even_row_top_dualGraph`** — and this is what the generalisation buys:
**every horizontal line of the box meets the WHOLE CONTOUR an even number of times**, not merely one
circuit of a decomposition of it. `DualGraph.evenDegrees_dualGraph` gives the hypothesis at a `+`
boundary with no decomposition anywhere in sight, so the statement is available before the contour
is cut up and independently of how it is cut up.

## What is NOT here

**NO RAY, NO CROSSING COUNT, NO COVERING.** `RowParity`'s own fence stands: this is a parity of
counts along a row, and **the ray argument that turns it into a statement about a site's cluster is
`RayWalk`'s, and is not touched.** Residue (b) of `S3b-ii` — the open-path analogue of that ray
argument — is **not** attempted here. **No cost claimed** (`ERRATUM 246`).

**NOTHING ABOUT PATH GRAPHS.** The obvious next move is that a path graph has even degree
everywhere **except its two endpoints**, so the telescope would acquire a correction term at the
two rows containing them — which is the shape residue (b) wants. **That is not proved**, and as
of 2026-09-06 this estate has **no degree theorem for `SimpleGraph.IsPathGraph` at all**: the
predicate was defined today and appears only as a conclusion, where the cycle case has
`CycleDecomposition.ncard_neighborSet_cycle_of_mem`. **Counted, not assumed** (`ERRATUM 58`) —
every occurrence of the name in `paper_f` was read. **Not attempted, no cost claimed** (`ERRATUM
246`).

⚠ **THE DEGREE THEOREM EXISTS THE SAME DAY AND THE PARAGRAPH ABOVE IS KEPT AS WRITTEN**
(`ERRATUM 94`, annotated **in the unit that superseded it**, which is `ERRATUM 471`'s own rule).
`PathGraphDegree.even_ncard_neighborSet_path` gives **even at every non-endpoint** — two on the
path, none off it — and `ncard_neighborSet_path_endpoint` gives **exactly one at each end**, so
the endpoints are precisely where evenness fails. **The rest of the paragraph stands**: the
correction term is still not computed, because this file's chain takes `EvenDegrees H`
**globally**, and refining it to a pointwise hypothesis is a separate step and is not taken.

**THE `+` BOUNDARY IS STILL THERE.** `partial_row` and `even_row` take `PlusBoundary σ` for the two
edge-of-the-box facts (`sideL_notMem_bonds`, `sideD_notMem_bonds`), and **that hypothesis is used**
— it is not the one being removed here. The generalisation is in `H`, not in `σ`.

**W3 DOES NOT MOVE.** A hypothesis is weakened; no new object is constructed and no residue is
closed. **No claim is made that the Peierls chain gains anything beyond a wider hypothesis.**

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `EvenDegrees H` and `H ≤ dualGraph σ`
throughout, plus `PlusBoundary σ` from `partial_row` onwards. **`IsCycleGraph` appears in exactly
one theorem here**, `even_row_isCycleGraph`, and only to discharge the general one.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace EvenRowParity

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds CircuitSides RowParity SimpleGraph

variable {n : ℕ}

/-! ## 1. The per-plaquette identity, from even degrees alone -/

theorem even_card_sides_of_evenDegrees {σ : Config n} {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (hev : EvenDegrees H) (P : Plaq n) :
    Even (Finset.univ.filter fun d : Fin 4 => sideOf P d ∈ bonds σ H).card := by
  rw [card_filter_eq_ncard_neighborSet hle P]
  exact hev P

theorem even_sides_of_evenDegrees {σ : Config n} {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (hev : EvenDegrees H) (P : Plaq n) :
    Even ((if sideL P ∈ bonds σ H then 1 else 0) + (if sideU P ∈ bonds σ H then 1 else 0)
        + (if sideR P ∈ bonds σ H then 1 else 0)
        + (if sideD P ∈ bonds σ H then 1 else 0)) := by
  have h := even_card_sides_of_evenDegrees hle hev P
  rwa [Finset.card_filter, Fin.sum_univ_four] at h

/-- **THE TELESCOPING IDENTITY, WITHOUT THE CIRCUIT.** -/
theorem sides_ud_eq_lr_of_evenDegrees {σ : Config n} {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (hev : EvenDegrees H) (P : Plaq n) :
    ((if sideD P ∈ bonds σ H then 1 else 0) + (if sideU P ∈ bonds σ H then 1 else 0)) % 2 =
      ((if sideL P ∈ bonds σ H then 1 else 0) + (if sideR P ∈ bonds σ H then 1 else 0)) % 2 := by
  obtain ⟨k, hk⟩ := even_sides_of_evenDegrees hle hev P
  omega

/-! ## 2. The telescope along a row, and the induction up the rows -/

theorem partial_row_of_evenDegrees {σ : Config n} (hσ : PlusBoundary σ)
    {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ) (hev : EvenDegrees H) {j : ℕ}
    (hj : j + 1 < n) :
    ∀ a, a + 1 < n →
      (cntD σ H j hj a + cntU σ H j hj a) % 2 =
        (if sideL (rowP j hj a) ∈ bonds σ H then 1 else 0) % 2 := by
  intro a
  induction a with
  | zero =>
    intro _
    have h0 : sideL (rowP j hj 0) ∉ bonds σ H :=
      sideL_notMem_bonds hσ H (by simp only [rowP]; omega)
    simp [cntD, cntU, h0]
  | succ a ih =>
    intro ha
    have hIH := ih (by omega)
    have hlr := sides_ud_eq_lr_of_evenDegrees hle hev (rowP j hj a)
    have hR : sideL (rowP j hj (a + 1)) = sideR (rowP j hj a) := by
      rw [← rightP_rowP hj (by omega), sideL_rightP _ (by rw [rowP_i hj (by omega)]; omega)]
    rw [cntD_succ, cntU_succ, hR]
    omega

theorem full_row_of_evenDegrees {σ : Config n} (hσ : PlusBoundary σ)
    {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ) (hev : EvenDegrees H) {j : ℕ}
    (hj : j + 1 < n) :
    (cntD σ H j hj (n - 1) + cntU σ H j hj (n - 1)) % 2 = 0 := by
  have hsplit : n - 1 = (n - 2) + 1 := by omega
  have hprev := partial_row_of_evenDegrees hσ hle hev hj (n - 2) (by omega)
  have hlr := sides_ud_eq_lr_of_evenDegrees hle hev (rowP j hj (n - 2))
  have hend : sideR (rowP j hj (n - 2)) ∉ bonds σ H :=
    sideR_notMem_bonds hσ H (by simp only [rowP]; omega)
  simp only [hend, if_false] at hlr
  rw [hsplit, cntD_succ, cntU_succ]
  omega

/-- **EVERY HORIZONTAL LINE MEETS AN EVEN-DEGREE SUBGRAPH OF THE DUAL AN EVEN NUMBER OF TIMES.** -/
theorem even_row_of_evenDegrees {σ : Config n} (hσ : PlusBoundary σ)
    {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ) (hev : EvenDegrees H) :
    ∀ j, (hj : j + 1 < n) → cntD σ H j hj (n - 1) % 2 = 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    have hz : ∀ k, sideD (rowP 0 hj k) ∉ bonds σ H := fun k =>
      sideD_notMem_bonds hσ H rfl
    simp [cntD, hz]
  | succ j ih =>
    intro hj
    have hj0 : j + 1 < n := by omega
    have hrow := full_row_of_evenDegrees hσ hle hev hj0
    have hswap := cntU_eq_cntD σ H hj0 (by omega) (n - 1)
    have hIH := ih hj0
    rw [hswap] at hrow
    omega

theorem even_row_top_of_evenDegrees {σ : Config n} (hσ : PlusBoundary σ)
    {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ) (hev : EvenDegrees H) {j : ℕ}
    (hj : j + 1 < n) : cntU σ H j hj (n - 1) % 2 = 0 := by
  have hrow := full_row_of_evenDegrees hσ hle hev hj
  have hIH := even_row_of_evenDegrees hσ hle hev j hj
  omega

/-! ## 3. Nothing is lost, and something is gained -/

/-- The original, recovered: a cycle graph has even degrees. -/
theorem even_row_isCycleGraph {σ : Config n} (hσ : PlusBoundary σ) {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) :
    ∀ j, (hj : j + 1 < n) → cntD σ H j hj (n - 1) % 2 = 0 :=
  even_row_of_evenDegrees hσ hle hcyc.evenDegrees

/-- **AND THE WHOLE CONTOUR, NOT MERELY ONE CIRCUIT OF IT.** At a `+` boundary the dual graph
itself has even degrees, so the crossing parity is available **before** the contour is cut up and
independently of how it is cut up. -/
theorem even_row_dualGraph {σ : Config n} (hσ : PlusBoundary σ) :
    ∀ j, (hj : j + 1 < n) → cntD σ (dualGraph σ) j hj (n - 1) % 2 = 0 :=
  even_row_of_evenDegrees hσ le_rfl (evenDegrees_dualGraph hσ)

theorem even_row_top_dualGraph {σ : Config n} (hσ : PlusBoundary σ) {j : ℕ} (hj : j + 1 < n) :
    cntU σ (dualGraph σ) j hj (n - 1) % 2 = 0 :=
  even_row_top_of_evenDegrees hσ le_rfl (evenDegrees_dualGraph hσ) hj

end EvenRowParity
