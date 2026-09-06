import RowParityCorrection

/-!
# Locating the correction: which rows a path's ends fall in, and the parity of the rest

`RowParityCorrection` computed the crossing-parity of a horizontal line for **any** subgraph of the
dual — it is the parity of the number of odd-degree plaquettes below the line — and fenced what was
left: *the correction is counted, not located; nothing says how many odd plaquettes lie in a given
row, nor which row the two ends of a path fall in.*

**This locates it, and the result is the open-path statement the interior chain has for circuits.**

## What is proved

**`even_degCnt_of_row_ne`** — **a row containing neither of the two exceptional plaquettes
contributes nothing.** A plaquette of row `j` has second coordinate `j` (`RowParity.rowP_j`), so if
neither exceptional plaquette has second coordinate `j` then every term of `degCnt` is even and the
sum is.

**`even_degBelow_of_no_row_below`** — **hence a line with no exceptional plaquette anywhere below it
sees an even correction**, and **`even_cntD_of_no_endpoint_below`** — **so it meets the subgraph an
even number of times**, with no hypothesis on the subgraph beyond the two exceptional plaquettes.

**`odd_degCnt_of_row_eq`** — **and a row containing exactly one of them contributes exactly one.**
The row's enumeration `rowP j hj k` for `k < n − 1` runs over the row's plaquettes **injectively**
(`min k (n − 2) = k` there), so the exceptional plaquette appears once, at `k = P.i`, and every
other term is even.

**`odd_cntD_of_one_endpoint_below`** — **so a line with an odd correction below it meets the
subgraph an ODD number of times.** It takes **no exceptional plaquettes at all** — only that
`degBelow` is odd, which is what `odd_degCnt_of_row_eq` supplies; the binders were removed after
the linter reported them unused, which is a small generalisation. For a path graph, whose two
exceptional plaquettes are its endpoints (`PathGraphDegree.exists_endpoints_of_isPathGraph`),
the two theorems together read: **every horizontal line strictly between the two ends is crossed
oddly, and every line below both is crossed evenly** — the open-path analogue of
`RowParity.even_row`, which says a **circuit** crosses every line evenly.

## What is NOT here

**NO RAY, AND NO COVERING.** Residue (b) of `S3b-ii` is *the open-path analogue of the ray
argument*, and the ray argument is `RayWalk`'s: it takes a **site**, runs a ray from it, and
concludes the site is **down**. What is proved here is about **horizontal lines and rows**, and
**nothing connects a line's crossing parity to a site's spin or to a cluster**. That connection is
the whole of `RayWalk`, and **it is not touched**. **Residue (b) is not closed and no part of it is
claimed.** Not attempted, no cost claimed (`ERRATUM 246`).

⚠ **A RAY APPEARS THE SAME DAY AND THIS PARAGRAPH IS KEPT AS WRITTEN** (`ERRATUM 94`, annotated
in the unit that superseded it, per `ERRATUM 471`). `RayPieceParity.crossings_leftRay_eq_cntD`
identifies the leftward ray's crossings of a piece with that piece's row count, so this file's
two parities are **ray** parities: the ray from a site crosses a piece evenly with no
exceptional plaquette below it and oddly with an odd correction below it. **The heading is what
moves; the body stands** — nothing here reaches a site's **spin** or a **cluster**, which needs
the crossings of a decomposition to sum to the crossings of the whole contour, and neither that
nor a decomposition of the contour is supplied. **Residue (b) is still not closed.**

**THE TWO EXCEPTIONAL PLAQUETTES ARE NOT ASSUMED DISTINCT, AND NOT ASSUMED TO BE ENDPOINTS.**
Everything here takes them as **given** — two plaquettes outside which the degree is even — which
is exactly what `exists_endpoints_of_isPathGraph` returns and **all** that is used. **No theorem
here mentions `IsPathGraph`**, and the path case is an instantiation a caller makes.

**NOTHING SAYS A PATH'S ENDS ARE IN DIFFERENT ROWS.** If both are in one row the correction is even
there and every line is crossed evenly, and **that case is not excluded** — it is simply a path
whose ends are level.

**W3 DOES NOT MOVE.** A parity is located; no ray is built, no site is reached, no cluster is
covered.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `H ≤ dualGraph σ` and `PlusBoundary σ`
from the row theorems, exactly as `RowParityCorrection` has them, plus the two exceptional
plaquettes. **No degree hypothesis on `H`**, no cycle, no path.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace RowParityLocate

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds CircuitSides RowParity
open RowParityCorrection SimpleGraph

variable {n : ℕ}

/-! ## 1. A row with neither exceptional plaquette contributes nothing -/

/-- **A ROW CONTAINING NEITHER EXCEPTIONAL PLAQUETTE CONTRIBUTES AN EVEN CORRECTION.** -/
theorem even_degCnt_of_row_ne {H : SimpleGraph (Plaq n)} {A B : Plaq n}
    (hAB : ∀ P : Plaq n, P ≠ A → P ≠ B → Even ((H.neighborSet P).ncard))
    {j : ℕ} (hj : j + 1 < n) (hA : A.j ≠ j) (hB : B.j ≠ j) (a : ℕ) :
    Even (degCnt H j hj a) := by
  rw [degCnt, even_iff_two_dvd]
  refine Finset.dvd_sum fun k _ => Even.two_dvd ?_
  refine hAB _ (fun hc => hA ?_) (fun hc => hB ?_)
  · rw [← hc, rowP_j]
  · rw [← hc, rowP_j]

theorem even_degBelow_of_no_row_below {H : SimpleGraph (Plaq n)} {A B : Plaq n}
    (hAB : ∀ P : Plaq n, P ≠ A → P ≠ B → Even ((H.neighborSet P).ncard))
    {j : ℕ} (hA : ¬ A.j < j) (hB : ¬ B.j < j) : Even (degBelow H j) := by
  rw [degBelow, even_iff_two_dvd]
  refine Finset.dvd_sum fun i hi => Even.two_dvd ?_
  rw [Finset.mem_range] at hi
  by_cases h : i + 1 < n
  · rw [dif_pos h]
    exact even_degCnt_of_row_ne hAB h (fun hc => hA (hc ▸ hi)) (fun hc => hB (hc ▸ hi)) _
  · rw [dif_neg h]
    exact ⟨0, rfl⟩

/-- **SO A LINE WITH NO EXCEPTIONAL PLAQUETTE BELOW IT MEETS THE SUBGRAPH EVENLY.** -/
theorem even_cntD_of_no_endpoint_below {σ : Config n} (hσ : PlusBoundary σ)
    {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ) {A B : Plaq n}
    (hAB : ∀ P : Plaq n, P ≠ A → P ≠ B → Even ((H.neighborSet P).ncard))
    {j : ℕ} (hj : j + 1 < n) (hA : ¬ A.j < j) (hB : ¬ B.j < j) :
    cntD σ H j hj (n - 1) % 2 = 0 := by
  have hrow := even_row_parity hσ hle j hj
  obtain ⟨k, hk⟩ := even_degBelow_of_no_row_below hAB hA hB
  omega

/-! ## 2. A row with exactly one of them contributes exactly one -/

/-- **A ROW CONTAINING EXACTLY ONE EXCEPTIONAL PLAQUETTE CONTRIBUTES AN ODD CORRECTION.** The
enumeration `rowP j hj k` runs over the row injectively for `k < n − 1`, so the exceptional
plaquette appears exactly once, at `k = A.i`. -/
theorem odd_degCnt_of_row_eq {H : SimpleGraph (Plaq n)} {A B : Plaq n}
    (hAB : ∀ P : Plaq n, P ≠ A → P ≠ B → Even ((H.neighborSet P).ncard))
    {j : ℕ} (hj : j + 1 < n) (hA : A.j = j) (hB : B.j ≠ j)
    (hodd : Odd ((H.neighborSet A).ncard)) :
    Odd (degCnt H j hj (n - 1)) := by
  have hmem : A.i ∈ Finset.range (n - 1) := by
    rw [Finset.mem_range]
    have := A.hi
    omega
  have hrow : rowP j hj A.i = A := by
    have hle : A.i ≤ n - 2 := by have := A.hi; omega
    simp only [rowP, min_eq_left hle]
    cases A with
    | mk i j' hi hj' => simp_all
  rw [degCnt, ← Finset.add_sum_erase _ _ hmem, hrow]
  refine hodd.add_even (even_iff_two_dvd.mpr (Finset.dvd_sum fun k hk => Even.two_dvd ?_))
  rw [Finset.mem_erase, Finset.mem_range] at hk
  refine hAB _ (fun hc => hk.1 ?_) (fun hc => hB ?_)
  · have hle : k ≤ n - 2 := by omega
    have := congrArg Plaq.i hc
    simp only [rowP, min_eq_left hle] at this
    exact this
  · rw [← hc, rowP_j]

/-- **SO A LINE WITH EXACTLY ONE OF THEM BELOW IT MEETS THE SUBGRAPH AN ODD NUMBER OF TIMES.** For
a path graph this says: **every horizontal line strictly between the two ends is crossed oddly.**
The open-path analogue of `RowParity.even_row`, which says a circuit crosses every line evenly. -/
theorem odd_cntD_of_one_endpoint_below {σ : Config n} (hσ : PlusBoundary σ)
    {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ)
    {j : ℕ} (hj : j + 1 < n) (hodd : Odd (degBelow H j)) :
    cntD σ H j hj (n - 1) % 2 = 1 := by
  have hrow := even_row_parity hσ hle j hj
  obtain ⟨k, hk⟩ := hodd
  omega

end RowParityLocate
