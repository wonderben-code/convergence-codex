import TracePathSum
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The two-dimensional Ising transfer matrix, and its partition function as a trace

`WALLS.md` §W4.0 lists three things the mass-gap wall needs, and the first is:

> *"**The `2ⁿ × 2ⁿ` transfer matrix for the two-dimensional model**, as a `Matrix` over `ℝ` indexed
> by spin columns, with its entries the row-to-row Boltzmann weights. A build, not research: the
> one-dimensional case is now done and shows the shape."*

This is that build, and — because `TracePathSum.sum_cyc_eq_trace` landed first — it comes with the
identity that makes it a transfer matrix rather than an array of numbers.

> **`Col n`** — a column of `n+1` spins, `Fin (n+1) → Bool`. There are `2ⁿ⁺¹` of them, and the
> matrix is indexed by them. The width carries the `+1` because the column's own bonds wrap.

>
>
> **`transfer2 β n σ τ = exp (β (intra σ + inter σ τ))`** — the row-to-row Boltzmann weight:
> `intra` is the column's own vertical bonds, `inter` the horizontal bonds to the next column.
>
> **`partition2_eq_trace`** — **the partition function of the periodic `(n+1) × (M+1)` lattice is
> `tr T^{M+1}`.** Every vertical bond is counted once, by its own column's `intra`; every
> horizontal bond once, by `inter`; and then the sum over configurations is the cyclic
> sum-over-paths identity.
>
> **`transfer2_zero_apply`** — and at width `1` (that is, `Col 0`) this is **not** the chain's
> transfer matrix, but
> `e^β` times it. Checked rather than assumed, because the names invite the inference.

## Conventions, stated rather than left to be inferred

**The lattice is a torus.** `intra` sums `σ i · σ (i+1)` with `i+1` wrapping in `Fin (n+1)`, and
the column index wraps in `Fin (M+1)`, so both directions are periodic. That is what makes the trace
identity available at all.

**The sign is absorbed.** The weight is `exp (β · Σ s s')`, i.e. `exp (−β H)` for the ferromagnetic
`H = −Σ s s'`, with `β > 0` the low-temperature end. No `−` appears below because it is already in
the convention.

**`spin` is the ±1 encoding**, `true ↦ 1`, `false ↦ −1`.

## What this does NOT do

**It does not close W4 and it is not a mass gap.** The wall's item 2 — separating the top eigenvalue
of this matrix — is untouched, and it is the hard one: Perron–Frobenius is absent from Mathlib
(probed 2026-08-11, `PerronFrobenius`/`perronFrobenius`: zero files), and the hand-rolled `2 × 2`
argument in `IsingTransferMatrix` does not generalise. **Having the operator is not having its
spectrum.**

⚠ **THE CLAIM STANDS AND THE PROBE IS THE WRONG ONE — `ERRATUM 234`, third instance, kept per
`ERRATUM 94`.** `PerronFrobenius`/`perronFrobenius` really are zero files, and no Perron–Frobenius
**conclusion** is in Mathlib. But that probe searches for the theorem's **eponym**, and Mathlib
does not name it after anybody: it names the **hypotheses**. `Matrix.IsPrimitive` and
`Matrix.IsIrreducible` exist, seventeen declarations between them, every one a definition or an
accessor. **And `Matrix.IsPrimitive` is field-for-field the hypothesis triple this estate's
`PerronPrimitive` hand-wrote** — `nonneg` and `exists_pos_pow`. So the bad probe did not hide a
theorem; it hid the fact that the estate and the library had been describing the same object under
different names for a fortnight. `PerronMathlibPredicate` joins them.

⚠ **«ITEM 2 … IS UNTOUCHED» WAS TRUE ON 11 AUGUST AND IS FALSE SINCE 22 AUGUST. THE SENTENCE IS
KEPT PER `ERRATUM 94`.** Item 2 is **closed**, by nine files ending at
`PerronGap.transferSym_gap`: `|λ| < λ_top` for every eigenvalue of `transferSym` off the argmax,
with `PerronVector.exists_pos_top_eigenvector` and `PerronSimple.top_eigenspace_dim_one` as its
two halves. **The probe result above is NOT withdrawn**: general Perron–Frobenius is still absent
from Mathlib and is still proved nowhere here. What closed item 2 is narrower and is exactly what
this matrix needs — the **symmetric, strictly positive** case, which `transferSym` is in and
`transfer2` is not. And the note about the hand-rolled `2 × 2` argument stands as written: it did
not generalise; a different argument did.

**AND THE WALL DID NOT MOVE, WHICH IS WHY THIS PARAGRAPH IS A CORRECTION AND NOT A CLOSURE.** W4
now rests entirely on item 3, and item 3 rests on one sentence: the eigenvalue separation
**uniform in the width**. Everything the estate proves about this matrix is at one fixed `n`.

**No eigenvalue, gap, or free energy is computed here.** The matrix is `2ⁿ⁺¹ × 2ⁿ⁺¹`, and
nothing below
diagonalises it, estimates it, or takes any limit in `n`.
-/

namespace IsingTransfer2D

open Finset Real

/-- The `±1` encoding of a spin. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

theorem spin_sq (b : Bool) : spin b * spin b = 1 := by
  cases b <;> norm_num [spin]

/-- **A column of `n+1` spins.** The transfer matrix is indexed by these, and there are `2ⁿ⁺¹`.
The width is written `n+1` rather than `n` because the column's own bonds wrap — `i + 1` in `Fin n`
needs `n` non-zero — and a zero-width column has no content to lose. -/
abbrev Col (n : ℕ) : Type := Fin (n + 1) → Bool

/-- **AND THERE REALLY ARE `2ⁿ⁺¹` OF THEM.** `WALLS` §W4.0 item 1 asks for *"the `2ⁿ × 2ⁿ` transfer
matrix"*, and a file that says so in prose while indexing by an opaque type has not answered it.
This is the size claim, checked. -/
theorem card_Col (n : ℕ) : Fintype.card (Col n) = 2 ^ (n + 1) := by
  simp [Col]

variable {n : ℕ}

/-- **The column's own vertical bonds**, periodic in the column direction. -/
def intra (σ : Col n) : ℝ := ∑ i : Fin (n + 1), spin (σ i) * spin (σ (i + 1))

/-- **The horizontal bonds** between two adjacent columns. -/
def inter (σ τ : Col n) : ℝ := ∑ i : Fin (n + 1), spin (σ i) * spin (τ i)

/-- **THE TWO-DIMENSIONAL TRANSFER MATRIX**, indexed by the `2ⁿ⁺¹` columns. -/
noncomputable def transfer2 (β : ℝ) (n : ℕ) : Matrix (Col n) (Col n) ℝ :=
  fun σ τ => exp (β * (intra σ + inter σ τ))

/-- Every entry is strictly positive — the fact Perron–Frobenius would consume, recorded here
because it is the one structural property of this matrix that is immediate and because W4's item 2
is exactly the theorem that needs it. **Stating it is not proving item 2.** -/
theorem transfer2_pos (β : ℝ) (σ τ : Col n) : 0 < transfer2 β n σ τ := exp_pos _

/-! ## The energy of a full configuration, and the partition function -/

/-- The energy sum of a configuration of `M+1` columns: each column contributes its own vertical
bonds and its horizontal bonds to the next, and the column index wraps. **Every bond of the torus
appears exactly once** — vertical bonds through `intra`, horizontal through `inter`. -/
def energy (M : ℕ) (s : Fin (M + 1) → Col n) : ℝ :=
  ∑ j : Fin (M + 1), (intra (s j) + inter (s j) (s (j + 1)))

/-- **The partition function** of the periodic `(n+1) × (M+1)` lattice. -/
noncomputable def partition2 (β : ℝ) (n M : ℕ) : ℝ :=
  ∑ s : Fin (M + 1) → Col n, exp (β * energy M s)

/-- **THE PARTITION FUNCTION IS THE TRACE OF A POWER OF THE TRANSFER MATRIX.** The exponential of
the energy sum factorises over columns, each factor is a matrix entry by construction, and then
`TracePathSum.sum_cyc_eq_trace` does the rest.

This is what makes `transfer2` a *transfer matrix* rather than a `2ⁿ⁺¹ × 2ⁿ⁺¹` array of
numbers, and it
is the reason `WALLS` §W4.0 item 1 is worth building at all. -/
theorem partition2_eq_trace (β : ℝ) (n M : ℕ) :
    partition2 β n M = Matrix.trace (transfer2 β n ^ (M + 1)) := by
  have hfac : ∀ s : Fin (M + 1) → Col n,
      exp (β * energy M s) = ∏ j : Fin (M + 1), transfer2 β n (s j) (s (j + 1)) := by
    intro s
    simp only [energy, transfer2, Finset.mul_sum]
    exact Real.exp_sum _ _
  simp only [partition2]
  rw [Finset.sum_congr rfl fun s _ => hfac s]
  exact TracePathSum.sum_cyc_eq_trace (transfer2 β n) M

/-! ## Width one is not the chain, and the file says so with a theorem

The names invite the inference that `transfer2 β 0` — width one — is
`IsingTransferMatrix.transfer β`. It is not: at width one the vertical wrap makes the single site
bond with **itself**, contributing a constant `exp β` to every entry. That is the standard
artefact of periodic boundaries at width one, and it is checked here rather than left for a reader
to trip over. -/

theorem intra_zero (σ : Col 0) : intra σ = 1 := by
  simp [intra, spin_sq]

/-- **AT WIDTH ONE EVERY ENTRY CARRIES A SPURIOUS `e^β`.** So `transfer2 β 0` is `e^β` times the
chain's matrix, not the chain's matrix. -/
theorem transfer2_zero_apply (β : ℝ) (σ τ : Col 0) :
    transfer2 β 0 σ τ = exp β * exp (β * (spin (σ 0) * spin (τ 0))) := by
  simp only [transfer2]
  rw [← Real.exp_add]
  congr 1
  simp [intra_zero, inter]
  ring

end IsingTransfer2D
