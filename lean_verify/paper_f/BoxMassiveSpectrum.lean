import BoxLapBasis
import BoxSpectrumComplete
import GraphLaplacian

/-!
# `−Δ + m²` on the `d`-dimensional box, diagonalised completely

`UNLOCK_WATCHLIST`'s *a BOX is not a circulant* item asks one question: does the eigenvalue route
that works on the cycle reach **this estate's box graphs**? Twenty status lines have been written
against it. Everything is now in place except one line of arithmetic, and this file is that line.

> **`massive_mulVec_siteLapVec`** — `massive (boxGraph d n) m` sends each half-step cosine mode to
> `(∑ᵢ (2 − 2cos(kᵢπ/n)) + m²)` times itself. The mass shifts every eigenvalue and moves no
> eigenvector.
>
> **`massive_eigenvalue_iff`** — so a real `μ` is an eigenvalue of `massive (boxGraph d n) m`
> **iff** `μ = ∑ᵢ (2 − 2cos(kᵢπ/n)) + m²` for a frequency vector with each `kᵢ` in `0 … n−1`.
> **There are no others**, in any dimension, at any side length, for any mass.
>
> **`massive_eigenvalue_le`** and **`massive_eigenvalue_top`** — the largest eigenvalue is
> **exactly** `d·(2 + 2cos(π/n)) + m²`, attained at the frequency `n−1` on every axis; and
> **`lt_degree_const`** proves that is strictly below `LaplacianDegreeBound`'s `4d + m²` whenever
> `d ≥ 1`.

## The route is not the one the item named, and the difference is the interesting part

The item says of the box that *"the one-dimensional path's **Dirichlet** Laplacian has sine
eigenvectors rather than exponential ones"*. **`BoxGraph.boxGraph` has a FREE boundary, not a
Dirichlet one** — an end site genuinely has one neighbour rather than two — and the free-boundary
problem's modes are **cosines sampled half a step off the grid**, not sines. That is why
`PathAdjSpectrum`'s sine vectors diagonalise the **adjacency** matrix and not `D − A`, and why
sixteen status lines fenced on exactly that gap. The item's *"no character is an eigenvector"*
stays true throughout: a half-step cosine is not a character.

## What this does NOT do

**No multiplicity.** Which frequency vectors share an eigenvalue is not asked. `d = 1` is settled —
the eigenvalues are injective there (`BoxLapBasis.lapEigenvalue_injective`) — and at `d ≥ 2` they
demonstrably repeat, `(1,2)` and `(2,1)` giving the same sum. **No count of any fibre is proved**
and as of 31 Aug 2026 none is costed (`ERRATUM 194`, `ERRATUM 246`).

**No Loewner statement, so `BoxMassiveBound`'s constant does not move.** The exact maximum here is
`2d + 2d·cos(π/n) + m²`, **below** that file's bound `2d + 2d·cos(π/(n+1)) + m²`; turning an
eigenvalue maximum into `massive ≼ c·1` needs these modes shown **orthogonal**, which
`BoxModeOrthogonal` does for the adjacency modes and **nobody has done for these**. Not attempted,
not costed.

**No continuum limit.** `d·(2 + 2cos(π/n)) → 4d` is arithmetic about the answer and is not stated.

**Nothing downstream is rewired.** `SqrtGreenBound`, `LatticeWitnessBound` and the rest keep their
constants.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BoxMassiveSpectrum

open Finset Matrix SimpleGraph BoxGraph PathLapSpectrum BoxLapSpectrum BoxLapBasis GraphLaplacian

variable {d m : ℕ}

/-! ## 1. The mass shifts the eigenvalue and moves no eigenvector -/

theorem massive_mulVec_siteLapVec (d m : ℕ) (mass : ℝ) (k : Site d (m + 1)) :
    massive (boxGraph d (m + 1)) mass *ᵥ siteLapVec d (m + 1) k
      = (boxLapEig d (m + 1) (fun i => (k i).val) + mass ^ 2) • siteLapVec d (m + 1) k := by
  classical
  rw [massive, Matrix.add_mulVec, lapMatrix_mulVec_siteLapVec]
  funext p
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal]
  ring

/-! ## 2. The complete spectrum -/

/-- **`−Δ + m²` ON THE BOX, EXACTLY.**

**The name is deliberately the one `MassiveTorusSpectrum.massive_eigenvalue_iff` already carries**,
and the two are the same statement about different objects: that one is `massive` on the **torus**,
stated over **`ℂ`** through `MatrixLoewner.cx`, with the **characters** as its basis; this one is
`massive` on the **box**, over **`ℝ`**, with half-step cosines. **They are the two halves of the
same question** — a periodic lattice and a lattice with boundary — and both are three lines off the
same `SignlessTorusComplete.eigenvalue_iff_of_basis`, which is why that lemma was generalised away
from `ℂ` (`newnames_scan`, 31 Aug 2026). -/
theorem massive_eigenvalue_iff (d m : ℕ) (mass μ : ℝ) :
    (∃ x : Site d (m + 1) → ℝ, x ≠ 0 ∧ massive (boxGraph d (m + 1)) mass *ᵥ x = μ • x)
      ↔ ∃ k : Site d (m + 1), boxLapEig d (m + 1) (fun i => (k i).val) + mass ^ 2 = μ :=
  SignlessTorusComplete.eigenvalue_iff_of_basis _ (boxLapBasis d m)
    (fun k => boxLapEig d (m + 1) (fun i => (k i).val) + mass ^ 2)
    (fun k => by rw [boxLapBasis_apply]; exact massive_mulVec_siteLapVec d m mass k) μ

/-! ## 3. The largest eigenvalue, exactly -/

/-- Each axis contributes at most `2 + 2cos(π/n)`, because `kπ/n ≤ π − π/n` and cosine decreases. -/
theorem lapEig_axis_le (m k : ℕ) (hk : k ≤ m) :
    2 - 2 * Real.cos (2 * half (m + 1) k) ≤ 2 + 2 * Real.cos (Real.pi / ((m : ℝ) + 1)) := by
  rw [two_half]
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hkm : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hmirror : Real.cos (Real.pi - (k : ℝ) * Real.pi / ((m : ℝ) + 1))
      = -Real.cos ((k : ℝ) * Real.pi / ((m : ℝ) + 1)) := Real.cos_pi_sub _
  have hbase : (0 : ℝ) ≤ Real.pi / ((m : ℝ) + 1) := by positivity
  have hle : Real.pi / ((m : ℝ) + 1) ≤ Real.pi - (k : ℝ) * Real.pi / ((m : ℝ) + 1) := by
    rw [le_sub_iff_add_le]
    have hjoin : Real.pi / ((m : ℝ) + 1) + (k : ℝ) * Real.pi / ((m : ℝ) + 1)
        = ((1 + (k : ℝ)) * Real.pi) / ((m : ℝ) + 1) := by field_simp
    rw [hjoin, div_le_iff₀ hm]
    nlinarith [Real.pi_pos]
  have hpi : Real.pi - (k : ℝ) * Real.pi / ((m : ℝ) + 1) ≤ Real.pi := by
    have : (0 : ℝ) ≤ (k : ℝ) * Real.pi / ((m : ℝ) + 1) := by positivity
    linarith
  have := Real.cos_le_cos_of_nonneg_of_le_pi hbase hpi hle
  rw [hmirror] at this
  linarith

/-- **EVERY EIGENVALUE IS AT MOST `d·(2 + 2cos(π/n)) + m²`.** -/
theorem massive_eigenvalue_le (d m : ℕ) (mass μ : ℝ)
    (h : ∃ x : Site d (m + 1) → ℝ, x ≠ 0 ∧ massive (boxGraph d (m + 1)) mass *ᵥ x = μ • x) :
    μ ≤ (d : ℝ) * (2 + 2 * Real.cos (Real.pi / ((m : ℝ) + 1))) + mass ^ 2 := by
  obtain ⟨k, rfl⟩ := (massive_eigenvalue_iff d m mass μ).1 h
  have hsum : boxLapEig d (m + 1) (fun i => (k i).val)
      ≤ ∑ _i : Fin d, (2 + 2 * Real.cos (Real.pi / ((m : ℝ) + 1))) := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact lapEig_axis_le m (k i).val (Nat.lt_succ_iff.1 (k i).isLt)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  linarith

/-- **AND IT IS ATTAINED**, at the frequency `n − 1` on every axis. -/
theorem massive_eigenvalue_top (d m : ℕ) (mass : ℝ) :
    ∃ x : Site d (m + 1) → ℝ, x ≠ 0 ∧ massive (boxGraph d (m + 1)) mass *ᵥ x
      = ((d : ℝ) * (2 + 2 * Real.cos (Real.pi / ((m : ℝ) + 1))) + mass ^ 2) • x := by
  refine (massive_eigenvalue_iff d m mass _).2
    ⟨fun _ => (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)), ?_⟩
  have hax : ∀ _i : Fin d, 2 - 2 * Real.cos (2 * half (m + 1) m)
      = 2 + 2 * Real.cos (Real.pi / ((m : ℝ) + 1)) := by
    intro _
    rw [two_half]
    have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
    have hmirror : (m : ℝ) * Real.pi / ((m : ℝ) + 1) = Real.pi - Real.pi / ((m : ℝ) + 1) := by
      field_simp
      ring
    rw [hmirror, Real.cos_pi_sub]
    ring
  rw [boxLapEig]
  rw [Finset.sum_congr rfl fun i _ => hax i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- **AND THE EXACT MAXIMUM IS STRICTLY BELOW THE DEGREE BOUND `4d + m²`** at every `d ≥ 1` and
every side length — proved, not asserted. -/
theorem lt_degree_const (d m : ℕ) (hd : 0 < d) (mass : ℝ) :
    (d : ℝ) * (2 + 2 * Real.cos (Real.pi / ((m : ℝ) + 1))) + mass ^ 2 < 4 * (d : ℝ) + mass ^ 2 := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcos := BoxSpectrumComplete.cos_base_lt_one m
  nlinarith

end BoxMassiveSpectrum
