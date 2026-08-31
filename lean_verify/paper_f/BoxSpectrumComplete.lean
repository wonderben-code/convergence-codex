import BoxAdjBasis
import SignlessTorusComplete

/-!
# The `d`-dimensional box's adjacency spectrum, complete — and its spectral radius

`BoxAdjSpectrum` exhibited `n^d` eigenvectors of `(boxGraph d n).adjMatrix ℝ`; `BoxAdjBasis` proved
they are a basis and closed on one sentence — *"it does not say the spectrum is exactly the
`boxEig`s… that step needs `SignlessTorusComplete.eigenvalue_iff_of_basis`, which is stated over
`ℂ`"*. That lemma is now stated over an arbitrary field, so the step is available.

> **`eigenvalue_iff`** — for every dimension `d` and every side length `n ≥ 1`, a real number `μ`
> is an eigenvalue of `(boxGraph d n).adjMatrix ℝ` **iff** `μ = ∑ᵢ 2·cos(kᵢπ/(n+1))` for some
> frequency vector with each `kᵢ` in `1 … n`. **There are no others.**
>
> **`abs_boxEig_le`** and **`abs_le_of_eigenvalue`** — hence every eigenvalue satisfies
> `|μ| ≤ 2d·cos(π/(n+1))`, and **`boxEig_top`** exhibits `2d·cos(π/(n+1))` as one of them, so that
> bound is **attained**.
>
> **`abs_lt_two_mul_dim`** — and therefore, in every dimension `d ≥ 1` and at every side length,
> **every eigenvalue satisfies `|μ| < 2d` strictly**.

## What the radius bound says that a degree bound does not

`BoxDegree.boxGraph_degree_le` bounds the box's degree by `2d`, and a degree bound is the standard
route to `‖A‖ ≤ 2d`. **This is strictly better and it is sharp**: the spectral radius is *exactly*
`2d·cos(π/(n+1))` — attained, by `boxEig_top` — and `cos_base_lt_one` turns that into the strict
`|μ| < 2d`. The gap is the box's boundary, which is the same feature that keeps
`UNLOCK_WATCHLIST`'s box item shut.

## What this is NOT

**It is the ADJACENCY matrix and not `GraphLaplacian.massive`.** The estate's operator is
`D − A + m²` with the **true** degree, `PathDegreeBoundary.pathGraph_degree` shows that degree is
`1` at a path's ends and `2` inside, so `D` is not a scalar and this spectrum is not that one.
**`UNLOCK_WATCHLIST`'s *a BOX is not a circulant* item does not move**, for the reason it has given
throughout: it was never blocked on `A`.

**No limit is taken.** `2d·cos(π/(n+1)) → 2d` is arithmetic about the bound and is **not stated or
proved here**, and as of 31 Aug 2026 no cost is offered for it (`ERRATUM 194`, `ERRATUM 246`).

**No multiplicity.** Which frequency vectors share an eigenvalue is exactly the question
`TorusNonReflectionCollision` answers negatively on the torus, and nothing here counts a fibre.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BoxSpectrumComplete

open Finset Matrix SimpleGraph BoxGraph BoxAdjSpectrum BoxAdjBasis

variable {d n : ℕ}

/-! ## 1. Completeness -/

/-- **THE BOX'S ADJACENCY SPECTRUM, EXACTLY.**

**The name is deliberately the one `SignlessTorusComplete.eigenvalue_iff` already carries**, and
the two are different theorems in different namespaces: that one is the **signless Laplacian** of
the **torus** over **`ℂ`**, this one the **adjacency matrix** of the **box** over **`ℝ`**. They
share a name because they are the same question about different objects, and both are three lines
off the same `eigenvalue_iff_of_basis` — which is why that lemma was generalised away from `ℂ`. -/
theorem eigenvalue_iff (d n : ℕ) [NeZero n] (μ : ℝ) :
    (∃ x : Site d n → ℝ, x ≠ 0 ∧ (boxGraph d n).adjMatrix ℝ *ᵥ x = μ • x)
      ↔ ∃ k : Site d n, boxEig d n (fun i => (k i).val + 1) = μ :=
  SignlessTorusComplete.eigenvalue_iff_of_basis _ (boxBasis d n)
    (fun k => boxEig d n fun i => (k i).val + 1)
    (fun k => by rw [boxBasis_apply]; exact adjMatrix_mulVec_siteVec n d k) μ

/-! ## 2. The spectral radius -/

/-- The angle of a frequency in `1 … n` lies in `[π/(n+1), nπ/(n+1)]`, so its cosine is squeezed
between `± cos(π/(n+1))`: below because cosine decreases, above by reflecting through `π/2`. -/
theorem abs_cos_le (n : ℕ) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    |Real.cos ((k : ℝ) * Real.pi / ((n : ℝ) + 1))| ≤ Real.cos (Real.pi / ((n : ℝ) + 1)) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  have hbase : Real.pi / ((n : ℝ) + 1) = (1 : ℝ) * Real.pi / ((n : ℝ) + 1) := by ring
  have hlow : Real.pi / ((n : ℝ) + 1) ≤ (k : ℝ) * Real.pi / ((n : ℝ) + 1) := by
    rw [hbase, div_le_div_iff_of_pos_right hn1]
    nlinarith [Real.pi_pos]
  have hhigh : (k : ℝ) * Real.pi / ((n : ℝ) + 1) ≤ Real.pi := by
    rw [div_le_iff₀ hn1]
    nlinarith [Real.pi_pos]
  have hpos : (0 : ℝ) ≤ Real.pi / ((n : ℝ) + 1) := by positivity
  have hupper : Real.cos ((k : ℝ) * Real.pi / ((n : ℝ) + 1))
      ≤ Real.cos (Real.pi / ((n : ℝ) + 1)) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hpos hhigh hlow
  have hrefl : -Real.cos ((k : ℝ) * Real.pi / ((n : ℝ) + 1))
      ≤ Real.cos (Real.pi / ((n : ℝ) + 1)) := by
    have hmirror : Real.cos (Real.pi - (k : ℝ) * Real.pi / ((n : ℝ) + 1))
        = -Real.cos ((k : ℝ) * Real.pi / ((n : ℝ) + 1)) := Real.cos_pi_sub _
    rw [← hmirror]
    refine Real.cos_le_cos_of_nonneg_of_le_pi hpos ?_ ?_
    · have hnn : (0 : ℝ) ≤ (k : ℝ) * Real.pi / ((n : ℝ) + 1) := by positivity
      linarith
    · rw [le_sub_iff_add_le]
      have hjoin : Real.pi / ((n : ℝ) + 1) + (k : ℝ) * Real.pi / ((n : ℝ) + 1)
          = ((1 + (k : ℝ)) * Real.pi) / ((n : ℝ) + 1) := by field_simp
      rw [hjoin, div_le_iff₀ hn1]
      nlinarith [Real.pi_pos]
  exact abs_le.2 ⟨by linarith, hupper⟩

/-- **EVERY EIGENVALUE IS AT MOST `2d·cos(π/(n+1))` IN ABSOLUTE VALUE.** -/
theorem abs_boxEig_le (d n : ℕ) {k : Fin d → ℕ} (hk : ∀ i, 1 ≤ k i) (hkn : ∀ i, k i ≤ n) :
    |boxEig d n k| ≤ 2 * d * Real.cos (Real.pi / ((n : ℝ) + 1)) := by
  have hstep : ∀ i : Fin d,
      |2 * Real.cos ((k i : ℝ) * Real.pi / ((n : ℝ) + 1))|
        ≤ 2 * Real.cos (Real.pi / ((n : ℝ) + 1)) := by
    intro i
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (abs_cos_le n (hk i) (hkn i)) (by norm_num)
  calc |boxEig d n k| ≤ ∑ i : Fin d, |2 * Real.cos ((k i : ℝ) * Real.pi / ((n : ℝ) + 1))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, 2 * Real.cos (Real.pi / ((n : ℝ) + 1)) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = 2 * d * Real.cos (Real.pi / ((n : ℝ) + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **AND THE BOUND IS ATTAINED**, at the frequency `1` on every axis. -/
theorem boxEig_top (d n : ℕ) :
    boxEig d n (fun _ => 1) = 2 * d * Real.cos (Real.pi / ((n : ℝ) + 1)) := by
  rw [boxEig]
  simp only [Nat.cast_one, one_mul]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **SO THE SPECTRAL RADIUS IS AT MOST `2d·cos(π/(n+1))`.** -/
theorem abs_le_of_eigenvalue (d n : ℕ) [NeZero n] {μ : ℝ}
    (h : ∃ x : Site d n → ℝ, x ≠ 0 ∧ (boxGraph d n).adjMatrix ℝ *ᵥ x = μ • x) :
    |μ| ≤ 2 * d * Real.cos (Real.pi / ((n : ℝ) + 1)) := by
  obtain ⟨k, rfl⟩ := (eigenvalue_iff d n μ).1 h
  exact abs_boxEig_le d n (fun i => Nat.le_add_left 1 _) fun i => (k i).isLt

/-! ## 3. And that is strictly inside the degree bound -/

/-- `cos(π/(n+1)) < 1`, because the angle is strictly between `0` and `π`. -/
theorem cos_base_lt_one (n : ℕ) : Real.cos (Real.pi / ((n : ℝ) + 1)) < 1 := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpos : (0 : ℝ) < Real.pi / ((n : ℝ) + 1) := by positivity
  have hle : Real.pi / ((n : ℝ) + 1) ≤ Real.pi := by
    rw [div_le_iff₀ hn1]
    nlinarith [Real.pi_pos]
  have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hle hpos
  simpa using this

/-- **THE BOX'S ADJACENCY SPECTRAL RADIUS IS STRICTLY BELOW ITS DEGREE BOUND**, in every dimension
`d ≥ 1` and at every side length. `BoxDegree.boxGraph_degree_le` gives `2d` and a degree bound can
give no better; the gap is the box's boundary. -/
theorem abs_lt_two_mul_dim (d n : ℕ) [NeZero n] (hd : 0 < d) {μ : ℝ}
    (h : ∃ x : Site d n → ℝ, x ≠ 0 ∧ (boxGraph d n).adjMatrix ℝ *ᵥ x = μ • x) :
    |μ| < 2 * d := by
  have hbound := abs_le_of_eigenvalue d n h
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  nlinarith [cos_base_lt_one n]

end BoxSpectrumComplete
