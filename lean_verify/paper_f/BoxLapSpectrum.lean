import PathLapSpectrum
import BoxProdLapSpectrum
import GraphIsoLapSpectrum
import BoxGraphSuccIso

/-!
# The `d`-dimensional box's FREE-BOUNDARY Laplacian, diagonalised

`UNLOCK_WATCHLIST`'s *a BOX is not a circulant* item has said since it was written that *"a box has
a BOUNDARY and its degree is not constant … so no character is an eigenvector"*, and every unit in
this sequence has taken that to mean `D − A` was out of reach — which is why sixteen status lines
fenced with *"still the adjacency matrix"*. `PathLapSpectrum` broke that at `d = 1` with **half-step
cosines**, which are not characters; `BoxProdLapSpectrum` made Laplacian eigenvalues add across a
product **with the degrees included**; `GraphIsoLapSpectrum` made them survive a relabelling. This
file runs the three together.

> **`boxLapVec d n k p = ∏ᵢ cos((2·pᵢ+1)·kᵢπ/(2n))`** — one half-step cosine per axis.
>
> **`lapMatrix_mulVec_boxLapVec`** — for **every** dimension `d`, **every** side length `n ≥ 1` and
> **every** frequency vector `k : Fin d → ℕ`:
> `L_{boxGraph d n} · boxLapVec d n k = (∑ᵢ (2 − 2cos(kᵢπ/n))) · boxLapVec d n k`.
> **No hypotheses**, and with the **true** free-boundary degree at every site.
>
> **`boxLapVec_ne_zero`** — and with `kᵢ < n` on every axis the vector is nonzero, so these are
> eigen**values**.

## What this is and is not, precisely

**It is the operator this estate actually uses, minus the mass.** `GraphLaplacian.massive` is
`L + m²`, so every eigenvalue here shifts by `m²` and every eigenvector is unchanged — **but that
shift is not stated in this file** and no `massive` statement is made here.

**It is not a basis, so it is not the whole spectrum.** That the `n^d` vectors with `0 ≤ kᵢ < n` are
independent is **not proved here**. The `d = 1` eigenvalues `2 − 2cos(kπ/n)` are distinct on that
range, but in `d ≥ 2` the sums repeat — `(1,2)` and `(2,1)` again — so the cheap route is closed
exactly as it was for the adjacency matrix, and the replacement is `ProdVecIndependent`'s
product-of-bases argument plus an induction. **That product-of-bases induction is not attempted in
this file, and as of 31 Aug 2026 no cost is offered for it** (`ERRATUM 194`, `ERRATUM 246`).

**The item's own sentence is still true.** No character is an eigenvector of this operator, and
nothing here says otherwise; what is exhibited is a family of **non-characters**. The item is routed
around rather than refuted, and `STATUS (16)` records that distinction.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BoxLapSpectrum

open Finset Matrix SimpleGraph BoxGraph BoxGraphSuccIso PathLapSpectrum

variable {d m : ℕ}

/-! ## 1. The vector and the eigenvalue -/

/-- **ONE HALF-STEP COSINE PER AXIS**, multiplied. -/
noncomputable def boxLapVec (d n : ℕ) (k : Fin d → ℕ) (p : Site d n) : ℝ :=
  ∏ i, cosMode n (k i) (p i)

/-- **THE SUM OF THE PER-AXIS EIGENVALUES.** -/
noncomputable def boxLapEig (d n : ℕ) (k : Fin d → ℕ) : ℝ :=
  ∑ i, (2 - 2 * Real.cos (2 * half n (k i)))

/-- The eigenvalue with the angle spelled out: `2·half n k` is `kπ/n`. -/
theorem boxLapEig_eq (d m : ℕ) (k : Fin d → ℕ) :
    boxLapEig d (m + 1) k = ∑ i, (2 - 2 * Real.cos ((k i : ℝ) * Real.pi / ((m : ℝ) + 1))) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  rw [half]
  have h2 : (2 : ℝ) * ((m : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-! ## 2. Peeling one axis -/

theorem boxLapVec_succ (d m : ℕ) (k : Fin (d + 1) → ℕ) :
    (fun p : Site (d + 1) (m + 1) =>
        BoxProdAdjSpectrum.prodVec (cosMode (m + 1) (k 0))
          (boxLapVec d (m + 1) (Fin.tail k)) ((boxGraph_succ_iso d (m + 1)).symm p))
      = boxLapVec (d + 1) (m + 1) k := by
  funext p
  simp only [BoxProdAdjSpectrum.prodVec, boxLapVec, Fin.prod_univ_succ, Fin.tail]
  rfl

theorem boxLapEig_succ (d m : ℕ) (k : Fin (d + 1) → ℕ) :
    (2 - 2 * Real.cos (2 * half (m + 1) (k 0))) + boxLapEig d (m + 1) (Fin.tail k)
      = boxLapEig (d + 1) (m + 1) k := by
  simp only [boxLapEig, Fin.sum_univ_succ, Fin.tail]

/-! ## 3. The eigenvalue equation, in every dimension and with no hypotheses -/

/-- **THE `d`-DIMENSIONAL BOX'S FREE-BOUNDARY LAPLACIAN MODES.** -/
theorem lapMatrix_mulVec_boxLapVec (m d : ℕ) (k : Fin d → ℕ) :
    (boxGraph d (m + 1)).lapMatrix ℝ *ᵥ boxLapVec d (m + 1) k
      = boxLapEig d (m + 1) k • boxLapVec d (m + 1) k := by
  revert k
  induction d with
  | zero =>
      intro k
      funext p
      have hnb : (boxGraph 0 (m + 1)).neighborFinset p = ∅ := by
        ext q
        simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
        rintro ⟨i, -, -⟩
        exact i.elim0
      rw [SimpleGraph.lapMatrix_mulVec_apply, SimpleGraph.degree, hnb, Finset.card_empty,
        Finset.sum_empty]
      simp [boxLapEig]
  | succ d ih =>
      intro k
      have hu := lapMatrix_mulVec_cosMode m (k 0)
      have hprod := BoxProdLapSpectrum.lapMatrix_mulVec_prodVec
        (G := pathGraph (m + 1)) (H := boxGraph d (m + 1)) hu (ih (Fin.tail k))
      have htr := GraphIsoLapSpectrum.lapMatrix_mulVec_smul_iso
        (boxGraph_succ_iso d (m + 1)) hprod
      rw [boxLapVec_succ, boxLapEig_succ] at htr
      exact htr

/-! ## 4. And the vector is nonzero, so these are eigenvalues -/

/-- At the corner site every factor is `cos` of an angle in `[0, π/2)`. -/
theorem cosMode_corner_pos {n k : ℕ} (hn : 0 < n) (hk : k < n) :
    0 < cosMode n k (⟨0, hn⟩ : Fin n) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hrw : cosMode n k (⟨0, hn⟩ : Fin n) = Real.cos (half n k) := by
    simp [cosMode, cs]
  rw [hrw, half]
  refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
  · have : (0 : ℝ) ≤ (k : ℝ) * Real.pi / (2 * (n : ℝ)) := by positivity
    nlinarith [Real.pi_pos]
  · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ))]
    have hkn : (k : ℝ) < (n : ℝ) := by exact_mod_cast hk
    nlinarith [Real.pi_pos]

/-- **NONZERO whenever every frequency is below the side length.** -/
theorem boxLapVec_ne_zero {n : ℕ} {k : Fin d → ℕ} (hn : 0 < n) (hk : ∀ i, k i < n) :
    boxLapVec d n k ≠ 0 := by
  intro hcon
  have hp : (0 : ℝ) < ∏ i, cosMode n (k i) (⟨0, hn⟩ : Fin n) :=
    Finset.prod_pos fun i _ => cosMode_corner_pos hn (hk i)
  have h := congrFun hcon (fun _ => (⟨0, hn⟩ : Fin n))
  rw [boxLapVec] at h
  simp only [Pi.zero_apply] at h
  rw [h] at hp
  exact lt_irrefl 0 hp

end BoxLapSpectrum
