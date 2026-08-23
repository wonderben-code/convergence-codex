/-
  IsingSlabAniso.lean — the anisotropic three-dimensional Ising slab, as an
  instance of what is already proved.

  WHY. `PROOF_STRATEGY` §7 rule 3: deepen by removing one restrictive hypothesis
  at a time. The slab chain removed the dimension fence and then the `Col n`
  fence; what it did NOT remove is that all three coupling constants are equal.
  Every theorem about the slab is about the ISOTROPIC model, and the physically
  interesting three-dimensional questions are usually asked with the couplings
  free — a slab is, after all, a system one of whose directions is different from
  the other two.

  AND IT TURNS OUT TO COST NOTHING, WHICH IS THE POINT OF THE FILE. `transferG`
  takes the cross-section's own energy `E` as a PARAMETER and multiplies it by
  `β`, the same `β` that multiplies the layer-to-layer coupling. So the model
  with in-layer couplings `β·Ja`, `β·Jb` and length coupling `β` is
  `transferG β (slabIntraAniso Ja Jb)` — an instance, not a generalisation, and
  nothing had to be reproved.

  **AND IT IS THE THIRD INSTANCE, NOT THE SECOND.** `transferG`'s `E` already had
  two: `intra`, the strip's column, and `slabIntra`, the isotropic square. What
  makes this one worth a file is that the first two differ in the SHAPE of the
  cross-section and agree on the physics, while this one keeps the shape and
  changes the physics — so it is the first evidence that the `E` parameter buys
  models and not just geometries. A generality is worth what its instances are
  (`ERRATUM 48`'s family), and until now every instance was the same model on a
  different lattice.

  WHAT IS PROVED HERE. `slabIntraAniso` with its flip invariance — the only
  hypothesis the chain ever asked of a cross-section energy — and then, by
  instantiation: a spectral gap, the vanishing magnetisation at the top
  eigenvector, the finite-volume two-point function as a ratio of traces and in
  the eigenvalues, its length limit, exponential decay of that limit, and the
  wall stated for the anisotropic family. `slabIntraAniso_one_one` recovers the
  isotropic `slabIntra` on the nose.

  WHAT IS NOT TOUCHED, AS EVER. `r` depends on `β`, on `Ja`, on `Jb` and on the
  cross-section, and nothing says it stays below one as the cross-section grows.
  Anisotropy does not move `WALLS` §W4 §6 item 3 and this file does not suggest
  it might — if anything it widens the family over which the open question is
  open.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingSlabTopRatio

namespace IsingSlabAniso

open Filter Topology Finset Matrix Real
open IsingTransfer2D IsingSlabTransfer IsingSlabFlip IsingSlabMagnetisation
open IsingSlabDecay IsingSlabConfig IsingSlabSpectral IsingSlabLimit IsingSlabTopRatio

open scoped Matrix

variable {a b : ℕ}

/-! ## 1. The anisotropic cross-section energy -/

/-- **THE CROSS-SECTION'S OWN ENERGY WITH THE TWO IN-LAYER COUPLINGS FREE.** Against the Boltzmann
weight `exp (β · energyG …)` this is the model with in-layer couplings `β·Ja` and `β·Jb` and
layer-to-layer coupling `β`: two of the three constants are free relative to the third, which is
all anisotropy is. -/
def slabIntraAniso (Ja Jb : ℝ) (σ : Cross (Fin (a + 1) × Fin (b + 1))) : ℝ :=
  ∑ p : Fin (a + 1) × Fin (b + 1),
    (Ja * (spin (σ p) * spin (σ (p.1 + 1, p.2))) + Jb * (spin (σ p) * spin (σ (p.1, p.2 + 1))))

/-- **AT `Ja = Jb = 1` IT IS THE ISOTROPIC ENERGY**, so the existing slab is this file's `(1,1)`
case and not a parallel construction. -/
theorem slabIntraAniso_one_one (σ : Cross (Fin (a + 1) × Fin (b + 1))) :
    slabIntraAniso 1 1 σ = slabIntra σ := by
  simp only [slabIntraAniso, slabIntra, one_mul]

/-- **THE ONE HYPOTHESIS THE WHOLE CHAIN EVER ASKED OF A CROSS-SECTION ENERGY**, and the
anisotropic energy satisfies it for the same reason the isotropic one does: every term is a
product of TWO spins, and both change sign. The couplings never enter. -/
theorem slabIntraAniso_flipCross (Ja Jb : ℝ) (σ : Cross (Fin (a + 1) × Fin (b + 1))) :
    slabIntraAniso Ja Jb (flipCross σ) = slabIntraAniso Ja Jb σ := by
  simp only [slabIntraAniso, spin_flipCross]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-! ## 2. The transfer matrix, and everything that follows from it

Each theorem below is an instantiation. None of them has a proof of its own, and that is the
content of this file: the anisotropic slab needed no new mathematics, only a different `E`. -/

/-- **THE ANISOTROPIC SLAB'S TRANSFER MATRIX.** -/
noncomputable def anisoTransfer (β Ja Jb : ℝ) (a b : ℕ) :
    Matrix (Cross (Fin (a + 1) × Fin (b + 1))) (Cross (Fin (a + 1) × Fin (b + 1))) ℝ :=
  transferG β (slabIntraAniso (a := a) (b := b) Ja Jb)

theorem anisoTransfer_pos (β Ja Jb : ℝ) (a b : ℕ)
    (σ τ : Cross (Fin (a + 1) × Fin (b + 1))) : 0 < anisoTransfer β Ja Jb a b σ τ :=
  transferG_pos _ _ σ τ

theorem anisoTransfer_isHermitian (β Ja Jb : ℝ) (a b : ℕ) :
    Matrix.IsHermitian (anisoTransfer β Ja Jb a b) :=
  transferG_isHermitian _ _

/-- **A SPECTRAL GAP FOR THE ANISOTROPIC SLAB**, at every choice of the two in-layer couplings. -/
theorem aniso_gap (β Ja Jb : ℝ) (a b : ℕ) {p₀ : Cross (Fin (a + 1) × Fin (b + 1))}
    (hp₀ : ∀ j, (anisoTransfer_isHermitian β Ja Jb a b).eigenvalues j
      ≤ (anisoTransfer_isHermitian β Ja Jb a b).eigenvalues p₀)
    {q : Cross (Fin (a + 1) × Fin (b + 1))}
    (hne : (anisoTransfer_isHermitian β Ja Jb a b).eigenvalues q
      ≠ (anisoTransfer_isHermitian β Ja Jb a b).eigenvalues p₀) :
    |(anisoTransfer_isHermitian β Ja Jb a b).eigenvalues q|
      < (anisoTransfer_isHermitian β Ja Jb a b).eigenvalues p₀ :=
  transferG_gap _ _ hp₀ hne

/-- **THE MAGNETISATION AT THE TOP EIGENVECTOR VANISHES**, for every anisotropy. -/
theorem aniso_spinEigen_top_eq_zero (β Ja Jb : ℝ) (v : Fin (a + 1) × Fin (b + 1))
    {p₀ : Cross (Fin (a + 1) × Fin (b + 1))}
    (hp₀ : ∀ j, (transferG_isHermitian β (slabIntraAniso (a := a) (b := b) Ja Jb)).eigenvalues j
      ≤ (transferG_isHermitian β (slabIntraAniso (a := a) (b := b) Ja Jb)).eigenvalues p₀) :
    spinEigenG β (slabIntraAniso (a := a) (b := b) Ja Jb) v p₀ p₀ = 0 :=
  spinEigenG_top_eq_zero (slabIntraAniso_flipCross Ja Jb) β v hp₀

/-- **THE FINITE-VOLUME TWO-POINT FUNCTION IS A RATIO OF TRACES**, with the spin diagonal inserted
twice — a genuine anisotropic three-dimensional Ising correlation. -/
theorem aniso_corr2Sep_eq_trace_div (β Ja Jb : ℝ) (M : ℕ) (k : Fin (M + 1))
    (v : Fin (a + 1) × Fin (b + 1)) :
    corr2SepG β (slabIntraAniso (a := a) (b := b) Ja Jb) M k v
      = Matrix.trace (Matrix.diagonal (fun σ : Cross (Fin (a + 1) × Fin (b + 1)) => spin (σ v))
            * transfer2G β (slabIntraAniso (a := a) (b := b) Ja Jb) ^ (k : ℕ)
            * Matrix.diagonal (fun σ : Cross (Fin (a + 1) × Fin (b + 1)) => spin (σ v))
            * transfer2G β (slabIntraAniso (a := a) (b := b) Ja Jb) ^ (M + 1 - (k : ℕ)))
          / Matrix.trace (transfer2G β (slabIntraAniso (a := a) (b := b) Ja Jb) ^ (M + 1)) :=
  corr2SepG_eq_trace_div _ _ _ _ _

/-- **AND IN THE EIGENVALUES.** -/
theorem aniso_corr2Sep_eq_spectral (β Ja Jb : ℝ) (M : ℕ) (k : Fin (M + 1))
    (v : Fin (a + 1) × Fin (b + 1)) :
    corr2SepG β (slabIntraAniso (a := a) (b := b) Ja Jb) M k v
      = (∑ p, ∑ q, ‖spinEigenG β (slabIntraAniso (a := a) (b := b) Ja Jb) v p q‖ ^ 2
            * ((anisoTransfer_isHermitian β Ja Jb a b).eigenvalues q ^ (k : ℕ)
              * (anisoTransfer_isHermitian β Ja Jb a b).eigenvalues p ^ (M + 1 - (k : ℕ))))
          / ∑ p, (anisoTransfer_isHermitian β Ja Jb a b).eigenvalues p ^ (M + 1) :=
  corr2SepG_eq_spectral _ _ _ _ _

/-- **EXPONENTIAL DECAY FOR THE ANISOTROPIC THREE-DIMENSIONAL SLAB.** The two-point function at
separation `κ` along the length converges as the slab grows long, and the limit is bounded by
`r ^ κ` with `r < 1`.

**As in the isotropic case, and for the same reason, this is not about the phase transition**: it
holds at every `β` and every pair of in-layer couplings, and a slab of fixed cross-section is a
chain whatever its couplings are. -/
theorem aniso_corr2Sep_decay (β Ja Jb : ℝ) (v : Fin (a + 1) × Fin (b + 1)) :
    ∃ (p₀ : Cross (Fin (a + 1) × Fin (b + 1))) (r : ℝ), 0 ≤ r ∧ r < 1 ∧
      (∀ κ : ℕ, Tendsto (fun M : ℕ =>
          corr2SepG β (slabIntraAniso (a := a) (b := b) Ja Jb) (M + κ)
            ⟨κ, Nat.lt_succ_of_le (Nat.le_add_left κ M)⟩ v)
        atTop (𝓝 (corr2SepInfG β (slabIntraAniso (a := a) (b := b) Ja Jb) v p₀ κ)))
      ∧ ∀ κ : ℕ, |corr2SepInfG β (slabIntraAniso (a := a) (b := b) Ja Jb) v p₀ κ| ≤ r ^ κ :=
  corr2Sep_limit_decay (slabIntraAniso_flipCross Ja Jb) β v

/-- **AND THE DECAY BOUND WITH THE RATE NAMED**, rather than existentially quantified. -/
theorem aniso_corr2SepInf_abs_le (β Ja Jb : ℝ) (v : Fin (a + 1) × Fin (b + 1)) (κ : ℕ) :
    |corr2SepInfG β (slabIntraAniso (a := a) (b := b) Ja Jb) v
        (topIndexG β (slabIntraAniso (a := a) (b := b) Ja Jb)) κ|
      ≤ subTopRatioG β (slabIntraAniso (a := a) (b := b) Ja Jb) ^ κ :=
  corr2SepInfG_abs_le_subTopRatioG (slabIntraAniso_flipCross Ja Jb) β v κ

/-! ## 3. The wall, over the anisotropic family -/

/-- **`WALLS` §W4 §6 item 3 FOR THE ANISOTROPIC SLAB**, at fixed couplings, as the cross-section
grows in both directions. **Not proved for any `β ≠ 0`**, exactly as in the isotropic case —
anisotropy widens the family over which the question is open and does not touch the question. -/
def UniformSubTopRatioAniso (β Ja Jb : ℝ) : Prop :=
  UniformSubTopRatioFam (ι := ℕ × ℕ) (W := fun p => Fin (p.1 + 1) × Fin (p.2 + 1))
    (fun p => slabIntraAniso (a := p.1) (b := p.2) Ja Jb) β

/-- **AND IT IS SATISFIABLE**, at `β = 0`, with `δ = 1` — for every anisotropy at once, because at
`β = 0` the entries are `exp 0 = 1` and the energy never appears. -/
theorem uniformSubTopRatioAniso_zero (Ja Jb : ℝ) : UniformSubTopRatioAniso 0 Ja Jb :=
  uniformSubTopRatioFam_zero _

/-- **AND THIS IS WHAT IT WOULD BUY**: one exponential rate for the whole anisotropic family of
slabs at once. -/
theorem aniso_decay_uniform_of_uniform {β Ja Jb : ℝ} (h : UniformSubTopRatioAniso β Ja Jb) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : ℕ × ℕ) (v : Fin (p.1 + 1) × Fin (p.2 + 1)) (κ : ℕ),
      |corr2SepInfG β (slabIntraAniso (a := p.1) (b := p.2) Ja Jb) v
          (topIndexG β (slabIntraAniso (a := p.1) (b := p.2) Ja Jb)) κ| ≤ (1 - δ) ^ κ :=
  decay_uniform_of_uniformSubTopRatioFam (fun _ _ => slabIntraAniso_flipCross Ja Jb _) h

end IsingSlabAniso
