/-
  IsingFiniteVolume: the 2-d Ising Model Meets the Gibbs Machinery
  =================================================================

  The watchlist item "ExhibitsSymmetryBreaking for a CONCRETE lattice
  model" was blocked on (i) a finite-volume Gibbs DEFINITION and (ii) an
  interacting lattice model in Lean. Trigger (i) fired when
  `FiniteGibbs.lean` landed; this file delivers (ii) and connects them:
  the genuine two-dimensional Ising model on an n×n box, with the
  genuine spin-flip symmetry, plugged into the genuine Gibbs measure.
  Leg (iii) — the Peierls mathematics — is NOT attempted here and
  remains a mapped wall (see NOT PROVEN below).

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `Config`, `adj`, `isingH` — the model as DEFINITIONS: spins in
     Bool on the n×n box, nearest-neighbour adjacency with FREE
     boundary conditions, H(σ) = −Σ_{p~q} σ_p·σ_q summed over ORDERED
     adjacent pairs (each bond counted twice — a harmless rescaling of
     the coupling, stated once here).
  2. `isingH_flip`, `measurePreserving_flip` — the global spin flip is
     a symmetry of the Hamiltonian AND of the counting reference
     measure (the flip is an involutive bijection, so counting is
     preserved — proven via `encard` of images, not enumeration).
  3. `ising_isProbability` — the Ising Gibbs measure
     `FiniteGibbs.gibbs β (isingH n) count` is an honest probability
     measure at EVERY β (H is bounded by (n·n)² crudely; the counting
     measure is finite and nonzero).
  4. **`ising_gibbs_flip_invariant`** and, in ℤ₂-group form,
     **`ising_no_finite_volume_breaking`** — the punchline the split of
     ERRATA 34 predicted: for the REAL interacting Ising model, the
     finite-volume Gibbs measure is flip-invariant at EVERY inverse
     temperature; the clause-(2) SHAPE (∃ β_c beyond which some group
     element breaks invariance) is REFUTED for every n. Symmetry
     breaking, if it is anywhere, is in the thermodynamic limit or in
     boundary conditions — never in finite-volume invariance.
  5. The nontriviality certificates that keep this out of ERRATA 34's
     degeneracy: `flip_ne` (the flip moves every configuration, n ≥ 1),
     and `isingH_not_constant` (H separates the all-aligned
     configuration from the chessboard configuration for every n ≥ 2 —
     proven abstractly via the parity argument, no finite enumeration:
     aligned neighbours contribute −1 each to H, chessboard neighbours
     +1 each, and an n ≥ 2 box has at least one bond).

  NOT proven here (the honest walls, unchanged):

  * The Peierls leg: any statement of the form "symmetry breaking
    happens" — magnetisation bounds under boundary conditions, contour
    counting, the thermodynamic limit. The watchlist maps it as a wall;
    this file only clears the definitional ground it was blocked on.
    Any future formulation must pass the ERRATA-34 test (write it, then
    try to refute it BEFORE proving it) — at finite volume the theorems
    HERE show measure non-invariance can never be that formulation.
  * Periodic boundary conditions (free boundary is chosen and stated),
    external field, coupling constants beyond the ±1 normalisation.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import FiniteGibbs
import Mathlib.Data.ZMod.Basic

open MeasureTheory

noncomputable section

namespace IsingFiniteVolume

/-! ## 1. The model -/

/-- Sites of the n×n box. -/
abbrev Site (n : ℕ) := Fin n × Fin n

/-- Configurations: a Boolean spin at every site. -/
abbrev Config (n : ℕ) := Site n → Bool

/-- Every singleton of configurations is measurable: it is the finite
    intersection of coordinate constraints. (Mathlib has this instance
    for products but not for finite function spaces.) -/
instance (n : ℕ) : MeasurableSingletonClass (Config n) := by
  constructor
  intro σ
  have h : {σ} = ⋂ p : Site n, (fun τ : Config n => τ p) ⁻¹' {σ p} := by
    ext τ
    simp [funext_iff]
  rw [h]
  exact MeasurableSet.iInter fun p =>
    measurable_pi_apply p (measurableSet_singleton (σ p))

/-- Spin value: true ↦ +1, false ↦ −1. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

theorem abs_spin (b : Bool) : |spin b| = 1 := by
  cases b <;> simp [spin]

theorem spin_not (b : Bool) : spin (!b) = -spin b := by
  cases b <;> simp [spin]

/-- Nearest-neighbour adjacency on the n×n box, FREE boundary: the
    sites differ by one step in exactly one coordinate. -/
def adj {n : ℕ} (p q : Site n) : Prop :=
  (p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
  (p.2 = q.2 ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val))

instance {n : ℕ} (p q : Site n) : Decidable (adj p q) := by
  unfold adj; infer_instance

/-- The Ising Hamiltonian, free boundary, ORDERED adjacent pairs (each
    bond twice — a rescaling of the coupling, harmless for every
    theorem below): H(σ) = −Σ_{p~q} σ_p·σ_q. -/
def isingH (n : ℕ) (σ : Config n) : ℝ :=
  -∑ p : Site n, ∑ q : Site n,
    if adj p q then spin (σ p) * spin (σ q) else 0

/-! ## 2. The symmetry -/

/-- The global spin flip. -/
def flip {n : ℕ} (σ : Config n) : Config n := fun p => !(σ p)

theorem flip_involutive {n : ℕ} : Function.Involutive (flip (n := n)) :=
  fun σ => by funext p; simp [flip]

/-- The flip moves EVERY configuration (n ≥ 1): the action is
    nontrivial in the strongest pointwise sense. -/
theorem flip_ne (n : ℕ) (hn : 0 < n) (σ : Config n) : flip σ ≠ σ := by
  intro h
  have h0 := congrFun h (⟨⟨0, hn⟩, ⟨0, hn⟩⟩ : Site n)
  simp [flip] at h0

/-- The Hamiltonian is flip-invariant: both spins negate, the product
    survives. -/
theorem isingH_flip (n : ℕ) (σ : Config n) :
    isingH n (flip σ) = isingH n σ := by
  unfold isingH flip
  congr 1
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  split
  · rw [spin_not, spin_not]
    ring
  · rfl

/-- The flip preserves the counting reference measure: it is an
    involutive bijection, so preimages have the same `encard`. -/
theorem measurePreserving_flip (n : ℕ) :
    MeasurePreserving (flip (n := n)) Measure.count Measure.count := by
  refine ⟨measurable_of_countable _, ?_⟩
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_of_countable _) hs]
  have hpre : flip ⁻¹' s = flip (n := n) '' s := by
    ext τ
    constructor
    · intro h
      exact ⟨flip τ, h, flip_involutive τ⟩
    · rintro ⟨υ, hυ, rfl⟩
      simpa [Set.mem_preimage, flip_involutive υ] using hυ
  rw [Measure.count_apply (measurable_of_countable (flip (n := n)) hs),
    Measure.count_apply hs, hpre,
    (flip_involutive (n := n)).injective.encard_image s]

/-! ## 3. Boundedness, probability -/

/-- The crude uniform bound |H| ≤ (n·n)²: every ordered-pair term has
    absolute value at most 1, and there are (n·n)² ordered pairs. -/
theorem isingH_bound (n : ℕ) (σ : Config n) :
    |isingH n σ| ≤ ((n : ℝ) * n) ^ 2 := by
  rw [isingH, abs_neg]
  have hterm : ∀ p q : Site n,
      |if adj p q then spin (σ p) * spin (σ q) else 0| ≤ 1 := by
    intro p q
    split
    · rw [abs_mul, abs_spin, abs_spin]
      norm_num
    · simp
  calc |∑ p : Site n, ∑ q : Site n,
        if adj p q then spin (σ p) * spin (σ q) else 0|
      ≤ ∑ p : Site n, |∑ q : Site n,
          if adj p q then spin (σ p) * spin (σ q) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : Site n, ∑ q : Site n,
          |if adj p q then spin (σ p) * spin (σ q) else 0| :=
        Finset.sum_le_sum fun p _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Site n, ∑ _q : Site n, (1 : ℝ) :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hterm p q
    _ = ((n : ℝ) * n) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ]
        ring

theorem measurable_isingH (n : ℕ) : Measurable (isingH n) :=
  measurable_of_countable _

/-- **The Ising Gibbs measure is an honest probability measure at every
    β** — `FiniteGibbs.isProbabilityMeasure_gibbs` instantiated. -/
theorem ising_isProbability (n : ℕ) (β : ℝ) :
    IsProbabilityMeasure
      (FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n))) :=
  FiniteGibbs.isProbabilityMeasure_gibbs β (isingH_bound n)
    Measure.count Measure.count_ne_zero''

/-! ## 4. Invariance at every β -/

/-- **The Ising Gibbs measure is flip-invariant at EVERY inverse
    temperature** — the real interacting model, not a toy. -/
theorem ising_gibbs_flip_invariant (n : ℕ) (β : ℝ) :
    Measure.map flip
        (FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n)))
      = FiniteGibbs.gibbs β (isingH n) Measure.count :=
  FiniteGibbs.gibbs_map_of_invariant β (measurable_isingH n)
    (measurePreserving_flip n) (isingH_flip n)

/-! ## 5. The ℤ₂ group form -/

/-- The ℤ₂ action: the nonidentity element acts by the global flip. -/
def zflip (n : ℕ) (g : Multiplicative (ZMod 2)) (σ : Config n) : Config n :=
  if Multiplicative.toAdd g = 0 then σ else flip σ

theorem zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

theorem zflip_one (n : ℕ) (σ : Config n) : zflip n 1 σ = σ := by
  simp [zflip]

theorem zflip_mul (n : ℕ) (g h : Multiplicative (ZMod 2)) (σ : Config n) :
    zflip n (g * h) σ = zflip n g (zflip n h σ) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  unfold zflip
  rcases zmod2_cases (Multiplicative.toAdd g) with hg | hg <;>
    rcases zmod2_cases (Multiplicative.toAdd h) with hh | hh <;>
      simp [toAdd_mul, hg, hh, h11, flip_involutive σ]

instance (n : ℕ) : MulAction (Multiplicative (ZMod 2)) (Config n) where
  smul := zflip n
  one_smul := zflip_one n
  mul_smul := zflip_mul n

theorem measurePreserving_zflip (n : ℕ) (g : Multiplicative (ZMod 2)) :
    MeasurePreserving (fun σ : Config n => g • σ)
      Measure.count Measure.count := by
  by_cases hg : Multiplicative.toAdd g = 0
  · have h : (fun σ : Config n => g • σ) = id := by
      funext σ
      change zflip n g σ = σ
      simp [zflip, hg]
    rw [h]
    exact MeasurePreserving.id _
  · have h : (fun σ : Config n => g • σ) = flip := by
      funext σ
      change zflip n g σ = flip σ
      simp [zflip, hg]
    rw [h]
    exact measurePreserving_flip n

theorem isingH_zflip (n : ℕ) (g : Multiplicative (ZMod 2)) (σ : Config n) :
    isingH n (g • σ) = isingH n σ := by
  by_cases hg : Multiplicative.toAdd g = 0
  · have h : g • σ = σ := by
      change zflip n g σ = σ
      simp [zflip, hg]
    rw [h]
  · have h : g • σ = flip σ := by
      change zflip n g σ = flip σ
      simp [zflip, hg]
    rw [h, isingH_flip]

/-- **No finite-volume symmetry breaking for the 2-d Ising model**: the
    clause-(2) SHAPE of the refuted phase-transition statement fails for
    the real model at every box size — there is no β_c beyond which any
    ℤ₂ element breaks invariance. `FiniteGibbs.no_finite_volume_breaking`
    instantiated at its intended target. -/
theorem ising_no_finite_volume_breaking (n : ℕ) :
    ¬ ∃ β_c : ℝ, ∀ β > β_c, ∃ g : Multiplicative (ZMod 2),
        FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n))
          ≠ Measure.map (fun σ => g • σ)
              (FiniteGibbs.gibbs β (isingH n) Measure.count) :=
  FiniteGibbs.no_finite_volume_breaking (measurable_isingH n)
    (measurePreserving_zflip n) (isingH_zflip n)

/-! ## 6. Nontriviality: the model genuinely interacts -/

/-- The chessboard configuration: spin by site parity. -/
def chess (n : ℕ) : Config n := fun p => decide ((p.1.val + p.2.val) % 2 = 0)

/-- Adjacent sites have opposite parity. -/
theorem adj_parity {n : ℕ} {p q : Site n} (h : adj p q) :
    (p.1.val + p.2.val) % 2 ≠ (q.1.val + q.2.val) % 2 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' : p.1.val = q.1.val := congrArg Fin.val h1
    rcases h2 with h2 | h2 <;> omega
  · have h1' : p.2.val = q.2.val := congrArg Fin.val h1
    rcases h2 with h2 | h2 <;> omega

/-- On the chessboard, every adjacent ordered pair contributes −1. -/
theorem spin_chess_adj {n : ℕ} {p q : Site n} (h : adj p q) :
    spin (chess n p) * spin (chess n q) = -1 := by
  have hpar := adj_parity h
  unfold chess spin
  by_cases hp : (p.1.val + p.2.val) % 2 = 0 <;>
    by_cases hq : (q.1.val + q.2.val) % 2 = 0
  · omega
  · simp [hp, hq]
  · simp [hp, hq]
  · omega

/-- The all-aligned configuration has strictly negative energy (n ≥ 2):
    at least one bond exists, and every bond contributes −1. -/
theorem isingH_allTrue_neg (n : ℕ) (hn : 2 ≤ n) :
    isingH n (fun _ => true) < 0 := by
  have hterm : ∀ p q : Site n,
      (0 : ℝ) ≤ if adj p q then spin true * spin true else 0 := by
    intro p q
    split
    · simp [spin]
    · exact le_rfl
  have hpair : adj (⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩ : Site n)
      ⟨⟨0, by omega⟩, ⟨1, by omega⟩⟩ := by
    left
    exact ⟨rfl, Or.inl rfl⟩
  have h1 : (1 : ℝ) ≤ ∑ q : Site n,
      if adj (⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩ : Site n) q
        then spin true * spin true else 0 := by
    have hs := Finset.single_le_sum
      (f := fun q : Site n =>
        if adj (⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩ : Site n) q
          then spin true * spin true else 0)
      (fun q _ => hterm _ q)
      (Finset.mem_univ (⟨⟨0, by omega⟩, ⟨1, by omega⟩⟩ : Site n))
    simp only [] at hs
    rw [if_pos hpair] at hs
    simpa [spin] using hs
  have h2 : (1 : ℝ) ≤ ∑ p : Site n, ∑ q : Site n,
      if adj p q then spin true * spin true else 0 := by
    refine le_trans h1 ?_
    exact Finset.single_le_sum
      (f := fun p : Site n => ∑ q : Site n,
        if adj p q then spin true * spin true else 0)
      (fun p _ => Finset.sum_nonneg fun q _ => hterm p q)
      (Finset.mem_univ _)
  rw [isingH, neg_lt_zero]
  exact lt_of_lt_of_le one_pos h2

/-- The chessboard configuration has strictly positive energy (n ≥ 2):
    every bond contributes +1 to H. -/
theorem isingH_chess_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < isingH n (chess n) := by
  have hterm : ∀ p q : Site n,
      (0 : ℝ) ≤ -(if adj p q then spin (chess n p) * spin (chess n q) else 0) := by
    intro p q
    split
    · rename_i h
      rw [spin_chess_adj h]
      norm_num
    · simp
  have hpair : adj (⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩ : Site n)
      ⟨⟨0, by omega⟩, ⟨1, by omega⟩⟩ := by
    left
    exact ⟨rfl, Or.inl rfl⟩
  have h1 : (1 : ℝ) ≤ ∑ q : Site n,
      -(if adj (⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩ : Site n) q
          then spin (chess n (⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩ : Site n))
            * spin (chess n q) else 0) := by
    have hs := Finset.single_le_sum
      (f := fun q : Site n =>
        -(if adj (⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩ : Site n) q
            then spin (chess n (⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩ : Site n))
              * spin (chess n q) else 0))
      (fun q _ => hterm _ q)
      (Finset.mem_univ (⟨⟨0, by omega⟩, ⟨1, by omega⟩⟩ : Site n))
    simp only [] at hs
    rw [if_pos hpair, spin_chess_adj hpair] at hs
    simpa using hs
  have h2 : (1 : ℝ) ≤ ∑ p : Site n, ∑ q : Site n,
      -(if adj p q then spin (chess n p) * spin (chess n q) else 0) := by
    refine le_trans h1 ?_
    exact Finset.single_le_sum
      (f := fun p : Site n => ∑ q : Site n,
        -(if adj p q then spin (chess n p) * spin (chess n q) else 0))
      (fun p _ => Finset.sum_nonneg fun q _ => hterm p q)
      (Finset.mem_univ _)
  have hneg : ∑ p : Site n, ∑ q : Site n,
      -(if adj p q then spin (chess n p) * spin (chess n q) else 0)
      = -∑ p : Site n, ∑ q : Site n,
          (if adj p q then spin (chess n p) * spin (chess n q) else 0) := by
    simp
  rw [hneg] at h2
  rw [isingH]
  linarith

/-- **The Hamiltonian genuinely interacts**: it separates the aligned
    configuration from the chessboard for every n ≥ 2 — this is not the
    trivial-Hamiltonian degeneracy of ERRATA 34. -/
theorem isingH_not_constant (n : ℕ) (hn : 2 ≤ n) :
    isingH n (fun _ => true) ≠ isingH n (chess n) :=
  ne_of_lt (lt_trans (isingH_allTrue_neg n hn) (isingH_chess_pos n hn))

/-- **The package**: a genuinely interacting Hamiltonian, a genuinely
    nontrivial symmetry, and no finite-volume breaking at any box size
    n ≥ 2. The honest per-model successor to the refuted universal
    phase-transition statement, at its definitional ground floor. -/
theorem ising_honest_no_breaking (n : ℕ) (hn : 2 ≤ n) :
    isingH n (fun _ => true) ≠ isingH n (chess n)
      ∧ (∀ σ : Config n, flip σ ≠ σ)
      ∧ ¬ ∃ β_c : ℝ, ∀ β > β_c, ∃ g : Multiplicative (ZMod 2),
          FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n))
            ≠ Measure.map (fun σ => g • σ)
                (FiniteGibbs.gibbs β (isingH n) Measure.count) :=
  ⟨isingH_not_constant n hn, flip_ne n (by omega),
    ising_no_finite_volume_breaking n⟩

end IsingFiniteVolume
