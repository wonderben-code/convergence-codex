/-
  HermitePiProper.lean — the n-dimensional Stein class is a PROPER subset of
  L²(γⁿ).

  WHY. `HermitePiPoincare` proves `Var(f) ≤ Σᵢ ∫ gᵢ²` for every `f` in the
  n-dimensional Stein class, and `SteinGeneralPi` gives a criterion that puts
  a great many functions in it. Neither says the class is smaller than
  `L²(γⁿ)`. If it were not, the inequality would be a statement about every
  square-integrable function, which is false in one dimension and would be
  surprising in `n` — so the gap was not cosmetic. In one dimension the
  estate closed it with `HermiteHilbertBasis.exists_memLp_not_steinPair`,
  by construction. This file does the same in every dimension, and reduces
  to that construction rather than repeating it.

  WHAT THIS FILE PROVES:
  1. **`exists_memLp_not_steinPairPi`** — in every dimension `n ≥ 1` there
     is an `f ∈ L²(γⁿ)` with **no** Stein partner at all. Not "no obvious
     one": the refutation is a single divergent series and it kills every
     candidate `g` simultaneously.
  2. **`steinPairPi_proper`**, **`sobolevWeakPi_proper`** and
     **`smoothSteinPairPi_proper`** — and therefore all three n-dimensional
     classes are proper, the last two through `W6ConversePi`'s arrow.

  HOW, AND THE POINT IS THAT ALMOST NOTHING HERE IS NEW. The refutation was
  already proved — as a `have` inside `poincare_steinPi`. It is now
  `HermitePiPoincare.summable_weighted_coeffPi`: **if `f` has a partner then
  `Σ_k kᵢ·(∏ⱼmⱼ!)·c_k(f)² converges`.** So a coefficient sequence whose
  ordinary series converges and whose `kᵢ`-weighted series diverges has no
  partner. Put the coefficients on the multi-indices `eᵢ·j` and zero
  elsewhere; there `∏ⱼ mⱼ! = j!` and `kᵢ = j`, so both series are the 1-d
  series of `HermiteHilbertBasis.badSeq`, one summable and one not.
  `HermitePiRiesz.exists_of_summable_pi` turns the sequence into a function.

  THAT EXTRACTION IS THE SIXTH TIME the estate has paid for machinery buried
  inside a proof, so it was done by moving the `have` out of
  `poincare_steinPi` and having that proof cite the named theorem — not by
  transcribing it here.

  WHAT THIS DOES NOT DO. It does not give the n-dimensional coefficient
  CHARACTERISATION. In one dimension `HermiteHilbertBasis.steinPair_iff_sobolev`
  makes membership EQUIVALENT to `Σ (n+1)·n!·cₙ(f)² < ∞` and properness is a
  corollary of it; here only one direction is available
  (`coeffPi_recursion` and the summability above), which is enough to REFUTE
  membership and not enough to CERTIFY it from coefficients alone. So
  `exists_memLp_not_steinPairPi` is proved, and the biconditional it would
  have followed from in 1-d is still open.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import W6ConversePi
import HermiteHilbertBasis

namespace HermitePiProper

open MeasureTheory ProbabilityTheory Filter Topology
open GaussianPoincare GaussianProductMeasure HermitePi
open HermitePiBessel HermitePiBasis HermitePiRiesz
open HermitePiStein HermitePiPoincare TextbookSobolevPi W6ConversePi

noncomputable section

variable {n : ℕ}

/-! ## 1. The single-coordinate multi-indices

`eᵢ·j` — the multi-index that is `j` at `i` and `0` everywhere else. It is
where the whole construction lives, and it is what turns two n-dimensional
series into two 1-dimensional ones.
-/

/-- The embedding of `ℕ` into multi-indices along the `i`-th axis. -/
def emb (n : ℕ) (i : Fin n) (j : ℕ) : Fin n → ℕ := Pi.single i j

theorem emb_apply_self (i : Fin n) (j : ℕ) : emb n i j i = j := by
  classical
  simp [emb]

theorem emb_injective (i : Fin n) : Function.Injective (emb n i) := by
  intro j j' hjj
  have := congrArg (fun m : Fin n → ℕ => m i) hjj
  simpa [emb_apply_self] using this

/-- `∏ⱼ (eᵢ·j)ⱼ! = j!` — every factor but the `i`-th is `0! = 1`. The estate
    had this only at the value `1` (`HermitePiPoincare.facPi_single`). -/
theorem facPi_emb (i : Fin n) (j : ℕ) : facPi n (emb n i j) = (j.factorial : ℝ) := by
  classical
  rw [facPi, Finset.prod_eq_single i]
  · rw [emb_apply_self]
  · intro l _ hl
    rw [emb, Pi.single_eq_of_ne hl]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-! ## 2. The coefficient sequence

`HermiteHilbertBasis.badSeq` along the `i`-th axis, zero off it. The
`Function.extend` is what makes "zero off the axis" a definition rather than
a case split repeated in every proof.
-/

/-- The 1-d bad sequence, transplanted onto the `i`-axis. -/
def aPi (n : ℕ) (i : Fin n) : (Fin n → ℕ) → ℝ :=
  Function.extend (emb n i) HermiteHilbertBasis.badSeq 0

theorem aPi_emb (i : Fin n) (j : ℕ) :
    aPi n i (emb n i j) = HermiteHilbertBasis.badSeq j :=
  (emb_injective i).extend_apply _ _ j

theorem aPi_off (i : Fin n) {k : Fin n → ℕ} (hk : k ∉ Set.range (emb n i)) :
    aPi n i k = 0 := by
  rw [aPi, Function.extend_apply' _ _ _ (fun ⟨j, hj⟩ => hk ⟨j, hj⟩)]
  rfl

/-! ## 3. One series converges and one does not

Both are the estate's own 1-dimensional series, reached by the same
injection. `summable_badSeq` and `not_summable_badSeq` do the work; the only
arithmetic here is that the estate's divergent series carries the weight
`j+1` where this one carries `j`, and the difference between them is the
convergent series.
-/

/-- The unweighted series CONVERGES, so the sequence is a legal set of
    Hermite coefficients. -/
theorem summable_facPi_aPi (i : Fin n) :
    Summable fun k : Fin n → ℕ => facPi n k * aPi n i k ^ 2 := by
  have hzero : ∀ k ∉ Set.range (emb n i), facPi n k * aPi n i k ^ 2 = 0 := by
    intro k hk
    rw [aPi_off i hk]
    ring
  refine ((emb_injective i).summable_iff hzero).mp ?_
  refine HermiteHilbertBasis.summable_badSeq.congr fun j => ?_
  simp only [Function.comp_apply]
  rw [facPi_emb, aPi_emb]

/-- The `kᵢ`-weighted series DIVERGES. This is the whole refutation. -/
theorem not_summable_weighted_aPi (i : Fin n) :
    ¬ Summable fun k : Fin n → ℕ => (k i : ℝ) * (facPi n k * aPi n i k ^ 2) := by
  intro hcon
  have hzero : ∀ k ∉ Set.range (emb n i),
      (k i : ℝ) * (facPi n k * aPi n i k ^ 2) = 0 := by
    intro k hk
    rw [aPi_off i hk]
    ring
  have hj : Summable fun j : ℕ =>
      (j : ℝ) * ((j.factorial : ℝ) * HermiteHilbertBasis.badSeq j ^ 2) := by
    refine (((emb_injective i).summable_iff hzero).mpr hcon).congr fun j => ?_
    simp only [Function.comp_apply]
    rw [facPi_emb, aPi_emb, emb_apply_self]
  refine HermiteHilbertBasis.not_summable_badSeq ?_
  refine (hj.add HermiteHilbertBasis.summable_badSeq).congr fun j => ?_
  ring

/-! ## 4. The witness, and the three classes it makes proper -/

/-- **THE n-DIMENSIONAL STEIN CLASS IS A PROPER SUBSET OF `L²(γⁿ)`.** Not an
    observation about the definition: a function is constructed, and the
    divergent series of §3 refutes every candidate partner at once. -/
theorem exists_memLp_not_steinPairPi (i : Fin n) :
    ∃ f : (Fin n → ℝ) → ℝ, MemLp f 2 (gaussPi n)
      ∧ ¬ ∃ g : Fin n → ((Fin n → ℝ) → ℝ), SteinPairPi n f g := by
  obtain ⟨f, hf, hfc⟩ := exists_of_summable_pi n (summable_facPi_aPi i)
  refine ⟨f, hf, fun ⟨g, hg⟩ => not_summable_weighted_aPi i ?_⟩
  refine (summable_weighted_coeffPi n hg i).congr fun k => ?_
  rw [hfc k]

/-- Stated as the properness claim. -/
theorem steinPairPi_proper (i : Fin n) :
    ∃ f : (Fin n → ℝ) → ℝ, MemLp f 2 (gaussPi n)
      ∧ ∀ g : Fin n → ((Fin n → ℝ) → ℝ), ¬ SteinPairPi n f g := by
  obtain ⟨f, hf, hns⟩ := exists_memLp_not_steinPairPi i
  exact ⟨f, hf, fun g hg => hns ⟨g, hg⟩⟩

/-- **AND SO IS THE TEXTBOOK CLASS**, inherited through `W6ConversePi`'s
    arrow: a `SobolevWeakPi` member is a `SteinPairPi` member, so a function
    that is not the latter is not the former. -/
theorem sobolevWeakPi_proper (i : Fin n) :
    ∃ f : (Fin n → ℝ) → ℝ, MemLp f 2 (gaussPi n)
      ∧ ∀ g : Fin n → ((Fin n → ℝ) → ℝ), ¬ SobolevWeakPi n f g := by
  obtain ⟨f, hf, hns⟩ := exists_memLp_not_steinPairPi i
  exact ⟨f, hf, fun g hg => hns ⟨g, steinPairPi_of_sobolevWeakPi n hg⟩⟩

/-- And the `Cc^∞`-tested class, by the same arrow. -/
theorem smoothSteinPairPi_proper (i : Fin n) :
    ∃ f : (Fin n → ℝ) → ℝ, MemLp f 2 (gaussPi n)
      ∧ ∀ g : Fin n → ((Fin n → ℝ) → ℝ), ¬ SmoothSteinPairPi n f g := by
  obtain ⟨f, hf, hns⟩ := exists_memLp_not_steinPairPi i
  exact ⟨f, hf, fun g hg => hns ⟨g, steinPairPi_of_smoothSteinPairPi n hg⟩⟩

/-! ## 5. Review round 60 — the ways this could be hollow

**"The witness could be zero, or the statement could hold vacuously in
dimension 0."** Every theorem above takes an `i : Fin n`, which is
inhabited only when `n ≥ 1`, so nothing is claimed in dimension `0` — and
nothing should be: `Fin 0 → ℝ` is a point, `L²` over it is one-dimensional,
and the constants exhaust it. The witness itself is nonzero because its
coefficients are: `badSeq j = (√(j!))⁻¹·(j+1)⁻¹` is never `0`, and
`exists_of_summable_pi` returns a function realising them exactly.

**"The refutation could be refuting the wrong thing."** It refutes the
existence of ANY `g` with `SteinPairPi n f g`, quantified inside the
statement — not the failure of some particular candidate. That is what
makes §4 a properness theorem rather than a remark about one attempt.

**"§4 might not actually need the n-dimensional machinery."** It needs
exactly one n-dimensional fact, `summable_weighted_coeffPi`, and that fact
is where `coeffPi_recursion`, `facPi_succAt` and the `succAt` bijection all
enter. The rest is the 1-d construction carried along an axis, which is the
honest description and is why this file is short.

**"The three properness statements could be the same statement three
times."** They are three statements about three classes, and the second and
third are inherited along an arrow that only exists because of
`W6ConversePi`. Before this morning neither could have been stated.
-/

/-- The witness has a nonzero coefficient, so it is not the zero function in
    `L²(γⁿ)` — the refutation is not being carried by a degenerate example. -/
theorem aPi_ne_zero (i : Fin n) (j : ℕ) : aPi n i (emb n i j) ≠ 0 := by
  rw [aPi_emb]
  exact HermiteHilbertBasis.badSeq_ne_zero j

end

end HermitePiProper
