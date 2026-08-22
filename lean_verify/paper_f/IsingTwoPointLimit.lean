import IsingTwoPointSpectral

/-!
# The long strip: the two-point function in the limit, and the limit is not zero

`IsingTwoPointSpectral.corr2Sep_eq_spectral` writes the strip's two-point function as
`(∑ₚ∑_q ‖Bₚq‖² λ_qᵏ λₚᴹ⁺¹⁻ᵏ) / (∑ₚ λₚᴹ⁺¹)`. `TransferPowerSum` §4 already takes `M → ∞` in the
denominator alone. This file takes it in both.

## What is proved

* **`corr2Sep_tendsto`** — at fixed width and fixed separation `κ`, as the strip's LENGTH grows
  the two-point function converges, to `∑_q ‖B_{p₀q}‖² · (λ_q/λ_{p₀})^κ` with `p₀` an index of a
  largest eigenvalue. Every term of that finite sum but one has `|λ_q/λ_{p₀}| < 1`;
* **`corr2SepInf`** — that limit, named, so the statements below are about an object rather than
  about a limit expression;
* **`spinEigen_mul_self`**, **`sum_sq_spinEigen_row`** and **`corr2SepInf_zero`** — the
  observable squares to the identity, so each row of squared entries of `B` sums to one, so the
  limit at zero separation is `1`. **`IsingTwoPoint.corr2Sep_zero` says every finite strip already
  gives `1` there**, and proves it by reindexing a configuration sum with no matrix algebra in it,
  so this is a check on `corr2Sep_eq_spectral` and on §2 that shares no step with either;
* **`corr2SepInf_eq_diag_add`** — its `q = p₀` term is `‖B_{p₀p₀}‖²` and carries **no `κ` at
  all**, the ratio there being `1`;
* **`corr2SepInf_tendsto_diag`** — so as the separation grows the infinite strip's two-point
  function tends to `‖B_{p₀p₀}‖²`;
* **`corr2SepInf_connected_tendsto_zero`** — and the object that goes to zero is the **connected**
  function `⟨σ₀σ_κ⟩_∞ − ‖B_{p₀p₀}‖²`;
* **`exists_subTop_ratio`** and **`corr2SepInf_connected_le`** — **EXPONENTIAL CLUSTERING**:
  `|⟨σ₀σ_κ⟩_∞ − ‖B_{p₀p₀}‖²| ≤ rᵏ`, with `r < 1` the largest eigenvalue ratio off the top index.
  The constant is `1`, and that is §3's row sum rather than a convenience — the off-diagonal
  squared entries are part of a family summing to one.

## What this is NOT, and one of these is a correction to an obvious target

**It is not a mass gap and does not move `WALLS` §W4.** Every quantity here is at FIXED WIDTH `n`;
the limit taken is in the strip's length. Item 3 wants `n → ∞`, and no theorem in this estate
takes that limit.

**And "the two-point function decays to zero" is FALSE as a target**, which is why
`corr2SepInf_eq_diag_add` is stated before anything asymptotic. The diagonal term is the square of
the spin observable's expectation in the top eigenvector — the magnetisation, in the physics
name — and nothing here says it vanishes. There is a standard argument that it does: flipping
every spin leaves `IsingTransfer2D.energy` unchanged and negates the observable, while the top
eigenvector is strictly positive (`PerronVector.exists_pos_top_eigenvector`) and so is fixed by
that permutation rather than negated. **None of that is in this estate** — probed 2026-08-22 over
`paper_f/Ising*.lean` and `paper_f/Perron*.lean` for `energy_neg`, `energy_not`, `spin_flip`: zero
each — and none of it is assumed below. What is proved is convergence to the diagonal term,
whatever that term is.

⚠ **SUPERSEDED — `IsingMagnetisationVanishes` PROVES `‖B_{p₀p₀}‖² = 0`, so `corr2SepInf` tends to
ZERO and `|corr2SepInf κ| ≤ rᵏ`. The paragraph above is kept per `ERRATUM 94`, and every sentence
in it remains true OF THIS FILE.** Two things in it were right: that decay to zero may not be
**assumed** here, and that the flip invariance was genuinely absent when this was written — it was
supplied afterwards by `IsingFlipSymmetry`. One was incomplete: **the route named above, through
the top eigenvector's strict positivity, is not the route taken.** The proof conjugates the flip
into the eigenbasis, where it commutes with a diagonal matrix, and uses only simplicity of the top
eigenvalue **in the list**. So this file's clustering-to-an-unknown-constant becomes clustering to
a known one, and `corr2SepInf_connected_le` becomes an exponential **decay** bound. **Nothing
about the width changes and `WALLS` §W4 does not move.**

**But `r` DEPENDS ON THE WIDTH.** It is built from that width's eigenvalues, and nothing here says
it stays below one as `n` grows — which is exactly `WALLS` §W4 §6 item 3's open sentence. What §5
is, is exponential clustering for **one** strip.

**`corr2SepInf_connected_tendsto_zero` is weaker than `corr2SepInf_connected_le` and is kept
anyway**, with its own proof: the bound needs the largest off-top ratio to be **attained**, and so
needs `Col n` to have more than one element, while the convergence does not. The two are not the
same statement proved twice — one is qualitative and holds more generally.

**And the boundedness `|corr2SepInf κ| ≤ 1` is not proved**, being cheap from §3's row sum and
needed by nothing below.

**And `p₀` is a parameter, not a canonical object.** `PerronGap.exists_max_eigenvalue` supplies an
index carrying a largest eigenvalue, and `TransferPowerSum.index_eq_of_eigenvalues_eq_top` says
there is only one — but the second fact is not invoked here, so every statement below is relative
to whichever index the hypothesis names.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace IsingTwoPointLimit

open Filter Topology Finset
open IsingTransfer2D IsingTransferSym IsingTwoPoint IsingTwoPointSpectral

open scoped Matrix

/-- The hypothesis both Perron statements consume, at the strip's own matrix. -/
theorem transferSym_entries_pos (β : ℝ) (n : ℕ) : ∀ a b : Col n, 0 < transferSym β n a b :=
  fun a b => transferSym_pos β a b

/-! ## 1. The limit, named -/

/-- **THE TWO-POINT FUNCTION OF THE INFINITE STRIP OF FIXED WIDTH**, relative to a choice `p₀` of
index carrying a largest eigenvalue. It is a finite sum of `κ`-th powers of ratios, all of modulus
at most one and exactly one of them equal to one. -/
noncomputable def corr2SepInf (β : ℝ) (n : ℕ) (i : Fin (n + 1)) (p₀ : Col n) (κ : ℕ) : ℝ :=
  ∑ q, ‖spinEigen β n i p₀ q‖ ^ 2
    * ((transferSym_isHermitian β n).eigenvalues q
        / (transferSym_isHermitian β n).eigenvalues p₀) ^ κ

/-! ## 2. The length limit -/

/-- **AT FIXED WIDTH AND FIXED SEPARATION, THE TWO-POINT FUNCTION CONVERGES AS THE STRIP GROWS.**
The separation is written `κ` and the length `M + κ`, so that `κ` is a natural number held fixed
while the `Fin` it lives in grows with `M`.

Both the numerator and the denominator are `∑ₚ cₚ · (λₚ/λ_{p₀})^(M+1)` for weights `c` that do not
depend on `M`, so `TransferPowerSum.tendsto_weighted_ratio_pow` — extracted from
`partition2_div_top_pow_tendsto_one`'s proof for exactly this reason — supplies both limits, and
the denominator's is `λ_{p₀}^κ ≠ 0`. -/
theorem corr2Sep_tendsto (β : ℝ) (n : ℕ) (i : Fin (n + 1)) (κ : ℕ) :
    ∃ p₀ : Col n,
      (∀ j, (transferSym_isHermitian β n).eigenvalues j
          ≤ (transferSym_isHermitian β n).eigenvalues p₀) ∧
      0 < (transferSym_isHermitian β n).eigenvalues p₀ ∧
      Tendsto (fun M : ℕ =>
          corr2Sep β n (M + κ) ⟨κ, Nat.lt_succ_of_le (Nat.le_add_left κ M)⟩ i)
        atTop (𝓝 (corr2SepInf β n i p₀ κ)) := by
  classical
  have hpos : ∀ a b : Col n, 0 < transferSym β n a b := transferSym_entries_pos β n
  obtain ⟨p₀, hp₀⟩ := PerronGap.exists_max_eigenvalue (transferSym_isHermitian β n)
  have hp₀pos : 0 < (transferSym_isHermitian β n).eigenvalues p₀ :=
    PerronGap.eigenvalue_max_pos _ hpos hp₀
  have hp₀ne : (transferSym_isHermitian β n).eigenvalues p₀ ≠ 0 := ne_of_gt hp₀pos
  refine ⟨p₀, hp₀, hp₀pos, ?_⟩
  have hnum := TransferPowerSum.tendsto_weighted_ratio_pow (transferSym_isHermitian β n) hpos hp₀
    (fun p => ∑ q, ‖spinEigen β n i p q‖ ^ 2 * (transferSym_isHermitian β n).eigenvalues q ^ κ)
  have hden := TransferPowerSum.tendsto_weighted_ratio_pow (transferSym_isHermitian β n) hpos hp₀
    (fun p => (transferSym_isHermitian β n).eigenvalues p ^ κ)
  have hdiv := hnum.div hden (pow_ne_zero κ hp₀ne)
  have hlim : (∑ q, ‖spinEigen β n i p₀ q‖ ^ 2
        * (transferSym_isHermitian β n).eigenvalues q ^ κ)
        / (transferSym_isHermitian β n).eigenvalues p₀ ^ κ
      = corr2SepInf β n i p₀ κ := by
    rw [corr2SepInf, Finset.sum_div]
    exact Finset.sum_congr rfl fun q _ => by rw [div_pow, mul_div_assoc]
  rw [← hlim]
  refine Tendsto.congr (fun M => ?_) hdiv
  simp only [Pi.div_apply]
  have hnumM : (∑ p, (∑ q, ‖spinEigen β n i p q‖ ^ 2
          * (transferSym_isHermitian β n).eigenvalues q ^ κ)
        * ((transferSym_isHermitian β n).eigenvalues p
            / (transferSym_isHermitian β n).eigenvalues p₀) ^ (M + 1))
      = (∑ p, ∑ q, ‖spinEigen β n i p q‖ ^ 2
            * ((transferSym_isHermitian β n).eigenvalues q ^ κ
              * (transferSym_isHermitian β n).eigenvalues p ^ (M + 1)))
        / (transferSym_isHermitian β n).eigenvalues p₀ ^ (M + 1) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [div_pow, ← mul_div_assoc, mul_assoc]
  have hdenM : (∑ p, (transferSym_isHermitian β n).eigenvalues p ^ κ
        * ((transferSym_isHermitian β n).eigenvalues p
            / (transferSym_isHermitian β n).eigenvalues p₀) ^ (M + 1))
      = (∑ p, (transferSym_isHermitian β n).eigenvalues p ^ (M + κ + 1))
        / (transferSym_isHermitian β n).eigenvalues p₀ ^ (M + 1) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [div_pow, ← mul_div_assoc, ← pow_add, show κ + (M + 1) = M + κ + 1 from by omega]
  have hval : ((⟨κ, Nat.lt_succ_of_le (Nat.le_add_left κ M)⟩ : Fin (M + κ + 1)) : ℕ) = κ := rfl
  rw [hnumM, hdenM, div_div_div_cancel_right₀ (pow_ne_zero (M + 1) hp₀ne),
    corr2Sep_eq_spectral, hval, show M + κ + 1 - κ = M + 1 from by omega]

/-! ## 3. That the limit is the right one, and not vacuous

`IsingTwoPoint.corr2Sep_zero` proves `⟨σ₀σ₀⟩ = 1` from `spin_sq`, by reindexing a configuration
sum with no matrix algebra anywhere in it. §2's limit at zero separation is therefore forced to be
`1`, and it is — for a reason sharing no step with that proof: the observable squares to the
identity, so its eigenbasis reading does too, so each row of squared entries sums to one. A
mis-stated `corr2Sep_eq_spectral` — a transposed index, a wrong row of `B`, a dropped
normalisation — would fail this. -/

/-- The spin observable squares to the identity, because a spin does. -/
theorem spinDiag_mul_self (n : ℕ) (i : Fin (n + 1)) :
    (Matrix.diagonal fun σ : Col n => spin (σ i))
        * (Matrix.diagonal fun σ : Col n => spin (σ i)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  exact (Matrix.diagonal_eq_diagonal_iff.mpr fun σ : Col n => spin_sq (σ i)).trans
    Matrix.diagonal_one

theorem eigenvectorUnitary_conjTranspose_mul (β : ℝ) (n : ℕ) :
    ((transferSym_isHermitian β n).eigenvectorUnitary : Matrix (Col n) (Col n) ℝ)ᴴ
      * ((transferSym_isHermitian β n).eigenvectorUnitary : Matrix (Col n) (Col n) ℝ) = 1 := by
  have h := Matrix.UnitaryGroup.star_mul_self (transferSym_isHermitian β n).eigenvectorUnitary
  rwa [Matrix.star_eq_conjTranspose] at h

/-- **AND SO DOES ITS EIGENBASIS READING**, the unitary cancelling in the middle — which is
`IsingTwoPointSpectral.conj_mul_conj`, at its second instantiation. -/
theorem spinEigen_mul_self (β : ℝ) (n : ℕ) (i : Fin (n + 1)) :
    spinEigen β n i * spinEigen β n i = 1 := by
  have hUs := eigenvectorUnitary_conjTranspose_mul β n
  rw [spinEigen, conj_mul_conj _ _ _ _ (mul_eq_one_comm.mp hUs), spinDiag_mul_self,
    Matrix.mul_one, hUs]

/-- **THE SQUARED ENTRIES OF EACH ROW SUM TO ONE.** The diagonal of `B² = 1`, with `B` symmetric. -/
theorem sum_sq_spinEigen_row (β : ℝ) (n : ℕ) (i : Fin (n + 1)) (p : Col n) :
    ∑ q, ‖spinEigen β n i p q‖ ^ 2 = 1 := by
  have h := congrArg (fun X : Matrix (Col n) (Col n) ℝ => X p p) (spinEigen_mul_self β n i)
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [← h]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Real.norm_eq_abs, sq_abs, pow_two, spinEigen_symm β n i q p]

/-- **THE NORMALISATION CHECK, AND IT IS NOT A TAUTOLOGY.** At zero separation the limit is `1`,
which is what `IsingTwoPoint.corr2Sep_zero` says every finite strip already gives. -/
theorem corr2SepInf_zero (β : ℝ) (n : ℕ) (i : Fin (n + 1)) (p₀ : Col n) :
    corr2SepInf β n i p₀ 0 = 1 := by
  rw [corr2SepInf]
  simpa using sum_sq_spinEigen_row β n i p₀

/-! ## 4. The diagonal term, and what it forbids -/

/-- **THE `q = p₀` TERM CARRIES NO SEPARATION.** Its ratio is `λ_{p₀}/λ_{p₀} = 1`, so it is
`‖B_{p₀p₀}‖²` for every `κ`. Stated before anything asymptotic because it is what makes
*"the two-point function decays to zero"* the wrong target. -/
theorem corr2SepInf_eq_diag_add (β : ℝ) (n : ℕ) (i : Fin (n + 1)) {p₀ : Col n}
    (hp₀pos : 0 < (transferSym_isHermitian β n).eigenvalues p₀) (κ : ℕ) :
    corr2SepInf β n i p₀ κ
      = ‖spinEigen β n i p₀ p₀‖ ^ 2
        + ∑ q ∈ univ.erase p₀, ‖spinEigen β n i p₀ q‖ ^ 2
            * ((transferSym_isHermitian β n).eigenvalues q
                / (transferSym_isHermitian β n).eigenvalues p₀) ^ κ := by
  classical
  rw [corr2SepInf, ← Finset.add_sum_erase univ _ (mem_univ p₀),
    div_self (ne_of_gt hp₀pos), one_pow, mul_one]

/-- **SO THE INFINITE STRIP'S TWO-POINT FUNCTION TENDS TO THE DIAGONAL TERM AS THE SEPARATION
GROWS**, and not to zero. Same engine as §2, at the same weights, with the exponent now the
separation rather than the length. -/
theorem corr2SepInf_tendsto_diag (β : ℝ) (n : ℕ) (i : Fin (n + 1)) {p₀ : Col n}
    (hp₀ : ∀ j, (transferSym_isHermitian β n).eigenvalues j
        ≤ (transferSym_isHermitian β n).eigenvalues p₀) :
    Tendsto (fun κ : ℕ => corr2SepInf β n i p₀ κ) atTop
      (𝓝 (‖spinEigen β n i p₀ p₀‖ ^ 2)) := by
  have h := TransferPowerSum.tendsto_weighted_ratio_pow (transferSym_isHermitian β n)
    (transferSym_entries_pos β n) hp₀ (fun q => ‖spinEigen β n i p₀ q‖ ^ 2)
  have h2 : Tendsto (fun κ : ℕ => corr2SepInf β n i p₀ (κ + 1)) atTop
      (𝓝 (‖spinEigen β n i p₀ p₀‖ ^ 2)) := h
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp h2

/-- **AND THE OBJECT THAT GOES TO ZERO IS THE CONNECTED FUNCTION.** This is the correct shape of a
clustering statement for the strip, and the reason `corr2SepInf_eq_diag_add` is stated at all.

**No rate.** See the header: an exponential bound is one step further and is not taken here. -/
theorem corr2SepInf_connected_tendsto_zero (β : ℝ) (n : ℕ) (i : Fin (n + 1)) {p₀ : Col n}
    (hp₀ : ∀ j, (transferSym_isHermitian β n).eigenvalues j
        ≤ (transferSym_isHermitian β n).eigenvalues p₀) :
    Tendsto (fun κ : ℕ => corr2SepInf β n i p₀ κ - ‖spinEigen β n i p₀ p₀‖ ^ 2) atTop (𝓝 0) := by
  have h := (corr2SepInf_tendsto_diag β n i hp₀).sub_const (‖spinEigen β n i p₀ p₀‖ ^ 2)
  simpa using h

/-! ## 5. The rate

§4 says the connected function goes to zero. This says how fast, and the constant is `1`:
`|⟨σ₀σ_κ⟩_∞ − ‖B_{p₀p₀}‖²| ≤ rᵏ` with `r` the largest ratio off the top index. The `1` is not a
convenience — it is §3's row sum, since the off-diagonal squared entries are part of a family
summing to one. -/

/-- **THE LARGEST RATIO OFF THE TOP INDEX IS BELOW ONE**, and it is attained, so this is a number
and not an infimum. `Col n` has `2ⁿ⁺¹ ≥ 2` elements (`IsingTransfer2D.card_Col`), which is what
makes the set it is a maximum over nonempty; a one-element index type would make the statement
vacuous and the bound below trivial. -/
theorem exists_subTop_ratio (β : ℝ) (n : ℕ) {p₀ : Col n}
    (hp₀ : ∀ j, (transferSym_isHermitian β n).eigenvalues j
        ≤ (transferSym_isHermitian β n).eigenvalues p₀) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ q ∈ univ.erase p₀,
      |(transferSym_isHermitian β n).eigenvalues q
        / (transferSym_isHermitian β n).eigenvalues p₀| ≤ r := by
  classical
  have hpos : ∀ a b : Col n, 0 < transferSym β n a b := transferSym_entries_pos β n
  have hp₀pos : 0 < (transferSym_isHermitian β n).eigenvalues p₀ :=
    PerronGap.eigenvalue_max_pos _ hpos hp₀
  obtain ⟨q₁, hq₁⟩ := exists_ne p₀
  have hne : (univ.erase p₀).Nonempty := ⟨q₁, Finset.mem_erase.mpr ⟨hq₁, mem_univ q₁⟩⟩
  obtain ⟨qm, hqm, hmax⟩ := Finset.exists_max_image (univ.erase p₀)
    (fun q => |(transferSym_isHermitian β n).eigenvalues q
      / (transferSym_isHermitian β n).eigenvalues p₀|) hne
  have hlt : ∀ q ∈ univ.erase p₀,
      |(transferSym_isHermitian β n).eigenvalues q
        / (transferSym_isHermitian β n).eigenvalues p₀| < 1 := by
    intro q hq
    have hqne : q ≠ p₀ := (Finset.mem_erase.mp hq).1
    have hvne : (transferSym_isHermitian β n).eigenvalues q
        ≠ (transferSym_isHermitian β n).eigenvalues p₀ := fun h =>
      hqne (TransferPowerSum.index_eq_of_eigenvalues_eq_top _ hpos hp₀ h)
    rw [abs_div, abs_of_pos hp₀pos, div_lt_one hp₀pos]
    exact PerronGap.abs_eigenvalues_lt_of_ne _ hpos hp₀ hvne
  exact ⟨_, abs_nonneg _, hlt qm hqm, fun q hq => hmax q hq⟩

/-- **EXPONENTIAL CLUSTERING FOR THE STRIP OF FIXED WIDTH.** The connected two-point function of
the infinite strip is bounded by `rᵏ`, with `r < 1` the largest eigenvalue ratio off the top index.

**Read what this is about.** The strip has a FIXED width `n` and the limit taken to reach
`corr2SepInf` was in the length. `r` depends on `n` — it is built from that width's eigenvalues —
and **nothing here says it stays below one as the width grows**, which is `WALLS` §W4 §6 item 3's
open sentence and is untouched. What this is, is exponential clustering for one strip. -/
theorem corr2SepInf_connected_le (β : ℝ) (n : ℕ) (i : Fin (n + 1)) {p₀ : Col n}
    (hp₀ : ∀ j, (transferSym_isHermitian β n).eigenvalues j
        ≤ (transferSym_isHermitian β n).eigenvalues p₀) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ κ : ℕ,
      |corr2SepInf β n i p₀ κ - ‖spinEigen β n i p₀ p₀‖ ^ 2| ≤ r ^ κ := by
  classical
  have hpos : ∀ a b : Col n, 0 < transferSym β n a b := transferSym_entries_pos β n
  have hp₀pos : 0 < (transferSym_isHermitian β n).eigenvalues p₀ :=
    PerronGap.eigenvalue_max_pos _ hpos hp₀
  obtain ⟨r, hr0, hr1, hrle⟩ := exists_subTop_ratio β n hp₀
  refine ⟨r, hr0, hr1, fun κ => ?_⟩
  rw [corr2SepInf_eq_diag_add β n i hp₀pos κ, add_sub_cancel_left]
  calc |∑ q ∈ univ.erase p₀, ‖spinEigen β n i p₀ q‖ ^ 2
          * ((transferSym_isHermitian β n).eigenvalues q
              / (transferSym_isHermitian β n).eigenvalues p₀) ^ κ|
      ≤ ∑ q ∈ univ.erase p₀, |‖spinEigen β n i p₀ q‖ ^ 2
          * ((transferSym_isHermitian β n).eigenvalues q
              / (transferSym_isHermitian β n).eigenvalues p₀) ^ κ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ univ.erase p₀, ‖spinEigen β n i p₀ q‖ ^ 2 * r ^ κ := by
        refine Finset.sum_le_sum fun q hq => ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hrle q hq) κ)
          (sq_nonneg _)
    _ = (∑ q ∈ univ.erase p₀, ‖spinEigen β n i p₀ q‖ ^ 2) * r ^ κ := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ q, ‖spinEigen β n i p₀ q‖ ^ 2) * r ^ κ := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr0 κ)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun q _ _ => sq_nonneg _
    _ = r ^ κ := by rw [sum_sq_spinEigen_row, one_mul]

end IsingTwoPointLimit
