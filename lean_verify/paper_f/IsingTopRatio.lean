/-
  IsingTopRatio.lean — the top eigenvalue index and the sub-top ratio, by name,
  and the strip's decay bound with no hypotheses left in it.

  WHY. Everything the strip chain proves about decay is stated at a `p₀`
  supplied as a HYPOTHESIS — `(hp₀ : ∀ j, λ j ≤ λ p₀)` — and at an `r`
  supplied by an EXISTENTIAL. Both are fine for a theorem about one strip and
  both are fatal for the question `WALLS` §W4 §6 item 3 actually asks, which
  is what happens to that `r` as the width `n` grows. **A quantity that only
  ever appears bound cannot be said to have a limit.** So this file writes
  both down as functions of `β` and `n` and nothing else.

  WHAT THIS FILE PROVES:
  1. **`topIndex`** — the index at which the transfer matrix's eigenvalue list
     is largest, and **`topIndex_max`**, which is the hypothesis `hp₀` every
     theorem downstream of `IsingTwoPointLimit` has been carrying. It is
     `Finite.exists_max` at `Col n`, which is finite and nonempty because it
     is `Fin (n+1) → Bool`. **The argmax has been derived FOUR TIMES INSIDE
     PROOFS and never named** — `PerronGap`, `PerronVector`, `RayleighPow`
     each open with `Finset.exists_max_image` on an eigenvalue list, and
     `IsingTwoPointLimit.exists_subTop_ratio` does it on the erased set — so
     the hypothesis was dischargeable from the day the first of them was
     written, and every theorem above them took it instead.
  2. **`subTopRatio`** — `maxᵩ≠ₚ₀ |λ_q / λ_{p₀}|`, the largest eigenvalue
     ratio off the top index, as a `Finset.sup'` over `univ.erase (topIndex)`.
     `subTopRatio_lt_one` is the Perron gap and `le_subTopRatio` is the
     defining bound. `IsingTwoPointLimit.exists_subTop_ratio` is exactly the
     statement that this thing exists; `subTopRatio_isWitness` closes that
     loop, so the existential and the name are not two facts.
  3. **`corr2SepInf_abs_le_subTopRatio`** — the payoff, and it is the point of
     the file: `|⟨σ₀σ_κ⟩_∞| ≤ (subTopRatio β n)^κ`, **with no hypotheses at
     all** beyond `β`, `n`, a site and a separation. Every input to the
     estimate is now a function of the width.
  4. **`UniformSubTopRatio`** — and therefore item 3 can be WRITTEN DOWN, in
     the estate's convention for naming a gap as a `def`. It is
     `∃ δ > 0, ∀ n, subTopRatio β n ≤ 1 - δ`, and
     `decay_uniform_of_uniformSubTopRatio` proves it is the right statement by
     showing what it delivers: one rate that works at every width.

  WHAT IS NOT PROVED, AND IT IS THE WHOLE OF ITEM 3.
  **`UniformSubTopRatio β` is not proved for any `β`, and no route to it is
  recorded here.** What this file changes is that the sentence now has a
  subject. Before it, "the ratio stays below one as the width grows" could
  not be typed, because neither the ratio nor the index it is measured from
  existed as a function of the width.

  **AND IT IS STATED AT A FIXED `β` ON PURPOSE.** `subTopRatio_lt_one` holds
  at every `β` and every `n`, and a reader may take the uniform statement to
  be the same fact with a quantifier moved. It is not, and the difference is
  physical: a strip of any FIXED width is a one-dimensional system and has no
  phase transition, which is why `subTopRatio β n < 1` needs no hypothesis on
  `β`; the two-dimensional model it approximates as `n → ∞` does have one.
  So a proof of `UniformSubTopRatio β` MUST use `β`, and any argument that
  establishes it uniformly in `β` is wrong. **That is a constraint on the
  shape of a proof, not a proof, and the estate proves nothing about a
  critical temperature** — `IsingFiniteVolume` and everything above it are
  stated at arbitrary `β` throughout.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import IsingMagnetisationVanishes

namespace IsingTopRatio

open Filter Topology Finset
open IsingTransfer2D IsingTransferSym IsingTwoPoint IsingTwoPointSpectral IsingTwoPointLimit
open IsingMagnetisationVanishes

open scoped Matrix

variable {n : ℕ}

/-! ## 1. The top index, and the hypothesis that was always dischargeable

`Col n` is `Fin (n+1) → Bool`, so it is finite and nonempty, and a real-valued function on it
attains its maximum. `Finite.exists_max` says exactly that and its conclusion is exactly the `hp₀`
carried by `IsingTwoPointLimit` and `IsingMagnetisationVanishes`. -/

/-- **THE INDEX OF THE LARGEST EIGENVALUE** of the symmetrised transfer matrix. -/
noncomputable def topIndex (β : ℝ) (n : ℕ) : Col n :=
  (Finite.exists_max (transferSym_isHermitian β n).eigenvalues).choose

/-- **AND IT IS THE MAXIMUM**, which is the hypothesis every decay theorem downstream has taken. -/
theorem topIndex_max (β : ℝ) (n : ℕ) (j : Col n) :
    (transferSym_isHermitian β n).eigenvalues j
      ≤ (transferSym_isHermitian β n).eigenvalues (topIndex β n) :=
  (Finite.exists_max (transferSym_isHermitian β n).eigenvalues).choose_spec j

/-- **THE TOP EIGENVALUE IS STRICTLY POSITIVE.** `PerronGap.eigenvalue_max_pos` at `topIndex`;
the strict positivity of the matrix entries is `transferSym_pos`. -/
theorem topIndex_pos (β : ℝ) (n : ℕ) :
    0 < (transferSym_isHermitian β n).eigenvalues (topIndex β n) :=
  PerronGap.eigenvalue_max_pos _ (transferSym_entries_pos β n) (topIndex_max β n)

/-- **THERE IS SOMETHING OFF THE TOP INDEX**, which is what makes the maximum in §2 a maximum of
something. The proof runs on `Nontrivial (Col n)` — found by instance search from `Bool` being
nontrivial and `Fin (n+1)` inhabited — and not on `IsingTransfer2D.card_Col`; the cardinality
`2ⁿ⁺¹ ≥ 2` is the same fact counted rather than witnessed, and is not what is used here. -/
theorem erase_topIndex_nonempty (β : ℝ) (n : ℕ) : (univ.erase (topIndex β n)).Nonempty := by
  obtain ⟨q, hq⟩ := exists_ne (topIndex β n)
  exact ⟨q, Finset.mem_erase.mpr ⟨hq, mem_univ q⟩⟩

/-! ## 2. The sub-top ratio

The number `IsingTwoPointLimit.exists_subTop_ratio` asserts to exist, written down. It is a
`Finset.sup'` rather than an `iSup` so that it is attained and no completeness argument is
involved; §1's nonemptiness is what `sup'` needs. -/

/-- **THE LARGEST EIGENVALUE RATIO OFF THE TOP INDEX**, `maxᵩ≠ₚ₀ |λ_q / λ_{p₀}|`. -/
noncomputable def subTopRatio (β : ℝ) (n : ℕ) : ℝ :=
  (univ.erase (topIndex β n)).sup' (erase_topIndex_nonempty β n) fun q =>
    |(transferSym_isHermitian β n).eigenvalues q
      / (transferSym_isHermitian β n).eigenvalues (topIndex β n)|

/-- **THE DEFINING BOUND**: every ratio off the top index is at most `subTopRatio`. -/
theorem le_subTopRatio (β : ℝ) (n : ℕ) {q : Col n} (hq : q ≠ topIndex β n) :
    |(transferSym_isHermitian β n).eigenvalues q
      / (transferSym_isHermitian β n).eigenvalues (topIndex β n)| ≤ subTopRatio β n :=
  Finset.le_sup' (fun q => |(transferSym_isHermitian β n).eigenvalues q
    / (transferSym_isHermitian β n).eigenvalues (topIndex β n)|)
    (Finset.mem_erase.mpr ⟨hq, mem_univ q⟩)

theorem subTopRatio_nonneg (β : ℝ) (n : ℕ) : 0 ≤ subTopRatio β n := by
  obtain ⟨q, hq⟩ := erase_topIndex_nonempty β n
  exact le_trans (abs_nonneg _) (le_subTopRatio β n (Finset.mem_erase.mp hq).1)

/-- **THE PERRON GAP, AS A STATEMENT ABOUT A NAMED NUMBER.** `subTopRatio β n < 1` at every width
and every `β`. Read §4 before reading a limit into this: the quantifier order is the whole item. -/
theorem subTopRatio_lt_one (β : ℝ) (n : ℕ) : subTopRatio β n < 1 := by
  have hpos : ∀ a b : Col n, 0 < transferSym β n a b := transferSym_entries_pos β n
  have hrfl : subTopRatio β n
      = (univ.erase (topIndex β n)).sup' (erase_topIndex_nonempty β n) fun q =>
        |(transferSym_isHermitian β n).eigenvalues q
          / (transferSym_isHermitian β n).eigenvalues (topIndex β n)| := rfl
  rw [hrfl, Finset.sup'_lt_iff]
  intro q hq
  have hqne : q ≠ topIndex β n := (Finset.mem_erase.mp hq).1
  have hvne : (transferSym_isHermitian β n).eigenvalues q
      ≠ (transferSym_isHermitian β n).eigenvalues (topIndex β n) := fun h =>
    hqne (TransferPowerSum.index_eq_of_eigenvalues_eq_top _ hpos (topIndex_max β n) h)
  rw [abs_div, abs_of_pos (topIndex_pos β n), div_lt_one (topIndex_pos β n)]
  exact PerronGap.abs_eigenvalues_lt_of_ne _ hpos (topIndex_max β n) hvne

/-- **AND IT IS THE EXISTENTIAL'S WITNESS**, so the name and
`IsingTwoPointLimit.exists_subTop_ratio` are one fact and not two (`ERRATUM 201`). -/
theorem subTopRatio_isWitness (β : ℝ) (n : ℕ) :
    0 ≤ subTopRatio β n ∧ subTopRatio β n < 1 ∧ ∀ q ∈ univ.erase (topIndex β n),
      |(transferSym_isHermitian β n).eigenvalues q
        / (transferSym_isHermitian β n).eigenvalues (topIndex β n)| ≤ subTopRatio β n :=
  ⟨subTopRatio_nonneg β n, subTopRatio_lt_one β n,
    fun _ hq => le_subTopRatio β n (Finset.mem_erase.mp hq).1⟩

/-! ## 3. The decay bound with nothing bound

`IsingMagnetisationVanishes.corr2SepInf_abs_le` says there EXISTS an `r < 1` bounding the infinite
strip's two-point function, at a `p₀` given by hypothesis. Both are now supplied. -/

/-- **EXPONENTIAL DECAY OF THE STRIP'S TWO-POINT FUNCTION, WITH NO HYPOTHESES.**
`|⟨σ₀σ_κ⟩_∞| ≤ (subTopRatio β n)^κ` at every width `n`, site `i` and separation `κ`.

The vanishing of the diagonal term is `spinEigen_top_eq_zero` — the global spin flip, conjugated
into the eigenbasis, commutes with a diagonal matrix — and the sum over the rest is
`corr2SepInf_connected_le_of_ratio_le` at `r = subTopRatio β n`. -/
theorem corr2SepInf_abs_le_subTopRatio (β : ℝ) (n : ℕ) (i : Fin (n + 1)) (κ : ℕ) :
    |corr2SepInf β n i (topIndex β n) κ| ≤ subTopRatio β n ^ κ := by
  have h := corr2SepInf_connected_le_of_ratio_le β n i (topIndex_pos β n)
    (subTopRatio_nonneg β n) (fun q hq => le_subTopRatio β n (Finset.mem_erase.mp hq).1) κ
  rwa [spinEigen_top_eq_zero β n i (topIndex_max β n), norm_zero, zero_pow (by norm_num),
    sub_zero] at h

/-! ## 4. What is not proved, named

`WALLS` §W4 §6 item 3, in the estate's convention for a gap: a `def` whose own doc comment says
what is missing, so that `check_ledger.py --gapmarks` tracks it and a theorem concluding it would
be found automatically. -/

/-- **NOT PROVED HERE, AND THIS IS `WALLS` §W4 §6 item 3.** That the sub-top ratio stays below one
UNIFORMLY IN THE WIDTH: one `δ > 0` serving every `n` at once.

**What separates it from `subTopRatio_lt_one`** is only the order of two quantifiers, and that is
the entire remaining content of the item. The estate proves `∀ n, subTopRatio β n < 1`; this asks
for `∃ δ > 0, ∀ n, subTopRatio β n ≤ 1 - δ`. Nothing here proves it and no route is recorded.

**It is stated at a fixed `β` because it is not expected to hold at every `β`** — that expectation
is physical and is NOT proved anywhere in this estate; the header says why and says so. -/
def UniformSubTopRatio (β : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, subTopRatio β n ≤ 1 - δ

/-! **IS IT INHABITED?** A `Prop` naming a gap is worth less if nothing can satisfy it, and this
one is **not proved for any `β` here**. The obvious candidate is `β = 0`: every entry of
`transfer2 0 n` is `exp 0 = 1` and `halfIntra 0 n` is the identity, so `transferSym 0 n` should be
the all-ones matrix, which has rank one — top eigenvalue `2ⁿ⁺¹` and every other eigenvalue `0` —
giving `subTopRatio 0 n = 0` at every width and `UniformSubTopRatio 0` with `δ = 1`. **That is a
sketch and not a theorem**: none of it is proved below, the eigenvalue list of a rank-one matrix is
not in this estate, and the word "should" is doing real work. It is written here because it names
the next unit and because a reader is entitled to know whether the target is known to be
satisfiable. It is not — not even at infinite temperature.

**⚠ SUPERSEDED THE SAME DAY, AND BY THE UNIT THIS PARAGRAPH NAMED** (`ERRATUM 94`: the paragraph
above is kept as written). **`IsingTopRatioZero.uniformSubTopRatio_zero` proves
`UniformSubTopRatio 0`**, with `δ = 1`, so the target IS satisfiable. The sketch above is the proof
in outline and the step it called missing was supplied rather than assumed:
`eigenvalues_sq_eq_of_mul_self` — a Hermitian `A` with `A * A = c • A` has every eigenvalue
satisfying `λ² = c·λ` — which needs no eigenvalue list for a rank-one matrix and no rank at all,
only the eigenvector basis used twice. **What does NOT change**: the wall does not move, nothing
here or there says anything about `β ≠ 0`, and `β = 0` is the degenerate case where the matrix has
rank one and non-interacting spins do not correlate. Read the other way it is a filter on
strategies — **an argument that would also work at `β = 0` is not yet doing the work.** -/

/-- **AND THIS IS WHAT IT WOULD BUY**, which is why the `def` above is the right statement of the
item rather than a name attached to nothing: one exponential rate, valid at every width at once. -/
theorem decay_uniform_of_uniformSubTopRatio {β : ℝ} (h : UniformSubTopRatio β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (i : Fin (n + 1)) (κ : ℕ),
      |corr2SepInf β n i (topIndex β n) κ| ≤ (1 - δ) ^ κ := by
  obtain ⟨δ, hδ, hle⟩ := h
  refine ⟨δ, hδ, fun n i κ => le_trans (corr2SepInf_abs_le_subTopRatio β n i κ) ?_⟩
  exact pow_le_pow_left₀ (subTopRatio_nonneg β n) (hle n) κ

end IsingTopRatio
