import TransferPowerSum
import RayleighMatrix

/-!
# A spectral gap from the entry ratio alone, and why it cannot reach `W4`'s item

`WALLS §W4` item 3 is `IsingTopRatio.UniformSubTopRatio β` — the sub-top eigenvalue ratio of the
Ising transfer matrix bounded away from one **uniformly in the width** — and the wall records that
it is *"proved at no `β` but `0`, with no route recorded"*. This file records a route, proves it in
general, and shows exactly where it stops.

> `subTop_ratio_le` — for a symmetric matrix whose entries all lie in `[a, b]` with `0 < a`, every
> eigenvalue off the top satisfies `|λ / λ_top| ≤ √(b² − a²) / a`. **The bound does not mention the
> size of the matrix.**

So `b < a√2` gives a gap that is uniform in the dimension, which is the shape `UniformSubTopRatio`
asks for.

## Why it needs no perturbation theory

The usual route to a uniform gap is an eigenvalue-perturbation estimate, and Mathlib has none —
`Weyl` and its relatives are absent (probed by shape). What replaces it here is two facts the
estate already owns:

* `TransferPowerSum.trace_pow_eq_sum_eigenvalues_pow` at `k = 2`, which makes `∑ λ²` the sum of the
  squared ENTRIES — a quantity the hypothesis bounds directly;
* `RayleighMatrix.quadForm_le_of_eigenvalues_le` at the all-ones vector, which bounds the top
  eigenvalue BELOW by `N · a`.

Subtracting the second from the first leaves every other eigenvalue squared below `N²(b² − a²)`,
and the two factors of `N` cancel in the ratio. **The cancellation is the whole content**: each
half is proportional to the dimension and the quotient is not.

## Where it stops, stated as a number rather than as a difficulty

`IsingTransferSym.transferSym_apply` gives the entries as
`exp(β·intra σ/2) · exp(β·inter σ τ) · exp(β·intra τ/2)`. **Read from the definitions rather than
recalled**: a column is `Col n = Fin (n+1) → Bool`, so it has `n + 1` sites, and both
`IsingTransfer2D.intra` and `.inter` are sums of `n + 1` products of two `±1` spins — each ranges
over `[−(n+1), n+1]`. The exponent therefore ranges over `[−2β(n+1), 2β(n+1)]` and the entry ratio
`b/a` of `transferSym β n` is at most `exp(4β(n+1))` and at least `exp(4β(n+1))`'s reciprocal
regime — in either direction, **it grows without bound in the width at every `β > 0`**, while the
criterion needs it below `√2`. Hence:

* at `β = 0` every entry is `exp 0 = 1`, the criterion gives ratio `0`, and
  `IsingTopRatio.uniformSubTopRatio_zero`'s content is recovered from a general statement —
  `ratio_zero_of_constant_entries` below;
* **at every `β > 0` this route is silent, and not because the estimate is lossy.** The quantity it
  consumes is already unbounded in `n`.

**That is a recorded dead end, not a step.** `W4`'s item does not move, and the file says so: what
would be needed is an estimate that sees the transfer matrix's STRUCTURE — that the large entries
are few and correlated across rows — where this one sees only their range. The classical route with
that property is the Birkhoff–Hopf contraction coefficient, which needs the Hilbert projective
metric. **Probed, not assumed**: `grep -rn Birkhoff Mathlib` returns three hits, two of them
Poincaré–Birkhoff–Witt and one a comment in `Order/Group/Unbundled/Abs.lean`, and there is no
projective metric of any kind. So that route is a build and not a citation.
-/

namespace SpectralEntryRatio

open Finset Matrix RayleighMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

/-! ## 1. The sum of squared eigenvalues is the sum of squared entries -/

/-- **`∑ λ² = ∑∑ Aᵢⱼ²`** for a real symmetric matrix. `TransferPowerSum`'s trace identity at
`k = 2`, with the trace of `A²` expanded entrywise and symmetry used once. -/
theorem sum_sq_eigenvalues (hA : A.IsHermitian) :
    ∑ j, (hA.eigenvalues j) ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 := by
  have htr := TransferPowerSum.trace_pow_eq_sum_eigenvalues_pow (𝕜 := ℝ) hA 2
  have hexp : (A ^ 2).trace = ∑ i, ∑ j, (A i j) ^ 2 := by
    simp only [pow_two, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => ?_
    have hsym : A j x = A x j := by
      have h := hA.apply x j
      simpa using h
    rw [hsym]
  rw [← hexp, htr]
  simp

/-! ## 2. The top eigenvalue is at least `N · a` -/

/-- The all-ones vector, as a member of the space the eigenbasis lives in. -/
noncomputable def onesVec (ι : Type*) [Fintype ι] : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun _ => (1 : ℝ))

omit [DecidableEq ι] in
theorem inner_ones_ones : (inner ℝ (onesVec ι) (onesVec ι) : ℝ) = (Fintype.card ι : ℝ) := by
  rw [inner_expand]
  simp only [onesVec, WithLp.ofLp_toLp, mul_one]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

omit [DecidableEq ι] in
theorem quadForm_ones (A : Matrix ι ι ℝ) :
    (inner ℝ (onesVec ι) (mv A (onesVec ι)) : ℝ) = ∑ i, ∑ j, A i j := by
  rw [inner_expand]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mv_row]
  simp [onesVec]

/-- **THE TOP EIGENVALUE IS AT LEAST `N · a`**, from the Rayleigh quotient at the all-ones vector
and nothing else. -/
theorem card_mul_le_top (hA : A.IsHermitian) {a : ℝ} (hlo : ∀ i j, a ≤ A i j)
    {p₀ : ι} (htop : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues p₀) (hne : Nonempty ι) :
    (Fintype.card ι : ℝ) * a ≤ hA.eigenvalues p₀ := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hq := quadForm_le_of_eigenvalues_le hA htop (onesVec ι)
  rw [quadForm_ones, inner_ones_ones] at hq
  have hlow : ((Fintype.card ι : ℝ)) * ((Fintype.card ι : ℝ) * a) ≤ ∑ i, ∑ j, A i j := by
    have : ∀ i ∈ (univ : Finset ι), ((Fintype.card ι : ℝ)) * a ≤ ∑ j, A i j := by
      intro i _
      calc ((Fintype.card ι : ℝ)) * a
          = ∑ _j : ι, a := by rw [Finset.sum_const, Finset.card_univ]; ring
        _ ≤ ∑ j, A i j := Finset.sum_le_sum fun j _ => hlo i j
    calc ((Fintype.card ι : ℝ)) * ((Fintype.card ι : ℝ) * a)
        = ∑ _i : ι, ((Fintype.card ι : ℝ) * a) := by
          rw [Finset.sum_const, Finset.card_univ]; ring
      _ ≤ ∑ i, ∑ j, A i j := Finset.sum_le_sum this
  nlinarith [hlow, hq, hcard]

/-! ## 3. Every other eigenvalue is at most `N · √(b² − a²)` -/

/-- **THE OFF-TOP BOUND.** The squared eigenvalues sum to the squared entries, which is at most
`N²b²`; the top one alone is at least `N²a²`; what is left bounds each of the others. -/
theorem sq_off_top_le (hA : A.IsHermitian) {a b : ℝ} (ha : 0 ≤ a)
    (hlo : ∀ i j, a ≤ A i j) (hhi : ∀ i j, A i j ≤ b)
    {p₀ : ι} (htop : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues p₀) (hne : Nonempty ι)
    {q : ι} (hq : q ≠ p₀) :
    (hA.eigenvalues q) ^ 2 ≤ (Fintype.card ι : ℝ) ^ 2 * (b ^ 2 - a ^ 2) := by
  classical
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have htopge := card_mul_le_top hA hlo htop hne
  -- the two named eigenvalues sit inside the full sum
  have hpair : (hA.eigenvalues q) ^ 2 + (hA.eigenvalues p₀) ^ 2
      ≤ ∑ j, (hA.eigenvalues j) ^ 2 := by
    have hsub : ({q, p₀} : Finset ι) ⊆ univ := Finset.subset_univ _
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun j _ _ => sq_nonneg (hA.eigenvalues j))
    calc (hA.eigenvalues q) ^ 2 + (hA.eigenvalues p₀) ^ 2
        = ∑ j ∈ ({q, p₀} : Finset ι), (hA.eigenvalues j) ^ 2 := by
          rw [Finset.sum_pair hq]
      _ ≤ ∑ j, (hA.eigenvalues j) ^ 2 := this
  -- and the full sum is the squared entries
  have hentries : ∑ i, ∑ j, (A i j) ^ 2 ≤ (Fintype.card ι : ℝ) ^ 2 * b ^ 2 := by
    have hrow : ∀ i ∈ (univ : Finset ι), ∑ j, (A i j) ^ 2 ≤ (Fintype.card ι : ℝ) * b ^ 2 := by
      intro i _
      calc ∑ j, (A i j) ^ 2 ≤ ∑ _j : ι, b ^ 2 :=
            Finset.sum_le_sum fun j _ => by
              have h1 : a ≤ A i j := hlo i j
              have h2 : A i j ≤ b := hhi i j
              nlinarith
        _ = (Fintype.card ι : ℝ) * b ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ]; ring
    calc ∑ i, ∑ j, (A i j) ^ 2 ≤ ∑ _i : ι, ((Fintype.card ι : ℝ) * b ^ 2) :=
          Finset.sum_le_sum hrow
      _ = (Fintype.card ι : ℝ) ^ 2 * b ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ]; ring
  rw [sum_sq_eigenvalues hA] at hpair
  have hNa : (0 : ℝ) ≤ (Fintype.card ι : ℝ) * a := by positivity
  have hsqtop : ((Fintype.card ι : ℝ) * a) ^ 2 ≤ (hA.eigenvalues p₀) ^ 2 := by
    nlinarith [htopge, hNa]
  nlinarith [hpair, hentries, hsqtop]

/-! ## 4. The ratio, and it does not mention the dimension -/

/-- **THE CRITERION.** Every eigenvalue off the top is at most `√(b² − a²) / a` times the top one,
**with no dependence on the size of the matrix**. -/
theorem subTop_ratio_le (hA : A.IsHermitian) {a b : ℝ} (ha : 0 < a)
    (hlo : ∀ i j, a ≤ A i j) (hhi : ∀ i j, A i j ≤ b)
    {p₀ : ι} (htop : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues p₀) (hne : Nonempty ι)
    {q : ι} (hq : q ≠ p₀) :
    |hA.eigenvalues q / hA.eigenvalues p₀| ≤ Real.sqrt (b ^ 2 - a ^ 2) / a := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have htopge := card_mul_le_top hA hlo htop hne
  have htoppos : 0 < hA.eigenvalues p₀ := lt_of_lt_of_le (by positivity) htopge
  have hsq := sq_off_top_le hA ha.le hlo hhi htop hne hq
  have habs : |hA.eigenvalues q| ≤ (Fintype.card ι : ℝ) * Real.sqrt (b ^ 2 - a ^ 2) := by
    have hnn : (0 : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2 * (b ^ 2 - a ^ 2) :=
      le_trans (sq_nonneg _) hsq
    have : |hA.eigenvalues q| ≤ Real.sqrt ((Fintype.card ι : ℝ) ^ 2 * (b ^ 2 - a ^ 2)) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hsq
    calc |hA.eigenvalues q|
        ≤ Real.sqrt ((Fintype.card ι : ℝ) ^ 2 * (b ^ 2 - a ^ 2)) := this
      _ = (Fintype.card ι : ℝ) * Real.sqrt (b ^ 2 - a ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hcard.le]
  rw [abs_div, abs_of_pos htoppos, div_le_div_iff₀ htoppos ha]
  nlinarith [habs, htopge, Real.sqrt_nonneg (b ^ 2 - a ^ 2), hcard]

/-! ## 5. What it gives at `β = 0`, and what it cannot give beyond -/

/-- **THE CRITERION IS NOT VACUOUS AND ITS EXTREME CASE IS THE KNOWN ONE.** When every entry is
the same positive number the ratio is `0` — which is `IsingTopRatio.uniformSubTopRatio_zero`'s
content reached from a general statement rather than from the rank-one computation.

At `β = 0` every entry of the symmetrised transfer matrix is `exp 0 = 1`, so this applies with
`a = b = 1`. **At every `β > 0` it does not apply at any width beyond a `β`-dependent one**, because
the entry ratio of that matrix is `exp(Θ(β·n))`; see this file's header. -/
theorem ratio_zero_of_constant_entries (hA : A.IsHermitian) {c : ℝ} (hc : 0 < c)
    (hconst : ∀ i j, A i j = c)
    {p₀ : ι} (htop : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues p₀) (hne : Nonempty ι)
    {q : ι} (hq : q ≠ p₀) :
    hA.eigenvalues q = 0 := by
  have h := subTop_ratio_le hA hc (fun i j => (hconst i j).ge) (fun i j => (hconst i j).le)
    htop hne hq
  simp only [sub_self, Real.sqrt_zero, zero_div] at h
  have htopge := card_mul_le_top hA (fun i j => (hconst i j).ge) htop hne
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have htoppos : 0 < hA.eigenvalues p₀ := lt_of_lt_of_le (by positivity) htopge
  have hzero : hA.eigenvalues q / hA.eigenvalues p₀ = 0 :=
    abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  rw [div_eq_zero_iff] at hzero
  rcases hzero with h1 | h1
  · exact h1
  · exact absurd h1 (ne_of_gt htoppos)

/-! ## 6. The same criterion with the entry hypotheses removed -/

/-- **THE SUM OF ALL SQUARED RATIOS IS THE FROBENIUS NORM OVER THE TOP EIGENVALUE SQUARED.**
An identity, not an estimate: `sum_sq_eigenvalues` divided through by `λ_top²`. -/
theorem sum_sq_ratio_eq (hA : A.IsHermitian) (p₀ : ι) :
    ∑ j, (hA.eigenvalues j / hA.eigenvalues p₀) ^ 2
      = (∑ i, ∑ j, (A i j) ^ 2) / (hA.eigenvalues p₀) ^ 2 := by
  rw [← sum_sq_eigenvalues hA, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by rw [div_pow]

/-- **THE SHARP FORM, AND THE ENTRY HYPOTHESES ARE GONE.** Every off-top ratio squared is at most
`‖A‖_F²/λ_top² − 1`. §§1–4 arrive here through two crude bounds — `‖A‖_F² ≤ N²b²` and
`λ_top ≥ N·a` — and **those two bounds are the only thing the entry hypotheses were ever
buying**. -/
theorem sq_ratio_le_frobenius (hA : A.IsHermitian) {p₀ : ι} (hpos : 0 < hA.eigenvalues p₀)
    {q : ι} (hq : q ≠ p₀) :
    (hA.eigenvalues q / hA.eigenvalues p₀) ^ 2
      ≤ (∑ i, ∑ j, (A i j) ^ 2) / (hA.eigenvalues p₀) ^ 2 - 1 := by
  classical
  have hall := sum_sq_ratio_eq hA p₀
  have hsplit : ∑ j, (hA.eigenvalues j / hA.eigenvalues p₀) ^ 2
      = 1 + ∑ j ∈ univ.erase p₀, (hA.eigenvalues j / hA.eigenvalues p₀) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p₀), div_self (ne_of_gt hpos), one_pow]
  have hmem : q ∈ univ.erase p₀ := Finset.mem_erase.mpr ⟨hq, Finset.mem_univ q⟩
  have hle := Finset.single_le_sum
    (f := fun j => (hA.eigenvalues j / hA.eigenvalues p₀) ^ 2)
    (fun j _ => sq_nonneg _) hmem
  linarith [hall, hsplit, hle]

/-- **SO THE CRITERION IS `‖A‖_F² < 2·λ_top²`**, with no reference to entries at all. -/
theorem abs_ratio_lt_one_of_frobenius (hA : A.IsHermitian) {p₀ : ι}
    (hpos : 0 < hA.eigenvalues p₀)
    (hfro : ∑ i, ∑ j, (A i j) ^ 2 < 2 * (hA.eigenvalues p₀) ^ 2)
    {q : ι} (hq : q ≠ p₀) :
    |hA.eigenvalues q / hA.eigenvalues p₀| < 1 := by
  have hsq := sq_ratio_le_frobenius hA hpos hq
  have hpos2 : (0 : ℝ) < (hA.eigenvalues p₀) ^ 2 := by positivity
  have hdiv : (∑ i, ∑ j, (A i j) ^ 2) / (hA.eigenvalues p₀) ^ 2 < 2 := by
    rw [div_lt_iff₀ hpos2]; linarith
  have hlt : (hA.eigenvalues q / hA.eigenvalues p₀) ^ 2 < 1 := by linarith
  have habs : |hA.eigenvalues q / hA.eigenvalues p₀| ^ 2 < 1 := by rwa [sq_abs]
  nlinarith [abs_nonneg (hA.eigenvalues q / hA.eigenvalues p₀), habs]

/-- **AND IT IS A REFORMULATION RATHER THAN A SUFFICIENT CONDITION**, which is what makes it the
wrong tool for `W4` even in this sharp form: `‖A‖_F² < 2·λ_top²` says exactly that the sum of ALL
the off-top squared ratios is below one.

`IsingTopRatio.UniformSubTopRatio` asks only that the LARGEST of them stay below `1 − δ`. Over
`2ⁿ⁺¹` eigenvalues those are very different demands — a tail of `2ⁿ⁺¹` ratios each near `1/2` has
a maximum well inside the target and a sum of squares far above one. **So this route over-asks by
a factor that itself grows with the width**, and sharpening §§1–4 to their exact form does not
change that. The entry-ratio computation in this file's header shows where the crude version dies;
this shows that the sharp version was never going to be the right shape. -/
theorem frobenius_lt_iff_tail_lt_one (hA : A.IsHermitian) {p₀ : ι}
    (hpos : 0 < hA.eigenvalues p₀) :
    (∑ i, ∑ j, (A i j) ^ 2 < 2 * (hA.eigenvalues p₀) ^ 2)
      ↔ ∑ j ∈ univ.erase p₀, (hA.eigenvalues j / hA.eigenvalues p₀) ^ 2 < 1 := by
  classical
  have hpos2 : (0 : ℝ) < (hA.eigenvalues p₀) ^ 2 := by positivity
  have hall := sum_sq_ratio_eq hA p₀
  have hsplit : ∑ j, (hA.eigenvalues j / hA.eigenvalues p₀) ^ 2
      = 1 + ∑ j ∈ univ.erase p₀, (hA.eigenvalues j / hA.eigenvalues p₀) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p₀), div_self (ne_of_gt hpos), one_pow]
  rw [hsplit] at hall
  constructor
  · intro h
    have : (∑ i, ∑ j, (A i j) ^ 2) / (hA.eigenvalues p₀) ^ 2 < 2 := by
      rw [div_lt_iff₀ hpos2]; linarith
    linarith
  · intro h
    have : (∑ i, ∑ j, (A i j) ^ 2) / (hA.eigenvalues p₀) ^ 2 < 2 := by linarith
    rw [div_lt_iff₀ hpos2] at this
    linarith

end SpectralEntryRatio
