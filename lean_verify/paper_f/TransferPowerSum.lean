import PerronGap

/-!
# The partition function as a power sum of the transfer matrix's own eigenvalues

**This file exists because adversarial review of `PerronGap` §4 found that eight files of Perron
theory ended in a statement about one family of real numbers while the only quantity they were
built to control is stated about a different one** (`ERRATUM 222`).

`PerronGap.transferSym_eigenvalues_gap` separates the eigenvalues **of `T`**.
`IsingTransferSym.partition2_eq_sum_eigenvalues` sums the eigenvalues **of `T^{M+1}`**, and says
so in bold in its own docstring:

> *"Read the statement carefully — these are the eigenvalues of `T^{M+1}`, not the `(M+1)`-st
> powers of the eigenvalues of `T`. Getting from one to the other is the spectral mapping theorem,
> which is **not applied here**."*

Nothing joined the two. This file is that step.

> **`trace_pow_eq_sum_eigenvalues_pow`** — for a Hermitian matrix over any `RCLike` field,
> `tr (A ^ k) = ∑ (λ i) ^ k`. Conjugation by a unitary is a **star-algebra automorphism**, so it
> commutes with powers; the trace is conjugation-invariant; a diagonal matrix's power is diagonal.
>
> **`real_trace_pow_eq_sum_eigenvalues_pow`** — the same for a **real** symmetric matrix, with no
> coercion left in the statement. This is the rung `UNLOCK_WATCHLIST`'s 22 August item names.
>
> **`partition2_eq_sum_eigenvalues_pow`** — hence the two-dimensional Ising partition function is
> `∑ (λ i) ^ (M + 1)` over the eigenvalues of `transferSym` itself.

**WHY IT HAD TO BE BUILT.** `Matrix.herm_trace_pow` proves exactly the same identity
for a matrix over `ℂ`, and `transferSym` is real; its ancestor
`Matrix.trace_pow_eq_sum_roots_charpoly` needs `IsAlgClosed`, which `ℝ` is not. Both
were written by this project and neither reaches a real symmetric matrix — `ERRATUM 42`, a lemma
existing and a lemma applying are two different probes. **Mathlib has no eigenvalue-family
spectral mapping at all**: `eigenvalues_pow`, `pow_eigenvalues`, `eigenvalues_zpow`,
`eigenvalues_sq`, `spectral_mapping`, `spectrum_pow`, `trace_pow_eq_sum` are **0 each** in the
pinned dump, against `Matrix.IsHermitian.pow` and `Matrix.IsHermitian.trace_eq_sum_eigenvalues`
present. The ingredients were there; the theorem was not.

**WHAT THIS IS NOT.** It is not a mass gap and it does not touch `WALLS` §W4.0 §6 item 3. Every
statement below is about **one finite matrix at one fixed side length `n`**, and the physical
question needs `n → ∞` taken first. What it does is make the separation `PerronGap` proved bear on
the quantity it was proved for.
-/

namespace TransferPowerSum

open Matrix Finset RayleighMatrix

/-! ## 1. The spectral mapping step for traces

The classical three lines, over any `RCLike` field so that the real case is an instance rather
than a re-proof.
-/

/-- **THE TRACE OF A POWER IS THE POWER SUM OF THE EIGENVALUES.** Mathlib has
`IsHermitian.trace_eq_sum_eigenvalues` (the case `k = 1`) and `IsHermitian.pow` (a power of a
Hermitian matrix is Hermitian, which is what lets the partition function be stated in the *wrong*
eigenvalue family), and nothing joining them. -/
theorem trace_pow_eq_sum_eigenvalues_pow {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, ((hA.eigenvalues i : ℝ) : 𝕜) ^ k := by
  have hpow : A ^ k
      = (Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜)) hA.eigenvectorUnitary
          (Matrix.diagonal ((RCLike.ofReal ∘ hA.eigenvalues) ^ k)) := by
    rw [← Matrix.diagonal_pow, map_pow, ← hA.spectral_theorem]
  rw [hpow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- **THE REAL CASE, WITH NO COERCION IN THE STATEMENT.** This is the rung the watchlist item of
22 August names. `RCLike ℝ` makes it an instance of the theorem above rather than a second proof;
what it buys is that the statement can be *used* against a real symmetric matrix without carrying
`RCLike.ofReal` through every rewrite. -/
theorem real_trace_pow_eq_sum_eigenvalues_pow {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, hA.eigenvalues i ^ k := by
  simpa using trace_pow_eq_sum_eigenvalues_pow hA k

/-! ## 2. The partition function in its own matrix's spectrum

`IsingTransferSym.partition2_eq_trace_sym` already says `partition2 = tr (T ^ (M+1))`. §1 turns
the right-hand side into a power sum over the eigenvalues of `T`, which is the family
`PerronGap.transferSym_eigenvalues_gap` separates.
-/

open IsingTransfer2D IsingTransferSym in
/-- **THE TWO-DIMENSIONAL ISING PARTITION FUNCTION IS A POWER SUM OF THE TRANSFER MATRIX'S OWN
EIGENVALUES.** This is the statement `partition2_eq_sum_eigenvalues` deliberately did **not**
make — its docstring says the passage "is not applied here" — and it is the form every
transfer-matrix argument is written in. -/
theorem partition2_eq_sum_eigenvalues_pow (β : ℝ) (n M : ℕ) :
    partition2 β n M = ∑ i, (transferSym_isHermitian β n).eigenvalues i ^ (M + 1) := by
  rw [partition2_eq_trace_sym]
  exact real_trace_pow_eq_sum_eigenvalues_pow (transferSym_isHermitian β n) (M + 1)

/-! ## 3. The top eigenvalue occurs exactly once in the list

`PerronSimple.top_eigenspace_dim_one` says the top **eigenspace** is one-dimensional. That is not
the same statement as *the value occurs once in `hA.eigenvalues`*, and the difference is exactly
`ERRATUM 48`'s: the second follows from the first plus orthonormality of `eigenvectorBasis`, and
«it follows» is not «it is stated». The power sum of §2 is indexed by the LIST, so it is the list
statement that the sum needs.
-/

section Multiplicity

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

open PerronVector RayleighMatrix PerronSimple PerronGap

/-- **THE MODULUS OF A TOP EIGENVECTOR IS A STRICTLY POSITIVE TOP EIGENVECTOR.** Extracted from
the existence proof in `PerronVector` so that it applies to a vector already in hand — here an
element of `eigenvectorBasis` — rather than only to one the existence proof built. -/
theorem absVec_top_pos [Nonempty n] (hA : A.IsHermitian) (hpos : ∀ i j, 0 < A i j) {M : ℝ}
    (hmax : ∀ j, hA.eigenvalues j ≤ M) (hM : 0 < M) {v : EuclideanSpace ℝ n}
    (hv : mv A v = M • v) (hne : v ≠ 0) :
    mv A (absVec v) = M • absVec v ∧ ∀ i, 0 < (WithLp.ofLp (absVec v)) i := by
  have hvv : (0 : ℝ) < inner ℝ v v := real_inner_self_pos.mpr hne
  have hq : inner ℝ v (mv A v) = M * inner ℝ v v := by
    rw [hv, real_inner_smul_right]
  have hge : inner ℝ v (mv A v) ≤ inner ℝ (absVec v) (mv A (absVec v)) :=
    quadForm_absVec_ge (fun i j => le_of_lt (hpos i j)) v
  have hle : inner ℝ (absVec v) (mv A (absVec v)) ≤ M * inner ℝ (absVec v) (absVec v) :=
    quadForm_le_of_eigenvalues_le hA hmax (absVec v)
  have hnorm : inner ℝ (absVec v) (absVec v) = inner ℝ v v := normSq_absVec v
  rw [hnorm] at hle
  have heq : inner ℝ (absVec v) (mv A (absVec v)) = M * inner ℝ (absVec v) (absVec v) := by
    rw [hnorm]; linarith [hge, hle, hq]
  have hav : mv A (absVec v) = M • absVec v := mv_eq_smul_of_quadForm_eq hA hmax heq
  have hane : absVec v ≠ 0 := by
    intro h0
    rw [h0] at hnorm
    simp only [inner_zero_left] at hnorm
    linarith [hnorm, hvv]
  exact ⟨hav, pos_of_nonneg_top_eigenvector hpos hM hav (absVec_nonneg v) hane⟩

/-- **SO THE ARGMAX INDEX IS UNIQUE.** If two entries of the eigenvalue list both equal the
largest, the indices coincide: their basis vectors are orthogonal, and both are multiples of one
strictly positive vector, which forces one of them to vanish. -/
theorem index_eq_of_eigenvalues_eq_top [Nonempty n] (hA : A.IsHermitian) (hpos : ∀ i j, 0 < A i j)
    {k : n} (hk : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues k) {j : n}
    (hj : hA.eigenvalues j = hA.eigenvalues k) : j = k := by
  set M := hA.eigenvalues k with hMdef
  have hM : 0 < M := eigenvalue_max_pos hA hpos hk
  set bj := (hA.eigenvectorBasis j : EuclideanSpace ℝ n) with hbj
  set bk := (hA.eigenvectorBasis k : EuclideanSpace ℝ n) with hbk
  have hbkne : bk ≠ 0 := eigenvectorBasis_ne_zero hA k
  have hbjne : bj ≠ 0 := eigenvectorBasis_ne_zero hA j
  have hvk : mv A bk = M • bk := mv_eigenvectorBasis hA k
  have hvj : mv A bj = M • bj := by rw [← hj]; exact mv_eigenvectorBasis hA j
  -- `u` is introduced by `obtain` rather than named as `absVec bk`, so that rewriting `bk`
  -- below cannot reach inside it.
  obtain ⟨u, hu, hupos, huu⟩ : ∃ u : EuclideanSpace ℝ n, mv A u = M • u ∧
      (∀ i, 0 < (WithLp.ofLp u) i) ∧ (0 : ℝ) < inner ℝ u u := by
    obtain ⟨h1, h2⟩ := absVec_top_pos hA hpos hk hM hvk hbkne
    exact ⟨absVec bk, h1, h2, by rw [normSq_absVec]; exact real_inner_self_pos.mpr hbkne⟩
  obtain ⟨cj, hcj⟩ := top_eigenspace_dim_one hpos hM hu hupos hvj
  obtain ⟨ck, hck⟩ := top_eigenspace_dim_one hpos hM hu hupos hvk
  by_contra hne
  have horth : inner ℝ bj bk = (0 : ℝ) := by
    have := (hA.eigenvectorBasis).orthonormal.2 hne
    simpa [hbj, hbk] using this
  rw [hcj, hck, real_inner_smul_left, real_inner_smul_right] at horth
  rcases mul_eq_zero.mp horth with h | h
  · exact hbjne (by rw [hcj, h, zero_smul])
  · exact hbkne (by rw [hck, (mul_eq_zero.mp h).resolve_right (ne_of_gt huu), zero_smul])

end Multiplicity

/-! ## 4. What the gap is for

A separation `|λ_j| < λ_k` is worth having because it makes every non-top term of §2's power sum
geometrically small against the top one. With §3 supplying that `k` is the *only* index carrying
the top value, the whole sum divided by `λ_k ^ (M+1)` converges to `1`.

**This is a statement about one finite matrix at one fixed side length `n`, and the limit taken is
in the LENGTH `M` of the strip, not in its WIDTH `n`.** `WALLS` §W4.0 §6 item 3 needs `n → ∞`
first, and nothing here takes that limit. It is not the mass gap and it is not a step toward one.

§5 takes the logarithm, which is the form the quantity has a name in.
-/

section Asymptotics

open Filter Topology IsingTransfer2D IsingTransferSym

/-- **THE PARTITION FUNCTION IS ASYMPTOTICALLY THE TOP EIGENVALUE'S POWER.** For every inverse
temperature and every strip width, `partition2 β n M / λ_top ^ (M+1) → 1` as the strip length
`M → ∞`. Every ingredient is from this chain: §2 for the power sum, `PerronGap` for the
separation, §3 for the top value occurring once. -/
theorem partition2_div_top_pow_tendsto_one (β : ℝ) (n : ℕ) :
    ∃ k : Col n, 0 < (transferSym_isHermitian β n).eigenvalues k ∧
      Tendsto (fun M : ℕ =>
          partition2 β n M / (transferSym_isHermitian β n).eigenvalues k ^ (M + 1))
        atTop (𝓝 1) := by
  classical
  set hA := transferSym_isHermitian β n with hAdef
  have hpos : ∀ i j : Col n, 0 < transferSym β n i j := fun i j => transferSym_pos β i j
  obtain ⟨k, hk⟩ := PerronGap.exists_max_eigenvalue hA
  have hkpos : 0 < hA.eigenvalues k := PerronGap.eigenvalue_max_pos hA hpos hk
  refine ⟨k, hkpos, ?_⟩
  have hrw : ∀ M : ℕ, partition2 β n M / hA.eigenvalues k ^ (M + 1)
      = ∑ i, (hA.eigenvalues i / hA.eigenvalues k) ^ (M + 1) := by
    intro M
    rw [partition2_eq_sum_eigenvalues_pow, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => (div_pow _ _ _).symm
  refine Tendsto.congr (fun M => (hrw M).symm) ?_
  have hterm : ∀ i : Col n, Tendsto (fun M : ℕ => (hA.eigenvalues i / hA.eigenvalues k) ^ (M + 1))
      atTop (𝓝 (if i = k then (1 : ℝ) else 0)) := by
    intro i
    by_cases hik : i = k
    · subst hik
      simp [div_self (ne_of_gt hkpos)]
    · have hne : hA.eigenvalues i ≠ hA.eigenvalues k := fun h =>
        hik (index_eq_of_eigenvalues_eq_top hA hpos hk h)
      have hlt : |hA.eigenvalues i| < hA.eigenvalues k :=
        PerronGap.abs_eigenvalues_lt_of_ne hA hpos hk hne
      have habs : |hA.eigenvalues i / hA.eigenvalues k| < 1 := by
        rw [abs_div, abs_of_pos hkpos, div_lt_one hkpos]
        exact hlt
      have h0 := tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs
      have := h0.mul_const (hA.eigenvalues i / hA.eigenvalues k)
      simpa [hik, pow_succ] using this
  have hsum := tendsto_finset_sum (univ : Finset (Col n)) fun i (_ : i ∈ univ) => hterm i
  simpa using hsum

end Asymptotics

/-! ## 5. The free energy per row, which is what §4 is called in the literature

The physicist's statement is `(1/M)·log Z → log λ_top`. Writing the note *"it follows from §4 by
taking logarithms and is not stated here"* was the first draft of this section, and it was the
wrong draft: `ERRATUM 48` and `ERRATUM 222` are both about the distance between «it follows» and
«it is stated», and the honest response to noticing that distance is to close it.

**IT ALSO REMOVED AN UNPROVED ASSERTION FROM THE PROSE.** That note said the derivation needs
`0 < partition2`, *"which is true and is not proved in this estate"* — a claim about a real number
with no proof behind it, in a file whose subject is the difference between those two things.
`partition2_pos` below is three lines and the sentence is gone.

**AND THE PROBE THAT FOUND THE ABSENCE IS WORTH RECORDING** (`ERRATUM 42`, third instance in this
one file). This estate proves partition-function positivity twice — `BoundaryFieldRatio.
partition_pos` and `PeierlsConditional.plus_partition_pos` — and **neither is about
`IsingTransfer2D.partition2`**. Together with `Matrix.herm_trace_pow` being complex-
only and `trace_pow_eq_sum_roots_charpoly` needing `IsAlgClosed`, that is three lemmas in one
file's review that exist for the neighbouring object and not for this one.
-/

section FreeEnergy

open Filter Topology IsingTransfer2D IsingTransferSym

/-- **THE PARTITION FUNCTION IS POSITIVE.** A finite sum of exponentials over a nonempty type. -/
theorem partition2_pos (β : ℝ) (n M : ℕ) : 0 < partition2 β n M :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- **THE FREE ENERGY PER ROW IS THE LOGARITHM OF THE TOP EIGENVALUE.** For every inverse
temperature and every strip width, `(M+1)⁻¹ · log (partition2 β n M) → log λ_top` as the strip
length grows.

**The limit is still in `M` and not in `n`**, so this is the free energy of a strip of FIXED
WIDTH. `WALLS` §W4.0 §6 item 3 wants `n → ∞`, and no theorem in this estate takes that limit. -/
theorem log_partition2_tendsto_log_top (β : ℝ) (n : ℕ) :
    ∃ k : Col n, 0 < (transferSym_isHermitian β n).eigenvalues k ∧
      Tendsto (fun M : ℕ => ((M : ℝ) + 1)⁻¹ * Real.log (partition2 β n M))
        atTop (𝓝 (Real.log ((transferSym_isHermitian β n).eigenvalues k))) := by
  obtain ⟨k, hkpos, hlim⟩ := partition2_div_top_pow_tendsto_one β n
  refine ⟨k, hkpos, ?_⟩
  set lk := (transferSym_isHermitian β n).eigenvalues k with hlkdef
  have hsplit : ∀ M : ℕ, ((M : ℝ) + 1)⁻¹ * Real.log (partition2 β n M)
      = Real.log lk + ((M : ℝ) + 1)⁻¹ * Real.log (partition2 β n M / lk ^ (M + 1)) := by
    intro M
    have hM : ((M : ℝ) + 1) ≠ 0 := by positivity
    rw [Real.log_div (ne_of_gt (partition2_pos β n M)) (pow_ne_zero _ (ne_of_gt hkpos)),
      Real.log_pow]
    push_cast
    field_simp
    ring
  refine Tendsto.congr (fun M => (hsplit M).symm) ?_
  have hlog : Tendsto (fun M : ℕ => Real.log (partition2 β n M / lk ^ (M + 1))) atTop (𝓝 0) := by
    have hc : ContinuousAt Real.log 1 := Real.continuousAt_log one_ne_zero
    simpa using hc.tendsto.comp hlim
  have hinv : Tendsto (fun M : ℕ => ((M : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa using tendsto_const_nhds.add (hinv.mul hlog)

end FreeEnergy

end TransferPowerSum
