import PerronSimple

/-!
# `|λ| < M`, which is the other half of «separation» and closes `WALLS` §W4.0 §6 item 2

`PerronSimple` proved the top eigenvalue is **simple** and said in capitals that a *gap* in the
transfer-matrix sense wants more: `|λ| < M` for every other eigenvalue, with **`−M` excluded by
nothing**. That is this file.

> **`abs_le_top_of_eigenvector`** — for a symmetric matrix with **nonnegative** entries, every
> eigenvalue satisfies `|λ| ≤ M`. (The entrywise Perron inequality, run through the variational
> bound.)
>
> **`eq_zero_of_neg_top_eigenvector`** — for a **strictly** positive one, `−M` is **not** an
> eigenvalue.
>
> **`abs_lt_top_of_ne`** — hence `|λ| < M` for every eigenvalue other than `M`. **That is the
> separation `WALLS` §W4.0 §6 item 2 asked for.**
>
> **`transferSym_gap`** — the instance at the symmetrised two-dimensional Ising transfer matrix.

The `−M` argument is the classical one and every ingredient of it was proved earlier this week: if
`Av = −M·v` then `|v|` satisfies `A|v| ≥ M|v|` entrywise, so it achieves equality in the
variational inequality and is a top eigenvector; positivity then makes it strictly positive and
forces equality in the triangle inequality at every index, so all entries of `v` share a sign;
so `v = ±|v|` and `Av = M·v` as well as `−M·v`, which with `M > 0` forces `v = 0`.

## **WHAT THIS CLOSES, AND WHAT IT DOES NOT**

§4, added after the rest compiled, states the separation **about the eigenvalue list**
(`hA.eigenvalues`) rather than about a supplied eigenvector — which is the form `WALLS` §W4.0 §6
item 2 is about and the form `IsingTransferSym.partition2_eq_sum_eigenvalues` consumes. *Stating
it only about supplied eigenvectors would have been `ERRATUM 48`'s defect: the list version does
follow, from `mulVec_eigenvectorBasis`, and «it follows» is not «it is stated».*

It closes item 2 **for a strictly positive symmetric matrix**, which is what
`IsingTransferSym.transferSym` is. Item 2's own words were *"either Perron–Frobenius (absent from
Mathlib; a contribution in its own right) or a direct estimate exploiting positivity of the
entries"*, and its standing note that the `2 × 2` hand-rolled `abs_lamMinus_lt_lamPlus` *"does not
generalise as written"* is now answered by a different argument that does.

**It does not close W4 and does not move the row.** Item 3 — the passage from a spectral gap to
correlation decay — is discharged only for the one-dimensional chain and is untouched at `d ≥ 2`,
and §6 itself says the physical `d ≥ 2` mass gap is open mathematics with no formalisation route
known to this project. **A gap for one finite matrix at one fixed side length is not a mass gap**,
and nothing here says otherwise.

**⚠ SUPERSEDED 2026-08-22 (`ERRATUM 94`: the sentence above is kept as written; `ERRATUM 242`).
THE PASSAGE FROM A SPECTRAL GAP TO CORRELATION DECAY IS DISCHARGED AT `d = 2`, AND IT IS
DISCHARGED USING THIS FILE.** `IsingTopRatio.corr2SepInf_abs_le_subTopRatio` bounds the infinite
strip's two-point function by `(subTopRatio β n)^κ`, and `subTopRatio_lt_one`'s proof calls
`PerronGap.abs_eigenvalues_lt_of_ne` — so the decay theorem literally consumes the gap proved here,
on `IsingTransferSym.transferSym`, which is the **two-dimensional** Ising transfer matrix. Both
clauses are wrong: not *"only for the one-dimensional chain"*, and `d = 2` is exactly where it was
done. **`WALLS` §W4 was corrected on this same phrasing and the correction never reached here**
(`ERRATUM 228`'s eighth instance retired *"in `d ≥ 2` none of this is available"*).

**WHAT IS ACTUALLY UNTOUCHED, and it is not smaller for being stated correctly:** the WIDTH limit.
Every quantity in that chain is at one fixed width `n`; `IsingTopRatio.UniformSubTopRatio` names
what item 3 now wants — one `δ > 0` with `subTopRatio β n ≤ 1 - δ` for every `n` — it is proved at
no `β` but `β = 0` (`IsingTopRatioZero`), and no route is recorded. **The wall does not move.**

**AND NO MACHINE-CHECKED CITATION CAN BE PUT HERE**: the correcting theorem is DOWNSTREAM — the
strip chain imports this file — so a citation in this header would be an import cycle. Same
structural reason `W6ConversePi` records for its own corrections; the back-reference lives in
`IsingTopRatio` instead, which is the direction a machine can resolve.
-/

namespace PerronGap

open Matrix Finset RayleighMatrix PerronVector PerronSimple PerronEquality

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-! ## 1. Every eigenvalue is bounded by the top one -/

omit [Fintype n] [DecidableEq n] in
theorem absVec_row (v : EuclideanSpace ℝ n) (i : n) :
    (WithLp.ofLp (absVec v)) i = |(WithLp.ofLp v) i| := rfl

omit [DecidableEq n] in
/-- The entrywise Perron inequality, in the `mv` idiom: `|λ|·|vᵢ| ≤ (A|v|)ᵢ`. -/
theorem abs_smul_le_mv_absVec (hpos : ∀ i j, 0 ≤ A i j) {lam : ℝ} {v : EuclideanSpace ℝ n}
    (hv : mv A v = lam • v) (i : n) :
    |lam| * (WithLp.ofLp (absVec v)) i ≤ (WithLp.ofLp (mv A (absVec v))) i := by
  have hleft : |lam| * (WithLp.ofLp (absVec v)) i = |∑ j, A i j * (WithLp.ofLp v) j| := by
    rw [absVec_row, ← abs_mul, ← mv_row]
    congr 1
    rw [hv]; rfl
  rw [hleft, mv_row]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  rw [abs_mul, abs_of_nonneg (hpos i j), absVec_row]

/-- **EVERY EIGENVALUE OF A SYMMETRIC NONNEGATIVE MATRIX IS BOUNDED BY THE TOP ONE.** -/
theorem abs_le_top_of_eigenvector (hA : A.IsHermitian) (hpos : ∀ i j, 0 ≤ A i j) {M : ℝ}
    (hmax : ∀ j, hA.eigenvalues j ≤ M) {lam : ℝ} {v : EuclideanSpace ℝ n}
    (hv : mv A v = lam • v) (hne : v ≠ 0) : |lam| ≤ M := by
  set u := absVec v with hu
  have hunorm : inner ℝ u u = inner ℝ v v := normSq_absVec v
  have hupos : 0 < inner ℝ u u := by
    rw [hunorm]
    exact real_inner_self_pos.mpr hne
  have hge : |lam| * inner ℝ u u ≤ inner ℝ u (mv A u) := by
    rw [inner_expand, inner_expand, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc |lam| * ((WithLp.ofLp u) i * (WithLp.ofLp u) i)
        = (WithLp.ofLp u) i * (|lam| * (WithLp.ofLp u) i) := by ring
      _ ≤ (WithLp.ofLp u) i * (WithLp.ofLp (mv A u)) i :=
          mul_le_mul_of_nonneg_left (abs_smul_le_mv_absVec hpos hv i) (absVec_nonneg v i)
  have hle : inner ℝ u (mv A u) ≤ M * inner ℝ u u := quadForm_le_of_eigenvalues_le hA hmax u
  nlinarith [hge, hle, hupos]

/-! ## 2. `−M` is not an eigenvalue -/

/-- **FOR A STRICTLY POSITIVE SYMMETRIC MATRIX, `−M` IS NOT AN EIGENVALUE.** -/
theorem eq_zero_of_neg_top_eigenvector [Nonempty n] (hA : A.IsHermitian)
    (hpos : ∀ i j, 0 < A i j) {M : ℝ} (hmax : ∀ j, hA.eigenvalues j ≤ M) (hM : 0 < M)
    {v : EuclideanSpace ℝ n} (hv : mv A v = (-M) • v) : v = 0 := by
  by_contra hne
  set u := absVec v with hu
  have hunorm : inner ℝ u u = inner ℝ v v := normSq_absVec v
  have hupos : 0 < inner ℝ u u := by rw [hunorm]; exact real_inner_self_pos.mpr hne
  -- `|v|` achieves equality in the variational inequality
  have hent : ∀ i, M * (WithLp.ofLp u) i ≤ (WithLp.ofLp (mv A u)) i := by
    intro i
    have := abs_smul_le_mv_absVec (fun i j => le_of_lt (hpos i j)) hv i
    rwa [abs_neg, abs_of_pos hM] at this
  have hge : M * inner ℝ u u ≤ inner ℝ u (mv A u) := by
    rw [inner_expand, inner_expand, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc M * ((WithLp.ofLp u) i * (WithLp.ofLp u) i)
        = (WithLp.ofLp u) i * (M * (WithLp.ofLp u) i) := by ring
      _ ≤ (WithLp.ofLp u) i * (WithLp.ofLp (mv A u)) i :=
          mul_le_mul_of_nonneg_left (hent i) (absVec_nonneg v i)
  have hle : inner ℝ u (mv A u) ≤ M * inner ℝ u u := quadForm_le_of_eigenvalues_le hA hmax u
  have heq : inner ℝ u (mv A u) = M * inner ℝ u u := le_antisymm hle hge
  have hueig : mv A u = M • u := mv_eq_smul_of_quadForm_eq hA hmax heq
  have hune : u ≠ 0 := by
    intro h0; rw [h0] at hupos; simp at hupos
  have huposi : ∀ i, 0 < (WithLp.ofLp u) i :=
    pos_of_nonneg_top_eigenvector hpos hM hueig (absVec_nonneg v) hune
  -- equality in the triangle inequality at every index, so `v` has one sign
  have htri : ∀ i, |∑ j, A i j * (WithLp.ofLp v) j| = ∑ j, A i j * |(WithLp.ofLp v) j| := by
    intro i
    have hL : |∑ j, A i j * (WithLp.ofLp v) j| = M * (WithLp.ofLp u) i := by
      rw [← mv_row, hv]
      change |(-M) * (WithLp.ofLp v) i| = M * |(WithLp.ofLp v) i|
      rw [abs_mul, abs_neg, abs_of_pos hM]
    have hR : ∑ j, A i j * |(WithLp.ofLp v) j| = M * (WithLp.ofLp u) i := by
      have h1 : ∑ j, A i j * |(WithLp.ofLp v) j| = (WithLp.ofLp (mv A u)) i := by
        rw [mv_row]
        exact (Finset.sum_congr rfl fun j _ => by rw [absVec_row]).symm
      rw [h1, hueig]
      rfl
    rw [hL, hR]
  have hsign := nonneg_or_nonpos_of_abs_sum_eq (fun j => A (Classical.arbitrary n) j)
    (WithLp.ofLp v) (fun j => hpos (Classical.arbitrary n) j) (htri (Classical.arbitrary n))
  -- either way `mv A v = M • v`, and with `mv A v = (-M) • v` and `M > 0` that kills `v`
  have hMv : mv A v = M • v := by
    rcases hsign with hnn | hnp
    · have : v = u := by
        ext i; rw [absVec_row, abs_of_nonneg (hnn i)]
      rw [this, hueig]
    · have : v = (-1 : ℝ) • u := by
        ext i
        change (WithLp.ofLp v) i = (-1 : ℝ) * (WithLp.ofLp u) i
        rw [absVec_row, abs_of_nonpos (hnp i)]; ring
      rw [this, mv_smul, hueig, smul_smul, smul_smul, mul_comm]
  have hcontr : (2 * M) • v = 0 := by
    have := hMv.symm.trans hv
    have h2 : M • v - (-M) • v = 0 := by rw [sub_eq_zero]; exact this
    calc (2 * M) • v = M • v - (-M) • v := by module
      _ = 0 := h2
  have h2M : (2 * M) ≠ 0 := by positivity
  exact hne (by simpa [h2M] using hcontr)

/-! ## 3. The gap -/

/-- **`|λ| < M` FOR EVERY EIGENVALUE OTHER THAN `M`. THAT IS THE SEPARATION ITEM 2 ASKED FOR.** -/
theorem abs_lt_top_of_ne [Nonempty n] (hA : A.IsHermitian)
    (hpos : ∀ i j, 0 < A i j) {M : ℝ} (hmax : ∀ j, hA.eigenvalues j ≤ M) (hM : 0 < M)
    {lam : ℝ} {v : EuclideanSpace ℝ n} (hv : mv A v = lam • v) (hne : v ≠ 0)
    (hlam : lam ≠ M) : |lam| < M := by
  have hb : |lam| ≤ M :=
    abs_le_top_of_eigenvector hA (fun i j => le_of_lt (hpos i j)) hmax hv hne
  rcases lt_or_eq_of_le hb with h | h
  · exact h
  · exfalso
    rcases abs_eq (le_of_lt hM) |>.mp h with h1 | h1
    · exact hlam h1
    · exact hne (eq_zero_of_neg_top_eigenvector hA hpos hmax hM (by rw [hv, h1]))

open IsingTransfer2D IsingTransferSym in
/-- **THE SYMMETRISED TWO-DIMENSIONAL ISING TRANSFER MATRIX HAS A SPECTRAL GAP.**

**And it is not a mass gap.** `WALLS` §W4.0 §6 item 3 — the passage from a spectral gap to
correlation decay — exists here only for the one-dimensional chain, and §6 says the physical
`d ≥ 2` question is open mathematics. This is one finite matrix at one fixed side length.

**[⚠ THE CLAUSE «exists here only for the one-dimensional chain» IS FALSE — it is discharged at
`d = 2` and BY THIS THEOREM: `IsingTopRatio.subTopRatio_lt_one` calls `abs_eigenvalues_lt_of_ne`
and `corr2SepInf_abs_le_subTopRatio` turns it into exponential decay of the two-dimensional
strip's two-point function. See the header's dated supersession; `ERRATUM 242`. What is untouched
is the WIDTH limit.]** -/
theorem transferSym_gap (β : ℝ) (m : ℕ) :
    ∃ (M : ℝ) (u : EuclideanSpace ℝ (Col m)), (∀ i, 0 < (WithLp.ofLp u) i) ∧ 0 < M ∧
      mv (transferSym β m) u = M • u ∧
      ∀ (lam : ℝ) (v : EuclideanSpace ℝ (Col m)), mv (transferSym β m) v = lam • v → v ≠ 0 →
        lam ≠ M → |lam| < M := by
  obtain ⟨M, u, hupos, hmax, hM, heig⟩ := exists_pos_top_eigenvector_transferSym β m
  exact ⟨M, u, hupos, hM, heig, fun lam v hv hne hlam =>
    abs_lt_top_of_ne (transferSym_isHermitian β m) (fun i j => transferSym_pos β i j)
      hmax hM hv hne hlam⟩

/-! ## 4. The same statement about the eigenvalue list

Everything above takes an eigen**vector**. `WALLS` §W4.0 §6 item 2 is about the **spectrum**, and
`IsingTransferSym.partition2_eq_sum_eigenvalues` consumes `hA.eigenvalues`. The passage is
`mulVec_eigenvectorBasis` and it is written out here rather than left as *«it follows»*.
-/

theorem eigenvectorBasis_ne_zero [Nonempty n] (hA : A.IsHermitian) (j : n) :
    (hA.eigenvectorBasis j : EuclideanSpace ℝ n) ≠ 0 := by
  intro h
  have hn : ‖(hA.eigenvectorBasis j : EuclideanSpace ℝ n)‖ = 1 :=
    (hA.eigenvectorBasis).orthonormal.1 j
  rw [h, norm_zero] at hn
  norm_num at hn

theorem exists_max_eigenvalue [Nonempty n] (hA : A.IsHermitian) :
    ∃ k, ∀ j, hA.eigenvalues j ≤ hA.eigenvalues k := by
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_max_image (univ : Finset n) hA.eigenvalues Finset.univ_nonempty
  exact ⟨k, fun j => hk j (mem_univ j)⟩

/-- **THE LARGEST EIGENVALUE OF A STRICTLY POSITIVE SYMMETRIC MATRIX IS STRICTLY POSITIVE.** -/
theorem eigenvalue_max_pos [Nonempty n] (hA : A.IsHermitian) (hpos : ∀ i j, 0 < A i j) {k : n}
    (hk : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues k) : 0 < hA.eigenvalues k := by
  set b := (hA.eigenvectorBasis k : EuclideanSpace ℝ n) with hb
  set u := absVec b with hu
  have hbne : b ≠ 0 := eigenvectorBasis_ne_zero hA k
  have hunorm : inner ℝ u u = inner ℝ b b := normSq_absVec b
  have hupos : 0 < inner ℝ u u := by rw [hunorm]; exact real_inner_self_pos.mpr hbne
  have hune : u ≠ 0 := by intro h0; rw [h0] at hupos; simp at hupos
  have hex : ∃ p, (WithLp.ofLp u) p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hune (by ext i; simpa using hcon i)
  obtain ⟨p, hp⟩ := hex
  have hup : 0 < (WithLp.ofLp u) p := lt_of_le_of_ne (absVec_nonneg b p) (Ne.symm hp)
  have h1 : 0 < inner ℝ u (mv A u) := by
    rw [inner_expand]
    refine Finset.sum_pos' (fun i _ => ?_) ⟨p, mem_univ p, ?_⟩
    · rw [mv_row]
      exact mul_nonneg (absVec_nonneg b i)
        (Finset.sum_nonneg fun j _ => mul_nonneg (le_of_lt (hpos i j)) (absVec_nonneg b j))
    · rw [mv_row]
      refine mul_pos hup (Finset.sum_pos' (fun j _ =>
        mul_nonneg (le_of_lt (hpos p j)) (absVec_nonneg b j)) ⟨p, mem_univ p, ?_⟩)
      exact mul_pos (hpos p p) hup
  have h2 : inner ℝ u (mv A u) ≤ hA.eigenvalues k * inner ℝ u u :=
    quadForm_le_of_eigenvalues_le hA hk u
  nlinarith [h1, h2, hupos]

/-- **THE SEPARATION, STATED ABOUT THE EIGENVALUE LIST.** Every eigenvalue other than the largest
is strictly smaller **in absolute value**. -/
theorem abs_eigenvalues_lt_of_ne [Nonempty n] (hA : A.IsHermitian) (hpos : ∀ i j, 0 < A i j)
    {k : n} (hk : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues k) {j : n}
    (hne : hA.eigenvalues j ≠ hA.eigenvalues k) :
    |hA.eigenvalues j| < hA.eigenvalues k :=
  abs_lt_top_of_ne hA hpos hk (eigenvalue_max_pos hA hpos hk)
    (mv_eigenvectorBasis hA j) (eigenvectorBasis_ne_zero hA j) hne

open IsingTransfer2D IsingTransferSym in
/-- **THE GAP FOR THE SYMMETRISED TWO-DIMENSIONAL ISING TRANSFER MATRIX, ABOUT ITS EIGENVALUES.**
This is the form `partition2_eq_sum_eigenvalues` speaks in. -/
theorem transferSym_eigenvalues_gap (β : ℝ) (m : ℕ) :
    ∃ k : Col m, 0 < (transferSym_isHermitian β m).eigenvalues k ∧
      (∀ j, (transferSym_isHermitian β m).eigenvalues j
        ≤ (transferSym_isHermitian β m).eigenvalues k) ∧
      ∀ j, (transferSym_isHermitian β m).eigenvalues j
            ≠ (transferSym_isHermitian β m).eigenvalues k →
        |(transferSym_isHermitian β m).eigenvalues j|
          < (transferSym_isHermitian β m).eigenvalues k := by
  obtain ⟨k, hk⟩ := exists_max_eigenvalue (transferSym_isHermitian β m)
  refine ⟨k, eigenvalue_max_pos _ (fun i j => transferSym_pos β i j) hk, hk, fun j hj => ?_⟩
  exact abs_eigenvalues_lt_of_ne _ (fun i j => transferSym_pos β i j) hk hj

end PerronGap
