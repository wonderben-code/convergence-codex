import PerronVector

/-!
# Simplicity of the top eigenvalue, which is what `WALLS` §W4.0 §6 item 2 asked for

`PerronVector` proved the Perron half — a strictly positive top eigenvector — and said in capitals
that this is **not** a separation, because item 2 asked for the top eigenvalue to be **separated**
and a positive eigenvector says nothing about the second one. It also said the missing content was
now exactly *simplicity*, and that the classical route to simplicity consumes the positive
eigenvector just built. **This file is that route.**

> **`pos_of_nonneg_top_eigenvector`** — a **nonnegative, nonzero** top eigenvector of a strictly
> positive matrix is **strictly** positive. (The argument inside `PerronVector`'s existence proof,
> extracted so it can be used on a vector nobody constructed.)
>
> **`eq_zero_of_nonneg_top_eigenvector_of_zero`** — so a nonnegative top eigenvector with **one**
> zero entry is **zero everywhere**.
>
> **`top_eigenspace_dim_one`** — hence **any** top eigenvector is a multiple of the positive one.
> That is simplicity.

The trick is the classical one and it is one line long once the two lemmas above exist: subtract
the largest multiple of the positive eigenvector `u` that keeps `v - c·u` nonnegative. At the
index achieving that minimum the difference is zero, and the difference is still a top
eigenvector, so it is zero everywhere.

## **WHAT THIS IS AND IS NOT, FOR `WALLS` §W4.0 §6 ITEM 2**

Item 2 asks for *«separation of its top eigenvalue»*. **Simplicity is one of the two things that
phrase means and this file supplies it**: the eigenspace of `M` is one-dimensional, so `M` occurs
once and every other eigenvalue is **strictly below** it.

**The other thing it can mean is not here.** For a *gap* in the transfer-matrix sense one wants
`|λ| < M` for every other eigenvalue — and `−M` is not excluded by anything below. Ruling out
`−M` for a strictly positive matrix is a separate classical argument and **is not attempted**.
`IsingTransferMatrix.abs_lamMinus_lt_lamPlus` is the `2 × 2` instance of exactly that missing
statement, done by hand, and it does not generalise as written — which is what §6 item 2 said in
the first place.

**⚠ SUPERSEDED 2026-08-27, kept as written (`ERRATUM 94`, found by `ERRATUM 305`).** *"Ruling out
`−M` for a strictly positive matrix is a separate classical argument and is not attempted"* is
false: `PerronGap.abs_eigenvalues_lt_of_ne` is that argument and
`PerronPrimitive.abs_lt_max_of_ne_of_pos` recovers it from the primitive case, both giving
`|λⱼ| < λ_max` for every eigenvalue other than the top one of a Hermitian, strictly positive
matrix. **Still true**: *"the other thing it can mean is not here"*, scoped to this file.
**AND THIS ONE COULD NOT HAVE BEEN CAUGHT BY AN IMPORT-GRAPH TRIGGER.** Neither `PerronGap` nor
`PerronPrimitive` imports this file — they sit on a different branch of the `Perron` family — so
the expiry rule `claims_accepted.txt` uses, *"a file committed ABOVE this one is newer"*, would
never have fired. An estate-scope claim is falsifiable by anything in the estate, and the import
graph is a conservative proxy for that, not the thing itself.

**And the wall does not move.** Item 3 — the passage from a spectral gap to correlation decay — is
discharged only for the one-dimensional chain and untouched at `d ≥ 2`.

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
no `β` but `β = 0` (`IsingTopRatioZero`), and **from 2026-08-26 a route IS
recorded** — `SpectralEntryRatio.subTop_ratio_le`, a dimension-free bound on the sub-top
ratio from the entry ratio, together with the number showing it cannot reach this matrix
(`ERRATUM 269`; the citation is downstream, as the paragraph below says). **The wall does
not move**, and what is retired is the claim that nothing had been tried.

**AND NO MACHINE-CHECKED CITATION CAN BE PUT HERE**: the correcting theorem is DOWNSTREAM — the
strip chain imports this file — so a citation in this header would be an import cycle. Same
structural reason `W6ConversePi` records for its own corrections; the back-reference lives in
`IsingTopRatio` instead, which is the direction a machine can resolve.
-/

namespace PerronSimple

open Matrix Finset RayleighMatrix PerronVector

variable {n : Type*} [Fintype n] {A : Matrix n n ℝ}

/-! ## 1. A nonnegative top eigenvector is strictly positive -/

/-- **A NONNEGATIVE, NONZERO TOP EIGENVECTOR OF A STRICTLY POSITIVE MATRIX IS STRICTLY POSITIVE.**
Extracted from `PerronVector`'s existence proof so that it applies to a vector nobody built. -/
theorem pos_of_nonneg_top_eigenvector (hpos : ∀ i j, 0 < A i j) {M : ℝ} (hM : 0 < M)
    {w : EuclideanSpace ℝ n} (hw : mv A w = M • w) (hnn : ∀ i, 0 ≤ (WithLp.ofLp w) i)
    (hne : w ≠ 0) : ∀ i, 0 < (WithLp.ofLp w) i := by
  have hex : ∃ p, (WithLp.ofLp w) p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (by ext i; simpa using hcon i)
  obtain ⟨p, hp⟩ := hex
  have hwp : 0 < (WithLp.ofLp w) p := lt_of_le_of_ne (hnn p) (Ne.symm hp)
  intro i
  have hrow : 0 < (WithLp.ofLp (mv A w)) i := by
    rw [mv_row]
    exact Finset.sum_pos' (fun j _ => mul_nonneg (le_of_lt (hpos i j)) (hnn j))
      ⟨p, mem_univ p, mul_pos (hpos i p) hwp⟩
  have hsm : (WithLp.ofLp (mv A w)) i = M * (WithLp.ofLp w) i := by rw [hw]; rfl
  rw [hsm] at hrow
  nlinarith [hrow, hM]

/-- **SO ONE ZERO ENTRY MAKES IT ZERO EVERYWHERE.** -/
theorem eq_zero_of_nonneg_top_eigenvector_of_zero (hpos : ∀ i j, 0 < A i j) {M : ℝ} (hM : 0 < M)
    {w : EuclideanSpace ℝ n} (hw : mv A w = M • w) (hnn : ∀ i, 0 ≤ (WithLp.ofLp w) i)
    {k : n} (hk : (WithLp.ofLp w) k = 0) : w = 0 := by
  by_contra hne
  have := pos_of_nonneg_top_eigenvector hpos hM hw hnn hne k
  rw [hk] at this
  exact lt_irrefl 0 this

/-! ## 2. Simplicity -/

/-- **EVERY TOP EIGENVECTOR IS A MULTIPLE OF THE POSITIVE ONE.** That is simplicity: the
eigenspace of `M` is one-dimensional, so `M` occurs once and every other eigenvalue is strictly
below it. -/
theorem top_eigenspace_dim_one [Nonempty n] (hpos : ∀ i j, 0 < A i j) {M : ℝ} (hM : 0 < M)
    {u : EuclideanSpace ℝ n} (hu : mv A u = M • u) (hupos : ∀ i, 0 < (WithLp.ofLp u) i)
    {v : EuclideanSpace ℝ n} (hv : mv A v = M • v) :
    ∃ c : ℝ, v = c • u := by
  obtain ⟨k, -, hk⟩ := Finset.exists_min_image (univ : Finset n)
    (fun i => (WithLp.ofLp v) i / (WithLp.ofLp u) i) Finset.univ_nonempty
  set c := (WithLp.ofLp v) k / (WithLp.ofLp u) k with hc
  refine ⟨c, ?_⟩
  set w := v + (-c) • u with hwdef
  have hwapp : ∀ i, (WithLp.ofLp w) i = (WithLp.ofLp v) i - c * (WithLp.ofLp u) i := by
    intro i; simp [hwdef]; ring
  have hweig : mv A w = M • w := by
    rw [hwdef, mv_add, mv_smul, hu, hv]
    module
  have hwnn : ∀ i, 0 ≤ (WithLp.ofLp w) i := by
    intro i
    rw [hwapp i]
    have hci : c ≤ (WithLp.ofLp v) i / (WithLp.ofLp u) i := hk i (mem_univ i)
    have hui : 0 < (WithLp.ofLp u) i := hupos i
    rw [le_div_iff₀ hui] at hci
    linarith
  have hwk : (WithLp.ofLp w) k = 0 := by
    rw [hwapp k, hc, div_mul_cancel₀ _ (ne_of_gt (hupos k))]
    ring
  have hzero : w = 0 :=
    eq_zero_of_nonneg_top_eigenvector_of_zero hpos hM hweig hwnn hwk
  have : v + (-c) • u = 0 := by rw [← hwdef]; exact hzero
  have hv' : v = c • u := by
    have := congrArg (fun x => x + c • u) this
    simpa [add_assoc, ← add_smul] using this
  exact hv'

/-! ## 3. The wall's own matrix -/

open IsingTransfer2D IsingTransferSym in
/-- **THE SYMMETRISED TWO-DIMENSIONAL ISING TRANSFER MATRIX HAS A SIMPLE, STRICTLY POSITIVE TOP
EIGENVALUE.** Every eigenvector for it is a multiple of one strictly positive vector.

**This is half of what `WALLS` §W4.0 §6 item 2 means by «separation» and not the other half**:
`|λ| < M` for every other eigenvalue is a further statement, `−M` is not excluded here, and it is
not attempted. -/
theorem transferSym_top_simple (β : ℝ) (m : ℕ) :
    ∃ (M : ℝ) (u : EuclideanSpace ℝ (Col m)), (∀ i, 0 < (WithLp.ofLp u) i) ∧ 0 < M ∧
      mv (transferSym β m) u = M • u ∧
      ∀ v : EuclideanSpace ℝ (Col m), mv (transferSym β m) v = M • v → ∃ c : ℝ, v = c • u := by
  obtain ⟨M, u, hupos, -, hM, heig⟩ := exists_pos_top_eigenvector_transferSym β m
  exact ⟨M, u, hupos, hM, heig, fun v hv =>
    top_eigenspace_dim_one (fun i j => transferSym_pos β i j) hM heig hupos hv⟩

end PerronSimple
