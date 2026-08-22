import RayleighMatrix
import PerronEquality
import IsingTransferSym

/-!
# A nonnegative top eigenvector, and a strictly positive one

`RayleighMatrix` §4 ends by saying half (a) of `WALLS` §W4.0 §6 item 2 is complete **as a
statement about the form**, and names what it is short of: *the application* — producing a `v`
that achieves equality and whose entrywise modulus does too, which is where the positivity of `A`
would finally enter. **This file is that application**, and it turns out to be one inequality.

> **`quadForm_absVec_ge`** — for a matrix with **nonnegative** entries, replacing `v` by its
> entrywise modulus **never decreases** the quadratic form. One line of content: `Aᵢⱼvᵢvⱼ ≤
> Aᵢⱼ|vᵢ||vⱼ|`.
>
> **`exists_nonneg_top_eigenvector`** — hence a **symmetric matrix with nonnegative entries has a
> nonnegative eigenvector for its largest eigenvalue**, and that eigenvalue is `≥ 0`.
>
> **`exists_pos_top_eigenvector`** — and with **strictly** positive entries the eigenvector is
> **strictly positive** and the eigenvalue is **strictly positive**.

The second is the Perron half of Perron–Frobenius for the symmetric case. The argument is the
classical one and every step of it is now a named theorem in this estate rather than a sentence:
the top eigenvector `b` achieves equality in `RayleighMatrix.quadForm_le_of_eigenvalues_le`; `|b|`
achieves it too, by the inequality above and `normSq_absVec`; so `|b|` is an eigenvector by
`RayleighMatrix.mv_eq_smul_of_quadForm_eq`; and strict positivity of the entries then forces every
coordinate of `|b|` up off zero.

## **WHAT IS STILL MISSING, AND IT IS HALF (b)**

Perron–Frobenius has a second half: that the top eigenvalue is **simple**. Nothing here approaches
it. Two nonnegative nowhere-zero eigenvectors for the same eigenvalue can still be independent as
far as anything proved here is concerned, and ruling that out is where positivity is used a second
time.

**And it applies to the wall's own matrix**, which is checked below rather than asserted
(`ERRATUM 48`): `IsingTransferSym.transferSym` is Hermitian (`transferSym_isHermitian`) and has
strictly positive entries (`transferSym_pos`), both already proved in this estate, so
`exists_pos_top_eigenvector_transferSym` is an instance and not an analogy. **That matrix is the
symmetrised two-dimensional Ising transfer matrix — `transfer2` itself is NOT symmetric, which is
why `IsingTransferSym` exists at all, and applying this file to `transfer2` directly would be
wrong.**

**And the wall does not move.** `WALLS` §W4.0 §6 item 3 — the passage from a spectral gap to
correlation decay — is discharged only for the one-dimensional chain and untouched at `d ≥ 2`,
and §6 itself says the physical `d ≥ 2` mass gap is open mathematics with no formalisation route
known to this project. Everything here is one classical theorem about one finite matrix at one
fixed side length.
-/

namespace PerronVector

open Matrix Finset RayleighMatrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-! ## 1. The entrywise modulus -/

/-- The entrywise modulus of a vector. -/
noncomputable def absVec (v : EuclideanSpace ℝ n) : EuclideanSpace ℝ n :=
  WithLp.toLp 2 (fun i => |(WithLp.ofLp v) i|)

omit [Fintype n] [DecidableEq n] in
theorem absVec_apply (v : EuclideanSpace ℝ n) (i : n) :
    (WithLp.ofLp (absVec v)) i = |(WithLp.ofLp v) i| := rfl

omit [Fintype n] [DecidableEq n] in
theorem absVec_nonneg (v : EuclideanSpace ℝ n) (i : n) : 0 ≤ (WithLp.ofLp (absVec v)) i :=
  abs_nonneg _

omit [DecidableEq n] in
/-- Taking the modulus does not change the squared norm. -/
theorem normSq_absVec (v : EuclideanSpace ℝ n) :
    inner ℝ (absVec v) (absVec v) = inner ℝ v v := by
  rw [inner_expand, inner_expand]
  exact Finset.sum_congr rfl fun i _ => by rw [absVec_apply, ← abs_mul, abs_mul_self]

omit [DecidableEq n] in
/-- **AND WITH NONNEGATIVE ENTRIES IT DOES NOT DECREASE THE QUADRATIC FORM.** -/
theorem quadForm_absVec_ge (hpos : ∀ i j, 0 ≤ A i j) (v : EuclideanSpace ℝ n) :
    inner ℝ v (mv A v) ≤ inner ℝ (absVec v) (mv A (absVec v)) := by
  rw [inner_expand, inner_expand]
  simp only [mv_row]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [absVec_apply, absVec_apply]
  have hle : (WithLp.ofLp v) i * ((WithLp.ofLp v) j)
      ≤ |(WithLp.ofLp v) i| * |(WithLp.ofLp v) j| := by
    rw [← abs_mul]; exact le_abs_self _
  calc (WithLp.ofLp v) i * (A i j * (WithLp.ofLp v) j)
      = A i j * ((WithLp.ofLp v) i * (WithLp.ofLp v) j) := by ring
    _ ≤ A i j * (|(WithLp.ofLp v) i| * |(WithLp.ofLp v) j|) :=
        mul_le_mul_of_nonneg_left hle (hpos i j)
    _ = |(WithLp.ofLp v) i| * (A i j * |(WithLp.ofLp v) j|) := by ring

/-! ## 2. The Perron eigenvector -/

/-- **A SYMMETRIC MATRIX WITH NONNEGATIVE ENTRIES HAS A NONNEGATIVE EIGENVECTOR FOR ITS LARGEST
EIGENVALUE.** -/
theorem exists_nonneg_top_eigenvector [Nonempty n] (hA : A.IsHermitian)
    (hpos : ∀ i j, 0 ≤ A i j) :
    ∃ (M : ℝ) (u : EuclideanSpace ℝ n), u ≠ 0 ∧ (∀ i, 0 ≤ (WithLp.ofLp u) i) ∧
      (∀ j, hA.eigenvalues j ≤ M) ∧ 0 ≤ M ∧ mv A u = M • u := by
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_max_image (univ : Finset n) hA.eigenvalues Finset.univ_nonempty
  set M := hA.eigenvalues k with hM
  have hmax : ∀ j, hA.eigenvalues j ≤ M := fun j => hk j (mem_univ j)
  set b := hA.eigenvectorBasis k with hb
  have hbnorm : inner ℝ b b = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, (hA.eigenvectorBasis).orthonormal.1 k]
    norm_num
  -- the top eigenvector achieves equality
  have hbeq : inner ℝ b (mv A b) = M * inner ℝ b b := by
    rw [mv_eigenvectorBasis hA, real_inner_smul_right]
  set u := absVec b with hu
  have hunorm : inner ℝ u u = inner ℝ b b := normSq_absVec b
  have hge : M * inner ℝ u u ≤ inner ℝ u (mv A u) := by
    rw [hunorm, ← hbeq]; exact quadForm_absVec_ge hpos b
  have hle : inner ℝ u (mv A u) ≤ M * inner ℝ u u :=
    quadForm_le_of_eigenvalues_le hA hmax u
  have heq : inner ℝ u (mv A u) = M * inner ℝ u u := le_antisymm hle hge
  have hune : u ≠ 0 := by
    intro h0
    rw [h0] at hunorm
    simp only [inner_zero_left] at hunorm
    rw [hbnorm] at hunorm
    norm_num at hunorm
  have hMnonneg : 0 ≤ M := by
    have h1 : (0 : ℝ) ≤ inner ℝ u (mv A u) := by
      rw [inner_expand]
      refine Finset.sum_nonneg fun i _ => ?_
      rw [mv_row]
      exact mul_nonneg (absVec_nonneg b i)
        (Finset.sum_nonneg fun j _ => mul_nonneg (hpos i j) (absVec_nonneg b j))
    have h2 : (0 : ℝ) < inner ℝ u u := by rw [hunorm, hbnorm]; norm_num
    nlinarith [heq]
  exact ⟨M, u, hune, fun i => absVec_nonneg b i, hmax, hMnonneg,
    mv_eq_smul_of_quadForm_eq hA hmax heq⟩

/-- **AND WITH STRICTLY POSITIVE ENTRIES, A STRICTLY POSITIVE EIGENVECTOR AND A STRICTLY POSITIVE
EIGENVALUE.** This is the Perron half of Perron–Frobenius, for the symmetric case. -/
theorem exists_pos_top_eigenvector [Nonempty n] (hA : A.IsHermitian)
    (hpos : ∀ i j, 0 < A i j) :
    ∃ (M : ℝ) (u : EuclideanSpace ℝ n), (∀ i, 0 < (WithLp.ofLp u) i) ∧
      (∀ j, hA.eigenvalues j ≤ M) ∧ 0 < M ∧ mv A u = M • u := by
  obtain ⟨M, u, hune, hunn, hmax, -, heig⟩ :=
    exists_nonneg_top_eigenvector hA (fun i j => le_of_lt (hpos i j))
  have hex : ∃ p, (WithLp.ofLp u) p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hune (by ext i; simpa using hcon i)
  obtain ⟨p, hp⟩ := hex
  have hup : 0 < (WithLp.ofLp u) p := lt_of_le_of_ne (hunn p) (Ne.symm hp)
  -- every coordinate of `A *ᵥ u` is strictly positive
  have hrowpos : ∀ i, 0 < (WithLp.ofLp (mv A u)) i := by
    intro i
    rw [mv_row]
    refine Finset.sum_pos' (fun j _ => mul_nonneg (le_of_lt (hpos i j)) (hunn j))
      ⟨p, mem_univ p, mul_pos (hpos i p) hup⟩
  have hsmul : ∀ i, (WithLp.ofLp (mv A u)) i = M * (WithLp.ofLp u) i := by
    intro i; rw [heig]; rfl
  have hMpos : 0 < M := by
    have hpp := hrowpos p
    rw [hsmul p] at hpp
    nlinarith [hpp, hup]
  refine ⟨M, u, fun i => ?_, hmax, hMpos, heig⟩
  have hii := hrowpos i
  rw [hsmul i] at hii
  nlinarith [hii, hMpos]

/-! ## 3. The wall's own matrix -/

open IsingTransfer2D IsingTransferSym in
/-- **APPLIED TO THE SYMMETRISED TWO-DIMENSIONAL ISING TRANSFER MATRIX**, which is Hermitian and
strictly positive by two theorems this estate already had.

**This is `WALLS` §W4.0 §6 item 2's first clause and not its second.** A strictly positive top
eigenvector is not a *separation*: nothing here says the top eigenvalue is simple or strictly
above the rest, and item 2 asked for exactly that.

**FORWARD POINTER, added 2026-08-22 — the sentence above is unchanged and remains true OF THIS
FILE.** The second clause is proved: `PerronSimple.top_eigenspace_dim_one` for simplicity and
`PerronGap.abs_lt_top_of_ne` for the strict domination, both consuming the vector this theorem
produces. Added because a reader landing here otherwise takes *"nothing here says"* for *"nothing
says"* — `ERRATUM 230`'s defect, whose repair is a pointer at the true claim and not a rewrite of
it. -/
theorem exists_pos_top_eigenvector_transferSym (β : ℝ) (m : ℕ) :
    ∃ (M : ℝ) (u : EuclideanSpace ℝ (Col m)), (∀ i, 0 < (WithLp.ofLp u) i) ∧
      (∀ j, (transferSym_isHermitian β m).eigenvalues j ≤ M) ∧ 0 < M ∧
      mv (transferSym β m) u = M • u :=
  exists_pos_top_eigenvector (transferSym_isHermitian β m) (fun i j => transferSym_pos β i j)

end PerronVector
