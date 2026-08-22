import RayleighPow

/-!
# The gap for a PRIMITIVE symmetric matrix — one restrictive hypothesis removed

Every theorem in `PerronVector`, `PerronSimple` and `PerronGap` assumes **every entry of `A` is
strictly positive**. That is the easiest case of Perron–Frobenius and not the useful one: an
adjacency matrix has zeros on its diagonal, and a transfer matrix with any forbidden transition
has zeros off it. The classical hypothesis is **primitivity** — some power of `A` is strictly
positive — and this file replaces the one by the other for real symmetric matrices.

> **`abs_lt_max_of_ne`** — if `A` is symmetric and **some ODD power of `A` has all entries
> strictly positive**, then `|λ| < λ_max` for every eigenvalue other than the largest.
>
> **`max_pos`** — and that largest eigenvalue is strictly positive.

**WHY IT WAS NOT AVAILABLE UNTIL NOW, AND WHAT MADE IT AVAILABLE.** `PerronGap` applied to `A ^ k`
gives a gap *for `A ^ k`*, in `A ^ k`'s own eigenvalue family. Getting back to `A` needs the top
eigenvalue of `A ^ k` identified with the `k`-th power of the top eigenvalue of `A`, and that is
`RayleighPow.max_eigenvalues_pow`, proved in the previous unit. **The chain is: the eigenvectors of
`A` are eigenvectors of `A ^ k`, `PerronGap` bounds them there, and `RayleighPow` says the bound is
the right number.**

**WHY «ODD», AND WHAT IS AND IS NOT CLAIMED BY IT.** For odd `k` the map `x ↦ x ^ k` is strictly
monotone on `ℝ`, so it carries the largest eigenvalue to the largest and reflects strict
inequalities back. **For even `k` it does neither** — `x ↦ x²` sends `−5` above `3` — so **this
proof** needs odd `k` and the hypothesis says so.

**WHETHER THE THEOREM ITSELF NEEDS IT IS NOT DECIDED HERE, AND SAYING THAT IS THE POINT.** The
classical route to the even case runs *primitive ⇒ not bipartite ⇒ the spectrum is not symmetric
about `0` ⇒ `−λ_max` is not an eigenvalue*, and **none of those three steps exists in this
estate**: `bipartite` appears here only as a property of specific lattice graphs, and no theorem
anywhere relates it to a spectrum. So the odd hypothesis is a limit of the argument, **stated as
one rather than dressed up as a limit of the mathematics** (`ERRATUM 194`, `ERRATUM 219`: a
difficulty claim written without a probe is the recurring defect in this record).

**AND IT IS NOT A LOSS OF GENERALITY IN PRACTICE, WHICH IS STATED AND NOT PROVED HERE.** For a
nonnegative `A` with no zero row, `A ^ k > 0` implies `A ^ m > 0` for every `m ≥ k`, so an odd
witness always exists. **That implication is not proved in this file** and the hypothesis is
therefore stated with the odd `k` supplied, rather than derived from a bare `∃ k` — `ERRATUM 48`:
the convenient version would be asserting a step nobody took.

**WHAT DOES NOT MOVE.** This is still one finite symmetric matrix. `WALLS` §W4.0 §6 item 3 — the
passage from a spectral gap to correlation decay at `d ≥ 2` — is untouched, and a gap for a
primitive matrix at fixed side length is not a mass gap either.
-/

namespace PerronPrimitive

open Matrix Finset RayleighMatrix RayleighPow PerronGap

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- For odd `k`, `x ↦ x ^ k` carries `A`'s largest eigenvalue to the largest `k`-th power. -/
theorem pow_max (hA : A.IsHermitian) {k : ℕ} (hk : Odd k) {p : n}
    (hp : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues p) (j : n) :
    hA.eigenvalues j ^ k ≤ hA.eigenvalues p ^ k :=
  (hk.pow_le_pow).mpr (hp j)

/-- **THE LARGEST EIGENVALUE OF A PRIMITIVE SYMMETRIC MATRIX IS STRICTLY POSITIVE.** -/
theorem max_pos [Nonempty n] (hA : A.IsHermitian) {k : ℕ} (hk : Odd k)
    (hpos : ∀ i j, 0 < (A ^ k) i j) {p : n}
    (hp : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues p) : 0 < hA.eigenvalues p := by
  obtain ⟨q, hq⟩ := exists_max_eigenvalue (hA.pow k)
  have hqpos : 0 < (hA.pow k).eigenvalues q := eigenvalue_max_pos (hA.pow k) hpos hq
  have hid : (hA.pow k).eigenvalues q = hA.eigenvalues p ^ k :=
    max_eigenvalues_pow hA k (pow_max hA hk hp) hq
  rw [hid] at hqpos
  exact (hk.pow_pos_iff).mp hqpos

/-- **THE SEPARATION, FOR A PRIMITIVE SYMMETRIC MATRIX.** Every eigenvalue other than the largest
is strictly smaller **in absolute value** — with strict positivity of every entry of `A` replaced
by strict positivity of every entry of one odd power of `A`. -/
theorem abs_lt_max_of_ne [Nonempty n] (hA : A.IsHermitian) {k : ℕ} (hk : Odd k)
    (hpos : ∀ i j, 0 < (A ^ k) i j) {p : n}
    (hp : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues p) {j : n}
    (hne : hA.eigenvalues j ≠ hA.eigenvalues p) :
    |hA.eigenvalues j| < hA.eigenvalues p := by
  have hmax : ∀ i, (hA.pow k).eigenvalues i ≤ hA.eigenvalues p ^ k :=
    eigenvalues_pow_le_max hA k (pow_max hA hk hp)
  have hMpos : 0 < hA.eigenvalues p ^ k := (hk.pow_pos_iff).mpr (max_pos hA hk hpos hp)
  have hjne : hA.eigenvalues j ^ k ≠ hA.eigenvalues p ^ k := by
    intro heq
    exact hne (le_antisymm ((hk.pow_le_pow).mp heq.le) ((hk.pow_le_pow).mp heq.ge))
  have hlt : |hA.eigenvalues j ^ k| < hA.eigenvalues p ^ k :=
    abs_lt_top_of_ne (hA.pow k) hpos hmax hMpos (mv_pow_eigenvectorBasis hA k j)
      (eigenvectorBasis_ne_zero hA j) hjne
  rw [abs_pow] at hlt
  exact (hk.pow_lt_pow).mp hlt

/-! ## The old theorem is the case `k = 1`, instantiated rather than asserted

`ERRATUM 201`'s discipline: a generalisation that is never applied to the case it generalises has
its coverage merely claimed. `PerronGap.abs_eigenvalues_lt_of_ne` is recovered below by taking
`k = 1`, whose `A ^ 1 = A` is the only step.
-/

/-- **THE STRICTLY POSITIVE CASE IS `k = 1`.** This recovers `PerronGap.abs_eigenvalues_lt_of_ne`
from the primitive theorem, so the generalisation is checked against what it generalises. -/
theorem abs_lt_max_of_ne_of_pos [Nonempty n] (hA : A.IsHermitian) (hpos : ∀ i j, 0 < A i j)
    {p : n} (hp : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues p) {j : n}
    (hne : hA.eigenvalues j ≠ hA.eigenvalues p) :
    |hA.eigenvalues j| < hA.eigenvalues p :=
  abs_lt_max_of_ne hA odd_one (by simpa using hpos) hp hne

open IsingTransfer2D IsingTransferSym in
/-- **AND AT THE WALL'S OWN MATRIX**, through the `k = 1` route, which is where
`IsingTransferSym.transferSym` sits: strictly positive, hence primitive with an odd witness.

**THIS IS DELIBERATELY THE SAME STATEMENT AS `PerronGap.transferSym_eigenvalues_gap` AND IS NOT A
NEW RESULT.** It exists as the check that the generalisation covers the case it generalises, at
the one matrix this project actually cares about — the difference between a generalisation and a
claim of one. Nothing downstream should cite this in preference to `PerronGap`'s version. -/
theorem transferSym_gap_primitive (β : ℝ) (m : ℕ) :
    ∃ p : Col m, 0 < (transferSym_isHermitian β m).eigenvalues p ∧
      (∀ j, (transferSym_isHermitian β m).eigenvalues j
        ≤ (transferSym_isHermitian β m).eigenvalues p) ∧
      ∀ j, (transferSym_isHermitian β m).eigenvalues j
            ≠ (transferSym_isHermitian β m).eigenvalues p →
        |(transferSym_isHermitian β m).eigenvalues j|
          < (transferSym_isHermitian β m).eigenvalues p := by
  obtain ⟨p, hp⟩ := exists_max_eigenvalue (transferSym_isHermitian β m)
  have hpos : ∀ i j : Col m, 0 < transferSym β m i j := fun i j => transferSym_pos β i j
  have hodd : ∀ i j : Col m, 0 < (transferSym β m ^ 1) i j := by simpa using hpos
  exact ⟨p, max_pos _ odd_one hodd hp, hp,
    fun j hj => abs_lt_max_of_ne _ odd_one hodd hp hj⟩

/-! ## The theorem does not reach this project's own lattices, and that is a THEOREM here

`PROOF_STRATEGY` §6 question 1 asks what a unit unlocked. The honest answer for the theorem above
is **nothing new in this estate**, and `ERRATUM 48` says a generalisation producing no new member
has its usefulness merely asserted unless somebody checks. This section is the check, and it
returns a **negative with a proof** rather than a negative with a shrug.

`TorusBipartite.torusGraph_colorable_two` proves the periodic lattice is two-colourable at even
side length, **in every dimension**. A two-coloured graph's adjacency matrix has **no odd power
with a positive diagonal**, so it is never primitive with an odd witness, so `abs_lt_max_of_ne`
cannot be applied to it — ever, at any side length, in any dimension.

**The proof is one line of linear algebra rather than a walk count.** Conjugating by the diagonal
sign matrix of the colouring negates `A`, so `A` is similar to `−A`; an odd power is therefore
similar to its own negative and has trace zero; and a strictly positive matrix has positive trace.
-/

section Bipartite

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `±1` diagonal matrix of a two-colouring. -/
noncomputable def signOf (c : n → Bool) : Matrix n n ℝ :=
  Matrix.diagonal (fun i => if c i then (1 : ℝ) else -1)

theorem signOf_mul_self (c : n → Bool) : signOf c * signOf c = 1 := by
  rw [signOf, Matrix.diagonal_mul_diagonal]
  refine (Matrix.diagonal_eq_diagonal_iff.mpr fun i => ?_).trans Matrix.diagonal_one
  by_cases h : c i <;> simp [h]

/-- **CONJUGATING BY THE COLOUR SIGNS NEGATES A TWO-COLOURED ADJACENCY MATRIX.** -/
theorem signOf_conj (A : Matrix n n ℝ) {c : n → Bool} (hbip : ∀ i j, c i = c j → A i j = 0) :
    signOf c * A * signOf c = -A := by
  ext i j
  rw [signOf, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : c i = c j
  · simp [hbip i j h]
  · have : (if c i then (1 : ℝ) else -1) * (if c j then (1 : ℝ) else -1) = -1 := by
      cases hci : c i <;> cases hcj : c j <;> simp_all
    calc (if c i then (1:ℝ) else -1) * A i j * (if c j then (1:ℝ) else -1)
        = ((if c i then (1:ℝ) else -1) * (if c j then (1:ℝ) else -1)) * A i j := by ring
      _ = -A i j := by rw [this]; ring
    
/-- **AN ODD POWER OF A TWO-COLOURED ADJACENCY MATRIX HAS TRACE ZERO.** It is similar to its own
negative. -/
theorem trace_pow_eq_zero (A : Matrix n n ℝ) {c : n → Bool}
    (hbip : ∀ i j, c i = c j → A i j = 0) {k : ℕ} (hk : Odd k) : (A ^ k).trace = 0 := by
  have hconj : signOf c * A ^ k * signOf c = -A ^ k := by
    have hone : signOf c * signOf c = 1 := signOf_mul_self c
    have hp : ∀ m : ℕ, (signOf c * A * signOf c) ^ m = signOf c * A ^ m * signOf c := by
      intro m
      induction m with
      | zero => simp [hone]
      | succ p ih =>
          rw [pow_succ, ih, pow_succ]
          simp only [Matrix.mul_assoc]
          congr 1
          congr 1
          rw [← Matrix.mul_assoc, hone, Matrix.one_mul]
    rw [← hp k, signOf_conj A hbip, hk.neg_pow]
  have h1 : (signOf c * A ^ k * signOf c).trace = (A ^ k).trace := by
    rw [Matrix.trace_mul_cycle, signOf_mul_self, Matrix.one_mul]
  rw [hconj, Matrix.trace_neg] at h1
  linarith [h1]

/-- **SO A TWO-COLOURED GRAPH IS NEVER PRIMITIVE WITH AN ODD WITNESS**, and `abs_lt_max_of_ne`
cannot be applied to the adjacency matrix of this project's periodic lattice at any side length or
dimension — `TorusBipartite.torusGraph_colorable_two` supplies the colouring. -/
theorem not_pos_pow_of_bipartite [Nonempty n] (A : Matrix n n ℝ) {c : n → Bool}
    (hbip : ∀ i j, c i = c j → A i j = 0) {k : ℕ} (hk : Odd k) :
    ¬ (∀ i j, 0 < (A ^ k) i j) := by
  intro hpos
  have hz : (A ^ k).trace = 0 := trace_pow_eq_zero A hbip hk
  have : (0 : ℝ) < (A ^ k).trace :=
    Finset.sum_pos (fun i _ => hpos i i) Finset.univ_nonempty
  linarith [hz, this]

end Bipartite

end PerronPrimitive
