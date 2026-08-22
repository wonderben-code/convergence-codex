import TracePathSum

/-!
# The transfer identity with a different matrix at every step

`TracePathSum.sum_cyc_eq_trace` proves that the sum over cyclic configurations of the product of
transfer entries around the loop is `tr (Mᴺ⁺¹)`. **Every step uses the same matrix**, which is what
a homogeneous model needs and not what an observable needs: inserting a spin at column `k` weights
the walk at one time only, and `IsingTwoPoint.SeparatedTransferFormula` is the statement that
therefore did not follow.

This file generalises the whole of `TracePathSum` to a **sequence** of matrices — one per step —
and the separated formula is then a corollary rather than a new combinatorial argument.

## What is proved

* **`seqProd`** — the ordered product `Ms 0 · Ms 1 ⋯ Ms n`, and **`walkProdSeq`**, the product
  along an open walk taking `Ms i` at step `i`;
* **`seqProd_apply`** — `(Ms 0 ⋯ Ms n) a b` is the sum over walks of length `n+1` from `a` to `b`,
  the step-`i` factor taken from `Ms i`. This is `TracePathSum.pow_succ_apply` with the constant
  sequence;
* **`openProdSeq_cons_snoc`**, **`cyc_eq_walkProdSeq`** — the same two identifications, and the
  wrap-around is discharged in the same single place;
* **`sum_cyc_seq`** — **THE INHOMOGENEOUS TRANSFER IDENTITY**: the cyclic configuration sum with a
  different matrix at each step is the trace of their ordered product. `sum_cyc_eq_trace` is the
  constant case and `IsingTwoPoint.sum_cyc_weighted` is one diagonal factor.

**Absent from Mathlib by name**, probed 2026-08-22 against the environment dump:
`Matrix.trace_list_prod`, `Matrix.trace_prod`, `trace_prod_eq_sum`, `Matrix.prod_apply`,
`List.prod_matrix_apply`, `Matrix.trace_prod_eq` — zero each; and the unweighted case's own
absence probe is recorded in `WALLS` §W4 §6 item 3.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TracePathSeq

open TracePathSum

variable {α R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

/-! ## 1. The ordered product and the inhomogeneous walk -/

/-- **The ordered product `Ms 0 · Ms 1 ⋯ Ms n`**, `n+1` factors. -/
def seqProd (Ms : ℕ → Matrix α α R) : ℕ → Matrix α α R
  | 0 => Ms 0
  | n + 1 => Ms 0 * seqProd (fun i => Ms (i + 1)) n

/-- **The product along a walk** from `a` through the interior `s` to `b`, taking `Ms i` at
step `i`. -/
def walkProdSeq (Ms : ℕ → Matrix α α R) (b : α) : ∀ n, α → (Fin n → α) → R
  | 0, a, _ => Ms 0 a b
  | n + 1, a, s => Ms 0 a (s 0) * walkProdSeq (fun i => Ms (i + 1)) b n (s 0) (Fin.tail s)

omit [Fintype α] [DecidableEq α] in
@[simp] theorem walkProdSeq_zero (Ms : ℕ → Matrix α α R) (b a : α) (s : Fin 0 → α) :
    walkProdSeq Ms b 0 a s = Ms 0 a b := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem walkProdSeq_succ (Ms : ℕ → Matrix α α R) (b a : α) (n : ℕ)
    (s : Fin (n + 1) → α) :
    walkProdSeq Ms b (n + 1) a s
      = Ms 0 a (s 0) * walkProdSeq (fun i => Ms (i + 1)) b n (s 0) (Fin.tail s) := rfl

/-! ## 2. The ordered product's entries are the walk sums -/

omit [DecidableEq α] in
/-- **`(Ms 0 ⋯ Ms n) a b` IS THE SUM OVER WALKS** of length `n+1` from `a` to `b`, the step-`i`
factor taken from `Ms i`. The proof is `TracePathSum.pow_succ_apply`'s, with the sequence shifted
at each peel. -/
theorem seqProd_apply (Ms : ℕ → Matrix α α R) :
    ∀ (n : ℕ) (a b : α), (seqProd Ms n) a b = ∑ s : Fin n → α, walkProdSeq Ms b n a s
  | 0, a, b => by simp [seqProd]
  | n + 1, a, b => by
    have hstep : (seqProd Ms (n + 1)) a b
        = ∑ c, Ms 0 a c * (seqProd (fun i => Ms (i + 1)) n) c b := by
      rw [seqProd, Matrix.mul_apply]
    rw [hstep]
    have hIH : ∀ c, (seqProd (fun i => Ms (i + 1)) n) c b
        = ∑ t : Fin n → α, walkProdSeq (fun i => Ms (i + 1)) b n c t :=
      fun c => seqProd_apply (fun i => Ms (i + 1)) n c b
    have hleft : (∑ c, Ms 0 a c * (seqProd (fun i => Ms (i + 1)) n) c b)
        = ∑ p : α × (Fin n → α),
            Ms 0 a p.1 * walkProdSeq (fun i => Ms (i + 1)) b n p.1 p.2 := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun c _ => by rw [hIH c, Finset.mul_sum]
    rw [hleft]
    refine Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => α)
      (fun p => Ms 0 a p.1 * walkProdSeq (fun i => Ms (i + 1)) b n p.1 p.2)
      (fun s => walkProdSeq Ms b (n + 1) a s) fun p => ?_
    simp [Fin.consEquiv, Fin.tail_cons]

omit [DecidableEq α] in
/-- **AND THE TRACE IS THE SUM OVER CLOSED WALKS.** -/
theorem trace_seqProd (Ms : ℕ → Matrix α α R) (n : ℕ) :
    Matrix.trace (seqProd Ms n) = ∑ a, ∑ s : Fin n → α, walkProdSeq Ms a n a s := by
  simp only [Matrix.trace, Matrix.diag]
  exact Finset.sum_congr rfl fun a _ => seqProd_apply Ms n a a

/-! ## 3. Closing the walk up -/

/-- **The product along an OPEN path** of `n+1` points, `n` factors, step `i` taken from `Ms i`. -/
def openProdSeq (Ms : ℕ → Matrix α α R) (n : ℕ) (p : Fin (n + 1) → α) : R :=
  ∏ i : Fin n, Ms i (p i.castSucc) (p i.succ)

omit [Fintype α] [DecidableEq α] in
theorem openProdSeq_succ (Ms : ℕ → Matrix α α R) (n : ℕ) (p : Fin (n + 2) → α) :
    openProdSeq Ms (n + 1) p
      = Ms 0 (p 0) (p 1) * openProdSeq (fun i => Ms (i + 1)) n (Fin.tail p) := by
  simp only [openProdSeq, Fin.prod_univ_succ, Fin.castSucc_zero, Fin.succ_zero_eq_one]
  refine congrArg (Ms 0 (p 0) (p 1) * ·) (Finset.prod_congr rfl fun i _ => ?_)
  rw [Fin.tail, Fin.tail, Fin.val_succ, ← Fin.succ_castSucc]

omit [Fintype α] [DecidableEq α] in
/-- **THE OPEN PRODUCT ALONG `a, t, b` IS THE WALK PRODUCT**, sequence version. -/
theorem openProdSeq_cons_snoc (Ms : ℕ → Matrix α α R) (b : α) :
    ∀ (n : ℕ) (a : α) (t : Fin n → α),
      openProdSeq Ms (n + 1) (Fin.cons a (Fin.snoc t b)) = walkProdSeq Ms b n a t
  | 0, a, t => by
    have hb : (Fin.snoc t b : Fin 1 → α) 0 = b := by simp [Fin.snoc]
    simp [openProdSeq, hb]
  | n + 1, a, t => by
    rw [openProdSeq_succ, Fin.tail_cons, walkProdSeq_succ]
    have hsnoc : (Fin.snoc t b : Fin (n + 2) → α)
        = Fin.cons (t 0) (Fin.snoc (Fin.tail t) b) := by
      rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
    have h0 : (Fin.cons a (Fin.snoc t b) : Fin (n + 3) → α) 0 = a := Fin.cons_zero _ _
    have h1 : (Fin.cons a (Fin.snoc t b) : Fin (n + 3) → α) 1 = t 0 := by
      rw [← Fin.succ_zero_eq_one, Fin.cons_succ]
      simp
    rw [h0, h1, hsnoc, openProdSeq_cons_snoc (fun i => Ms (i + 1)) b n (t 0) (Fin.tail t)]

omit [Fintype α] [DecidableEq α] in
/-- **THE CYCLIC PRODUCT IS AN OPEN PRODUCT** along `s` with its own first point appended. The
matrix index does not move, so the wrap-around is discharged exactly where
`TracePathSum.cyc_eq_openProd` discharges it. -/
theorem cyc_eq_openProdSeq (Ms : ℕ → Matrix α α R) (N : ℕ) (s : Fin (N + 1) → α) :
    ∏ i : Fin (N + 1), Ms i (s i) (s (i + 1))
      = openProdSeq Ms (N + 1) (Fin.snoc s (s 0)) := by
  simp only [openProdSeq]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.snoc_castSucc]
  refine congrArg (Ms i (s i)) ?_
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.succ_last, Fin.snoc_last, Fin.last_add_one]
  · intro j
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, castSucc_add_one]

omit [Fintype α] [DecidableEq α] in
/-- **THE CYCLIC PRODUCT ALONG `s` IS THE CLOSED WALK FROM `s 0` BACK TO `s 0`.** -/
theorem cyc_eq_walkProdSeq (Ms : ℕ → Matrix α α R) (N : ℕ) (s : Fin (N + 1) → α) :
    (∏ i : Fin (N + 1), Ms i (s i) (s (i + 1)))
      = walkProdSeq Ms (s 0) N (s 0) (Fin.tail s) := by
  rw [cyc_eq_openProdSeq]
  have : (Fin.snoc s (s 0) : Fin (N + 2) → α)
      = Fin.cons (s 0) (Fin.snoc (Fin.tail s) (s 0)) := by
    rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
  rw [this, openProdSeq_cons_snoc]

/-! ## 4. The inhomogeneous transfer identity -/

omit [DecidableEq α] in
/-- **THE CYCLIC CONFIGURATION SUM WITH A DIFFERENT MATRIX AT EACH STEP IS THE TRACE OF THEIR
ORDERED PRODUCT.** `TracePathSum.sum_cyc_eq_trace` is the constant sequence and
`IsingTwoPoint.sum_cyc_weighted` is one diagonal factor. -/
theorem sum_cyc_seq (Ms : ℕ → Matrix α α R) (N : ℕ) :
    ∑ s : Fin (N + 1) → α, ∏ i : Fin (N + 1), Ms i (s i) (s (i + 1))
      = Matrix.trace (seqProd Ms N) := by
  rw [Finset.sum_congr rfl fun s _ => cyc_eq_walkProdSeq Ms N s, trace_seqProd]
  have hprod : (∑ p : α × (Fin N → α), walkProdSeq Ms p.1 N p.1 p.2)
      = ∑ a, ∑ t : Fin N → α, walkProdSeq Ms a N a t := Fintype.sum_prod_type _
  rw [← hprod]
  refine Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (N + 1) => α).symm
    (fun s => walkProdSeq Ms (s 0) N (s 0) (Fin.tail s))
    (fun p => walkProdSeq Ms p.1 N p.1 p.2) fun s => ?_
  simp [Fin.consEquiv]

/-! ## 5. Computing the ordered product for a sequence with two insertions -/

omit [DecidableEq α] in
/-- `seqProd Ms n` reads only `Ms 0, …, Ms n`. -/
theorem seqProd_congr (Ms Ns : ℕ → Matrix α α R) :
    ∀ (n : ℕ), (∀ i, i ≤ n → Ms i = Ns i) → seqProd Ms n = seqProd Ns n
  | 0, h => by simp [seqProd, h 0 (le_refl 0)]
  | n + 1, h => by
    rw [seqProd, seqProd, h 0 (Nat.zero_le _),
      seqProd_congr (fun i => Ms (i + 1)) (fun i => Ns (i + 1)) n
        (fun i hi => h (i + 1) (by omega))]

theorem seqProd_const (T : Matrix α α R) : ∀ n : ℕ, seqProd (fun _ => T) n = T ^ (n + 1)
  | 0 => by simp [seqProd]
  | n + 1 => by rw [seqProd, seqProd_const T n, ← pow_succ' T (n + 1)]

/-- **ONE INSERTION AT THE HEAD.** -/
theorem seqProd_head_const (A T : Matrix α α R) :
    ∀ n : ℕ, seqProd (fun i => if i = 0 then A else T) n = A * T ^ n
  | 0 => by simp [seqProd]
  | n + 1 => by
    rw [seqProd]
    have h0 : (if (0 : ℕ) = 0 then A else T) = A := by simp
    have h1 : (fun i : ℕ => if i + 1 = 0 then A else T) = (fun _ : ℕ => T) := by
      funext i; simp
    rw [h0, h1, seqProd_const]

omit [DecidableEq α] in
/-- **THE ORDERED PRODUCT SPLITS**, `n+1` factors then `m+1`. -/
theorem seqProd_split (Ms : ℕ → Matrix α α R) :
    ∀ (n m : ℕ), seqProd Ms (n + 1 + m)
      = seqProd Ms n * seqProd (fun i => Ms (i + n + 1)) m
  | 0, m => by
    rw [show (0 : ℕ) + 1 + m = m + 1 by omega, seqProd, seqProd]
  | n + 1, m => by
    rw [show n + 1 + 1 + m = (n + 1 + m) + 1 by omega, seqProd, seqProd,
      seqProd_split (fun i => Ms (i + 1)) n m, mul_assoc]
    refine congrArg (Ms 0 * ·) (congrArg (seqProd (fun i => Ms (i + 1)) n * ·) ?_)
    exact seqProd_congr _ _ m fun i _ => congrArg Ms (by omega)

/-! ## 6. The two-weight cyclic identity -/

/-- **THE CYCLIC SUM WITH TWO WEIGHTS, AT COLUMN `0` AND COLUMN `k+1`.** This is the shape an
observable needs and `TracePathSum.sum_cyc_eq_trace` cannot state: the second weight sits at a
fixed time, so the walk is inhomogeneous, and `sum_cyc_seq` is what makes it a trace. -/
theorem sum_cyc_two_weight (T : Matrix α α R) (w v : α → R) (k m : ℕ) :
    (∑ s : Fin (k + m + 2) → α, w (s 0) * v (s ⟨k + 1, by omega⟩)
        * ∏ i : Fin (k + m + 2), T (s i) (s (i + 1)))
      = Matrix.trace (Matrix.diagonal w * T ^ (k + 1) * Matrix.diagonal v * T ^ (m + 1)) := by
  set Ms : ℕ → Matrix α α R :=
    fun i => if i = 0 then Matrix.diagonal w * T
      else if i = k + 1 then Matrix.diagonal v * T else T with hMs
  set j : Fin (k + m + 2) := ⟨k + 1, by omega⟩ with hj
  have hjv : (j : ℕ) = k + 1 := rfl
  have hj0 : (0 : Fin (k + m + 2)) ≠ j := by
    intro h
    have h' : (0 : ℕ) = k + 1 := by
      have hval := congrArg Fin.val h
      simp [hjv] at hval
    omega
  have hfac : ∀ s : Fin (k + m + 2) → α,
      w (s 0) * v (s j) * ∏ i : Fin (k + m + 2), T (s i) (s (i + 1))
        = ∏ i : Fin (k + m + 2), Ms i (s i) (s (i + 1)) := by
    intro s
    have hpt : ∀ i : Fin (k + m + 2), Ms i (s i) (s (i + 1))
        = ((if i = 0 then w (s 0) else 1) * (if i = j then v (s j) else 1))
          * T (s i) (s (i + 1)) := by
      intro i
      by_cases h0 : i = 0
      · subst h0
        have hMs0 : Ms ((0 : Fin (k + m + 2)) : ℕ) = Matrix.diagonal w * T := by simp [hMs]
        rw [hMs0, Matrix.diagonal_mul, if_pos rfl, if_neg hj0, mul_one]
      · by_cases h1 : i = j
        · subst h1
          have hMsj : Ms ((j : Fin (k + m + 2)) : ℕ) = Matrix.diagonal v * T := by
            simp [hMs, hjv]
          rw [hMsj, Matrix.diagonal_mul, if_neg h0, if_pos rfl, one_mul]
        · have hv0 : (i : ℕ) ≠ 0 := fun h => h0 (Fin.ext (by simpa using h))
          have hv1 : (i : ℕ) ≠ k + 1 := fun h => h1 (Fin.ext (by simpa [hjv] using h))
          have hMsi : Ms (i : ℕ) = T := by simp [hMs, hv0, hv1]
          rw [hMsi, if_neg h0, if_neg h1, one_mul, one_mul]
    rw [Finset.prod_congr rfl fun i _ => hpt i, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp
  rw [Finset.sum_congr rfl fun s _ => hfac s, sum_cyc_seq]
  have hleft : seqProd Ms k = Matrix.diagonal w * T * T ^ k := by
    rw [seqProd_congr Ms (fun i => if i = 0 then Matrix.diagonal w * T else T) k
      (fun i hi => by
        by_cases h : i = 0
        · simp [hMs, h]
        · have hk : i ≠ k + 1 := by omega
          simp [hMs, h, hk])]
    exact seqProd_head_const _ _ k
  have hright : seqProd (fun i => Ms (i + k + 1)) m = Matrix.diagonal v * T * T ^ m := by
    rw [seqProd_congr _ (fun i => if i = 0 then Matrix.diagonal v * T else T) m
      (fun i _ => by
        by_cases h : i = 0
        · simp [hMs, h]
        · simp [hMs, h])]
    exact seqProd_head_const _ _ m
  rw [show k + m + 1 = k + 1 + m by omega, seqProd_split Ms k m, hleft, hright,
    mul_assoc (Matrix.diagonal w) T (T ^ k), ← pow_succ' T k,
    mul_assoc (Matrix.diagonal v) T (T ^ m), ← pow_succ' T m, ← mul_assoc]

end TracePathSeq
