import LovelockPermutations

/-!
# The combinatorial half of step 2, without the coefficient matrix the last unit said it needed

## ERRATUM 169: the missing coefficient matrix was presented as the obstacle, and it was not one

`LovelockPermutations` closed by saying what step 2 still needed, and then said it could not be
had:

> The argument is standard — expand the assignment in coordinates, note that equivariance forces
> the coefficient matrix to depend only on whether two indices agree, so it is `α·δ + β·(all
> ones)`, and tracelessness kills the `β` term — **but every step of it needs the coefficient
> matrix built, which means representing `T` restricted to diagonal tensors as a linear map on
> `ℝⁿ` and reading off its entries. None of that is here.**

**The middle sentence is true of the argument it describes** — the coordinate expansion really
does need the coefficient matrix — and the last sentence is a plain fact about that file. **What
is wrong is the framing.** Sitting in a section headed *"What is NOT proved, and it is the half
the guess got wrong"*, it presents the un-built matrix as **what stands between the estate and
step 2**. It is not. A different argument reaches the same conclusion and never builds one, and
this file is that argument: **no linear map on `ℝⁿ` is defined anywhere below, no basis is
chosen, and no matrix entry is read off.**

**Why that is an erratum and not merely an improvement.** The paragraph did not say *"here is one
route, and it needs a matrix"*. It said every step of the argument needs one, in the section where
this campaign records what it cannot do — so it reads as a claim about an **obstacle** rather
than about a **choice of route**, and a claim about an obstacle is a claim about an object I had
not constructed: the proof that avoids it. That is the same shape as `ERRATA 163`, `164` and
`165`. The aggravating detail is *where* it sits: a sentence in the "what is NOT proved" section
is the least likely in the file to be re-read sceptically, because that section is where the file
is already being honest.

## What replaces the coefficient matrix

**Two witnesses at a time.** For `i ≠ j`, `hIJ i j` is the diagonal 2-tensor with `+1` at `i`,
`−1` at `j` and `0` elsewhere — traceless, symmetric, and requiring no basis to name. From it:

* `ricciSeed h` is an algebraic curvature tensor built from a symmetric `h` as
  `(n−2)⁻¹ · (h ⊙ δ)`, and for **traceless** `h` it is its own Ricci summand with
  `tracefreeRicci (ricciSeed h) = h` (`tracefreeRicci_ricciSeed`, `ricciPart_ricciSeed`). So
  `RicciProportional`'s subject `T (ricciPart R)` is available at `R = ricciSeed h` **without
  quantifying over all `R` and without inverting `tracefreeRicci`** — the seed is the inverse,
  written down;
* the transposition `(i j)` sends `hIJ i j` to **minus itself** (`hIJ_perm` at
  `Equiv.swap i j`), so equivariance plus homogeneity gives
  `T (ricciSeed (hIJ i j)) (τ b) (τ c) = − T (ricciSeed (hIJ i j)) b c`. **A number equal to its
  own negative is zero**, exactly as in step 1, and it kills every diagonal entry away from `i`
  and `j` at once (`T_ricciSeed_hIJ_eq_zero`) while forcing the entry at `j` to be the negative of
  the entry at `i` (`T_ricciSeed_hIJ_j`);
* step 1 kills the off-diagonal (`T_ricciSeed_hIJ_offDiag`).

Those three facts are what the coefficient matrix was going to be used to establish, and together
they say

    T (ricciSeed (hIJ i j)) b c  =  α · hIJ i j b c ,      α = T (ricciSeed (hIJ i j)) i i

which is `T_ricciSeed_hIJ_eq_smul` — **`T` is a multiple of the identity on the witness**.

**And `α` is a single constant.** Three theorems get there, each moving one thing:
`T_ricciSeed_hIJ_diag_const` moves the first index by a second transposition with `j` held fixed;
`T_ricciSeed_hIJ_diag_const_snd` moves the second with `i` held fixed; and
`T_ricciSeed_hIJ_diag_symm` swaps the pair using **no permutation at all** — the witness is
negated, so the answer is, and the entry at `j` was already minus the entry at `i`. The first two
chain to any pair of pairs except when `i = j'`, and that case is exactly the third.
`T_ricciSeed_hIJ_diag_eq` is the assembly.

**And the transposition rung carries no dimension hypothesis.** `T_ricciSeed_hIJ_swap`,
`_eq_zero`, `_j` and all four constancy theorems take neither `(n:ℝ) − 2 ≠ 0` nor `n ≥ 3`. `hn2`
enters through one door only — the inversion `tracefreeRicci_ricciSeed` — and so reaches exactly
`ricciPart_ricciSeed`, `T_ricciSeed_hIJ_offDiag`, and the two assemblies built on those.

**Why no matrix is needed.** The coefficient-matrix route asks what `T` does to each basis vector
and assembles the answers; this route asks what `T` must do to *one* tensor that a group element
negates. The first needs coordinates on the space of diagonal tensors; the second needs one
element of `Equiv.Perm (Fin n)` and the fact that `ℝ` has no element equal to its own negative
except zero.

## What is still not here, stated as a fact about this file

**Step 2 is not finished.** What is proved is the conclusion **on the witnesses `hIJ i j`**. Going
from there to *every* traceless diagonal `h` is the expansion `h = ∑_{i ≠ j₀} h ᵢᵢ · hIJ i j₀`,
which is an identity of functions that tracelessness makes true, followed by pushing `T` across a
`Finset.sum` using the additivity hypothesis `hadd`. That is real work of a different kind —
induction over a `Finset` with `T` applied to a sum of *functions* — and **it is not in this
file.** This sentence is a claim about this file and nothing else; it says nothing about whether
that expansion is hard, because I have not attempted it.

§4 restates the conclusion in `RicciProportional`'s own shape at `R = ricciSeed (hIJ i j)`
(`T_ricciPart_ricciSeed_hIJ`), so that the connection to the open `Prop` is machine-checked rather
than asserted here. **It is the `Prop` at one tensor, not the `Prop`.**

**Step 3 is untouched** and is where the refusal stands: the spectral theorem carried across to
`IsOrth`. **And nothing here bears on `KillsWeyl`.** The watchlist item does not move.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockDiagonalWitness

open AlgebraicCurvature LovelockProjections LovelockEquivariance LovelockReflections
  LovelockPermutations Finset

variable {n : ℕ}

/-! ## 1. The two-index witness

`hIJ i j` is `+1` at `i`, `−1` at `j`, zero elsewhere, and zero off the diagonal. It is traceless
and symmetric, and naming it costs no basis and no coordinates.
-/

/-- **THE WITNESS.** Diagonal, `+1` at `i`, `−1` at `j`. -/
def hIJ (i j : Fin n) (b c : Fin n) : ℝ :=
  if b = c then (if b = i then 1 else if b = j then -1 else 0) else 0

theorem hIJ_offDiag (i j : Fin n) {b c : Fin n} (hbc : b ≠ c) : hIJ i j b c = 0 := by
  simp [hIJ, hbc]

theorem hIJ_at_i (i j : Fin n) : hIJ i j i i = 1 := by simp [hIJ]

theorem hIJ_at_j {i j : Fin n} (hij : i ≠ j) : hIJ i j j j = -1 := by
  simp [hIJ, Ne.symm hij]

theorem hIJ_at_other {i j b : Fin n} (hbi : b ≠ i) (hbj : b ≠ j) : hIJ i j b b = 0 := by
  simp [hIJ, hbi, hbj]

theorem hIJ_symm (i j : Fin n) (b c : Fin n) : hIJ i j b c = hIJ i j c b := by
  rcases eq_or_ne b c with rfl | hbc
  · rfl
  · rw [hIJ_offDiag i j hbc, hIJ_offDiag i j (Ne.symm hbc)]

/-- **AND IT IS TRACELESS**, which is the one property `ricciSeed` needs of it. -/
theorem hIJ_trace {i j : Fin n} (hij : i ≠ j) : ∑ b, hIJ i j b b = 0 := by
  have hfun : ∀ b : Fin n,
      hIJ i j b b = (if b = i then (1 : ℝ) else 0) - (if b = j then (1 : ℝ) else 0) := by
    intro b
    by_cases hbi : b = i
    · have hbj : b ≠ j := by rw [hbi]; exact hij
      rw [hbi, hIJ_at_i, if_pos rfl, if_neg (by rw [← hbi]; exact hbj)]
      norm_num
    · by_cases hbj : b = j
      · rw [hbj, hIJ_at_j hij, if_pos rfl, if_neg (by rw [← hbj]; exact hbi)]
        norm_num
      · rw [hIJ_at_other hbi hbj, if_neg hbi, if_neg hbj]
        norm_num
  rw [Finset.sum_congr rfl fun b _ => hfun b, Finset.sum_sub_distrib]
  simp

/-- **A RELABELLING MOVES THE TWO INDICES AND DOES NOTHING ELSE.** This is the only fact about
permutations the file needs, and it replaces the whole coefficient-matrix computation. -/
theorem hIJ_perm (σ : Equiv.Perm (Fin n)) (i j b c : Fin n) :
    hIJ i j (σ b) (σ c) = hIJ (σ.symm i) (σ.symm j) b c := by
  have key : ∀ x y : Fin n, (σ x = y) ↔ (x = σ.symm y) := fun x y =>
    ⟨fun h => by rw [← h, Equiv.symm_apply_apply], fun h => by rw [h, Equiv.apply_symm_apply]⟩
  simp only [hIJ]
  rcases eq_or_ne b c with rfl | hbc
  · rw [if_pos rfl, if_pos rfl]
    by_cases h1 : b = σ.symm i
    · rw [if_pos h1, if_pos ((key b i).mpr h1)]
    · rw [if_neg h1, if_neg fun hc => h1 ((key b i).mp hc)]
      by_cases h2 : b = σ.symm j
      · rw [if_pos h2, if_pos ((key b j).mpr h2)]
      · rw [if_neg h2, if_neg fun hc => h2 ((key b j).mp hc)]
  · rw [if_neg fun hc => hbc (σ.injective hc), if_neg hbc]

/-- **AND THE TRANSPOSITION OF THE TWO INDICES NEGATES IT.** The whole of step 2's combinatorics
sits on this line. -/
theorem hIJ_swap {i j : Fin n} (hij : i ≠ j) (b c : Fin n) : hIJ j i b c = -(hIJ i j b c) := by
  rcases eq_or_ne b c with rfl | hbc
  · by_cases hbi : b = i
    · rw [hbi, hIJ_at_i, hIJ_at_j (Ne.symm hij)]
    · by_cases hbj : b = j
      · rw [hbj, hIJ_at_i, hIJ_at_j hij]
        norm_num
      · rw [hIJ_at_other hbj hbi, hIJ_at_other hbi hbj]
        norm_num
  · rw [hIJ_offDiag j i hbc, hIJ_offDiag i j hbc]
    norm_num

/-! ## 2. The seed, which inverts `tracefreeRicci` instead of quantifying over `R`

`RicciProportional` is a statement about `T (ricciPart R)`. To test it on a chosen 2-tensor one
needs an `R` whose traceless Ricci tensor *is* that tensor. For traceless symmetric `h` the
Kulkarni–Nomizu product against the metric supplies one outright, and it is its own Ricci summand.
-/

/-- **THE SEED.** `(n−2)⁻¹ · (h ⊙ δ)`. -/
noncomputable def ricciSeed (h : Fin n → Fin n → ℝ) (a b c d : Fin n) : ℝ :=
  (1 / ((n : ℝ) - 2)) * kn h delta a b c d

theorem isAlgCurv_ricciSeed {h : Fin n → Fin n → ℝ} (hs : ∀ a b, h a b = h b a) :
    IsAlgCurv (ricciSeed h) :=
  isAlgCurv_smul _ (isAlgCurv_kn hs delta_symm)

theorem ricci_ricciSeed (h : Fin n → Fin n → ℝ) (b c : Fin n) :
    ricci (ricciSeed h) b c
      = (1 / ((n : ℝ) - 2)) * ((∑ a, h a a) * delta b c + ((n : ℝ) - 2) * h b c) := by
  have hfun : ricciSeed h = fun a b c d => (1 / ((n : ℝ) - 2)) * kn h delta a b c d := rfl
  rw [hfun, ricci_smul, ricci_kn_delta]

theorem scal_ricciSeed_of_traceless {h : Fin n → Fin n → ℝ} (htr : ∑ a, h a a = 0) :
    scal (ricciSeed h) = 0 := by
  have hb : ∀ b : Fin n,
      ricci (ricciSeed h) b b = (1 / ((n : ℝ) - 2)) * (((n : ℝ) - 2) * h b b) := by
    intro b
    rw [ricci_ricciSeed, htr, delta_self]
    ring
  have hs : scal (ricciSeed h) = ∑ b, ricci (ricciSeed h) b b := rfl
  rw [hs, Finset.sum_congr rfl fun b _ => hb b, ← Finset.mul_sum, ← Finset.mul_sum, htr,
    mul_zero, mul_zero]

/-- **THE SEED INVERTS `tracefreeRicci`.** -/
theorem tracefreeRicci_ricciSeed (hn2 : (n : ℝ) - 2 ≠ 0) {h : Fin n → Fin n → ℝ}
    (htr : ∑ a, h a a = 0) : tracefreeRicci (ricciSeed h) = h := by
  funext b c
  rw [tracefreeRicci, scal_ricciSeed_of_traceless htr, ricci_ricciSeed, htr]
  field_simp
  ring

/-- **AND THE SEED IS ITS OWN RICCI SUMMAND**, so `RicciProportional`'s subject is reachable at it
without quantifying over every algebraic curvature tensor. -/
theorem ricciPart_ricciSeed (hn2 : (n : ℝ) - 2 ≠ 0) {h : Fin n → Fin n → ℝ}
    (htr : ∑ a, h a a = 0) : ricciPart (ricciSeed h) = ricciSeed h := by
  funext a b c d
  have h1 : ricciPart (ricciSeed h) a b c d
      = (1 / ((n : ℝ) - 2)) * kn (tracefreeRicci (ricciSeed h)) delta a b c d := rfl
  rw [h1, tracefreeRicci_ricciSeed hn2 htr]
  rfl

/-- The seed transports along a frame change, because `kn` does and `δ` is fixed. -/
theorem act_ricciSeed {Q : Fin n → Fin n → ℝ} (hQ : IsOrth Q) (h : Fin n → Fin n → ℝ) :
    act Q (ricciSeed h) = ricciSeed (act2 Q h) := by
  funext a b c d
  have h1 : act Q (ricciSeed h) a b c d
      = (1 / ((n : ℝ) - 2)) * act Q (kn h delta) a b c d := by
    simp only [act, ricciSeed, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [h1, act_kn, act2_delta_fun hQ]
  rfl

/-- And it is odd, which is what turns the transposition into a sign. -/
theorem ricciSeed_neg (h : Fin n → Fin n → ℝ) :
    ricciSeed (fun x y => -(h x y)) = fun a b c d => (-1 : ℝ) * ricciSeed h a b c d := by
  funext a b c d
  simp only [ricciSeed, kn]
  ring

/-! ## 3. What an equivariant `T` must do to the witness -/

variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-- Relabelling the 2-tensor relabels `T`'s answer, one step from `T_act_permMat`. -/
theorem T_ricciSeed_perm
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {h : Fin n → Fin n → ℝ} (hs : ∀ a b, h a b = h b a)
    (σ : Equiv.Perm (Fin n)) (b c : Fin n) :
    T (ricciSeed (act2 (permMat σ) h)) b c = T (ricciSeed h) (σ b) (σ c) := by
  rw [← act_ricciSeed (isOrth_permMat σ) h,
    hequiv (permMat σ) (isOrth_permMat σ) (ricciSeed h) (isAlgCurv_ricciSeed hs) b c,
    act2_permMat]

/-- Negating the 2-tensor negates `T`'s answer, by homogeneity at `lam = −1`. -/
theorem T_ricciSeed_neg
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (h : Fin n → Fin n → ℝ) (b c : Fin n) :
    T (ricciSeed (fun x y => -(h x y))) b c = -(T (ricciSeed h) b c) := by
  rw [ricciSeed_neg, hsmul]
  norm_num

/-- **THE RUNG, AND IT IS THE SAME RUNG AS STEP 1'S.** The transposition `(i j)` negates the
witness, so `T`'s answer at the relabelled entry is minus its answer at the entry. -/
theorem T_ricciSeed_hIJ_swap
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i j : Fin n} (hij : i ≠ j) (b c : Fin n) :
    T (ricciSeed (hIJ i j)) (Equiv.swap i j b) (Equiv.swap i j c)
      = -(T (ricciSeed (hIJ i j)) b c) := by
  have hact : act2 (permMat (Equiv.swap i j)) (hIJ i j) = fun x y => -(hIJ i j x y) := by
    funext x y
    rw [act2_permMat, hIJ_perm, Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_right,
      hIJ_swap hij]
  rw [← T_ricciSeed_perm hequiv (hIJ_symm i j) (Equiv.swap i j) b c, hact,
    T_ricciSeed_neg hsmul]

/-- **EVERY DIAGONAL ENTRY AWAY FROM `i` AND `j` VANISHES**, because the transposition fixes it and
the rung says it is its own negative. -/
theorem T_ricciSeed_hIJ_eq_zero
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i j : Fin n} (hij : i ≠ j) {b : Fin n} (hbi : b ≠ i) (hbj : b ≠ j) :
    T (ricciSeed (hIJ i j)) b b = 0 := by
  have h := T_ricciSeed_hIJ_swap hsmul hequiv hij b b
  rw [Equiv.swap_apply_of_ne_of_ne hbi hbj] at h
  linarith

/-- **AND THE ENTRY AT `j` IS MINUS THE ENTRY AT `i`.** -/
theorem T_ricciSeed_hIJ_j
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i j : Fin n} (hij : i ≠ j) :
    T (ricciSeed (hIJ i j)) j j = -(T (ricciSeed (hIJ i j)) i i) := by
  have h := T_ricciSeed_hIJ_swap hsmul hequiv hij i i
  rwa [Equiv.swap_apply_left] at h

/-- The off-diagonal is step 1's, applied at the seed. -/
theorem T_ricciSeed_hIJ_offDiag (hn2 : (n : ℝ) - 2 ≠ 0)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i j : Fin n} (hij : i ≠ j) {b c : Fin n} (hbc : b ≠ c) :
    T (ricciSeed (hIJ i j)) b c = 0 := by
  have hdiag : ∀ x y : Fin n, x ≠ y → tracefreeRicci (ricciSeed (hIJ i j)) x y = 0 := by
    intro x y hxy
    rw [tracefreeRicci_ricciSeed hn2 (hIJ_trace hij)]
    exact hIJ_offDiag i j hxy
  have key := T_ricciPart_diagonal hequiv (isAlgCurv_ricciSeed (hIJ_symm i j)) hdiag hbc
  rwa [ricciPart_ricciSeed hn2 (hIJ_trace hij)] at key

/-- **STEP 2 ON THE WITNESS: `T` IS A MULTIPLE OF THE IDENTITY THERE**, and the multiple is read
off the single entry `(i,i)`. No coefficient matrix was built to get here. Whether the multiple is
the same for every pair `(i,j)` is the next two theorems, and they answer it one index at a
time. -/
theorem T_ricciSeed_hIJ_eq_smul (hn2 : (n : ℝ) - 2 ≠ 0)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i j : Fin n} (hij : i ≠ j) (b c : Fin n) :
    T (ricciSeed (hIJ i j)) b c = T (ricciSeed (hIJ i j)) i i * hIJ i j b c := by
  rcases eq_or_ne b c with rfl | hbc
  · by_cases hbi : b = i
    · rw [hbi, hIJ_at_i]
      ring
    · by_cases hbj : b = j
      · rw [hbj, hIJ_at_j hij, T_ricciSeed_hIJ_j hsmul hequiv hij]
        ring
      · rw [T_ricciSeed_hIJ_eq_zero hsmul hequiv hij hbi hbj, hIJ_at_other hbi hbj]
        ring
  · rw [T_ricciSeed_hIJ_offDiag hn2 hequiv hij hbc, hIJ_offDiag i j hbc]
    ring

/-- **AND THE MULTIPLE DOES NOT DEPEND ON THE FIRST INDEX**, by a second transposition — this one
moving `i` while fixing `j`. This is the form the expansion at a fixed second index needs. -/
theorem T_ricciSeed_hIJ_diag_const
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i i' j : Fin n} (hij : i ≠ j) (hij' : i' ≠ j) :
    T (ricciSeed (hIJ i' j)) i' i' = T (ricciSeed (hIJ i j)) i i := by
  rcases eq_or_ne i i' with rfl | hii'
  · rfl
  · have hact : act2 (permMat (Equiv.swap i i')) (hIJ i j) = hIJ i' j := by
      funext x y
      rw [act2_permMat, hIJ_perm, Equiv.symm_swap, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hij) (Ne.symm hij')]
    have h := T_ricciSeed_perm hequiv (hIJ_symm i j) (Equiv.swap i i') i' i'
    rwa [hact, Equiv.swap_apply_right] at h

/-- **AND NOT ON THE SECOND EITHER**, by the transposition that moves `j` and fixes `i`. Both
hypotheses are needed for that: the swap must miss `i` at both ends. -/
theorem T_ricciSeed_hIJ_diag_const_snd
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i j j' : Fin n} (hij : i ≠ j) (hij' : i ≠ j') :
    T (ricciSeed (hIJ i j')) i i = T (ricciSeed (hIJ i j)) i i := by
  rcases eq_or_ne j j' with rfl | hjj'
  · rfl
  · have hact : act2 (permMat (Equiv.swap j j')) (hIJ i j) = hIJ i j' := by
      funext x y
      rw [act2_permMat, hIJ_perm, Equiv.symm_swap,
        Equiv.swap_apply_of_ne_of_ne hij hij', Equiv.swap_apply_left]
    have h := T_ricciSeed_perm hequiv (hIJ_symm i j) (Equiv.swap j j') i i
    rwa [hact, Equiv.swap_apply_of_ne_of_ne hij hij'] at h

/-- **SWAPPING THE PAIR LEAVES THE MULTIPLE ALONE**, and this one needs no permutation at all: the
witness is negated, so `T`'s answer is, and the entry at `j` was already minus the entry at `i`. -/
theorem T_ricciSeed_hIJ_diag_symm
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i j : Fin n} (hij : i ≠ j) :
    T (ricciSeed (hIJ j i)) j j = T (ricciSeed (hIJ i j)) i i := by
  have hfun : hIJ j i = fun x y => -(hIJ i j x y) :=
    funext fun x => funext fun y => hIJ_swap hij x y
  rw [hfun, T_ricciSeed_neg hsmul, T_ricciSeed_hIJ_j hsmul hequiv hij, neg_neg]

/-- **SO THE MULTIPLE IS A SINGLE CONSTANT**, the same for every ordered pair of distinct indices.
The two one-index moves chain directly unless `i = j'`, and that case is the swap above. -/
theorem T_ricciSeed_hIJ_diag_eq
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i j i' j' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j') :
    T (ricciSeed (hIJ i' j')) i' i' = T (ricciSeed (hIJ i j)) i i := by
  rcases eq_or_ne i j' with heq | hne
  · have hii' : i ≠ i' := by rw [heq]; exact Ne.symm hij'
    have h1 : T (ricciSeed (hIJ i' j')) i' i' = T (ricciSeed (hIJ i i')) i i := by
      rw [← heq]
      exact T_ricciSeed_hIJ_diag_symm hsmul hequiv hii'
    rw [h1, T_ricciSeed_hIJ_diag_const_snd hequiv hij hii']
  · rw [T_ricciSeed_hIJ_diag_const hequiv hne hij',
      T_ricciSeed_hIJ_diag_const_snd hequiv hij hne]

/-! ## 4. The same statement in the shape `RicciProportional` is written in

`LovelockReduction.RicciProportional T α` reads `T (ricciPart R) b c = α * tracefreeRicci R b c`.
The theorems above are stated on the seed rather than on `ricciPart`, because that is where the
argument happens; this restates the conclusion in the open `Prop`'s own shape at `R = ricciSeed
(hIJ i j)`, so that the connection is machine-checked rather than asserted in prose. **It is the
`Prop` at one tensor, not the `Prop`** — `RicciProportional` quantifies over every algebraic
curvature tensor, and getting there needs the expansion this file does not do.
-/

/-- **`RicciProportional`'S OWN EQUATION, AT THE WITNESS.** -/
theorem T_ricciPart_ricciSeed_hIJ (hn2 : (n : ℝ) - 2 ≠ 0)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i j : Fin n} (hij : i ≠ j) (b c : Fin n) :
    T (ricciPart (ricciSeed (hIJ i j))) b c
      = T (ricciSeed (hIJ i j)) i i * tracefreeRicci (ricciSeed (hIJ i j)) b c := by
  rw [ricciPart_ricciSeed hn2 (hIJ_trace hij), tracefreeRicci_ricciSeed hn2 (hIJ_trace hij)]
  exact T_ricciSeed_hIJ_eq_smul hn2 hsmul hequiv hij b c

end LovelockDiagonalWitness
