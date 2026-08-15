import LovelockWitnessCount

/-!
# The witness family had more relations in it, and they close the last parameter

`WALLS` §W5.0 §5e records the direct route's count — what an equivariant `T` can do to the explicit
Weyl witness `W = weylPart (knSquare (twoProj i j))` — falling `n² → n → 2 → 1`, and stopping at

> `2(n−1)·T W i i + (n−1)(n−2)·T W k k = 0`

with the comment that **one is not zero** and that this is where the route ends. **The reason given
for it ending is false, and this file is the correction.** §5e said:

> no further relation is available *from this family* … the only linear relation the family
> satisfies is the one that produces `constCurv`.

**There are `n` more, one for each index**, they were never looked for, and together they force
`T W = 0`. `ERRATUM 175` records the claim; this header records the mathematics.

## The relation that was missed

The global relation §5e used is `∑ᵢ∑ⱼ knSquare (twoProj i j) = 2·constCurv n`
(`LovelockWitnessSum.sum_knSquare_twoProj`), whose Weyl part vanishes. **Fix `i` and sum over `j`
alone** and something better happens:

* `sum_knSquare_twoProj_row` — `∑ⱼ knSquare (twoProj i j) = (oneProj i) ⊙ δ`, where `oneProj i` is
  the rank-one diagonal projector. Four delta contractions; `knSquare (twoProj i j)` is exactly
  `oneProj i ⊙ oneProj j` once the two square terms cancel, and `∑ⱼ oneProj j = δ`;
* **`weylPart_kn_delta`** — and **the Weyl part of `h ⊙ δ` is zero for every `h`.** Computed from
  `LovelockProjections.ricci_kn_delta`: the trace-free Ricci tensor of `h ⊙ δ` is
  `(n−2)(h − (tr h/n) δ)`, so `ricciPart (h ⊙ δ) = h ⊙ δ − (2 tr h/n)·constCurv` and
  `scalPart (h ⊙ δ)` is exactly that correction back. **`h` is not assumed symmetric** — the
  computation never needs it, and the hypothesis was written down and then not taken;
* `sum_weylPart_twoProj_row` — hence `∑ⱼ weylPart (knSquare (twoProj i j)) = 0`, **for each fixed
  `i` separately**. The global relation of §5e is the sum of these `n`, which is why it is weaker.

The scalar curvature of `h ⊙ δ` is `LovelockOrthogonality.scal_kn_delta`, which already existed.
**A copy of it was written here and committed before the fourth review question was asked**; it is
gone and `ERRATUM 176` records why the question was skipped.

## And the count finishes

* `T_sum_weyl_twoProj_row` — `T` across the row sum, by `LovelockDiagonalSum.T_sum`;
* `sum_row_i`, `sum_row_k` — the two counts, with no curvature in them;
* **`T_weyl_twoProj_eq_zero`** — reading the row sum at `(i,i)` gives `(n−1)·a = 0`, and reading it
  at `(k,k)` for `k ∉ {i,j}` gives `a + (n−2)·b = 0`. **Two equations, two unknowns, and at
  `n ≥ 3` both values are zero.** With `LovelockWeylTwoValues.T_weyl_twoProj_shape` that is
  `T (weylPart (knSquare (twoProj i j))) = 0` at every entry.

## What this is, stated carefully, because it is easy to over-read

**It is `KillsWeyl` on the witness family, unconditionally, at every `n ≥ 3`** — and the family is
not trivial: `WeylNonzeroGeneral` shows `weylPart (knSquare (twoProj i j))` is **non-zero** at every
`n ≥ 4`, which is the dimension range the whole question lives in. So an equivariant `T` is now
known to annihilate an explicit non-zero Weyl tensor in every dimension of interest, with no
hypothesis beyond additivity, homogeneity and equivariance.

**IT IS NOT `KillsWeyl`.** `KillsWeyl T` quantifies over **every** algebraic curvature tensor, and
this file evaluates `T` on one orbit's worth. The step from here to there is exactly §5b's question
— whether the `O(n)`-orbit of `W` spans the Weyl summand — and **nothing here touches it.**

**What has changed is the size of the remaining gap on this route, and that is worth stating
exactly.** Before this file the direct route needed two things: kill the last free parameter, and
span. **Now it needs one: span.** `WALLS` §W5.0 §5e is corrected in place and `ERRATUM 175` records
why the sentence that said otherwise was written. **The watchlist item does not move**, because the
item is the classification and the classification still turns on the span.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockWitnessRowSum

open AlgebraicCurvature LovelockProjections LovelockEquivariance LovelockOrthogonality
  LovelockDiagonalSum WeylNonzeroGeneral LovelockWeylTwoValues LovelockWitnessSum
  LovelockWitnessTransport LovelockWitnessCount Finset

variable {n : ℕ}

/-- **THE RANK-ONE DIAGONAL PROJECTOR** at `i`. `twoProj i j` is `oneProj i + oneProj j`. -/
def oneProj (i : Fin n) (a b : Fin n) : ℝ := delta a i * delta b i

/-- **THE ROW SUM.** Summing the witnesses over the second index alone gives the Kulkarni–Nomizu
product of the rank-one projector with the metric. The two square terms in `knSquare (twoProj i j)`
cancel, leaving the cross term `oneProj i ⊙ oneProj j`, and `∑ⱼ oneProj j = δ`. -/
theorem sum_knSquare_twoProj_row (i : Fin n) (a b c d : Fin n) :
    ∑ j, knSquare (twoProj i j) a b c d = kn (oneProj i) delta a b c d := by
  have hterm : ∀ j : Fin n, knSquare (twoProj i j) a b c d
      = (delta a i * delta d i) * (delta b j * delta c j)
        + (delta a j * delta d j) * (delta b i * delta c i)
        - (delta a i * delta c i) * (delta b j * delta d j)
        - (delta a j * delta c j) * (delta b i * delta d i) := by
    intro j; simp only [knSquare, twoProj]; ring
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul,
    sum_delta_right b c, sum_delta_right a d, sum_delta_right b d, sum_delta_right a c]
  simp only [kn, oneProj]

/-- And its trace-free Ricci tensor, which is `(n−2)` times the trace-free part of `h`. -/
theorem tracefreeRicci_kn_delta (hn0 : (n : ℝ) ≠ 0) (h : Fin n → Fin n → ℝ) :
    tracefreeRicci (kn h delta)
      = fun x y => ((n : ℝ) - 2) * (h x y - ((∑ z, h z z) / (n : ℝ)) * delta x y) := by
  funext x y
  rw [tracefreeRicci, ricci_kn_delta, scal_kn_delta]
  field_simp
  ring

/-- **`h ⊙ δ` HAS NO WEYL PART, FOR EVERY `h`.** `ricciPart` recovers all of it except a multiple
of `constCurv`, and `scalPart` is exactly that multiple. **Symmetry of `h` is not assumed** — the
computation runs on `ricci_kn_delta`, which does not use it either. -/
theorem weylPart_kn_delta (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0) (hn2 : (n : ℝ) - 2 ≠ 0)
    (h : Fin n → Fin n → ℝ) (a b c d : Fin n) :
    weylPart (kn h delta) a b c d = 0 := by
  simp only [weylPart, ricciPart, scalPart, tracefreeRicci_kn_delta hn0 h, scal_kn_delta,
    knSquare_delta]
  simp only [kn, constCurv]
  field_simp
  ring

/-- **AND SO THE WITNESSES IN ONE ROW HAVE WEYL PARTS SUMMING TO ZERO** — `n` relations where
`WALLS` §W5.0 §5e recorded one, the one it recorded being their sum. -/
theorem sum_weylPart_twoProj_row (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0)
    (hn2 : (n : ℝ) - 2 ≠ 0) (i : Fin n) (a b c d : Fin n) :
    ∑ j, weylPart (knSquare (twoProj i j)) a b c d = 0 := by
  have hfun : (fun x y z w => ∑ j : Fin n, knSquare (twoProj i j) x y z w)
      = kn (oneProj i) delta :=
    funext fun x => funext fun y => funext fun z => funext fun w =>
      sum_knSquare_twoProj_row i x y z w
  have hstep : ∑ j : Fin n, weylPart (knSquare (twoProj i j)) a b c d
      = weylPart (fun x y z w => ∑ j : Fin n, knSquare (twoProj i j) x y z w) a b c d :=
    (weylPart_sum (fun j => knSquare (twoProj i j)) a b c d).symm
  rw [hstep, hfun, weylPart_kn_delta hn0 hn1 hn2]

variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-- `T` pushed across the row sum. -/
theorem T_sum_weyl_twoProj_row
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0) (hn2 : (n : ℝ) - 2 ≠ 0)
    (i : Fin n) (b c : Fin n) :
    ∑ j, T (weylPart (knSquare (twoProj i j))) b c = 0 := by
  have hzero : (fun x y z w => ∑ j : Fin n, weylPart (knSquare (twoProj i j)) x y z w)
      = fun _ _ _ _ => (0 : ℝ) :=
    funext fun x => funext fun y => funext fun z => funext fun w =>
      sum_weylPart_twoProj_row hn0 hn1 hn2 i x y z w
  have h1 : T (fun x y z w => ∑ j : Fin n, weylPart (knSquare (twoProj i j)) x y z w) b c
      = ∑ j : Fin n, T (weylPart (knSquare (twoProj i j))) b c :=
    T_sum hadd hsmul univ (fun j => weylPart (knSquare (twoProj i j))) b c
  rw [hzero, T_zero hsmul] at h1
  exact h1.symm

/-- Counting the row at the distinguished index: one term vanishes, `n − 1` are equal. -/
theorem sum_row_i (F : Fin n → ℝ) (i : Fin n) (v : ℝ)
    (hself : F i = 0) (hother : ∀ j, j ≠ i → F j = v) :
    ∑ j, F j = ((n : ℝ) - 1) * v := by
  classical
  have hcast1 : ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have h1 : (1 : ℕ) ≤ n := Fin.pos i
    push_cast [Nat.cast_sub h1]
    ring
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hself, zero_add,
    Finset.sum_congr rfl fun j hj => hother j (Finset.mem_erase.mp hj).1,
    Finset.sum_const, nsmul_eq_mul, hcast1]

/-- Counting the row at an outside index: one term vanishes, one is exceptional, `n − 2` are
equal. -/
theorem sum_row_k (F : Fin n → ℝ) (i k : Fin n) (hki : k ≠ i) (u v : ℝ)
    (hself : F i = 0) (hk : F k = u) (hother : ∀ j, j ≠ i → j ≠ k → F j = v) :
    ∑ j, F j = u + ((n : ℝ) - 2) * v := by
  classical
  have hkmem : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩
  have hcard2 : (((Finset.univ.erase i).erase k).card : ℝ) = (n : ℝ) - 2 := by
    rw [Finset.card_erase_of_mem hkmem, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
    have h2 : 2 ≤ n := by
      have hlt : 1 < Fintype.card (Fin n) := Fintype.one_lt_card_iff.mpr ⟨k, i, hki⟩
      simpa using hlt
    have hsub : n - 1 - 1 = n - 2 := by omega
    rw [hsub]
    push_cast [Nat.cast_sub h2]
    ring
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hself, zero_add,
    ← Finset.add_sum_erase _ _ hkmem, hk]
  congr 1
  rw [Finset.sum_congr rfl fun j hj => hother j
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase hj)).1 (Finset.mem_erase.mp hj).1,
    Finset.sum_const, nsmul_eq_mul, hcard2]

/-- **AN EQUIVARIANT `T` ANNIHILATES THE WITNESS, AT EVERY `n ≥ 3`.** Two rows, two equations,
two unknowns. Read the header before reading this as `KillsWeyl`: the family is one orbit, and
whether that orbit spans the Weyl summand is untouched. -/
theorem T_weyl_twoProj_eq_zero
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    (hn3 : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (b c : Fin n) :
    T (weylPart (knSquare (twoProj i j))) b c = 0 := by
  classical
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
  -- a third index
  have hne : ((Finset.univ.erase i).erase j).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem
      (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, hk⟩ := hne
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hk)).1
  -- the two values
  set a := T (weylPart (knSquare (twoProj i j))) i i with ha
  set v := T (weylPart (knSquare (twoProj i j))) k k with hv
  -- row at i
  have hrowi : ((n : ℝ) - 1) * a = 0 := by
    rw [← sum_row_i (fun j' => T (weylPart (knSquare (twoProj i j'))) i i) i a
      (T_weyl_twoProj_self hsmul i i i)
      (fun j' hj' => T_weyl_p_indep hequiv hij (Ne.symm hj'))]
    exact T_sum_weyl_twoProj_row hadd hsmul hn0 hn1 hn2 i i i
  have hazero : a = 0 := by
    rcases mul_eq_zero.mp hrowi with h | h
    · exact absurd h hn1
    · exact h
  -- row at k
  have hrowk : a + ((n : ℝ) - 2) * v = 0 := by
    rw [← sum_row_k (fun j' => T (weylPart (knSquare (twoProj i j'))) k k) i k hki a v
      (T_weyl_twoProj_self hsmul i k k)
      ((T_weyl_twoProj_pair hequiv i k).symm.trans (T_weyl_p_indep hequiv hij (Ne.symm hki)))
      (fun j' hj'i hj'k =>
        T_weyl_q_indep hequiv hij (Ne.symm hj'i) hki hkj hki (Ne.symm hj'k))]
    exact T_sum_weyl_twoProj_row hadd hsmul hn0 hn1 hn2 i k k
  have hvzero : v = 0 := by
    rw [hazero, zero_add] at hrowk
    rcases mul_eq_zero.mp hrowk with h | h
    · exact absurd h hn2
    · exact h
  rw [T_weyl_twoProj_shape hequiv hki hkj b c, ← ha, ← hv, hazero, hvzero]
  simp

end LovelockWitnessRowSum
