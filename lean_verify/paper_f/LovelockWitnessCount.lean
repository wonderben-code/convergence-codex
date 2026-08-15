import LovelockWitnessTransport

/-!
# The count, and the two numbers become one

`LovelockWitnessTransport` ended with the last step named and declined:

> Every term of the vanishing double sum is now one of two numbers … **Counting the terms would
> give `2(n−1)·p + (n−1)(n−2)·q = 0`** … **That count is not done here.** It is a `Finset`
> cardinality computation and nothing more, but it is not a theorem until it is written, and this
> file does not claim it.

**It is written here, and the arithmetic is what was predicted.**

## What is proved

* **`sum_two_values`** — a self-contained combinatorial lemma with no curvature in it: if `f` on
  `Fin n × Fin n` vanishes on the diagonal, equals `p` whenever exactly one argument is a fixed `i`,
  and equals `q` off both, then `∑ₐ∑_b f a b = 2(n−1)p + (n−1)(n−2)q`. Two `Finset.erase`
  computations;
* `knSquare_twoProj_self` — `knSquare (twoProj a a)` is **identically zero**, one `ring` after
  unfolding, which is why the diagonal terms of the double sum contribute nothing;
* `weylPart_zero` and `T_weyl_twoProj_self` — and so `T` of them is zero;
* **`two_value_relation`** — for every additive, homogeneous, equivariant `T`:
  **`2(n−1)·T W i i + (n−1)(n−2)·T W k k = 0`**, where `W` is the witness for the pair `(i,j)` and
  `k` is any index outside it.

## The count, and exactly what it does not settle

`KillsWeyl` asks `T W = 0`. The free-number count over the last four units has run
**`n²` → `n` → `2` → `1`**: diagonality, then two values, then this one relation. **One is not
zero.** The relation is one equation in two unknowns; it leaves a one-parameter family, and nothing
in this estate excludes it. **The watchlist item does not move.**

**And the deeper reason it cannot**, restated once more because four files have now said it: this
is **one witness family**. `KillsWeyl` quantifies over every algebraic curvature tensor. Whether the
`O(n)`-orbit of a single Weyl tensor spans the Weyl summand is `WALLS` §W5.0 §5b's irreducibility
question, and **nothing in this group has approached it.** Cutting the witness family's freedom to
one number is a sharper statement about `T` than the estate had, and it is not a step toward the
theorem.

**What would be a step, and is not attempted here:** a second, independent family of Weyl tensors
whose relations cut the remaining parameter — or the irreducibility itself.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockWitnessCount

open AlgebraicCurvature LovelockProjections LovelockEquivariance WeylNonzeroGeneral
  LovelockWeylTwoValues LovelockWitnessSum LovelockWitnessTransport LovelockDiagonalSum Finset

variable {n : ℕ}
variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-! ## 1. The combinatorial lemma, with no curvature in it -/

theorem sum_two_values {p q : ℝ} {i : Fin n} (f : Fin n → Fin n → ℝ)
    (hdiag : ∀ a, f a a = 0)
    (hp : ∀ a b, a ≠ b → (a = i ∨ b = i) → f a b = p)
    (hq : ∀ a b, a ≠ b → a ≠ i → b ≠ i → f a b = q) :
    ∑ a, ∑ b, f a b = 2 * ((n : ℝ) - 1) * p + ((n : ℝ) - 1) * ((n : ℝ) - 2) * q := by
  classical
  have hpos : 0 < n := Fin.pos i
  have hcast1 : ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have : (1 : ℕ) ≤ n := hpos
    push_cast [Nat.cast_sub this]
    ring
  have hi : ∑ b, f i b = ((n : ℝ) - 1) * p := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hdiag i, zero_add,
      Finset.sum_congr rfl fun b hb =>
        hp i b (fun e => (Finset.mem_erase.mp hb).1 e.symm) (Or.inl rfl),
      Finset.sum_const, nsmul_eq_mul, hcast1]
  have hother : ∀ a : Fin n, a ≠ i → ∑ b, f a b = p + ((n : ℝ) - 2) * q := by
    intro a hai
    have hia : i ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨fun e => hai e.symm, mem_univ i⟩
    have hcard2 : (((Finset.univ.erase a).erase i).card : ℝ) = (n : ℝ) - 2 := by
      rw [Finset.card_erase_of_mem hia, Finset.card_erase_of_mem (Finset.mem_univ a),
        Finset.card_univ, Fintype.card_fin]
      have h2 : 2 ≤ n := by
        have hlt : 1 < Fintype.card (Fin n) := Fintype.one_lt_card_iff.mpr ⟨a, i, hai⟩
        simpa using hlt
      have hsub : n - 1 - 1 = n - 2 := by omega
      rw [hsub]
      push_cast [Nat.cast_sub h2]
      ring
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), hdiag a, zero_add,
      ← Finset.add_sum_erase _ _ hia, hp a i (fun e => hai e) (Or.inr rfl)]
    congr 1
    rw [Finset.sum_congr rfl fun b hb => hq a b
      (fun e => (Finset.mem_erase.mp (Finset.mem_of_mem_erase hb)).1 e.symm)
      hai (Finset.mem_erase.mp hb).1, Finset.sum_const, nsmul_eq_mul, hcard2]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hi,
    Finset.sum_congr rfl fun a ha => hother a (Finset.mem_erase.mp ha).1,
    Finset.sum_const, nsmul_eq_mul, hcast1]
  ring

/-! ## 2. The diagonal terms vanish -/

theorem knSquare_twoProj_self (a x y z w : Fin n) :
    knSquare (twoProj a a) x y z w = 0 := by
  simp only [knSquare, twoProj]; ring

theorem weylPart_zero (a b c d : Fin n) :
    weylPart (fun _ _ _ _ => (0 : ℝ)) a b c d = 0 := by
  have hfun : (fun (_ _ _ _ : Fin n) => (0 : ℝ))
      = fun x y z w => ∑ i : Empty,
          (fun (_ : Empty) => (fun (_ _ _ _ : Fin n) => (0 : ℝ))) i x y z w := by
    funext x y z w; simp
  rw [hfun, weylPart_sum]
  simp

theorem T_weyl_twoProj_self
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (a b c : Fin n) : T (weylPart (knSquare (twoProj a a))) b c = 0 := by
  have hfun : weylPart (knSquare (twoProj a a)) = fun _ _ _ _ => (0 : ℝ) := by
    funext x y z w
    have h0 : (knSquare (twoProj a a) : Fin n → Fin n → Fin n → Fin n → ℝ)
        = fun _ _ _ _ => (0 : ℝ) :=
      funext fun x' => funext fun y' => funext fun z' => funext fun w' =>
        knSquare_twoProj_self a x' y' z' w'
    rw [h0, weylPart_zero]
  rw [hfun, T_zero hsmul]

/-! ## 3. The relation -/

theorem two_value_relation
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0)
    {i j k : Fin n} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    2 * ((n : ℝ) - 1) * T (weylPart (knSquare (twoProj i j))) i i
      + ((n : ℝ) - 1) * ((n : ℝ) - 2) * T (weylPart (knSquare (twoProj i j))) k k = 0 := by
  have hsum := T_sum_weyl_twoProj hadd hsmul hn0 hn1 i i
  rw [sum_two_values (i := i) (fun a b => T (weylPart (knSquare (twoProj a b))) i i)
    (fun a => T_weyl_twoProj_self hsmul a i i)
    (fun a b hab hor => by
      rcases hor with rfl | rfl
      · exact T_weyl_p_indep hequiv hij hab
      · exact (T_weyl_twoProj_pair hequiv a b).symm.trans (T_weyl_p_indep hequiv hij hab))
    (fun a b hab hai hbi =>
      T_weyl_q_indep hequiv hij hab hki hkj (Ne.symm hai) (Ne.symm hbi))] at hsum
  exact hsum

end LovelockWitnessCount
