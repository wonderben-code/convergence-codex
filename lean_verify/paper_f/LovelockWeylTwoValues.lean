import LovelockWeylWitness
import LovelockPermutations

/-!
# `T` on the Weyl witness: from `n²` numbers to two

`LovelockWeylWitness` retired a sentence nine headers had been repeating, by showing that an
equivariant `T` sends *some* non-zero Weyl tensor to a **diagonal** 2-tensor. It then said exactly
how far that was from the answer, and named what should cut it further:

> The witness is invariant under the permutations fixing `{i, j}` and changes sign under the
> transposition `(i j)`, so permutation equivariance — `LovelockPermutations` — should force
> `T W = diag(p, p, q, …, q)` with `p` at `i` and `j`: **two numbers.** … Neither is proved here,
> both are hand sketches, and by this project's vocabulary a hand sketch is a guess.

**The first of those two is now a theorem.** `T W` is diagonal, its value at `i` equals its value at
`j`, and its value is the same at every index outside `{i, j}`. **Two numbers, in every dimension.**

## What is proved

* **`act_knSquare`** — `act Q (knSquare h) = knSquare (act2 Q h)`, **for every `Q` and every `h`**.
  `LovelockReflectionFour.act_reflect_knSquare_diagonal` is its corollary at `Q = reflect m` with
  `h` diagonal; the general statement needs **neither orthogonality nor diagonality**, so this is
  `PROOF_STRATEGY` §7 item 3 — two restrictive hypotheses removed at once;
* `twoProj_perm` and **`act_permMat_twoProjCurv`** — a permutation that fixes `{i, j}` **setwise**
  leaves the witness alone. Both cases: fixing `i` and `j` individually, and swapping them;
* `reflect_twoProjCurv` and **`T_weyl_twoProj_diagonal`** — the witness is reflection-invariant, so
  `LovelockReflections.diagonal_of_reflection_invariant` sends it to a diagonal 2-tensor. This is
  `LovelockWeylWitness`'s theorem again, stated on the explicit witness rather than existentially,
  which is what the permutation argument needs;
* **`T_weyl_twoProj_perm`** — relabelling by any such permutation relabels `T W`, via
  `LovelockPermutations.T_act_permMat`;
* **`T_weyl_twoProj_off`** and **`T_weyl_twoProj_pair`** — the transposition of two indices outside
  `{i, j}` gives `T W x x = T W y y`; the transposition `(i j)` gives `T W i i = T W j j`;
* **`T_weyl_twoProj_shape`** — the four together, in one statement.

## The arithmetic, continued from where `LovelockWeylWitness` left it

`KillsWeyl` asks `T W = 0`. The count of free numbers has gone `n²` → `n` (diagonality) → **`2`**.
**Two is not zero, and the watchlist item does not move.**

**What is still a guess.** `LovelockWeylWitness` named a second step: the sum of
`knSquare (twoProj i j)` over `i < j` should be `constCurv`, whose Weyl part vanishes, giving one
linear relation between the two numbers and leaving one. **That is still a hand sketch and it is
still not proved here.**

**⚠ SUPERSEDED 2026-08-27, kept as written (`ERRATUM 94`, found by `ERRATUM 309`).** It stopped
being a sketch: `LovelockWitnessSum.sum_knSquare_twoProj` is `∑ᵢ∑ⱼ knSquare (twoProj i j) =
2·constCurv n` at every dimension, `weylPart_constCurv` kills the Weyl part, and
`sum_weylPart_twoProj` is the linear relation this paragraph predicted. That file quotes this
sentence and answers it in four words — *"and the sketch was right"*. **The count is unaffected**:
this file's `2` and the item's non-movement stand as written.

**And one number would still not be `KillsWeyl`.** The statement quantifies over every algebraic
curvature tensor; this is one witness, and the orbit of a single Weyl tensor is not known to span
the Weyl summand. That is `WALLS` §W5.0 §5b's irreducibility question, which nothing in this group
has approached.


**⚠ SUPERSEDED — `LovelockKillsWeyl.killsWeyl_of_equivariant` PROVES `KillsWeyl` AT EVERY `n ≥ 3`**
(`171d474`, 15 August), and the paragraph above is kept per `ERRATUM 94`. Every additive,
homogeneous, `O(n)`-equivariant `T` annihilates the Weyl summand; `classification` follows, and the
watchlist's Lovelock item is CLOSED — its sweep record reads *"the closure is `KillsWeyl` at every
`n ≥ 3`"*. **So *"the watchlist item does not move"* is true only in the sense that a closed item
cannot move, and it invites the opposite reading.** What is still open at W5 is not this: it is
rung 2 of `WALLS` §W5.1's staircase, an **affine connection and Levi-Civita** — zero names in
Mathlib. `ERRATUM 230`.

**What the two numbers are is also not computed.** `p` and `q` are `T W i i` and `T W k k`; no
theorem here evaluates either, and for all this file says they may be anything at all.

**^ THE CLAUSE ABOVE PUTTING THE AFFINE CONNECTION AT *ZERO NAMES IN MATHLIB* IS FALSE, AND IS
KEPT AS WRITTEN** (`ERRATUM 416`, 2026-09-02). Mathlib has **`CovariantDerivative`** — 73 names in
this estate's own `env_names.txt` — and `IsCovariantDerivativeOn` (24), with `torsion` beside them;
the probe behind the clause asked for the lower-case `covariantDerivative`, which is **0**
(`ERRATUM 411`). **EVERY OTHER CLAUSE STANDS, RE-PROBED TODAY RATHER THAN INHERITED**: `LeviCivita`
**0**, `HeatKernel` and `heatKernel` **0** each, and curvature **0** in four spellings
(`Curvature`, `curvature`, `riemannianCurvature`, `RiemannCurvature`). **So rung 2 is still the
wall's remaining step, this file still does not bear on it, and no verdict here changes** — what
moved is the rung W5 fails at, which `WALLS` §W5.1 records. **The clause reached eight files by
header inheritance, which is the mechanism `ERRATUM 230` already names**, and no absence mode caught
it because the sentence names no identifier to probe.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockWeylTwoValues

open AlgebraicCurvature LovelockProjections LovelockEquivariance LovelockReflections
  LovelockReflectionFour LovelockPermutations LovelockReduction WeylNonzeroGeneral Finset

variable {n : ℕ}
variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-! ## 1. The frame change through `knSquare`, with no hypotheses -/

/-- **THE FRAME CHANGE PASSES THROUGH `knSquare`**, for every `Q` and every `h`. -/
theorem act_knSquare (Q : Fin n → Fin n → ℝ) (h : Fin n → Fin n → ℝ) (a b c d : Fin n) :
    act Q (knSquare h) a b c d = knSquare (act2 Q h) a b c d := by
  have hfun : (fun x y z w => (2 : ℝ) * knSquare h x y z w) = kn h h := by
    funext x y z w
    show (2 : ℝ) * knSquare h x y z w = kn h h x y z w
    rw [kn_self]
  have key : act Q (fun x y z w => (2 : ℝ) * knSquare h x y z w) a b c d
      = 2 * knSquare (act2 Q h) a b c d := by
    rw [hfun, act_kn, kn_self]
  rw [act_smul] at key
  linarith

/-! ## 2. The witness's permutation symmetry -/

theorem twoProj_perm {i j : Fin n} (σ : Equiv.Perm (Fin n))
    (hσ : (σ i = i ∧ σ j = j) ∨ (σ i = j ∧ σ j = i)) (b c : Fin n) :
    twoProj i j (σ b) (σ c) = twoProj i j b c := by
  simp only [twoProj]
  rcases hσ with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have e1 : ∀ x : Fin n, delta (σ x) i = delta x i := by
      intro x
      by_cases h : x = i
      · subst h; simp [delta, hi]
      · have : σ x ≠ i := by rw [← hi]; exact fun e => h (σ.injective e)
        simp [delta, h, this]
    have e2 : ∀ x : Fin n, delta (σ x) j = delta x j := by
      intro x
      by_cases h : x = j
      · subst h; simp [delta, hj]
      · have : σ x ≠ j := by rw [← hj]; exact fun e => h (σ.injective e)
        simp [delta, h, this]
    rw [e1, e1, e2, e2]
  · have e1 : ∀ x : Fin n, delta (σ x) i = delta x j := by
      intro x
      by_cases h : x = j
      · subst h; simp [delta, hj]
      · have : σ x ≠ i := by rw [← hj]; exact fun e => h (σ.injective e)
        simp [delta, h, this]
    have e2 : ∀ x : Fin n, delta (σ x) j = delta x i := by
      intro x
      by_cases h : x = i
      · subst h; simp [delta, hi]
      · have : σ x ≠ j := by rw [← hi]; exact fun e => h (σ.injective e)
        simp [delta, h, this]
    rw [e1, e1, e2, e2]
    ring

theorem act_permMat_twoProjCurv {i j : Fin n} (σ : Equiv.Perm (Fin n))
    (hσ : (σ i = i ∧ σ j = j) ∨ (σ i = j ∧ σ j = i)) :
    act (permMat σ) (knSquare (twoProj i j)) = knSquare (twoProj i j) := by
  funext a b c d
  rw [act_knSquare]
  have hf : act2 (permMat σ) (twoProj i j) = twoProj i j := by
    funext b' c'
    rw [act2_permMat]
    exact twoProj_perm σ hσ b' c'
  rw [hf]

theorem reflect_twoProjCurv (i j : Fin n) (m : Fin n) :
    act (reflect m) (knSquare (twoProj i j)) = knSquare (twoProj i j) :=
  funext fun a => funext fun b => funext fun c => funext fun d =>
    act_reflect_knSquare_diagonal (fun _ _ hpq => diagonal_twoProj i j hpq) m a b c d

/-! ## 3. What `T` does to it -/

theorem T_weyl_twoProj_diagonal
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    (i j : Fin n) {b c : Fin n} (hbc : b ≠ c) :
    T (weylPart (knSquare (twoProj i j))) b c = 0 := by
  refine diagonal_of_reflection_invariant hequiv
    (isAlgCurv_weylPart (isAlgCurv_twoProjCurv i j)) ?_ hbc
  intro m
  funext a b' c' d'
  rw [act_weylPart (isOrth_reflect m), reflect_twoProjCurv i j m]

theorem T_weyl_twoProj_perm
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i j : Fin n} (σ : Equiv.Perm (Fin n))
    (hσ : (σ i = i ∧ σ j = j) ∨ (σ i = j ∧ σ j = i)) (b c : Fin n) :
    T (weylPart (knSquare (twoProj i j))) b c
      = T (weylPart (knSquare (twoProj i j))) (σ b) (σ c) := by
  have hW : act (permMat σ) (weylPart (knSquare (twoProj i j)))
      = weylPart (knSquare (twoProj i j)) := by
    funext a b' c' d'
    rw [act_weylPart (isOrth_permMat σ), act_permMat_twoProjCurv σ hσ]
  have hkey := T_act_permMat hequiv (isAlgCurv_weylPart (isAlgCurv_twoProjCurv i j)) σ b c
  rw [hW] at hkey
  exact hkey

theorem T_weyl_twoProj_off
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i j x y : Fin n} (hxi : x ≠ i) (hxj : x ≠ j) (hyi : y ≠ i) (hyj : y ≠ j) :
    T (weylPart (knSquare (twoProj i j))) x x
      = T (weylPart (knSquare (twoProj i j))) y y := by
  have hfix : (Equiv.swap x y) i = i ∧ (Equiv.swap x y) j = j :=
    ⟨Equiv.swap_apply_of_ne_of_ne (Ne.symm hxi) (Ne.symm hyi),
     Equiv.swap_apply_of_ne_of_ne (Ne.symm hxj) (Ne.symm hyj)⟩
  have h := T_weyl_twoProj_perm hequiv (Equiv.swap x y) (Or.inl hfix) x x
  rw [Equiv.swap_apply_left] at h
  exact h

theorem T_weyl_twoProj_pair
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    (i j : Fin n) :
    T (weylPart (knSquare (twoProj i j))) i i
      = T (weylPart (knSquare (twoProj i j))) j j := by
  have hswap : (Equiv.swap i j) i = j ∧ (Equiv.swap i j) j = i :=
    ⟨Equiv.swap_apply_left i j, Equiv.swap_apply_right i j⟩
  have h := T_weyl_twoProj_perm hequiv (Equiv.swap i j) (Or.inr hswap) i i
  rw [Equiv.swap_apply_left] at h
  exact h

theorem T_weyl_twoProj_shape
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) (b c : Fin n) :
    T (weylPart (knSquare (twoProj i j))) b c
      = if b = c then
          (if b = i ∨ b = j then T (weylPart (knSquare (twoProj i j))) i i
           else T (weylPart (knSquare (twoProj i j))) k k)
        else 0 := by
  by_cases hbc : b = c
  · subst hbc
    by_cases hbi : b = i
    · subst hbi; simp
    · by_cases hbj : b = j
      · rw [if_pos rfl, if_pos (Or.inr hbj)]
        rw [hbj]
        exact (T_weyl_twoProj_pair hequiv i j).symm
      · rw [if_pos rfl, if_neg (by tauto)]
        exact T_weyl_twoProj_off hequiv hbi hbj hki hkj
  · rw [if_neg hbc]
    exact T_weyl_twoProj_diagonal hequiv i j hbc

end LovelockWeylTwoValues
