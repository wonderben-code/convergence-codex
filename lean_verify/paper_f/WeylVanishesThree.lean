import LovelockOrthogonality

/-!
# In dimension three the Weyl piece is identically zero, and half the remaining problem goes with it

`LovelockReduction` left the classification resting on **two** open statements, `KillsWeyl T` and
`RicciProportional T α`, and named the first as the harder — *"where the missing invariant theory
sits"*. **In dimension three the first one is free.**

`weylPart_eq_zero`: on `Fin 3`, the Weyl summand of every algebraic curvature tensor is identically
zero. So `killsWeyl_three` holds for **every** homogeneous `T` with no hypothesis about
equivariance or representation theory at all, and
`classification_three_of_ricciProportional` reaches the classification's conclusion from
`RicciProportional` **alone**.

**Three is the first dimension where the classification is open** —
`AlgebraicCurvature.lovelock_two` closes `n = 2` — so this halves the remaining problem exactly
where it starts.

## Why it is true, and why the proof is arithmetic rather than representation theory

On `Fin 3` an algebraic curvature tensor has **six** independent components, and its Ricci tensor —
symmetric on three indices — also has six. The Ricci map is therefore a bijection, and a tensor with
vanishing Ricci must vanish. `eq_zero_of_ricci_eq_zero` is that statement, proved by writing the six
Ricci equations out and solving them: three of them say `A + D = A + G = D + G = 0`, forcing
`A = D = G = 0`, and the other three say `B = C = E = 0` directly. Everything else is a sign or a
pair swap away from one of those six.

**The 36 off-diagonal reductions were generated mechanically, not typed.** Each says
`R i j k l = 0` for `i ≠ j` and `k ≠ l`, and each is a `linarith` over the two antisymmetries, the
pair symmetry and one of the six. A script enumerated the pairs, canonicalised each quadruple, and
emitted the exact fact list; **`ERRATUM 162`'s ordering applied to a different kind of value** — the
reductions were produced by a command rather than written and then checked.

## Checked outside Lean first

The vanishing was verified by exact rational arithmetic on **generic** algebraic curvature tensors —
random four-index arrays projected onto the symmetry class — at `n = 3` for three seeds, all giving
`max |Weyl| = 0`, and at `n = 4` for three seeds, all giving a **nonzero** maximum. The second half
matters as much as the first: it confirms this is a fact about dimension three and not an artefact
of the decomposition.

## What this is NOT

**It is not the classification, even at `n = 3`.** `RicciProportional` is untouched and remains
exactly as open as it was; what is gone is the other half. The theorem below is a *conditional* one
and its hypothesis is the surviving open statement.

**And it does not generalise.** The numerics say so at `n = 4` and the dimension count says why:
from four up, the curvature tensor has strictly more components than its Ricci tensor, and the
difference is the Weyl piece. Nothing here bears on `n ≥ 4`, which is the physically relevant
case, and the watchlist item stays open on exactly that.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace WeylVanishesThree

open AlgebraicCurvature LovelockProjections Finset

variable {R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ}

/-! ## 1. The two degenerate families -/

theorem eq_zero_of_left (hR : IsAlgCurv R) (a c d : Fin 3) : R a a c d = 0 := by
  have h := hR.antisymm_left a a c d; linarith

theorem eq_zero_of_right (hR : IsAlgCurv R) (a b c : Fin 3) : R a b c c = 0 := by
  have h := hR.antisymm_right a b c c; linarith

/-! ## 2. Six equations, six unknowns -/

/-- **A CURVATURE TENSOR ON `Fin 3` WITH VANISHING RICCI TRACE IS ZERO.** -/
theorem eq_zero_of_ricci_eq_zero (hR : IsAlgCurv R) (h0 : ∀ b c, ricci R b c = 0) :
    ∀ a b c d : Fin 3, R a b c d = 0 := by
  have hll := eq_zero_of_left hR
  have hrr := eq_zero_of_right hR
  -- the nine Ricci equations, expanded
  have r00 := h0 0 0; have r11 := h0 1 1; have r22 := h0 2 2
  have r01 := h0 0 1; have r02 := h0 0 2; have r12 := h0 1 2
  simp only [ricci, Fin.sum_univ_three] at r00 r11 r22 r01 r02 r12
  -- the six independent components
  have hA : R 0 1 0 1 = 0 := by
    linarith [hll 0 0 0, hll 1 1 1, hll 2 2 2, r00, r11, r22,
      hR.antisymm_left 1 0 0 1, hR.antisymm_left 2 0 0 2,
      hR.antisymm_left 0 1 1 0, hR.antisymm_right 0 1 0 1,
      hR.antisymm_left 2 1 1 2, hR.antisymm_right 1 2 1 2,
      hR.antisymm_left 0 2 2 0, hR.antisymm_right 0 2 0 2,
      hR.antisymm_left 1 2 2 1]
  have hD : R 0 2 0 2 = 0 := by
    linarith [hll 0 0 0, hll 1 1 1, hll 2 2 2, r00, r11, r22, hA,
      hR.antisymm_left 1 0 0 1, hR.antisymm_left 2 0 0 2,
      hR.antisymm_left 0 1 1 0, hR.antisymm_right 0 1 0 1,
      hR.antisymm_left 2 1 1 2, hR.antisymm_right 1 2 1 2,
      hR.antisymm_left 0 2 2 0, hR.antisymm_right 0 2 0 2,
      hR.antisymm_left 1 2 2 1]
  have hG : R 1 2 1 2 = 0 := by
    linarith [hll 0 0 0, hll 1 1 1, hll 2 2 2, r00, r11, r22, hA, hD,
      hR.antisymm_left 1 0 0 1, hR.antisymm_left 2 0 0 2,
      hR.antisymm_left 0 1 1 0, hR.antisymm_right 0 1 0 1,
      hR.antisymm_left 2 1 1 2, hR.antisymm_right 1 2 1 2,
      hR.antisymm_left 0 2 2 0, hR.antisymm_right 0 2 0 2,
      hR.antisymm_left 1 2 2 1]
  have hE : R 0 2 1 2 = 0 := by
    linarith [r01, hll 0 0 1, hrr 1 0 1,
      hR.antisymm_left 0 0 1 0, hR.antisymm_right 1 0 1 1,
      hR.antisymm_left 2 0 1 2]
  have hC : R 0 1 1 2 = 0 := by
    linarith [r02, hll 0 0 2, hrr 2 0 2,
      hR.antisymm_left 0 0 2 0, hR.antisymm_right 2 0 2 2,
      hR.antisymm_left 1 0 2 1, hR.antisymm_right 0 1 2 1]
  have hB : R 0 1 0 2 = 0 := by
    linarith [r12, hll 1 1 2, hrr 2 1 2,
      hR.antisymm_right 1 1 2 1, hR.antisymm_right 2 1 2 2,
      hR.antisymm_right 0 1 2 0]
  -- every off-diagonal component, generated rather than typed
  have h0101 : R 0 1 0 1 = 0 := by
    linarith [hA]
  have h0102 : R 0 1 0 2 = 0 := by
    linarith [hB]
  have h0110 : R 0 1 1 0 = 0 := by
    linarith [hR.antisymm_right 0 1 1 0, hA]
  have h0112 : R 0 1 1 2 = 0 := by
    linarith [hC]
  have h0120 : R 0 1 2 0 = 0 := by
    linarith [hR.antisymm_right 0 1 2 0, hB]
  have h0121 : R 0 1 2 1 = 0 := by
    linarith [hR.antisymm_right 0 1 2 1, hC]
  have h0201 : R 0 2 0 1 = 0 := by
    linarith [hR.pair_symm 0 2 0 1, hB]
  have h0202 : R 0 2 0 2 = 0 := by
    linarith [hD]
  have h0210 : R 0 2 1 0 = 0 := by
    linarith [hR.antisymm_right 0 2 1 0, hR.pair_symm 0 2 0 1, hB]
  have h0212 : R 0 2 1 2 = 0 := by
    linarith [hE]
  have h0220 : R 0 2 2 0 = 0 := by
    linarith [hR.antisymm_right 0 2 2 0, hD]
  have h0221 : R 0 2 2 1 = 0 := by
    linarith [hR.antisymm_right 0 2 2 1, hE]
  have h1001 : R 1 0 0 1 = 0 := by
    linarith [hR.antisymm_left 1 0 0 1, hA]
  have h1002 : R 1 0 0 2 = 0 := by
    linarith [hR.antisymm_left 1 0 0 2, hB]
  have h1010 : R 1 0 1 0 = 0 := by
    linarith [hR.antisymm_left 1 0 1 0, hR.antisymm_right 0 1 1 0, hA]
  have h1012 : R 1 0 1 2 = 0 := by
    linarith [hR.antisymm_left 1 0 1 2, hC]
  have h1020 : R 1 0 2 0 = 0 := by
    linarith [hR.antisymm_left 1 0 2 0, hR.antisymm_right 0 1 2 0, hB]
  have h1021 : R 1 0 2 1 = 0 := by
    linarith [hR.antisymm_left 1 0 2 1, hR.antisymm_right 0 1 2 1, hC]
  have h1201 : R 1 2 0 1 = 0 := by
    linarith [hR.pair_symm 1 2 0 1, hC]
  have h1202 : R 1 2 0 2 = 0 := by
    linarith [hR.pair_symm 1 2 0 2, hE]
  have h1210 : R 1 2 1 0 = 0 := by
    linarith [hR.antisymm_right 1 2 1 0, hR.pair_symm 1 2 0 1, hC]
  have h1212 : R 1 2 1 2 = 0 := by
    linarith [hG]
  have h1220 : R 1 2 2 0 = 0 := by
    linarith [hR.antisymm_right 1 2 2 0, hR.pair_symm 1 2 0 2, hE]
  have h1221 : R 1 2 2 1 = 0 := by
    linarith [hR.antisymm_right 1 2 2 1, hG]
  have h2001 : R 2 0 0 1 = 0 := by
    linarith [hR.antisymm_left 2 0 0 1, hR.pair_symm 0 2 0 1, hB]
  have h2002 : R 2 0 0 2 = 0 := by
    linarith [hR.antisymm_left 2 0 0 2, hD]
  have h2010 : R 2 0 1 0 = 0 := by
    linarith [hR.antisymm_left 2 0 1 0, hR.antisymm_right 0 2 1 0, hR.pair_symm 0 2 0 1, hB]
  have h2012 : R 2 0 1 2 = 0 := by
    linarith [hR.antisymm_left 2 0 1 2, hE]
  have h2020 : R 2 0 2 0 = 0 := by
    linarith [hR.antisymm_left 2 0 2 0, hR.antisymm_right 0 2 2 0, hD]
  have h2021 : R 2 0 2 1 = 0 := by
    linarith [hR.antisymm_left 2 0 2 1, hR.antisymm_right 0 2 2 1, hE]
  have h2101 : R 2 1 0 1 = 0 := by
    linarith [hR.antisymm_left 2 1 0 1, hR.pair_symm 1 2 0 1, hC]
  have h2102 : R 2 1 0 2 = 0 := by
    linarith [hR.antisymm_left 2 1 0 2, hR.pair_symm 1 2 0 2, hE]
  have h2110 : R 2 1 1 0 = 0 := by
    linarith [hR.antisymm_left 2 1 1 0, hR.antisymm_right 1 2 1 0, hR.pair_symm 1 2 0 1, hC]
  have h2112 : R 2 1 1 2 = 0 := by
    linarith [hR.antisymm_left 2 1 1 2, hG]
  have h2120 : R 2 1 2 0 = 0 := by
    linarith [hR.antisymm_left 2 1 2 0, hR.antisymm_right 1 2 2 0, hR.pair_symm 1 2 0 2, hE]
  have h2121 : R 2 1 2 1 = 0 := by
    linarith [hR.antisymm_left 2 1 2 1, hR.antisymm_right 1 2 2 1, hG]
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
      | exact hll _ _ _
      | exact hrr _ _ _
      | assumption

/-! ## 3. Hence the Weyl piece vanishes, and `KillsWeyl` is free -/

/-- **THE WEYL SUMMAND IS IDENTICALLY ZERO IN DIMENSION THREE.** -/
theorem weylPart_eq_zero (hR : IsAlgCurv R) (a b c d : Fin 3) : weylPart R a b c d = 0 := by
  refine eq_zero_of_ricci_eq_zero (isAlgCurv_weylPart hR) (fun x y => ?_) a b c d
  exact ricci_weylPart (by norm_num) (by norm_num) R x y

theorem weylPart_eq_zero_fun (hR : IsAlgCurv R) :
    weylPart R = fun _ _ _ _ => (0 : ℝ) := by
  funext a b c d; exact weylPart_eq_zero hR a b c d

/-- **SO THE FIRST OF `LovelockReduction`'s TWO OPEN STATEMENTS HOLDS AUTOMATICALLY AT `n = 3`**,
for every homogeneous `T` — no equivariance, no representation theory. -/
theorem killsWeyl_three {T : (Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ}
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c) :
    LovelockReduction.KillsWeyl T := by
  have hzero : T (fun _ _ _ _ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
    have h := hsmul 0 (fun _ _ _ _ => (0 : ℝ))
    simpa using h
  intro R hR b c
  rw [weylPart_eq_zero_fun hR, hzero]

/-! ## 4. The payoff: one open statement instead of two -/

/-- **AT `n = 3` THE CLASSIFICATION FOLLOWS FROM `RicciProportional` ALONE.** -/
theorem classification_three_of_ricciProportional
    {T : (Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ} (i : Fin 3)
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {α : ℝ} (hRic : LovelockReduction.RicciProportional T α)
    (hR : IsAlgCurv R) (b c : Fin 3) :
    T R b c
      = α * ricci R b c
        + (T (constCurv 3) i i / ((3 : ℝ) * ((3 : ℝ) - 1)) - α / (3 : ℝ))
            * scal R * delta b c := by
  have h := LovelockReduction.classification_of_killsWeyl_of_ricciProportional
    (n := 3) i hadd hsmul hequiv (killsWeyl_three hsmul) hRic hR b c
  simpa using h

end WeylVanishesThree
