import LovelockKillsWeyl

/-!
# The classification's coefficients are functions of `T` alone

`LovelockKillsWeyl.classification` states `T R = α·ricci R + β·scal R·δ` with

> `α = T (ricciSeed (hIJ i₀ j₀)) i₀ i₀`  and  `β` built from `T (constCurv n) i i`

for **an arbitrary** distinct pair `i₀ ≠ j₀` and **an arbitrary** index `i`. A reader is entitled
to ask whether the right-hand side therefore depends on choices the left-hand side does not.
**It does not, and this file proves it** — so the classification is a statement about `T`, not
about `T` together with three auxiliary indices.

## What is proved

* **`ricciProportional_unique`** — `RicciProportional T α` pins `α`. Evaluate it at
  `ricciSeed (hIJ i₀ j₀)`, whose trace-free Ricci tensor is `hIJ i₀ j₀`
  (`tracefreeRicci_ricciSeed`) and whose value at `(i₀, i₀)` is `1` (`hIJ_at_i`), so `α·1` is
  determined;
* **`alpha_indep`** — hence the `ricci` coefficient is the same for every admissible pair, since
  `LovelockDiagonalise.ricciProportional` supplies a witness for each;
* **`beta_indep`** — and the `scal` coefficient is the same for every index, by
  `AlgebraicCurvature.equivariant_constCurv`, which was already there and needs only equivariance;
* **`classification_coeff_indep`** — the two right-hand sides agree.

## Two hypotheses written down and then not taken

The last theorem was drafted with `3 ≤ n` and with `IsAlgCurv R`. **It needs neither.** `3 ≤ n` was
only ever used to produce `(n : ℝ) − 2 ≠ 0`, which is now the hypothesis; and `R` enters the
statement purely as an argument of `ricci` and `scal`, so the identity between the two right-hand
sides is an identity of expressions and holds for **every** four-index array. The unused-variable
linter is what said so.

**Nothing here changes what `classification` proves.** It removes an ambiguity in how the statement
reads, which is the sort of thing worth a file when the statement is the estate's headline result.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockCoefficients

open AlgebraicCurvature LovelockProjections LovelockReduction LovelockDiagonalWitness
  LovelockDiagonalise LovelockKillsWeyl Finset

variable {n : ℕ} {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-- **`RicciProportional` PINS ITS COEFFICIENT.** Evaluate at `ricciSeed (hIJ i₀ j₀)`, where the
trace-free Ricci tensor is `hIJ i₀ j₀` and its `(i₀, i₀)` entry is `1`. -/
theorem ricciProportional_unique (hn2 : (n : ℝ) - 2 ≠ 0) {α₀ α₁ : ℝ}
    (h0 : RicciProportional T α₀) (h1 : RicciProportional T α₁)
    {i₀ j₀ : Fin n} (hij₀ : i₀ ≠ j₀) : α₀ = α₁ := by
  have hsym : ∀ a b : Fin n, hIJ i₀ j₀ a b = hIJ i₀ j₀ b a := hIJ_symm i₀ j₀
  have htr : ∑ a, hIJ i₀ j₀ a a = 0 := hIJ_trace hij₀
  have hcurv : IsAlgCurv (ricciSeed (hIJ i₀ j₀)) := isAlgCurv_ricciSeed hsym
  have hpart : ricciPart (ricciSeed (hIJ i₀ j₀)) = ricciSeed (hIJ i₀ j₀) :=
    ricciPart_ricciSeed hn2 htr
  have htf : tracefreeRicci (ricciSeed (hIJ i₀ j₀)) = hIJ i₀ j₀ :=
    tracefreeRicci_ricciSeed hn2 htr
  have e0 := h0 _ hcurv i₀ i₀
  have e1 := h1 _ hcurv i₀ i₀
  rw [hpart, htf, hIJ_at_i] at e0 e1
  rw [e1] at e0
  linarith

/-- **THE `ricci` COEFFICIENT DOES NOT DEPEND ON THE AUXILIARY PAIR.** -/
theorem alpha_indep (hn2 : (n : ℝ) - 2 ≠ 0)
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i₀ j₀ i₁ j₁ : Fin n} (h0 : i₀ ≠ j₀) (h1 : i₁ ≠ j₁) :
    T (ricciSeed (hIJ i₀ j₀)) i₀ i₀ = T (ricciSeed (hIJ i₁ j₁)) i₁ i₁ :=
  ricciProportional_unique hn2 (ricciProportional hn2 hadd hsmul hequiv h0)
    (ricciProportional hn2 hadd hsmul hequiv h1) h0

/-- **AND THE `scal` COEFFICIENT DOES NOT DEPEND ON THE AUXILIARY INDEX.** -/
theorem beta_indep
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    (i j : Fin n) : T (constCurv n) i i = T (constCurv n) j j := by
  have h := equivariant_constCurv i hequiv j j
  rw [delta_self, mul_one] at h
  exact h.symm

/-- **SO THE CLASSIFICATION'S TWO COEFFICIENTS ARE FUNCTIONS OF `T` ALONE.** -/
theorem classification_coeff_indep (hn2 : (n : ℝ) - 2 ≠ 0)
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    (i i' : Fin n) {i₀ j₀ i₁ j₁ : Fin n} (h0 : i₀ ≠ j₀) (h1 : i₁ ≠ j₁)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) :
    T (ricciSeed (hIJ i₀ j₀)) i₀ i₀ * ricci R b c
        + (T (constCurv n) i i / ((n : ℝ) * ((n : ℝ) - 1))
            - T (ricciSeed (hIJ i₀ j₀)) i₀ i₀ / (n : ℝ)) * scal R * delta b c
      = T (ricciSeed (hIJ i₁ j₁)) i₁ i₁ * ricci R b c
        + (T (constCurv n) i' i' / ((n : ℝ) * ((n : ℝ) - 1))
            - T (ricciSeed (hIJ i₁ j₁)) i₁ i₁ / (n : ℝ)) * scal R * delta b c := by
  rw [alpha_indep hn2 hadd hsmul hequiv h0 h1, beta_indep hequiv i i']

end LovelockCoefficients
