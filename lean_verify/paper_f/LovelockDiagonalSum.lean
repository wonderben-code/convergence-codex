import LovelockDiagonalWitness

/-!
# Step 2, finished: from the two-index witnesses to every diagonal traceless tensor

`LovelockDiagonalWitness` proved step 2's conclusion **on the witnesses** `hIJ i j` and said
plainly what was left:

> Going from there to *every* traceless diagonal `h` is the expansion
> `h = ∑_{i ≠ j₀} h ᵢᵢ · hIJ i j₀`, which is an identity of functions that tracelessness makes
> true, followed by pushing `T` across a `Finset.sum` using the additivity hypothesis `hadd`. That
> is real work of a different kind — induction over a `Finset` with `T` applied to a sum of
> *functions* — and **it is not in this file.**

This is that file, and **the description held**: two inductions and one counting identity, no new
idea. The sentence was written as a claim about a file rather than as a difficulty judgement, and
that is why it did not have to be withdrawn.

## What is proved

**`T_ricciPart_eq_smul_of_diagonal`** — for `T` additive, homogeneous and equivariant, and any `R`
whose traceless Ricci tensor is **diagonal**,

    T (ricciPart R) b c  =  α · tracefreeRicci R b c ,     α = T (ricciSeed (hIJ i₀ j₀)) i₀ i₀

for any chosen pair `i₀ ≠ j₀` — and `LovelockDiagonalWitness.T_ricciSeed_hIJ_diag_eq` already says
the choice does not matter. **That is `LovelockReduction.RicciProportional`'s own equation, with
one hypothesis added: that the traceless Ricci tensor is diagonal.** Steps 1 and 2 of the
elementary route are complete.

The route:

* `T_zero` and `T_sum` — `T` of a finite sum of four-index arrays is the sum of the `T`s. Pure
  `Finset` induction on `hadd`, with the empty case supplied by `hsmul` at `lam = 0`;
* `ricciSeed_sum` and `ricciSeed_smul` — the seed is linear in its 2-tensor, so the expansion
  survives being fed to it;
* **`hIJ_expand`** — the counting identity. Off the diagonal both sides vanish; at `b ≠ j₀` the
  sum collapses to the single term `i = b`; and **at `j₀` every witness contributes `−1`, so the
  sum is `−∑_{i ≠ j₀} h ᵢᵢ`, which tracelessness turns into `h j₀ j₀`.** That last line is the
  only place tracelessness is spent, and it is what makes the `n − 1` witnesses `hIJ i j₀` enough
  to reach every diagonal traceless tensor. (No basis, span or dimension is claimed here or below
  — `hIJ_expand` is an identity of functions, proved entry by entry.)

## Two hypotheses that are not taken, both by `ERRATUM 166`'s question

`ERRATUM 166` recorded that every hypothesis audit in this campaign had asked *is it used?* and
never *is it implied by something already assumed?*. Asked here in advance rather than in review:

* **symmetry of `h` is not a hypothesis.** `isAlgCurv_ricciSeed` needs it, but a *diagonal* tensor
  is symmetric — both sides vanish off the diagonal — so `hdiag` already supplies it;
* **`IsAlgCurv R` is not a hypothesis** of `T_ricciPart_eq_smul_of_diagonal`, and that surprised
  me. `ricciPart R` depends on `R` only through `tracefreeRicci R`, and the one place `IsAlgCurv R`
  would be needed — knowing `tracefreeRicci R` is symmetric, via `ricci_symm` — is again supplied
  by `hdiag`. So the theorem holds for **any** four-index array whose traceless Ricci tensor is
  diagonal, algebraic curvature tensor or not. `RicciProportional` quantifies over algebraic
  curvature tensors, so this is strictly more than it asks for, and it costs nothing.

`(n:ℝ) ≠ 0` is likewise derived rather than assumed, from the argument `i₀ : Fin n` two tokens away
— the same derivation `LovelockReduction` made after `ERRATUM 166`.

## What is still not here, and it is TWO things, not one

A draft of this header said *"the whole of what stands between this file and `RicciProportional`
is step 3"*. **That is wrong, and it is the scope claim `ERRATA 163–165` are about**, so it is
corrected here rather than after the fact. Removing `hdiag` takes two things:

1. **Step 3, which is still the refusal.** A general symmetric traceless 2-tensor is diagonal only
   in a frame adapted to it, and producing that frame is the spectral theorem carried across to
   `AlgebraicCurvature.IsOrth`. The bridge `isOrth_of_mem_orthogonalGroup` exists; the
   diagonalisation does not.
2. **And undoing the frame change afterwards.** Diagonalising gives the conclusion for `act Q R`;
   getting it back to `R` needs `act2 Q` to be injective for orthogonal `Q` — and
   `AlgebraicCurvature` §"How a four-index array transforms under `Q`" says outright that the
   composition law is **not proved**: *"that `act (Q · Qʹ) = act Q ∘ act Qʹ` … is not established
   here and is not used below"*. Nothing in `paper_f` inverts `act2`.

The second **looks** like a short computation from `IsOrth` — contract with `Qᵀ` and collapse two
row inner products. **That is a sizing judgement, and this line of files exists because one of
mine was wrong**, so it is recorded as a guess for a later unit to test, not as a promise.

**And nothing here bears on `KillsWeyl`**, the harder of `LovelockReduction`'s two `Prop`s and the
one where the missing invariant theory lives. The watchlist item does not move.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockDiagonalSum

open AlgebraicCurvature LovelockProjections LovelockEquivariance LovelockReflections
  LovelockPermutations LovelockDiagonalWitness Finset

variable {n : ℕ}
variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-! ## 1. `T` across a finite sum

`hadd` is stated for two summands. Getting to a `Finset.sum` is an induction, and its base case is
`T 0 = 0`, which is **not** a separate assumption: `hsmul` at `lam = 0` gives it.
-/

/-- **`T` KILLS THE ZERO ARRAY**, from homogeneity alone. -/
theorem T_zero
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (b c : Fin n) : T (fun _ _ _ _ => (0 : ℝ)) b c = 0 := by
  have hfun : (fun a b c d => (0 : ℝ) * (fun (_ _ _ _ : Fin n) => (0 : ℝ)) a b c d)
      = fun (_ _ _ _ : Fin n) => (0 : ℝ) := by
    funext a b c d; ring
  have h := hsmul 0 (fun (_ _ _ _ : Fin n) => (0 : ℝ))
  rw [hfun] at h
  simpa using congrFun (congrFun h b) c

/-- **AND IT PASSES THROUGH A FINITE SUM.** -/
theorem T_sum
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (s : Finset (Fin n)) (F : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) :
    T (fun a b' c' d' => ∑ i ∈ s, F i a b' c' d') b c = ∑ i ∈ s, T (F i) b c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using T_zero hsmul b c
  | @insert x s hx ih =>
      have hfun : (fun a b' c' d' => ∑ i ∈ insert x s, F i a b' c' d')
          = fun a b' c' d' => F x a b' c' d' + ∑ i ∈ s, F i a b' c' d' := by
        funext a b' c' d'; rw [Finset.sum_insert hx]
      have hstep : T (fun a b' c' d' => ∑ i ∈ insert x s, F i a b' c' d') b c
          = T (F x) b c + T (fun a b' c' d' => ∑ i ∈ s, F i a b' c' d') b c := by
        rw [hfun, hadd (F x) (fun a b' c' d' => ∑ i ∈ s, F i a b' c' d')]
      rw [hstep, ih, Finset.sum_insert hx]

/-! ## 2. The seed is linear in its 2-tensor -/

theorem ricciSeed_smul (lam : ℝ) (g : Fin n → Fin n → ℝ) (a b c d : Fin n) :
    ricciSeed (fun x y => lam * g x y) a b c d = lam * ricciSeed g a b c d := by
  simp only [ricciSeed, kn]; ring

theorem ricciSeed_sum (s : Finset (Fin n)) (g : Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    ricciSeed (fun x y => ∑ i ∈ s, g i x y) a b c d = ∑ i ∈ s, ricciSeed (g i) a b c d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ricciSeed, kn]
  | @insert x s hx ih =>
      have hfun : (fun p q => ∑ i ∈ insert x s, g i p q)
          = fun p q => g x p q + ∑ i ∈ s, g i p q := by
        funext p q; rw [Finset.sum_insert hx]
      rw [hfun, Finset.sum_insert hx, ← ih]
      simp only [ricciSeed, kn]
      ring

/-! ## 3. The counting identity

The `n − 1` witnesses `hIJ i j₀` reach every diagonal traceless tensor, and the one place that
costs anything is the entry at `j₀`, where every witness contributes `−1` and tracelessness turns
the total into the right number.
-/

/-- Away from `j₀` the witness is the indicator of `i`. -/
theorem hIJ_diag_of_ne {i j b : Fin n} (hbj : b ≠ j) :
    hIJ i j b b = if b = i then 1 else 0 := by
  by_cases hbi : b = i
  · rw [hbi, hIJ_at_i, if_pos rfl]
  · rw [hIJ_at_other hbi hbj, if_neg hbi]

/-- **THE EXPANSION.** A diagonal traceless `h` is the combination of the `n − 1` witnesses
`hIJ i j₀`, `i ≠ j₀`, with its own diagonal entries as coefficients. -/
theorem hIJ_expand {h : Fin n → Fin n → ℝ}
    (hdiag : ∀ x y, x ≠ y → h x y = 0) (htr : ∑ a, h a a = 0) (j₀ : Fin n) (x y : Fin n) :
    h x y = ∑ i ∈ Finset.univ.erase j₀, h i i * hIJ i j₀ x y := by
  classical
  rcases eq_or_ne x y with rfl | hxy
  · by_cases hx : x = j₀
    · -- at `j₀`: every witness contributes `−1`, and tracelessness supplies the total
      have hval : ∀ i ∈ Finset.univ.erase j₀, h i i * hIJ i j₀ x x = -(h i i) := by
        intro i hi
        rw [hx, hIJ_at_j (Finset.ne_of_mem_erase hi)]
        ring
      rw [Finset.sum_congr rfl hval, Finset.sum_neg_distrib]
      have hsplit : h j₀ j₀ + ∑ i ∈ Finset.univ.erase j₀, h i i = ∑ i, h i i :=
        Finset.add_sum_erase Finset.univ (fun i => h i i) (Finset.mem_univ j₀)
      rw [htr] at hsplit
      rw [hx]
      linarith
    · -- away from `j₀`: the sum collapses onto `i = x`
      have hval : ∀ i ∈ Finset.univ.erase j₀,
          h i i * hIJ i j₀ x x = if i = x then h i i else 0 := by
        intro i _
        rw [hIJ_diag_of_ne hx]
        by_cases hix : i = x
        · rw [if_pos hix, if_pos (by rw [hix]), mul_one]
        · rw [if_neg hix, if_neg (fun hc => hix hc.symm), mul_zero]
      rw [Finset.sum_congr rfl hval,
        Finset.sum_ite_eq' (Finset.univ.erase j₀) x (fun i => h i i),
        if_pos (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩)]
  · rw [hdiag x y hxy]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    rw [hIJ_offDiag i j₀ hxy, mul_zero]

/-! ## 4. Step 2, assembled -/

/-- **STEP 2 ON EVERY DIAGONAL TRACELESS TENSOR.** Symmetry of `h` is not assumed: a diagonal
tensor is symmetric. -/
theorem T_ricciSeed_eq_smul_of_diagonal (hn2 : (n : ℝ) - 2 ≠ 0)
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i₀ j₀ : Fin n} (hij₀ : i₀ ≠ j₀)
    {h : Fin n → Fin n → ℝ} (hdiag : ∀ x y, x ≠ y → h x y = 0) (htr : ∑ a, h a a = 0)
    (b c : Fin n) :
    T (ricciSeed h) b c = T (ricciSeed (hIJ i₀ j₀)) i₀ i₀ * h b c := by
  classical
  set α := T (ricciSeed (hIJ i₀ j₀)) i₀ i₀ with hα
  have hfun : h = fun x y => ∑ i ∈ Finset.univ.erase j₀, h i i * hIJ i j₀ x y :=
    funext fun x => funext fun y => hIJ_expand hdiag htr j₀ x y
  -- the seed of `h` is the same combination of the seeds of the witnesses
  have hseed : ricciSeed h
      = fun a b' c' d' => ∑ i ∈ Finset.univ.erase j₀,
          ricciSeed (fun x y => h i i * hIJ i j₀ x y) a b' c' d' := by
    funext a b' c' d'
    conv_lhs => rw [hfun]
    exact ricciSeed_sum _ (fun i x y => h i i * hIJ i j₀ x y) a b' c' d'
  have hT : T (ricciSeed h) b c
      = ∑ i ∈ Finset.univ.erase j₀, T (ricciSeed (fun x y => h i i * hIJ i j₀ x y)) b c := by
    rw [hseed]
    exact T_sum hadd hsmul _ (fun i => ricciSeed (fun x y => h i i * hIJ i j₀ x y)) b c
  -- each summand is a scalar times `T` on a witness, and each of those is `α` times the witness
  have hterm : ∀ i ∈ Finset.univ.erase j₀,
      T (ricciSeed (fun x y => h i i * hIJ i j₀ x y)) b c = α * (h i i * hIJ i j₀ b c) := by
    intro i hi
    have hij : i ≠ j₀ := Finset.ne_of_mem_erase hi
    have hsc : ricciSeed (fun x y => h i i * hIJ i j₀ x y)
        = fun a b' c' d' => h i i * ricciSeed (hIJ i j₀) a b' c' d' :=
      funext fun a => funext fun b' => funext fun c' => funext fun d' =>
        ricciSeed_smul (h i i) (hIJ i j₀) a b' c' d'
    have hstep : T (ricciSeed (fun x y => h i i * hIJ i j₀ x y)) b c
        = h i i * T (ricciSeed (hIJ i j₀)) b c := by
      rw [hsc, hsmul]
    rw [hstep, T_ricciSeed_hIJ_eq_smul hn2 hsmul hequiv hij b c,
      T_ricciSeed_hIJ_diag_eq hsmul hequiv hij₀ hij, ← hα]
    ring
  rw [hT, Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← hIJ_expand hdiag htr j₀ b c]

/-! ## 5. The same statement in `RicciProportional`'s shape

`ricciPart R` is by definition `(n−2)⁻¹ · (tracefreeRicci R ⊙ δ)`, which is `ricciSeed
(tracefreeRicci R)` — the two are the same term. So §4 transfers with no work, and what comes out
is `LovelockReduction.RicciProportional`'s own equation with `hdiag` added.
-/

/-- **STEPS 1 AND 2, COMPLETE.** `RicciProportional`'s equation for every `R` whose traceless Ricci
tensor is diagonal. **`IsAlgCurv R` is not a hypothesis** — `ricciPart R` sees `R` only through
`tracefreeRicci R`, and the symmetry that `IsAlgCurv` would have supplied comes from `hdiag`
instead. `(n:ℝ) ≠ 0` is derived from `i₀ : Fin n`. -/
theorem T_ricciPart_eq_smul_of_diagonal (hn2 : (n : ℝ) - 2 ≠ 0)
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i₀ j₀ : Fin n} (hij₀ : i₀ ≠ j₀)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hdiag : ∀ b c, b ≠ c → tracefreeRicci R b c = 0) (b c : Fin n) :
    T (ricciPart R) b c
      = T (ricciSeed (hIJ i₀ j₀)) i₀ i₀ * tracefreeRicci R b c := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr i₀.pos.ne'
  have hfun : ricciPart R = ricciSeed (tracefreeRicci R) := rfl
  rw [hfun]
  exact T_ricciSeed_eq_smul_of_diagonal hn2 hadd hsmul hequiv hij₀ hdiag
    (trace_tracefreeRicci hn0 R) b c

end LovelockDiagonalSum
