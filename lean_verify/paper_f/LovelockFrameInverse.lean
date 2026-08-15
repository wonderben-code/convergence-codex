import LovelockDiagonalSum
import LovelockReduction

/-!
# Undoing a frame change, and `RicciProportional` reduced to diagonalisation alone

`LovelockDiagonalSum` finished steps 1 and 2 and then named **two** things standing between the
estate and `LovelockReduction.RicciProportional`, of which the second was recorded as a guess:

> **And undoing the frame change afterwards** — `act2 Q` injective for orthogonal `Q` … The second
> **looks** like a short computation from `IsOrth` — contract with `Qᵀ` and collapse two row inner
> products. **That is a sizing judgement, and this line of files exists because one of mine was
> wrong**, so it is recorded as a guess for a later unit to test, not as a promise.

**This file is that test, and the guess was right.** One contraction lemma, used twice.

## What is proved

* `act2_transp_act2` — for orthogonal `Q`, `act2 Qᵀ ∘ act2 Q` is the identity on 2-tensors, so
  **`eq_of_act2_eq`**: a frame change can be undone.
* **`ricciProportional_of_diagonalisable`** — if every symmetric 2-tensor can be brought to
  diagonal form by *some* orthogonal frame change, then `RicciProportional T α` holds outright,
  with `α = T (ricciSeed (hIJ i₀ j₀)) i₀ i₀` for any pair `i₀ ≠ j₀`.

So **the second of `LovelockReduction`'s two open `Prop`s now rests on the named hypothesis
`Diagonalisable n`** — the real-symmetric spectral theorem written in this estate's own
`IsOrth`/`act2` vocabulary — **together with the two dimension conditions the route has carried
throughout**: `(n:ℝ) − 2 ≠ 0`, which `ricciPart` needs to exist, and a pair of distinct indices
`i₀ ≠ j₀`, which is `n ≥ 2`. The three hypotheses on `T` itself (`hadd`, `hsmul`, `hequiv`) are the
ones `LovelockReduction`'s own theorem already assumes. That is the same service
`LovelockReduction` performed for the classification: replace a sentence about what is missing
with a `Prop` a later unit can attempt.

**`Diagonalisable` is stated for every symmetric 2-tensor, and only the traceless ones are used.**
A proof of it may therefore restrict to traceless `S` if that helps; the general form is kept
because the spectral theorem supplies it anyway and the restriction would only add a hypothesis to
carry.

## What this is NOT

**It is not the composition law**, and the distinction matters because `AlgebraicCurvature` states
outright that the composition law is unproved:

> that `act (Q · Qʹ) = act Q ∘ act Qʹ`, which is the other half of being a group action and what a
> `MulAction` instance would assert, is **not established here and is not used below**.

That is still true. What is proved here is **one consequence** of it — the single instance
`Qᵀ · Q = 1`, on 2-tensors only, by direct computation. Nothing here gives `act` a `MulAction`, and
nothing here touches four-index arrays.

**And it does not prove `Diagonalisable n`.** That is step 3 and it is still the refusal. What has
changed is only that the refusal is now a `Prop` with a name rather than a paragraph.

## Why `transp` is defined here rather than reused

`ERRATUM 168` added the review question *does this already exist in something the file imports?*.
Asked and answered: **Mathlib has `Matrix.transpose`, and it is not usable here.** This estate's
frame changes are plain functions `Fin n → Fin n → ℝ`, and Mathlib's `Matrix` is a non-reducible
`def` for exactly that function type — deliberately, so that the two do not silently unify. Using
`Matrix.transpose` would mean routing every frame change through `Matrix.of`, for a definition that
is one line. `AlgebraicCurvature` made the same choice for `IsOrth` and bridged it once, in
`isOrth_of_mem_orthogonalGroup`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockFrameInverse

open AlgebraicCurvature LovelockProjections LovelockEquivariance LovelockDiagonalWitness
  LovelockDiagonalSum LovelockReduction Finset

variable {n : ℕ}
variable {Q : Fin n → Fin n → ℝ}

/-! ## 1. The one contraction, and it is used twice -/

/-- The transposed frame change. See the header for why this is not `Matrix.transpose`. -/
def transp (Q : Fin n → Fin n → ℝ) (a b : Fin n) : ℝ := Q b a

/-- Transposing swaps the two halves of `IsOrth` and nothing else. **Not used below** —
`act2_transp_act2` works straight from `IsOrth.cols`. It is stated because "the frame change can be
undone" would be a weaker sentence if the undoing were not itself a frame change, and this is what
says it is. Labelled so it is not read as load-bearing. -/
theorem isOrth_transp (hQ : IsOrth Q) : IsOrth (transp Q) where
  rows := hQ.cols
  cols := hQ.rows

/-- **THE CONTRACTION.** A column inner product of `Q` against a `Q`-weighted sum collapses to
evaluation, by `IsOrth.cols` and nothing else. -/
theorem sum_col_contract (hQ : IsOrth Q) (b : Fin n) (f : Fin n → ℝ) :
    ∑ p, Q p b * (∑ x, Q p x * f x) = f b := by
  have h1 : ∀ p : Fin n, Q p b * (∑ x, Q p x * f x) = ∑ x, Q p b * Q p x * f x := by
    intro p
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [Finset.sum_congr rfl fun p _ => h1 p, Finset.sum_comm]
  have h2 : ∀ x : Fin n, ∑ p, Q p b * Q p x * f x = delta x b * f x := by
    intro x
    rw [← Finset.sum_mul, hQ.cols b x, delta_symm b x]
  rw [Finset.sum_congr rfl fun x _ => h2 x]
  exact sum_delta_left b f

/-! ## 2. The frame change is invertible on 2-tensors -/

/-- **UNDOING A FRAME CHANGE.** Not the composition law — one instance of it, on 2-tensors. -/
theorem act2_transp_act2 (hQ : IsOrth Q) (S : Fin n → Fin n → ℝ) (b c : Fin n) :
    act2 (transp Q) (act2 Q S) b c = S b c := by
  have hinner : ∀ p : Fin n, ∑ q, Q q c * act2 Q S p q = ∑ x, Q p x * S x c := by
    intro p
    have e1 : ∀ q : Fin n,
        Q q c * act2 Q S p q = ∑ x, Q p x * (Q q c * ∑ y, Q q y * S x y) := by
      intro q
      simp only [act2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [Finset.sum_congr rfl fun q _ => e1 q, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum, sum_col_contract hQ c fun y => S x y]
  have hout : act2 (transp Q) (act2 Q S) b c
      = ∑ p, Q p b * ∑ q, Q q c * act2 Q S p q := by
    have hrhs : ∀ p : Fin n, Q p b * (∑ q, Q q c * act2 Q S p q)
        = ∑ q, Q p b * Q q c * act2 Q S p q := by
      intro p
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    rw [Finset.sum_congr rfl fun p _ => hrhs p]
    simp only [act2, transp]
  rw [hout, Finset.sum_congr rfl fun p _ => by rw [hinner p],
    sum_col_contract hQ b fun x => S x c]

/-- **AND THEREFORE A FRAME CHANGE CAN BE CANCELLED.** -/
theorem eq_of_act2_eq (hQ : IsOrth Q) {A B : Fin n → Fin n → ℝ}
    (h : ∀ b c, act2 Q A b c = act2 Q B b c) (b c : Fin n) : A b c = B b c := by
  have hf : act2 Q A = act2 Q B := funext fun x => funext fun y => h x y
  calc A b c = act2 (transp Q) (act2 Q A) b c := (act2_transp_act2 hQ A b c).symm
    _ = act2 (transp Q) (act2 Q B) b c := by rw [hf]
    _ = B b c := act2_transp_act2 hQ B b c

/-! ## 3. Step 3, named as a `Prop`

This is the real-symmetric spectral theorem written in the estate's vocabulary. It is stated, not
proved — `LovelockReduction` §1's reason applies verbatim: writing it as `theorem … := sorry`
would put a `sorry` in the estate for a statement nobody is currently attempting.
-/

/-- **THE ONE HYPOTHESIS `RicciProportional` NOW RESTS ON.** Every symmetric 2-tensor is diagonal
in some orthogonal frame. -/
def Diagonalisable (n : ℕ) : Prop :=
  ∀ S : Fin n → Fin n → ℝ, (∀ x y, S x y = S y x) →
    ∃ Q, IsOrth Q ∧ ∀ b c, b ≠ c → act2 Q S b c = 0

variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-- **`RicciProportional` FROM DIAGONALISATION ALONE.** Diagonalise the traceless Ricci tensor,
apply steps 1 and 2 in the adapted frame, and cancel the frame change with `eq_of_act2_eq`. -/
theorem ricciProportional_of_diagonalisable (hn2 : (n : ℝ) - 2 ≠ 0)
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {i₀ j₀ : Fin n} (hij₀ : i₀ ≠ j₀) (hD : Diagonalisable n) :
    RicciProportional T (T (ricciSeed (hIJ i₀ j₀)) i₀ i₀) := by
  intro R hR b c
  obtain ⟨Q, hQ, hd⟩ := hD (tracefreeRicci R) (tracefreeRicci_symm hR)
  -- in the adapted frame the traceless Ricci tensor is diagonal, so steps 1 and 2 apply
  have hdiagQ : ∀ x y : Fin n, x ≠ y → tracefreeRicci (act Q R) x y = 0 := by
    intro x y hxy
    rw [← act2_tracefreeRicci hQ R x y]
    exact hd x y hxy
  have key := T_ricciPart_eq_smul_of_diagonal hn2 hadd hsmul hequiv hij₀ hdiagQ
  -- both sides of `key` are the frame change applied to what we want
  have hL : ∀ x y : Fin n,
      T (ricciPart (act Q R)) x y = act2 Q (T (ricciPart R)) x y := by
    intro x y
    have hfun : ricciPart (act Q R) = act Q (ricciPart R) :=
      funext fun a => funext fun b' => funext fun c' => funext fun d' =>
        (act_ricciPart hQ R a b' c' d').symm
    rw [hfun]
    exact hequiv Q hQ (ricciPart R) (isAlgCurv_ricciPart hR) x y
  have hRHS : ∀ x y : Fin n,
      T (ricciSeed (hIJ i₀ j₀)) i₀ i₀ * tracefreeRicci (act Q R) x y
        = act2 Q (fun p q => T (ricciSeed (hIJ i₀ j₀)) i₀ i₀ * tracefreeRicci R p q) x y := by
    intro x y
    rw [act2_smul, act2_tracefreeRicci hQ]
  have heq : ∀ x y : Fin n, act2 Q (T (ricciPart R)) x y
      = act2 Q (fun p q => T (ricciSeed (hIJ i₀ j₀)) i₀ i₀ * tracefreeRicci R p q) x y := by
    intro x y
    rw [← hL x y, key x y, hRHS x y]
  exact eq_of_act2_eq hQ heq b c

end LovelockFrameInverse
