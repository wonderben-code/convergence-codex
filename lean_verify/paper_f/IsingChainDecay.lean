/-
  IsingChainDecay.lean — the pendant step, iterated: a field transmitted along a path of `k` bonds
  arrives multiplied by `(tanh J)^k`.

  WHY. `IsingPendantSite.pendant_expect` proved that ONE bond multiplies a transmitted
  magnetisation by `tanh J`, for an arbitrary model with an arbitrary energy. Its header, and
  `WALLS §W3.6`'s addendum, both say in terms that the ITERATION is not proved and that the
  geometric decay is an expectation rather than a theorem. **This file removes that sentence by
  doing the induction.**

  THERE IS NO NEW MATHEMATICS HERE AND THE FILE SAYS SO. Every step is `pendant_expect` and the
  content is entirely bookkeeping: a site set that grows by one `Option` per bond, its `Fintype`
  and `DecidableEq` instances built by the same recursion, and an induction that composes `k`
  copies of one theorem. **That is the point.** The mathematics was finished when the pendant step
  was stated at the right generality; what remained was to say `k` times.

  WHAT IT COMES TO. `chain_expect`: attach a path of `k` unfielded sites to a site `v₀` of any
  model, each bond of strength `J`. The far end has magnetisation `(tanh J)^k · ⟨σ_{v₀}⟩`, the
  expectation on the right being in the ORIGINAL model. Since `|tanh J| < 1` for every real `J`,
  **the transmitted field decays geometrically in the distance** — `chain_expect_abs_le` states
  that against the bound `|⟨σ_{v₀}⟩| ≤ 1`, so the decay is uniform in the model attached.

  WHAT IT DOES NOT DO, AND `WALLS §W3.6` IS UNMOVED. This is a statement about a comparison model,
  not about the Ising box: nothing here says which paths exist in an `n × n` box, and the step from
  "a path of length `k` transmits `(tanh J)^k`" to "a chain comparison on the box delivers `O(n)`"
  needs a count of paths and their lengths that is **not attempted here** (`ERRATUM 246`). What is
  now settled is the ingredient that step would use, and that it is a theorem rather than a
  physical expectation.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingPendantSite

namespace IsingChainDecay

open Finset Real
open IsingGriffiths IsingTransfer2D IsingPendantSite

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The site set grows by one `Option` per bond -/

/-- `chainSite V k` is `V` with `k` sites attached in a path. -/
abbrev chainSite (V : Type*) : ℕ → Type _
  | 0 => V
  | k + 1 => Option (chainSite V k)

instance chainFintype (V : Type*) [Fintype V] : (k : ℕ) → Fintype (chainSite V k)
  | 0 => inferInstanceAs (Fintype V)
  | k + 1 => letI := chainFintype V k; inferInstanceAs (Fintype (Option (chainSite V k)))

instance chainDecEq (V : Type*) [DecidableEq V] : (k : ℕ) → DecidableEq (chainSite V k)
  | 0 => inferInstanceAs (DecidableEq V)
  | k + 1 => letI := chainDecEq V k; inferInstanceAs (DecidableEq (Option (chainSite V k)))

/-- The site at the far end: the one added last. -/
def lastSite (V : Type*) (v₀ : V) : (k : ℕ) → chainSite V k
  | 0 => v₀
  | _ + 1 => none

/-- The energy after `k` bonds: one `pendantE` per bond, each attached to the previous far end. -/
def chainE (E : (V → Bool) → ℝ) (J : ℝ) (v₀ : V) :
    (k : ℕ) → (chainSite V k → Bool) → ℝ
  | 0 => E
  | k + 1 => pendantE (chainE E J v₀ k) J (lastSite V v₀ k)

/-! ## 2. The induction -/

/-- **A FIELD TRANSMITTED ALONG `k` BONDS ARRIVES MULTIPLIED BY `(tanh J)^k`.** Every step is
`IsingPendantSite.pendant_expect`; there is no new mathematics in the proof and none in the
statement. -/
theorem chain_expect (E : (V → Bool) → ℝ) (J : ℝ) (v₀ : V) (k : ℕ) :
    baseNum (chainE E J v₀ k) (lastSite V v₀ k) / basePart (chainE E J v₀ k)
      = tanh J ^ k * (baseNum E v₀ / basePart E) := by
  induction k with
  | zero => simp [chainE, lastSite]
  | succ k ih =>
      have hnum : baseNum (chainE E J v₀ (k + 1)) (lastSite V v₀ (k + 1))
          = pendantNum (chainE E J v₀ k) J (lastSite V v₀ k) := rfl
      have hpart : basePart (chainE E J v₀ (k + 1))
          = pendantPart (chainE E J v₀ k) J (lastSite V v₀ k) := rfl
      rw [hnum, hpart, pendant_expect, ih, pow_succ]
      ring

/-! ## 3. Geometric decay, uniformly in the model attached -/

/-- A magnetisation is an average of `±1`, so it never exceeds `1` in absolute value. -/
theorem abs_baseNum_div_le (E : (V → Bool) → ℝ) (v₀ : V) :
    |baseNum E v₀ / basePart E| ≤ 1 := by
  have hZ : (0:ℝ) < basePart E := basePart_pos E
  rw [abs_div, abs_of_pos hZ, div_le_one hZ]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [abs_mul, abs_of_pos (exp_pos (E τ))]
  have hs : |spin (τ v₀)| = 1 := by
    cases τ v₀ <;> simp [spin]
  rw [hs, one_mul]

/-- **AND SO THE TRANSMITTED FIELD DECAYS GEOMETRICALLY IN THE DISTANCE, WHATEVER IS ATTACHED.**
`|tanh J| < 1` at every real `J`, and the bound on the right does not mention the model. -/
theorem chain_expect_abs_le (E : (V → Bool) → ℝ) (J : ℝ) (v₀ : V) (k : ℕ) :
    |baseNum (chainE E J v₀ k) (lastSite V v₀ k) / basePart (chainE E J v₀ k)|
      ≤ |tanh J| ^ k := by
  rw [chain_expect, abs_mul, abs_pow]
  refine mul_le_of_le_one_right (by positivity) ?_
  exact abs_baseNum_div_le E v₀

end

end IsingChainDecay
