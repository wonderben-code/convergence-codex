/-
  IsingIsolatedSite.lean — a site the energy never mentions changes no correlation, and that is the
  first piece of the transport `WALLS §W3.6` names as the remaining obstacle.

  WHY. `IsingChainDecay` proves what a path of bonds transmits, on a site set built by adding one
  `Option` per bond. The Ising box lives on `Fin n × Fin n`. Connecting the two — the step
  `SPINE`'s 24 August addendum names as the last one on this arm — needs to know that the box's
  *other* sites, the ones a path-only comparison model never mentions, can be ignored. **This file
  proves exactly that**, and no more.

  WHAT IS PROVED. `isolated_expect`: if the energy is a function of the old configuration only —
  `E (fun v => σ (some v))`, with the new site `none` appearing nowhere — then the correlation at
  an OLD site is unchanged by the new site's presence. Both numerator and partition function are
  multiplied by exactly `2`, and the factor cancels.

  **`isolated_part` COMES FREE AND `isolated_num` DOES NOT.** The partition half is
  `IsingPendantSite.pendant_part` at `J = 0`, where `exp 0 + exp 0 = 2`: an isolated site is a
  pendant site with its bond switched off. The numerator half is **not** an instance of
  `pendant_num`, because that computes the expectation at the NEW site — which is `0` here, by
  `tanh 0` — while this computes it at an OLD one. Different observable, so it is proved rather
  than instantiated, and the header says so rather than letting a reader assume symmetry.

  WHAT IT DOES NOT DO. One site at a time. Iterating it to "the box's sites outside a path can all
  be ignored" is an induction of the same shape as `IsingChainDecay`'s, and the path-existence
  argument is beyond both. **Neither is attempted and neither's cost is claimed** (`ERRATUM 246`).
  **No wall moves.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingPendantSite
import IsingChainDecay

namespace IsingIsolatedSite

open Finset Real
open IsingGriffiths IsingTransfer2D IsingPendantSite

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- An isolated site is a pendant site with its bond switched off. -/
theorem pendantE_zero (E : (V → Bool) → ℝ) (v₀ : V) (σ : Option V → Bool) :
    pendantE E 0 v₀ σ = E (fun v => σ (some v)) := by
  rw [pendantE, zero_mul, zero_mul, add_zero]

/-- **THE PARTITION FUNCTION DOUBLES**, and this half is free: it is `pendant_part` at `J = 0`. -/
theorem isolated_part (E : (V → Bool) → ℝ) (v₀ : V) :
    ∑ σ : Option V → Bool, exp (E (fun v => σ (some v))) = 2 * basePart E := by
  have h := pendant_part E 0 v₀
  rw [pendantPart] at h
  simp only [pendantE_zero] at h
  rw [h]
  norm_num

/-- **AND SO DOES THE NUMERATOR AT AN OLD SITE.** This is NOT an instance of `pendant_num`, which
computes the expectation at the NEW site; the observable here is an old one. Each old
configuration is counted twice — once with the new spin up, once down — and the energy cannot tell
the difference. -/
theorem isolated_num (E : (V → Bool) → ℝ) (v₀ : V) :
    ∑ σ : Option V → Bool, spin (σ (some v₀)) * exp (E (fun v => σ (some v)))
      = 2 * baseNum E v₀ := by
  rw [sum_option, baseNum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring

/-- **A SITE THE ENERGY NEVER MENTIONS CHANGES NO CORRELATION.** Both halves double and the factor
cancels. -/
theorem isolated_expect (E : (V → Bool) → ℝ) (v₀ : V) :
    (∑ σ : Option V → Bool, spin (σ (some v₀)) * exp (E (fun v => σ (some v))))
      / (∑ σ : Option V → Bool, exp (E (fun v => σ (some v))))
      = baseNum E v₀ / basePart E := by
  rw [isolated_num E v₀, isolated_part E v₀]
  have hZ : (0:ℝ) < basePart E := basePart_pos E
  field_simp

/-! ## 2. ADDENDUM — the same, `k` sites at a time

The induction is the one `IsingChainDecay.chain_expect` performs, with the bond switched off at
every step, so the site set and its two instances are **reused rather than rebuilt**. -/

/-- The energy after `k` isolated sites are added: it still never mentions any of them. -/
def isoE (E : (V → Bool) → ℝ) : (k : ℕ) → (IsingChainDecay.chainSite V k → Bool) → ℝ
  | 0 => E
  | _ + 1 => fun σ => isoE E _ (fun v => σ (some v))

/-- The original site, seen from inside the enlarged site set. -/
def oldSite (V : Type*) (v₀ : V) : (k : ℕ) → IsingChainDecay.chainSite V k
  | 0 => v₀
  | _ + 1 => some (oldSite V v₀ _)

/-- **ANY NUMBER OF SITES THE ENERGY NEVER MENTIONS CHANGE NO CORRELATION.** Each step doubles both
halves and each doubling cancels; `2^k` never appears because it is cancelled as it is created. -/
theorem iso_expect (E : (V → Bool) → ℝ) (v₀ : V) (k : ℕ) :
    baseNum (isoE E k) (oldSite V v₀ k) / basePart (isoE E k) = baseNum E v₀ / basePart E := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hnum : baseNum (isoE E (k + 1)) (oldSite V v₀ (k + 1))
          = 2 * baseNum (isoE E k) (oldSite V v₀ k) :=
        isolated_num (isoE E k) (oldSite V v₀ k)
      have hpart : basePart (isoE E (k + 1)) = 2 * basePart (isoE E k) :=
        isolated_part (isoE E k) (oldSite V v₀ k)
      rw [hnum, hpart, ← ih]
      have hZ : (0:ℝ) < basePart (isoE E k) := basePart_pos _
      field_simp

end

end IsingIsolatedSite
