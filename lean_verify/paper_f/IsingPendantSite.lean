/-
  IsingPendantSite.lean — what ONE more bond does, at the generality where the rest of the model
  is arbitrary.

  WHY. `IsingCoupledPair` computed a two-site model and found that a site with no field of its
  own, bonded to a site carrying field `a`, has magnetisation `tanh J · tanh a`. That is one
  instance of a recursion, and this file states the recursion. `WALLS §W3.6` names the chain case
  — bonds in sequence — as the next rung; this is the step it is an induction over.

  WHAT IS PROVED. Take ANY finite-volume model on a site set `V`, with an arbitrary energy
  `E : (V → Bool) → ℝ` — no ferromagnetism, no non-negativity, no structure whatever. Add one new
  site, bonded with strength `J` to a single existing site `v₀`, carrying no field of its own.
  Then

      ⟨σ_new⟩ = tanh J · ⟨σ_{v₀}⟩,

  where the right-hand expectation is in the ORIGINAL model — `pendant_expect`. **One bond
  multiplies the transmitted magnetisation by `tanh J`, and by nothing else.**

  THE TWO IDENTITIES BEHIND IT, AND THEY ARE THE WHOLE CONTENT. Summing over the new spin gives
  `exp (J·s) ± exp (−J·s)` with `s = ±1`, and

  * the `+` combination is `exp J + exp (−J)` — **independent of `s`**, because `cosh` is even, so
    the partition function is the old one times a constant (`pendant_part`);
  * the `−` combination is `s · (exp J − exp (−J))` — **proportional to `s`**, because `sinh` is
    odd, so the numerator is the old one at the observable `σ_{v₀}` times a constant
    (`pendant_num`).

  The ratio is `tanh J` times the old ratio, and every hypothesis one might expect — that the old
  model is ferromagnetic, that `J ≥ 0`, that there is a field anywhere — is absent because neither
  identity uses one.

  WHAT THIS DOES NOT DO. It is one step, not the chain. Iterating it along a path of length `k`
  would give `(tanh J)^k · ⟨σ_{v₀}⟩`, which decays geometrically in the distance — and that is
  exactly why a chain comparison is expected to leave `WALLS §W3.6`'s arithmetic unchanged. **The
  iteration is not performed here and the expectation is not a theorem** (`ERRATUM 246`): setting
  up a path model and inducting over it is a separate unit, and until it is written this file
  claims one bond and nothing more.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingGriffithsMono

namespace IsingPendantSite

open Finset Real
open IsingGriffiths IsingTransfer2D

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The two parity identities -/

/-- `cosh` is even, so the `+` combination does not see the spin. -/
theorem exp_spin_add (J : ℝ) (b : Bool) :
    exp (J * spin b) + exp (-(J * spin b)) = exp J + exp (-J) := by
  have st : spin true = (1:ℝ) := rfl
  have sf : spin false = (-1:ℝ) := rfl
  cases b
  · rw [sf]
    rw [show J * (-1:ℝ) = -J by ring, neg_neg]
    ring
  · rw [st, mul_one]

/-- `sinh` is odd, so the `−` combination is proportional to the spin. -/
theorem exp_spin_sub (J : ℝ) (b : Bool) :
    exp (J * spin b) - exp (-(J * spin b)) = spin b * (exp J - exp (-J)) := by
  have st : spin true = (1:ℝ) := rfl
  have sf : spin false = (-1:ℝ) := rfl
  cases b
  · rw [sf]
    rw [show J * (-1:ℝ) = -J by ring, neg_neg]
    ring
  · rw [st, mul_one]
    ring

/-! ## 2. The model with one site added -/

/-- The energy of the extended model: the old energy, plus one bond from the new site to `v₀`. -/
def pendantE (E : (V → Bool) → ℝ) (J : ℝ) (v₀ : V) (σ : Option V → Bool) : ℝ :=
  E (fun v => σ (some v)) + J * spin (σ (some v₀)) * spin (σ none)

def basePart (E : (V → Bool) → ℝ) : ℝ := ∑ τ : V → Bool, exp (E τ)

def baseNum (E : (V → Bool) → ℝ) (v₀ : V) : ℝ := ∑ τ : V → Bool, spin (τ v₀) * exp (E τ)

def pendantPart (E : (V → Bool) → ℝ) (J : ℝ) (v₀ : V) : ℝ :=
  ∑ σ : Option V → Bool, exp (pendantE E J v₀ σ)

def pendantNum (E : (V → Bool) → ℝ) (J : ℝ) (v₀ : V) : ℝ :=
  ∑ σ : Option V → Bool, spin (σ none) * exp (pendantE E J v₀ σ)

theorem basePart_pos (E : (V → Bool) → ℝ) : 0 < basePart E :=
  Finset.sum_pos (fun _ _ => exp_pos _) ⟨fun _ => true, Finset.mem_univ _⟩

omit [Fintype V] [DecidableEq V] in
/-- **THE EXTENDED ENERGY AT A SPLIT CONFIGURATION IS THE OLD ONE PLUS ONE TERM**, and it holds by
`rfl`: `Option.rec` reduces on both constructors, so nothing has to be simplified. Doing this
before any arithmetic is what keeps §3 to one `linear_combination` each. -/
theorem pendantE_eval (E : (V → Bool) → ℝ) (J : ℝ) (v₀ : V) (τ : V → Bool) (b : Bool) :
    pendantE E J v₀ (fun o => Option.rec b τ o) = E τ + J * spin (τ v₀) * spin b := rfl

/-- Every sum over `Option V → Bool` splits into the new spin and the old configuration. -/
theorem sum_option (f : (Option V → Bool) → ℝ) :
    ∑ σ : Option V → Bool, f σ
      = ∑ τ : V → Bool, (f (fun o => Option.rec true τ o) + f (fun o => Option.rec false τ o)) := by
  rw [← (Equiv.piOptionEquivProd (β := fun _ : Option V => Bool)).symm.sum_comp f,
    Fintype.sum_prod_type]
  simp [Equiv.piOptionEquivProd, Finset.sum_add_distrib]

/-! ## 3. The partition function and the numerator -/

theorem pendant_part (E : (V → Bool) → ℝ) (J : ℝ) (v₀ : V) :
    pendantPart E J v₀ = (exp J + exp (-J)) * basePart E := by
  rw [pendantPart, sum_option, basePart, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [pendantE_eval, pendantE_eval]
  have st : spin true = (1:ℝ) := rfl
  have sf : spin false = (-1:ℝ) := rfl
  have ht : J * spin (τ v₀) * spin true = J * spin (τ v₀) := by rw [st]; ring
  have hf : J * spin (τ v₀) * spin false = -(J * spin (τ v₀)) := by rw [sf]; ring
  rw [ht, hf, Real.exp_add, Real.exp_add]
  linear_combination exp (E τ) * exp_spin_add J (τ v₀)

theorem pendant_num (E : (V → Bool) → ℝ) (J : ℝ) (v₀ : V) :
    pendantNum E J v₀ = (exp J - exp (-J)) * baseNum E v₀ := by
  rw [pendantNum, sum_option, baseNum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [pendantE_eval, pendantE_eval]
  have st : spin true = (1:ℝ) := rfl
  have sf : spin false = (-1:ℝ) := rfl
  have ht : J * spin (τ v₀) * spin true = J * spin (τ v₀) := by rw [st]; ring
  have hf : J * spin (τ v₀) * spin false = -(J * spin (τ v₀)) := by rw [sf]; ring
  rw [ht, hf, Real.exp_add, Real.exp_add, st, sf]
  linear_combination exp (E τ) * exp_spin_sub J (τ v₀)

/-! ## 4. The recursion -/

/-- **ONE BOND MULTIPLIES THE TRANSMITTED MAGNETISATION BY `tanh J`, AND BY NOTHING ELSE.** The
energy of the original model is arbitrary: no ferromagnetism, no sign condition on `J`, no field
anywhere. -/
theorem pendant_expect (E : (V → Bool) → ℝ) (J : ℝ) (v₀ : V) :
    pendantNum E J v₀ / pendantPart E J v₀ = tanh J * (baseNum E v₀ / basePart E) := by
  rw [pendant_num, pendant_part, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hJ : (0:ℝ) < exp J + exp (-J) := by positivity
  have hZ : (0:ℝ) < basePart E := basePart_pos E
  field_simp

end

end IsingPendantSite
