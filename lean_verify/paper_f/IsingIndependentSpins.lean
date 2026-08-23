/-
  IsingIndependentSpins.lean — the magnetisation of independent spins in a field, in closed form,
  and hence a LOWER BOUND on a ferromagnetic magnetisation that depends on nothing but `β·h`.

  WHY. `IsingGriffithsMono` proved that a correlation is monotone in the couplings and then named
  three legs it had not done, the second being: *"compute the zeroed model's magnetisation as a
  CONSTANT depending only on `β·h` — the sites are independent there, and this estate does not have
  that computation."* The watchlist trigger it left was *"when anything in this estate computes the
  magnetisation of a finite set of INDEPENDENT spins in a field."* **This is that computation**, and
  the third leg (that the constant is positive) is four lines after it.

  THE HYPOTHESIS IS ONE IDENTITY, WHICH IS WHY THIS IS USABLE. Rather than fixing the interaction
  family to be the singletons — which no concrete model in this estate literally is, since the
  zeroed terms are still present with coupling `0` — the theorems below take

      `∀ σ, ∑ᵢ Jᵢ · ∏_{Sᵢ} spin σ = c · ∑ᵥ spin (σ v)`

  as a hypothesis. Any model whose energy reduces to a uniform field satisfies it, whatever its
  index family looks like and however many zero couplings it carries.

  THE COMPUTATION. `exp` of a sum is a product, so the configuration sum factorises site by site
  (`Fintype.prod_sum`, the same step `IsingGriffiths` uses for the parity argument). Each factor is
  `∑_b exp (c · spin b) = eᶜ + e⁻ᶜ`, and the one factor carrying the observable is
  `∑_b spin b · exp (c · spin b) = eᶜ − e⁻ᶜ`. **The cardinality of the site set never appears**:
  numerator and denominator differ in exactly one factor, `Finset.mul_prod_erase` pulls that factor
  out of both, and the common product cancels. So the answer is `(eᶜ − e⁻ᶜ)/(eᶜ + e⁻ᶜ) = tanh c` at
  every finite site set, which is the whole point — a bound that does not know how big the box is.

  WHAT IS PROVED.

  * `sum_exp_spin`, `sum_spin_exp_spin` — the two one-site sums;
  * `part_eq`, `num_eq` — the factorisations, with the observable's factor split off;
  * **`expect_eq_tanh`** — `⟨σ_{v₀}⟩ = tanh c` for such a model, at every site and every finite site
    set;
  * **`tanh_le_expect`** — hence, with `IsingGriffithsMono.griffiths_expect_mono`, **a lower bound
    `tanh c ≤ ⟨σ_{v₀}⟩` for every ferromagnetic model dominating it**;
  * `expect_pos_of_pos` — and the bound is strictly positive when `c > 0`.

  WHAT IS STILL NOT DONE, AND IT IS NOW ONE THING. `IsingGriffithsMono`'s leg (i): exhibiting this
  estate's own slab couplings as such a dominated pair — the field terms kept, the intra and
  length-bond terms zeroed. Nothing here does that, and no claim is made about what it costs
  (`ERRATUM 246`). Until it is done, **this file proves nothing about the slab**; it proves a bound
  about any model that satisfies its hypothesis, and the slab has not been shown to.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingGriffithsMono

namespace IsingIndependentSpins

open Finset Real
open IsingTransfer2D IsingGriffiths IsingGriffithsMono

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {I : Type*} [Fintype I]

/-! ## 1. The two one-site sums -/

theorem sum_exp_spin (c : ℝ) : ∑ b : Bool, exp (c * spin b) = exp c + exp (-c) := by
  rw [Fintype.sum_bool]
  simp [spin]

theorem sum_spin_exp_spin (c : ℝ) :
    ∑ b : Bool, spin b * exp (c * spin b) = exp c - exp (-c) := by
  rw [Fintype.sum_bool]
  simp [spin]
  ring

/-! ## 2. The factorisations -/

variable (S : I → Finset V) (J : I → ℝ) (c : ℝ)

/-- The hypothesis carried by everything below: the model's energy IS a uniform field of
strength `c`. Stated as an identity on configurations so that zero couplings, extra index families
and any amount of bookkeeping are all allowed. -/
abbrev IsUniformField : Prop :=
  ∀ σ : V → Bool, ∑ i : I, J i * ∏ v ∈ S i, spin (σ v) = c * ∑ v : V, spin (σ v)

theorem part_eq (h : IsUniformField S J c) :
    part S J = ∏ _v : V, (exp c + exp (-c)) := by
  rw [part, Finset.sum_congr rfl fun σ _ => by rw [h σ, Finset.mul_sum, Real.exp_sum],
    ← Fintype.prod_sum fun (_ : V) (b : Bool) => exp (c * spin b)]
  exact Finset.prod_congr rfl fun _ _ => sum_exp_spin c

theorem num_eq (h : IsUniformField S J c) (v₀ : V) :
    num S J {v₀} = (exp c - exp (-c)) * ∏ _v ∈ Finset.univ.erase v₀, (exp c + exp (-c)) := by
  have hstep : ∀ σ : V → Bool,
      (∏ v ∈ ({v₀} : Finset V), spin (σ v)) * exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v))
        = ∏ v : V, ((if v = v₀ then spin (σ v) else 1) * exp (c * spin (σ v))) := by
    intro σ
    rw [Finset.prod_mul_distrib, Finset.prod_singleton, h σ, Finset.mul_sum, Real.exp_sum,
      Finset.prod_ite_eq' Finset.univ v₀ fun v => spin (σ v), if_pos (Finset.mem_univ v₀)]
  rw [num, Finset.sum_congr rfl fun σ _ => hstep σ,
    ← Fintype.prod_sum fun (v : V) (b : Bool) => (if v = v₀ then spin b else 1) * exp (c * spin b),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v₀)]
  congr 1
  · simpa using sum_spin_exp_spin c
  · refine Finset.prod_congr rfl fun v hv => ?_
    rw [Finset.sum_congr rfl fun b _ => by rw [if_neg (Finset.ne_of_mem_erase hv), one_mul]]
    exact sum_exp_spin c

/-! ## 3. The magnetisation -/

/-- **THE MAGNETISATION OF INDEPENDENT SPINS IN A FIELD IS `tanh c`**, at every site and at every
finite site set. The site count cancels: numerator and denominator differ in exactly one factor. -/
theorem expect_eq_tanh (h : IsUniformField S J c) (v₀ : V) :
    num S J {v₀} / part S J = tanh c := by
  have hpos : (0 : ℝ) < exp c + exp (-c) := by positivity
  have hP : (0 : ℝ) < ∏ _v ∈ Finset.univ.erase v₀, (exp c + exp (-c)) :=
    Finset.prod_pos fun _ _ => hpos
  rw [num_eq S J c h v₀, part_eq S J c h,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v₀),
    mul_comm (exp c - exp (-c)), mul_comm (exp c + exp (-c)),
    mul_div_mul_left _ _ (ne_of_gt hP), Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  rw [div_div_div_cancel_right₀]
  norm_num

/-! ## 4. The lower bound -/

/-- **AND SO A LOWER BOUND ON THE MAGNETISATION OF EVERY FERROMAGNETIC MODEL THAT DOMINATES IT.**
`J₀` is the pure field, `J` is anything at least as strong term by term, and the bound `tanh c`
depends on nothing but the field strength — **not on the site set, and not on how large it is**. -/
theorem tanh_le_expect (J₀ : I → ℝ) (h : IsUniformField S J₀ c) (hJ₀ : ∀ i, 0 ≤ J₀ i)
    (hle : ∀ i, J₀ i ≤ J i) (v₀ : V) :
    tanh c ≤ num S J {v₀} / part S J := by
  rw [← expect_eq_tanh S J₀ c h v₀]
  exact griffiths_expect_mono S J₀ J hJ₀ hle {v₀}

omit [Fintype V] [DecidableEq V] [Fintype I] in
/-- **`Real.tanh_pos` does not exist**, and the first draft of this docstring said it was merely
"not in the import closure", which would have told a reader to go looking for it. Grepped after the
build failed: this Mathlib has `Real.artanh_pos` — for the INVERSE function — and no sign lemma for
`tanh` at all. `IsingGriffiths.sinh_pos_of_pos` and `Real.cosh_pos` are both here, and the quotient
is two lines, which is the same trade `IsingGriffiths` made for the sign of `sinh`. -/
theorem tanh_pos_of_pos {c : ℝ} (hc : 0 < c) : 0 < tanh c := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (sinh_pos_of_pos hc) (Real.cosh_pos c)

/-- And the bound is strictly positive exactly when the field is on. -/
theorem expect_pos_of_pos (J₀ : I → ℝ) (h : IsUniformField S J₀ c) (hJ₀ : ∀ i, 0 ≤ J₀ i)
    (hle : ∀ i, J₀ i ≤ J i) (hc : 0 < c) (v₀ : V) :
    0 < num S J {v₀} / part S J :=
  lt_of_lt_of_le (tanh_pos_of_pos hc) (tanh_le_expect S J c J₀ h hJ₀ hle v₀)

end

end IsingIndependentSpins
