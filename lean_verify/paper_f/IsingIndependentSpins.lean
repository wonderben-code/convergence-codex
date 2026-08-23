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

  ADDENDUM 2026-08-23, SAME DAY — **THE OBSERVABLE NO LONGER HAS TO BE ONE SITE.** The bullets
  above are kept (`ERRATUM 94`) and now read one case of a general statement:
  **`expect_eq_tanh_pow`** — `⟨∏_{v ∈ A} σ_v⟩ = (tanh c)^{|A|}` for EVERY `A` — and
  **`tanh_pow_le_expect`**, the corresponding lower bound for every dominating ferromagnetic model.
  `expect_eq_tanh` and `tanh_le_expect` are now the `|A| = 1` instances, so the generalisation is
  instantiated and not left standing on its own (`ERRATUM 201`).

  **AND THE CANCELLATION STILL DOES THE WORK.** Numerator and denominator differ only on `A`, so the
  factor over the complement divides out whatever the complement is. `|A|` survives — but `A` is the
  OBSERVABLE, not the box, so the bound is still uniform in the site set. At `|A| = 2` this is a
  lower bound on a two-point function that does not depend on how far apart the two sites are.

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

theorem num_eq (h : IsUniformField S J c) (A : Finset V) :
    num S J A
      = (exp c - exp (-c)) ^ A.card * (exp c + exp (-c)) ^ (Finset.univ \ A).card := by
  have hstep : ∀ σ : V → Bool,
      (∏ v ∈ A, spin (σ v)) * exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v))
        = ∏ v : V, ((if v ∈ A then spin (σ v) else 1) * exp (c * spin (σ v))) := by
    intro σ
    rw [Finset.prod_mul_distrib, h σ, Finset.mul_sum, Real.exp_sum, Finset.prod_ite_mem,
      Finset.univ_inter]
  have hA : ∀ v ∈ A, (∑ b : Bool, (if v ∈ A then spin b else 1) * exp (c * spin b))
      = exp c - exp (-c) := by
    intro v hv
    simp only [if_pos hv]
    exact sum_spin_exp_spin c
  have hB : ∀ v ∈ Finset.univ \ A,
      (∑ b : Bool, (if v ∈ A then spin b else 1) * exp (c * spin b)) = exp c + exp (-c) := by
    intro v hv
    simp only [if_neg (Finset.mem_sdiff.mp hv).2, one_mul]
    exact sum_exp_spin c
  have h1 : ∏ v ∈ A, (∑ b : Bool, (if v ∈ A then spin b else 1) * exp (c * spin b))
      = (exp c - exp (-c)) ^ A.card := by
    rw [Finset.prod_congr rfl hA, Finset.prod_const]
  have h2 : ∏ v ∈ Finset.univ \ A,
        (∑ b : Bool, (if v ∈ A then spin b else 1) * exp (c * spin b))
      = (exp c + exp (-c)) ^ (Finset.univ \ A).card := by
    rw [Finset.prod_congr rfl hB, Finset.prod_const]
  rw [num, Finset.sum_congr rfl fun σ _ => hstep σ,
    ← Fintype.prod_sum fun (v : V) (b : Bool) =>
      (if v ∈ A then spin b else 1) * exp (c * spin b),
    ← Finset.prod_sdiff (Finset.subset_univ A), h1, h2, mul_comm]

/-- The partition function split the same way, so that the common factor is visible and cancels. -/
theorem part_eq_split (h : IsUniformField S J c) (A : Finset V) :
    part S J
      = (exp c + exp (-c)) ^ A.card * (exp c + exp (-c)) ^ (Finset.univ \ A).card := by
  rw [part_eq S J c h, ← Finset.prod_sdiff (Finset.subset_univ A), Finset.prod_const,
    Finset.prod_const, mul_comm]

/-! ## 3. The magnetisation -/

omit [Fintype V] [DecidableEq V] [Fintype I] in
theorem tanh_eq_exp_ratio (c : ℝ) : tanh c = (exp c - exp (-c)) / (exp c + exp (-c)) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, div_div_div_cancel_right₀]
  norm_num

/-- **EVERY CORRELATION OF INDEPENDENT SPINS IN A FIELD IS `(tanh c) ^ |A|`**, at every finite site
set. **The site count still cancels** — numerator and denominator differ only on `A`, so the factor
over the complement divides out whatever the complement is. Only `|A|` survives, and `A` is the
observable, not the box. -/
theorem expect_eq_tanh_pow (h : IsUniformField S J c) (A : Finset V) :
    num S J A / part S J = tanh c ^ A.card := by
  have hpos : (0 : ℝ) < exp c + exp (-c) := by positivity
  rw [num_eq S J c h A, part_eq_split S J c h A,
    mul_div_mul_right _ _ (ne_of_gt (pow_pos hpos (Finset.univ \ A).card)),
    ← div_pow, ← tanh_eq_exp_ratio]

/-- **THE MAGNETISATION**, the `|A| = 1` case, and the one the chain was built for. -/
theorem expect_eq_tanh (h : IsUniformField S J c) (v₀ : V) :
    num S J {v₀} / part S J = tanh c := by
  rw [expect_eq_tanh_pow S J c h {v₀}, Finset.card_singleton, pow_one]

/-! ## 4. The lower bound -/

/-- **AND SO A LOWER BOUND ON EVERY CORRELATION OF EVERY FERROMAGNETIC MODEL THAT DOMINATES IT.**
`J₀` is the pure field, `J` is anything at least as strong term by term, and the bound
`(tanh c) ^ |A|` depends on the field strength and on the OBSERVABLE — **not on the site set, and
not on how large it is**. -/
theorem tanh_pow_le_expect (J₀ : I → ℝ) (h : IsUniformField S J₀ c) (hJ₀ : ∀ i, 0 ≤ J₀ i)
    (hle : ∀ i, J₀ i ≤ J i) (A : Finset V) :
    tanh c ^ A.card ≤ num S J A / part S J := by
  rw [← expect_eq_tanh_pow S J₀ c h A]
  exact griffiths_expect_mono S J₀ J hJ₀ hle A

/-- The magnetisation case. -/
theorem tanh_le_expect (J₀ : I → ℝ) (h : IsUniformField S J₀ c) (hJ₀ : ∀ i, 0 ≤ J₀ i)
    (hle : ∀ i, J₀ i ≤ J i) (v₀ : V) :
    tanh c ≤ num S J {v₀} / part S J := by
  have := tanh_pow_le_expect S J c J₀ h hJ₀ hle {v₀}
  rwa [Finset.card_singleton, pow_one] at this

omit [Fintype V] [DecidableEq V] [Fintype I] in
/-- **`Real.tanh_pos` does not exist**, and the first draft of this docstring said it was merely
"not in the import closure", which would have told a reader to go looking for it. Grepped after the
build failed: this Mathlib has `Real.artanh_pos` — for the INVERSE function — and no sign lemma for
`tanh` at all. `IsingGriffiths.sinh_pos_of_pos` and `Real.cosh_pos` are both here, and the quotient
is two lines, which is the same trade `IsingGriffiths` made for the sign of `sinh`. -/
theorem tanh_pos_of_pos {c : ℝ} (hc : 0 < c) : 0 < tanh c := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (sinh_pos_of_pos hc) (Real.cosh_pos c)

/-- And every such correlation is strictly positive when the field is on. -/
theorem expect_pos_of_pos (J₀ : I → ℝ) (h : IsUniformField S J₀ c) (hJ₀ : ∀ i, 0 ≤ J₀ i)
    (hle : ∀ i, J₀ i ≤ J i) (hc : 0 < c) (A : Finset V) :
    0 < num S J A / part S J :=
  lt_of_lt_of_le (pow_pos (tanh_pos_of_pos hc) A.card) (tanh_pow_le_expect S J c J₀ h hJ₀ hle A)

end

end IsingIndependentSpins
