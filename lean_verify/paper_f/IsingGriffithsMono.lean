/-
  IsingGriffithsMono.lean — a ferromagnetic correlation is MONOTONE in the couplings.
  Griffiths' second inequality, in the form the estate needs, and it reduces to the first.

  WHY, AND IT IS NAMED IN THE WATCHLIST RATHER THAN GUESSED AT. The standing re-sweep of 23 August
  found that two unrelated methods — the `FieldThreshold`/`SharpThreshold` chain and
  `IsingSlabStrict.expectG_slab_pos` — now fail at the *same* missing ingredient: both give a
  positive magnetisation at each finite box and nothing uniform across boxes. It named the next rung
  as a route: *"Griffiths' SECOND inequality … would compare the coupled model against the SAME box
  with every intra coupling set to zero."* **This file is that rung.** It does not by itself close
  any item, and §5 says exactly what is still missing.

  THE REDUCTION, WHICH IS THE WHOLE CONTENT. Write `⟨σ_A⟩_J = N(J)/Z(J)`. Then

    `N(J')·Z(J) − N(J)·Z(J') = ∑_{σ,σ'} (∏_A σ − ∏_A σ') · exp(H_{J'}(σ) + H_J(σ'))`,

  and the doubled sum is re-indexed by `σ' = σ·τ`, the configuration whose spin at each site is the
  PRODUCT of the two. Under that substitution

    `∏_S σ' = (∏_S σ)(∏_S τ)`,  so  `H_{J'}(σ) + H_J(σ·τ) = ∑_i (J'ᵢ + Jᵢ·∏_S τ)·∏_S σ`,

  and `∏_A σ − ∏_A(σ·τ) = (∏_A σ)(1 − ∏_A τ)`. **Both factors are then non-negative for reasons
  already in the estate**: `1 − ∏_A τ ≥ 0` because a product of spins is `±1`, and the inner
  `σ`-sum is `IsingGriffiths.griffiths_nonneg` applied with the τ-dependent couplings
  `J'ᵢ + Jᵢ·∏_S τ`, which are `≥ 0` exactly because `0 ≤ J ≤ J'` — the `∏_S τ = −1` case is where
  `J ≤ J'` is used and the `+1` case is where `0 ≤ J` is.

  **SO GKS-II IS GKS-I EVALUATED AT A DIFFERENT COUPLING VECTOR**, and the usual apparatus of the
  duplicate-variable proof — new variables, a second Hamiltonian, a positivity argument of its own —
  is not needed here because `griffiths_nonneg` was already stated for an ARBITRARY family of
  interaction sets with arbitrary non-negative couplings. A theorem stated at the right generality
  paid for a second theorem three weeks later.

  ON `Bool`, THE PRODUCT IS `==` AND NOT `xor`, AND GETTING THAT BACKWARDS IS THE ONE TRAP.
  `spin` sends `false` to `−1`, so the spin-multiplicative identity is `true`, not `false`:
  `spin (a == b) = spin a · spin b`, while `spin (xor a b) = −spin a · spin b`. `cfgMul` is `==`
  pointwise, and it is an involution in its second argument, which is what makes it a re-indexing.

  WHAT IS PROVED.

  * `spin_cfgMul`, `prod_spin_cfgMul`, `cfgMulEquiv` — the re-indexing;
  * `dcoup`, `dcoup_nonneg` — the τ-dependent couplings and the only place the hypotheses are used;
  * `num_mul_part_le` — the unnormalised inequality `N(J)·Z(J') ≤ N(J')·Z(J)`;
  * **`griffiths_expect_mono`** — hence `⟨σ_A⟩_J ≤ ⟨σ_A⟩_{J'}` whenever `0 ≤ J ≤ J'` pointwise.

  WHAT IS NOT PROVED HERE, AND §5 IS WHERE THE ROUTE STOPS. The intended application needs three
  more things, none of them attempted in this file: that the estate's slab couplings can be
  presented as such a pair `J ≤ J'` with the intra part zeroed in `J`; that the zeroed model's
  magnetisation is a CONSTANT depending only on `β·h`; and that the constant is positive. The first
  looks like bookkeeping and the second is a computation this estate does not have — `tanh` occurs
  only in `IsingTransferMatrix.ratio_eq_tanh`, which is a spectral ratio and not a magnetisation
  (grepped 23 Aug during the re-sweep that named this rung, i.e. BEFORE this file was written —
  the label goes after the probe, `ERRATUM 250`). **No claim is made here about what those cost**
  (`ERRATUM 246`).

  ⚠ **TWO OF THE THREE WERE DONE ELEVEN MINUTES LATER. Annotated 2026-09-01** (`ERRATUM 94`,
  `ERRATUM 393`). This file was committed at **2026-08-23 14:27**; `IsingIndependentSpins` at
  **14:38**, and its header quotes the sentence above — *"the second being: 'compute the zeroed
  model's magnetisation as a CONSTANT depending only on `β·h` … this estate does not have that
  computation'. **This is that computation**"* — and adds that the third leg, positivity of the
  constant, *"is four lines after it"*. So the second and third of the three named needs were met
  the same afternoon; **the first, presenting the slab couplings as such a pair, is untouched and
  the sentence stands for it.** The probe recorded above was sound and its discipline —
  the label going after the probe — is exactly right; what is missing is anyone coming back.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingGriffiths

namespace IsingGriffithsMono

open Finset Real
open IsingTransfer2D IsingGriffiths

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {I : Type*} [Fintype I]

/-! ## 1. The pointwise product of two configurations -/

/-- The configuration whose spin at each site is the PRODUCT of the two given spins. On `Bool` that
is `==` and not `xor`: `spin false = −1`, so the spin-multiplicative identity is `true`. -/
def cfgMul (σ τ : V → Bool) : V → Bool := fun v => (σ v == τ v)

omit [Fintype V] [DecidableEq V] in
theorem spin_cfgMul (σ τ : V → Bool) (v : V) :
    spin (cfgMul σ τ v) = spin (σ v) * spin (τ v) := by
  cases h1 : σ v <;> cases h2 : τ v <;> simp [cfgMul, spin, h1, h2]

omit [Fintype V] [DecidableEq V] in
theorem cfgMul_involutive (σ : V → Bool) : Function.Involutive (cfgMul σ) := by
  intro τ
  funext v
  cases h1 : σ v <;> cases h2 : τ v <;> simp [cfgMul, h1, h2]

/-- Multiplying by a fixed configuration is therefore a permutation of the configuration space, and
that is the re-indexing the whole proof runs on. -/
def cfgMulEquiv (σ : V → Bool) : (V → Bool) ≃ (V → Bool) :=
  (cfgMul_involutive σ).toPerm _

omit [Fintype V] [DecidableEq V] in
@[simp] theorem cfgMulEquiv_apply (σ τ : V → Bool) : cfgMulEquiv σ τ = cfgMul σ τ := rfl

omit [Fintype V] [DecidableEq V] in
theorem prod_spin_cfgMul (A : Finset V) (σ τ : V → Bool) :
    ∏ v ∈ A, spin (cfgMul σ τ v) = (∏ v ∈ A, spin (σ v)) * ∏ v ∈ A, spin (τ v) := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => spin_cfgMul σ τ v

/-! ## 2. The τ-dependent couplings, and the only place the hypotheses are used -/

/-- The coupling vector the doubled system sees at the auxiliary configuration `τ`. -/
def dcoup (S : I → Finset V) (J J' : I → ℝ) (τ : V → Bool) : I → ℝ :=
  fun i => J' i + J i * ∏ v ∈ S i, spin (τ v)

omit [Fintype V] [DecidableEq V] [Fintype I] in
/-- **AND IT IS NON-NEGATIVE EXACTLY BECAUSE `0 ≤ J ≤ J'`.** The `∏ τ = 1` case needs `0 ≤ J`; the
`∏ τ = −1` case needs `J ≤ J'`. Neither hypothesis is spare. -/
theorem dcoup_nonneg (S : I → Finset V) {J J' : I → ℝ} (hJ : ∀ i, 0 ≤ J i)
    (hle : ∀ i, J i ≤ J' i) (τ : V → Bool) (i : I) : 0 ≤ dcoup S J J' τ i := by
  simp only [dcoup]
  rcases prod_spin_eq_one_or (S i) τ with h | h <;> rw [h] <;>
    [linarith [hJ i, hle i]; linarith [hJ i, hle i]]

/-! ## 3. The two sides, named -/

/-- The unnormalised correlation. -/
def num (S : I → Finset V) (J : I → ℝ) (A : Finset V) : ℝ :=
  ∑ σ : V → Bool, (∏ v ∈ A, spin (σ v)) * exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v))

/-- The partition function. -/
def part (S : I → Finset V) (J : I → ℝ) : ℝ :=
  ∑ σ : V → Bool, exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v))

theorem part_pos (S : I → Finset V) (J : I → ℝ) : 0 < part S J :=
  Finset.sum_pos (fun _ _ => exp_pos _) ⟨fun _ => true, Finset.mem_univ _⟩

omit [Fintype V] [DecidableEq V] in
/-- The two Boltzmann factors of the doubled system collapse onto one, at the coupling `dcoup τ`.
This is the identity the substitution `σ' = σ·τ` exists to produce. -/
theorem exp_mul_exp_cfgMul (S : I → Finset V) (J J' : I → ℝ) (σ τ : V → Bool) :
    exp (∑ i : I, J' i * ∏ v ∈ S i, spin (σ v))
        * exp (∑ i : I, J i * ∏ v ∈ S i, spin (cfgMul σ τ v))
      = exp (∑ i : I, dcoup S J J' τ i * ∏ v ∈ S i, spin (σ v)) := by
  rw [← Real.exp_add, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  simp only [dcoup]
  rw [prod_spin_cfgMul]
  ring

/-! ## 4. The inequality -/

/-- **THE UNNORMALISED FORM.** `N(J)·Z(J') ≤ N(J')·Z(J)`. -/
theorem num_mul_part_le (S : I → Finset V) (J J' : I → ℝ) (hJ : ∀ i, 0 ≤ J i)
    (hle : ∀ i, J i ≤ J' i) (A : Finset V) :
    num S J A * part S J' ≤ num S J' A * part S J := by
  rw [← sub_nonneg]
  have hA : num S J' A * part S J
      = ∑ τ : V → Bool, ∑ σ : V → Bool, (∏ v ∈ A, spin (σ v))
          * exp (∑ i : I, dcoup S J J' τ i * ∏ v ∈ S i, spin (σ v)) := by
    rw [Finset.sum_comm, num, part, Fintype.sum_mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← Equiv.sum_comp (cfgMulEquiv σ) fun σ' : V → Bool =>
      ((∏ v ∈ A, spin (σ v)) * exp (∑ i : I, J' i * ∏ v ∈ S i, spin (σ v)))
        * exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ' v))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [cfgMulEquiv_apply, mul_assoc, exp_mul_exp_cfgMul]
  have hB : num S J A * part S J'
      = ∑ τ : V → Bool, ∑ σ : V → Bool, (∏ v ∈ A, spin (σ v)) * (∏ v ∈ A, spin (τ v))
          * exp (∑ i : I, dcoup S J J' τ i * ∏ v ∈ S i, spin (σ v)) := by
    rw [Finset.sum_comm, num, part, Fintype.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← Equiv.sum_comp (cfgMulEquiv σ) fun σ' : V → Bool =>
      ((∏ v ∈ A, spin (σ' v)) * exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ' v)))
        * exp (∑ i : I, J' i * ∏ v ∈ S i, spin (σ v))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have h := exp_mul_exp_cfgMul S J J' σ τ
    rw [cfgMulEquiv_apply, prod_spin_cfgMul]
    linear_combination ((∏ v ∈ A, spin (σ v)) * ∏ v ∈ A, spin (τ v)) * h
  rw [hA, hB, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg fun τ _ => ?_
  rw [← Finset.sum_sub_distrib]
  have hfac : ∑ σ : V → Bool, ((∏ v ∈ A, spin (σ v))
        * exp (∑ i : I, dcoup S J J' τ i * ∏ v ∈ S i, spin (σ v))
      - (∏ v ∈ A, spin (σ v)) * (∏ v ∈ A, spin (τ v))
        * exp (∑ i : I, dcoup S J J' τ i * ∏ v ∈ S i, spin (σ v)))
      = (1 - ∏ v ∈ A, spin (τ v))
          * ∑ σ : V → Bool, (∏ v ∈ A, spin (σ v))
              * exp (∑ i : I, dcoup S J J' τ i * ∏ v ∈ S i, spin (σ v)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [hfac]
  refine mul_nonneg ?_ (griffiths_nonneg S _ (dcoup_nonneg S hJ hle τ) A)
  rcases prod_spin_eq_one_or A τ with h | h <;> rw [h] <;> norm_num

/-- **GRIFFITHS' SECOND INEQUALITY, IN THE FORM THIS ESTATE NEEDS: A FERROMAGNETIC CORRELATION IS
MONOTONE IN THE COUPLINGS.** If `0 ≤ J i ≤ J' i` at every interaction term, then
`⟨σ_A⟩_J ≤ ⟨σ_A⟩_{J'}` — turning couplings up never turns a correlation down. -/
theorem griffiths_expect_mono (S : I → Finset V) (J J' : I → ℝ) (hJ : ∀ i, 0 ≤ J i)
    (hle : ∀ i, J i ≤ J' i) (A : Finset V) :
    num S J A / part S J ≤ num S J' A / part S J' := by
  rw [div_le_div_iff₀ (part_pos S J) (part_pos S J')]
  exact num_mul_part_le S J J' hJ hle A

/-! ## 5. What this does not do -/

/-- The correlation at couplings `J` is at least the one at `0`, which is the shape the
magnetisation application wants: compare a coupled model against the same sites with every coupling
switched off. **`num S 0 A / part S 0` is not computed anywhere** — this file states the comparison
and nothing else. -/
theorem le_expect_of_nonneg (S : I → Finset V) (J : I → ℝ) (hJ : ∀ i, 0 ≤ J i) (A : Finset V) :
    num S 0 A / part S 0 ≤ num S J A / part S J :=
  griffiths_expect_mono S 0 J (fun _ => le_refl 0) hJ A

end

end IsingGriffithsMono
