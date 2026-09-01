/-
  IsingGriffiths.lean — Griffiths' first inequality, for an arbitrary finite Ising model with
  non-negative couplings.

  WHY. `IsingGKSParity` built two of the three ingredients and named the third — *"a sum over
  subsets of the bond set with a parity condition on the induced multiset"* — as the step nobody had
  attempted. **The parity condition never has to be computed.** That is the whole content of this
  file, and it is why the third rung is short.

  THE TRICK, STATED PLAINLY. The expansion produces, for each subset `T` of the interaction terms, a
  configuration sum of a product of spins over some collection of sites WITH REPETITION. Written as
  `∏ v, spin (σ v) ^ (multiplicity of v)` it factorises site by site — `Fintype.prod_sum` — and each
  factor is `∑_b spin b ^ n`, which is `2` for even `n` and `0` for odd. **Both are non-negative,
  so no case split on the parity is needed and the parity set is never constructed.** A first plan
  for this file built the odd-multiplicity set explicitly; it is not needed and is not here.

  WHAT IS PROVED.

  * `sum_pow_spin_nonneg` — `0 ≤ ∑_b spin b ^ n`, the whole parity argument in one line;
  * `prod_spin_eq_prod_pow` — a product of spins over a `Finset`, and any product of such, is
    `∏ v, spin (σ v) ^ c v` for the multiplicity `c`;
  * **`sum_prod_pow_spin_nonneg`** — hence every configuration sum of such a product is `≥ 0`;
  * **`griffiths_nonneg`** — for a finite family of interaction sets `S i` with non-negative
    couplings `J i`, and any observable set `A`,
    `0 ≤ ∑_σ (∏_{v ∈ A} spin (σ v)) · exp (∑_i J i · ∏_{v ∈ S i} spin (σ v))`.
    Bonds are `S i` of size two and a field is `S i` of size one, so **the hypothesis is exactly
    "ferromagnetic, with a field of the same sign as the observable"**;
  * `griffiths_expect_nonneg` — the same divided by the partition function, which is positive.

  WHAT THIS IS NOT. It is not yet a statement about the estate's slab. `energyG` is a sum over a
  path of configurations, and to apply the theorem above one must (i) reindex
  `Fin (M+1) → Cross V` as `(Fin (M+1) × V) → Bool`, and (ii) exhibit `β · energyG` as
  `∑_i J i · ∏_{v ∈ S i} spin` with every `J i ≥ 0` — the bonds along the length, the bonds inside a
  cross-section, and the field, each with coupling `β` or `β h`. **Neither step is attempted here
  and neither has been probed** (`ERRATUM 250`); naming them is not the same as costing them.

  ADDENDUM 2026-08-23 — BOTH PARAGRAPHS ABOVE ARE NOW OUT OF DATE, AND ARE KEPT (`ERRATUM 94`).

  * *"It is not yet a statement about the estate's slab … Neither step is attempted here."* Both
    steps were done the same day. `IsingSlabGriffiths.energy_eq` is (i) and (ii) together, and
    `IsingSlabFerro.slabIntraAniso_eq_intraOf` identifies the estate's own slab interaction as the
    `intraOf` parameter. The sentence was true when written and is recorded here, where the claim
    was made, and not only where the news was announced (`ERRATUM 226`).
  * *"`griffiths_nonneg` … `0 ≤ …`"*, and the whole file's `≥ 0` reading. **The same expansion gives
    `> 0`**, and it is now proved here: see `boltzmann_expansion`, `sum_pow_spin_pos`,
    `sum_prod_pow_spin_pos` and **`griffiths_pos`** below. The non-negativity theorems are unchanged
    and are still the right statement when no term sits on the observable's own set.

  WHAT THE STRICTNESS COST, STATED PLAINLY. Nothing new. The expansion that was a `have` inside
  `griffiths_nonneg` is now the named `boltzmann_expansion`, instantiated by both the non-negative
  and the positive theorem (`ERRATUM 201`); `sum_pow_spin_nonneg` computed `1 + (−1)^n` and threw
  the value away, and `sum_pow_spin_pos` is the same line keeping it. **The parity set is still
  never constructed**, in either direction.

  ADDENDUM 2026-08-23, SECOND — **THE STRICT INEQUALITY'S HYPOTHESIS WAS TOO STRONG AND IS NOW AT
  ITS ACTUAL SHAPE** (`PROOF_STRATEGY` §7 rule 3). `griffiths_pos` above asked that the observable
  set BE an interaction set, and its own docstring said nothing claimed that necessary. It was not.
  **`griffiths_pos_of_parity`**: a family `T` of interaction terms, all with strictly positive
  couplings, covering every site of `A` an ODD number of times and every other site an EVEN number,
  suffices — which is exactly `A = △_{i ∈ T} S i`, the classical condition. `griffiths_pos` is now
  the `|T| = 1` case and **`griffiths_pos_symmDiff`** is the `|T| = 2` one.

  **AND THE TWO-TERM CASE REACHES SOMETHING THE ONE-TERM CASE CANNOT: A CORRELATION WITH NO FIELD.**
  With `|T| = 1` the observable must be an interaction set, which for a two-point function means a
  bond — and a bond's own correlation. With `|T| = 2` the observable is a symmetric difference, so
  `{u, v}` for two sites joined by a path of bonds qualifies, and **no field term is involved at
  all**. Every strict-positivity result in this estate before today required `h > 0`; this one does
  not.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingGKSParity

namespace IsingGriffiths

open Finset Real
open IsingTransfer2D IsingGKSParity

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The parity argument, without the parity -/

/-- **`0 ≤ ∑_b spin b ^ n`.** It is `2` when `n` is even and `0` when `n` is odd, and the proof
needs neither case: `1 ^ n + (−1) ^ n` is `1 + (±1)`. -/
theorem sum_pow_spin_nonneg (n : ℕ) : 0 ≤ ∑ b : Bool, spin b ^ n := by
  have h : ∑ b : Bool, spin b ^ n = 1 + (-1 : ℝ) ^ n := by
    simp [spin]
  rw [h]
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow]; norm_num
  · rw [ho.neg_one_pow]; norm_num

/-- **AND IT IS `2` WHEN `n` IS EVEN.** The same one line, read for its value instead of its sign:
that is the entire difference between `≥ 0` and `> 0` in this file. -/
theorem sum_pow_spin_pos {n : ℕ} (hn : Even n) : 0 < ∑ b : Bool, spin b ^ n := by
  have h : ∑ b : Bool, spin b ^ n = 1 + (-1 : ℝ) ^ n := by
    simp [spin]
  rw [h, hn.neg_one_pow]
  norm_num

/-- **AND SO EVERY CONFIGURATION SUM OF A PRODUCT OF SPIN POWERS IS NON-NEGATIVE**, whatever the
multiplicities. This is the step that replaces the parity bookkeeping. -/
theorem sum_prod_pow_spin_nonneg (c : V → ℕ) :
    0 ≤ ∑ σ : V → Bool, ∏ v : V, spin (σ v) ^ c v := by
  rw [← Fintype.prod_sum fun (v : V) (b : Bool) => spin b ^ c v]
  exact Finset.prod_nonneg fun v _ => sum_pow_spin_nonneg (c v)

/-- **AND STRICTLY POSITIVE WHEN EVERY MULTIPLICITY IS EVEN** — the value is `2 ^ card V`, but only
its sign is needed and only its sign is taken. -/
theorem sum_prod_pow_spin_pos {c : V → ℕ} (hc : ∀ v, Even (c v)) :
    0 < ∑ σ : V → Bool, ∏ v : V, spin (σ v) ^ c v := by
  rw [← Fintype.prod_sum fun (v : V) (b : Bool) => spin b ^ c v]
  exact Finset.prod_pos fun v _ => sum_pow_spin_pos (hc v)

/-! ## 2. Products of spins as products of powers -/

/-- A product over a `Finset` is a product over everything with exponents `0` and `1`. -/
theorem prod_finset_eq_prod_pow (A : Finset V) (σ : V → Bool) :
    ∏ v ∈ A, spin (σ v) = ∏ v : V, spin (σ v) ^ (if v ∈ A then 1 else 0) := by
  have h : ∀ v : V, spin (σ v) ^ (if v ∈ A then 1 else 0)
      = if v ∈ A then spin (σ v) else 1 := by
    intro v
    by_cases hv : v ∈ A <;> simp [hv]
  rw [Finset.prod_congr rfl fun v _ => h v, Finset.prod_ite_mem, Finset.univ_inter]

/-- And a product of such collapses onto the summed exponents. -/
theorem prod_prod_eq_prod_pow {I : Type*} (T : Finset I) (S : I → Finset V)
    (σ : V → Bool) :
    ∏ i ∈ T, ∏ v ∈ S i, spin (σ v)
      = ∏ v : V, spin (σ v) ^ (∑ i ∈ T, if v ∈ S i then 1 else 0) := by
  rw [Finset.prod_congr rfl fun i _ => prod_finset_eq_prod_pow (S i) σ, Finset.prod_comm]
  exact Finset.prod_congr rfl fun v _ => Finset.prod_pow_eq_pow_sum T _ _

/-! ## 3. Each Boltzmann factor -/

omit [Fintype V] [DecidableEq V] in
theorem prod_spin_eq_one_or (A : Finset V) (σ : V → Bool) :
    ∏ v ∈ A, spin (σ v) = 1 ∨ ∏ v ∈ A, spin (σ v) = -1 := by
  classical
  induction A using Finset.induction with
  | empty => left; simp
  | insert a A ha ih =>
      rw [Finset.prod_insert ha]
      rcases spin_eq_one_or (σ a) with h | h <;> rcases ih with h2 | h2 <;>
        rw [h, h2] <;> norm_num

omit [Fintype V] [DecidableEq V] in
theorem exp_term (x : ℝ) (A : Finset V) (σ : V → Bool) :
    exp (x * ∏ v ∈ A, spin (σ v))
      = cosh x + (∏ v ∈ A, spin (σ v)) * sinh x :=
  exp_mul_of_abs_one (prod_spin_eq_one_or A σ) x

/-! ## 4. `sinh` is non-negative on the non-negative reals

`Real.sinh_nonneg_iff` did not resolve in this file's import closure, and pulling in the
differentiation file to reach it would import a great deal for one sign. Four lines from
`Real.sinh_eq` instead. -/

theorem sinh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ sinh x := by
  rw [Real.sinh_eq]
  have h : exp (-x) ≤ exp x := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- And strictly positive on the strictly positive reals. `Real.sinh_pos_of_pos` lives in the same
differentiation file `sinh_nonneg` avoided, so this is the same four lines with a strict inequality
rather than a new import.

**^ THAT NAME DOES NOT EXIST AND IS KEPT** (`ERRATUM 94`, `ERRATUM 402`), corrected 1 Sep 2026.
Probed against the pinned constant dump: Mathlib carries `Real.sinh_pos_iff` and
`Real.sinh_nonneg_iff` — **biconditionals** — in the `Real` namespace, and
`Mathlib.Meta.Positivity.sinh_pos_of_pos` in the **positivity-extension** namespace, which is not
`Real`. The sentence above took the `_of_pos` suffix from the second and the `Real` prefix from
the first. **The claim it supports is unaffected**: an import is still what this theorem avoids,
and `Real.sinh_pos_iff` is a real name in a file this one does not import — which is exactly what
the line two theorems above says about `Real.sinh_nonneg_iff`, correctly.
**IT SURVIVED BECAUSE THIS FILE DECLARES A BARE `sinh_pos_of_pos` ITSELF**: `--cites-lean` used to
resolve a qualified citation against any bare estate name, so the estate's own theorem is what hid
the wrong prefix on the Mathlib one. That clause is narrowed as of today. -/
theorem sinh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < sinh x := by
  rw [Real.sinh_eq]
  have h : exp (-x) < exp x := Real.exp_lt_exp.mpr (by linarith)
  linarith

/-! ## 5. Griffiths' first inequality -/

variable {I : Type*} [Fintype I]

/-- **THE EXPANSION, ONCE AND BY NAME.** Each Boltzmann factor is
`cosh (J i) + (∏ spin) · sinh (J i)` because `∏ spin` is `±1`; the product over the interaction
terms expands over subsets `T` (`Finset.prod_add`); and each `T`-term's spins collapse onto
multiplicities. The exponent of
`spin (σ v)` in the `T`-term is `[v ∈ A] + #{i ∈ T : v ∈ S i}` — the observable's own set counted
once, each chosen interaction set counted once.

**This identity carries both signs of the file.** `griffiths_nonneg` reads it as *every term is
`≥ 0`*; `griffiths_pos` reads it as *one named term is `> 0`*. It was a `have` inside the first of
those until 2026-08-23, which is why the second could not be attempted without repeating it.

`DecidableEq I` is on the STATEMENT here and not on `griffiths_nonneg`/`griffiths_pos`, which reach
it through `classical`: `Finset.univ \ T` needs the instance and the old `have` got it for free from
the enclosing proof, which is the one thing hoisting the identity actually cost. -/
theorem boltzmann_expansion [DecidableEq I] (S : I → Finset V) (J : I → ℝ) (A : Finset V)
    (σ : V → Bool) :
    (∏ v ∈ A, spin (σ v)) * exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v))
      = ∑ T ∈ Finset.univ.powerset,
          ((∏ i ∈ T, sinh (J i)) * ∏ i ∈ Finset.univ \ T, cosh (J i))
            * ∏ v : V, spin (σ v)
                ^ ((if v ∈ A then 1 else 0) + ∑ i ∈ T, if v ∈ S i then 1 else 0) := by
  classical
  rw [Real.exp_sum,
    Finset.prod_congr rfl fun i _ => (exp_term (J i) (S i) σ).trans (add_comm _ _),
    Finset.prod_add (fun i => (∏ v ∈ S i, spin (σ v)) * sinh (J i)) (fun i => cosh (J i))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_mul_distrib, prod_prod_eq_prod_pow T S σ, prod_finset_eq_prod_pow A σ]
  have hcomb : (∏ v : V, spin (σ v) ^ (if v ∈ A then 1 else 0))
      * ∏ v : V, spin (σ v) ^ (∑ i ∈ T, if v ∈ S i then 1 else 0)
      = ∏ v : V, spin (σ v)
          ^ ((if v ∈ A then 1 else 0) + ∑ i ∈ T, if v ∈ S i then 1 else 0) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => (pow_add _ _ _).symm
  rw [← hcomb]
  ring

/-- Every term of the expansion has a non-negative coefficient when the couplings are, and a
non-negative configuration sum whatever they are. Both halves of `griffiths_nonneg`, and the
non-negative half of `griffiths_pos`, are this lemma. -/
theorem expansion_term_nonneg [DecidableEq I] (S : I → Finset V) (J : I → ℝ) (hJ : ∀ i, 0 ≤ J i)
    (A : Finset V) (T : Finset I) :
    0 ≤ ∑ σ : V → Bool,
      ((∏ i ∈ T, sinh (J i)) * ∏ i ∈ Finset.univ \ T, cosh (J i))
        * ∏ v : V, spin (σ v)
            ^ ((if v ∈ A then 1 else 0) + ∑ i ∈ T, if v ∈ S i then 1 else 0) := by
  rw [← Finset.mul_sum]
  refine mul_nonneg (mul_nonneg ?_ ?_) (sum_prod_pow_spin_nonneg _)
  · exact Finset.prod_nonneg fun i _ => sinh_nonneg (hJ i)
  · exact Finset.prod_nonneg fun i _ => (Real.cosh_pos _).le

/-- **GRIFFITHS' FIRST INEQUALITY.** For any finite family of interaction sets with non-negative
couplings and any observable set, the unnormalised correlation is non-negative. Bonds are sets of
size two and a field is a set of size one, so the hypothesis `0 ≤ J i` is exactly *ferromagnetic,
with a field of the same sign as the observable*. -/
theorem griffiths_nonneg (S : I → Finset V) (J : I → ℝ) (hJ : ∀ i, 0 ≤ J i) (A : Finset V) :
    0 ≤ ∑ σ : V → Bool, (∏ v ∈ A, spin (σ v))
        * exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v)) := by
  classical
  rw [Finset.sum_congr rfl fun σ _ => boltzmann_expansion S J A σ, Finset.sum_comm]
  exact Finset.sum_nonneg fun T _ => expansion_term_nonneg S J hJ A T

/-- **THE MAGNETISATION CASE**, which is the one the watchlist item is about: `A = {v₀}`. -/
theorem griffiths_site_nonneg (S : I → Finset V) (J : I → ℝ) (hJ : ∀ i, 0 ≤ J i) (v₀ : V) :
    0 ≤ ∑ σ : V → Bool, spin (σ v₀) * exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v)) := by
  have h := griffiths_nonneg S J hJ {v₀}
  simpa using h

/-- **THE STRICT INEQUALITY, AT ITS ACTUAL HYPOTHESIS.** If some family `T` of interaction terms,
all with strictly positive couplings, covers every site of the observable set `A` an ODD number of
times and every other site an EVEN number, then the unnormalised correlation is strictly positive.

**THAT PARITY CONDITION IS EXACTLY `A = △_{i ∈ T} S i`**, the symmetric difference of the chosen
interaction sets — a sum of indicators is even precisely when the indicators agree mod 2 — and it is
the classical condition under which a ferromagnetic correlation is known to be positive. Every term
of `boltzmann_expansion` is `≥ 0` by `expansion_term_nonneg`; the `T` term is `> 0`;
`Finset.sum_pos'` is the whole difference.

**WHY THIS IS STATED AND NOT JUST `S i₀ = A`.** The `|T| = 1` case (`griffiths_pos` below) needs the
observable to BE an interaction set, which is the magnetisation case and little else. With `|T| > 1`
the observable can be a symmetric difference — `{u, v}` for two sites joined by a PATH of bonds, for
instance — and that is a two-point function rather than a one-point one. The earlier docstring said
of the `S i₀ = A` hypothesis that nothing claimed it necessary; this is what it was hiding. -/
theorem griffiths_pos_of_parity (S : I → Finset V) (J : I → ℝ) (hJ : ∀ i, 0 ≤ J i) (A : Finset V)
    (T : Finset I) (hT : ∀ i ∈ T, 0 < J i)
    (hpar : ∀ v : V, Even ((if v ∈ A then 1 else 0) + ∑ i ∈ T, if v ∈ S i then 1 else 0)) :
    0 < ∑ σ : V → Bool, (∏ v ∈ A, spin (σ v))
        * exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v)) := by
  classical
  rw [Finset.sum_congr rfl fun σ _ => boltzmann_expansion S J A σ, Finset.sum_comm]
  refine Finset.sum_pos' (fun T' _ => expansion_term_nonneg S J hJ A T')
    ⟨T, Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
  rw [← Finset.mul_sum]
  refine mul_pos (mul_pos ?_ ?_) (sum_prod_pow_spin_pos hpar)
  · exact Finset.prod_pos fun i hi => sinh_pos_of_pos (hT i hi)
  · exact Finset.prod_pos fun i _ => Real.cosh_pos _

/-- **THE ONE-TERM CASE**: the model carries the observable's own set with a strictly positive
coupling. For `A = {v₀}` this reads *a ferromagnetic model with a strictly positive field at `v₀`
has strictly positive magnetisation at `v₀`* — `griffiths_site_pos`. -/
theorem griffiths_pos (S : I → Finset V) (J : I → ℝ) (hJ : ∀ i, 0 ≤ J i) (A : Finset V)
    (i₀ : I) (hS : S i₀ = A) (hJ₀ : 0 < J i₀) :
    0 < ∑ σ : V → Bool, (∏ v ∈ A, spin (σ v))
        * exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v)) := by
  classical
  refine griffiths_pos_of_parity S J hJ A {i₀} (fun i hi => ?_) fun v => ?_
  · rw [Finset.mem_singleton] at hi
    exact hi ▸ hJ₀
  · rw [Finset.sum_singleton, hS]
    exact Even.add_self _

/-- **THE TWO-TERM CASE, WHICH IS THE ONE THE ONE-TERM CASE CANNOT REACH.** If two interaction sets
have strictly positive couplings, their symmetric difference is a strictly positive correlation.
`Finset.mem_symmDiff` is what turns the set condition into the parity one. -/
theorem griffiths_pos_symmDiff (S : I → Finset V) (J : I → ℝ) (hJ : ∀ i, 0 ≤ J i)
    (i₁ i₂ : I) (hne : i₁ ≠ i₂) (h₁ : 0 < J i₁) (h₂ : 0 < J i₂) :
    0 < ∑ σ : V → Bool, (∏ v ∈ symmDiff (S i₁) (S i₂), spin (σ v))
        * exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v)) := by
  classical
  refine griffiths_pos_of_parity S J hJ _ {i₁, i₂} (fun i hi => ?_) fun v => ?_
  · rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact h₁
    · rw [Finset.mem_singleton] at hi'
      exact hi' ▸ h₂
  · rw [Finset.sum_pair hne]
    by_cases hv₁ : v ∈ S i₁ <;> by_cases hv₂ : v ∈ S i₂ <;>
      simp [Finset.mem_symmDiff, hv₁, hv₂]

/-- **THE MAGNETISATION CASE OF THE STRICT INEQUALITY**, which is what the watchlist item asks for:
a strictly positive field at `v₀` is an interaction set `{v₀}` with a strictly positive coupling. -/
theorem griffiths_site_pos (S : I → Finset V) (J : I → ℝ) (hJ : ∀ i, 0 ≤ J i) (v₀ : V)
    (i₀ : I) (hS : S i₀ = {v₀}) (hJ₀ : 0 < J i₀) :
    0 < ∑ σ : V → Bool, spin (σ v₀) * exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v)) := by
  have h := griffiths_pos S J hJ {v₀} i₀ hS hJ₀
  simpa using h

/-- The partition function of such a model is positive, so the normalised correlation is
non-negative too. -/
theorem griffiths_expect_nonneg (S : I → Finset V) (J : I → ℝ) (hJ : ∀ i, 0 ≤ J i)
    (A : Finset V) :
    0 ≤ (∑ σ : V → Bool, (∏ v ∈ A, spin (σ v))
          * exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v)))
        / ∑ σ : V → Bool, exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v)) := by
  refine div_nonneg (griffiths_nonneg S J hJ A) ?_
  exact Finset.sum_nonneg fun σ _ => (exp_pos _).le

/-- And strictly positive, under the hypothesis of `griffiths_pos`: the partition function is a
finite sum of exponentials over a nonempty configuration space, hence positive. -/
theorem griffiths_expect_pos (S : I → Finset V) (J : I → ℝ) (hJ : ∀ i, 0 ≤ J i)
    (A : Finset V) (i₀ : I) (hS : S i₀ = A) (hJ₀ : 0 < J i₀) :
    0 < (∑ σ : V → Bool, (∏ v ∈ A, spin (σ v))
          * exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v)))
        / ∑ σ : V → Bool, exp (∑ i : I, J i * ∏ v ∈ S i, spin (σ v)) := by
  refine div_pos (griffiths_pos S J hJ A i₀ hS hJ₀) ?_
  exact Finset.sum_pos (fun σ _ => exp_pos _) ⟨fun _ => true, Finset.mem_univ _⟩

end

end IsingGriffiths
