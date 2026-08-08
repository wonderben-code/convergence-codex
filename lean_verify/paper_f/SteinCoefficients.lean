/-
  SteinCoefficients.lean — the Stein class, characterised by coefficients,
  and the derivative it names proved unique.

  WHY. `UNLOCK_WATCHLIST`'s W^{1,2}(γ) item ends with a warning and a task.
  The warning: *"defining the class BY the coefficients and then proving
  Poincaré for it would be circular-adjacent — say so if done."* The task:
  *"the real work is proving that characterisation equivalent to any
  external definition of the Sobolev space."*

  **The estate already owns an external definition.** `PoincareSteinClass`
  defines the Stein class by an INTEGRAL PAIRING — Gaussian integration by
  parts against every polynomial — and the item's own staircase text says
  why that is not circular: *"This is an IBP condition, not a coefficient
  condition."* So the equivalence the item calls "the real work" is
  provable, and provable in the honest direction: **a class defined by
  pairing, characterised by coefficients**, not the other way round.

  WHAT THIS FILE PROVES:
  1. **`mem_span_hermite`** — the Hermite polynomials span `ℝ[X]`. Absent
     from the estate and needed by everything below: `{Hₙ}` is monic of
     each degree, so subtracting the leading term and inducting on degree
     does it.
  2. **`steinPair_of_coeff`** — the CONVERSE of `coeff_steinPair`: if
     `f, g ∈ L²(γ)` and `cₙ(g) = (n+1)·cₙ₊₁(f)` for every `n`, then
     `(f,g)` is a Stein pair. Hence **`steinPair_iff_coeff`**, the
     characterisation. The pairing at `q = Hₙ` IS the recursion, in both
     directions; §2 supplies the linearity that carries it from the `Hₙ`
     to every polynomial.
  3. **`steinPartner_unique`** — and therefore the Stein derivative is
     WELL-DEFINED. `PoincareSteinClass` has called `g` "the derivative of
     f in the Gaussian-IBP sense" since it was written and **never proved
     that `f` determines it.** It does: two partners have the same
     coefficients, so their difference has zero L² norm.
  4. **`summable_sobolev_of_steinPair`** — the Sobolev-type summability
     `Σ (n+1)·n!·cₙ(f)² < ∞` as a NECESSARY condition for `f` to have a
     Stein partner. That is the coefficient characterisation of
     `W^{1,2}(γ)` the watchlist names, proved for a class defined without
     reference to coefficients.

  WHAT THIS DOES NOT DO. **The converse of item 4 is not proved.** Going
  from `Σ (n+1)·n!·cₙ(f)² < ∞` back to the EXISTENCE of a partner `g`
  needs Riesz–Fischer for a prescribed Hermite coefficient sequence — the
  estate has the Cauchy/limit machinery only for a function's own
  expansion. §6 states the missing ingredient exactly and names the route.
  And nothing here touches the Cc^∞ comparison (W6): that is a different
  question, still open, still unclaimed.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import PoincareSteinClass

namespace SteinCoefficients

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness HermiteBessel HermiteParseval
open PoincareSteinClass

noncomputable section

/-! ## 1. The Hermite polynomials span `ℝ[X]`

Needed because the Stein class is defined by a pairing against EVERY
polynomial while the coefficient recursion only sees the `Hₙ`. Monic of
each degree, so the standard subtract-the-leading-term induction applies;
the estate did not have this and Mathlib states it for neither family.
-/

theorem H_natDegree (n : ℕ) : (H n).natDegree = n := by
  rw [H, Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _)]
  exact Polynomial.natDegree_hermite

theorem H_degree (n : ℕ) : (H n).degree = (n : WithBot ℕ) := by
  rw [Polynomial.degree_eq_natDegree (H_ne_zero n), H_natDegree]

theorem mem_span_hermite_aux : ∀ (N : ℕ) (p : ℝ[X]), p.natDegree < N →
    p ∈ Submodule.span ℝ (Set.range H) := by
  intro N
  induction N with
  | zero => intro p hp; omega
  | succ N ih =>
    intro p hp
    by_cases hp0 : p = 0
    · rw [hp0]; exact Submodule.zero_mem _
    by_cases hdeg : p.natDegree < N
    · exact ih p hdeg
    have hd : p.natDegree = N := by omega
    set c := p.leadingCoeff with hc
    have hcne : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hp0
    have hsm : c • H N = Polynomial.C c * H N := (Polynomial.smul_eq_C_mul c).symm ▸ rfl
    have hdegp : p.degree = (N : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hp0, hd]
    have hdegcH : (c • H N).degree = (N : WithBot ℕ) := by
      rw [hsm, Polynomial.degree_C_mul hcne, H_degree]
    have hlead : (c • H N).leadingCoeff = c := by
      rw [hsm, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        (H_monic N).leadingCoeff, mul_one]
    have hsub : (p - c • H N).degree < (N : WithBot ℕ) := by
      have := Polynomial.degree_sub_lt (hdegp.trans hdegcH.symm) hp0 hlead.symm
      rwa [hdegp] at this
    have hmem : (p - c • H N) ∈ Submodule.span ℝ (Set.range H) := by
      by_cases hz : p - c • H N = 0
      · rw [hz]; exact Submodule.zero_mem _
      · exact ih _ ((Polynomial.natDegree_lt_iff_degree_lt hz).2 hsub)
    have hsplit : p = (p - c • H N) + c • H N := by ring
    rw [hsplit]
    exact Submodule.add_mem _ hmem
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨N, rfl⟩))

/-- **Every real polynomial is a finite combination of Hermite
    polynomials.** -/
theorem mem_span_hermite (p : ℝ[X]) : p ∈ Submodule.span ℝ (Set.range H) :=
  mem_span_hermite_aux (p.natDegree + 1) p (Nat.lt_succ_self _)

/-! ## 2. The pairing is linear in the test polynomial

`Agree f g q` is the Stein condition at the single test polynomial `q`.
Both sides are `ℝ`-linear in `q`, so §3 can check it on the `Hₙ` and
transport along §1.
-/

/-- The Stein pairing condition at a single test polynomial. -/
def Agree (f g : ℝ → ℝ) (p : ℝ[X]) : Prop :=
  ∫ x, g x * p.eval x ∂gauss = ∫ x, f x * (X * p - derivative p).eval x ∂gauss

theorem agree_zero {f g : ℝ → ℝ} : Agree f g 0 := by
  simp [Agree]

theorem agree_add {f g : ℝ → ℝ} (hf : MemLp f 2 gauss) (hg : MemLp g 2 gauss)
    (p q : ℝ[X]) (hp : Agree f g p) (hq : Agree f g q) : Agree f g (p + q) := by
  have hL : ∫ x, g x * (p + q).eval x ∂gauss
      = (∫ x, g x * p.eval x ∂gauss) + ∫ x, g x * q.eval x ∂gauss := by
    rw [← integral_add (integrable_f_mul_poly g hg p) (integrable_f_mul_poly g hg q)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Polynomial.eval_add]; ring
  have hsplit : X * (p + q) - derivative (p + q)
      = (X * p - derivative p) + (X * q - derivative q) := by
    rw [mul_add, derivative_add]; ring
  have hR : ∫ x, f x * (X * (p + q) - derivative (p + q)).eval x ∂gauss
      = (∫ x, f x * (X * p - derivative p).eval x ∂gauss)
        + ∫ x, f x * (X * q - derivative q).eval x ∂gauss := by
    rw [hsplit, ← integral_add (integrable_f_mul_poly f hf _)
      (integrable_f_mul_poly f hf _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Polynomial.eval_add]; ring
  rw [Agree, hL, hR, hp, hq]

theorem agree_smul {f g : ℝ → ℝ} (a : ℝ) (p : ℝ[X]) (hp : Agree f g p) :
    Agree f g (a • p) := by
  have hL : ∫ x, g x * (a • p).eval x ∂gauss = a * ∫ x, g x * p.eval x ∂gauss := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Polynomial.eval_smul, smul_eq_mul]; ring
  have hsplit : X * (a • p) - derivative (a • p) = a • (X * p - derivative p) := by
    rw [derivative_smul, Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul,
      Polynomial.smul_eq_C_mul]
    ring
  have hR : ∫ x, f x * (X * (a • p) - derivative (a • p)).eval x ∂gauss
      = a * ∫ x, f x * (X * p - derivative p).eval x ∂gauss := by
    rw [hsplit, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Polynomial.eval_smul, smul_eq_mul]; ring
  rw [Agree, hL, hR, hp]

/-! ## 3. The characterisation

`coeff_steinPair` was one direction. Here is the other, and with it the
biconditional: **the Stein class is exactly the coefficient recursion**,
for a class defined by pairing.
-/

/-- The pairing at `q = Hₙ` IS the recursion. -/
theorem agree_H_of_coeff {f g : ℝ → ℝ}
    (hrec : ∀ n : ℕ, coeff n g = (n + 1 : ℝ) * coeff (n + 1) f) (n : ℕ) :
    Agree f g (H n) := by
  rw [Agree, ← H_succ n, integral_mul_H, integral_mul_H, hrec n, Nat.factorial_succ]
  push_cast
  ring

/-- **The converse of `coeff_steinPair`.** -/
theorem steinPair_of_coeff {f g : ℝ → ℝ} (hf : MemLp f 2 gauss)
    (hg : MemLp g 2 gauss)
    (hrec : ∀ n : ℕ, coeff n g = (n + 1 : ℝ) * coeff (n + 1) f) :
    SteinPair f g := by
  refine ⟨hf, hg, fun q => ?_⟩
  have key : ∀ p ∈ Submodule.span ℝ (Set.range H), Agree f g p := by
    intro p hp
    refine Submodule.span_induction ?_ agree_zero ?_ ?_ hp
    · rintro x ⟨n, rfl⟩
      exact agree_H_of_coeff hrec n
    · intro x y _ _ hx hy
      exact agree_add hf hg x y hx hy
    · intro a x _ hx
      exact agree_smul a x hx
  exact key q (mem_span_hermite q)

/-- **THE CHARACTERISATION.** For square-integrable `f, g`, the Stein
    pairing holds if and only if the Hermite coefficients satisfy the
    recursion. The class is defined by an integral condition; the
    coefficient condition is a theorem about it, in both directions. -/
theorem steinPair_iff_coeff {f g : ℝ → ℝ} (hf : MemLp f 2 gauss)
    (hg : MemLp g 2 gauss) :
    SteinPair f g ↔ ∀ n : ℕ, coeff n g = (n + 1 : ℝ) * coeff (n + 1) f :=
  ⟨fun h n => coeff_steinPair h n, steinPair_of_coeff hf hg⟩

/-! ## 4. The Stein derivative is well-defined

`PoincareSteinClass` calls `g` "the derivative of `f` in the Gaussian-IBP
sense" and has done since it was written. **That phrase presupposes that
`f` determines `g`, and nothing proved it.** It does: two partners share
every coefficient, so their difference has zero norm.
-/

theorem coeff_sub {f g : ℝ → ℝ} (hf : MemLp f 2 gauss) (hg : MemLp g 2 gauss)
    (n : ℕ) : coeff n (f - g) = coeff n f - coeff n g := by
  simp only [HermiteBessel.coeff]
  rw [← sub_div]
  congr 1
  rw [← integral_sub (integrable_f_mul_poly f hf (H n))
    (integrable_f_mul_poly g hg (H n))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply]
  ring

/-- **The Stein partner is unique in L².** -/
theorem steinPartner_unique {f g₁ g₂ : ℝ → ℝ} (h₁ : SteinPair f g₁)
    (h₂ : SteinPair f g₂) : ∫ x, (g₁ x - g₂ x) ^ 2 ∂gauss = 0 := by
  have hcoeff : ∀ n : ℕ, coeff n (g₁ - g₂) = 0 := by
    intro n
    rw [coeff_sub h₁.2.1 h₂.2.1, coeff_steinPair h₁ n, coeff_steinPair h₂ n, sub_self]
  have hmem : MemLp (g₁ - g₂) 2 gauss := h₁.2.1.sub h₂.2.1
  have hp := parseval (g₁ - g₂) hmem
  have hzero : (fun n : ℕ => (n.factorial : ℝ) * coeff n (g₁ - g₂) ^ 2) = fun _ => 0 := by
    funext n
    rw [hcoeff n]
    ring
  rw [hzero] at hp
  have := hp.tsum_eq
  rw [tsum_zero] at this
  have hrw : ∫ x, (g₁ - g₂) x ^ 2 ∂gauss = ∫ x, (g₁ x - g₂ x) ^ 2 ∂gauss := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
  rw [hrw] at this
  exact this.symm

/-- The same statement as an almost-everywhere equality, which is what
    "the derivative is well-defined" means in L². -/
theorem steinPartner_ae_eq {f g₁ g₂ : ℝ → ℝ} (h₁ : SteinPair f g₁)
    (h₂ : SteinPair f g₂) : g₁ =ᵐ[gauss] g₂ := by
  have hmem : MemLp (g₁ - g₂) 2 gauss := h₁.2.1.sub h₂.2.1
  have hint : Integrable (fun x => (g₁ x - g₂ x) ^ 2) gauss := by
    have := HermiteBessel.integrable_sq (g₁ - g₂) hmem
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
  have hzero := steinPartner_unique h₁ h₂
  have hnn : 0 ≤ᵐ[gauss] fun x => (g₁ x - g₂ x) ^ 2 :=
    Filter.Eventually.of_forall fun x => sq_nonneg _
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 hzero
  filter_upwards [hae] with x hx
  have : (g₁ x - g₂ x) ^ 2 = 0 := hx
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  linarith [this]

/-! ## 5. The Sobolev summability

`Σ (n+1)·n!·cₙ(f)² < ∞` is exactly the coefficient characterisation of
`W^{1,2}(γ)` the watchlist names, and it is NECESSARY for `f` to have a
Stein partner. Proved for a class defined without reference to
coefficients, which is what makes it a characterisation rather than a
tautology.
-/

/-- **Having a Stein partner forces the Sobolev-type summability.** -/
theorem summable_sobolev_of_steinPair {f g : ℝ → ℝ} (h : SteinPair f g) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * (n.factorial : ℝ) * coeff n f ^ 2) := by
  have hgs := summable_coeff_sq g h.2.1
  have hfs := summable_coeff_sq f h.1
  have hrew : (fun n : ℕ => (n.factorial : ℝ) * coeff n g ^ 2)
      = fun n : ℕ => ((n + 1 : ℝ) * ((n + 1).factorial : ℝ) * coeff (n + 1) f ^ 2) := by
    funext n
    rw [coeff_steinPair h n, Nat.factorial_succ]
    push_cast
    ring
  rw [hrew] at hgs
  have hshift : Summable (fun m : ℕ => (m : ℝ) * (m.factorial : ℝ) * coeff m f ^ 2) := by
    rw [← summable_nat_add_iff 1]
    convert hgs using 2 with n
    push_cast
    ring
  have hsum := hfs.add hshift
  convert hsum using 2 with n
  ring

/-- Stated in the shape a Sobolev norm has: the `f`-part and the
    `g`-part of the summability, separately. -/
theorem summable_of_steinPair_parts {f g : ℝ → ℝ} (h : SteinPair f g) :
    Summable (fun n : ℕ => (n.factorial : ℝ) * coeff n f ^ 2)
      ∧ Summable (fun n : ℕ => (n.factorial : ℝ) * coeff n g ^ 2) :=
  ⟨summable_coeff_sq f h.1, summable_coeff_sq g h.2.1⟩

/-! ## 6. What is missing, exactly

**The converse of §5 is not proved.** From `Σ (n+1)·n!·cₙ(f)² < ∞` one
wants a partner `g`, and the candidate is forced: its coefficients must be
`aₙ = (n+1)·cₙ₊₁(f)`, and the hypothesis says exactly that
`Σ n!·aₙ² < ∞`, so the sequence is admissible. **What is missing is
Riesz–Fischer for a PRESCRIBED coefficient sequence** — the estate's
`HermiteParseval` builds the L² limit of the partial sums of a function's
OWN expansion (`cauchySeq_SL`, `tendsto_SN_L2`) and nothing constructs a
function from coefficients given in advance.

The route, named so it can be attempted rather than rediscovered: the
partial sums `∑_{n<N} aₙ Hₙ` are Cauchy in `L²(γ)` by the same
orthogonality computation as `norm_SL_sub_sq`, `Lp` is complete, and the
limit's coefficients are `aₙ` by continuity of the pairing. **A cleaner
route that would give this and much else: bundle `Hₙ/√(n!)` as a Mathlib
`HilbertBasis` of `L²(γ)`** — the estate has completeness
(`HermiteCompleteness`) and orthogonality already, so the missing piece is
the packaging, and `HilbertBasis.repr.symm` then supplies Riesz–Fischer
for free.

**And nothing here touches W6.** Whether the Stein class coincides with
the Cc^∞-defined `W^{1,2}(γ)` is a different question, still open, still
unclaimed; §5 characterises the Stein class, not the textbook space.
-/

/-! ## 7. The objection this file invites, answered

**"You have now shown the Stein class IS the coefficient class. So
proving Poincaré for it is proving it for a coefficient-defined class —
exactly what the watchlist warned was circular-adjacent."**

That objection is worth stating because it is the first thing a careful
reader will think, and it is wrong for a reason worth being precise
about.

The warning was against *choosing the definition to make the theorem
easy*: define the class by `Σ(1+n)·n!·cₙ² < ∞`, then prove Poincaré by
Parseval, and one has proved nothing about any pre-existing object.
**What this file does is the opposite direction.** The definition was
fixed first, by an integral pairing, for reasons having nothing to do
with Parseval; the coefficient description is a THEOREM about it. A
theorem that an independently-defined class admits a coefficient
description is what makes the class recognisable — it is the content of
every Sobolev-space characterisation in analysis.

Two facts keep that answer honest rather than rhetorical. **`poincare_stein`
does not use anything in this file** — it rests on `coeff_steinPair`, the
forward direction, which predates it; nothing here was needed to prove
the inequality and nothing here strengthens it. And the class contains a
large family described without any reference to coefficients or to
Parseval — every everywhere-differentiable `f` of polynomial growth,
`steinPair_of_polyGrowth` — so it is not an artefact of the description.
§8's `polyGrowth_in_class` restates that as the witness for this
paragraph.
-/

/-! ## 8. Review round 37 — that the characterisation is not empty

Three ways this file could be true and say nothing.

* If the Hermite polynomials did not span, §3's transport would be
  vacuous and `steinPair_of_coeff` would prove the pairing only at the
  `Hₙ`. They span, and §1 proves it.
* If no `f` had a Stein partner, §§3–5 would be about an empty class.
  `steinPair_id_one` is a witness, and §5's summability is checked
  against it.
* If the recursion were satisfiable only trivially, the characterisation
  would be a disguised triviality. It is not: at `(X, 1)` the
  coefficients are `c₁(f) = 1` and `c₀(g) = 1`, and the recursion relates
  two different indices nontrivially.
-/

/-- The class is nonempty and §5 applies to it. -/
theorem sobolev_summable_id :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * (n.factorial : ℝ)
      * coeff n (fun x => x) ^ 2) :=
  summable_sobolev_of_steinPair steinPair_id_one

/-- **§1 is load-bearing**: the span is what lets §3 conclude the pairing
    at an arbitrary polynomial. `X ^ 3` is not a Hermite polynomial, and
    it is in the span. -/
theorem cube_mem_span : (X ^ 3 : ℝ[X]) ∈ Submodule.span ℝ (Set.range H) :=
  mem_span_hermite _

/-- **The characterisation is a biconditional with content in both
    directions**, exhibited at the witness pair: the recursion holds, and
    the pairing holds, and §3 derives each from the other. -/
theorem coeff_recursion_id (n : ℕ) :
    coeff n (fun _ : ℝ => (1 : ℝ)) = (n + 1 : ℝ) * coeff (n + 1) (fun x : ℝ => x) :=
  coeff_steinPair steinPair_id_one n

/-- **Uniqueness is not vacuous**: the witness pair has a partner, so
    §4 says something about an inhabited situation. -/
theorem partner_unique_at_id {g : ℝ → ℝ} (h : SteinPair (fun x => x) g) :
    g =ᵐ[gauss] fun _ => 1 :=
  steinPartner_ae_eq h steinPair_id_one

/-- **§7's witness: the class is not an artefact of its coefficient
    description.** It contains every everywhere-differentiable function
    of polynomial growth, a family described with no reference to
    coefficients, to Parseval, or to Hermite anything. -/
theorem polyGrowth_in_class {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x) {C : ℝ} {m : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + x ^ 2) ^ m)
    (hb' : ∀ x, |f' x| ≤ C * (1 + x ^ 2) ^ m) :
    SteinPair f f' ∧ (∀ n : ℕ, coeff n f' = (n + 1 : ℝ) * coeff (n + 1) f) := by
  have hpair := steinPair_of_polyGrowth hderiv hb hb'
  exact ⟨hpair, fun n => coeff_steinPair hpair n⟩

end

end SteinCoefficients
