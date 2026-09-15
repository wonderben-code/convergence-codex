/-
  StoneConverseLocal: Stone's CONVERSE, locally — every unitary near `1` IS an exponential of a
  self-adjoint, uniquely; a one-parameter unitary group therefore has a continuous local generator;
  and THAT GENERATOR IS ADDITIVE. What is left is the extension from a neighbourhood of `0` to all
  of `ℝ`, and this file says precisely which step that is.

  **HOW THIS FILE'S OWN FIRST DRAFT WAS WRONG, recorded first because it is the same mistake this
  day is full of (`ERRATUM 590`).** The draft proved the first four items below and then said, in
  its NOT-CLAIMED list, that additivity was the missing step and that *"this estate has no lemma
  saying a cfc of commuting elements commutes, and that is the next thing to look for"*. **The
  estate half is true — the index has none — and the conclusion was wrong: MATHLIB HAS
  `Commute.cfc`, and `Commute.expUnitary_add` besides.** `estateclaim_scan.py` flagged the sentence
  before the draft was committed, its instruction is *run the claim's own query*, and running it
  took twenty seconds and produced two library names. **Additivity is now proved**, and the
  NOT-CLAIMED list below is about the step after it.

  SPINE LINK L21 (quantum outputs), whose open residue reads, verbatim: *"Stone's CONVERSE at
  finite level — open in every dimension, theorem-shaped, with a route through Mathlib's
  `Unitary.argSelfAdjoint`."* **The route is real and this file takes its first three steps.**
  `FiniteStone.lean` holds the FORWARD direction — `unitaryGroup H`, the group law, continuity,
  `dU/dt|₀ = iH` (`generator_recovery`) and injectivity of `H ↦ U` (`unitaryGroup_injective`).
  Nothing there recovers `H` from an arbitrary `U`, and that file's header says so; this one starts
  where it stops.

  WHAT IS PROVED, all of it for an arbitrary C⋆-algebra rather than for one matrix size.
  * **`exists_selfAdjoint_exp_eq`** — for every unitary `u` with `‖u − 1‖ < 2` there is a
    self-adjoint `a` with `‖a‖ ≤ π` and `exp(ia) = u`. This is Mathlib's
    `Unitary.argSelfAdjoint` (the continuous functional calculus of the principal argument) with
    `expUnitary_argSelfAdjoint`, and the norm bound is `Unitary.norm_argSelfAdjoint_le_pi`.
  * **`expUnitary_injOn_ball`** — and on `‖a‖ < π` the exponential is INJECTIVE, off
    `argSelfAdjoint_expUnitary`. So near the identity the correspondence
    `selfAdjoint ↔ unitary` is a bijection, which is what makes *the* generator well defined
    locally rather than merely existent.
  * **`local_generator_exists`** — hence the local converse: for `U : ℝ → unitary A` with
    `U 0 = 1` and `U` continuous at `0`, there is `δ > 0` such that every `U t` with `|t| < δ` is
    an exponential of a self-adjoint of norm at most `π`. **No group law is assumed** — continuity
    at one point and the value there are the whole hypothesis.
  * **`continuousAt_localGenerator`** — and the local generator is continuous at `0`, off
    `Unitary.continuousOn_argSelfAdjoint`. This is the hypothesis the remaining step needs.
  * **`star_commute`, `commute_argSelfAdjoint`, `argSelfAdjoint_mul_of_commute`** — **THE
    ADDITIVITY STEP.** Commuting unitaries have commuting arguments (`Commute.cfc` applied on each
    side, with `Unitary.toUnits` and `Commute.units_inv_left` supplying the `star` half it asks
    for), so `Commute.expUnitary_add` turns a sum of arguments into a product of unitaries and
    `argSelfAdjoint_expUnitary` reads the answer back: `arg (u * v) = arg u + arg v` whenever the
    two are near `1`, commute, and their arguments sum to norm `< π`.
  * **`localGenerator_add`** — the same for a one-parameter group, and **the group law enters here
    and only here**.
  * **`mem_pathComponentOne_iff_prod_exp`** — the global picture, cited rather than reproved:
    a unitary is in the path component of `1` exactly when it is a FINITE PRODUCT of exponentials
    of self-adjoints (Mathlib's `Unitary.mem_pathComponentOne_iff`). It is here to mark the
    boundary of the previous item: away from `1` the general C⋆ statement gives a product, not a
    single exponential.

  WHAT IS **NOT** PROVED, and the first of these is the whole remaining content of L21's residue.
  * **NO GLOBAL `H`, and this is now the whole residue.** The converse asks for one self-adjoint
    `H` with `U t = exp(itH)` for ALL `t`. What is here gives `a t` for each small `t`, continuous,
    and ADDITIVE where the hypotheses hold. The remaining step is homogeneity and extension:
    iterate `localGenerator_add` to get `a (n • t) = n • a t` while everything stays small, hence
    `a (t / n) = a t / n`, so `a` is `ℚ`-homogeneous near `0`; `continuousAt_localGenerator`
    upgrades that to `ℝ`-homogeneity; then `H := (1 / t₀) • a t₀` for one small `t₀` and the group
    law carries `U t = exp(i t H)` to all of `ℝ`. **Each of those four is a separate piece of work
    and none is written here.**
  * ~~**`hsum` is a HYPOTHESIS, not derived from smallness.** … **that derivation is not
    written** — it is the first thing the extension above needs.~~ **WRITTEN IN THE SAME UNIT:**
    `argSelfAdjoint_one` (`argSelfAdjoint 1 = 0`, off `cfc_apply_one`, which Mathlib does not
    state), `eventually_norm_localGenerator_lt` and **`localGenerator_add_of_small`** — additivity
    near `0` with NO norm hypothesis. **And the SECOND piece landed with it**:
    `localGenerator_nsmul` (`a (n t) = n · a t` on the window) and
    `localGenerator_eq_nsmul_div` (`a t = n · a (t / n)`), which is `ℚ`-divisibility in the form
    the next step consumes. **And the ALGEBRAIC half of the third piece landed with them**:
    `localGenerator_neg` (`a (−t) = −a t`), `localGenerator_zsmul` (`a (n t) = n · a t` for every
    INTEGER `n`) and `continuousAt_of_group` (a group continuous at `0` is continuous everywhere —
    which the `ℝ` step needs, since it compares two continuous functions on a window rather than
    at a point). With divisibility that is `ℚ`-homogeneity in full. **WHAT IS LEFT, and it is
    two things**: the passage from `ℚ` to `ℝ`, by comparing two continuous functions that agree
    on a dense set; and then `H := (1/t₀) • a t₀` for one small `t₀` with `U t = exp(itH)` carried
    to all of `ℝ` by the group law. Neither is written.
  * **The group law is nowhere used**, so nothing here is specific to one-parameter groups. That is
    a feature of the statements and a limit on them: `local_generator_exists` would hold for any
    continuous curve through `1`.
  * **Finite dimension is not used and its extra strength is not claimed.** In finite dimension
    EVERY unitary is a single exponential, by diagonalisation — no `‖u − 1‖ < 2` needed. That is
    true, standard, and **not proved here**; the hypothesis in `exists_selfAdjoint_exp_eq` is what
    the general C⋆ route gives, not a statement that it is necessary.
  * **No instantiation at a concrete carrier, and two costs measured rather than guessed.**
    At `EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)` the statements do not apply as
    written: `unitary` there elaborates through `ContinuousLinearMap.monoidWithZero` and
    `ContinuousLinearMap.instStarMulId`, while Mathlib's lemmas want
    `CStarAlgebra.toNormedRing.toMonoidWithZero` and `CStarAlgebra.toStarRing.toStarMul` — an
    instance-path mismatch, reported as a type mismatch on `u` with both paths printed, and NOT a
    heartbeat problem (tested at 2000000). At `CStarMatrix (Fin 4) (Fin 4) ℂ`, the carrier
    `CascadeGNS` uses, `Norm (CStarMatrix (Fin 4) (Fin 4) ℂ)` fails to synthesise even with
    `Mathlib.Analysis.CStarAlgebra.CStarMatrix` imported. **Neither is recorded as impossible** —
    both are recorded as not chased, which is the distinction `ERRATUM 583` exists for.
  * **Nothing about the Born rule, Gleason or Wigner**, the other named residues of L21.

  0 sorry. 0 new axioms. 17 declarations, all on `[propext, Classical.choice, Quot.sound]`.
-/

import FiniteStone
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.Exponential

namespace StoneConverseLocal

open Complex NormedSpace selfAdjoint Unitary
open scoped Real Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-! ## 1. Every unitary near the identity is an exponential -/

/-- **`‖u − 1‖ < 2 → u = exp(ia)` for a self-adjoint `a` with `‖a‖ ≤ π`.** The witness is
Mathlib's principal-argument functional calculus, so nothing is chosen by hand. -/
theorem exists_selfAdjoint_exp_eq (u : unitary A) (hu : ‖(u - 1 : A)‖ < 2) :
    ∃ a : selfAdjoint A, ‖a‖ ≤ Real.pi ∧ expUnitary a = u :=
  ⟨argSelfAdjoint u, Unitary.norm_argSelfAdjoint_le_pi u, expUnitary_argSelfAdjoint hu⟩

/-- **And on `‖a‖ < π` the exponential is injective**, so the local correspondence is a bijection
and *the* generator is well defined near `1` rather than merely existent. -/
theorem expUnitary_injOn_ball :
    Set.InjOn (expUnitary (A := A)) {a : selfAdjoint A | ‖a‖ < Real.pi} := by
  intro a ha b hb h
  rw [← argSelfAdjoint_expUnitary (x := a) ha, ← argSelfAdjoint_expUnitary (x := b) hb, h]

/-! ## 2. So a continuous curve through `1` has a local generator -/

/-- **The local converse.** `U 0 = 1` and continuity of `U` at `0` give a `δ` inside which every
`U t` is an exponential. **The group law is not assumed and not used.** -/
theorem local_generator_exists (U : ℝ → unitary A) (hU0 : U 0 = 1)
    (hc : ContinuousAt (fun t => ((U t : A))) 0) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ →
      ∃ a : selfAdjoint A, ‖a‖ ≤ Real.pi ∧ expUnitary a = U t := by
  have h1 : ContinuousAt (fun t => ‖((U t : A)) - 1‖) 0 := (hc.sub continuousAt_const).norm
  have h0 : ‖((U 0 : A)) - 1‖ = 0 := by simp [hU0]
  have hev : ∀ᶠ t in nhds (0 : ℝ), ‖((U t : A)) - 1‖ < 2 :=
    h1.eventually_lt_const (by rw [h0]; norm_num : ‖((U 0 : A)) - 1‖ < 2)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hmem : t ∈ Metric.ball (0 : ℝ) δ := by simpa [Real.dist_eq] using ht
  exact ⟨argSelfAdjoint (U t), Unitary.norm_argSelfAdjoint_le_pi _,
    expUnitary_argSelfAdjoint (hball t hmem)⟩

/-- **And the local generator is continuous at `0`.** This is the hypothesis the missing
additivity step needs, which is why it is proved here rather than left to the reader. -/
theorem continuousAt_localGenerator (U : ℝ → unitary A) (hU0 : U 0 = 1)
    (hc : ContinuousAt U 0) :
    ContinuousAt (fun t => argSelfAdjoint (U t)) 0 := by
  have hmem : U 0 ∈ Metric.ball (1 : unitary A) 2 := by simp [hU0]
  exact (Unitary.continuousOn_argSelfAdjoint.continuousAt
    (Metric.isOpen_ball.mem_nhds hmem)).comp hc

/-! ## 3. ADDITIVITY, which this file's first draft recorded as the missing step -/

/-- For a unitary `u`, anything commuting with `u` commutes with `star u`. Needed because
`Commute.cfc` asks for both, and `u` is not self-adjoint. Off `Unitary.toUnits` and
`Commute.units_inv_left`. -/
theorem star_commute {u : unitary A} {b : A} (h : Commute (u : A) b) :
    Commute (star (u : A)) b := by
  have := Commute.units_inv_left (u := Unitary.toUnits u) (a := b) h
  simpa using this

/-- **Commuting unitaries have commuting arguments.** `argSelfAdjoint` is a continuous functional
calculus of the unitary, and `Commute.cfc` carries commutation through it — applied twice, once on
each side. **This is the lemma this file's first draft said the estate did not have**: it does not,
but MATHLIB does (`Commute.cfc`), and the draft's own `estateclaim_scan` flag is what made me run
the query (`ERRATUM 590`). -/
theorem commute_argSelfAdjoint {u v : unitary A} (huv : Commute (u : A) (v : A)) :
    Commute ((argSelfAdjoint u : A)) ((argSelfAdjoint v : A)) := by
  have hA : Commute (cfc (arg · : ℂ → ℂ) (v : A)) (u : A) :=
    Commute.cfc huv.symm (star_commute huv.symm) _
  have hB : Commute (cfc (arg · : ℂ → ℂ) (u : A)) (cfc (arg · : ℂ → ℂ) (v : A)) :=
    Commute.cfc hA.symm (star_commute hA.symm) _
  simpa [argSelfAdjoint] using hB

/-- **THE ADDITIVITY STEP.** For commuting unitaries near `1` whose arguments sum to norm `< π`,
the argument of the product is the sum of the arguments. `Commute.expUnitary_add` turns the sum
into a product, `expUnitary_argSelfAdjoint` identifies both factors, and
`argSelfAdjoint_expUnitary` reads the answer back. **This is what `SPINE` L21 recorded as the
whole remaining content of Stone's converse.** -/
theorem argSelfAdjoint_mul_of_commute {u v : unitary A} (huv : Commute (u : A) (v : A))
    (hu : ‖(u - 1 : A)‖ < 2) (hv : ‖(v - 1 : A)‖ < 2)
    (hsum : ‖argSelfAdjoint u + argSelfAdjoint v‖ < Real.pi) :
    argSelfAdjoint (u * v) = argSelfAdjoint u + argSelfAdjoint v := by
  have h1 : expUnitary (argSelfAdjoint u + argSelfAdjoint v) = u * v := by
    rw [(commute_argSelfAdjoint huv).expUnitary_add, expUnitary_argSelfAdjoint hu,
      expUnitary_argSelfAdjoint hv]
  rw [← h1, argSelfAdjoint_expUnitary hsum]

/-- **The same for a one-parameter group**: where the hypotheses hold, the local generator is
additive. The group law enters here and only here. -/
theorem localGenerator_add (U : ℝ → unitary A) (hgrp : ∀ s t, U (s + t) = U s * U t)
    {s t : ℝ} (hs : ‖((U s : A)) - 1‖ < 2) (ht : ‖((U t : A)) - 1‖ < 2)
    (hsum : ‖argSelfAdjoint (U s) + argSelfAdjoint (U t)‖ < Real.pi) :
    argSelfAdjoint (U (s + t)) = argSelfAdjoint (U s) + argSelfAdjoint (U t) := by
  have hcomm : Commute ((U s : A)) ((U t : A)) := by
    have h : (U s) * (U t) = (U t) * (U s) := by
      rw [← hgrp s t, ← hgrp t s, add_comm]
    rw [commute_iff_eq]
    simpa using congrArg (fun w : unitary A => (w : A)) h
  rw [hgrp s t]
  exact argSelfAdjoint_mul_of_commute hcomm hs ht hsum

/-! ## 4. And near `0` the norm hypothesis is not needed: it follows from continuity -/

/-- `argSelfAdjoint 1 = 0`. Off `cfc_apply_one` and `Complex.arg_one`; Mathlib does not state it,
and everything in §4 needs it. -/
@[simp] theorem argSelfAdjoint_one : argSelfAdjoint (1 : unitary A) = 0 := by
  ext
  simp [argSelfAdjoint]

/-- **The local generator is eventually as small as you like.** Continuity at `0` plus
`argSelfAdjoint 1 = 0`; this is what turns the norm hypothesis of §3 into a conclusion. -/
theorem eventually_norm_localGenerator_lt (U : ℝ → unitary A) (hU0 : U 0 = 1)
    (hc : ContinuousAt U 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ‖argSelfAdjoint (U t)‖ < ε := by
  have hcg : ContinuousAt (fun t => argSelfAdjoint (U t)) 0 :=
    continuousAt_localGenerator U hU0 hc
  have h0 : ‖argSelfAdjoint (U 0)‖ = 0 := by rw [hU0, argSelfAdjoint_one]; simp
  exact (hcg.norm).eventually_lt_const (by simpa [h0] using hε)

/-- **ADDITIVITY NEAR `0`, WITH NO NORM HYPOTHESIS** — the first of the four pieces
`UNLOCK_WATCHLIST` entry 268 lists between the local half and a global `H`. Two applications of
continuity give one `δ` on which both `‖U t − 1‖ < 2` and `‖a t‖ < π/2` hold, and the triangle
inequality supplies what `localGenerator_add` was assuming. -/
theorem localGenerator_add_of_small (U : ℝ → unitary A) (hU0 : U 0 = 1)
    (hc : ContinuousAt U 0) (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃ δ > 0, ∀ s t : ℝ, |s| < δ → |t| < δ →
      argSelfAdjoint (U (s + t)) = argSelfAdjoint (U s) + argSelfAdjoint (U t) := by
  obtain ⟨δ₁, hδ₁, hb₁⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_norm_localGenerator_lt U hU0 hc (ε := Real.pi / 2) (by positivity))
  have hcoe : ContinuousAt (fun t => ((U t : A))) 0 :=
    (continuous_subtype_val.continuousAt).comp hc
  have hcn : ContinuousAt (fun t => ‖((U t : A)) - 1‖) 0 :=
    (hcoe.sub continuousAt_const).norm
  have h0 : ‖((U 0 : A)) - 1‖ = 0 := by simp [hU0]
  have hlt : ‖((U 0 : A)) - 1‖ < 2 := by rw [h0]; norm_num
  obtain ⟨δ₂, hδ₂, hb₂⟩ := Metric.eventually_nhds_iff_ball.mp (hcn.eventually_lt_const hlt)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s t hs ht => ?_⟩
  have hs1 : s ∈ Metric.ball (0 : ℝ) δ₁ := by
    simpa [Real.dist_eq] using lt_of_lt_of_le hs (min_le_left _ _)
  have ht1 : t ∈ Metric.ball (0 : ℝ) δ₁ := by
    simpa [Real.dist_eq] using lt_of_lt_of_le ht (min_le_left _ _)
  have hs2 : s ∈ Metric.ball (0 : ℝ) δ₂ := by
    simpa [Real.dist_eq] using lt_of_lt_of_le hs (min_le_right _ _)
  have ht2 : t ∈ Metric.ball (0 : ℝ) δ₂ := by
    simpa [Real.dist_eq] using lt_of_lt_of_le ht (min_le_right _ _)
  have hsum : ‖argSelfAdjoint (U s) + argSelfAdjoint (U t)‖ < Real.pi := by
    calc ‖argSelfAdjoint (U s) + argSelfAdjoint (U t)‖
        ≤ ‖argSelfAdjoint (U s)‖ + ‖argSelfAdjoint (U t)‖ := norm_add_le _ _
      _ < Real.pi / 2 + Real.pi / 2 := add_lt_add (hb₁ s hs1) (hb₁ t ht1)
      _ = Real.pi := by ring
  exact localGenerator_add U hgrp (hb₂ s hs2) (hb₂ t ht2) hsum

/-! ## 5. Iterating it: `ℕ`-homogeneity, and division -/

/-- **`a (n t) = n · a t` while everything stays in the window** — the second of the four pieces
`UNLOCK_WATCHLIST` entry 268 lists. Induction on `n` off `localGenerator_add_of_small`; the only
care needed is that `|k t| ≤ |(k+1) t|` and `|t| ≤ |(k+1) t|`, so one hypothesis on the largest
multiple covers every smaller one. -/
theorem localGenerator_nsmul (U : ℝ → unitary A) (hU0 : U 0 = 1) (hc : ContinuousAt U 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃ δ > 0, ∀ (n : ℕ) (t : ℝ), |(n : ℝ) * t| < δ →
      argSelfAdjoint (U ((n : ℝ) * t)) = n • argSelfAdjoint (U t) := by
  obtain ⟨δ, hδ, hadd⟩ := localGenerator_add_of_small U hU0 hc hgrp
  refine ⟨δ, hδ, ?_⟩
  intro n
  induction n with
  | zero => intro t _; simp [hU0]
  | succ k ih =>
    intro t ht
    push_cast at ht ⊢
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have ht' : |(k : ℝ) * t| < δ := by
      refine lt_of_le_of_lt ?_ ht
      rw [abs_mul, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg t)
      rw [abs_of_nonneg hk0, abs_of_nonneg (by linarith : (0:ℝ) ≤ (k:ℝ) + 1)]
      linarith
    have htt : |t| < δ := by
      refine lt_of_le_of_lt ?_ ht
      rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ (k:ℝ) + 1)]
      nlinarith [abs_nonneg t]
    have hsplit : ((k : ℝ) + 1) * t = (k : ℝ) * t + t := by ring
    rw [hsplit, hadd _ _ ht' htt, ih t ht', succ_nsmul]

/-- **And so the generator is divisible**: `a t = n · a (t / n)` for every positive `n`, on the
same window. This is the form the `ℝ`-homogeneity step consumes — stated with `n •` on the right
rather than `(1/n) •` on the left, so no scalar inverse appears and nothing has to be said about
`Module ℝ (selfAdjoint A)`. -/
theorem localGenerator_eq_nsmul_div (U : ℝ → unitary A) (hU0 : U 0 = 1)
    (hc : ContinuousAt U 0) (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃ δ > 0, ∀ (n : ℕ) (t : ℝ), 0 < n → |t| < δ →
      argSelfAdjoint (U t) = n • argSelfAdjoint (U (t / n)) := by
  obtain ⟨δ, hδ, hn⟩ := localGenerator_nsmul U hU0 hc hgrp
  refine ⟨δ, hδ, fun n t hnpos htlt => ?_⟩
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
  have hmul : (n : ℝ) * (t / n) = t := by field_simp
  have h := hn n (t / n) (by rw [hmul]; exact htlt)
  rw [hmul] at h
  exact h

/-! ## 6. Negation, `ℤ`-homogeneity, and continuity away from `0` -/

/-- **A one-parameter group continuous at `0` is continuous everywhere.** `U t = U t₀ · U (t − t₀)`
and multiplication is continuous. Needed for the `ℝ`-homogeneity step, which compares two
continuous functions on a window rather than at a point. -/
theorem continuousAt_of_group (U : ℝ → unitary A) (hc : ContinuousAt U 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) (t₀ : ℝ) : ContinuousAt U t₀ := by
  have hrw : U = fun t => U t₀ * U (t - t₀) := by
    funext t
    rw [← hgrp t₀ (t - t₀)]
    ring_nf
  have h1 : ContinuousAt (fun t : ℝ => U (t - t₀)) t₀ :=
    ContinuousAt.comp (by simpa using hc) ((continuous_sub_right t₀).continuousAt)
  rw [hrw]
  exact continuousAt_const.mul h1

/-- **`a (−t) = −a t`** — additivity at `t` and `−t`, with `argSelfAdjoint 1 = 0` closing it. -/
theorem localGenerator_neg (U : ℝ → unitary A) (hU0 : U 0 = 1) (hc : ContinuousAt U 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ → argSelfAdjoint (U (-t)) = -argSelfAdjoint (U t) := by
  obtain ⟨δ, hδ, hadd⟩ := localGenerator_add_of_small U hU0 hc hgrp
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hneg : |(-t)| < δ := by rwa [abs_neg]
  have h := hadd t (-t) ht hneg
  rw [add_neg_cancel, hU0, argSelfAdjoint_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- **`a (n t) = n · a t` for every INTEGER `n`**, by cases on the sign off `localGenerator_nsmul`
and `localGenerator_neg`. With `localGenerator_eq_nsmul_div` this is `ℚ`-homogeneity in full: the
algebraic half of the third piece is done, and what is left of it is the passage from `ℚ` to `ℝ`,
which is where `continuousAt_of_group` comes in. -/
theorem localGenerator_zsmul (U : ℝ → unitary A) (hU0 : U 0 = 1) (hc : ContinuousAt U 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃ δ > 0, ∀ (n : ℤ) (t : ℝ), |(n : ℝ) * t| < δ →
      argSelfAdjoint (U ((n : ℝ) * t)) = n • argSelfAdjoint (U t) := by
  obtain ⟨δ₁, hδ₁, hnat⟩ := localGenerator_nsmul U hU0 hc hgrp
  obtain ⟨δ₂, hδ₂, hneg⟩ := localGenerator_neg U hU0 hc hgrp
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun n t ht => ?_⟩
  have h1 : |(n : ℝ) * t| < δ₁ := lt_of_lt_of_le ht (min_le_left _ _)
  have h2 : |(n : ℝ) * t| < δ₂ := lt_of_lt_of_le ht (min_le_right _ _)
  obtain ⟨m, hm⟩ := n.eq_nat_or_neg
  rcases hm with rfl | rfl
  · push_cast at h1 ⊢
    rw [hnat m t h1]
    simp
  · have hcast : (((-(m : ℤ)) : ℤ) : ℝ) = -(m : ℝ) := by push_cast; ring
    rw [hcast] at h1 h2 ⊢
    rw [neg_mul, abs_neg] at h1 h2
    rw [neg_mul, hneg ((m : ℝ) * t) h2, hnat m t h1]
    simp

/-! ## 7. The boundary of the local statement -/

/-- **Away from `1`, a general C⋆-algebra gives a PRODUCT of exponentials, not one.** Mathlib's
`Unitary.mem_pathComponentOne_iff`, stated here to mark what `exists_selfAdjoint_exp_eq`'s
hypothesis is doing. In finite dimension one exponential always suffices, by diagonalisation —
true, standard, and not proved in this estate. -/
theorem mem_pathComponentOne_iff_prod_exp (u : unitary A) :
    u ∈ pathComponent (1 : unitary A) ↔
      ∃ l : List (selfAdjoint A), (l.map expUnitary).prod = u :=
  Unitary.mem_pathComponentOne_iff

end

end StoneConverseLocal
