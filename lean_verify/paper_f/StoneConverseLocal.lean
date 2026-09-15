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
  * **`hsum` is a HYPOTHESIS, not derived from smallness.** `argSelfAdjoint_mul_of_commute` and
    `localGenerator_add` both assume `‖a u + a v‖ < π` rather than deducing it from `s, t` being
    small. It should follow from `continuousAt_localGenerator` together with
    `argSelfAdjoint 1 = 0`, and **that derivation is not written** — it is the first thing the
    extension above needs, and it is named rather than assumed away.
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

  0 sorry. 0 new axioms. 9 declarations, all on `[propext, Classical.choice, Quot.sound]`.
-/

import FiniteStone
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.Exponential

namespace StoneConverseLocal

open Complex NormedSpace selfAdjoint Unitary
open scoped Real

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

/-! ## 3. The boundary of the local statement -/

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
