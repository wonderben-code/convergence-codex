/-
  StoneConverseLocal: **STONE'S CONVERSE, AND IT IS NO LONGER LOCAL.** A one-parameter unitary
  group in an arbitrary C⋆-algebra, continuous at the single point `0`, is `t ↦ exp(itH)` for a
  UNIQUE self-adjoint `H` — and conversely every such `H` gives one, so
  `FiniteStone.unitaryGroup` is a bijection from `selfAdjoint A` onto these groups. The local
  statements this file started as are all still here, in sections 1–6, because the global one is
  built out of them.

  **THE FILE'S NAME IS NOW WRONG, and is kept anyway.** `…Local` described the file for three
  units and stopped being true in the fourth. It is not renamed because the name is the key five
  registers and four generated `estateindex` batch files point to, and a rename that misses one
  of them is worse than a name with a note on it. **This is the note.**

  **HOW THIS FILE'S OWN FIRST DRAFT WAS WRONG, kept because the lesson keeps paying
  (`ERRATUM 590`).** The draft proved the first four items below and then said, in its
  NOT-CLAIMED list, that additivity was the missing step and that *"this estate has no lemma
  saying a cfc of commuting elements commutes, and that is the next thing to look for"*. **The
  estate half is true — the index has none — and the conclusion was wrong: MATHLIB HAS
  `Commute.cfc`, and `Commute.expUnitary_add` besides.** `estateclaim_scan.py` flagged the
  sentence before the draft was committed, its instruction is *run the claim's own query*, and
  running it took twenty seconds and produced two library names.

  **AND THE RECORDED PLAN FOR THE LAST STEP WAS WRONG ABOUT THE ORDER (`ERRATUM 591`).**
  `UNLOCK_WATCHLIST` 268, in this hand, listed four pieces and put `ℝ`-homogeneity of the LOCAL
  generator third: upgrade `a (qt) = q · a t` from rational `q` to real `q` by continuity, and
  only then build `H`. **That step is not needed and was never needed.** The local generator `a`
  is known continuous only AT the single point `0` (`continuousAt_localGenerator`), and more only
  where `U t` can be shown to stay in the ball of radius `2` about `1`, which is the window
  again — so a density argument about `a` has to fight the very window the step is trying to
  escape; `U` itself is continuous on all of `ℝ`
  (`continuousAt_of_group`, proved in the previous unit for precisely this purpose), and the
  density argument applied to `U` has no window to fight. The whole of the last step is: raise a
  small-`t` identity to an arbitrary INTEGER power, where the group law and `expUnitary_zsmul`
  both leave the window behind, and compare two globally continuous functions on the rational
  multiples of one `t₀`. `localGenerator_eq_smul` recovers the `ℝ`-homogeneity the plan wanted,
  as a COROLLARY of the global `H` rather than a step toward it. **The plan was right about the
  content and wrong about the direction of the arrow**, which is the same shape as `ERRATUM 582`
  earlier today: a route recorded as necessary when it was only sufficient.

  SPINE LINK L21 (quantum outputs), whose open residue read, verbatim: *"Stone's CONVERSE at
  finite level — open in every dimension, theorem-shaped, with a route through Mathlib's
  `Unitary.argSelfAdjoint`."* **The route was real and this file has now walked all of it.**
  `FiniteStone.lean` holds the FORWARD direction — `unitaryGroup H`, the group law, continuity,
  `dU/dt|₀ = iH` (`generator_recovery`) and injectivity of `H ↦ U` (`unitaryGroup_injective`).
  Nothing there recovers `H` from an arbitrary `U`; this file does, and `eq_unitaryGroup_iff`
  states the two halves as one equivalence.

  WHAT IS PROVED, all of it for an arbitrary C⋆-algebra rather than for one matrix size.
  * **`exists_selfAdjoint_exp_eq`** — for every unitary `u` with `‖u − 1‖ < 2` there is a
    self-adjoint `a` with `‖a‖ ≤ π` and `exp(ia) = u`. This is Mathlib's
    `Unitary.argSelfAdjoint` (the continuous functional calculus of the principal argument) with
    `expUnitary_argSelfAdjoint`, and the norm bound is `Unitary.norm_argSelfAdjoint_le_pi`.
  * **`expUnitary_injOn_ball`** — and on `‖a‖ < π` the exponential is INJECTIVE, off
    `argSelfAdjoint_expUnitary`. So near the identity the correspondence
    `selfAdjoint ↔ unitary` is a bijection, which is what makes *the* generator well defined
    locally rather than merely existent.
  * **`local_generator_exists`, `exists_expUnitary_localGenerator`** — hence the local converse:
    for `U : ℝ → unitary A` with `U 0 = 1` and `U` continuous at `0`, there is `δ > 0` such that
    every `U t` with `|t| < δ` is an exponential of a self-adjoint of norm at most `π`. **No
    group law is assumed** — continuity at one point and the value there are the whole
    hypothesis. The second form names the witness so the window can be used as a rewrite.
  * **`continuousAt_localGenerator`** — and the local generator is continuous at `0`, off
    `Unitary.continuousOn_argSelfAdjoint`.
  * **`star_commute`, `commute_argSelfAdjoint`, `argSelfAdjoint_mul_of_commute`** — **THE
    ADDITIVITY STEP.** Commuting unitaries have commuting arguments (`Commute.cfc` applied on each
    side, with `Unitary.toUnits` and `Commute.units_inv_left` supplying the `star` half it asks
    for), so `Commute.expUnitary_add` turns a sum of arguments into a product of unitaries and
    `argSelfAdjoint_expUnitary` reads the answer back: `arg (u * v) = arg u + arg v` whenever the
    two are near `1`, commute, and their arguments sum to norm `< π`.
  * **`localGenerator_add`, `argSelfAdjoint_one`, `eventually_norm_localGenerator_lt`,
    `localGenerator_add_of_small`** — additivity for a one-parameter group with NO norm side
    condition: shrink the window until both arguments have norm `< π/2`.
  * **`localGenerator_nsmul`, `localGenerator_eq_nsmul_div`, `localGenerator_neg`,
    `localGenerator_zsmul`** — `ℤ`-homogeneity and divisibility of the local generator on the
    window, which is `ℚ`-homogeneity in the form the global step consumes.
  * **`continuousAt_of_group`** — a one-parameter group continuous at `0` is continuous
    EVERYWHERE, off `U t = U t₀ · U (t − t₀)`. This is the hypothesis the global step actually
    needs, and the reason the plan's `ℝ`-homogeneity step is unnecessary.
  * **`eq_one_of_group`, `inv_of_group`, `group_natPow`, `group_zpow`** — `U 0 = 1` is not an
    extra hypothesis, `U (−t) = (U t)⁻¹`, and `U (nt) = (U t)ⁿ` for every integer `n` **with no
    smallness condition at all**. Everything in sections 5–6 is confined to `|t| < δ` because it
    goes through `argSelfAdjoint`; this does not, and that is how the window is escaped.
  * **`expUnitary_nsmul`, `expUnitary_neg`, `expUnitary_zsmul`** — the same for the exponential.
    Mathlib has `Commute.expUnitary_add` and `selfAdjoint.expUnitary_zero` and not these; the
    commutation hypotheses are `Commute.natCast_mul_left` (through `selfAdjoint.val_smul` and
    `nsmul_eq_mul`) and `Commute.neg_right_iff`, both on `Commute.refl`. **Those two names are
    what the tactic USES**; the first draft of this line said `Commute.nsmul_left`, which does
    not exist, and the build did not object — see `ERRATUM 593`.
  * **`denseRange_rat_mul`** — the rational multiples of any nonzero `t₀` are dense in `ℝ`,
    `Rat.denseRange_cast` composed with the surjection `x ↦ x t₀`.
  * **`exists_global_generator`** — **THE THEOREM.** `U` continuous at `0` with the group law
    gives `H : selfAdjoint A` with `U t = exp(itH)` for EVERY real `t`. Fix `t₀` in the window,
    set `H := t₀⁻¹ · a t₀`, use divisibility at `t₀/n` and integer powers to get agreement on
    every rational multiple of `t₀`, and finish with `Continuous.ext_on`.
  * **`global_generator_unique`, `exists_unique_global_generator`** — and `H` is UNIQUE, by
    reading both exponents back at one `t` small enough for both norms to sit below `π`. So the
    statement is `∃!`, which is what the classical theorem asserts.
  * **`exists_eq_unitaryGroup`, `eq_unitaryGroup_iff`** — the loop with `FiniteStone` closed:
    a map `ℝ → unitary A` is a one-parameter group continuous at `0` **exactly when** it is
    `FiniteStone.unitaryGroup H` for some self-adjoint `H`. Surjectivity is this file,
    injectivity is that one.
  * **`localGenerator_eq_smul`** — `a t = t · H` near `0`, the `ℝ`-homogeneity of `ERRATUM 591`,
    as a corollary.
  * **`hasDerivAt_of_group`** — **and every such group is DIFFERENTIABLE, everywhere, with
    `dU/dt = iH·U`.** `FiniteStone.hasDerivAt_unitaryGroup` proves that for the group BUILT from
    `H`; composed with the converse it becomes a statement about an arbitrary one, whose
    generator was not given but recovered.
  * **`generator_eq_neg_I_smul_deriv`** — and `H = −i·dU/dt|₀`, which is the form the classical
    statement takes. The last conjunct is what makes it a RECOVERY rather than a coincidence:
    any `L` with `dU/dt|₀ = L` gives `H = −iL`, by uniqueness of the derivative and
    `FiniteStone.generator_determined`. So the generator is not merely existent and unique — it
    is computable from `U` by one differentiation.
  * **`mem_pathComponentOne_iff_prod_exp`** — cited rather than reproved: a unitary is in the
    path component of `1` exactly when it is a FINITE PRODUCT of exponentials (Mathlib's
    `Unitary.mem_pathComponentOne_iff`). It marks the boundary of the SINGLE-exponential
    statements: away from `1`, and with no group law to lean on, a product is all one gets.

  WHAT IS **NOT** PROVED, and the first item is the one that matters.
  * **THIS IS THE NORM-CONTINUOUS STONE THEOREM, NOT THE UNBOUNDED ONE.** `ContinuousAt U 0` is
    continuity in the norm of `A`, and `H` is an element of `A`, hence bounded. The classical
    Stone theorem on a Hilbert space assumes only STRONG-operator continuity and produces a
    densely defined, generally UNBOUNDED self-adjoint generator; that theorem is not proved here
    and nothing here approaches it. **The gap is not an artefact of the proof.** This file's own
    `eq_unitaryGroup_iff` shows that the groups of the form `t ↦ exp(itH)` with `H : selfAdjoint A`
    are EXACTLY the norm-continuous ones, so asking for a generator inside `A` forces the
    stronger hypothesis. Weakening it means changing where `H` lives, which is a different
    theorem with different machinery. Measured, not assumed: Mathlib v4.29.1 has no
    one-parameter-group theory to defer to — `grep -r 'one-parameter\|oneParameter\|StoneTheorem'`
    over `Mathlib/` returns zero files — and the only unbounded-operator material is
    `Analysis/InnerProductSpace/LinearPMap.lean`, whose own header says *"We will develop the
    basics of the theory of unbounded operators on Hilbert spaces"* and which reaches the adjoint
    of a partially defined map with no spectral theory on top of it.
  * **In finite dimension the two hypotheses coincide**, so at the finite level L21 asked about,
    this IS the whole theorem — *for any C⋆-algebra carrier*. That sentence is a claim about the
    theorem, not about an instantiation, and the instantiation is the next item.
  * ~~**No instantiation at a concrete carrier, and two costs measured rather than guessed.**~~
    **CHASED THE NEXT UNIT, AND BOTH COSTS DISSOLVED (`ERRATUM 594`).**
    `StoneConverseCarriers.lean` lands every theorem below on `CStarMatrix n n ℂ` at any finite
    index, on `CascadeGNS.M4`, on `B(E)` for any complex Hilbert space, on `ℂⁿ` and on the
    cascade's GNS space — nine one-term applications, no new mathematics. The first cost was a
    missing `open scoped ComplexOrder` (`CStarMatrix.instCStarAlgebra` wants `PartialOrder` and
    `StarOrderedRing` on the ENTRY algebra, which for `ℂ` are scoped); the second a missing
    `import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap`, which is where
    `CStarAlgebra (E →L[ℂ] E)` lives — without it the C⋆ path did not exist to be found, which
    is why elaboration took the generic monoid one and printed a mismatch. **And the sentence
    below about heartbeats tested the wrong option**: the search that overruns is governed by
    `synthInstance.maxHeartbeats`, default 20000, not by `maxHeartbeats`; measured, 20000 fails
    and 21000 succeeds. The paragraph is kept verbatim as the erratum's evidence.
  * **The superseded paragraph, kept as written:**
    At `EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)` the statements do not apply as
    written: `unitary` there elaborates through `ContinuousLinearMap.monoidWithZero` and
    `ContinuousLinearMap.instStarMulId`, while Mathlib's lemmas want
    `CStarAlgebra.toNormedRing.toMonoidWithZero` and `CStarAlgebra.toStarRing.toStarMul` — an
    instance-path mismatch, reported as a type mismatch on `u` with both paths printed, and NOT a
    heartbeat problem (tested at 2000000). At `CStarMatrix (Fin 4) (Fin 4) ℂ`, the carrier
    `CascadeGNS` uses, `Norm (CStarMatrix (Fin 4) (Fin 4) ℂ)` fails to synthesise even with
    `Mathlib.Analysis.CStarAlgebra.CStarMatrix` imported. **Neither is recorded as impossible** —
    both are recorded as not chased, which is the distinction `ERRATUM 583` exists for. Until one
    is chased, `FiniteStone`'s forward direction and this file's converse are both abstract and
    do not meet at a named matrix algebra.
  * **Nothing about the Born rule, Gleason or Wigner**, the other named residues of L21.
  * **No self-adjointness of a generator defined by a limit.** `H` here is produced from
    `argSelfAdjoint`, which lands in `selfAdjoint A` by construction. The classical route — take
    `H := lim (U t − 1)/(it)` and PROVE it self-adjoint — is not taken and is not needed.

  0 sorry. 0 new axioms. 34 declarations, all on `[propext, Classical.choice, Quot.sound]`.
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

/-! ## 7. From `ℚ` to `ℝ`: the GLOBAL generator -/

/-- `U 0 = 1` is not an extra hypothesis — the group law forces it. Every statement above takes
`hU0` for readability, and this says what that costs: nothing. -/
theorem eq_one_of_group (U : ℝ → unitary A) (hgrp : ∀ s t, U (s + t) = U s * U t) :
    U 0 = 1 := by
  have h : U 0 * U 0 = 1 * U 0 := by rw [← hgrp 0 0, add_zero, one_mul]
  exact mul_right_cancel h

/-- **`U (−t) = (U t)⁻¹`**, likewise from the group law alone. -/
theorem inv_of_group (U : ℝ → unitary A) (hgrp : ∀ s t, U (s + t) = U s * U t) (t : ℝ) :
    U (-t) = (U t)⁻¹ := by
  have h : U t * U (-t) = 1 := by
    rw [← hgrp t (-t), add_neg_cancel, eq_one_of_group U hgrp]
  exact eq_inv_of_mul_eq_one_right h

/-- **`U (n t) = (U t)ⁿ` for every natural `n`, with NO smallness condition.** This is the step
that escapes the window: every homogeneity statement in sections 5 and 6 is confined to `|t| < δ`
because it goes through `argSelfAdjoint`, and this one does not. -/
theorem group_natPow (U : ℝ → unitary A) (hgrp : ∀ s t, U (s + t) = U s * U t) (n : ℕ) (t : ℝ) :
    U ((n : ℝ) * t) = U t ^ n := by
  induction n with
  | zero => simpa using eq_one_of_group U hgrp
  | succ k ih =>
    have hsplit : ((k : ℝ) + 1) * t = (k : ℝ) * t + t := by ring
    push_cast
    rw [hsplit, hgrp, ih, pow_succ]

/-- **And for every integer `n`**, by cases on the sign off `inv_of_group`. -/
theorem group_zpow (U : ℝ → unitary A) (hgrp : ∀ s t, U (s + t) = U s * U t) (n : ℤ) (t : ℝ) :
    U ((n : ℝ) * t) = U t ^ n := by
  obtain ⟨m, hm⟩ := n.eq_nat_or_neg
  rcases hm with rfl | rfl
  · push_cast
    rw [group_natPow U hgrp m t, zpow_natCast]
  · have hcast : (((-(m : ℤ)) : ℤ) : ℝ) = -(m : ℝ) := by push_cast; ring
    rw [hcast, neg_mul, inv_of_group U hgrp, group_natPow U hgrp m t, zpow_neg, zpow_natCast]

/-- **`exp(i · n a) = exp(i a)ⁿ`.** Mathlib has `Commute.expUnitary_add` and
`selfAdjoint.expUnitary_zero` but not this. The commutation hypothesis is `Commute.refl` pushed
through `selfAdjoint.val_smul`, `nsmul_eq_mul` and `Commute.natCast_mul_left` — the names `simp?`
reports, not the one this docstring first guessed (`ERRATUM 593`). -/
theorem expUnitary_nsmul (x : selfAdjoint A) (n : ℕ) :
    expUnitary (n • x) = expUnitary x ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hc : Commute (((k • x : selfAdjoint A) : A)) ((x : A)) := by simp
    rw [succ_nsmul, hc.expUnitary_add, ih, pow_succ]

/-- **`exp(i(−a)) = exp(ia)⁻¹`.** The commutation hypothesis is `Commute.neg_right_iff` on
`Commute.refl`, through `NegMemClass.coe_neg`. -/
theorem expUnitary_neg (x : selfAdjoint A) : expUnitary (-x) = (expUnitary x)⁻¹ := by
  have hc : Commute ((x : A)) (((-x : selfAdjoint A) : A)) := by simp
  have h := hc.expUnitary_add
  rw [add_neg_cancel, selfAdjoint.expUnitary_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- **`exp(i · n a) = exp(ia)ⁿ` for every integer `n`.** -/
theorem expUnitary_zsmul (x : selfAdjoint A) (n : ℤ) :
    expUnitary (n • x) = expUnitary x ^ n := by
  obtain ⟨m, hm⟩ := n.eq_nat_or_neg
  rcases hm with rfl | rfl
  · rw [natCast_zsmul, expUnitary_nsmul, zpow_natCast]
  · rw [neg_zsmul, natCast_zsmul, expUnitary_neg, expUnitary_nsmul, zpow_neg, zpow_natCast]

/-- `local_generator_exists` with its witness named, so the window can be used as a rewrite
instead of re-derived each time. -/
theorem exists_expUnitary_localGenerator (U : ℝ → unitary A) (hU0 : U 0 = 1)
    (hc : ContinuousAt U 0) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ → expUnitary (argSelfAdjoint (U t)) = U t := by
  have hcoe : ContinuousAt (fun t => ((U t : A))) 0 :=
    (continuous_subtype_val.continuousAt).comp hc
  have hcn : ContinuousAt (fun t => ‖((U t : A)) - 1‖) 0 := (hcoe.sub continuousAt_const).norm
  have h0 : ‖((U 0 : A)) - 1‖ = 0 := by simp [hU0]
  have hlt : ‖((U 0 : A)) - 1‖ < 2 := by rw [h0]; norm_num
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hcn.eventually_lt_const hlt)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hmem : t ∈ Metric.ball (0 : ℝ) δ := by simpa [Real.dist_eq] using ht
  exact expUnitary_argSelfAdjoint (hball t hmem)

/-- **The rational multiples of a nonzero `t₀` are dense in `ℝ`** — `Rat.denseRange_cast`
composed with the surjection `x ↦ x t₀`. This is the set the two continuous functions are
compared on. -/
theorem denseRange_rat_mul {t₀ : ℝ} (ht₀ : t₀ ≠ 0) :
    DenseRange (fun q : ℚ => (q : ℝ) * t₀) := by
  have hs : Function.Surjective (fun x : ℝ => x * t₀) := fun y => ⟨y / t₀, by field_simp⟩
  exact hs.denseRange.comp Rat.denseRange_cast (continuous_mul_const t₀)

set_option backward.isDefEq.respectTransparency false in
/-- **STONE'S CONVERSE: a strongly continuous one-parameter unitary group has a generator.**
For `U : ℝ → unitary A` continuous at `0` with `U (s + t) = U s * U t`, there is a self-adjoint
`H` with `U t = exp(i t H)` for **every** real `t`.

The proof is the one the registers named, with one economy. Fix `t₀` in the window on which both
`localGenerator_eq_nsmul_div` and `exists_expUnitary_localGenerator` apply, and set
`H := t₀⁻¹ · a t₀`. On `t₀ / n` divisibility gives `a (t₀/n) = (1/n) · a t₀`, so
`U (t₀/n) = exp(i (t₀/n) H)`; then `group_zpow` and `expUnitary_zsmul` raise both sides to an
arbitrary INTEGER power, which leaves the window behind and gives agreement on every rational
multiple of `t₀`. Those are dense, `U` is continuous everywhere by `continuousAt_of_group`, and
`Continuous.ext_on` finishes.

**The economy: `ℝ`-homogeneity of `a` is never needed.** The plan recorded in
`UNLOCK_WATCHLIST` 268 was to upgrade `ℚ`-homogeneity of the local generator to `ℝ`-homogeneity
and only then build `H`. That is unnecessary — the density argument is applied to `U` itself,
which is continuous on all of `ℝ`, rather than to `a`, which is only known continuous near `0`.
`localGenerator_eq_smul` below recovers the `ℝ`-homogeneity as a consequence. -/
theorem exists_global_generator (U : ℝ → unitary A) (hc : ContinuousAt U 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃ H : selfAdjoint A, ∀ t : ℝ, U t = expUnitary (t • H) := by
  have hU0 : U 0 = 1 := eq_one_of_group U hgrp
  obtain ⟨δ₁, hδ₁, hdiv⟩ := localGenerator_eq_nsmul_div U hU0 hc hgrp
  obtain ⟨δ₂, hδ₂, hexp⟩ := exists_expUnitary_localGenerator U hU0 hc
  have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have ht₀pos : 0 < min δ₁ δ₂ / 2 := by linarith
  have ht₀lt : min δ₁ δ₂ / 2 < min δ₁ δ₂ := by linarith
  refine ⟨(min δ₁ δ₂ / 2)⁻¹ • argSelfAdjoint (U (min δ₁ δ₂ / 2)), ?_⟩
  set t₀ := min δ₁ δ₂ / 2 with ht₀def
  have ht₀ne : t₀ ≠ 0 := ne_of_gt ht₀pos
  have ht1 : |t₀| < δ₁ := by
    rw [abs_of_pos ht₀pos]; exact lt_of_lt_of_le ht₀lt (min_le_left _ _)
  have key : ∀ q : ℚ, U ((q : ℝ) * t₀)
      = expUnitary (((q : ℝ) * t₀) • (t₀⁻¹ • argSelfAdjoint (U t₀))) := by
    intro q
    have hnpos : 0 < q.den := q.pos
    have hn1 : (1 : ℝ) ≤ (q.den : ℝ) := by exact_mod_cast hnpos
    have hspos : 0 < t₀ / (q.den : ℝ) := div_pos ht₀pos (by linarith)
    have hs2 : |t₀ / (q.den : ℝ)| < δ₂ := by
      rw [abs_of_pos hspos]
      calc t₀ / (q.den : ℝ) ≤ t₀ := div_le_self ht₀pos.le hn1
        _ < min δ₁ δ₂ := ht₀lt
        _ ≤ δ₂ := min_le_right _ _
    have hdivs : argSelfAdjoint (U t₀)
        = q.den • argSelfAdjoint (U (t₀ / (q.den : ℝ))) := hdiv q.den t₀ hnpos ht1
    have hqt : (q : ℝ) * t₀ = (q.num : ℝ) * (t₀ / (q.den : ℝ)) := by
      rw [Rat.cast_def]
      field_simp
    rw [hqt, group_zpow U hgrp, ← hexp _ hs2, ← expUnitary_zsmul]
    congr 1
    rw [smul_smul, hdivs, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      ← Int.cast_smul_eq_zsmul ℝ]
    congr 1
    field_simp
  have hcU : Continuous U := continuous_iff_continuousAt.mpr (continuousAt_of_group U hc hgrp)
  have hcE : Continuous (fun t : ℝ => expUnitary (t • (t₀⁻¹ • argSelfAdjoint (U t₀)))) := by
    fun_prop
  have hEq := Continuous.ext_on (denseRange_rat_mul ht₀ne) hcU hcE
    (by rintro x ⟨q, rfl⟩; exact key q)
  intro t
  exact congrFun hEq t

/-- **And the generator is unique.** At a `t` small enough for both `‖t H‖` and `‖t K‖` to sit
below `π`, `argSelfAdjoint_expUnitary` reads each exponent back, so `t H = t K` and `t ≠ 0`. -/
theorem global_generator_unique {H K : selfAdjoint A}
    (h : ∀ t : ℝ, expUnitary (t • H) = expUnitary (t • K)) : H = K := by
  have hM0 : 0 ≤ max ‖H‖ ‖K‖ := le_trans (norm_nonneg H) (le_max_left _ _)
  have hden : 0 < 2 * (1 + max ‖H‖ ‖K‖) := by linarith
  have htpos : 0 < Real.pi / (2 * (1 + max ‖H‖ ‖K‖)) := by positivity
  have hbound : ∀ x : selfAdjoint A, ‖x‖ ≤ max ‖H‖ ‖K‖ →
      ‖(Real.pi / (2 * (1 + max ‖H‖ ‖K‖))) • x‖ < Real.pi := by
    intro x hx
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, div_mul_eq_mul_div, div_lt_iff₀ hden]
    have hpi : 0 < Real.pi := Real.pi_pos
    have hlt : ‖x‖ < 2 * (1 + max ‖H‖ ‖K‖) := by linarith
    exact mul_lt_mul_of_pos_left hlt hpi
  have hH := argSelfAdjoint_expUnitary (hbound H (le_max_left _ _))
  have hK := argSelfAdjoint_expUnitary (hbound K (le_max_right _ _))
  have hsm : (Real.pi / (2 * (1 + max ‖H‖ ‖K‖))) • H
      = (Real.pi / (2 * (1 + max ‖H‖ ‖K‖))) • K := by
    rw [← hH, ← hK, h _]
  have h2 : (Real.pi / (2 * (1 + max ‖H‖ ‖K‖)))⁻¹ • (Real.pi / (2 * (1 + max ‖H‖ ‖K‖))) • H
      = (Real.pi / (2 * (1 + max ‖H‖ ‖K‖)))⁻¹ • (Real.pi / (2 * (1 + max ‖H‖ ‖K‖))) • K := by
    rw [hsm]
  rwa [smul_smul, smul_smul, inv_mul_cancel₀ (ne_of_gt htpos), one_smul, one_smul] at h2

/-- **Stone's converse in the form the classical statement takes**: the generator exists and is
unique. This is the whole of what `UNLOCK_WATCHLIST` entry 268 asked for. -/
theorem exists_unique_global_generator (U : ℝ → unitary A) (hc : ContinuousAt U 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃! H : selfAdjoint A, ∀ t : ℝ, U t = expUnitary (t • H) := by
  obtain ⟨H, hH⟩ := exists_global_generator U hc hgrp
  exact ⟨H, hH, fun K hK => global_generator_unique (fun t => (hK t).symm.trans (hH t))⟩

/-- **`ℝ`-homogeneity of the local generator, as a COROLLARY rather than a step.** The recorded
plan reached the global `H` through this statement; the route actually taken reaches this
statement from the global `H`. Recorded because the plan was wrong about the order, not about
the content. -/
theorem localGenerator_eq_smul (U : ℝ → unitary A) (hc : ContinuousAt U 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃ (H : selfAdjoint A) (δ : ℝ), 0 < δ ∧
      ∀ t : ℝ, |t| < δ → argSelfAdjoint (U t) = t • H := by
  obtain ⟨H, hH⟩ := exists_global_generator U hc hgrp
  refine ⟨H, Real.pi / (1 + ‖H‖), by positivity, fun t ht => ?_⟩
  have hnn : (0 : ℝ) ≤ ‖H‖ := norm_nonneg H
  have hlt : ‖t • H‖ < Real.pi := by
    rw [norm_smul, Real.norm_eq_abs]
    have h1 : |t| * ‖H‖ ≤ (Real.pi / (1 + ‖H‖)) * ‖H‖ :=
      mul_le_mul_of_nonneg_right ht.le hnn
    have h2 : (Real.pi / (1 + ‖H‖)) * ‖H‖ < Real.pi := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith [Real.pi_pos]
    linarith
  rw [hH t, argSelfAdjoint_expUnitary hlt]

/-! ## 8. The loop with `FiniteStone`: the complete characterisation -/

/-- **The two files meet.** `FiniteStone.unitaryGroup H t` IS `exp(i t H)` by definition, and that
file proves the FORWARD direction — group law, continuity, `dU/dt|₀ = iH`, and injectivity of
`H ↦ U`. This says every norm-continuous one-parameter group is one of those. -/
theorem exists_eq_unitaryGroup (U : ℝ → unitary A) (hc : ContinuousAt U 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃ H : selfAdjoint A, U = FiniteStone.unitaryGroup H := by
  obtain ⟨H, hH⟩ := exists_global_generator U hc hgrp
  exact ⟨H, funext fun t => by rw [hH t, FiniteStone.unitaryGroup]⟩

/-- **The complete characterisation, both directions.** A map `ℝ → unitary A` is a one-parameter
group continuous at `0` exactly when it is `t ↦ exp(i t H)` for a self-adjoint `H`, and by
`global_generator_unique` that `H` is unique. `←` is `FiniteStone`'s `unitaryGroup_add` and
`continuous_unitaryGroup`; `→` is this file's `exists_global_generator`. So
`FiniteStone.unitaryGroup` is a bijection from `selfAdjoint A` onto the norm-continuous
one-parameter groups: surjective here, injective there. -/
theorem eq_unitaryGroup_iff (U : ℝ → unitary A) :
    (ContinuousAt U 0 ∧ ∀ s t, U (s + t) = U s * U t)
      ↔ ∃ H : selfAdjoint A, U = FiniteStone.unitaryGroup H := by
  constructor
  · rintro ⟨hc, hgrp⟩
    exact exists_eq_unitaryGroup U hc hgrp
  · rintro ⟨H, rfl⟩
    exact ⟨(FiniteStone.continuous_unitaryGroup H).continuousAt,
      FiniteStone.unitaryGroup_add H⟩

/-! ## 9. The DERIVATIVE: `dU/dt = iH·U` with no generator supplied -/

/-- **Every norm-continuous one-parameter unitary group is differentiable, everywhere, and
satisfies `dU/dt = iH·U`.** `FiniteStone.hasDerivAt_unitaryGroup` proves this for the group BUILT
from `H`; composed with `exists_global_generator` it becomes a statement about an ARBITRARY such
group, whose generator was not given but recovered. The `H` here is the unique one of
`exists_unique_global_generator`, and the first conjunct says so. -/
theorem hasDerivAt_of_group (U : ℝ → unitary A) (hc : ContinuousAt U 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃ H : selfAdjoint A, (∀ t : ℝ, U t = expUnitary (t • H)) ∧
      ∀ t : ℝ, HasDerivAt (fun s => ((U s : A))) (Complex.I • (H : A) * ((U t : A))) t := by
  obtain ⟨H, hH⟩ := exists_global_generator U hc hgrp
  refine ⟨H, hH, fun t => ?_⟩
  have key := FiniteStone.hasDerivAt_unitaryGroup H t
  simp only [FiniteStone.unitaryGroup] at key
  simpa only [← hH] using key

/-- **And the generator IS the derivative at `0`: `H = −i · dU/dt|₀`.** This is the form the
classical statement takes, and the last conjunct is what makes it a recovery rather than a
coincidence: ANY `L` with `dU/dt|₀ = L` gives `H = −i L`, by uniqueness of the derivative and
`FiniteStone.generator_determined`. So the generator is not merely existent and unique — it is
COMPUTABLE from `U` by one differentiation. -/
theorem generator_eq_neg_I_smul_deriv (U : ℝ → unitary A) (hc : ContinuousAt U 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃ H : selfAdjoint A, (∀ t : ℝ, U t = expUnitary (t • H)) ∧
      HasDerivAt (fun s => ((U s : A))) (Complex.I • (H : A)) 0 ∧
      ∀ L : A, HasDerivAt (fun s => ((U s : A))) L 0 → (H : A) = -Complex.I • L := by
  obtain ⟨H, hH, hd⟩ := hasDerivAt_of_group U hc hgrp
  have h0 : HasDerivAt (fun s => ((U s : A))) (Complex.I • (H : A)) 0 := by
    have := hd 0
    rw [hH 0] at this
    simpa using this
  refine ⟨H, hH, h0, fun L hL => ?_⟩
  have hLeq : Complex.I • (H : A) = L := h0.unique hL
  rw [← hLeq, FiniteStone.generator_determined]

/-! ## 10. The boundary of the local statement -/

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
