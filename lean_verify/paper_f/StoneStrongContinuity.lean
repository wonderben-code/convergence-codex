/-
  StoneStrongContinuity: **the sentence `StoneConverseCarriers`' header asserted, proved.**

  That file closed Stone's converse on five named carriers and then wrote, under WHAT IS **NOT**
  PROVED: *"on an infinite-dimensional `E` that hypothesis is a real restriction … `B(E)`-norm
  continuity of `U` is strictly stronger than the strong operator continuity the classical theorem
  assumes. **In FINITE dimension the two coincide**, so for `Mₙ(ℂ)`, `CascadeGNS.M4` and `ℂⁿ` this
  is the whole theorem."* The clause in bold was prose. **It is a theorem here**, and with it the
  converse holds on the finite-dimensional carriers under the hypothesis the physics actually
  supplies: continuity of `t ↦ U t ψ` for each state `ψ`, at the single point `0`.

  WHAT KIND OF DEEPENING THIS IS, STATED EXACTLY, BECAUSE "WEAKER HYPOTHESIS" WOULD OVERSTATE
  IT. The hypothesis is weakened in FORM and proved EQUIVALENT in substance: on a
  finite-dimensional carrier no group satisfies the new hypothesis and fails the old one, and
  `continuousAt_iff_pointwise` is exactly the theorem that says so. The gain is therefore not
  generality. It is that the estate's theorems now take the hypothesis an evolution law actually
  supplies — continuity of each orbit, at one point — instead of one about the operator norm that
  a reader has to convert by hand, and that the conversion is an object rather than a sentence in
  a header. A statement reachable only through prose is not reachable from Lean.

  `CompleteSpace E` IS NOT A RESTRICTION AND IS NOT DROPPABLE HERE. It follows from
  `FiniteDimensional ℂ E` (`FiniteDimensional.complete`), but it is a THEOREM and not an
  instance, so the `CStarAlgebra (E →L[ℂ] E)` instance that `selfAdjoint.expUnitary` needs cannot
  be synthesised without it and the statements in §2 carry it. §3 instantiates at `ℂⁿ`, where it
  IS an instance, and those statements carry neither it nor finite-dimensionality — which is the
  cleanest evidence that neither is doing work.

  WHAT IS PROVED.
  * **`opNorm_le_sum_basis`** — `‖T‖ ≤ ∑ᵢ ‖T eᵢ‖` over any orthonormal basis. Elementary, and it
    is the whole analytic content: it turns `n` scalar limits into one norm limit.
  * **`continuousAt_of_pointwise`** — for `E` finite-dimensional, if `t ↦ f t x` is continuous at
    `t₀` for every `x` then `t ↦ f t` is continuous at `t₀` in the OPERATOR NORM. Proved by
    squeezing `‖f t - f t₀‖` between `0` and a finite sum of scalar limits. The proof uses only
    the basis vectors — `continuousAt_of_pointwise_basis` — and that form takes FORMALLY less
    input while proving the same thing, since the three results together make the basis form, the
    `∀ x` form and norm continuity equivalent.
  * **`continuousAt_iff_pointwise`** — the header's clause, as a biconditional.
  * **`continuousAt_unitary_iff_pointwise`** — the same for `U : ℝ → unitary (E →L[ℂ] E)`, whose
    continuity is continuity into a SUBTYPE and needs the inducing bridge to be said at all.
  * **`exists_unique_global_generator_of_strong`**, **`eq_unitaryGroup_iff_strong`**,
    **`schrodinger_of_strong`** — Stone's converse, its characterisation and the Schrödinger
    equation, on any finite-dimensional complex inner-product space, from pointwise continuity at
    `0` and the group law. The generator is still unique and still `−i·dU/dt|₀`.
  * **`euclidean_*_of_strong`** — the same at `ℂⁿ`, where `CompleteSpace` is an instance rather
    than a hypothesis, so the statements carry no completeness assumption at all.

  WHAT IS **NOT** PROVED.
  * **Nothing about infinite dimension, and the boundary is real rather than a limit of the
    method.** On an infinite-dimensional `E` strong continuity does NOT imply norm continuity, the
    generator of a strongly continuous group is in general UNBOUNDED, and no theorem here or in
    `StoneConverseLocal` reaches it. **No counterexample is built either** — translation on
    `L²(ℝ)` is the standard one and costs a Fourier-side unit of its own — so what this file adds
    to the boundary is that the finite-dimensional side is now closed, not that the other side is
    exhibited.
  * **The C⋆ carriers keep the norm hypothesis.** `CascadeGNS.M4` and `Mₙ(ℂ)` are finite
    dimensional, so the analogous weakening holds there too, but the right weak hypothesis on a
    general C⋆-algebra is continuity of `t ↦ φ (U t)` for every state `φ`, not of `t ↦ U t ψ`, and
    the bridge for it is a basis of the DUAL rather than of the space. That is a separate lemma
    with the same shape and it is not written here; `opNorm_le_sum_basis` does not supply it.
  * **Nothing about the generator's spectrum, the Born rule, Gleason or Wigner.** Unchanged from
    `StoneConverseCarriers`.

  0 sorry. 0 new axioms. All declarations on `[propext, Classical.choice, Quot.sound]`.
-/

import StoneConverseCarriers

namespace StoneStrongContinuity

open scoped ComplexOrder

noncomputable section

/-! ## 1. Pointwise continuity is norm continuity in finite dimension -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **THE ANALYTIC CONTENT, AND IT IS ONE INEQUALITY.** The operator norm is bounded by the sum
of the norms of the images of an orthonormal basis. Nothing here needs completeness: the bound is
`‖T x‖ ≤ ∑ᵢ ‖⟪eᵢ, x⟫‖ ‖T eᵢ‖ ≤ (∑ᵢ ‖T eᵢ‖) ‖x‖`, with `‖⟪eᵢ, x⟫‖ ≤ ‖x‖` because `‖eᵢ‖ = 1`. -/
theorem opNorm_le_sum_basis [FiniteDimensional ℂ E] (T : E →L[ℂ] E) :
    ‖T‖ ≤ ∑ i, ‖T (stdOrthonormalBasis ℂ E i)‖ := by
  classical
  set b := stdOrthonormalBasis ℂ E with hb
  refine T.opNorm_le_bound (Finset.sum_nonneg fun i _ => norm_nonneg _) fun x => ?_
  calc ‖T x‖ = ‖T (∑ i, inner ℂ (b i) x • b i)‖ := by rw [b.sum_repr' x]
    _ = ‖∑ i, inner ℂ (b i) x • T (b i)‖ := by simp
    _ ≤ ∑ i, ‖(inner ℂ (b i) x : ℂ) • T (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖x‖ * ‖T (b i)‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have h := norm_inner_le_norm (𝕜 := ℂ) (b i) x
        simpa [b.norm_eq_one i] using h
    _ = (∑ i, ‖T (b i)‖) * ‖x‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **AND IT ONLY EVER NEEDS THE BASIS VECTORS.** Stated separately from the `∀ x` form because
the hypothesis is FORMALLY weaker — finitely many vectors rather than all of them — and the proof
is the same: `n` scalar limits squeeze one norm limit through `opNorm_le_sum_basis`. It is not
weaker in strength: this theorem plus `pointwise_of_continuousAt` makes the two EQUIVALENT, which
is worth saying rather than implying, since "weaker hypothesis" reads as "more general theorem"
and here it is the same theorem reached with less input. -/
theorem continuousAt_of_pointwise_basis [FiniteDimensional ℂ E] (f : ℝ → (E →L[ℂ] E)) (t₀ : ℝ)
    (hp : ∀ i, ContinuousAt (fun t => f t (stdOrthonormalBasis ℂ E i)) t₀) :
    ContinuousAt f t₀ := by
  classical
  set b := stdOrthonormalBasis ℂ E with hb
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hterm : ∀ i, Filter.Tendsto (fun t => ‖f t (b i) - f t₀ (b i)‖) (nhds t₀) (nhds 0) := by
    intro i
    have h : Filter.Tendsto (fun t => f t (b i) - f t₀ (b i)) (nhds t₀)
        (nhds (f t₀ (b i) - f t₀ (b i))) := (hp i).sub continuousAt_const
    simpa using h.norm
  have hsum : Filter.Tendsto (fun t => ∑ i, ‖f t (b i) - f t₀ (b i)‖) (nhds t₀) (nhds 0) := by
    simpa using tendsto_finset_sum Finset.univ fun i (_ : i ∈ Finset.univ) => hterm i
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) hsum
  simpa using opNorm_le_sum_basis (f t - f t₀)

/-- **The `∀ x` form**, which is how strong continuity is written. -/
theorem continuousAt_of_pointwise [FiniteDimensional ℂ E] (f : ℝ → (E →L[ℂ] E)) (t₀ : ℝ)
    (hp : ∀ x : E, ContinuousAt (fun t => f t x) t₀) : ContinuousAt f t₀ :=
  continuousAt_of_pointwise_basis f t₀ fun _ => hp _

/-- The easy direction: evaluation at a fixed vector is continuous, so norm continuity gives
pointwise continuity. No finite-dimensionality. -/
theorem pointwise_of_continuousAt (f : ℝ → (E →L[ℂ] E)) (t₀ : ℝ) (hc : ContinuousAt f t₀)
    (x : E) : ContinuousAt (fun t => f t x) t₀ :=
  ((ContinuousLinearMap.apply ℂ E x).continuous.continuousAt).comp hc

/-- **THE SENTENCE `StoneConverseCarriers`' HEADER ASSERTED.** In finite dimension the strong and
norm topologies ask the same continuity question of a one-parameter family. -/
theorem continuousAt_iff_pointwise [FiniteDimensional ℂ E] (f : ℝ → (E →L[ℂ] E)) (t₀ : ℝ) :
    ContinuousAt f t₀ ↔ ∀ x : E, ContinuousAt (fun t => f t x) t₀ :=
  ⟨fun hc x => pointwise_of_continuousAt f t₀ hc x, continuousAt_of_pointwise f t₀⟩

/-- Continuity into `unitary A` is continuity into a SUBTYPE, and the subtype carries the induced
topology, so it is exactly continuity of the coercion. Needed because every statement below has a
`unitary` on the outside. -/
theorem continuousAt_unitary_of_coe {A : Type*} [NormedRing A] [StarRing A]
    (U : ℝ → unitary A) (t₀ : ℝ) (h : ContinuousAt (fun t => ((U t : A))) t₀) :
    ContinuousAt U t₀ := by
  have hind : Topology.IsInducing (fun u : unitary A => (u : A)) :=
    Topology.IsEmbedding.subtypeVal.isInducing
  exact (hind.continuousAt_iff).2 h

/-- The two put together, for a one-parameter family of unitaries. -/
theorem continuousAt_unitary_iff_pointwise [FiniteDimensional ℂ E] [CompleteSpace E]
    (U : ℝ → unitary (E →L[ℂ] E)) (t₀ : ℝ) :
    ContinuousAt U t₀ ↔ ∀ x : E, ContinuousAt (fun t => ((U t : E →L[ℂ] E)) x) t₀ := by
  refine ⟨fun hc x => ?_, fun hp => continuousAt_unitary_of_coe U t₀ ?_⟩
  · exact pointwise_of_continuousAt _ t₀ (continuousAt_subtype_val.comp hc) x
  · exact continuousAt_of_pointwise (fun t => ((U t : E →L[ℂ] E))) t₀ hp

/-! ## 2. Stone's converse under strong continuity -/

set_option synthInstance.maxHeartbeats 400000 in
-- `HSMul ℝ (selfAdjoint (E →L[ℂ] E))` needs more than the 20000 default, measured in
-- `ERRATUM 594`: 20000 fails and 21000 succeeds, so this is headroom on a 5% shortfall.
/-- **STONE'S CONVERSE FROM STRONG CONTINUITY.** On a finite-dimensional complex inner-product
space, a one-parameter group of unitaries whose orbits `t ↦ U t ψ` are merely continuous at `0`
has a unique self-adjoint generator. The hypothesis is the one an evolution law supplies; the
conclusion is `StoneConverseCarriers.operator_exists_unique_generator`'s. -/
theorem exists_unique_global_generator_of_strong [FiniteDimensional ℂ E] [CompleteSpace E]
    (U : ℝ → unitary (E →L[ℂ] E))
    (hp : ∀ x : E, ContinuousAt (fun t => ((U t : E →L[ℂ] E)) x) 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃! H : selfAdjoint (E →L[ℂ] E), ∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H) :=
  StoneConverseCarriers.operator_exists_unique_generator U
    ((continuousAt_unitary_iff_pointwise U 0).2 hp) hgrp

set_option synthInstance.maxHeartbeats 400000 in
-- Same shortfall (`ERRATUM 594`).
/-- **And the characterisation, so the weakened hypothesis is forced and not merely sufficient.**
Being a `FiniteStone.unitaryGroup` is equivalent to the group law plus continuity of the ORBITS at
one point. -/
theorem eq_unitaryGroup_iff_strong [FiniteDimensional ℂ E] [CompleteSpace E]
    (U : ℝ → unitary (E →L[ℂ] E)) :
    ((∀ x : E, ContinuousAt (fun t => ((U t : E →L[ℂ] E)) x) 0) ∧
        ∀ s t, U (s + t) = U s * U t)
      ↔ ∃ H : selfAdjoint (E →L[ℂ] E), U = FiniteStone.unitaryGroup H := by
  rw [← StoneConverseCarriers.operator_eq_unitaryGroup_iff U]
  exact and_congr_left' (continuousAt_unitary_iff_pointwise U 0).symm

set_option synthInstance.maxHeartbeats 400000 in
-- Same shortfall (`ERRATUM 594`).
/-- **THE SCHRÖDINGER EQUATION FROM STRONG CONTINUITY.** No generator is supplied and no norm
continuity is assumed: the orbits' continuity at `0` and the group law produce the `H` and the
equation `dψ/dt = iHψ` along every orbit. -/
theorem schrodinger_of_strong [FiniteDimensional ℂ E] [CompleteSpace E]
    (U : ℝ → unitary (E →L[ℂ] E))
    (hp : ∀ x : E, ContinuousAt (fun t => ((U t : E →L[ℂ] E)) x) 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃ H : selfAdjoint (E →L[ℂ] E), (∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H)) ∧
      ∀ (ψ : E) (t : ℝ),
        HasDerivAt (fun s => ((U s : E →L[ℂ] E)) ψ)
          ((Complex.I • (H : E →L[ℂ] E) * ((U t : E →L[ℂ] E))) ψ) t :=
  StoneConverseCarriers.operator_schrodinger U
    ((continuousAt_unitary_iff_pointwise U 0).2 hp) hgrp

end

/-! ## 3. At `ℂⁿ`, with no completeness hypothesis to carry -/

section Euclidean

noncomputable section

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
-- Same shortfall (`ERRATUM 594`).
/-- **At `ℂⁿ`.** `CompleteSpace` and `FiniteDimensional` are both instances here, so the
statement carries neither: the whole hypothesis is the group law and the continuity of each orbit
at `0`. This is the carrier `FiniteStone.cascade_schrodinger` uses for the forward direction. -/
theorem euclidean_exists_unique_generator_of_strong
    (U : ℝ → unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
    (hp : ∀ x : EuclideanSpace ℂ (Fin n),
      ContinuousAt (fun t =>
        ((U t : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) x) 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃! H : selfAdjoint (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
      ∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H) :=
  exists_unique_global_generator_of_strong U hp hgrp

set_option synthInstance.maxHeartbeats 400000 in
-- Same shortfall (`ERRATUM 594`).
/-- **And the Schrödinger equation at `ℂⁿ`**, from the orbits alone. -/
theorem euclidean_schrodinger_of_strong
    (U : ℝ → unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
    (hp : ∀ x : EuclideanSpace ℂ (Fin n),
      ContinuousAt (fun t =>
        ((U t : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) x) 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃ H : selfAdjoint (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
      (∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H)) ∧
      ∀ (ψ : EuclideanSpace ℂ (Fin n)) (t : ℝ),
        HasDerivAt
          (fun s => ((U s : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) ψ)
          ((Complex.I • (H : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
            * ((U t : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))) ψ) t :=
  schrodinger_of_strong U hp hgrp

end

end Euclidean

end StoneStrongContinuity
