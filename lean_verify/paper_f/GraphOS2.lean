/-
  GraphOS2.lean — measure-level reflection positivity for the lattice
  Gaussian field.

  WHY. Two documents in this estate name this unit, and one of them names it
  with a sentence that is now false.

  `LatticeField.lean` attempted the "OS2 packaging applies verbatim" claim
  and delivered a split verdict: the Gaussian-moments layer transferred, and
  `integral_pairing` / `os2_measure_level` did not, because — its words —
  **"THERE IS NO REFLECTION ON `Site n` AT ALL."** That was true when it was
  written. `LatticeReflection` then built the reflection, and
  `LatticeReflectionPositive` proved the covariance-level statement. **The
  stated obstruction is gone**, and ERRATUM 48's rule — when a file says "X
  is impossible because Y", and Y stops holding, attempt X — is what this
  file is.

  `WALLS.md` W1 and `GraphReflectionPositive` both record, as a NON-closure,
  that what is proved is about the covariance and not about the measure.
  This is that non-closure, for linear observables.

  WHAT THIS FILE PROVES:
  1. **`integral_pairing`** — for the Gaussian field of ANY finite graph, the
     integral of a product of two linear observables is the Green function
     contracted against their coefficients:
     `∫ (∑ c p ω p)(∑ d q ω q) = ∑∑ c p · d q · G(p,q)`.
  2. **`integral_pairing_refl`** — hence, with one observable composed with a
     reflection, the integral is EXACTLY the quadratic form appearing in
     `GraphReflection.ReflectionPositive`. Not an analogue of it: the same
     expression.
  3. **`os2_measure_level`** — **so measure-level OS2 is the covariance-level
     theorem, with nothing left over.** For any graph, any reflection, any
     half on which reflection positivity holds, and any coefficient family
     supported there, the reflected pairing has non-negative integral.
  4. **§3, the instances**: `os2_box` on the `d`-dimensional box of even
     side, **`os2_box_four`** in four dimensions, and **`os2_lattice`** on
     the estate's own `Fin n × Fin n` box against
     `LatticeField.latticeField` — the measure that file constructed and
     could not pair.
  5. **§4, non-degeneracy.** `integral_pairing_refl_single` computes the
     pairing at one site as `G(θp, p)`, and `os2_pos_single` shows it
     STRICTLY positive on a connected graph. Recorded because a
     non-negativity theorem whose integral is identically zero would be
     worthless, and because `LatticeReflection.reflectionPositive_empty` is
     on record as a warning that this family of statements has a degenerate
     corner.

  WHAT THIS DOES NOT DO.
  * **Linear observables only.** The OU-product programme needed four more
    files (`SchurExponential` → `OS2ExpKernel` → `OS2Exponential`) to reach
    the exponential algebra, which is the OS2 axiom as physics states it.
    **None of that is redone here and none of it transfers for free** — it
    consumed the Schur product theorem on the reflected kernel, and whether
    the lattice Green function's reflected kernel is PSD in that entrywise
    sense is a question this file does not ask.
  * **Even side, first coordinate.** Inherited verbatim from
    `LatticeReflectionPositive`; nothing here weakens or strengthens them.
  * **No infinite-volume limit, no continuum limit.** W2 is untouched.
  * **This is not a Gibbs measure.** The field here is Gaussian and free.
    The Peierls/Ruelle/Wilson citations that `_proof_004_logos` carries are
    about interacting lattice spin and gauge systems, and nothing in this
    file bears on them.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import LatticeReflectionPositive
import GraphGreenPositive

namespace GraphOS2

open Finset MeasureTheory ProbabilityTheory GraphLaplacian

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The pairing of two linear observables

`OS2MeasureLevel.integral_pairing` is this for the OU-product field. The
proof is the same shape — expand, exchange sum and integral, apply the
two-point function — and the reason it is written again rather than reused is
that that file's `fieldMeasure` is hard-wired to `prodCov` and is not generic
in the kernel, which is the specific finding `LatticeField` recorded.
-/

/-- **THE PAIRING IS THE GREEN FUNCTION, CONTRACTED.** -/
theorem integral_pairing (hm : m ≠ 0) (c d : V → ℝ) :
    ∫ ω, (∑ p, c p * ω p) * (∑ q, d q * ω q) ∂(gaussianField G m)
      = ∑ p, ∑ q, c p * d q * green G m p q := by
  have hexp : ∀ ω : EuclideanSpace ℝ V,
      (∑ p, c p * ω p) * (∑ q, d q * ω q)
        = ∑ p, ∑ q, (c p * d q) * (ω p * ω q) := by
    intro ω
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  simp_rw [hexp]
  have hterm : ∀ a b : V,
      Integrable (fun ω : EuclideanSpace ℝ V => ω a * ω b) (gaussianField G m) :=
    fun a b => (memLp_eval G m a).integrable_mul (memLp_eval G m b)
  rw [integral_finset_sum _ (fun p _ =>
    integrable_finset_sum _ (fun q _ => (hterm p q).const_mul (c p * d q)))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finset_sum _ (fun q _ => (hterm p q).const_mul (c p * d q))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_const_mul, twoPoint G hm p q]

/-! ## 2. The reflected pairing IS the covariance-level form -/

/-- **THE REFLECTED PAIRING.** Composing one observable with the reflection
    produces, on the nose, the double sum that
    `GraphReflection.ReflectionPositive` asserts non-negative. The whole
    content of §3 is that this is an equality and not a resemblance. -/
theorem integral_pairing_refl (hm : m ≠ 0) (θ : V ≃ V) (c : V → ℝ) :
    ∫ ω, (∑ p, c p * ω (θ p)) * (∑ q, c q * ω q) ∂(gaussianField G m)
      = ∑ p, ∑ q, c p * c q * green G m (θ p) q := by
  have hre : ∀ ω : EuclideanSpace ℝ V,
      (∑ p, c p * ω (θ p)) = ∑ p, c (θ.symm p) * ω p := fun ω =>
    (Finset.sum_congr rfl fun p _ => by rw [Equiv.symm_apply_apply]).trans
      (Equiv.sum_comp θ (fun p => c (θ.symm p) * ω p))
  simp_rw [hre]
  rw [integral_pairing G hm]
  refine (Equiv.sum_comp θ
    (fun p => ∑ q, c (θ.symm p) * c q * green G m p q)).symm.trans ?_
  exact Finset.sum_congr rfl fun p _ =>
    Finset.sum_congr rfl fun q _ => by rw [Equiv.symm_apply_apply]

/-- **MEASURE-LEVEL OS2 FOR THE GAUSSIAN FIELD OF ANY GRAPH**, for linear
    observables: covariance-level reflection positivity is exactly the
    statement about the measure, with no gap between them.

    `LatticeField` was right that its packaging did not transfer, and right
    about why — there was no reflection. It was one step from the whole
    thing, and the step was not in this layer. -/
theorem os2_measure_level (hm : m ≠ 0) {θ : V ≃ V} {H : Finset V}
    (hrp : GraphReflection.ReflectionPositive G m θ H)
    {c : V → ℝ} (hc : ∀ p, p ∉ H → c p = 0) :
    0 ≤ ∫ ω, (∑ p, c p * ω (θ p)) * (∑ q, c q * ω q) ∂(gaussianField G m) := by
  rw [integral_pairing_refl G hm]
  exact hrp c hc

/-! ## 3. The boxes -/

section Boxes

open BoxGraph GraphHalfSpace IsingFiniteVolume LatticeReflectionPositive

variable {d n : ℕ}

/-- Measure-level OS2 on the `d`-dimensional box of even side. -/
theorem os2_box (i : Fin d) (hn : Even n) (hm : m ≠ 0)
    {c : BoxGraph.Site d n → ℝ} (hc : ∀ p, p ∉ lowerHalf i n → c p = 0) :
    0 ≤ ∫ ω, (∑ p, c p * ω (GraphReflection.revSite (n := n) i p)) * (∑ q, c q * ω q)
        ∂(gaussianField (boxGraph d n) m) :=
  os2_measure_level _ hm
    (GraphReflectionPositive.reflectionPositive_box i hn hm) hc

/-- **AND IN FOUR DIMENSIONS.** -/
theorem os2_box_four (i : Fin 4) (hn : Even n) (hm : m ≠ 0)
    {c : BoxGraph.Site 4 n → ℝ} (hc : ∀ p, p ∉ lowerHalf i n → c p = 0) :
    0 ≤ ∫ ω, (∑ p, c p * ω (GraphReflection.revSite (n := n) i p)) * (∑ q, c q * ω q)
        ∂(gaussianField (boxGraph 4 n) m) :=
  os2_box i hn hm hc

/-- **THE ESTATE'S OWN FIELD, PAIRED.** `LatticeField.latticeField` is the
    measure that file built and then could not reflect. This is measure-level
    OS2 against it, for every region on either side of the first-coordinate
    cut. -/
theorem os2_lattice (hn : Even n) (hm : m ≠ 0)
    {half : Finset (IsingFiniteVolume.Site n)}
    (hlow : half ⊆ lowerHalfPair n ∨ half ⊆ (lowerHalfPair n)ᶜ)
    {c : IsingFiniteVolume.Site n → ℝ} (hc : ∀ p, p ∉ half → c p = 0) :
    0 ≤ ∫ ω, (∑ p, c p * ω (LatticeReflection.refl n p)) * (∑ q, c q * ω q)
        ∂(LatticeField.latticeField n m) := by
  rw [GraphLaplacian.latticeField_box]
  refine os2_measure_level _ hm ?_ hc
  rw [GraphReflection.reflectionPositive_box n m half]
  rcases hlow with h | h
  · exact reflectionPositive_lattice hn hm h
  · exact reflectionPositive_lattice_compl hn hm h

end Boxes

/-! ## 4. It is not identically zero

`LatticeReflection.reflectionPositive_empty` is recorded in that file as a
WARNING: the covariance-level statement has a corner where it holds because
the coefficients are forced to vanish. The measure-level statement inherits
that corner, so the same discipline applies — exhibit an instance where the
integral is a definite positive number, and say what makes it positive.
-/

/-- The pairing at a single site is the propagator joining that site to its
    mirror. -/
theorem integral_pairing_refl_single (hm : m ≠ 0) (θ : V ≃ V) (p : V) :
    ∫ ω, (∑ r, (if r = p then (1:ℝ) else 0) * ω (θ r)) * (∑ q, (if q = p then (1:ℝ) else 0) * ω q)
        ∂(gaussianField G m) = green G m (θ p) p := by
  classical
  rw [integral_pairing_refl G hm]
  simp

/-- **AND ON A CONNECTED GRAPH IT IS STRICTLY POSITIVE**, so §2's inequality
    is not `0 ≤ 0`. The strictness comes from `GraphGreenPositive.green_pos`,
    which is the maximum principle — every entry of the massive Green
    function is positive — and not from anything about reflections. -/
theorem os2_pos_single (hG : G.Connected) (hm : m ≠ 0) (θ : V ≃ V) (p : V) :
    0 < ∫ ω, (∑ r, (if r = p then (1:ℝ) else 0) * ω (θ r))
            * (∑ q, (if q = p then (1:ℝ) else 0) * ω q)
        ∂(gaussianField G m) := by
  rw [integral_pairing_refl_single G hm]
  exact GraphGreenPositive.green_pos G hG hm (θ p) p

/-! ## 5. Review round 85 — the ways this could be hollow

**"Is the equality in §2 doing any work, or is it a rearrangement?"** It is a
rearrangement, and that is the finding rather than an admission. The question
this unit existed to answer was whether the gap between covariance level and
measure level for THIS covariance is a gap at all, and the answer is that for
linear observables it is not: the integral IS the double sum, by the
two-point function and the linearity of the integral. **`LatticeField`'s
verdict is thereby completed rather than contradicted** — it said the
packaging failed for want of a reflection, and once the reflection exists the
packaging goes through. What would have made this unit a surprise is if it
had NOT, and that possibility was live: the OU-product programme needed four
files to get from a positive kernel to the OS2 axiom.

**"Then why is the exponential layer not here?"** Because the four files that
carried it for the OU field do not obviously transfer, and asserting they
would is the exact move this project keeps catching. `OS2ExpKernel` needs the
entrywise exponential of the REFLECTED kernel to be positive semidefinite,
via the Schur product theorem; the reflected kernel there is
`exp(−Δ|zᵢ − θzⱼ|)`, a product over coordinates, and the lattice Green
function is not a product over anything. **Whether the Schur route applies is
an open question and this file does not touch it.** Stating the linear layer
and stopping is the honest boundary.

**"`os2_lattice` takes a disjunction — is that a weakened statement?"** It is
the strongest form available, and the disjunction is not a hedge but the
shape of the mathematics: reflection positivity is a statement about
coefficients on ONE side of the cut, so a region must be on one side or the
other, and a region straddling the cut is a different — generally false —
assertion. `LatticeReflectionPositive.ReflectionPositive.mirror` is what makes
the second disjunct available at all.

**"Could the non-degeneracy be vacuous?"** No, and §4 spends a real theorem
on it: the pairing at a single site is computed exactly, and
`GraphGreenPositive.green_pos` makes it strictly positive on any connected
graph. **The strictness has nothing to do with the reflection** — it is the
maximum principle — and saying so matters, because a reader could otherwise
read §4 as evidence about reflections when it is evidence about propagators.

**"How much of OS is this now?"** One axiom, one covariance, one finite box,
linear observables, even side, one coordinate direction. The Gaussian field
here is free; the citations the estate's `_proof_004_logos` carries are about
interacting systems, and nothing here moves them. **What HAS changed since
this morning is the layer, not the scope**: the same single statement is now
true of the measure and not only of the kernel.
-/

end GraphOS2
