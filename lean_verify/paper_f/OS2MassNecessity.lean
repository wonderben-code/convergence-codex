import GraphOS2
import GraphOS2Exponential
import FieldMassNecessity

/-!
# The mass hypothesis is necessary for OS2 too, and four headers of this chain had stopped saying so

**`UNLOCK_WATCHLIST` has asked since 2026-09-05 whether any chain OTHER than the rotation chain
states a result in prose without the hypothesis that makes it non-vacuous** — the class
`ERRATUM 455` found, where five consecutive headers dropped `m ≠ 0`. Its own `LIKELY OUTCOME`
says: *until somebody looks, the honest statement is that ONE chain was checked.* **The OS chain
has now been looked at, and it is the second instance.**

## The measurement

Twelve `OS`-named files in `paper_f`, every declaration's binders read and compared with the
header that names it. **Four files carry declarations taking `m ≠ 0` and never mention a mass
condition anywhere in their headers**: `GraphOS2` (8 such declarations), `OS2AnySide` (12),
`GraphOS2Exponential` (5) and `LatticeOS1` (3) — **28 declarations across four files**. The one
file that does say it, `SpectrumOS2Bridge`, is the newest and carries a *hypotheses, read off the
binders* paragraph, which is the practice `ERRATUM 455` left behind. The other seven `OS` files
take no mass hypothesis at all and are not in question.

## What is proved here, and it is the same repair `FieldMassNecessity` made

**`integral_pairing_zero`** — at `m = 0` the OS2 pairing integral is **exactly zero**, at every
graph, every reflection `θ` and every coefficient vector. `FieldMassNecessity.gaussianField_zero`
makes the field a point mass at the origin and the integrand vanishes there.

**`os2_measure_level_zero`** — **so OS2 holds at `m = 0` with NO hypotheses at all**: no
`ReflectionPositive`, no support condition, no property of the graph. That is what the dropped word
costs a reader — the summary *OS2 for the Gaussian field of any graph* is **true at `m = 0` as
well**, and trivially, for a reason with nothing to do with reflection.

**`not_os2_pos_single_zero`** — **and the STRICT form is FALSE there**, at every graph, connected
or not. `GraphOS2.os2_pos_single` concludes `0 < ∫ ···` on a connected graph at `m ≠ 0`; at
`m = 0` that integral is `0`, so the strict conclusion fails. **The hypothesis is not decoration in
either direction**: it makes the non-strict statement non-vacuous and the strict statement true.

**`os2_exponential_zero`** — the exponential form degenerates the same way: at `m = 0` the
integral is `(∑ c i) · conj (∑ c j)`, the squared modulus of the coefficient sum, at every `θ`
and every frequency family. Non-negative, and again for no reason involving the graph.

## What is NOT here

**NO HEADER IS REWRITTEN.** The four files carry dated notes and their prose is kept
(`ERRATUM 94`). Rewriting them would erase the evidence for the second instance, which is the
thing this unit measured.

**NO SCANNER.** `binder_scan.py` and `binderenv_scan.py` already build the mechanisable half and
both say in their own docstrings that deciding which omitted binders are MATERIAL cannot be
mechanised. This unit is the unmechanisable half done by hand on one chain, and **it is not
evidence about any other chain**: the Clifford chain and the curvature chain are unlooked-at
(2026-09-19).

**NOTHING ABOUT WHETHER `m = 0` IS INTERESTING.** It is not: the zero-mass field is a point mass
and this estate's objects are about `m ≠ 0`. What the theorems here buy is that a reader can tell
the interesting statement from the trivial one, which is exactly what `ERRATUM 455` says a summary
is for.

**NO WALL MOVES.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace OS2MassNecessity

open Matrix GraphLaplacian MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. At zero mass the pairing vanishes -/

/-- **THE OS2 PAIRING INTEGRAL IS EXACTLY ZERO AT ZERO MASS**, at every graph, every `θ` and every
coefficient vector. The field is a point mass at the origin
(`FieldMassNecessity.gaussianField_zero`) and every linear observable vanishes there. -/
theorem integral_pairing_zero [Nonempty V] {θ : V ≃ V} {c : V → ℝ} :
    ∫ ω, (∑ p, c p * ω (θ p)) * (∑ q, c q * ω q) ∂(gaussianField G 0) = 0 := by
  rw [FieldMassNecessity.gaussianField_zero, integral_dirac]
  simp

/-- **SO OS2 HOLDS AT ZERO MASS WITH NO HYPOTHESES AT ALL** — no `ReflectionPositive`, no support
condition, no property of the graph. Compare `GraphOS2.os2_measure_level`, which takes all three
and `m ≠ 0`: **this is what its summary sentence says when the mass condition is dropped from
it.** -/
theorem os2_measure_level_zero [Nonempty V] (θ : V ≃ V) (c : V → ℝ) :
    0 ≤ ∫ ω, (∑ p, c p * ω (θ p)) * (∑ q, c q * ω q) ∂(gaussianField G 0) :=
  le_of_eq (integral_pairing_zero (G := G)).symm

/-! ## 2. And the strict form is false there -/

/-- **THE STRICT STATEMENT FAILS AT ZERO MASS**, at every graph, connected or not.
`GraphOS2.os2_pos_single` concludes `0 < ∫ ···` from connectivity and `m ≠ 0`; the integral is
`0` here, so the hypothesis is load-bearing rather than decorative. -/
theorem not_os2_pos_single_zero [Nonempty V] (θ : V ≃ V) (p : V) :
    ¬ (0 < ∫ ω, (∑ r, (if r = p then (1:ℝ) else 0) * ω (θ r))
            * (∑ q, (if q = p then (1:ℝ) else 0) * ω q)
        ∂(gaussianField G 0)) := by
  rw [integral_pairing_zero (G := G)]
  exact lt_irrefl 0

/-! ## 3. The exponential form degenerates the same way -/

/-- **AT ZERO MASS THE EXPONENTIAL PAIRING IS THE SQUARED MODULUS OF THE COEFFICIENT SUM**, at
every `θ` and every frequency family: the graph, the reflection and the frequencies all drop out.
Compare `GraphOS2Exponential.os2_exponential`. -/
theorem os2_exponential_zero [Nonempty V] {θ : V ≃ V} {M : ℕ} (t : Fin M → V → ℝ)
    (c : Fin M → ℂ) :
    ∫ ω, (∑ i, c i * Complex.exp ((∑ p, t i p * ω (θ p) : ℝ) * Complex.I))
        * (starRingEnd ℂ) (∑ j, c j * Complex.exp ((∑ p, t j p * ω p : ℝ) * Complex.I))
        ∂(gaussianField G 0)
      = (∑ i, c i) * (starRingEnd ℂ) (∑ j, c j) := by
  rw [FieldMassNecessity.gaussianField_zero, integral_dirac]
  simp

/-! ## 4. And OS1's Schwinger functions vanish at positive order -/

/-- **EVERY SCHWINGER FUNCTION OF POSITIVE ORDER IS ZERO AT ZERO MASS.** So `LatticeOS1`'s
invariance statement is an identity between two zeros there, at every graph and every
automorphism. **At order zero it is an identity between two empty products**, which is why this is
stated at `k + 1`. -/
theorem schwinger_zero [Nonempty V] {k : ℕ} (p : Fin (k + 1) → V) :
    ∫ ω, ∏ i, ω (p i) ∂(gaussianField G 0) = 0 := by
  rw [FieldMassNecessity.gaussianField_zero, integral_dirac]
  simp

end OS2MassNecessity
