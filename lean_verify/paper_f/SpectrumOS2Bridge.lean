import FieldTwinSpectrum

/-!
# A hypothesis about the spectrum, a conclusion about the axiom, and the implication is one-way

Two corners of this estate have been built independently and have never referenced each other.
`GreenDisconnected` proved that the two-point function is strictly positive **exactly** between
sites joined by a path, and that OS2's inequality at a singleton half is strict **exactly** when the
site reaches its own mirror. `FieldSimpleConnected` proved that a simple spectrum — of the
Laplacian, or of the propagator — forces the graph to be **connected**. As of 2026-09-06 the four
theorems of the first are used **only inside their own file**, and
`preconnected_of_eigenvalues_injective` likewise; **nothing composes them.**

Composed, they say something neither says alone: **a hypothesis about a spectrum forces an
Osterwalder–Schrader property of the measure.**

## What is proved

**`twoPoint_pos_of_finrank_le_one`, `os2_pos_single_of_finrank_le_one`** — **if every eigenspace
of the graph Laplacian is at most a line, then the two-point function is strictly positive at
every pair of sites, and OS2's inequality is strict at every single-site half.** The
**spectral** hypothesis is pure graph combinatorics — `∀ ν, finrank (ker (L − ν)) ≤ 1` names no
mass, no propagator and no measure — and the conclusion is about the Gaussian measure; `m ≠ 0`
is taken besides, and is read off the binders below. **The `θ` is an arbitrary permutation of
the sites, not a reflection**: neither involutivity nor adjacency-preservation is assumed
anywhere here, so these are stronger than the reflection statements they are named for.

**`twoPoint_pos_of_eigenvalues_injective`, `os2_pos_single_of_eigenvalues_injective`** — the same
from a **simple propagator spectrum**, which is the hypothesis the symmetry chain runs on.

**`not_finrank_le_one_of_twoPoint_eq_zero`, `not_eigenvalues_injective_of_twoPoint_eq_zero`,
`not_finrank_le_one_of_os2_not_strict`, `not_eigenvalues_injective_of_os2_not_strict`** — the
contrapositives, and they are the sharper reading: **if the two-point function fails to be strictly
positive at a single pair, or OS2 degenerates at a single site, the spectrum is degenerate.** One
site of one graph is enough to force a global spectral statement.

**`twinGraph_os2_strict`, `os2_strict_but_spectrum_degenerate`** — **and the implication does not
reverse.** `FieldTwinSpectrum.twinGraph` is **connected** (`twinGraph_connected`, which is the only
property of it used here — it is also acyclic, and that is a description and not something this
estate proves), so OS2 is strict at every one of its sites, and its Laplacian spectrum is
**degenerate**
(`FieldTwinSpectrum.not_injective_lapMatrix_eigenvalues`). So a degenerate spectrum does **not**
force OS2 to degenerate, and the bridge above runs one way only. **The gap is exhibited, not
merely allowed for.**

## What is NOT here

**THIS IS OS2 AT SINGLE-SITE HALVES, NOT OS2.** The statement proved is
`GraphOS2.integral_pairing_refl_single`'s inequality at a **singleton** half with the indicator of
one site. **Nothing here is about a general half, a general observable, or the full axiom**, and
the strictness of OS2 in its real form is untouched. Not attempted, no cost claimed
(`ERRATUM 246`).

**NOTHING IS ADDED TO EITHER CORNER.** Every theorem here is a composition of two existing ones,
and **no new mathematics is claimed** — what is new is that the composition exists at all. The one
statement with content of its own is the non-implication, and its content is a graph.

**NO CHARACTERISATION.** *Simple spectrum* is sufficient for the conclusion and, by the tree, **not
necessary**. What is necessary is exactly reachability, which `GreenDisconnected` already had; this
file adds a sufficient condition stated in spectral terms and **says plainly that it is not the
right one**.

**NO WALL MOVES.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. A
strictness statement at singleton halves on a finite graph is not `OS2` in the sense the wall
tracks, and **deriving a known strictness from a stronger hypothesis is not progress on it**.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): every theorem takes `m ≠ 0`, because
`gaussianField` is a point mass at `m = 0` and the propagator does not exist. The Laplacian-side
hypothesis takes **no mass in itself** — `∀ ν, finrank (ker (L − ν)) ≤ 1` mentions neither mass nor
propagator — and that is the point of stating the bridge from that side first.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace SpectrumOS2Bridge

open Matrix GraphLaplacian GreenDisconnected FieldSimpleConnected

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. From a hypothesis about the Laplacian to a property of the measure -/

/-- **EVERY EIGENSPACE A LINE FORCES STRICT POSITIVE CORRELATION AT EVERY PAIR.** -/
theorem twoPoint_pos_of_finrank_le_one (hm : m ≠ 0)
    (hdim : ∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) (p q : V) :
    0 < ∫ ω, ω p * ω q ∂(gaussianField G m) :=
  (twoPoint_pos_iff_reachable G hm p q).mpr (preconnected_of_finrank_le_one hdim p q)

/-- **AND OS2's INEQUALITY IS STRICT AT EVERY SINGLE-SITE HALF, FOR EVERY PERMUTATION OF THE
SITES** — `θ` is not assumed involutive and not assumed to preserve adjacency. -/
theorem os2_pos_single_of_finrank_le_one (hm : m ≠ 0)
    (hdim : ∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) (θ : V ≃ V) (p : V) :
    0 < ∫ ω, (∑ r, (if r = p then (1 : ℝ) else 0) * ω (θ r))
            * (∑ q, (if q = p then (1 : ℝ) else 0) * ω q) ∂(gaussianField G m) :=
  (os2_pos_single_iff_reachable G hm θ p).mpr (preconnected_of_finrank_le_one hdim (θ p) p)

/-! ## 2. And from a simple propagator spectrum, which is what the symmetry chain runs on -/

theorem twoPoint_pos_of_eigenvalues_injective (hm : m ≠ 0) (hH : (green G m).IsHermitian)
    (hsimple : Function.Injective hH.eigenvalues) (p q : V) :
    0 < ∫ ω, ω p * ω q ∂(gaussianField G m) :=
  (twoPoint_pos_iff_reachable G hm p q).mpr
    (preconnected_of_eigenvalues_injective hm hH hsimple p q)

/-- **A SIMPLE PROPAGATOR SPECTRUM FORCES OS2's INEQUALITY TO BE STRICT AT EVERY SINGLE SITE.** -/
theorem os2_pos_single_of_eigenvalues_injective (hm : m ≠ 0) (hH : (green G m).IsHermitian)
    (hsimple : Function.Injective hH.eigenvalues) (θ : V ≃ V) (p : V) :
    0 < ∫ ω, (∑ r, (if r = p then (1 : ℝ) else 0) * ω (θ r))
            * (∑ q, (if q = p then (1 : ℝ) else 0) * ω q) ∂(gaussianField G m) :=
  (os2_pos_single_iff_reachable G hm θ p).mpr
    (preconnected_of_eigenvalues_injective hm hH hsimple (θ p) p)

/-! ## 3. The contrapositives: one site forces a global spectral statement -/

theorem not_finrank_le_one_of_twoPoint_eq_zero (hm : m ≠ 0) {p q : V}
    (h : ¬ (0 < ∫ ω, ω p * ω q ∂(gaussianField G m))) :
    ¬ (∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) :=
  fun hdim => h (twoPoint_pos_of_finrank_le_one hm hdim p q)

theorem not_eigenvalues_injective_of_twoPoint_eq_zero (hm : m ≠ 0)
    (hH : (green G m).IsHermitian) {p q : V}
    (h : ¬ (0 < ∫ ω, ω p * ω q ∂(gaussianField G m))) :
    ¬ Function.Injective hH.eigenvalues :=
  fun hsimple => h (twoPoint_pos_of_eigenvalues_injective hm hH hsimple p q)

theorem not_finrank_le_one_of_os2_not_strict (hm : m ≠ 0) {θ : V ≃ V} {p : V}
    (h : ¬ (0 < ∫ ω, (∑ r, (if r = p then (1 : ℝ) else 0) * ω (θ r))
            * (∑ q, (if q = p then (1 : ℝ) else 0) * ω q) ∂(gaussianField G m))) :
    ¬ (∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) :=
  fun hdim => h (os2_pos_single_of_finrank_le_one hm hdim θ p)

/-- **OS2 DEGENERATING AT ONE SITE FORCES THE WHOLE PROPAGATOR SPECTRUM TO BE DEGENERATE.** -/
theorem not_eigenvalues_injective_of_os2_not_strict (hm : m ≠ 0) (hH : (green G m).IsHermitian)
    {θ : V ≃ V} {p : V}
    (h : ¬ (0 < ∫ ω, (∑ r, (if r = p then (1 : ℝ) else 0) * ω (θ r))
            * (∑ q, (if q = p then (1 : ℝ) else 0) * ω q) ∂(gaussianField G m))) :
    ¬ Function.Injective hH.eigenvalues :=
  fun hsimple => h (os2_pos_single_of_eigenvalues_injective hm hH hsimple θ p)

/-! ## 4. And the implication does not reverse -/

open FieldTwinSpectrum in
/-- The graph is connected, so OS2 is strict at every one of its sites. -/
theorem twinGraph_os2_strict {mass : ℝ} (hmass : mass ≠ 0) (θ : Fin 8 ≃ Fin 8) (p : Fin 8) :
    0 < ∫ ω, (∑ r, (if r = p then (1 : ℝ) else 0) * ω (θ r))
            * (∑ q, (if q = p then (1 : ℝ) else 0) * ω q) ∂(gaussianField twinGraph mass) :=
  os2_pos_single_of_connected twinGraph twinGraph_connected hmass θ p

open FieldTwinSpectrum in
/-- **A DEGENERATE SPECTRUM DOES NOT FORCE OS2 TO DEGENERATE.** On the tree of
`FieldTwinSpectrum` both halves hold at once, so §§1–2 run one way only and the converse of
`not_eigenvalues_injective_of_os2_not_strict` is **false**. -/
theorem os2_strict_but_spectrum_degenerate {mass : ℝ} (hmass : mass ≠ 0) :
    (∀ (θ : Fin 8 ≃ Fin 8) (p : Fin 8),
        0 < ∫ ω, (∑ r, (if r = p then (1 : ℝ) else 0) * ω (θ r))
                * (∑ q, (if q = p then (1 : ℝ) else 0) * ω q) ∂(gaussianField twinGraph mass))
      ∧ ¬ Function.Injective
            (FieldSimpleConverse.lapMatrix_isHermitian twinGraph).eigenvalues :=
  ⟨fun θ p => twinGraph_os2_strict hmass θ p, not_injective_lapMatrix_eigenvalues⟩

end SpectrumOS2Bridge
