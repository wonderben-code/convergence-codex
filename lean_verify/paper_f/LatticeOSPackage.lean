import LatticeRegularity
import LatticeOS1
import LatticeReflectionPositive

/-!
# The finite-volume OS shadows, named by what they say and not by their number

`ERRATUM 320` found that this estate numbers the Osterwalder–Schrader axioms **three** ways —
`F3_9d` and the watchlist put regularity at `OS0` and covariance at `OS1`;
`CascadeFoundation.OSVerification`, `F4_3f` and `F4_4a` put regularity at `OS5`;
`FieldAutInvariance` alone puts Euclidean invariance at `OS3` — and that a watchlist clause asking
for one of them stood open for eighteen days because the theorem answering it was filed under a
different number. `ASSUMPTIONS 50` sends the choice of numbering to the author.

**This file is the conservative reading of that decision: it names the properties by their content
and gives no number at all.** Nothing here has to be rewritten whichever way the author rules, and
nothing here can drift the way a numbered docstring drifted.

## The table

**Nineteen files of `paper_f` carry an explicit *"this is not OS`n`"* disclaimer, twenty-three
occurrences in all** — counted with `grep -o 'is not OS[0-9]\|IS NOT OS[0-9]' *.lean`, not
estimated, after a first draft of this header said *"four"* from memory and was wrong.
`FieldAutInvariance` alone has three. Every one of those disclaimers is correct and load-bearing,
and **this file does not replace any of them**: they stay where they are, attached to the theorems
they qualify. What this file adds is one place where the properties are named **without a number**,
so that the naming cannot drift the way `ERRATUM 320`'s did.

The four rows below are the properties, not the files:

| property, by content | finite-volume form | who proves it | the continuum statement it is NOT |
|---|---|---|---|
| regularity | `RegularFinVol` | `LatticeRegularity.generatingFunctional_le` | a bound on
Schwartz test functions yielding a distribution-valued measure |
| Euclidean covariance | `LatticeOS1.EuclideanCovariantFinVol` |
`LatticeOS1.gaussianField_euclideanCovariantFinVol` | covariance of continuum Schwinger
functions under `E(d)` |
| reflection positivity | `GraphReflection.ReflectionPositive` |
`LatticeReflectionPositive.reflectionPositive_lattice` | positivity of the continuum OS pairing |
| clustering | **not bundled — see below** | — | — |

## What is proved

> **`RegularFinVol G m`** — the generating functional is bounded by `exp(‖f‖²/(2m²))` at every `f`,
> **a constant naming no graph**. `LatticeRegularity` proves the inequality; this names it.
>
> **`gaussianField_shadows`** — the lattice field satisfies regularity **and** covariance, at every
> finite graph and every nonzero mass, with no hypothesis beyond `m ≠ 0`. The two that hold
> unconditionally, in one statement.
>
> **`gaussianField_shadows_rp`** — and reflection positivity too, on the box, given the reflection
> data those statements need. Kept separate **because its hypotheses are real**: a side length, an
> `Even n`, and a half contained in `lowerHalfPair n`. Bundling a conditional statement with two
> unconditional ones would hide exactly the thing a reader needs to see.

## What is NOT here, and why each is out

**Clustering is not bundled.** `GreenClustering.cross_abs_le` and
`LatticeHigherClustering.odd_pattern_abs_le` are real theorems, and both carry hypotheses — a
uniform degree bound `Δ`, a separation, an `ε`. There is no unconditional finite-volume clustering
statement to name, and **inventing a `Prop` whose only instance needs three side conditions would
make the package look more complete than the estate is.** It is named as absent rather than
manufactured.

**Permutation symmetry is not bundled** either: the estate has no statement of it for
`gaussianField`, and this file does not add one.

**None of these is the axiom it shadows.** Each row of the table above names the continuum
statement it is not, and the four originating files keep their own cautions verbatim. A finite
graph has no `E(d)`, no Schwartz space and no infinite volume; **a package of finite-volume shadows
is not an OS reconstruction and cannot be read as progress toward one.**

**`W2`'s leg does not move.** Identifying an infinite-volume limit as the `ℤ^d` free field needs
`G_n(x,y) → G(x,y)`, which `FieldTightness` named as where the analysis lives and which nothing
here touches.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeOSPackage

open MeasureTheory
open scoped RealInnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Regularity, as a statement -/

/-- **REGULARITY IN FINITE VOLUME.** The generating functional is bounded by a Gaussian in the
test function, with a constant built from the mass alone — **no graph appears in it**, which is
what makes the statement usable across a family of volumes. -/
def RegularFinVol (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) : Prop :=
  ∀ f : EuclideanSpace ℝ V,
    ∫ ω, Real.exp ⟪f, ω⟫ ∂(GraphLaplacian.gaussianField G m)
      ≤ Real.exp (‖f‖ ^ 2 / (2 * m ^ 2))

/-- The lattice field is regular in finite volume. `LatticeRegularity` proves the inequality;
this records that it is an instance of the named property and reproves nothing. -/
theorem gaussianField_regularFinVol (hm : m ≠ 0) : RegularFinVol G m :=
  fun f => LatticeRegularity.generatingFunctional_le hm f

/-! ## 2. The two that hold with no hypothesis but `m ≠ 0` -/

/-- **THE UNCONDITIONAL PAIR.** Regularity and Euclidean covariance, at every finite graph, every
nonzero mass, and with nothing else assumed. -/
theorem gaussianField_shadows (hm : m ≠ 0) :
    RegularFinVol G m ∧ LatticeOS1.EuclideanCovariantFinVol G m :=
  ⟨gaussianField_regularFinVol hm, LatticeOS1.gaussianField_euclideanCovariantFinVol hm⟩

end LatticeOSPackage

/-! ## 3. And reflection positivity, on the box, with its hypotheses in the open -/

namespace LatticeOSPackage

open IsingContourSeparation IsingFiniteVolume LatticeReflection LatticeReflectionPositive

/-- **ALL THREE, ABOUT ONE GRAPH.** `GraphReflection.reflectionPositive_box` is `Iff.rfl`, so the
lattice reflection-positivity statement **is** the graph one at `latticeGraph n`; the three
conjuncts below are therefore three properties of the single measure
`GraphLaplacian.gaussianField (latticeGraph n) m` and not three statements about three carriers.

Stated separately from `gaussianField_shadows` because the third conjunct needs data the first two
do not: an even side length and a half of the box below the cut. **Those hypotheses are the
statement's, not an artefact** — reflection positivity is a claim about a reflection, and there is
no reflection without one. -/
theorem gaussianField_shadows_rp {n : ℕ} (hn : Even n) {m : ℝ} (hm : m ≠ 0)
    {half : Finset (Site n)} (hsub : half ⊆ lowerHalfPair n) :
    RegularFinVol (latticeGraph n) m
      ∧ LatticeOS1.EuclideanCovariantFinVol (latticeGraph n) m
      ∧ GraphReflection.ReflectionPositive (latticeGraph n) m (refl n) half :=
  ⟨gaussianField_regularFinVol hm,
   LatticeOS1.gaussianField_euclideanCovariantFinVol hm,
   (GraphReflection.reflectionPositive_box n m half).mpr
     (reflectionPositive_lattice hn hm hsub)⟩

end LatticeOSPackage
