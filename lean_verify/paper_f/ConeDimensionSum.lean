/-
  ConeDimensionSum: the upper bound this chain's residue asked for — and it was already in the
  estate, one query away

  WHY THIS FILE EXISTS. Unit 88 closed the wheel's multiplicity from below and left one
  sentence: *the multiplicity is not pinned at two; the UPPER bound needs the rim's zero-sum
  spectrum exhausted, and unit 82's `finrank_coneEig_bounds` would transfer such a bound to the
  cone immediately — there is none.*

  **THE SECOND HALF OF THAT SENTENCE WAS WRONG, AND A QUERY SAID SO BEFORE ANYTHING WAS BUILT.**
  `HermitianFibreCount.sum_finrank_le` has been in the estate since 2026-09-13: for any real
  Hermitian `A` and any `Finset` of reals, **the eigenspace dimensions at those values sum to at
  most `card V`.** It needs no exhaustion, no basis and no enumeration — it is the pigeonhole a
  spectral decomposition gives, stated once and generally. So the transfer is one application
  plus `Fintype.card (Option V) = Fintype.card V + 1`, and this file is short because the work
  was done elsewhere. **That is `ERRATUM 258`'s most expensive error avoided by one `awk`.**

  **A COUNT THAT THE FIRST DRAFT OF THIS HEADER GOT WRONG, corrected before the commit.** It
  said *the third time in this chain that the thing declared missing was present*, which is a
  number nobody had counted — `ERRATUM 613`'s exact species, a count of the chain standing in
  for a count of the instances. Counted: **within the cone chain this is the FIRST** shipped
  claim of absence that was false. The campaign has two neighbours and they are different
  species — `RE-SWEEP #59`'s `FINDING 1` (`ERRATUM 615`), which shipped and was withdrawn, and
  `RE-SWEEP #60`'s candidate, which was refuted by query before it was written. Unit 79's
  mis-priced wheel instance and unit 83's unused `cone_disc_pos` are neither: one was a price,
  the other a theorem present and unspent.

  WHAT IS PROVED.

  * **`signlessLap_coneGraph_isHermitian`** — the cone's `Q` is Hermitian, off
    `LaplacianSignlessDefinite.signlessLap_isHermitian`, which is general in the graph.
  * **`sum_finrank_coneEig_le`** — for every `Finset ℝ`, the cone's eigenspace dimensions at
    those values sum to at most `card V + 1`. **The upper bound, transferred.**
  * **`finrank_coneEig_eq_of_sum_eq`** — **THE PRINCIPLE THAT MAKES IT USEFUL.** If a lower
    bound `f` is known at every value of a `Finset` and those lower bounds already sum to
    `card V + 1`, then **every one of them is exact**. No further work per eigenvalue: the
    pigeonhole closes them all at once.
  * **`two_mul_card_le_of_two_le`** — and a bound that bites without any spectrum: at most
    `(card V + 1) / 2` values can carry multiplicity two or more, because `2 · card s ≤ card V + 1`.
  * **`sum_finrank_coneEig_le_of_top_mem`** — sharpened by unit 86: since the top is simple,
    everything OTHER than the top sums to at most `card V`.

  WHAT IS **NOT** CLAIMED, AND ONE OF THESE IS A WALL WORTH NAMING.

  * **THE WHEEL'S MULTIPLICITY TABLE DOES NOT FOLLOW FROM THIS FILE**, and the obstruction is
    not a dimension count. Assembling it needs the eigenvalues to be **distinct**, and while
    `3 + 2cos(2πk/N)` are distinct across `0 ≤ k ≤ N/2` by injectivity of `cos` on `[0, π]`,
    **whether `hubRootMinus` coincides with one of them is a COINCIDENCE QUESTION** — a root of
    `λ² = (N+5)λ − 4N` against a cosine — of exactly the species this estate records as
    library-blocked at `L102` (*which frequencies give a one-orbit fibre*) and at the odd-`n`
    cyclotomic item. **Not attempted and no cost offered** (`ERRATUM 194`, `ERRATUM 246`). Until
    it is settled the lower bounds cannot be shown to sum to `card V + 1`, because the sum is
    over a `Finset` whose cardinality depends on that non-collision.
  * **NO SPECTRUM IS COMPUTED HERE.** This file proves an inequality about dimensions and a
    principle for using it. It names no graph, computes no eigenvalue, and adds nothing to any
    family.
  * **NOTHING ABOUT MATHLIB'S `IsHermitian.eigenvalues` INDEXING.** `sum_finrank_le` is stated
    over an arbitrary `Finset` precisely so that the enumeration is not needed, which is why it
    is usable here at all — the fence this cluster has met in every unit is side-stepped rather
    than crossed.
    [**OVERTAKEN 2026-09-17, unit 113** (`ERRATUM 94`): it is crossed now, in
    `WheelSecondFence`, and this file's own `signlessLap_coneGraph_isHermitian` is the witness
    the crossing runs on. Side-stepping it here was still the right choice — the `Finset` form is
    what makes `sum_finrank_le` usable at all.]
  * **NOTHING ABOUT THE CASCADE, THE SPINE OR ANY WALL OF THE PAPER.**

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import ConeTopEigen
import HermitianFibreCount

namespace ConeDimensionSum

open SimpleGraph LaplacianSignless Matrix
open ConeSignlessSpectrum ConeMultiplicity ConeMultiplicityExact ConeTopEigen

section Sum

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The cone's signless Laplacian is Hermitian — general in the graph, so general in the cone. -/
theorem signlessLap_coneGraph_isHermitian :
    (signlessLap (coneGraph G)).IsHermitian :=
  LaplacianSignlessDefinite.signlessLap_isHermitian (coneGraph G)

/-- **THE UPPER BOUND, TRANSFERRED.** The cone's eigenspace dimensions at any finite set of
values sum to at most `card V + 1`. No exhaustion, no basis, no enumeration. -/
theorem sum_finrank_coneEig_le (s : Finset ℝ) :
    ∑ lam ∈ s, Module.finrank ℝ (coneEig G lam) ≤ Fintype.card V + 1 := by
  have h := HermitianFibreCount.sum_finrank_le (signlessLap_coneGraph_isHermitian G) s
  rw [Fintype.card_option] at h
  exact h

/-- **THE PRINCIPLE THAT MAKES IT USEFUL.** Lower bounds that already sum to `card V + 1` are
all exact — the pigeonhole closes every eigenvalue at once rather than one at a time. -/
theorem finrank_coneEig_eq_of_sum_eq {s : Finset ℝ} {f : ℝ → ℕ}
    (hlb : ∀ lam ∈ s, f lam ≤ Module.finrank ℝ (coneEig G lam))
    (hsum : ∑ lam ∈ s, f lam = Fintype.card V + 1) :
    ∀ lam ∈ s, Module.finrank ℝ (coneEig G lam) = f lam := by
  have hle := sum_finrank_coneEig_le G s
  have heq : ∑ lam ∈ s, f lam = ∑ lam ∈ s, Module.finrank ℝ (coneEig G lam) := by
    have h1 : ∑ lam ∈ s, f lam ≤ ∑ lam ∈ s, Module.finrank ℝ (coneEig G lam) :=
      Finset.sum_le_sum hlb
    omega
  intro lam hlam
  exact ((Finset.sum_eq_sum_iff_of_le hlb).1 heq lam hlam).symm

/-- **A BOUND THAT BITES WITH NO SPECTRUM AT ALL**: at most `(card V + 1) / 2` values can carry
multiplicity two or more. -/
theorem two_mul_card_le_of_two_le {s : Finset ℝ}
    (h2 : ∀ lam ∈ s, 2 ≤ Module.finrank ℝ (coneEig G lam)) :
    2 * s.card ≤ Fintype.card V + 1 := by
  have hcard : s.card * 2 ≤ ∑ lam ∈ s, Module.finrank ℝ (coneEig G lam) := by
    simpa using Finset.card_nsmul_le_sum s _ 2 h2
  have hle := sum_finrank_coneEig_le G s
  omega

/-- **SHARPENED BY UNIT 86**: the top is simple, so everything other than the top sums to at
most `card V`. -/
theorem sum_finrank_coneEig_le_of_top_mem [Nonempty V] {d : ℕ} (hreg : ∀ i, G.degree i = d)
    (s : Finset ℝ) :
    ∑ lam ∈ s.erase (hubRootPlus (Fintype.card V) d),
        Module.finrank ℝ (coneEig G lam) ≤ Fintype.card V := by
  have htop := finrank_coneEig_hubRootPlus G hreg
  have hins := sum_finrank_coneEig_le G
    (insert (hubRootPlus (Fintype.card V) d) (s.erase (hubRootPlus (Fintype.card V) d)))
  rw [Finset.sum_insert (Finset.notMem_erase _ _), htop] at hins
  omega

end Sum

end ConeDimensionSum
