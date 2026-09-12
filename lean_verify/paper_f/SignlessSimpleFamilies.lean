import PawSignlessSpectrum

/-!
# Simple signless spectra: three families, all of them transported

**THE ENTRY BEFORE THIS ONE ENDED BY SAYING WHAT A READER WOULD WANT NEXT: a family rather than a
graph.** The signless side of `SimpleSpectrumCharpoly`'s criterion had exactly two graphs on it —
the single edge (`MultipartiteSignlessSingleton`) and the paw (`PawSignlessSpectrum`) — and one
family against it, the equipartite multipartite graphs. **The estate already had three more
families, and none of them needed a new computation.**

`SignlessBipartite.charpoly_signlessLap_eq_of_colorable` conjugates `Q = S L S` by the diagonal of a
`±1` two-colouring, so on a two-colourable graph the two characteristic polynomials are **equal**.
Simplicity is a property of a characteristic polynomial. So on every two-colourable graph the
signless question and the Laplacian question are **the same question**, and every family this
estate has settled on the Laplacian side settles on the signless side too.

## What is proved

**`nodup_signless_iff_lap_of_colorable`, `finrank_signless_le_one_iff_lap_of_colorable`** — that
sentence, in both of the estate's two vocabularies: equal characteristic polynomials have the same
root multiset, and `SimpleSpectrumCharpoly`'s two criteria turn each side into *every eigenspace is
a line*.

**`finrank_signless_le_one_line`, `nodup_roots_charpoly_signlessLap_line`** — **the path, at every
length**, on the satisfying side. `FieldLaplacianInstance.finrank_lapMatrix_le_one_line` is the
Laplacian half and has been in the estate since the symmetry-count chain; the path is
`boxGraph 1 (k+1)`, two-colourable by `SignlessBipartite.boxGraph_colorable_two`. **This is the
first infinite family of graphs with a simple signless spectrum in this estate.**

**`not_finrank_signless_le_one_box`, `not_nodup_roots_charpoly_signlessLap_box`** — **the box in two
dimensions and up, at every side length**, on the failing side, from
`FieldSimpleBox.not_finrank_lapMatrix_le_one_box`.

**`not_finrank_signless_le_one_torus`, `not_nodup_roots_charpoly_signlessLap_torus`** — **and the
periodic lattice at even side length**, from
`FieldSimpleConnected.not_finrank_lapMatrix_le_one_torus`, two-colourable by
`TorusBipartite.torusGraph_colorable_two`. Odd side length is outside the transport because the
graph is then not two-colourable.

## What is NOT here

* **NOTHING IS COMPUTED.** No eigenvalue, no polynomial, no eigenvector. Every theorem here is a
  composition of two results that were already in the estate, and the whole file is transport. It
  is recorded as a unit because the three families were not on the signless side yesterday and are
  today, not because anything was hard.
* **THE TWO-COLOURABILITY HYPOTHESIS IS NOT SHOWN NECESSARY.** No graph is exhibited anywhere where
  the signless and Laplacian answers differ. The one graph whose signless simplicity this chain
  established off the two-colourable case — the paw — has a **simple Laplacian spectrum** as well
  (`PawSimpleSpectrum.finrank_lapMatrix_le_one_paw`), so it does not separate the two questions.
  Whether they can differ at all is open, and nothing here bears on it. Not attempted
  (`ERRATUM 246`).
* **THE TRANSPORT REACHES ONLY TWO-COLOURABLE GRAPHS**, which is why the equipartite multipartite
  family of `MultipartiteSignlessCharpoly` is not covered by it: that family is proved **not**
  two-colourable at three or more parts, and its failing instance was proved directly through the
  spectrum.
* **NO NEW SATISFYING GRAPH OFF THE TWO-COLOURABLE CASE.** The paw is still the only one, and one
  is not a family.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0`
  and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the estate's `Fintype`, `DecidableEq` and
`DecidableRel` instances; `G.Colorable 2` on the two general statements, which is what the
conjugation needs; `1 ≤ d` and `Even (N + 3)` on the torus, both inherited from the theorems being
transported. **No mass, no propagator, and no metric anywhere** — the Laplacian halves of all three
families were already stated in the mass-free form.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessSimpleFamilies

open Matrix SimpleGraph LaplacianSignless BoxGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. On a two-colourable graph the two questions are the same question -/

theorem nodup_signless_iff_lap_of_colorable (hcol : G.Colorable 2) :
    (signlessLap G).charpoly.roots.Nodup ↔ (G.lapMatrix ℝ).charpoly.roots.Nodup := by
  rw [SignlessBipartite.charpoly_signlessLap_eq_of_colorable G hcol]

theorem finrank_signless_le_one_iff_lap_of_colorable (hcol : G.Colorable 2) :
    (∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap G) - μ • LinearMap.id)) ≤ 1)
      ↔ (∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id)) ≤ 1) := by
  rw [← SimpleSpectrumCharpoly.nodup_roots_charpoly_signlessLap_iff,
    nodup_signless_iff_lap_of_colorable hcol,
    SimpleSpectrumCharpoly.nodup_roots_charpoly_lapMatrix_iff,
    ← FieldSimpleConverse.finrank_lapMatrix_le_one_iff_injective]

/-! ## 2. An infinite family on the satisfying side: the path -/

theorem finrank_signless_le_one_line (k : ℕ) (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap (boxGraph 1 (k + 1))) - μ • LinearMap.id)) ≤ 1 :=
  (finrank_signless_le_one_iff_lap_of_colorable
    (SignlessBipartite.boxGraph_colorable_two 1 (k + 1))).mpr
    (FieldLaplacianInstance.finrank_lapMatrix_le_one_line k) μ

theorem nodup_roots_charpoly_signlessLap_line (k : ℕ) :
    (signlessLap (boxGraph 1 (k + 1))).charpoly.roots.Nodup :=
  (SimpleSpectrumCharpoly.nodup_roots_charpoly_signlessLap_iff _).mpr
    (finrank_signless_le_one_line k)

/-! ## 3. An infinite family on the failing side: the box in two dimensions and up -/

theorem not_finrank_signless_le_one_box (d m : ℕ) :
    ¬ (∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap (boxGraph (d + 2) (m + 2))) - μ • LinearMap.id)) ≤ 1) := by
  intro h
  exact FieldSimpleBox.not_finrank_lapMatrix_le_one_box d m
    ((finrank_signless_le_one_iff_lap_of_colorable
      (SignlessBipartite.boxGraph_colorable_two (d + 2) (m + 2))).mp h)

theorem not_nodup_roots_charpoly_signlessLap_box (d m : ℕ) :
    ¬ (signlessLap (boxGraph (d + 2) (m + 2))).charpoly.roots.Nodup := by
  rw [SimpleSpectrumCharpoly.nodup_roots_charpoly_signlessLap_iff]
  exact not_finrank_signless_le_one_box d m

/-! ## 4. And the periodic lattice, at even side length -/

theorem not_finrank_signless_le_one_torus {d : ℕ} (hd : 1 ≤ d) (N : ℕ) (hN : Even (N + 3)) :
    ¬ (∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap (TorusReflection.torusGraph d (N + 3)))
          - μ • LinearMap.id)) ≤ 1) := by
  intro h
  exact FieldSimpleConnected.not_finrank_lapMatrix_le_one_torus hd N
    ((finrank_signless_le_one_iff_lap_of_colorable
      (TorusBipartite.torusGraph_colorable_two hN)).mp h)

theorem not_nodup_roots_charpoly_signlessLap_torus {d : ℕ} (hd : 1 ≤ d) (N : ℕ)
    (hN : Even (N + 3)) :
    ¬ (signlessLap (TorusReflection.torusGraph d (N + 3))).charpoly.roots.Nodup := by
  rw [SimpleSpectrumCharpoly.nodup_roots_charpoly_signlessLap_iff]
  exact not_finrank_signless_le_one_torus hd N hN

end SignlessSimpleFamilies
