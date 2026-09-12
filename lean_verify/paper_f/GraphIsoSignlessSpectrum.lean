import SecularSumZeroGap

/-!
# `Q` transports along a graph isomorphism, and the three-vertex path is one graph

**TWO NAMED GAPS, AND THEY TURN OUT TO BE THE SAME UNIT.**

**The first is the pattern this run keeps finding.** `GraphIsoSpectrum` carries an eigenvector of
the **adjacency** matrix across an isomorphism; `GraphIsoLapSpectrum` carries one of the
**Laplacian**; **nothing carries one of `Q`**, and neither file mentions it. The pointwise formula
is missing in the same shape: Mathlib has `adjMatrix_mulVec_apply` and `lapMatrix_mulVec_apply`, and
this estate has no `signlessLap` analogue. A fact stated at two of its three instances, again.

**The second is a sentence.** `MultipartiteSimpleSpectrum` (entry 151) classified the complete
multipartite family's simple-Laplacian members as exactly the size profiles `(1,1)` and `(1,2)`, and
recorded plainly: *both are paths, and both are already on the satisfying list — **the
identification of those two profiles with `P₂` and `P₃` is classical and is NOT formalised**; no
graph isomorphism exists in this chain.* Now two do.

**And the two gaps meet.** This chain has been computing about the three-vertex path in **two
incarnations that were never identified**: `UnbalancedMultipartiteSecularEquation`'s
`completeMultipartiteGraph (fun i : Fin 2 => Fin (i.1 + 1))`, whose signless spectrum it derived
from the secular equation, and `pathGraph 3`, which the field-theory chain has used since the
beginning. Once the isomorphism exists and `Q` transports along one, the first chain's answer is the
second chain's.

## What is proved

**`signlessLap_mulVec_apply`** — `(Q x)ᵥ = deg(v)·xᵥ + ∑_{u ∼ v} xᵤ`, the `+` version of Mathlib's
Laplacian formula.

**`signlessLap_mulVec_comp_symm`, `signlessLap_mulVec_smul_iso`, `isEigen_iso`,
`isEigen_iso_iff`** — an eigenvector of `Q` transports along an isomorphism and the eigenvalue does
not move. Line for line the shape of `GraphIsoLapSpectrum`, which is the point: a third instance of
a statement written at two.

**`adjMatrix_reindex`, `lapMatrix_reindex`, `signlessLap_reindex`, `charpoly_adjMatrix_iso`,
`charpoly_lapMatrix_iso`, `charpoly_signlessLap_iso`** — **and then the same gap opens one level
up, so this file closes that too.** All three matrices are `Matrix.reindex e e` of one another, and
`Matrix.charpoly_reindex` turns that into equal characteristic polynomials. The two older files
stop at the `mulVec` statement, which carries **an eigenvector at a given eigenvalue** and nothing
else; the polynomial carries the spectrum **with multiplicity**. The three proofs are the same
proof.

**`finrank_eigenspace_signless_iso`** — so eigenspace dimensions cross as well, through
`HermitianRootMultiplicity.rootMultiplicity_charpoly_signlessLap`.

**`pathIso`, `edgeIso`** — the identifications entry 151 named:
`completeMultipartiteGraph (1,2) ≃g pathGraph 3`, with `⟨0,0⟩` the centre, and
`completeMultipartiteGraph (1,1) ≃g pathGraph 2`. Both `decide`.

**`isEigenvalue_signless_pathGraph_three`** — hence **`Q`'s spectrum on `pathGraph 3` is exactly
`{0, 1, 3}`**, carried across from a computation done by the secular equation on a graph nobody had
identified with this one.

## What is NOT here

* **THE TWO OLDER FILES ARE NOT UPGRADED IN PLACE.** `GraphIsoSpectrum` and
  `GraphIsoLapSpectrum` still stop at their `mulVec` statements; the polynomial-level versions for
  their matrices live here instead, downstream of both, because moving them would edit two files
  for one unit. **Nothing there is wrong** — it is weaker than it needed to be, which is this
  file's whole subject, and saying so is not a criticism of either.
* **NOTHING IS TRANSPORTED FOR A WEIGHTED OR MASSIVE MATRIX.** The three reindexings are for the
  bare graph matrices; the field-theory chain's massive operators are not touched (`ERRATUM 246`).
* **THE CLASSIFICATION IS NOT RE-DERIVED.** Entry 151's theorem stands as it was; this file supplies
  the identification its own fence said was missing and changes nothing else about it, and **it adds
  no new graph to the satisfying list** — that was entry 151's point and it still holds.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0`
  and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): for the transport, `Fintype`, `DecidableEq`
and `DecidableRel` on both graphs and nothing else — **no connectivity, no regularity, no
colourability**; for the two isomorphisms, nothing at all, both being finite checks. **No mass, no
propagator, and no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace GraphIsoSignlessSpectrum

open Matrix SimpleGraph LaplacianSignless

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-! ## 1. The pointwise formula, which Mathlib has for `A` and for `L` -/

theorem signlessLap_mulVec_apply (v : V) (vec : V → ℝ) :
    (signlessLap G *ᵥ vec) v = G.degree v * vec v + ∑ u ∈ G.neighborFinset v, vec u := by
  simp_rw [signlessLap, Matrix.add_mulVec, Pi.add_apply, SimpleGraph.degMatrix_mulVec_apply,
    SimpleGraph.adjMatrix_mulVec_apply]

/-! ## 2. So `Q` transports along an isomorphism, as `A` and `L` already did -/

theorem signlessLap_mulVec_comp_symm (e : G ≃g H) (v : V → ℝ) :
    signlessLap H *ᵥ (fun w => v (e.symm w)) = fun w => (signlessLap G *ᵥ v) (e.symm w) := by
  funext w
  obtain ⟨a, rfl⟩ : ∃ a, e a = w := ⟨e.symm w, e.right_inv w⟩
  have hinv : ∀ b : V, e.symm (e b) = b := fun b => e.left_inv b
  rw [hinv a]
  rw [signlessLap_mulVec_apply, signlessLap_mulVec_apply,
    GraphIsoSpectrum.sum_neighborFinset_iso e (fun w => v (e.symm w)) a,
    SimpleGraph.Iso.degree_eq e a]
  simp only [hinv]

/-- **AN EIGENVECTOR OF `Q` TRANSPORTS, AND THE EIGENVALUE DOES NOT MOVE.** -/
theorem signlessLap_mulVec_smul_iso (e : G ≃g H) {v : V → ℝ} {c : ℝ}
    (hv : signlessLap G *ᵥ v = c • v) :
    signlessLap H *ᵥ (fun w => v (e.symm w)) = c • fun w => v (e.symm w) := by
  rw [signlessLap_mulVec_comp_symm e v, hv]
  rfl

theorem isEigen_iso (e : G ≃g H) {c : ℝ}
    (h : ∃ v : V → ℝ, v ≠ 0 ∧ signlessLap G *ᵥ v = c • v) :
    ∃ w : W → ℝ, w ≠ 0 ∧ signlessLap H *ᵥ w = c • w := by
  obtain ⟨v, hv0, hv⟩ := h
  exact ⟨fun w => v (e.symm w), GraphIsoSpectrum.comp_symm_ne_zero e hv0,
    signlessLap_mulVec_smul_iso e hv⟩

theorem isEigen_iso_iff (e : G ≃g H) (c : ℝ) :
    (∃ v : V → ℝ, v ≠ 0 ∧ signlessLap G *ᵥ v = c • v)
      ↔ ∃ w : W → ℝ, w ≠ 0 ∧ signlessLap H *ᵥ w = c • w :=
  ⟨isEigen_iso e, isEigen_iso e.symm⟩

/-! ## 3. All three matrices reindex, so all three characteristic polynomials agree -/

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
theorem adjMatrix_reindex (e : G ≃g H) :
    H.adjMatrix ℝ = Matrix.reindex e.toEquiv e.toEquiv (G.adjMatrix ℝ) := by
  ext a b
  have hadj : H.Adj a b ↔ G.Adj (e.symm a) (e.symm b) := by
    rw [← e.map_adj_iff, e.apply_symm_apply, e.apply_symm_apply]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply]
  exact if_congr hadj rfl rfl

theorem lapMatrix_reindex (e : G ≃g H) :
    H.lapMatrix ℝ = Matrix.reindex e.toEquiv e.toEquiv (G.lapMatrix ℝ) := by
  ext a b
  have hd : H.degree a = G.degree (e.symm a) := by
    have h := SimpleGraph.Iso.degree_eq e (e.symm a)
    rwa [e.apply_symm_apply] at h
  have hadj : H.Adj a b ↔ G.Adj (e.symm a) (e.symm b) := by
    rw [← e.map_adj_iff, e.apply_symm_apply, e.apply_symm_apply]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, SimpleGraph.lapMatrix,
    Matrix.sub_apply, SimpleGraph.degMatrix, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply, EmbeddingLike.apply_eq_iff_eq]
  rw [hd]
  congr 1
  exact if_congr hadj rfl rfl

theorem signlessLap_reindex (e : G ≃g H) :
    signlessLap H = Matrix.reindex e.toEquiv e.toEquiv (signlessLap G) := by
  ext a b
  have hd : H.degree a = G.degree (e.symm a) := by
    have h := SimpleGraph.Iso.degree_eq e (e.symm a)
    rwa [e.apply_symm_apply] at h
  have hadj : H.Adj a b ↔ G.Adj (e.symm a) (e.symm b) := by
    rw [← e.map_adj_iff, e.apply_symm_apply, e.apply_symm_apply]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, signlessLap, Matrix.add_apply,
    SimpleGraph.degMatrix, Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply,
    EmbeddingLike.apply_eq_iff_eq]
  rw [hd]
  congr 1
  exact if_congr hadj rfl rfl

theorem charpoly_adjMatrix_iso (e : G ≃g H) :
    (H.adjMatrix ℝ).charpoly = (G.adjMatrix ℝ).charpoly := by
  rw [adjMatrix_reindex e, Matrix.charpoly_reindex]

theorem charpoly_lapMatrix_iso (e : G ≃g H) :
    (H.lapMatrix ℝ).charpoly = (G.lapMatrix ℝ).charpoly := by
  rw [lapMatrix_reindex e, Matrix.charpoly_reindex]

theorem charpoly_signlessLap_iso (e : G ≃g H) :
    (signlessLap H).charpoly = (signlessLap G).charpoly := by
  rw [signlessLap_reindex e, Matrix.charpoly_reindex]

/-- **AND SO MULTIPLICITIES CROSS**, not only the spectrum as a set. -/
theorem finrank_eigenspace_signless_iso (e : G ≃g H) (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G) - μ • LinearMap.id))
      = Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap H) - μ • LinearMap.id)) := by
  rw [← HermitianRootMultiplicity.rootMultiplicity_charpoly_signlessLap,
    ← HermitianRootMultiplicity.rootMultiplicity_charpoly_signlessLap,
    charpoly_signlessLap_iso e]

/-! ## 4. The three-vertex path, in this chain's two incarnations -/

section Path

/-- The three-vertex path as the secular files write it: parts of sizes `1` and `2`. -/
abbrev PathPart : Fin 2 → Type := fun i => Fin (i.1 + 1)

/-- `⟨0,0⟩` is the centre, `⟨1,0⟩` and `⟨1,1⟩` the two ends. -/
def toFin3 : (Σ i, PathPart i) → Fin 3
  | ⟨0, _⟩ => 1
  | ⟨1, ⟨0, _⟩⟩ => 0
  | ⟨1, ⟨1, _⟩⟩ => 2

def ofFin3 : Fin 3 → (Σ i, PathPart i)
  | 0 => ⟨1, ⟨0, by omega⟩⟩
  | 1 => ⟨0, ⟨0, by omega⟩⟩
  | 2 => ⟨1, ⟨1, by omega⟩⟩

theorem left_inv_fin3 : ∀ p, ofFin3 (toFin3 p) = p := by decide

theorem right_inv_fin3 : ∀ v, toFin3 (ofFin3 v) = v := by decide

/-- **THE IDENTIFICATION `MultipartiteSimpleSpectrum` CALLED CLASSICAL AND DID NOT FORMALISE.** -/
def pathIso : completeMultipartiteGraph PathPart ≃g pathGraph 3 where
  toEquiv := ⟨toFin3, ofFin3, left_inv_fin3, right_inv_fin3⟩
  map_rel_iff' := by decide

/-- The other profile `MultipartiteSimpleSpectrum` named: two parts of one vertex, which is `K₂`. -/
abbrev EdgePart : Fin 2 → Type := fun _ => Fin 1

def toFin2 : (Σ i, EdgePart i) → Fin 2 := fun p => ⟨p.1.1, p.1.2⟩

def ofFin2 : Fin 2 → (Σ i, EdgePart i) := fun v => ⟨⟨v.1, v.2⟩, ⟨0, by omega⟩⟩

theorem left_inv_fin2 : ∀ p, ofFin2 (toFin2 p) = p := by decide

theorem right_inv_fin2 : ∀ v, toFin2 (ofFin2 v) = v := by decide

/-- **AND THE `(1,1)` PROFILE IS THE TWO-VERTEX PATH.** -/
def edgeIso : completeMultipartiteGraph EdgePart ≃g pathGraph 2 where
  toEquiv := ⟨toFin2, ofFin2, left_inv_fin2, right_inv_fin2⟩
  map_rel_iff' := by decide

/-! ## 5. So the secular chain's spectrum is the path graph's -/

/-- **`Q`'s SPECTRUM ON `pathGraph 3` IS `{0, 1, 3}`**, carried across from
`UnbalancedMultipartiteSecularEquation.isEigenvalue_signless_path`, which computed it by the secular
equation on a graph nobody had identified with this one. -/
theorem isEigenvalue_signless_pathGraph_three (μ : ℝ) :
    (∃ w : Fin 3 → ℝ, w ≠ 0 ∧ signlessLap (pathGraph 3) *ᵥ w = μ • w)
      ↔ μ = 0 ∨ μ = 1 ∨ μ = 3 :=
  (isEigen_iso_iff pathIso μ).symm.trans
    (UnbalancedMultipartiteSecularEquation.isEigenvalue_signless_path μ)

/-- **AND THE CHARACTERISTIC POLYNOMIALS ARE THE SAME POLYNOMIAL**, so the agreement is with
multiplicity and not only as sets. -/
theorem charpoly_signlessLap_pathGraph_three :
    (signlessLap (pathGraph 3)).charpoly
      = (signlessLap (completeMultipartiteGraph PathPart)).charpoly :=
  charpoly_signlessLap_iso pathIso

end Path

end GraphIsoSignlessSpectrum
