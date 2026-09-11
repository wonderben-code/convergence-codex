import LaplacianSignless
import BipartiteAdjSymmetry
import BoxLapSpectrum
import TorusBipartite

/-!
# On a two-colourable graph the signless Laplacian is the Laplacian, conjugated

**So the box's `Q`-spectrum is its `L`-spectrum, with multiplicities.**

**THREE FILES OF THE SIGNLESS CHAIN CARRY THE SAME FENCE, AND ITS REASON IS RIGHT WHILE ITS
CONCLUSION IS WRONG.** `SignlessTorusSpectrum`, `SignlessTorusReal` and `SignlessTorusComplete` each
say that the **box** *"is not reached and is not close — a boundary and a non-constant degree, so no
character family at all"*, and the first adds that *"no eigenvalue of `Q` is known at any graph that
is not a cycle or a torus"*. Every clause about characters is true. **No character family is
needed**: on a two-colourable graph `Q = S L S` with `S` the diagonal of the `±1` colouring, and `S`
is its own inverse, so `Q` and `L` are **similar**. The box is two-colourable at every side length,
so its signless spectrum is its Laplacian spectrum — which `BoxLapSpectrum` computed on 31 August.

**HOW THIS TARGET WAS FOUND, because the method is the transferable part.** The previous unit closed
a fence carried by **four** files and observed that a fence repeated across files is a better target
than one stated once: four authors wanted the object and none needed it. This estate has a census of
**verbatim** repeated fences (`fencedup_scan.py`) whose own documented limit is that *a fence
reworded on its way into the next header is invisible*. A one-off shingle census over the `paper_f`
headers — normalising code spans and punctuation, 9-word windows, three files or more — returns the
near-duplicates that mode cannot see, and after the boilerplate groups this fence was the largest.
**The census is a throwaway and is not shipped**: it judged nothing, and the judgement half is the
part `ERRATUM 60` says a mode must not claim.

**WHAT HAD TO BE PROVED RATHER THAN SUBSTITUTED, MEASURED BEFORE WRITING** (`ERRATUM 500`'s rule):

* **THE MATRIX IDENTITY.** `RegularBipartiteSharp.IsSignColouring` and
  `exists_signColouring_of_colorable` are this estate's, and `BipartiteAdjSymmetry` spends them on
  the **adjacency** matrix — as a `mulVec` statement, at one vertex. **Nothing conjugates either
  Laplacian by anything**: of the files mentioning `signlessLap`, none states a similarity.
  `signlessLap_eq_conj` is the identity `Q = S L S`, from which the spectral statements are
  corollaries rather than separate computations.
* **THE BOX'S TWO-COLOURABILITY.** `TorusBipartite.torusGraph_colorable_two` needs **even** side
  length, because a periodic lattice of odd side contains an odd cycle. The box needs no parity
  hypothesis at all — a free boundary closes no cycle — and the proof is the coordinate-sum
  argument with the wrap-around case deleted (`sum_val_eq_succ_of_adj`, reusing
  `TorusBipartite.siteParity` rather than declaring a second one).
* **AND ONE FACT IS RESTATED RATHER THAN IMPORTED, WITH THE REASON SAID.**
  `lapMatrix_isHermitian'` is `FieldSimpleConverse.lapMatrix_isHermitian` with identical
  hypotheses — a one-line consequence of Mathlib's `posSemidef_lapMatrix`. Importing that file
  would pull the whole Gaussian-field chain in behind it, so both stay, which is `ERRATUM 465`'s
  rule applied to the import graph rather than to the statement.

## What is proved

**`signlessLap_eq_conj`** — **`Q = S L S`** for any sign colouring: the whole file in one line, and
no eigenvector in sight.

**`charpoly_signlessLap_eq`**, **`charpoly_signlessLap_eq_of_colorable`** — so the two
**characteristic polynomials are equal**, via `Matrix.charpoly_units_conj` on the self-inverse
`signUnit`. That is the same eigenvalues **with the same multiplicities**, algebraic ones included.

**`eigenvalues_signlessLap_multiset_eq`** (and `_of_colorable`) — and the same statement in the
vocabulary a reader wants: the two `IsHermitian.eigenvalues` enumerations are the **same multiset**,
through Mathlib's `roots_charpoly_eq_eigenvalues`.

**`signlessLap_mulVec_signMul`**, **`signlessLap_mulVec_of_lapMatrix`** — the explicit transfer: a
Laplacian eigenvector times the signs is a signless eigenvector at the **same** eigenvalue.

**`boxGraph_colorable_two`** — **THE BOX IS TWO-COLOURABLE IN EVERY DIMENSION AT EVERY SIDE
LENGTH**, with `boxColoring` as the colouring itself.

**`signlessLap_mulVec_boxSignlessVec`**, **`boxSignlessVec_ne_zero`** — **THE BOX'S SIGNLESS
MODES**: `BoxLapSpectrum`'s cosine modes with alternating signs, at `boxLapEig`'s eigenvalues, in
every dimension and at every side length, non-zero so they are eigenvalues.

**`charpoly_signlessLap_boxGraph`**, **`eigenvalues_signlessLap_multiset_eq_boxGraph`** — and the
box's `Q`-spectrum is its `L`-spectrum with multiplicities, not merely mode by mode.

**`charpoly_signlessLap_torusGraph`**, **`eigenvalues_signlessLap_multiset_eq_torusGraph`** — the
same on the periodic lattice at even side, where the estate's character route gives eigenvectors and
**no** multiplicities.

**`charpoly_signlessLap_ne_of_posDef`**, **`charpoly_signlessLap_ne_odd_cycle`** — **AND THE
HYPOTHESIS IS A REAL DIVIDING LINE.** The Laplacian is singular on any non-empty graph, the constant
vector being in its kernel; a positive-definite `Q` therefore cannot share its characteristic
polynomial. On an **odd cycle** `Q` is positive definite — the estate's own
`LaplacianSignlessDefinite.odd_cycle_signlessLap_posDef` — so there the two spectra genuinely
differ. Not vacuous and not universal.

## What is NOT here

* **NO COMPLETENESS, ON THE BOX OR ANYWHERE.** The charpoly equality transfers whatever is known
  about the Laplacian's spectrum and adds nothing to it: `BoxLapSpectrum` exhibits `n^d` modes and
  does not prove they exhaust, and `BoxLapMultiplicity` bounds the multiplicities **below**. So the
  box's `Q`-spectrum is known exactly as well as its `L`-spectrum is, which is not exactly.
* **NO ℂ-TO-ℝ TRANSFER FOR THE TORUS.** `SignlessTorusComplete` fences that its statements are
  about `Q` over `ℂ` and that the real transfer *is not made and no file claims it*; **that fence
  stands** — everything here is about the real symmetric matrices from the start, and nothing
  below connects them to the complex character computation. The two routes are not compared, and
  at even side length they agree only because both compute the same spectrum, which is **not**
  proved here.
* **NOTHING FOR A NON-BIPARTITE GRAPH** beyond the negative above. An odd cycle's signless spectrum
  is still uncomputed; no `Q`-eigenvalue is known at any graph that is neither a cycle, a torus, nor
  bipartite-with-a-known-Laplacian.
* **THE CONVERSE TRANSFER IS NOT WRITTEN OUT HERE.** `S` is its own inverse, so applying
  `signlessLap_mulVec_of_lapMatrix` to `Q` runs the correspondence backwards; no statement below
  does it and none below needs it. Not attempted here, no cost claimed (`ERRATUM 246`).
* **NO WALL MOVES, AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and
  `OS1` in its continuum sense. A finite-volume spectrum identified exactly is a shadow named
  exactly.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `V` a `Fintype` with `DecidableEq`, a graph
with `DecidableRel G.Adj`. The general theorems take a sign colouring `IsSignColouring G σ` or
`G.Colorable 2` and **nothing else**; the necessity theorems add `[Nonempty V]`, which is what puts
the constant vector in the Laplacian's kernel; the box theorems take **no hypothesis at all** —
neither a parity of the side length nor a positive dimension — and
`signlessLap_mulVec_boxSignlessVec` is stated at side `m + 1` because `BoxLapSpectrum` is.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessBipartite

open Matrix Finset SimpleGraph BoxGraph LaplacianSignless RegularBipartiteSharp
open BipartiteAdjSymmetry BoxLapSpectrum

section General

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  {σ : V → ℝ}

/-! ## 1. Conjugating by the signs -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem mul_self_sign (hσ : IsSignColouring G σ) (v : V) : σ v * σ v = 1 := by
  rcases hσ.1 v with h | h <;> rw [h] <;> norm_num

omit [DecidableRel G.Adj] in
theorem diagonal_mul_diagonal_sign (hσ : IsSignColouring G σ) :
    Matrix.diagonal σ * Matrix.diagonal σ = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  refine (Matrix.diagonal_eq_diagonal_iff.mpr ?_).trans Matrix.diagonal_one
  exact fun v => mul_self_sign G hσ v

theorem diagonal_mul_degMatrix_mul_diagonal (hσ : IsSignColouring G σ) :
    Matrix.diagonal σ * G.degMatrix ℝ * Matrix.diagonal σ = G.degMatrix ℝ := by
  ext u v
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases huv : u = v
  · subst huv
    rw [mul_comm ((G.degMatrix ℝ) u u), ← mul_assoc, mul_self_sign G hσ, one_mul]
  · simp [SimpleGraph.degMatrix, Matrix.diagonal_apply_ne _ huv]

theorem diagonal_mul_adjMatrix_mul_diagonal (hσ : IsSignColouring G σ) :
    Matrix.diagonal σ * G.adjMatrix ℝ * Matrix.diagonal σ = -(G.adjMatrix ℝ) := by
  ext u v
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.neg_apply]
  by_cases hadj : G.Adj u v
  · rw [SimpleGraph.adjMatrix_apply, if_pos hadj, hσ.2 u v hadj]
    have := mul_self_sign G hσ v
    nlinarith [this]
  · rw [SimpleGraph.adjMatrix_apply, if_neg hadj]
    ring

/-- **THE SIGNLESS LAPLACIAN IS THE LAPLACIAN CONJUGATED BY THE SIGNS.** -/
theorem signlessLap_eq_conj (hσ : IsSignColouring G σ) :
    signlessLap G = Matrix.diagonal σ * G.lapMatrix ℝ * Matrix.diagonal σ := by
  rw [SimpleGraph.lapMatrix, Matrix.mul_sub, Matrix.sub_mul,
    diagonal_mul_degMatrix_mul_diagonal G hσ, diagonal_mul_adjMatrix_mul_diagonal G hσ,
    sub_neg_eq_add, signlessLap]

/-! ## 2. So they are similar, and their characteristic polynomials agree -/

theorem lapMatrix_isHermitian' : (G.lapMatrix ℝ).IsHermitian :=
  (SimpleGraph.posSemidef_lapMatrix ℝ G).isHermitian

noncomputable def signUnit (hσ : IsSignColouring G σ) : (Matrix V V ℝ)ˣ where
  val := Matrix.diagonal σ
  inv := Matrix.diagonal σ
  val_inv := diagonal_mul_diagonal_sign G hσ
  inv_val := diagonal_mul_diagonal_sign G hσ

omit [DecidableRel G.Adj] in
@[simp] theorem coe_signUnit (hσ : IsSignColouring G σ) :
    ((signUnit G hσ : (Matrix V V ℝ)ˣ) : Matrix V V ℝ) = Matrix.diagonal σ := rfl

omit [DecidableRel G.Adj] in
@[simp] theorem coe_signUnit_inv (hσ : IsSignColouring G σ) :
    (((signUnit G hσ)⁻¹ : (Matrix V V ℝ)ˣ) : Matrix V V ℝ) = Matrix.diagonal σ := rfl

/-- **THE TWO MATRICES HAVE THE SAME CHARACTERISTIC POLYNOMIAL**, so the same eigenvalues with the
same multiplicities, on any graph carrying a sign colouring. -/
theorem charpoly_signlessLap_eq (hσ : IsSignColouring G σ) :
    (signlessLap G).charpoly = (G.lapMatrix ℝ).charpoly := by
  rw [signlessLap_eq_conj G hσ]
  have h := Matrix.charpoly_units_conj (signUnit G hσ) (G.lapMatrix ℝ)
  rwa [coe_signUnit, coe_signUnit_inv] at h

/-- **AND A TWO-COLOURABLE GRAPH CARRIES ONE.** -/
theorem charpoly_signlessLap_eq_of_colorable (hcol : G.Colorable 2) :
    (signlessLap G).charpoly = (G.lapMatrix ℝ).charpoly := by
  obtain ⟨σ, hσ⟩ := exists_signColouring_of_colorable hcol
  exact charpoly_signlessLap_eq G hσ

/-- **SO THE TWO EIGENVALUE ENUMERATIONS ARE THE SAME MULTISET** — the same `|V|` numbers with the
same multiplicities, which is what a spectrum is. -/
theorem eigenvalues_signlessLap_multiset_eq (hσ : IsSignColouring G σ) :
    Multiset.map (LaplacianSignlessDefinite.signlessLap_isHermitian G).eigenvalues
        Finset.univ.val
      = Multiset.map (lapMatrix_isHermitian' G).eigenvalues Finset.univ.val := by
  have h1 := (LaplacianSignlessDefinite.signlessLap_isHermitian G).roots_charpoly_eq_eigenvalues
  have h2 := (lapMatrix_isHermitian' G).roots_charpoly_eq_eigenvalues
  rw [charpoly_signlessLap_eq G hσ, h2] at h1
  simpa [Function.comp_def] using h1.symm

theorem eigenvalues_signlessLap_multiset_eq_of_colorable (hcol : G.Colorable 2) :
    Multiset.map (LaplacianSignlessDefinite.signlessLap_isHermitian G).eigenvalues
        Finset.univ.val
      = Multiset.map (lapMatrix_isHermitian' G).eigenvalues Finset.univ.val := by
  obtain ⟨σ, hσ⟩ := exists_signColouring_of_colorable hcol
  exact eigenvalues_signlessLap_multiset_eq G hσ

/-! ## 3. And the eigenvectors transfer explicitly -/

theorem signlessLap_mulVec_signMul (hσ : IsSignColouring G σ) (x : V → ℝ) (v : V) :
    (signlessLap G *ᵥ fun u => σ u * x u) v = σ v * ((G.lapMatrix ℝ) *ᵥ x) v := by
  have hdeg : ((G.degMatrix ℝ) *ᵥ fun u => σ u * x u) v
      = σ v * ((G.degMatrix ℝ) *ᵥ x) v := by
    simp [SimpleGraph.degMatrix, Matrix.mulVec_diagonal]
    ring
  have hadj := adjMatrix_mulVec_signMul G hσ x v
  rw [signlessLap, Matrix.add_mulVec, Pi.add_apply, hdeg, hadj, SimpleGraph.lapMatrix,
    Matrix.sub_mulVec, Pi.sub_apply]
  ring

/-- **A LAPLACIAN EIGENVECTOR TIMES THE SIGNS IS A SIGNLESS EIGENVECTOR AT THE SAME EIGENVALUE.** -/
theorem signlessLap_mulVec_of_lapMatrix (hσ : IsSignColouring G σ) {μ : ℝ} {x : V → ℝ}
    (hx : (G.lapMatrix ℝ) *ᵥ x = μ • x) :
    signlessLap G *ᵥ (fun u => σ u * x u) = μ • (fun u => σ u * x u) := by
  funext v
  rw [signlessLap_mulVec_signMul G hσ x v, hx]
  simp [mul_left_comm]

end General

/-! ## 4. The box is two-colourable at every side length -/

section Box

variable {d n : ℕ}

theorem sum_val_eq_succ_of_adj {p q : Site d n} (h : (boxGraph d n).Adj p q) :
    (∑ i, (q i).val) = (∑ i, (p i).val) + 1 ∨ (∑ i, (p i).val) = (∑ i, (q i).val) + 1 := by
  classical
  obtain ⟨i, hoff, hcase⟩ := h
  have hsplit : ∀ r : Site d n, ∑ j, (r j).val
      = (r i).val + ∑ j ∈ Finset.univ.erase i, (r j).val :=
    fun r => (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hrest : ∑ j ∈ Finset.univ.erase i, (p j).val
      = ∑ j ∈ Finset.univ.erase i, (q j).val :=
    Finset.sum_congr rfl fun j hj => by rw [hoff j (Finset.ne_of_mem_erase hj)]
  rw [hsplit p, hsplit q, hrest]
  omega

theorem siteParity_ne_of_adj_box {p q : Site d n} (h : (boxGraph d n).Adj p q) :
    TorusBipartite.siteParity p ≠ TorusBipartite.siteParity q := by
  have h1 := sum_val_eq_succ_of_adj h
  unfold TorusBipartite.siteParity
  omega

/-- The two-colouring of the box as data: the parity of the coordinate sum. -/
def boxColoring (d n : ℕ) : (boxGraph d n).Coloring (Fin 2) :=
  Coloring.mk (fun p => ⟨TorusBipartite.siteParity p, Nat.mod_lt _ (by norm_num)⟩) <| by
    intro p q hadj
    have hne := siteParity_ne_of_adj_box hadj
    simpa [Fin.ext_iff] using hne

/-- **THE BOX IS TWO-COLOURABLE, IN EVERY DIMENSION AND AT EVERY SIDE LENGTH** — no evenness, the
free boundary meaning there is no wrap-around to close an odd cycle. -/
theorem boxGraph_colorable_two (d n : ℕ) : (boxGraph d n).Colorable 2 := by
  simpa using (boxColoring d n).colorable

end Box

/-! ## 5. So the box's signless modes are its Laplacian modes with alternating signs -/

section BoxModes

variable {d n : ℕ}

/-- The alternating sign of a site: `(−1)` to the coordinate sum. -/
noncomputable def boxSign (p : Site d n) : ℝ := (-1) ^ (∑ i, (p i).val)

theorem isSignColouring_boxSign (d n : ℕ) :
    IsSignColouring (boxGraph d n) (boxSign (d := d) (n := n)) := by
  refine ⟨fun p => ?_, fun p q hadj => ?_⟩
  · rcases Nat.even_or_odd (∑ i, (p i).val) with h | h
    · exact Or.inl (h.neg_one_pow)
    · exact Or.inr (h.neg_one_pow)
  · rcases sum_val_eq_succ_of_adj hadj with h | h
    · rw [boxSign, boxSign, h, pow_succ]
      ring
    · rw [boxSign, boxSign, h, pow_succ]
      ring

/-- The box's signless Laplacian modes: the Laplacian modes with alternating signs. -/
noncomputable def boxSignlessVec (d n : ℕ) (k : Fin d → ℕ) (p : Site d n) : ℝ :=
  boxSign p * boxLapVec d n k p

/-- **THE `d`-DIMENSIONAL BOX'S FREE-BOUNDARY SIGNLESS LAPLACIAN MODES, AT EVERY SIDE LENGTH AND
IN EVERY DIMENSION**, with the Laplacian's eigenvalues. -/
theorem signlessLap_mulVec_boxSignlessVec (m d : ℕ) (k : Fin d → ℕ) :
    signlessLap (boxGraph d (m + 1)) *ᵥ boxSignlessVec d (m + 1) k
      = boxLapEig d (m + 1) k • boxSignlessVec d (m + 1) k :=
  signlessLap_mulVec_of_lapMatrix _ (isSignColouring_boxSign d (m + 1))
    (lapMatrix_mulVec_boxLapVec m d k)

theorem boxSignlessVec_ne_zero {k : Fin d → ℕ} (hn : 0 < n) (hk : ∀ i, k i < n) :
    boxSignlessVec d n k ≠ 0 :=
  signMul_ne_zero _ (isSignColouring_boxSign d n) (boxLapVec_ne_zero hn hk)

/-- **AND THE TWO SPECTRA AGREE WITH MULTIPLICITY ON THE BOX.** -/
theorem charpoly_signlessLap_boxGraph (d n : ℕ) :
    (signlessLap (boxGraph d n)).charpoly = ((boxGraph d n).lapMatrix ℝ).charpoly :=
  charpoly_signlessLap_eq _ (isSignColouring_boxSign d n)

/-- **SO THE BOX'S SIGNLESS SPECTRUM IS ITS LAPLACIAN SPECTRUM, AS A LIST WITH MULTIPLICITIES.** -/
theorem eigenvalues_signlessLap_multiset_eq_boxGraph (d n : ℕ) :
    Multiset.map (LaplacianSignlessDefinite.signlessLap_isHermitian (boxGraph d n)).eigenvalues
        Finset.univ.val
      = Multiset.map (lapMatrix_isHermitian' (boxGraph d n)).eigenvalues Finset.univ.val :=
  eigenvalues_signlessLap_multiset_eq _ (isSignColouring_boxSign d n)

/-- **AND ON THE PERIODIC LATTICE AT EVEN SIDE LENGTH**, where the estate's character route gives
eigenvectors and not multiplicities. -/
theorem charpoly_signlessLap_torusGraph (d : ℕ) {n : ℕ} (hn : Even n) :
    (signlessLap (TorusReflection.torusGraph d n)).charpoly
      = ((TorusReflection.torusGraph d n).lapMatrix ℝ).charpoly :=
  charpoly_signlessLap_eq_of_colorable _ (TorusBipartite.torusGraph_colorable_two hn)

theorem eigenvalues_signlessLap_multiset_eq_torusGraph (d : ℕ) {n : ℕ} (hn : Even n) :
    Multiset.map (LaplacianSignlessDefinite.signlessLap_isHermitian
        (TorusReflection.torusGraph d n)).eigenvalues Finset.univ.val
      = Multiset.map (lapMatrix_isHermitian' (TorusReflection.torusGraph d n)).eigenvalues
        Finset.univ.val :=
  eigenvalues_signlessLap_multiset_eq_of_colorable _
    (TorusBipartite.torusGraph_colorable_two hn)

end BoxModes

/-! ## 6. And the two-colourability is not decoration -/

section Necessity

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem det_lapMatrix_eq_zero [Nonempty V] : (G.lapMatrix ℝ).det = 0 :=
  Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨fun _ => 1, fun h => one_ne_zero (congrFun h (Classical.arbitrary V)),
      SimpleGraph.lapMatrix_mulVec_const_eq_zero G⟩

/-- A positive-definite signless Laplacian cannot share the Laplacian's characteristic polynomial:
the Laplacian is singular on any non-empty graph, the constant vector being in its kernel. -/
theorem charpoly_signlessLap_ne_of_posDef [Nonempty V] (hpos : (signlessLap G).PosDef) :
    (signlessLap G).charpoly ≠ (G.lapMatrix ℝ).charpoly := by
  intro h
  have hdet : (signlessLap G).det = (G.lapMatrix ℝ).det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, Matrix.det_eq_sign_charpoly_coeff, h]
  rw [det_lapMatrix_eq_zero G] at hdet
  exact absurd hdet hpos.det_pos.ne'

/-- **SO THE HYPOTHESIS IS A REAL DIVIDING LINE: ON AN ODD CYCLE THE TWO SPECTRA DIFFER**, with the
estate's own witness — `LaplacianSignlessDefinite.odd_cycle_signlessLap_posDef`. -/
theorem charpoly_signlessLap_ne_odd_cycle (M : ℕ) :
    (signlessLap (SimpleGraph.cycleGraph (2 * M + 3))).charpoly
      ≠ ((SimpleGraph.cycleGraph (2 * M + 3)).lapMatrix ℝ).charpoly :=
  charpoly_signlessLap_ne_of_posDef _
    (LaplacianSignlessDefinite.odd_cycle_signlessLap_posDef M)

end Necessity

end SignlessBipartite
