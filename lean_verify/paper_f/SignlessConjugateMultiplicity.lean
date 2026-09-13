import SignlessBipartite
import BoxLapMultiplicityExact

/-!
# Multiplicities transfer across the two-colouring, and the box's `Q` is counted exactly

**THE COMPOSITION THE PREVIOUS UNIT NAMED AND DID NOT MAKE.** `BoxLapMultiplicityExact` closed
`L`'s multiplicities on the free-boundary box and said in terms that *nothing about `Q` on the box
is added here*, the box being two-colourable and `SignlessBipartite` holding the transfer. This
file makes it, and the step it needs is **not** the characteristic polynomial.

**WHY THE CHARACTERISTIC POLYNOMIAL IS THE WRONG TOOL HERE.**
`SignlessBipartite.charpoly_signlessLap_eq` gives `Q` and `L` the same polynomial, hence the same
**algebraic** multiplicities. Every multiplicity in this chain is a `finrank` of a kernel — a
**geometric** multiplicity — and the two agree only for a diagonalisable matrix, which is a fact
about these operators that the estate has nowhere stated (`ERRATUM 455`'s discipline applied to a
step, not to a hypothesis). So the polynomial is bypassed: `signlessLap_eq_conj` is a
**similarity**, `Q = S L S` with `S` diagonal and `S² = 1`, and a similarity moves eigenspaces, not
merely their dimensions-counted-with-algebraic-multiplicity.

## What is proved

**`colourSignEquiv`** — multiplication by the two-colouring's signs, as a linear equivalence of
`V → ℝ` with itself. It is its own inverse, `σ v² = 1` being the whole of the proof. Its name took
three tries; see the declaration.

**`ker_signlessLap_eq_map`** — for a graph carrying a sign colouring, **`Q`'s eigenspace at `μ` is
the image of `L`'s eigenspace at `μ` under `colourSignEquiv`**, at every real `μ`. The estate had
the forward half of this at the level of a single vector (`signlessLap_mulVec_of_lapMatrix`); what
is new is that the map is an equivalence, so the inclusion is an equality and nothing is lost.

**`finrank_eigenspace_signlessLap_eq_lap`** — hence **the two operators have the same multiplicity
at every real `μ`, on every graph with a sign colouring**, and `..._of_colorable` says it with
two-colourability as the hypothesis instead. **This is a general theorem about graphs and it is
the file's content**; everything below is instantiation.

**`finrank_eigenspace_boxSignlessLap`** — **`Q`'s multiplicity on the free-boundary box is the
same exact fibre count as `L`'s**, in every dimension and at every side length, by composing the
transfer with `BoxLapMultiplicityExact.finrank_eigenspace_boxLap`. This is the composition the
previous unit named as not made.

**AND IT SUBSUMES THE ROUTE THE ESTATE ALREADY HAD, WHICH IS NOT RESTATED HERE** (`ERRATUM 176`).
`SignlessSimpleFamilies.finrank_signless_le_one_iff_lap_of_colorable` proves that *every*
multiplicity is at most one on one side iff on the other, and it goes the long way round: through
`charpoly_signlessLap_eq_of_colorable`, then `SimpleSpectrumCharpoly`'s Nodup criterion in both
directions. That iff is this file's theorem quantified over `μ`, so it is now a one-line corollary
— **and it is left where it is**, because re-declaring it would be a duplicate.

## What is NOT here

* **NO NEW COUNT AT `d ≥ 2`.** `Q`'s multiplicity on the box is now exactly `L`'s, and `L`'s is a
  fibre count nobody has computed at two dimensions and above — the same wall, reached from the
  other side. **Transporting a question is not answering it.**
* **NOTHING NEW ON THE PATH, AND NOTHING AT ALL ON THE TORUS.** At `d = 1` the box's signless
  spectrum is simple, and that is `SignlessSimpleFamilies.finrank_signless_le_one_line`, already in
  the estate. The periodic lattice needs no transfer whatever:
  `TorusRealMultiplicity.finrank_eigenspace_signless_real` computes `Q`'s multiplicity there
  **directly, at every side length `≥ 3` and with no parity hypothesis**, where a two-colouring
  transfer would reach only the even ones. **A weaker theorem drafted and then deleted after
  reading the file it would have duplicated** (`ERRATUM 527`'s rule: grep for the name before
  writing the sentence).
* **THE TWO-COLOURING HYPOTHESIS IS NOT SHOWN NECESSARY.** No graph is exhibited where the two
  multiplicities differ. `SignlessSimpleFamilies` records the same gap for simplicity, and this
  file does not close it (`ERRATUM 246`).

> ⚠ **BOTH SENTENCES ARE FALSE ABOUT THE ESTATE WITHIN THE DAY, AND THEY ARE KEPT AS WRITTEN**
> (`ERRATUM 94`, `ERRATUM 537`, 2026-09-13). **The hypothesis IS necessary and it IS shown**:
> `SignlessColourableNecessary.colorable_two_iff_forall_finrank_eq`, four units later, is a
> biconditional — the multiplicities agree at every `μ` **exactly when** `G` is two-colourable, and
> `μ = 0` already decides it. **And a graph IS exhibited where they differ**, twice:
> `SignlessExcessBothWays.excess_both_ways_P1122` on `K_{1,1,2,2}`, in **both** directions, and
> `PawSignlessSpectrum.charpoly_signlessLap_ne_lapMatrix_paw` on the paw. The second sentence is
> wrong in a second way as well: `SignlessSimpleFamilies` records a gap for **simplicity**, which is
> a different question with a different answer — there the hypothesis is **not** necessary, and
> `SignlessSimpleNotNecessary` proves it with the paw. **Two fences, one wording, two answers.**
* **NOTHING ABOUT ALGEBRAIC MULTIPLICITY.** The polynomial route is described above and not taken;
  no diagonalisability statement is made, used, or needed.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a finite vertex type with decidable
equality and adjacency, and a sign colouring — or, in the `_of_colorable` form, `G.Colorable 2`.
The box theorem takes a dimension and a side length and nothing else. No mass, no propagator, no
metric.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessConjugateMultiplicity

open Matrix SimpleGraph LaplacianSignless SignlessBipartite RegularBipartiteSharp
open BoxGraph BoxLapSpectrum

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {σ : V → ℝ}

/-! ## 1. The signs, as a linear equivalence -/

/-- **MULTIPLICATION BY THE SIGNS.** An involution, because each `σ v` is `±1`.

**THE NAME TOOK THREE TRIES AND THE THIRD IS WHY IT IS THIS LONG.** `signEquiv` is
`FieldLineCount`'s bijection from `Finset V` onto a graph's isometric symmetries; `signMulEquiv` is
`FieldSignGroup`'s `MulEquiv` onto `(ZMod 2)^V`. Neither is this, and both have a fair claim on
their name. `newnames_scan` flagged each in turn before the commit, and the estate's `sign` prefix
belongs to the field-symmetry chain — twenty declarations of it — so this one names the
**two-colouring** instead. Renamed rather than accepted, twice, which is
`LaplacianSignlessKernel.compRep`'s precedent. -/
def colourSignEquiv (hσ : IsSignColouring G σ) : (V → ℝ) ≃ₗ[ℝ] (V → ℝ) where
  toFun x := fun v => σ v * x v
  map_add' x y := by funext v; simp [mul_add]
  map_smul' c x := by funext v; simp [mul_left_comm]
  invFun x := fun v => σ v * x v
  left_inv x := by
    funext v
    simp only [← mul_assoc, mul_self_sign G hσ v, one_mul]
  right_inv x := by
    funext v
    simp only [← mul_assoc, mul_self_sign G hσ v, one_mul]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem colourSignEquiv_apply (hσ : IsSignColouring G σ) (x : V → ℝ) (v : V) :
    colourSignEquiv hσ x v = σ v * x v := rfl

/-! ## 2. It carries one eigenspace onto the other -/

/-- Membership in the kernel is the eigenvector equation, for either matrix. -/
theorem mem_ker_iff (A : Matrix V V ℝ) (μ : ℝ) (y : V → ℝ) :
    y ∈ LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id) ↔ A *ᵥ y = μ • y := by
  rw [LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    ← Matrix.toLin'_apply A y, sub_eq_zero]

/-- **`Q`'s EIGENSPACE IS THE IMAGE OF `L`'s.** -/
theorem ker_signlessLap_eq_map (hσ : IsSignColouring G σ) (μ : ℝ) :
    LinearMap.ker (Matrix.toLin' (signlessLap G) - μ • LinearMap.id)
      = (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id)).map
          (colourSignEquiv hσ : (V → ℝ) →ₗ[ℝ] (V → ℝ)) := by
  ext x
  rw [mem_ker_iff, Submodule.mem_map]
  constructor
  · intro hx
    -- `σ · x` is the Laplacian eigenvector, and `colourSignEquiv` sends it back to `x`.
    refine ⟨colourSignEquiv hσ x, (mem_ker_iff _ μ _).2 ?_, (colourSignEquiv hσ).left_inv x⟩
    funext v
    have hy : (fun u => σ u * (colourSignEquiv hσ x) u) = x := (colourSignEquiv hσ).left_inv x
    have h1 : (signlessLap G *ᵥ fun u => σ u * (colourSignEquiv hσ x) u) v
        = σ v * ((G.lapMatrix ℝ) *ᵥ colourSignEquiv hσ x) v :=
      signlessLap_mulVec_signMul G hσ (colourSignEquiv hσ x) v
    rw [hy] at h1
    have h2 : (signlessLap G *ᵥ x) v = μ * x v := by rw [hx]; simp
    have h3 : σ v * ((G.lapMatrix ℝ) *ᵥ colourSignEquiv hσ x) v = μ * x v := h1 ▸ h2
    have h4 := congrArg (fun t : ℝ => σ v * t) h3
    simp only [← mul_assoc, mul_self_sign G hσ v, one_mul] at h4
    rw [h4]
    simp only [Pi.smul_apply, smul_eq_mul, colourSignEquiv_apply]
    ring
  · rintro ⟨y, hy, rfl⟩
    exact signlessLap_mulVec_of_lapMatrix G hσ ((mem_ker_iff _ μ y).1 hy)

/-! ## 3. So the multiplicities agree -/

/-- **THE SAME MULTIPLICITY AT EVERY REAL `μ`**, on any graph with a sign colouring. -/
theorem finrank_eigenspace_signlessLap_eq_lap (hσ : IsSignColouring G σ) (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G) - μ • LinearMap.id))
      = Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id)) := by
  rw [ker_signlessLap_eq_map hσ μ, LinearEquiv.finrank_map_eq]

/-- The same, with two-colourability as the hypothesis. -/
theorem finrank_eigenspace_signlessLap_eq_lap_of_colorable (hcol : G.Colorable 2) (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G) - μ • LinearMap.id))
      = Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id)) := by
  obtain ⟨σ, hσ⟩ := exists_signColouring_of_colorable hcol
  exact finrank_eigenspace_signlessLap_eq_lap hσ μ

/-! ## 4. The box, exactly -/

/-- **`Q`'s MULTIPLICITY ON THE FREE-BOUNDARY BOX IS THE SAME EXACT FIBRE COUNT AS `L`'s.** -/
theorem finrank_eigenspace_boxSignlessLap (d m : ℕ) (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (boxGraph d (m + 1))) - μ • LinearMap.id))
      = Nat.card {k : Site d (m + 1) //
          BoxLapSpectrum.boxLapEig d (m + 1) (fun i => (k i).val) = μ} := by
  rw [finrank_eigenspace_signlessLap_eq_lap_of_colorable
    (SignlessBipartite.boxGraph_colorable_two d (m + 1)) μ]
  exact BoxLapMultiplicityExact.finrank_eigenspace_boxLap d m μ

end SignlessConjugateMultiplicity
