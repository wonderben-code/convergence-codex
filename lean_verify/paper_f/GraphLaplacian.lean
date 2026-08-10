/-
  GraphLaplacian.lean — the lattice chain off the square box.

  WHY. `PROOF_STRATEGY` §7 rule 3 says deepen rather than broaden, and the
  user's queue says "remove one restrictive hypothesis at a time". The
  hypothesis being removed here is a whole type. `LatticeLaplacian` and
  `LatticeField` state every theorem for `Site n = Fin n × Fin n`, and **the
  box is genuinely needed in three of them**: the kernel theorem, which is
  false on a disconnected graph, and the two trace theorems, which are
  statements about `IsingContourEnergy.bondCount` and so are about the box by
  construction. Everything else — `massive_posDef`, `green_posDef`,
  `green_isSymm`, `memLp_eval`, `integral_eval`, `twoPoint` — uses only
  `PosSemidef`, `PosDef` and `IsGaussian`, and was never about a square. The
  box entered for one reason, that W3 happened to have built it, while
  `WALLS.md` W1 and W2 both want `d = 4`.

  WHAT THIS FILE PROVES:
  1. **`massive`, `green`, `gaussianField` over an arbitrary finite simple
     graph** `G`, with `massive_posDef`, `green_posDef`, `green_diag_pos`,
     `twoPoint` and the rest. The whole W1 covariance layer, no longer
     two-dimensional and no longer square.
  2. **`lapMatrix_mulVec_eq_zero_iff_const`** — the kernel is the constants
     under `G.Connected`. The box's version carried the hypothesis `0 < n`;
     that has become the property that was doing the work.
  3. **`quadratic_form_mono`, `lapMatrix_sub_posSemidef` and
     `lapMatrix_toEuclideanLin_le`** — **the statement the box cannot make.**
     Adding edges increases the Dirichlet energy pointwise, so `L_G ≤ L_{G'}`
     whenever `G ≤ G'`, stated both as `PosSemidef` of the difference and as
     a `≤` between `toEuclideanLin` images. A fixed box has a fixed edge set
     and cannot express comparison at all; this is content the generalisation
     BUYS rather than merely re-hosts. (**Both formulations are detours**:
     Mathlib has a Loewner `≤` on `Matrix` itself, and
     `MatrixLoewner.lapMatrix_le` uses it. See §7 and ERRATUM 62.)
  4. **§6: the box is an instance** — `LatticeLaplacian.massive`,
     `LatticeLaplacian.green` and `LatticeField.latticeField` are the general
     definitions at `latticeGraph n`, by `rfl`, and the box's kernel theorem
     is the general one fed `latticeGraph_connected`.
  5. **`trace_lapMatrix_brokenGraph`** — and §4 has a use the moment it
     exists, because the estate already holds two graphs on the same sites:
     W3's `brokenGraph σ` is a subgraph of the lattice, so the contour is
     dominated in the Loewner order and **`2·|γ(σ)|` is the trace of a
     Laplacian**.

  WHAT THIS DOES NOT DO. **No box theorem gets stronger.** §6's box
  statements are one-step consequences of what was already there, and every
  earlier box theorem still says exactly what it said. It does not touch
  reflection positivity — the reflection is genuinely box-specific
  (`Fin.rev`) and `LatticeReflection` stays where it is. And §4 stops at the
  Loewner order on LAPLACIANS: the step a physicist would want next, that
  `green` is ANTItone in the graph, is **not proved here**. §7 said it needed
  a theorem Mathlib lacked; that was wrong, and `MatrixLoewner.green_antitone`
  walks the leg. This file is left as it was written, with §7 recording the
  error, rather than retro-fitted.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import LatticeField
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace GraphLaplacian

open MeasureTheory ProbabilityTheory Matrix Finset
open scoped RealInnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The massive operator over an arbitrary graph -/

/-- **`−Δ_G + m²`** for an arbitrary finite simple graph. -/
def massive (m : ℝ) : Matrix V V ℝ :=
  G.lapMatrix ℝ + Matrix.diagonal (fun _ => m ^ 2)

theorem massive_isSymm (m : ℝ) : (massive G m).IsSymm :=
  (G.isSymm_lapMatrix (R := ℝ)).add (Matrix.isSymm_diagonal _)

/-- **THE MASSIVE OPERATOR ENTRYWISE**: degree plus mass on the diagonal,
    `−1` across an edge, `0` otherwise.

    **RELOCATED 2026-08-10 from `PrismTransfer.massive_apply`**, which stated
    it for an arbitrary graph while living in a file about prisms. Anything
    downstream that needed the entries had to import the prism machinery to
    get them, and `BoxOddReflection` is where that finally bit. The prism
    file keeps the name and now restates this. -/
theorem massive_apply (m : ℝ) (p q : V) :
    massive G m p q
      = (if p = q then (G.degree p : ℝ) + m ^ 2 else 0) - (if G.Adj p q then 1 else 0) := by
  classical
  simp only [massive, Matrix.add_apply, SimpleGraph.lapMatrix, Matrix.sub_apply,
    SimpleGraph.degMatrix, SimpleGraph.adjMatrix, Matrix.diagonal_apply, Matrix.of_apply]
  by_cases h : p = q
  · subst h; simp
  · simp [h]

omit [Fintype V] in
theorem diagonal_massSq_posDef {m : ℝ} (hm : m ≠ 0) :
    (Matrix.diagonal (fun _ : V => m ^ 2)).PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun _ => by positivity

/-- **THE MASSIVE OPERATOR IS POSITIVE DEFINITE** on every finite simple
    graph: positive semidefinite Laplacian plus a positive multiple of the
    identity. Connectivity is not needed and neither is the box. -/
theorem massive_posDef {m : ℝ} (hm : m ≠ 0) : (massive G m).PosDef :=
  Matrix.PosDef.posSemidef_add (SimpleGraph.posSemidef_lapMatrix ℝ G)
    (diagonal_massSq_posDef hm)

theorem massive_isUnit {m : ℝ} (hm : m ≠ 0) : IsUnit (massive G m) :=
  (massive_posDef G hm).isUnit

/-- **THE GREEN FUNCTION** of an arbitrary finite simple graph. -/
noncomputable def green (m : ℝ) : Matrix V V ℝ := (massive G m)⁻¹

theorem green_posDef {m : ℝ} (hm : m ≠ 0) : (green G m).PosDef :=
  (massive_posDef G hm).inv

theorem green_isSymm {m : ℝ} (hm : m ≠ 0) : (green G m).IsSymm := by
  have h := (green_posDef G hm).isHermitian
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h

theorem green_mul_massive {m : ℝ} (hm : m ≠ 0) : green G m * massive G m = 1 :=
  Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp (massive_isUnit G hm))

theorem green_diag_pos {m : ℝ} (hm : m ≠ 0) (p : V) : 0 < green G m p p := by
  simpa using (green_posDef G hm).2 (x := Finsupp.single p (1:ℝ)) (by simp)

/-! ## 2. The zero mode, and why the mass is necessary

The box version of the kernel theorem carried `0 < n`. What that hypothesis
was actually for is `latticeGraph_connected`; here it appears as itself.
-/

theorem lapMatrix_mulVec_const (c : ℝ) : G.lapMatrix ℝ *ᵥ (fun _ => c) = 0 :=
  (SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable (G := G)
    (x := fun _ => c)).mpr fun _ _ _ => rfl

/-- **THE KERNEL IS EXACTLY THE CONSTANTS** on any connected finite simple
    graph. -/
theorem lapMatrix_mulVec_eq_zero_iff_const (hG : G.Connected) (x : V → ℝ) :
    G.lapMatrix ℝ *ᵥ x = 0 ↔ ∃ c : ℝ, x = fun _ => c := by
  obtain ⟨v⟩ := hG.nonempty
  constructor
  · intro h
    have hreach := (SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable
      (G := G) (x := x)).mp h
    exact ⟨x v, funext fun p => hreach p v (hG.preconnected p v)⟩
  · rintro ⟨c, rfl⟩
    exact lapMatrix_mulVec_const G c

/-- **So the massless operator is never positive definite** on a nonempty
    vertex set — connected or not, and in particular on the box.

    Note the proof: `LatticeLaplacian.lattLap_not_posDef` reached this by
    hand, running the constant vector through `nonsing_inv_mul`. Mathlib
    proves `SimpleGraph.det_lapMatrix_eq_zero` in the very file that supplies
    `posSemidef_lapMatrix`, so the lemma was in scope the whole time and the
    box proof was reinventing it. See §7. -/
theorem lapMatrix_not_posDef [Nonempty V] : ¬ (G.lapMatrix ℝ).PosDef := by
  intro hpd
  have hdet : IsUnit (G.lapMatrix ℝ).det := (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
  rw [SimpleGraph.det_lapMatrix_eq_zero] at hdet
  exact not_isUnit_zero hdet

/-! ## 3. The trace -/

theorem lapMatrix_diag (p : V) : G.lapMatrix ℝ p p = (G.degree p : ℝ) := by
  simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix]

/-- **The trace counts ordered bonds.** On the box this is
    `IsingContourEnergy.bondCount`; §6 records the bridge. -/
theorem trace_lapMatrix : Matrix.trace (G.lapMatrix ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
  have hdeg : Matrix.trace (G.lapMatrix ℝ) = ((∑ p : V, G.degree p : ℕ) : ℝ) := by
    rw [Matrix.trace]
    push_cast
    exact Finset.sum_congr rfl fun p _ => lapMatrix_diag G p
  rw [hdeg, SimpleGraph.sum_degrees_eq_twice_card_edges]
  push_cast
  ring

/-! ## 4. Monotonicity in the graph — the statement the box cannot make

Everything above is the box's theory re-hosted. This section is not: it
compares two graphs, and a fixed box has one edge set. Adding edges can only
raise the Dirichlet energy, so the Laplacians are ordered in the Loewner
sense.

The ordering is stated twice here: once as `PosSemidef (B − A)`, which is
what the proof produces, and once as a `≤` between `toEuclideanLin` images
via `LinearMap.instLoewnerPartialOrder` and
`Matrix.isPositive_toEuclideanLin_iff`. **Both are detours.** Mathlib carries
`Matrix.instPartialOrder` — a Loewner `≤` on `Matrix` itself, scoped to
`MatrixOrder` — and `MatrixLoewner.lapMatrix_le` states the theorem in it.
§7 records how this file's review section managed to get that wrong twice in
one day.
-/

/-- **Adding edges raises the Dirichlet energy.** -/
theorem quadratic_form_mono {G G' : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (h : G ≤ G') (x : V → ℝ) :
    Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) x x
      ≤ Matrix.toLinearMap₂' ℝ (G'.lapMatrix ℝ) x x := by
  rw [G.lapMatrix_toLinearMap₂' ℝ x, G'.lapMatrix_toLinearMap₂' ℝ x]
  have hsum : (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0)
      ≤ (∑ i : V, ∑ j : V, if G'.Adj i j then (x i - x j) ^ 2 else 0) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    by_cases hij : G.Adj i j
    · rw [if_pos hij, if_pos (h hij)]
    · rw [if_neg hij]
      split_ifs
      · positivity
      · exact le_rfl
  linarith

/-- **THE LOEWNER ORDER ON GRAPH LAPLACIANS**: `G ≤ G'` implies
    `L_G ≤ L_{G'}`, written as `PosSemidef (L_{G'} − L_G)` because Mathlib
    carries no order on matrices. -/
theorem lapMatrix_sub_posSemidef {G G' : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel G'.Adj] (h : G ≤ G') :
    (G'.lapMatrix ℝ - G.lapMatrix ℝ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (G'.isSymm_lapMatrix (R := ℝ)).sub (G.isSymm_lapMatrix (R := ℝ))
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg,
      ← Matrix.toLinearMap₂'_apply', ← Matrix.toLinearMap₂'_apply']
    exact quadratic_form_mono h x

/-- The same order for the massive operators at a common mass: the mass term
    cancels, so the comparison is entirely the graph's. -/
theorem massive_sub_posSemidef {G G' : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel G'.Adj] (h : G ≤ G') (m : ℝ) :
    (massive G' m - massive G m).PosSemidef := by
  have hEq : massive G' m - massive G m = G'.lapMatrix ℝ - G.lapMatrix ℝ := by
    simp only [massive]
    abel
  rw [hEq]
  exact lapMatrix_sub_posSemidef h

/-- **THE SAME STATEMENT IN MATHLIB'S LOEWNER ORDER.** `L_G ≤ L_{G'}` as
    operators on `EuclideanSpace ℝ V`, with `≤` the library's own
    `LinearMap.instLoewnerPartialOrder` rather than a local abbreviation. -/
theorem lapMatrix_toEuclideanLin_le {G G' : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel G'.Adj] (h : G ≤ G') :
    (G.lapMatrix ℝ).toEuclideanLin ≤ (G'.lapMatrix ℝ).toEuclideanLin := by
  rw [LinearMap.le_def, ← map_sub]
  exact Matrix.isPositive_toEuclideanLin_iff.mpr (lapMatrix_sub_posSemidef h)

theorem massive_toEuclideanLin_le {G G' : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel G'.Adj] (h : G ≤ G') (m : ℝ) :
    (massive G m).toEuclideanLin ≤ (massive G' m).toEuclideanLin := by
  rw [LinearMap.le_def, ← map_sub]
  exact Matrix.isPositive_toEuclideanLin_iff.mpr (massive_sub_posSemidef h m)

/-! ## 5. The Gaussian field -/

/-- **THE GAUSSIAN FIELD OF A GRAPH**: centred, with covariance the graph's
    massive Green function. -/
noncomputable def gaussianField (m : ℝ) : Measure (EuclideanSpace ℝ V) :=
  multivariateGaussian 0 (green G m)

instance isGaussian_gaussianField (m : ℝ) : IsGaussian (gaussianField G m) :=
  isGaussian_multivariateGaussian

omit [DecidableEq V] in
private theorem coord_eq_inner (a : V) (ω : EuclideanSpace ℝ V) :
    ω a = ⟪EuclideanSpace.basisFun V ℝ a, ω⟫ :=
  (EuclideanSpace.basisFun_inner (ι := V) (𝕜 := ℝ) ω a).symm

theorem memLp_eval (m : ℝ) (p : V) :
    MemLp (fun ω : EuclideanSpace ℝ V => ω p) 2 (gaussianField G m) := by
  have h : (fun ω : EuclideanSpace ℝ V => ω p)
      = fun ω : EuclideanSpace ℝ V => ⟪EuclideanSpace.basisFun V ℝ p, ω⟫ := by
    ext ω
    exact coord_eq_inner p ω
  rw [h]
  exact MemLp.const_inner _ IsGaussian.memLp_two_id

theorem integral_eval (m : ℝ) (p : V) : ∫ ω, ω p ∂(gaussianField G m) = 0 := by
  have h : (fun ω : EuclideanSpace ℝ V => ω p)
      = fun ω : EuclideanSpace ℝ V => ⟪EuclideanSpace.basisFun V ℝ p, ω⟫ := by
    ext ω
    exact coord_eq_inner p ω
  rw [h]
  have hid : Integrable (fun ω : EuclideanSpace ℝ V => ω) (gaussianField G m) :=
    IsGaussian.integrable_id
  rw [integral_inner hid]
  have hzero : ∫ ω, ω ∂(gaussianField G m) = 0 := integral_id_multivariateGaussian
  rw [hzero, inner_zero_right]

/-- **THE TWO-POINT FUNCTION IS THE GRAPH'S GREEN FUNCTION.** -/
theorem twoPoint {m : ℝ} (hm : m ≠ 0) (p q : V) :
    ∫ ω, ω p * ω q ∂(gaussianField G m) = green G m p q := by
  have hcov : cov[fun ω : EuclideanSpace ℝ V => ω p,
      fun ω : EuclideanSpace ℝ V => ω q; gaussianField G m] = green G m p q :=
    covariance_eval_multivariateGaussian (green_posDef G hm).posSemidef p q
  have hsub := covariance_eq_sub (memLp_eval G m p) (memLp_eval G m q)
  rw [integral_eval, integral_eval, mul_zero, sub_zero] at hsub
  rw [← hcov, hsub]
  simp only [Pi.mul_apply]

theorem twoPoint_diag_pos {m : ℝ} (hm : m ≠ 0) (p : V) :
    0 < ∫ ω, ω p * ω p ∂(gaussianField G m) := by
  rw [twoPoint G hm p p]
  exact green_diag_pos G hm p

/-! ## 6. The box is an instance

`UNLOCK_WATCHLIST` predicted these bridges would be `rfl`. They are, and the
prediction was worth testing rather than asserting: had `LatticeLaplacian`
been written against a different notion of Laplacian, or with a different
`DecidableRel` instance in scope, the equations would have needed transport
and the two theories would have drifted apart.
-/

section Box

open IsingFiniteVolume IsingContourSeparation IsingContourEnergy

theorem massive_box (n : ℕ) (m : ℝ) :
    LatticeLaplacian.massive n m = massive (latticeGraph n) m := rfl

theorem green_box (n : ℕ) (m : ℝ) :
    LatticeLaplacian.green n m = green (latticeGraph n) m := rfl

theorem latticeField_box (n : ℕ) (m : ℝ) :
    LatticeField.latticeField n m = gaussianField (latticeGraph n) m := rfl

/-- The box's kernel theorem is the general one fed the box's connectivity.
    **This is what "removing a restrictive hypothesis" means here**: `0 < n`
    was never about `n`, it was about the graph being connected. -/
theorem kernel_box {n : ℕ} (hn : 0 < n) (x : Site n → ℝ) :
    LatticeLaplacian.lattLap n *ᵥ x = 0 ↔ ∃ c : ℝ, x = fun _ => c :=
  lapMatrix_mulVec_eq_zero_iff_const _ (latticeGraph_connected hn) x

/-- And the box's trace theorem is the general one, with
    `IsingContourEnergy.bondCount` identified as `2·|E|`. -/
theorem trace_box (n : ℕ) :
    Matrix.trace (LatticeLaplacian.lattLap n)
      = 2 * ((latticeGraph n).edgeFinset.card : ℝ) :=
  trace_lapMatrix _

/-! ### An instance of §4 that is not artificial

`PROOF_STRATEGY` §6 question 1 asks what a unit unlocks. The comparison
theorems of §4 need two graphs on the same vertex set, and the estate
already has them: W3's `IsingContourEnergy.brokenGraph σ` — the bonds a
configuration breaks — is a subgraph of the lattice by construction. So the
contour, which W3 built as an `edgeFinset`, acquires a spectral reading.
-/

theorem brokenGraph_le (n : ℕ) (σ : Config n) : brokenGraph σ ≤ latticeGraph n :=
  fun _ _ h => h.1

/-- The broken-bond Laplacian is dominated by the lattice Laplacian in the
    Loewner order: breaking a subset of the bonds cannot raise the Dirichlet
    energy above the full lattice's. -/
theorem lapMatrix_brokenGraph_le (n : ℕ) (σ : Config n) :
    ((latticeGraph n).lapMatrix ℝ - (brokenGraph σ).lapMatrix ℝ).PosSemidef :=
  lapMatrix_sub_posSemidef (brokenGraph_le n σ)

/-- **THE CONTOUR LENGTH IS A TRACE.** `IsingContourEnergy.contour σ` was
    defined as `(brokenGraph σ).edgeFinset`, so §3 reads it off directly:
    `2·|γ(σ)|` is the trace of a graph Laplacian. W3's counting object and
    W1's spectral object are the same object seen twice. -/
theorem trace_lapMatrix_brokenGraph (n : ℕ) (σ : Config n) :
    Matrix.trace ((brokenGraph σ).lapMatrix ℝ) = 2 * ((contour σ).card : ℝ) :=
  trace_lapMatrix _

end Box

/-! ## 7. Review round 75 — the ways this could be hollow

**"Generalisation could be busywork."** The test `PROOF_STRATEGY` §7 rule 3
implies is whether the general setting BUYS anything, and §4 is the answer:
`quadratic_form_mono` and `lapMatrix_sub_posSemidef` compare two graphs, and
a fixed box cannot state a comparison because it has one edge set. That is
new mathematics in this estate, not a re-hosting. **And the buy is not
hypothetical** — `lapMatrix_brokenGraph_le` and
`trace_lapMatrix_brokenGraph` instantiate it against an object W3 already
built, which is the check ERRATUM 48 asks for when a unit's contribution is
"this makes X possible": attempt X. §1–§3 and §5 are honest re-hosting and
are labelled as such; they are worth having because W1 and W2 want `d = 4`
and a two-dimensional square box was always the wrong carrier.

**"`trace_lapMatrix_brokenGraph` could be a tautology dressed up."** It is
one `rfl` away from §3, and the header says so. What is not trivial is that
it type-checks at all: it needs `contour σ` to BE
`(brokenGraph σ).edgeFinset` up to definitional equality, including the
`DecidableRel` instance W3 had in scope, and had those instances differed the
proof term `trace_lapMatrix _` would have failed. The content is the
identification of two objects built for unrelated reasons, not the arithmetic.

**"The bridges could be doing work and hiding a mismatch."** They are `rfl`,
which is the strongest available evidence that no work is being done — the
box definitions and the general ones are the same term. `kernel_box` is the
one bridge that is not `rfl`, and it is the interesting one: it exhibits
`0 < n` as `latticeGraph_connected hn`, which is exactly the hypothesis
being removed.

**"§4 could be advertised as more than it is."** It is the Loewner order on
LAPLACIANS. The statement a physicist wants is the reverse order on GREEN
FUNCTIONS — more edges, faster decay — and that needs operator antitonicity
of the inverse, `0 < A ≤ B → B⁻¹ ≤ A⁻¹`. **That leg is written down here and
not attempted, per `PROOF_STRATEGY` §3.**

**AMENDED THE SAME DAY, TWICE, AND BOTH DRAFTS OF THIS PARAGRAPH WERE
WRONG. See ERRATUM 62 and `MatrixLoewner.lean`.** Draft one said "Mathlib
has neither a Loewner order on matrices nor that theorem". Draft two
corrected the first half to "the order exists on OPERATORS, not on
`Matrix`", added `lapMatrix_toEuclideanLin_le` as the fix, and asserted the
second half survived "a grep for that shape across
`Mathlib/LinearAlgebra/Matrix/` and `Mathlib/Analysis/`".

**Both halves are false.** `Mathlib/Analysis/Matrix/Order.lean` — a file
none of the three probes opened — defines `Matrix.instPartialOrder`,
`A ≤ B := (B − A).PosSemidef`, scoped to `MatrixOrder`. And
`CStarAlgebra.inv_le_inv` is the antitonicity, in
`Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean`, which the
grep did not reach because it searched `Analysis/` for matrix-shaped names
and the theorem is stated for C⋆-algebras.

**Corrected by proving, in both rounds.** `lapMatrix_toEuclideanLin_le`
below stays — it is true and it is where the second draft's mistake led —
but `MatrixLoewner.lapMatrix_le` now states the same thing in the order
Mathlib actually has, and `MatrixLoewner.green_antitone` walks the leg this
paragraph said was not attempted. **The estate's `PosSemidef (B − A)`
formulations were a detour around notation that existed.**

**"A library lemma could have been reinvented."** One was, and it is
recorded rather than quietly fixed. `LatticeLaplacian.lattLap_not_posDef`
runs the constant vector through `nonsing_inv_mul` by hand;
`SimpleGraph.det_lapMatrix_eq_zero` is a `@[simp]` lemma in the same Mathlib
file as `posSemidef_lapMatrix`, which `LatticeLaplacian` already imported —
so it was in scope and unused. **The box theorem is not wrong and is not
being deleted** — a working proof stays — but the pattern is worth naming
and generalises past this instance: the grep that found `lapMatrix` stopped
at the lemma it went looking for and did not read the file. ERRATUM 40/42
says an "absent from Mathlib" claim decays; this is the weaker cousin, where
nothing was claimed absent and the lemma was simply never looked for.

**"This could be claimed as progress on W1."** It is not. W1's failing step
is reflection positivity, §4 stops one theorem short of even the ordering
that would bear on it, and the reflection itself is box-specific and
untouched in `LatticeReflection`. What has changed is the carrier: the
covariance layer is no longer restricted to two dimensions, so when a
`d = 4` graph is written down the layer is already over it.
-/

end GraphLaplacian
