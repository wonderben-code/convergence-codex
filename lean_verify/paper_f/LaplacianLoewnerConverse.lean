import LaplacianSharpEquality
import RayleighPow

/-!
# The characterisation in the Loewner order: the constant cannot be lowered iff the graph is
two-colourable

`LaplacianSharpEquality` characterised attainment **at a supplied vector**: a connected `Δ`-regular
graph has some `x ≠ 0` with `xᵀLx = 2Δ‖x‖²` exactly when it is two-colourable. It fenced itself
there, and named what it was not doing — the statement `RegularBipartiteSharp` and
`CycleSpectralBound` are actually phrased in, which is about the **Loewner order**:

```
massive G m ≼ c·1  can be had with  c < 2Δ + m²   ⟺   G is NOT two-colourable
```

**That fence is closed here, and the route it traced is the route taken.** For an arbitrary
Hermitian matrix this estate already had both variational directions —
`RayleighPow.eigenvalues_le_of_quadForm_le` (a quadratic-form bound bounds every eigenvalue, by
testing it on each eigenvector) and `RayleighMatrix.quadForm_le_of_eigenvalues_le` (and back) —
together with `RayleighMatrix.mv_eigenvectorBasis`, the vector that **attains** the form at each
eigenvalue. The argument is then three lines of logic on top of the previous unit:

* every eigenvalue of `massive G m` is at most `2Δ + m²`, which is `LaplacianDegreeBound` read
  through the first direction;
* if `G` is connected, regular and **not** two-colourable then no non-zero vector attains that
  value, so no **eigenvector** does, so every eigenvalue is **strictly** below it;
* the eigenvalue list is finite, so its maximum is a `c < 2Δ + m²`, and the second direction turns
  that back into `massive ≼ c·1`.

**THE `∀ c` HYPOTHESIS IS NEVER VACUOUS**, which is worth one sentence because a "cannot be
lowered" statement quantified over `c` would say nothing if no `c` worked:
`LaplacianDegreeBound.massive_le_smul_one` supplies `c = 2Δ + m²` at every graph with a degree
bound, so the antecedent always has a witness.

**THIS IS `CycleSpectralBound`'s ARGUMENT WITH THE BASIS TAKEN AWAY.** That file proved the odd
cycle does not attain by computing the entire character spectrum and taking a `Finset.sup'` of it;
`massive_le_smul_one_of_eigenvalues_le` is its bridge from an eigenvalue bound to a Loewner bound,
and it is available only because the characters diagonalise the cycle explicitly. Here the
eigenbasis is `Matrix.IsHermitian.eigenvectorBasis` and nothing about it is known or needed, so the
conclusion holds for **every** connected regular graph. The odd cycle and the odd periodic lattice
in every dimension are instantiated below (`ERRATUM 201`), the first of them recovering the shape
of `odd_cycle_lt` with no spectrum computed.

**THE ESTATE'S FIRST USE OF AN ABSTRACT EIGENVALUE LIST ON A GRAPH OPERATOR**, probed rather than
assumed (`ERRATUM 42`, by shape and not by name): no file in `paper_f` states `IsHermitian` of
`massive` or of `SimpleGraph.lapMatrix`, and no occurrence of `eigenvalues` in `paper_f` is applied
to either — the two that come close, `CycleLaplacianSpectrum` and `CycleSpectralBound`, work with
an explicit character family and never form `hA.eigenvalues`. So `massive_isHermitian` is new, and
it is one rewrite.

## What this does NOT do

**It does not identify the constant.** `exists_lt_massive_le_smul_one` produces *a* `c` strictly
below `2Δ + m²` — the maximum of the eigenvalue list — and says nothing about what that maximum
is, nor that it is positive, which `CycleSpectralBound.odd_cycle_lt` does deliver on the cycle.
For the odd cycle that file names the constant as a supremum of cosines and declines to evaluate
it; nothing here improves on that, and no closed form for the spectral gap is claimed for any
graph.

**It does not remove connectivity**, which is false without: `C₃ ⊔ C₄` is 2-regular, attains, and
is not two-colourable. **It does not touch non-regular graphs**, where `RegularBipartiteSharp`
only has the averaged statement. **And it says nothing about a field**: no measure is built, `OS4`
does not move, and no published tag moves.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LaplacianLoewnerConverse

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection LaplacianSharpEquality
open scoped MatrixOrder

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The bridge between the matrix pairing and the inner product -/

/-- `massive` is Hermitian, which over `ℝ` is its symmetry and one rewrite. -/
theorem massive_isHermitian (m : ℝ) : (massive G m).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact massive_isSymm G m

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The quadratic form of a matrix, read on `EuclideanSpace` and read with `dotProduct`, are the
same number. `RayleighMatrix` works on the former because that is where the eigenbasis lives; every
graph statement in this estate is written in the latter. -/
theorem inner_mv_eq (A : Matrix V V ℝ) (v : EuclideanSpace ℝ V) :
    inner ℝ v (RayleighMatrix.mv A v) = (WithLp.ofLp v) ⬝ᵥ A *ᵥ (WithLp.ofLp v) := by
  rw [RayleighMatrix.inner_expand, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RayleighMatrix.mv_row]
  rfl

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The same for the norm. -/
theorem inner_self_eq (v : EuclideanSpace ℝ V) :
    inner ℝ v v = (WithLp.ofLp v) ⬝ᵥ (WithLp.ofLp v) := by
  rw [RayleighMatrix.inner_expand, dotProduct]

/-! ## 2. Every eigenvalue is below the constant, and strictly so when the colouring fails -/

/-- `LaplacianDegreeBound`'s bound read through the variational direction: **every** eigenvalue of
`massive` is at most `2Δ + m²`. -/
theorem eigenvalues_massive_le {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (m : ℝ) (j : V) :
    (massive_isHermitian G m).eigenvalues j ≤ 2 * (Δ : ℝ) + m ^ 2 := by
  refine RayleighPow.eigenvalues_le_of_quadForm_le (massive_isHermitian G m) (fun v => ?_) j
  rw [inner_mv_eq, inner_self_eq]
  set w := WithLp.ofLp v with hw
  have h1 := dotProduct_massive_mulVec G m w
  have h2 := LaplacianDegreeBound.lapMatrix_quadForm_le G
    (fun p => le_of_eq (by rw [hreg p])) w
  have h3 : (2 * (Δ : ℝ) + m ^ 2) * (w ⬝ᵥ w)
      = 2 * (Δ : ℝ) * (w ⬝ᵥ w) + m ^ 2 * (w ⬝ᵥ w) := by ring
  rw [h3, h1]
  linarith

/-- **AND STRICTLY BELOW IT WHEN THE GRAPH IS NOT TWO-COLOURABLE.** The eigenvector at an
eigenvalue equal to the constant would attain the quadratic form there, and
`LaplacianSharpEquality.colorable_two_of_quadForm_eq` says nothing does. -/
theorem eigenvalues_massive_lt_of_not_colorable {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hG : G.Connected) (m : ℝ) (hcol : ¬ G.Colorable 2) (j : V) :
    (massive_isHermitian G m).eigenvalues j < 2 * (Δ : ℝ) + m ^ 2 := by
  refine lt_of_le_of_ne (eigenvalues_massive_le G hreg m j) fun heq => hcol ?_
  set hH := massive_isHermitian G m with hHdef
  set b : EuclideanSpace ℝ V := hH.eigenvectorBasis j with hb
  have hnorm : inner ℝ b b = (1 : ℝ) := by
    have h1 : ‖b‖ = 1 := (hH.eigenvectorBasis).orthonormal.1 j
    have h2 := real_inner_self_eq_norm_sq b
    rw [h2, h1]; norm_num
  have hq : inner ℝ b (RayleighMatrix.mv (massive G m) b) = hH.eigenvalues j := by
    rw [RayleighMatrix.mv_eigenvectorBasis hH, real_inner_smul_right, hnorm, mul_one]
  rw [inner_mv_eq] at hq
  rw [inner_self_eq] at hnorm
  set w := WithLp.ofLp b with hw
  have hne : w ≠ 0 := by
    intro h0
    rw [h0] at hnorm
    simp [dotProduct] at hnorm
  have hattain : w ⬝ᵥ (massive G m) *ᵥ w = (2 * (Δ : ℝ) + m ^ 2) * (w ⬝ᵥ w) := by
    rw [hq, heq, hnorm, mul_one]
  exact colorable_two_of_quadForm_eq G hreg hG hne
    ((quadForm_eq_iff_neg_adj G hreg w).mpr
      ((massive_quadForm_eq_iff_neg_adj G hreg m w).mp hattain))

/-! ## 3. Hence the constant can be lowered, and the characterisation -/

/-- **THE CONVERSE `LaplacianSharpEquality` DECLINED TO CLAIM.** A connected regular graph that is
not two-colourable admits a strictly smaller constant in the Loewner order. -/
theorem exists_lt_massive_le_smul_one [Nonempty V] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hG : G.Connected) (m : ℝ) (hcol : ¬ G.Colorable 2) :
    ∃ c : ℝ, c < 2 * (Δ : ℝ) + m ^ 2 ∧ massive G m ≤ c • (1 : Matrix V V ℝ) := by
  classical
  set hH := massive_isHermitian G m with hHdef
  refine ⟨Finset.univ.sup' Finset.univ_nonempty hH.eigenvalues, ?_, ?_⟩
  · rw [Finset.sup'_lt_iff]
    exact fun j _ => eigenvalues_massive_lt_of_not_colorable G hreg hG m hcol j
  · refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_))
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      refine Matrix.IsSymm.sub ?_ (massive_isSymm G m)
      rw [Matrix.smul_one_eq_diagonal]
      exact Matrix.isSymm_diagonal _
    · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg]
      have h1 : x ⬝ᵥ ((Finset.univ.sup' Finset.univ_nonempty hH.eigenvalues)
            • (1 : Matrix V V ℝ)) *ᵥ x
          = (Finset.univ.sup' Finset.univ_nonempty hH.eigenvalues) * (x ⬝ᵥ x) := by
        rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
      rw [h1]
      have hmax : ∀ j : V, hH.eigenvalues j
          ≤ Finset.univ.sup' Finset.univ_nonempty hH.eigenvalues :=
        fun j => Finset.le_sup' _ (Finset.mem_univ j)
      have := RayleighMatrix.quadForm_le_of_eigenvalues_le hH hmax (WithLp.toLp 2 x)
      rwa [inner_mv_eq, inner_self_eq] at this

/-- **THE CHARACTERISATION IN THE LOEWNER ORDER.** For a connected regular graph, the constant
`2Δ + m²` cannot be lowered **exactly when** the graph is two-colourable — the forward half being
`RegularBipartiteSharp`'s and the converse being §3's. -/
theorem massive_le_smul_one_iff_colorable [Nonempty V] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hG : G.Connected) (m : ℝ) :
    (∀ c : ℝ, massive G m ≤ c • (1 : Matrix V V ℝ) → 2 * (Δ : ℝ) + m ^ 2 ≤ c)
      ↔ G.Colorable 2 := by
  constructor
  · intro hmin
    by_contra hcol
    obtain ⟨c, hlt, hle⟩ := exists_lt_massive_le_smul_one G hreg hG m hcol
    exact absurd (hmin c hle) (not_le.mpr hlt)
  · intro hcolor c hle
    obtain ⟨σ, hσ⟩ := RegularBipartiteSharp.exists_signColouring_of_colorable hcolor
    exact RegularBipartiteSharp.le_of_massive_le_smul_one_of_regular G hreg hσ m c hle

/-! ## 4. The two families, with no spectrum computed -/

/-- **THE ODD CYCLE, WITHOUT ITS EIGENVALUES.** `CycleSpectralBound.odd_cycle_lt` proves this from
the full character spectrum; here it is the general theorem at `Δ = 2`. **The two are NOT the same
statement and the differences run both ways**: that one assumes `m ≠ 0` and this one does not, and
that one also delivers `0 < c` while this one does not — positivity of the eigenvalue maximum is a
separate fact and is not proved here. Neither identifies the constant. -/
theorem odd_cycle_exists_lt (M : ℕ) (m : ℝ) :
    ∃ c : ℝ, c < 4 + m ^ 2 ∧ massive (cycleGraph (2 * M + 3)) m
      ≤ c • (1 : Matrix (Fin (2 * M + 3)) (Fin (2 * M + 3)) ℝ) := by
  have hreg : (cycleGraph (2 * M + 3)).IsRegularOfDegree 2 := fun v =>
    cycleGraph_degree_three_le (n := 2 * M) (v := v)
  have hconn : (cycleGraph (2 * M + 3)).Connected := by
    have := SimpleGraph.cycleGraph_connected (n := 2 * M + 2)
    simpa using this
  have hcol : ¬ (cycleGraph (2 * M + 3)).Colorable 2 := by
    intro hc
    have hchi : (cycleGraph (2 * M + 3)).chromaticNumber = 3 :=
      chromaticNumber_cycleGraph_of_odd (2 * M + 3) (by omega) ⟨M + 1, by ring⟩
    have hle := hc.chromaticNumber_le
    rw [hchi] at hle
    norm_num at hle
  obtain ⟨c, hlt, hle⟩ := exists_lt_massive_le_smul_one _ hreg hconn m hcol
  exact ⟨c, by norm_num at hlt ⊢; linarith, hle⟩

/-- **AND THE ODD PERIODIC LATTICE, IN EVERY DIMENSION.** `LaplacianSharpEquality` got this far in
the vector-level language; this is the Loewner statement, which is the one
`LaplacianDegreeBound` and `TorusRegular` are phrased in. -/
theorem torus_odd_exists_lt {d n : ℕ} (hodd : Odd (n + 1)) (h3 : 3 ≤ n + 1) (m : ℝ) :
    ∃ c : ℝ, c < 4 * ((d : ℝ) + 1) + m ^ 2 ∧ massive (torusGraph (d + 1) (n + 1)) m
      ≤ c • (1 : Matrix (Site (d + 1) (n + 1)) (Site (d + 1) (n + 1)) ℝ) := by
  haveI : Nonempty (Site (d + 1) (n + 1)) := TorusRegular.nonempty_site (by omega)
  obtain ⟨c, hlt, hle⟩ := exists_lt_massive_le_smul_one _
    (RegularSelfEmbedding.torusGraph_isRegularOfDegree h3)
    (TorusDecay.torusGraph_connected (d + 1) (by omega)) m
    (torus_not_colorable_two_of_odd hodd h3)
  refine ⟨c, ?_, hle⟩
  have : (2 : ℝ) * ((2 * (d + 1) : ℕ) : ℝ) = 4 * ((d : ℝ) + 1) := by push_cast; ring
  linarith [this ▸ hlt]

end LaplacianLoewnerConverse
