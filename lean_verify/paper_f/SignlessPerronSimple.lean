import SignlessPrimitive
import PerronSimple
import PerronVector
import HermitianSpectralMapping
import HermitianCharpoly
import HermitianFlatSpectrum

/-!
# Perron–Frobenius for a connected graph's signless Laplacian

**THE TWO STEPS `SignlessPrimitive` LEFT, AND THE THEOREM THEY WERE FOR.** That file proved
`Q ^ Fintype.card V` is entrywise positive for a connected graph on two or more vertices — which
is verbatim the hypothesis `PerronSimple.top_eigenspace_dim_one` takes — and stopped, naming what
remained: *that `Q ^ card V` is Hermitian with top eigenvalue `M ^ card V`, and that `Q`'s top
eigenspace sits inside that power's.* Both are here, and with them:

**`top_simple_connected` — THE LARGEST EIGENVALUE OF A CONNECTED GRAPH'S SIGNLESS LAPLACIAN IS
SIMPLE.** Perron–Frobenius, for the operator this fortnight has been about, on every connected
graph with at least two vertices and no other hypothesis.

**AND IT CLOSES THE FLAT-SPECTRUM QUESTION, WHICH IS WHY IT WAS BUILT.**
`SignlessFlatWitness` found a flat spectrum with `M = 2` on two disjoint edges and asked whether a
**connected** graph could do it; `SignlessFlatConnected` answered *no* for two-colourable graphs by
looking at the kernel, and could not reach the rest because a connected non-two-colourable `Q` is
positive definite and has no kernel to look at. **`flat_implies_simple_connected` answers it for
every connected graph at once**, by looking at the top instead of the bottom.

**WHAT THE PROOF ACTUALLY NEEDED, AND IT WAS NOT IRREDUCIBILITY.** `topEig_pow` is the spectral
step: for a Hermitian matrix with non-negative eigenvalues the top of `A ^ k`'s spectrum is the
`k`-th power of the top of `A`'s, from `HermitianSpectralMapping.eigenvalues_pow_multiset` and
monotonicity. `mv_iff` is the plumbing between `RayleighMatrix.mv` on `EuclideanSpace` and
`Matrix.mulVec` on the plain function type, which the Perron chain needed and did not have as a
statement. Everything else is `PerronVector.exists_nonneg_top_eigenvector`,
`PerronSimple.pos_of_nonneg_top_eigenvector` and `PerronSimple.top_eigenspace_dim_one`, composed.

## What is proved

**`mv_iff`** — an eigenvector equation on `EuclideanSpace` is the same as one on `n → ℝ`.

**`topEig`, `le_topEig`, `exists_topEig`** — the top of a Hermitian spectrum, as a value.

**`exists_pow_eigenvalue`, `topEig_pow`** — the top of `A ^ k`'s spectrum is the top of `A`'s,
raised to `k`, when the eigenvalues are non-negative.

**`pow_mulVec_of_eigen`** — an eigenvector of `A` at `μ` is one of `A ^ k` at `μ ^ k`.

**`top_simple_connected`** — **THE FILE'S THEOREM.**

**`flat_implies_simple_connected`** — so on a connected graph a flat spectrum is a simple one.

## What is NOT here

* **NO SECOND EIGENVALUE, as of 2026-09-13 (entry 17).** Perron gives simplicity at the top and
  says nothing about any other multiplicity; the rest of a connected graph's signless spectrum can
  be as degenerate as it likes, and the complete multipartite tables in this chain show it is.
* **NO SPECTRAL GAP.** That the top is simple is not that it is separated, and nothing here bounds
  the second eigenvalue away from the first. `PerronGap` is a different chain and is untouched.
* **NOTHING FOR A DISCONNECTED GRAPH.** There no power is entrywise positive and the top
  eigenvalue can repeat once per component — `SignlessFlatWitness` is exactly that.
* **NOTHING GENERAL ABOUT IRREDUCIBLE MATRICES.** The route runs through primitivity of this
  particular family; `Matrix.IsIrreducible` appears nowhere, and **no general Perron–Frobenius is
  added to the estate** (`ERRATUM 246`).
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): for the graph theorems, a finite vertex
type with decidable equality and adjacency, `Nontrivial V` and `G.Connected`. The spectral helpers
take `IsHermitian` and, for `topEig_pow`, non-negative eigenvalues.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessPerronSimple

open Matrix SimpleGraph LaplacianSignless RayleighMatrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem mv_iff (A : Matrix n n ℝ) (M : ℝ) (x : n → ℝ) :
    mv A (WithLp.toLp 2 x) = M • (WithLp.toLp 2 x) ↔ A *ᵥ x = M • x := by
  constructor
  · intro h
    funext i
    have := congrFun (congrArg WithLp.ofLp h) i
    simpa [mv] using this
  · intro h
    apply WithLp.ofLp_injective (p := 2)
    funext i
    simpa [mv] using congrFun h i

/-- The top of a Hermitian matrix's spectrum. -/
noncomputable def topEig {A : Matrix n n ℝ} (hA : A.IsHermitian) [Nonempty n] : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty hA.eigenvalues

theorem le_topEig {A : Matrix n n ℝ} (hA : A.IsHermitian) [Nonempty n] (i : n) :
    hA.eigenvalues i ≤ topEig hA :=
  Finset.le_sup' _ (Finset.mem_univ i)

theorem exists_topEig {A : Matrix n n ℝ} (hA : A.IsHermitian) [Nonempty n] :
    ∃ i, hA.eigenvalues i = topEig hA := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := n)) hA.eigenvalues
  exact ⟨i, hi.symm⟩

theorem exists_pow_eigenvalue {A : Matrix n n ℝ} (hA : A.IsHermitian) (k : ℕ) (j : n) :
    ∃ i, (hA.pow k).eigenvalues i = hA.eigenvalues j ^ k := by
  have hmem : hA.eigenvalues j ^ k
      ∈ Multiset.map (fun i => hA.eigenvalues i ^ k) Finset.univ.val :=
    Multiset.mem_map_of_mem _ (Finset.mem_val.mpr (Finset.mem_univ j))
  rw [← HermitianSpectralMapping.eigenvalues_pow_multiset hA k, Multiset.mem_map] at hmem
  obtain ⟨i, -, hi⟩ := hmem
  exact ⟨i, hi⟩

theorem topEig_pow [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (hnn : ∀ i, 0 ≤ hA.eigenvalues i) (k : ℕ) :
    topEig (hA.pow k) = topEig hA ^ k := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ fun i _ => ?_
    obtain ⟨j, hj⟩ := HermitianSpectralMapping.exists_eigenvalue_pow_eq hA k i
    rw [hj]
    gcongr
    exacts [hnn j, le_topEig hA j]
  · obtain ⟨i₀, hi₀⟩ := exists_topEig hA
    obtain ⟨i, hi⟩ := exists_pow_eigenvalue hA k i₀
    rw [← hi₀, ← hi]
    exact le_topEig (hA.pow k) i

theorem pow_mulVec_of_eigen {A : Matrix n n ℝ} {μ : ℝ} {x : n → ℝ} (h : A *ᵥ x = μ • x) :
    ∀ k, (A ^ k) *ᵥ x = μ ^ k • x := by
  intro k
  induction k with
  | zero => simp
  | succ m ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul,
      pow_succ, mul_comm]

open LaplacianSignless SignlessPrimitive in
theorem top_simple_connected {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G)
      - (topEig (LaplacianSignlessDefinite.signlessLap_isHermitian G)) • LinearMap.id)) ≤ 1 := by
  classical
  set hQ := LaplacianSignlessDefinite.signlessLap_isHermitian G with hQdef
  set k := Fintype.card V with hk
  have hPpos : ∀ i j, 0 < ((signlessLap G) ^ k) i j := pow_card_pos G hconn
  have hPnn : ∀ i j, 0 ≤ ((signlessLap G) ^ k) i j := fun i j => (hPpos i j).le
  obtain ⟨M, u, hune, hunn, hmax, -, hMu⟩ :=
    PerronVector.exists_nonneg_top_eigenvector (hQ.pow k) hPnn
  -- `M` is positive, because `P` is entrywise positive and `u` is non-negative and non-zero.
  have hupos0 : ∃ i, 0 < (WithLp.ofLp u) i := by
    by_contra hno
    push Not at hno
    exact hune (by ext i; exact le_antisymm (hno i) (hunn i))
  obtain ⟨i₀, hi₀⟩ := hupos0
  have hMpos : 0 < M := by
    have hrow : 0 < (WithLp.ofLp (RayleighMatrix.mv ((signlessLap G) ^ k) u)) i₀ := by
      rw [RayleighMatrix.mv_row]
      exact Finset.sum_pos' (fun j _ => mul_nonneg (hPnn i₀ j) (hunn j))
        ⟨i₀, Finset.mem_univ _, mul_pos (hPpos i₀ i₀) hi₀⟩
    rw [hMu] at hrow
    have : (WithLp.ofLp (M • u)) i₀ = M * (WithLp.ofLp u) i₀ := rfl
    rw [this] at hrow
    nlinarith [hrow, hi₀]
  have hupos : ∀ i, 0 < (WithLp.ofLp u) i :=
    PerronSimple.pos_of_nonneg_top_eigenvector hPpos hMpos hMu hunn hune
  -- `M` is the top of `P`'s spectrum: at most, by `hmax`; at least, because `u` witnesses it.
  have hueig : ((signlessLap G) ^ k) *ᵥ (WithLp.ofLp u) = M • (WithLp.ofLp u) := by
    have := (mv_iff ((signlessLap G) ^ k) M (WithLp.ofLp u)).1 (by simpa using hMu)
    simpa using this
  have hMtop : M = topEig (hQ.pow k) := by
    refine le_antisymm ?_ (Finset.sup'_le _ _ fun i _ => hmax i)
    have hmem : M ∈ Finset.univ.image (hQ.pow k).eigenvalues := by
      rw [HermitianCharpoly.mem_image_eigenvalues_iff]
      exact ⟨WithLp.ofLp u, fun h => hune (by ext i; simpa using congrFun h i), hueig⟩
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
    rw [← hi]; exact le_topEig (hQ.pow k) i
  have hnn : ∀ i, 0 ≤ hQ.eigenvalues i :=
    (LaplacianSignlessDefinite.signlessLap_posSemidef G).eigenvalues_nonneg
  have hMeq : M = topEig hQ ^ k := by rw [hMtop, topEig_pow hQ hnn]
  -- every top eigenvector of `Q` is a top eigenvector of `P`, hence a multiple of `u`
  refine le_trans (Submodule.finrank_mono (?_ : _ ≤ Submodule.span ℝ {WithLp.ofLp u}))
    (le_of_eq_of_le (finrank_span_singleton (fun h => absurd (hupos i₀) (by simp [h]))) le_rfl)
  intro x hx
  rw [LinearMap.mem_ker] at hx
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx
  rw [Matrix.toLin'_apply, sub_eq_zero] at hx
  have hPx : ((signlessLap G) ^ k) *ᵥ x = M • x := by
    rw [pow_mulVec_of_eigen hx k, hMeq]
  obtain ⟨c, hc⟩ := PerronSimple.top_eigenspace_dim_one hPpos hMpos hMu hupos
    ((mv_iff ((signlessLap G) ^ k) M x).2 hPx)
  refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
  funext i
  simpa using (congrFun (congrArg WithLp.ofLp hc) i).symm

/-- **SO ON A CONNECTED GRAPH A FLAT SIGNLESS SPECTRUM IS A SIMPLE ONE**, which closes the
question `SignlessFlatWitness` asked and `SignlessFlatConnected` answered only for the
two-colourable half. -/
theorem flat_implies_simple_connected {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) {M : ℕ}
    (hflat : ∀ μ ∈ Finset.univ.image
        (LaplacianSignlessDefinite.signlessLap_isHermitian G).eigenvalues,
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G) - μ • LinearMap.id)) = M) :
    M = 1 := by
  classical
  set hQ := LaplacianSignlessDefinite.signlessLap_isHermitian G with hQdef
  obtain ⟨i₀, hi₀⟩ := exists_topEig hQ
  have hmem : topEig hQ ∈ Finset.univ.image hQ.eigenvalues :=
    Finset.mem_image.mpr ⟨i₀, Finset.mem_univ _, hi₀⟩
  have hle := top_simple_connected G hconn
  have hpos := HermitianFlatSpectrum.finrank_pos_of_mem_image hQ hmem
  rw [hflat _ hmem] at hle hpos
  omega

end SignlessPerronSimple
