import FieldLaplacianInstance
import FieldSignReflection

/-!
# The converse of the criterion, and so the door swings both ways

`FieldSimpleCriterion.eigenvalues_injective_of_finrank_le_one` proved that *every eigenspace of
`massive` is at most a line* forces the propagator's spectrum to be simple, and
`FieldLaplacianSimple` restated that hypothesis about the graph's Laplacian alone and called it a
door. Both files fenced the same missing step, and `FieldLaplacianInstance` fenced it in as many
words: the reverse implication *"is true for a symmetric matrix because the eigenspaces span, and
is **not proved anywhere in this estate**"*. It is proved here, and carried back to the graph.

## What is proved

**`coeff_eq_zero_of_mv_smul`, `eq_smul_of_mv_smul`** — for a Hermitian matrix whose eigenvalue
function is injective, an eigenvector at `ν` is a **multiple of the single eigenbasis vector
sitting at `ν`**. The first step is the estate's own `RayleighMatrix.inner_basis_mv`: pairing the
eigenvector equation against an eigenbasis vector gives `(λⱼ - ν) · ⟨eⱼ, v⟩ = 0`, so every
coefficient off `ν` vanishes; injectivity is what leaves at most one that does not.

**`finrank_le_one_of_injective`** — **so every eigenspace of such a matrix is at most a line.**
This is the general fact, about **one Hermitian matrix and its own eigenspaces**. The two cases —
`ν` is an eigenvalue, and `ν` is not — are separated by hand: in the first the eigenspace sits
inside the span of one basis vector, in the second every coefficient vanishes and the eigenspace
is `⊥`.

**`injective_of_finrank_le_one`, `finrank_le_one_iff_injective`** — **and for one Hermitian matrix
the two conditions are one condition**: every eigenspace at most a line **iff** the eigenvalues
are pairwise distinct.

**`finrank_massive_le_one_of_eigenvalues_injective`** — **the literal converse of the criterion.**
This is not the same statement as the one above: the criterion's hypothesis is about the
eigenspaces of `massive` and its conclusion about the eigenvalues of `green`, so the one-matrix
fact does not apply on its own. The bridge is
`FieldSignReflection.green_mulVec_of_massive_mulVec`, which sends an eigenvector of `massive` at
`ν ≠ 0` to an eigenvector of `green` at `ν⁻¹`; at `ν = 0` the eigenspace is `⊥` because
`green * massive = 1`.

**`finrank_lapMatrix_le_one_of_eigenvalues_injective`** — **and back to the graph's Laplacian**,
by `FieldLaplacianSimple.ker_massive_eq`, which shifts the eigenvalue and leaves the subspace
alone.

**`finrank_massive_le_one_iff`, `finrank_lapMatrix_le_one_iff`** — **so the criterion is an
equivalence and the door of `FieldLaplacianSimple` is a two-way door.** *Every eigenspace of the
Laplacian is at most a line* ⟺ *every eigenspace of `massive` is at most a line* ⟺ *the
propagator's spectrum is simple*. The hypothesis the whole symmetry chain runs on has a spectral
name.

**`lapMatrix_isHermitian`, `finrank_lapMatrix_le_one_iff_injective`** — **and the fence
`FieldLaplacianSimple` left on its own side comes down too**: for the Laplacian, *every eigenspace
is at most a line* is exactly *the `|V|` eigenvalues are pairwise distinct*. That statement takes
**no mass, no propagator and no hypothesis at all**.

**`eigenvalues_injective_iff_lapMatrix`** — **so at every non-zero mass the propagator and the
graph's Laplacian have simple spectra together**, with no eigenspace mentioned on either side.

**`not_eigenvalues_injective_of_no_adj`** — **so an edgeless graph on two or more vertices has a
degenerate propagator spectrum**, by contraposition through
`FieldLaplacianInstance.not_finrank_le_one_of_no_adj`.

## What is NOT here

**NO CHARACTERISATION OF THE GRAPHS.** Four conditions are shown equal to each other; **none of
them is shown equal to a property of the graph one could check by looking at it**. The path graph
still satisfies them and edgeless graphs still fail them, and those are still the only two
families known. The standing question on `UNLOCK_WATCHLIST` is untouched — an equivalence between
spectral conditions is not a characterisation of the graphs satisfying them.

⚠ **A THIRD FAMILY AND A NECESSARY CONDITION ARRIVED THE SAME DAY, AND THE PARAGRAPH ABOVE IS KEPT
AS WRITTEN** (`ERRATUM 94`). `FieldSimpleConnected`: **connectivity is necessary**
(`preconnected_of_finrank_le_one`, one eigenvalue's worth of work — at `ν = 0` the eigenspace
counts components) **and not sufficient**, every **periodic lattice** of dimension `d ≥ 1` being
connected and failing at every mass.
**The sentence that matters is unchanged**: still no characterisation, and still only the path on
the satisfying side.

**`injective_of_finrank_le_one` REPEATS AN ARGUMENT THE ESTATE ALREADY HAD.** It is
`FieldSimpleCriterion.eigenvalues_injective_of_finrank_le_one`'s proof with the `massive`/`green`
inversion step deleted — same orthonormal-basis contradiction, same
`Submodule.eq_of_le_of_finrank_le`.
**The criterion is not re-derived from it here**, though it could be: the transfer runs the other
way too (`FieldSimpleCriterion.massive_mulVec_of_green_mulVec`). Filed, not done, no cost claimed
(`ERRATUM 246`).

**`not_eigenvalues_injective_of_no_adj` IS NOT NEW INFORMATION**, and is not claimed to be. On an
edgeless graph `FieldSymmetryEdgeless.green_eq_smul_of_no_adj` says the propagator is a scalar
matrix outright, so every eigenvalue is the same one and degeneracy is immediate. It is here as a
**demonstration that the new implication carries on an example**, in the manner of
`FieldLaplacianInstance`, not as a fact that needed it.

⚠ **AND IT IS SUBSUMED WITHIN THE HOUR, KEPT AND NOT DELETED** (`ERRATUM 94`).
`FieldSimpleConnected.not_eigenvalues_injective_of_not_preconnected` is the same statement for
**any** disconnected graph, and `FieldSimpleConnected.not_preconnected_of_no_adj` shows *no edges*
plus *two or more vertices* is exactly a failure of connectivity — so the theorem below is that one
at one family.

**NOTHING IS SHOWN TO BE EXACTLY A LINE.** Every eigenspace statement here is an upper bound,
`≤ 1`. No eigenspace is shown non-trivial, and no `Nonempty` hypothesis appears anywhere.

**NO NON-HERMITIAN MATRIX.** §§1–3 take a `Matrix.IsHermitian` hypothesis on `A` and use the
spectral theorem through `Matrix.IsHermitian.eigenvectorBasis`; nothing here says anything about a
matrix that is not symmetric, where an eigenvalue can be simple and its eigenspace still fail to
split off.

**NO EIGENVALUE IS COMPUTED.** `Function.Injective hA.eigenvalues` is a statement about Mathlib's
enumeration of the spectrum; **no index-matching between two enumerations is done anywhere in this
file**, and none is needed, exactly as in `FieldLaplacianSimple`.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`). §§1–3 take **no mass, no graph and no
propagator**: they are statements about a Hermitian matrix over an arbitrary `Fintype`. In §§4–5,
`m ≠ 0` is taken by `finrank_massive_le_one_of_eigenvalues_injective`,
`finrank_lapMatrix_le_one_of_eigenvalues_injective`, `finrank_massive_le_one_iff`,
`finrank_lapMatrix_le_one_iff`, `eigenvalues_injective_iff_lapMatrix` and
`not_eigenvalues_injective_of_no_adj` — **six of the nine** — and only because `green` is defined
as an inverse and `green_mul_massive` is what makes the two operators trade places.
`lapMatrix_isHermitian` and `finrank_lapMatrix_le_one_iff_injective` take **no hypothesis
whatever**, and `FieldLaplacianSimple.ker_massive_eq`, the step that carries the result from
`massive` to the Laplacian, takes none either.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldSimpleConverse

open Matrix RayleighMatrix

section Hermitian

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-! ## 1. Off the eigenvalue, the coefficient vanishes -/

theorem coeff_def (hA : A.IsHermitian) (v : EuclideanSpace ℝ n) (j : n) :
    coeff hA v j = inner ℝ (hA.eigenvectorBasis j) v := rfl

theorem coeff_eq_zero_of_mv_smul (hA : A.IsHermitian) {ν : ℝ} {v : EuclideanSpace ℝ n}
    (hv : mv A v = ν • v) {j : n} (hj : hA.eigenvalues j ≠ ν) : coeff hA v j = 0 := by
  have h1 := inner_basis_mv hA v j
  rw [hv, real_inner_smul_right] at h1
  have h2 : (hA.eigenvalues j - ν) * coeff hA v j = 0 := by
    rw [sub_mul, ← h1, coeff]
    ring
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) hj
  · exact h

theorem inner_eq_zero_of_mv_smul (hA : A.IsHermitian) {ν : ℝ} {v : EuclideanSpace ℝ n}
    (hv : mv A v = ν • v) {j : n} (hj : hA.eigenvalues j ≠ ν) :
    inner ℝ (hA.eigenvectorBasis j) v = 0 :=
  coeff_eq_zero_of_mv_smul hA hv hj

/-! ## 2. So an eigenvector is a multiple of the one eigenbasis vector at that eigenvalue -/

theorem eq_smul_of_mv_smul (hA : A.IsHermitian) (hsimple : Function.Injective hA.eigenvalues)
    {ν : ℝ} {j₀ : n} (hj₀ : hA.eigenvalues j₀ = ν) {v : EuclideanSpace ℝ n}
    (hv : mv A v = ν • v) : v = coeff hA v j₀ • hA.eigenvectorBasis j₀ := by
  have hrepr := (hA.eigenvectorBasis).sum_repr v
  conv_lhs => rw [← hrepr]
  refine (Finset.sum_eq_single j₀ (fun i _ hi => ?_)
    (fun hi => absurd (Finset.mem_univ _) hi)).trans ?_
  · have hne : hA.eigenvalues i ≠ ν := fun h => hi (hsimple (h.trans hj₀.symm))
    have hz : (hA.eigenvectorBasis).repr v i = 0 := by
      rw [OrthonormalBasis.repr_apply_apply]
      exact inner_eq_zero_of_mv_smul hA hv hne
    rw [hz, zero_smul]
  · have hz : (hA.eigenvectorBasis).repr v j₀ = coeff hA v j₀ :=
      OrthonormalBasis.repr_apply_apply _ _ _
    rw [hz]

/-! ## 3. So every eigenspace is at most a line -/

omit [DecidableEq n] in
theorem mv_toLp_of_mulVec {ν : ℝ} {x : n → ℝ} (hx : A *ᵥ x = ν • x) :
    mv A (WithLp.toLp 2 x) = ν • (WithLp.toLp 2 x : EuclideanSpace ℝ n) := by
  rw [mv]
  simp [hx]

/-- **A SIMPLE SPECTRUM MAKES EVERY EIGENSPACE AT MOST A LINE.** This is the general fact about
one Hermitian matrix and its own eigenspaces; §4 is what the criterion actually needs. -/
theorem finrank_le_one_of_injective (hA : A.IsHermitian)
    (hsimple : Function.Injective hA.eigenvalues) (ν : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - ν • LinearMap.id)) ≤ 1 := by
  by_cases hex : ∃ j₀, hA.eigenvalues j₀ = ν
  · obtain ⟨j₀, hj₀⟩ := hex
    have hb0 : (⇑(hA.eigenvectorBasis j₀) : n → ℝ) ≠ 0 := by
      intro hz
      have h1 : ‖hA.eigenvectorBasis j₀‖ = 1 := (hA.eigenvectorBasis).orthonormal.1 j₀
      rw [show (hA.eigenvectorBasis j₀) = (0 : EuclideanSpace ℝ n) from by
        ext v; exact congrFun hz v] at h1
      simp at h1
    have hle : LinearMap.ker (Matrix.toLin' A - ν • LinearMap.id)
        ≤ Submodule.span ℝ {(⇑(hA.eigenvectorBasis j₀) : n → ℝ)} := by
      intro x hx
      have hmul := (FieldCycleRotation.mem_eigenspace_iff_mulVec A ν x).mp hx
      have hv := eq_smul_of_mv_smul hA hsimple hj₀ (mv_toLp_of_mulVec hmul)
      refine Submodule.mem_span_singleton.mpr ⟨coeff hA (WithLp.toLp 2 x) j₀, ?_⟩
      funext p
      exact (congrFun (congrArg (fun y : EuclideanSpace ℝ n => WithLp.ofLp y) hv) p).symm
    calc Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - ν • LinearMap.id))
        ≤ Module.finrank ℝ (Submodule.span ℝ {(⇑(hA.eigenvectorBasis j₀) : n → ℝ)}) :=
          Submodule.finrank_mono hle
      _ = 1 := finrank_span_singleton hb0
  · have hex' : ∀ j, hA.eigenvalues j ≠ ν := fun j hj => hex ⟨j, hj⟩
    have hbot : LinearMap.ker (Matrix.toLin' A - ν • LinearMap.id) = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
      have hmul := (FieldCycleRotation.mem_eigenspace_iff_mulVec A ν x).mp hx
      have hall : ∀ j, coeff hA (WithLp.toLp 2 x) j = 0 := fun j =>
        coeff_eq_zero_of_mv_smul hA (mv_toLp_of_mulVec hmul) (hex' j)
      have hrepr := (hA.eigenvectorBasis).sum_repr (WithLp.toLp 2 x : EuclideanSpace ℝ n)
      have hzero : (WithLp.toLp 2 x : EuclideanSpace ℝ n) = 0 := by
        rw [← hrepr]
        refine Finset.sum_eq_zero fun j _ => ?_
        have hz : (hA.eigenvectorBasis).repr (WithLp.toLp 2 x) j = 0 := by
          rw [OrthonormalBasis.repr_apply_apply]
          exact hall j
        rw [hz, zero_smul]
      funext p
      exact congrFun (congrArg (fun y : EuclideanSpace ℝ n => WithLp.ofLp y) hzero) p
    rw [hbot, finrank_bot]
    norm_num

/-- **AND CONVERSELY, FOR THE SAME MATRIX**: if every eigenspace of a Hermitian matrix is at most
a line then its eigenvalue function is injective. -/
theorem injective_of_finrank_le_one (hA : A.IsHermitian)
    (hdim : ∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' A - ν • LinearMap.id)) ≤ 1) :
    Function.Injective hA.eigenvalues := by
  intro i j hij
  by_contra hne
  set b := hA.eigenvectorBasis
  set W := LinearMap.ker (Matrix.toLin' A - (hA.eigenvalues i) • LinearMap.id)
  have hmem : ∀ k : n, hA.eigenvalues k = hA.eigenvalues i → (⇑(b k) : n → ℝ) ∈ W := by
    intro k hk
    refine (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr ?_
    rw [← hk]
    exact hA.mulVec_eigenvectorBasis k
  have hi := hmem i rfl
  have hj := hmem j hij.symm
  have hi0 : (⇑(b i) : n → ℝ) ≠ 0 := by
    intro hz
    have h1 : ‖b i‖ = 1 := b.orthonormal.1 i
    rw [show (b i) = (0 : EuclideanSpace ℝ n) from by
      ext v; exact congrFun hz v] at h1
    simp at h1
  have hspan : Submodule.span ℝ {(⇑(b i) : n → ℝ)} = W := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hi
    · rw [finrank_span_singleton hi0]
      exact hdim _
  have hjmem : (⇑(b j) : n → ℝ) ∈ Submodule.span ℝ {(⇑(b i) : n → ℝ)} := hspan ▸ hj
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hjmem
  have hcEuclid : b j = c • b i := by ext v; exact (congrFun hc v).symm
  have hortho : inner ℝ (b i) (b j) = 0 := b.orthonormal.2 hne
  rw [hcEuclid, real_inner_smul_right, real_inner_self_eq_norm_sq, b.orthonormal.1 i] at hortho
  have hc0 : c = 0 := by simpa using hortho
  have hone : ‖b j‖ = 1 := b.orthonormal.1 j
  rw [hcEuclid, hc0, zero_smul, norm_zero] at hone
  exact absurd hone (by norm_num)

/-- **SO FOR A HERMITIAN MATRIX THE TWO CONDITIONS ARE ONE CONDITION**: every eigenspace is at
most a line **iff** the eigenvalues are pairwise distinct. -/
theorem finrank_le_one_iff_injective (hA : A.IsHermitian) :
    (∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - ν • LinearMap.id)) ≤ 1)
      ↔ Function.Injective hA.eigenvalues :=
  ⟨injective_of_finrank_le_one hA, fun h => finrank_le_one_of_injective hA h⟩

end Hermitian

section Graph

open GraphLaplacian

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 4. The literal converse: from the propagator's spectrum back to the eigenspaces -/

/-- **A SIMPLE PROPAGATOR SPECTRUM MAKES EVERY EIGENSPACE OF `massive` AT MOST A LINE** — the
converse of `FieldSimpleCriterion.eigenvalues_injective_of_finrank_le_one`, which
`FieldLaplacianInstance` fenced as not proved anywhere in this estate. -/
theorem finrank_massive_le_one_of_eigenvalues_injective (hm : m ≠ 0)
    (hH : (green G m).IsHermitian) (hsimple : Function.Injective hH.eigenvalues) (ν : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (massive G m) - ν • LinearMap.id)) ≤ 1 := by
  rcases eq_or_ne ν 0 with rfl | hν
  · have hbot : LinearMap.ker (Matrix.toLin' (massive G m) - (0 : ℝ) • LinearMap.id) = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
      have hmul := (FieldCycleRotation.mem_eigenspace_iff_mulVec (massive G m) 0 x).mp hx
      have hgm : green G m *ᵥ (massive G m *ᵥ x) = x := by
        rw [Matrix.mulVec_mulVec, green_mul_massive G hm, Matrix.one_mulVec]
      rw [hmul, zero_smul, Matrix.mulVec_zero] at hgm
      exact hgm.symm
    rw [hbot, finrank_bot]
    norm_num
  · have hle : LinearMap.ker (Matrix.toLin' (massive G m) - ν • LinearMap.id)
        ≤ LinearMap.ker (Matrix.toLin' (green G m) - ν⁻¹ • LinearMap.id) := by
      intro x hx
      refine (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr ?_
      exact FieldSignReflection.green_mulVec_of_massive_mulVec hm hν
        ((FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mp hx)
    exact (Submodule.finrank_mono hle).trans (finrank_le_one_of_injective hH hsimple ν⁻¹)

/-- **AND EVERY EIGENSPACE OF THE GRAPH'S LAPLACIAN TOO.** The mass shifts the eigenvalue and
leaves the subspace alone (`FieldLaplacianSimple.ker_massive_eq`, which takes no hypothesis). -/
theorem finrank_lapMatrix_le_one_of_eigenvalues_injective (hm : m ≠ 0)
    (hH : (green G m).IsHermitian) (hsimple : Function.Injective hH.eigenvalues) (ν : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1 := by
  have h := finrank_massive_le_one_of_eigenvalues_injective hm hH hsimple (ν + m ^ 2)
  rw [FieldLaplacianSimple.ker_massive_eq] at h
  have hshift : ν + m ^ 2 - m ^ 2 = ν := by ring
  rw [hshift] at h
  exact h

/-! ## 5. So the three conditions are one condition -/

/-- **THE CRITERION IS AN EQUIVALENCE.** -/
theorem finrank_massive_le_one_iff (hm : m ≠ 0) (hH : (green G m).IsHermitian) :
    (∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (massive G m) - ν • LinearMap.id)) ≤ 1)
      ↔ Function.Injective hH.eigenvalues :=
  ⟨FieldSimpleCriterion.eigenvalues_injective_of_finrank_le_one hm hH,
    fun h => finrank_massive_le_one_of_eigenvalues_injective hm hH h⟩

/-- **AND SO THE DOOR OF `FieldLaplacianSimple` IS A TWO-WAY DOOR**: the hypothesis stated about
the graph's Laplacian alone is *exactly* simplicity of the propagator's spectrum. -/
theorem finrank_lapMatrix_le_one_iff (hm : m ≠ 0) (hH : (green G m).IsHermitian) :
    (∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1)
      ↔ Function.Injective hH.eigenvalues :=
  ⟨FieldLaplacianSimple.eigenvalues_injective_of_lapMatrix hm hH,
    fun h => finrank_lapMatrix_le_one_of_eigenvalues_injective hm hH h⟩

/-- The graph's Laplacian is Hermitian: it is positive semidefinite. -/
theorem lapMatrix_isHermitian (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.lapMatrix ℝ).IsHermitian :=
  (SimpleGraph.posSemidef_lapMatrix ℝ G).isHermitian

/-- **AND THE FENCE `FieldLaplacianSimple` LEFT ON ITS OWN SIDE COMES DOWN TOO**: for the
Laplacian, *every eigenspace is at most a line* is **exactly** *the `|V|` eigenvalues are pairwise
distinct*. No mass and no propagator appear in this statement. -/
theorem finrank_lapMatrix_le_one_iff_injective :
    (∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1)
      ↔ Function.Injective (lapMatrix_isHermitian G).eigenvalues :=
  finrank_le_one_iff_injective _

/-- **SO THE PROPAGATOR AND THE GRAPH'S LAPLACIAN HAVE SIMPLE SPECTRA TOGETHER**, at every
non-zero mass, and neither side mentions the other's eigenspaces. -/
theorem eigenvalues_injective_iff_lapMatrix (hm : m ≠ 0) (hH : (green G m).IsHermitian) :
    Function.Injective hH.eigenvalues
      ↔ Function.Injective (lapMatrix_isHermitian G).eigenvalues :=
  (finrank_lapMatrix_le_one_iff hm hH).symm.trans finrank_lapMatrix_le_one_iff_injective

/-- **SO AN EDGELESS GRAPH ON TWO OR MORE VERTICES HAS A DEGENERATE PROPAGATOR SPECTRUM.** Not new
information — `FieldSymmetryEdgeless.green_eq_smul_of_no_adj` makes the propagator a scalar matrix
outright — but a demonstration that the new implication carries on an example. -/
theorem not_eigenvalues_injective_of_no_adj (hm : m ≠ 0) (hH : (green G m).IsHermitian)
    (h : ∀ i j : V, ¬ G.Adj i j) (hcard : 2 ≤ Fintype.card V) :
    ¬ Function.Injective hH.eigenvalues := fun hsimple =>
  FieldLaplacianInstance.not_finrank_le_one_of_no_adj h hcard
    (finrank_lapMatrix_le_one_of_eigenvalues_injective hm hH hsimple)

end Graph

end FieldSimpleConverse
