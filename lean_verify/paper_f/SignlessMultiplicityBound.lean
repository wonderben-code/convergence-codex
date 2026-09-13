/-
  SignlessMultiplicityBound.lean — an UPPER bound on signless eigenvalue
  multiplicities, and the first exact multiplicity it pins.

  WHY THIS FILE EXISTS. `LaplacianMultiplicityBound` bounds the multiplicity of
  every non-zero Laplacian eigenvalue — `mult(ν) + #components ≤ |V|` — by the one
  eigenspace the Laplacian always has for free, the kernel, whose dimension is the
  component count. It then squeezes that against `LaplacianTwinClass`'s lower bound
  to get an EXACT multiplicity for the complete graph. **The signless side had no
  upper bound at all**, so every signless multiplicity in the estate is a `≤`
  pointing the wrong way and no signless multiplicity is exact.

  `Q = D + A` has no kernel to spend — for a connected non-bipartite graph it is
  positive definite. What it has instead is a TOP: `topEigen`, which every
  Hermitian matrix attains. So the role `0` plays for `L` is played by `topEigen`
  for `Q`, and the bound comes out **stronger in shape than its Laplacian twin**:
  it needs no connectivity and no component count, because a top eigenvalue always
  exists and always contributes at least a line, whereas `dim ker L` can be `1` or
  `|V|` and has to be computed.

  WHAT THIS FILE PROVES.

  1. `one_le_finrank_eigenspace`, `one_le_finrank_topEigen` — for a Hermitian
     matrix, every eigenvalue's eigenspace is at least a line, and in particular
     `topEigen`'s is. Proved from `eigenvectorBasis`, whose members are unit
     vectors, which is why the statement needs no hypothesis beyond `Nonempty`.
  2. `disjoint_ker_topEigen` — the top eigenspace meets any other eigenspace only
     at `0`. This is the two-eigenvalue argument of
     `LaplacianMultiplicityBound.disjoint_ker_zero` with neither eigenvalue equal
     to zero, so it is `sub_ne_zero` where that one was `smul_eq_zero`.
  3. **`finrank_add_one_le`** — for every finite non-empty graph and every
     `ν ≠ topEigen(Q)`, `mult_Q(ν) + 1 ≤ |V|`. **No connectivity hypothesis.**
  4. **`finrank_signless_top_eq`** — the complete graph on `n + 3` vertices has
     `Q`-eigenvalue `n + 1` with multiplicity **exactly** `n + 2`. Lower bound:
     the whole vertex set is one closed twin class
     (`SignlessTwinClass.card_sub_one_le_finrank_signless_of_closed_class`, which
     puts it at `deg − 1 = n + 1`). Upper bound: item 3, once `n + 1 ≠ topEigen`,
     which is the bracket `Δ + 1 ≤ topEigen` from `SignlessMaxDegreeBound` and not
     a computation of `topEigen` — **the squeeze never needs to know what the top
     eigenvalue IS, only that it is bigger than `n + 1`.**

  This is the first exact multiplicity of a signless eigenvalue in the estate, and
  it is the signless twin of `LaplacianMultiplicityBound.finrank_top_eq`: same
  graph, same route, multiplicity `n + 2` in both, at `n + 1` here and `n + 3`
  there. **The multiplicities agree and the eigenvalues do not**, which is
  `SignlessTwinClass`'s observation carried to an exact statement.

  WHAT IS NOT CLAIMED. Item 3 is not sharp in general and is not claimed to be:
  on a graph with a large twin class it is attained, and on a graph with a simple
  spectrum it is far off. Nothing here computes `topEigen` for any graph, and
  nothing here says which graphs attain the bound. Not attempted, no cost claimed
  (`ERRATUM 246`).

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import SignlessTwinClass
import SignlessPerronSimple
import SignlessMaxDegreeBound
import SignlessStarExact
import LaplacianMultiplicityBound

namespace SignlessMultiplicityBound

open Matrix SimpleGraph LaplacianSignless RayleighVariational

noncomputable section

/-! ## 1. Every eigenvalue's eigenspace is at least a line -/

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- **AN EIGENVALUE'S EIGENSPACE IS NEVER TRIVIAL.** `eigenvectorBasis i` is a unit
vector — hence non-zero — lying in the eigenspace at `eigenvalues i`. -/
theorem one_le_finrank_eigenspace (hA : A.IsHermitian) (i : n) :
    1 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' A - (hA.eigenvalues i) • LinearMap.id)) := by
  set b := hA.eigenvectorBasis
  have hmem : (⇑(b i) : n → ℝ) ∈ LinearMap.ker
      (Matrix.toLin' A - (hA.eigenvalues i) • LinearMap.id) :=
    (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr (hA.mulVec_eigenvectorBasis i)
  have hne : (⇑(b i) : n → ℝ) ≠ 0 := by
    intro hz
    have h1 : ‖b i‖ = 1 := b.orthonormal.1 i
    rw [show (b i) = (0 : EuclideanSpace ℝ n) from by ext v; exact congrFun hz v] at h1
    simp at h1
  have hsub : Submodule.span ℝ {(⇑(b i) : n → ℝ)} ≤ LinearMap.ker
      (Matrix.toLin' A - (hA.eigenvalues i) • LinearMap.id) := by
    rw [Submodule.span_le, Set.singleton_subset_iff]; exact hmem
  have h := Submodule.finrank_mono hsub
  rwa [finrank_span_singleton hne] at h

/-- In particular the TOP eigenspace, which is the one this file spends. -/
theorem one_le_finrank_topEigen [Nonempty n] (hA : A.IsHermitian) :
    1 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' A - (topEigen hA) • LinearMap.id)) := by
  obtain ⟨i, hi⟩ := SignlessPerronSimple.exists_topEigen hA
  rw [← hi]
  exact one_le_finrank_eigenspace hA i

/-! ## 2. The top eigenspace meets no other -/

/-- Distinct eigenvalues have disjoint eigenspaces. `LaplacianMultiplicityBound`
states this with one eigenvalue equal to `0`, where the argument closes on
`smul_eq_zero`; here neither is `0` and it closes on `sub_ne_zero`. -/
theorem disjoint_ker_topEigen [Nonempty n] (hA : A.IsHermitian) {ν : ℝ}
    (hν : ν ≠ topEigen hA) :
    Disjoint (LinearMap.ker (Matrix.toLin' A - (topEigen hA) • LinearMap.id))
      (LinearMap.ker (Matrix.toLin' A - ν • LinearMap.id)) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  have h0 := (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mp hx
  have h1 := (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mp hy
  have h2 : (topEigen hA - ν) • x = 0 := by
    rw [sub_smul, ← h0, ← h1, sub_self]
  rcases smul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hν
  · exact h

/-! ## 3. So every eigenvalue below the top has multiplicity at most `|V| − 1` -/

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **THE UPPER BOUND, FOR EVERY FINITE GRAPH AND WITH NO CONNECTIVITY.** Any
eigenvalue of `Q` other than the top has multiplicity at most `|V| − 1`, because
the top eigenspace is at least a line and the two are disjoint. -/
theorem finrank_add_one_le [Nonempty V] {ν : ℝ}
    (hν : ν ≠ topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G)) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap G) - ν • LinearMap.id)) + 1
      ≤ Fintype.card V := by
  have hdisj := Submodule.finrank_add_finrank_le_of_disjoint
    (disjoint_ker_topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G) hν)
  have htop := one_le_finrank_topEigen
    (LaplacianSignlessDefinite.signlessLap_isHermitian G)
  rw [Module.finrank_pi] at hdisj
  omega

/-! ## 4. The complete graph, squeezed -/

theorem regular_top (n : ℕ) :
    (⊤ : SimpleGraph (Fin (n + 3))).IsRegularOfDegree (n + 2) := fun u =>
  LaplacianMultiplicityBound.degree_top n u

theorem maxDegree_top (n : ℕ) : (⊤ : SimpleGraph (Fin (n + 3))).maxDegree = n + 2 :=
  SignlessStarExact.maxDegree_of_regular _ (regular_top n)

/-- `n + 1` is strictly below the top of `Q`'s spectrum, by the bracket
`Δ + 1 ≤ topEigen` alone. **No computation of `topEigen` is needed and none is
done** — the squeeze in §4 wants an inequality, not a value. -/
theorem lt_topEigen_top (n : ℕ) :
    ((n : ℝ) + 1) < topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian
      (⊤ : SimpleGraph (Fin (n + 3)))) := by
  have hΔ : 0 < (⊤ : SimpleGraph (Fin (n + 3))).maxDegree := by
    rw [maxDegree_top]; omega
  have h := SignlessMaxDegreeBound.maxDegree_add_one_le_topEigen
    (G := (⊤ : SimpleGraph (Fin (n + 3)))) hΔ
  rw [maxDegree_top] at h
  push_cast at h
  linarith

/-- **THE COMPLETE GRAPH ON `n + 3` VERTICES HAS `Q`-EIGENVALUE `n + 1` WITH
MULTIPLICITY EXACTLY `n + 2`** — the first exact multiplicity of a signless
eigenvalue in this estate. The lower bound is the closed twin class of §4 of
`SignlessTwinClass` (the whole vertex set is one, at `deg − 1`); the upper bound
is §3 of this file. `LaplacianMultiplicityBound.finrank_top_eq` is the same
squeeze on the same graph and reaches the same multiplicity `n + 2` — at
eigenvalue `n + 3` rather than `n + 1`, the two-apart that `SignlessTwinClass`
explains. -/
theorem finrank_signless_top_eq (n : ℕ) :
    Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (signlessLap (⊤ : SimpleGraph (Fin (n + 3))))
        - ((n : ℝ) + 1) • LinearMap.id)) = n + 2 := by
  have hval : (((⊤ : SimpleGraph (Fin (n + 3))).degree ⟨0, by omega⟩ : ℝ) - 1)
      = (n : ℝ) + 1 := by
    rw [LaplacianMultiplicityBound.degree_top]
    push_cast
    ring
  have hlow := SignlessTwinClass.card_sub_one_le_finrank_signless_of_closed_class
    (G := (⊤ : SimpleGraph (Fin (n + 3)))) (S := Finset.univ) (u₀ := ⟨0, by omega⟩)
    (fun u _ => (LaplacianClosedTwins.closed_top u).trans
      (LaplacianClosedTwins.closed_top _).symm)
  rw [hval, Finset.card_univ, Fintype.card_fin] at hlow
  have hup := finrank_add_one_le (G := (⊤ : SimpleGraph (Fin (n + 3))))
    (ν := (n : ℝ) + 1) (ne_of_lt (lt_topEigen_top n))
  rw [Fintype.card_fin] at hup
  omega

/-! ## 5. Review round 61 — the ways this could be hollow

**"§3 could be vacuous — maybe no `ν` differs from the top."** `finrank_signless_top_eq`
applies it at `n + 1`, and `lt_topEigen_top` proves that value is genuinely below
the top for every `n`. On a graph with a simple spectrum there are `|V| − 1` such
`ν`; on the one-vertex graph there are none and §3 says nothing, correctly.

**"§3 could be the Laplacian bound with a word changed."**
`LaplacianMultiplicityBound.finrank_add_card_component_le` spends the KERNEL,
whose dimension is a theorem (`finrank_ker_lapMatrix_zero_eq_card_component`) and
varies from `1` to `|V|`. This spends the TOP, whose dimension needs no theorem
at all beyond `eigenvectorBasis` — which is why this statement carries no
connectivity hypothesis and no component count where its twin carries both. The
two bounds are also incomparable: on a disconnected graph the Laplacian bound is
the stronger one.

**"§4 might secretly compute `topEigen`."** It does not, and `lt_topEigen_top` is
where that would have to happen. It uses only `Δ + 1 ≤ topEigen`. The complete
graph's actual top signless eigenvalue is `2(n + 2)`, which is nowhere in this
file and is not needed: an exact multiplicity at one eigenvalue does not require
knowing any other.

**"The lower bound might not be the twin class."** It is —
`card_sub_one_le_finrank_signless_of_closed_class` at `S = univ`, which needs the
class form proved in the previous unit. The pair form of `SignlessTwins` gives
only `2 ≤`, and `2 < n + 2` as soon as `n ≥ 1`, so this squeeze does not close
with the pair theorems and is the first thing in the estate that consumes the
class form on the signless side.
-/

end

end SignlessMultiplicityBound
