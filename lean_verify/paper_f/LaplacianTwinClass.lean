import MixedTwinWitness

/-!
# A whole class of twins, not two pairs of them

`LaplacianTwins` and `LaplacianClosedTwins` both count to two: **two** pairs of twins at one
eigenvalue give **two** independent eigenvectors. That is the right shape when the pairs come from
different places in the graph, and the wrong one when they come from the same place — a set of
`k` mutually twin vertices contributes `k − 1` independent differences, not `2`, and one pair
contributes only `1`.

## What is proved

**`linearIndependent_twinDiff_class`** — the differences of the members of a set against one fixed
member are **linearly independent**, for any set and any vertex, with no graph in the statement at
all: evaluating a vanishing combination at a member reads off its coefficient.

**`card_sub_one_le_finrank`** — **the counting step for a whole class.** If every difference against
a fixed `u₀` is an eigenvector at `ν`, the eigenspace at `ν` has dimension at least `|S| − 1`. Like
`LaplacianClosedTwins.two_le_finrank_of_pair` it mentions **no notion of twin**, only eigenvector
equations, and its hypothesis runs over `S.erase u₀` rather than `S` — the difference of `u₀` with
itself is not a twin difference and is never needed.

**`card_sub_one_le_finrank_of_open_class`, `card_sub_one_le_finrank_of_closed_class`** — so a class
of mutual **open** twins gives `|S| − 1` at their common degree, and a class of mutual **closed**
twins gives `|S| − 1` at one more than it.

**`not_injective_of_open_class`, `not_injective_of_closed_class`** — **a class of three or more
mutual twins therefore makes the Laplacian spectrum degenerate.** *Three*, not two: one pair
contributes one eigenvector and one eigenvector is no obstruction, which is exactly why the earlier
theorems need **two** pairs.

**`not_injective_top`** — **and the class form recovers a bound the pair form could not**: the whole
vertex set of a complete graph is a single closed twin class, so **three** vertices suffice here
where `LaplacianClosedTwins.not_injective_top_via_closed_twins` needed **four**.

## What is NOT here

**NEITHER FORM SUBSUMES THE OTHER, AND THE EARLIER FILES ARE NOT SUPERSEDED.** Two pairs from two
different classes are not a class, and a class of three is not two pairs. `LaplacianTwins`'
theorem applies where this one cannot (`FieldTwinSpectrum.twinGraph` has two classes of size two and
no class of size three) and this one applies where that one cannot (a complete graph on three
vertices). **The two counting steps have the same shape and different reach.**

**STILL A LOWER BOUND.** `|S| − 1 ≤ dim` is proved; **the eigenspace is not shown to be exactly
that**, and for a class that is not maximal it will not be. No upper bound of any kind appears
anywhere in this estate as of 2026-09-06.

**NO MAXIMAL CLASS, NO PARTITION.** *Being twins* is an equivalence relation on the vertices, the
classes partition the graph, and the eigenvalue multiplicities should be readable off that
partition. **None of that is stated**: `S` here is any set whose members are twins of `u₀`, maximal
or not, and no equivalence, quotient or partition is constructed. Not attempted, no cost claimed
(`ERRATUM 246`).

**NO CHARACTERISATION.** Twin classes are **sufficient** for degeneracy and nowhere near necessary —
the cycle is degenerate and has no twins at all. The standing `UNLOCK_WATCHLIST` question does not
move.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): **no statement takes a mass, a propagator
or a measure**. `linearIndependent_twinDiff_class` takes neither `Fintype V` nor a graph — it is a
fact about indicator differences — and `card_sub_one_le_finrank` takes no membership hypothesis on
`u₀` at all: if `u₀ ∉ S` the bound still holds, with `S.erase u₀ = S`, and it is stronger.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace LaplacianTwinClass

open SimpleGraph Matrix GraphLaplacian LaplacianTwins LaplacianClosedTwins

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. A family of differences against one fixed vertex is independent -/

omit [Fintype V] [DecidableRel G.Adj] in
theorem linearIndependent_twinDiff_class {S : Finset V} {u₀ : V} :
    LinearIndependent ℝ (fun i : ↥(S.erase u₀) => CutTwins.twinDiff (i : V) u₀) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hj : (j : V) ≠ u₀ := Finset.ne_of_mem_erase j.2
  have h := congrFun hg (j : V)
  rw [Finset.sum_apply] at h
  have hterm : ∀ i : ↥(S.erase u₀),
      (g i • CutTwins.twinDiff (i : V) u₀) (j : V) = if j = i then g i else 0 := by
    intro i
    by_cases hij : (j : V) = (i : V)
    · have : j = i := Subtype.ext hij
      simp [CutTwins.twinDiff, this]
    · have : ¬ j = i := fun hc => hij (congrArg Subtype.val hc)
      simp [CutTwins.twinDiff, hij, hj, this]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq Finset.univ j g] at h
  simpa using h

/-! ## 2. So a class of vertices whose differences are all eigenvectors gives a lower bound -/

/-- **THE COUNTING STEP FOR A WHOLE CLASS.** If every difference against a fixed member of `S` is an
eigenvector at `ν`, the eigenspace at `ν` has dimension at least `|S| − 1`. -/
theorem card_sub_one_le_finrank {S : Finset V} {u₀ : V} {ν : ℝ}
    (heig : ∀ u ∈ S.erase u₀,
      G.lapMatrix ℝ *ᵥ CutTwins.twinDiff u u₀ = ν • CutTwins.twinDiff u u₀) :
    S.card - 1 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) := by
  have hsub : Submodule.span ℝ
      (Set.range (fun i : ↥(S.erase u₀) => CutTwins.twinDiff (i : V) u₀))
      ≤ LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    exact (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr
      (heig (i : V) i.2)
  have hcard : Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun i : ↥(S.erase u₀) => CutTwins.twinDiff (i : V) u₀)))
      = (S.erase u₀).card := by
    rw [finrank_span_eq_card linearIndependent_twinDiff_class, Fintype.card_coe]
  have hle := Submodule.finrank_mono hsub
  rw [hcard] at hle
  refine le_trans ?_ hle
  exact Finset.pred_card_le_card_erase

/-! ## 3. A class of open twins, and a class of closed twins -/

theorem card_sub_one_le_finrank_of_open_class {S : Finset V} {u₀ : V}
    (hS : ∀ u ∈ S, G.neighborFinset u = G.neighborFinset u₀) :
    S.card - 1 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - (G.degree u₀ : ℝ) • LinearMap.id)) := by
  refine card_sub_one_le_finrank (u₀ := u₀) fun u hu => ?_
  have hmem := Finset.mem_of_mem_erase hu
  have h := LaplacianTwins.lapMatrix_mulVec_twinDiff (Finset.ne_of_mem_erase hu) (hS u hmem)
  rwa [LaplacianTwins.degree_eq_of_neighborFinset_eq (hS u hmem)] at h

theorem card_sub_one_le_finrank_of_closed_class {S : Finset V} {u₀ : V}
    (hS : ∀ u ∈ S, insert u (G.neighborFinset u) = insert u₀ (G.neighborFinset u₀)) :
    S.card - 1 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - ((G.degree u₀ : ℝ) + 1) • LinearMap.id)) := by
  refine card_sub_one_le_finrank (u₀ := u₀) fun u hu => ?_
  have hmem := Finset.mem_of_mem_erase hu
  have h := lapMatrix_mulVec_twinDiff_closed (Finset.ne_of_mem_erase hu) (hS u hmem)
  rwa [degree_eq_of_closed (hS u hmem)] at h

/-! ## 4. So a class of three or more forces a repeated eigenvalue -/

/-- **A CLASS OF THREE OR MORE MUTUAL TWINS MAKES ITS DEGREE A REPEATED EIGENVALUE.** One pair is
not enough — it gives one eigenvector — which is why `LaplacianTwins`' theorem needs **two** pairs
and this one needs a class of **three**. -/
theorem not_injective_of_open_class {S : Finset V} {u₀ : V}
    (hS : ∀ u ∈ S, G.neighborFinset u = G.neighborFinset u₀) (hcard : 3 ≤ S.card) :
    ¬ Function.Injective (FieldSimpleConverse.lapMatrix_isHermitian G).eigenvalues := by
  intro hinj
  have hdim := FieldSimpleConverse.finrank_lapMatrix_le_one_iff_injective.mpr hinj
  have h1 := hdim (G.degree u₀ : ℝ)
  have h2 := card_sub_one_le_finrank_of_open_class hS
  omega

theorem not_injective_of_closed_class {S : Finset V} {u₀ : V}
    (hS : ∀ u ∈ S, insert u (G.neighborFinset u) = insert u₀ (G.neighborFinset u₀))
    (hcard : 3 ≤ S.card) :
    ¬ Function.Injective (FieldSimpleConverse.lapMatrix_isHermitian G).eigenvalues := by
  intro hinj
  have hdim := FieldSimpleConverse.finrank_lapMatrix_le_one_iff_injective.mpr hinj
  have h1 := hdim ((G.degree u₀ : ℝ) + 1)
  have h2 := card_sub_one_le_finrank_of_closed_class hS
  omega

/-! ## 5. The complete graph is one closed class -/

/-- **AND THE CLASS FORM RECOVERS THE THREE-VERTEX BOUND** that the pair form of
`LaplacianClosedTwins` could not: the whole vertex set of a complete graph is a single closed twin
class, so three vertices suffice where two pairs needed four. -/
theorem not_injective_top (n : ℕ) :
    ¬ Function.Injective (FieldSimpleConverse.lapMatrix_isHermitian
      (⊤ : SimpleGraph (Fin (n + 3)))).eigenvalues :=
  not_injective_of_closed_class (S := Finset.univ) (u₀ := ⟨0, by omega⟩)
    (fun u _ => (closed_top u).trans (closed_top _).symm)
    (by simp)

end LaplacianTwinClass
