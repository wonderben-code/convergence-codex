import TwinClassNotExact

/-!
# Two classes at one eigenvalue, which is the statement the last erratum said was missing

`ERRATUM 468` refuted a sentence I had written twice — *the eigenspace of a twin class has dimension
one less than the class size* — and named the true statement in that direction: the differences of
**all** twin classes at one eigenvalue together span the sum of their deficits. **This is that
statement for two classes.** The general form is still not proved.

On two disjoint triangles it turns `(3−1) + (3−1) = 4` from an arithmetic coincidence into an
instance: `four_le_finrank_twoTriangles` re-derives the previous unit's hand-built bound from the
theorem.

## What is proved

**`sum_twinDiff_apply`** — a vanishing combination of differences against a fixed base point reads
off its own coefficient at each member. `LaplacianTwinClass` did this inside its independence proof;
it is a lemma here because the two-class argument needs it twice.

**`twinDiff_apply_eq_zero`** — a difference inside one class is **zero** on any vertex of a disjoint
class. That is the entire reason the two families do not interfere.

**`linearIndependent_two_classes`** — so the two families, indexed by a sum type, are independent
together.

**`sum_sub_one_le_finrank`** — **two disjoint classes at one eigenvalue contribute the sum of their
deficits.** Like the counting steps before it this mentions **no notion of twin**: two families of
eigenvector equations at a common `ν`, and disjointness.

**`sum_sub_one_le_finrank_of_open_classes`, `sum_sub_one_le_finrank_of_closed_classes`** — the two
instantiations, each needing the two base points to have equal degree so that the eigenvalues agree.

**`four_le_finrank_twoTriangles`** — and the previous unit's `4` is `(3−1) + (3−1)`.

## What is NOT here

**THE GENERAL STATEMENT IS STILL NOT PROVED.** `ERRATUM 468` named the sum over **all** classes;
this file does **two**. Nothing here is stated for a family of classes, no partition of the vertices
is constructed, and **the arithmetic of two triangles is not evidence for the general form** — it is
one graph, and it was one graph when the erratum said so. Not attempted, no cost claimed
(`ERRATUM 246`).

**STILL NO UPPER BOUND.** Everything here is `≤ dim`. The dimension is not computed for any graph,
and **no upper bound on the multiplicity of any eigenvalue of any graph exists in this estate** as
of 2026-09-06 — which is what `ERRATUM 468` was ultimately about, and it is untouched.

**NO MIXED FORM.** Two **open** classes and two **closed** classes are instantiated; **one of each**
is not, though `sum_sub_one_le_finrank` would carry it exactly as
`LaplacianClosedTwins.two_le_finrank_of_pair` carries the mixed pair. It is omitted because no graph
is at hand that needs it, and adding it would be a statement with no instance — the thing
`MixedTwinWitness` was written to avoid.

**THE CLASSES ARE NOT REQUIRED TO BE MAXIMAL OR EVEN TO BE CLASSES.** `S₁` and `S₂` are any disjoint
sets whose members are twins of their base points. **No equivalence relation is constructed**, and
`ERRATUM 468`'s finding — that maximality is not what makes the bound unsharp — is unaffected.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): **no statement takes a mass, a propagator
or a measure**. The first three lemmas take neither `Fintype V` nor a graph.
`sum_sub_one_le_finrank` takes the two base points' membership and the disjointness and **nothing
about twins**.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace LaplacianTwoClasses

open SimpleGraph Matrix GraphLaplacian LaplacianTwinClass LaplacianClosedTwins

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. Reading a coefficient off, and a difference vanishing on a disjoint set -/

omit [Fintype V] [DecidableRel G.Adj] in
theorem sum_twinDiff_apply {S : Finset V} {u₀ : V} (g : ↥(S.erase u₀) → ℝ)
    (j : ↥(S.erase u₀)) :
    ∑ i : ↥(S.erase u₀), (g i • CutTwins.twinDiff (i : V) u₀) (j : V) = g j := by
  have hj : (j : V) ≠ u₀ := Finset.ne_of_mem_erase j.2
  have hterm : ∀ i : ↥(S.erase u₀),
      (g i • CutTwins.twinDiff (i : V) u₀) (j : V) = if j = i then g i else 0 := by
    intro i
    by_cases hij : (j : V) = (i : V)
    · have hji : j = i := Subtype.ext hij
      simp [CutTwins.twinDiff, hji]
    · have hji : ¬ j = i := fun hc => hij (congrArg Subtype.val hc)
      simp [CutTwins.twinDiff, hij, hj, hji]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq Finset.univ j g]
  simp

omit [Fintype V] [DecidableRel G.Adj] in
theorem twinDiff_apply_eq_zero {S₁ S₂ : Finset V} (hdisj : Disjoint S₁ S₂) {a x y : V}
    (ha : a ∈ S₁) (hx : x ∈ S₂) (hy : y ∈ S₂) : CutTwins.twinDiff x y a = 0 := by
  have hax : a ≠ x := fun h => (Finset.disjoint_left.mp hdisj ha) (h ▸ hx)
  have hay : a ≠ y := fun h => (Finset.disjoint_left.mp hdisj ha) (h ▸ hy)
  simp [CutTwins.twinDiff, hax, hay]

/-! ## 2. The two families together are independent -/

omit [Fintype V] [DecidableRel G.Adj] in
theorem linearIndependent_two_classes {S₁ S₂ : Finset V} {u₁ u₂ : V}
    (hu₁ : u₁ ∈ S₁) (hu₂ : u₂ ∈ S₂) (hdisj : Disjoint S₁ S₂) :
    LinearIndependent ℝ (Sum.elim
      (fun i : ↥(S₁.erase u₁) => CutTwins.twinDiff (i : V) u₁)
      (fun i : ↥(S₂.erase u₂) => CutTwins.twinDiff (i : V) u₂)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  cases j with
  | inl a =>
      have ha1 : (a : V) ∈ S₁ := Finset.mem_of_mem_erase a.2
      have h := congrFun hg (a : V)
      rw [Finset.sum_apply, Fintype.sum_sum_type] at h
      have h2 : ∑ i : ↥(S₂.erase u₂),
          ((fun i : ↥(S₂.erase u₂) => g (Sum.inr i) •
            CutTwins.twinDiff (i : V) u₂) i) (a : V) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        simp [twinDiff_apply_eq_zero hdisj ha1 (Finset.mem_of_mem_erase i.2) hu₂]
      simp only [Sum.elim_inl, Sum.elim_inr] at h
      rw [h2, add_zero] at h
      rw [sum_twinDiff_apply (fun i => g (Sum.inl i)) a] at h
      simpa using h
  | inr b =>
      have hb2 : (b : V) ∈ S₂ := Finset.mem_of_mem_erase b.2
      have h := congrFun hg (b : V)
      rw [Finset.sum_apply, Fintype.sum_sum_type] at h
      have h1 : ∑ i : ↥(S₁.erase u₁),
          ((fun i : ↥(S₁.erase u₁) => g (Sum.inl i) •
            CutTwins.twinDiff (i : V) u₁) i) (b : V) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        simp [twinDiff_apply_eq_zero hdisj.symm hb2 (Finset.mem_of_mem_erase i.2) hu₁]
      simp only [Sum.elim_inl, Sum.elim_inr] at h
      rw [h1, zero_add] at h
      rw [sum_twinDiff_apply (fun i => g (Sum.inr i)) b] at h
      simpa using h

/-! ## 3. So two disjoint classes at one eigenvalue add -/

/-- **TWO DISJOINT CLASSES AT ONE EIGENVALUE CONTRIBUTE THE SUM OF THEIR DEFICITS.** This is the
statement `ERRATUM 468` says the twin files should have made, **for two classes**; the general form,
over all classes at once, is still not proved. -/
theorem sum_sub_one_le_finrank {S₁ S₂ : Finset V} {u₁ u₂ : V} {ν : ℝ}
    (hu₁ : u₁ ∈ S₁) (hu₂ : u₂ ∈ S₂) (hdisj : Disjoint S₁ S₂)
    (h₁ : ∀ u ∈ S₁.erase u₁,
      G.lapMatrix ℝ *ᵥ CutTwins.twinDiff u u₁ = ν • CutTwins.twinDiff u u₁)
    (h₂ : ∀ u ∈ S₂.erase u₂,
      G.lapMatrix ℝ *ᵥ CutTwins.twinDiff u u₂ = ν • CutTwins.twinDiff u u₂) :
    (S₁.card - 1) + (S₂.card - 1) ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) := by
  have hsub : Submodule.span ℝ (Set.range (Sum.elim
      (fun i : ↥(S₁.erase u₁) => CutTwins.twinDiff (i : V) u₁)
      (fun i : ↥(S₂.erase u₂) => CutTwins.twinDiff (i : V) u₂)))
      ≤ LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    rintro (i | i)
    · exact (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr (h₁ _ i.2)
    · exact (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr (h₂ _ i.2)
  have hcard : Module.finrank ℝ (Submodule.span ℝ (Set.range (Sum.elim
      (fun i : ↥(S₁.erase u₁) => CutTwins.twinDiff (i : V) u₁)
      (fun i : ↥(S₂.erase u₂) => CutTwins.twinDiff (i : V) u₂))))
      = (S₁.erase u₁).card + (S₂.erase u₂).card := by
    rw [finrank_span_eq_card (linearIndependent_two_classes hu₁ hu₂ hdisj), Fintype.card_sum,
      Fintype.card_coe, Fintype.card_coe]
  have hle := Submodule.finrank_mono hsub
  rw [hcard] at hle
  have e1 := Finset.pred_card_le_card_erase (s := S₁) (a := u₁)
  have e2 := Finset.pred_card_le_card_erase (s := S₂) (a := u₂)
  omega

/-! ## 4. Two open classes, or two closed ones -/

theorem sum_sub_one_le_finrank_of_open_classes {S₁ S₂ : Finset V} {u₁ u₂ : V}
    (hu₁ : u₁ ∈ S₁) (hu₂ : u₂ ∈ S₂) (hdisj : Disjoint S₁ S₂)
    (hS₁ : ∀ u ∈ S₁, G.neighborFinset u = G.neighborFinset u₁)
    (hS₂ : ∀ u ∈ S₂, G.neighborFinset u = G.neighborFinset u₂)
    (hdeg : G.degree u₂ = G.degree u₁) :
    (S₁.card - 1) + (S₂.card - 1) ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - (G.degree u₁ : ℝ) • LinearMap.id)) := by
  refine sum_sub_one_le_finrank hu₁ hu₂ hdisj (fun u hu => ?_) (fun u hu => ?_)
  · have hmem := Finset.mem_of_mem_erase hu
    have h := LaplacianTwins.lapMatrix_mulVec_twinDiff (Finset.ne_of_mem_erase hu) (hS₁ u hmem)
    rwa [LaplacianTwins.degree_eq_of_neighborFinset_eq (hS₁ u hmem)] at h
  · have hmem := Finset.mem_of_mem_erase hu
    have h := LaplacianTwins.lapMatrix_mulVec_twinDiff (Finset.ne_of_mem_erase hu) (hS₂ u hmem)
    rwa [LaplacianTwins.degree_eq_of_neighborFinset_eq (hS₂ u hmem), hdeg] at h

theorem sum_sub_one_le_finrank_of_closed_classes {S₁ S₂ : Finset V} {u₁ u₂ : V}
    (hu₁ : u₁ ∈ S₁) (hu₂ : u₂ ∈ S₂) (hdisj : Disjoint S₁ S₂)
    (hS₁ : ∀ u ∈ S₁, insert u (G.neighborFinset u) = insert u₁ (G.neighborFinset u₁))
    (hS₂ : ∀ u ∈ S₂, insert u (G.neighborFinset u) = insert u₂ (G.neighborFinset u₂))
    (hdeg : G.degree u₂ = G.degree u₁) :
    (S₁.card - 1) + (S₂.card - 1) ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - ((G.degree u₁ : ℝ) + 1) • LinearMap.id)) := by
  refine sum_sub_one_le_finrank hu₁ hu₂ hdisj (fun u hu => ?_) (fun u hu => ?_)
  · have hmem := Finset.mem_of_mem_erase hu
    have h := lapMatrix_mulVec_twinDiff_closed (Finset.ne_of_mem_erase hu) (hS₁ u hmem)
    rwa [degree_eq_of_closed (hS₁ u hmem)] at h
  · have hmem := Finset.mem_of_mem_erase hu
    have h := lapMatrix_mulVec_twinDiff_closed (Finset.ne_of_mem_erase hu) (hS₂ u hmem)
    rwa [degree_eq_of_closed (hS₂ u hmem), hdeg] at h

/-! ## 5. The four dimensions of two triangles, from theory -/

/-- **AND THE PREVIOUS UNIT'S FOUR IS `(3−1) + (3−1)`.** `TwinClassNotExact.four_le_finrank`
exhibited the four vectors by hand; this derives the same bound from the two-class theorem, which is
what makes `(3−1) + (3−1) = 4` an instance of something rather than an arithmetic coincidence. -/
theorem four_le_finrank_twoTriangles :
    4 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (TwinClassNotExact.twoTriangles.lapMatrix ℝ) - (3 : ℝ) • LinearMap.id)) := by
  have h := sum_sub_one_le_finrank_of_closed_classes
    (G := TwinClassNotExact.twoTriangles) (S₁ := {0, 1, 2}) (S₂ := {3, 4, 5})
    (u₁ := 0) (u₂ := 3) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [show ((TwinClassNotExact.twoTriangles.degree 0 : ℝ) + 1) = 3 from by
    rw [TwinClassNotExact.degrees 0]; norm_num] at h
  simpa using h

end LaplacianTwoClasses
