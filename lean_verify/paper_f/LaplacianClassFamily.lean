import FieldTwinRotation

/-!
# The sum over all classes, which is what the erratum actually named

`LaplacianTwoClasses` proved that **two** disjoint classes at one eigenvalue contribute the sum of
their deficits, and said in as many words that `ERRATUM 468` had named the sum over **all** classes,
that this was two rather than all, and that two triangles was one graph and not evidence. **This is
all of them**, and three triangles is the instance two classes cannot reach.

## What is proved

**`linearIndependent_family`** — the differences of a **collection** of pairwise disjoint classes,
each against its own base point, are independent together. Indexed by a sigma type over the
collection; the argument is the two-class one with `Finset.sum_eq_single` doing what the sum-type
case split did.

**`sum_card_sub_one_le_finrank`** — **so a collection of pairwise disjoint classes at one eigenvalue
contributes `∑ (|T| − 1)`.** As with every counting step in this chain it mentions **no notion of
twin**: a family of eigenvector equations at a common `ν`, base points, and pairwise disjointness.

**`sum_card_sub_one_le_finrank_of_closed`, `..._of_open`** — the two instantiations, each asking
that the base points' eigenvalues agree.

**`threeTriangles`, `six_le_finrank_threeTriangles`** — **six dimensions at one eigenvalue, from
three classes.** `LaplacianTwoClasses` reaches four on two triangles and no further; the third class
is what the family form buys, and it is why this file has a graph of its own rather than reusing
`TwinClassNotExact.twoTriangles`.

## What is NOT here

**STILL NO UPPER BOUND.** `∑ (|T| − 1) ≤ dim`, and **the dimension is not computed for any graph**.
`TwinClassNotExact` showed the class bound is not sharp for **one** class; **whether the sum over
all classes is sharp is not addressed**, and on three triangles it happens to be — six is the
dimension — but that is one graph and this file proves no such thing. **This estate still has no
upper bound on the multiplicity of any eigenvalue of any graph** as of 2026-09-06.

**NO PARTITION, NO EQUIVALENCE, NO MAXIMALITY.** `C` is any collection of pairwise disjoint sets
whose members are twins of their base points. **Nothing here says the classes exhaust the vertices,
that being twins is an equivalence relation, or that the classes are maximal** — and
`ERRATUM 468`'s finding, that maximality is not what makes the one-class bound unsharp, is
untouched.

**THE MIXED CASE IS NOT INSTANTIATED**, again: `sum_card_sub_one_le_finrank` carries a collection in
which some classes are open and others closed, since it takes eigenvector equations rather than a
notion of twin — but no such collection is exhibited, and stating a corollary with no instance is
what `MixedTwinWitness` was written to avoid.

**THE THREE-TRIANGLE GRAPH IS NOT INTERESTING AND IS NOT CLAIMED TO BE.** It exists so the family
theorem has an instance beyond two, which the two-class theorem could already do. Its spectrum is
`{0, 0, 0, 3, 3, 3, 3, 3, 3}` and **none of that is proved here** — only that six of those
dimensions are there.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): **no statement takes a mass, a propagator
or a measure**. `linearIndependent_family` takes neither `Fintype V` nor a graph — it is a fact
about indicator differences and disjoint sets.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace LaplacianClassFamily

open SimpleGraph Matrix GraphLaplacian LaplacianTwoClasses

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. The combined family over a whole collection of classes -/

omit [Fintype V] [DecidableRel G.Adj] in
theorem linearIndependent_family {C : Finset (Finset V)} {base : Finset V → V}
    (hbase : ∀ T ∈ C, base T ∈ T)
    (hpd : ∀ T ∈ C, ∀ U ∈ C, T ≠ U → Disjoint T U) :
    LinearIndependent ℝ
      (fun i : (Σ T : ↥C, ↥((T : Finset V).erase (base (T : Finset V)))) =>
        CutTwins.twinDiff ((i.2 : V)) (base (i.1 : Finset V))) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hj1 : (j.2 : V) ∈ (j.1 : Finset V) := Finset.mem_of_mem_erase j.2.2
  have h := congrFun hg (j.2 : V)
  rw [Finset.sum_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma] at h
  have hsplit : ∀ T : ↥C, T ≠ j.1 →
      ∑ i : ↥((T : Finset V).erase (base (T : Finset V))),
        (g ⟨T, i⟩ • CutTwins.twinDiff ((i : V)) (base (T : Finset V))) (j.2 : V) = 0 := by
    intro T hT
    refine Finset.sum_eq_zero fun i _ => ?_
    have hne : (T : Finset V) ≠ (j.1 : Finset V) := fun hc => hT (Subtype.ext hc)
    have hdisj := hpd (j.1 : Finset V) j.1.2 (T : Finset V) T.2 (Ne.symm hne)
    simp [twinDiff_apply_eq_zero hdisj hj1 (Finset.mem_of_mem_erase i.2)
      (hbase (T : Finset V) T.2)]
  rw [Finset.sum_eq_single j.1 (fun T _ hT => hsplit T hT)
    (fun hc => absurd (Finset.mem_univ _) hc)] at h
  rw [sum_twinDiff_apply (fun i => g ⟨j.1, i⟩) j.2] at h
  simpa using h

/-! ## 2. So a whole collection of classes at one eigenvalue adds -/

/-- **THE STATEMENT `ERRATUM 468` NAMED, IN FULL.** A collection of pairwise disjoint classes, all
of whose differences against their own base points are eigenvectors at one `ν`, contributes the
**sum** of their deficits. -/
theorem sum_card_sub_one_le_finrank {C : Finset (Finset V)} {base : Finset V → V} {ν : ℝ}
    (hbase : ∀ T ∈ C, base T ∈ T)
    (hpd : ∀ T ∈ C, ∀ U ∈ C, T ≠ U → Disjoint T U)
    (heig : ∀ T ∈ C, ∀ u ∈ T.erase (base T),
      G.lapMatrix ℝ *ᵥ CutTwins.twinDiff u (base T) = ν • CutTwins.twinDiff u (base T)) :
    ∑ T ∈ C, (T.card - 1) ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) := by
  have hsub : Submodule.span ℝ (Set.range
      (fun i : (Σ T : ↥C, ↥((T : Finset V).erase (base (T : Finset V)))) =>
        CutTwins.twinDiff ((i.2 : V)) (base (i.1 : Finset V))))
      ≤ LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    rintro ⟨T, i⟩
    exact (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr
      (heig (T : Finset V) T.2 (i : V) i.2)
  have hcard : Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun i : (Σ T : ↥C, ↥((T : Finset V).erase (base (T : Finset V)))) =>
        CutTwins.twinDiff ((i.2 : V)) (base (i.1 : Finset V)))))
      = ∑ T ∈ C, (T.erase (base T)).card := by
    rw [finrank_span_eq_card (linearIndependent_family hbase hpd), Fintype.card_sigma,
      show (∑ T : ↥C, Fintype.card ↥((T : Finset V).erase (base (T : Finset V))))
          = ∑ T : ↥C, ((T : Finset V).erase (base (T : Finset V))).card from
        Finset.sum_congr rfl fun T _ => Fintype.card_coe _]
    exact Finset.sum_attach C (fun T => (T.erase (base T)).card)
  have hle := Submodule.finrank_mono hsub
  rw [hcard] at hle
  refine le_trans (Finset.sum_le_sum fun T _ => ?_) hle
  exact Finset.pred_card_le_card_erase

/-! ## 3. The two kinds of class -/

theorem sum_card_sub_one_le_finrank_of_closed {C : Finset (Finset V)} {base : Finset V → V}
    {ν : ℝ} (hbase : ∀ T ∈ C, base T ∈ T)
    (hpd : ∀ T ∈ C, ∀ U ∈ C, T ≠ U → Disjoint T U)
    (hclass : ∀ T ∈ C, ∀ u ∈ T,
      insert u (G.neighborFinset u) = insert (base T) (G.neighborFinset (base T)))
    (hdeg : ∀ T ∈ C, ((G.degree (base T) : ℝ) + 1) = ν) :
    ∑ T ∈ C, (T.card - 1) ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) := by
  refine sum_card_sub_one_le_finrank hbase hpd fun T hT u hu => ?_
  have hmem := Finset.mem_of_mem_erase hu
  have h := LaplacianClosedTwins.lapMatrix_mulVec_twinDiff_closed
    (Finset.ne_of_mem_erase hu) (hclass T hT u hmem)
  rwa [LaplacianClosedTwins.degree_eq_of_closed (hclass T hT u hmem), hdeg T hT] at h

theorem sum_card_sub_one_le_finrank_of_open {C : Finset (Finset V)} {base : Finset V → V}
    {ν : ℝ} (hbase : ∀ T ∈ C, base T ∈ T)
    (hpd : ∀ T ∈ C, ∀ U ∈ C, T ≠ U → Disjoint T U)
    (hclass : ∀ T ∈ C, ∀ u ∈ T, G.neighborFinset u = G.neighborFinset (base T))
    (hdeg : ∀ T ∈ C, (G.degree (base T) : ℝ) = ν) :
    ∑ T ∈ C, (T.card - 1) ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) := by
  refine sum_card_sub_one_le_finrank hbase hpd fun T hT u hu => ?_
  have hmem := Finset.mem_of_mem_erase hu
  have h := LaplacianTwins.lapMatrix_mulVec_twinDiff
    (Finset.ne_of_mem_erase hu) (hclass T hT u hmem)
  rwa [LaplacianTwins.degree_eq_of_neighborFinset_eq (hclass T hT u hmem), hdeg T hT] at h

/-! ## 4. Three triangles, which two classes cannot reach -/

/-- Adjacency of `threeTriangles`: `0–1–2`, `3–4–5`, `6–7–8`, with nothing between them. -/
def threeAdj : Fin 9 → Fin 9 → Bool
  | 0, 1 | 1, 0 | 0, 2 | 2, 0 | 1, 2 | 2, 1 => true
  | 3, 4 | 4, 3 | 3, 5 | 5, 3 | 4, 5 | 5, 4 => true
  | 6, 7 | 7, 6 | 6, 8 | 8, 6 | 7, 8 | 8, 7 => true
  | _, _ => false

def threeTriangles : SimpleGraph (Fin 9) where
  Adj u v := threeAdj u v = true
  symm := by intro u v h; revert u v; decide
  loopless := ⟨by intro u h; revert u; decide⟩

instance : DecidableRel threeTriangles.Adj := fun u v =>
  inferInstanceAs (Decidable (threeAdj u v = true))

theorem threeTriangles_degrees : ∀ v : Fin 9, threeTriangles.degree v = 2 := by decide

/-- The three classes, and a base point in each. -/
def classes : Finset (Finset (Fin 9)) := {{0, 1, 2}, {3, 4, 5}, {6, 7, 8}}

def baseOf (T : Finset (Fin 9)) : Fin 9 := if (0 : Fin 9) ∈ T then 0 else if 3 ∈ T then 3 else 6

set_option maxRecDepth 40000 in
/-- **SIX DIMENSIONS AT ONE EIGENVALUE, FROM THREE CLASSES.** `LaplacianTwoClasses` reaches four
here and no further; the family form is what gets the third class. -/
theorem six_le_finrank_threeTriangles :
    6 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (threeTriangles.lapMatrix ℝ) - (3 : ℝ) • LinearMap.id)) := by
  have h := sum_card_sub_one_le_finrank_of_closed (G := threeTriangles) (C := classes)
    (base := baseOf) (ν := 3) (by decide) (by decide) (by decide)
    (fun T _ => by rw [threeTriangles_degrees]; norm_num)
  rwa [show (∑ T ∈ classes, (T.card - 1)) = 6 from by decide] at h

end LaplacianClassFamily
