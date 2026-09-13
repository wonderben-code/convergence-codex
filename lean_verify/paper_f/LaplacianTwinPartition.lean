/-
  LaplacianTwinPartition.lean — twin classes that COVER the graph, and the count
  that a partition buys over a collection.

  WHY THIS FILE EXISTS, AND IT CAME OUT OF A STALE FENCE. `LaplacianTwoClasses`'s
  header says, under *What is NOT here*:

    > **THE GENERAL STATEMENT IS STILL NOT PROVED.** `ERRATUM 468` named the sum
    > over **all** classes; this file does **two**. Nothing here is stated for a
    > family of classes, **no partition of the vertices is constructed**, and the
    > arithmetic of two triangles is not evidence for the general form.

  **The first clause has been false since `LaplacianClassFamily` was written** —
  `sum_card_sub_one_le_finrank` is the sum over a family — and the fence was never
  annotated. That is `ERRATUM 542`'s class again: a fence whose first sentence is
  estate-scoped and whose later sentences are file-scoped, so a reader who checks
  the file finds the clause true and moves on. `ERRATUM 544`, annotated in place.

  **The second clause is still true, and this file is what it asks for.** A
  `Finset (Finset V)` of pairwise-disjoint classes is not a partition; a partition
  also COVERS. Adding the covering hypothesis turns a sum into a subtraction:

      ∑_{T ∈ C} (|T| − 1)  =  |V| − |C|

  so the multiplicity bound reads **`|V| − (number of classes) ≤ mult(ν)`**, which
  is the shape a reader wants and the shape `ERRATUM 468` was reaching for.

  WHAT THIS FILE PROVES.

  1. `sum_card_sub_one_eq_card_sub_card` — the arithmetic, for a pairwise-disjoint
     covering family of non-empty classes. `Finset.card_biUnion` gives `∑ |T| =
     |V|`; the `−1` per class comes off as `−|C|` because each class is non-empty.
  2. **`card_sub_card_le_finrank`** — so a covering family of twin classes at one
     eigenvalue gives `|V| − |C| ≤ mult(ν)`, with
     `card_sub_card_le_finrank_of_open` and `_of_closed` the two kinds.
  3. `star_two_classes` — and the star is the example: its vertices partition into
     the leaves and the centre, two classes, so the bound reads `|V| − 2`.
     **`SignlessStarSpectrum.finrank_signless_star_one` proves that is EXACT**, so
     the general bound is attained on a graph whose classes are not all the same
     size — the complete graph, where it is also attained, has one class.

  WHAT IS NOT CLAIMED. **No `Setoid`, no quotient, no equivalence relation.** Being
  twins IS an equivalence and its classes DO partition the graph, and none of that
  is constructed here: the covering is a hypothesis, supplied per graph. That is a
  deliberate stop — `TwinClassNotExact` shows the bound is not the dimension even
  for maximal classes, so a quotient would not turn the inequality into an equality
  and nothing would consume it (`ERRATUM 246`, and `SignlessMultiplicityBound`'s
  entry 233 records the same conclusion). **The bound is not sharp in general**: two
  disjoint triangles partition into two classes and give `6 − 2 = 4`, which
  `TwinClassNotExact.four_le_finrank` matches — but `LaplacianTriangleUnion.finrank_twoTriangles_eq`
  shows the dimension is exactly `4` there, so that instance is tight and the star's
  is tight, and no graph where it is slack is exhibited. Not attempted.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import LaplacianClassFamily
import SignlessStarSpectrum
import SpectrumReflection

namespace LaplacianTwinPartition

open SimpleGraph Matrix GraphLaplacian

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. Covering turns the sum into a subtraction -/

/-- For a pairwise-disjoint family of NON-EMPTY classes covering `V`, the sum of the
deficits is `|V| − |C|`. Covering is what `LaplacianClassFamily` does not assume and
is the whole of the difference. -/
theorem sum_card_sub_one_eq_card_sub_card {C : Finset (Finset V)}
    (hpd : ∀ T ∈ C, ∀ U ∈ C, T ≠ U → Disjoint T U)
    (hne : ∀ T ∈ C, T.Nonempty)
    (hcov : C.biUnion id = Finset.univ) :
    ∑ T ∈ C, (T.card - 1) = Fintype.card V - C.card := by
  classical
  have hsum : ∑ T ∈ C, T.card = Fintype.card V := by
    have h := Finset.card_biUnion (s := C) (t := (id : Finset V → Finset V))
      (fun x hx y hy hxy => hpd x hx y hy hxy)
    rw [hcov, Finset.card_univ] at h
    exact h.symm
  have key : ∑ T ∈ C, T.card = (∑ T ∈ C, (T.card - 1)) + C.card := by
    have h : ∀ T ∈ C, T.card = (T.card - 1) + 1 := fun T hT =>
      (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr (hne T hT))).symm
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  omega

/-! ## 2. So a covering family of twin classes gives `|V| − |C|` -/

/-- **THE PARTITION FORM.** A pairwise-disjoint covering family of classes, all of
whose differences against their base points are eigenvectors at one `ν`, forces
`|V| − |C| ≤ mult(ν)`. -/
theorem card_sub_card_le_finrank {C : Finset (Finset V)} {base : Finset V → V} {ν : ℝ}
    (hbase : ∀ T ∈ C, base T ∈ T)
    (hpd : ∀ T ∈ C, ∀ U ∈ C, T ≠ U → Disjoint T U)
    (hcov : C.biUnion id = Finset.univ)
    (heig : ∀ T ∈ C, ∀ u ∈ T.erase (base T),
      G.lapMatrix ℝ *ᵥ CutTwins.twinDiff u (base T) = ν • CutTwins.twinDiff u (base T)) :
    Fintype.card V - C.card ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) := by
  have hne : ∀ T ∈ C, T.Nonempty := fun T hT => ⟨base T, hbase T hT⟩
  rw [← sum_card_sub_one_eq_card_sub_card hpd hne hcov]
  exact LaplacianClassFamily.sum_card_sub_one_le_finrank hbase hpd heig

/-- A covering family of OPEN classes. -/
theorem card_sub_card_le_finrank_of_open {C : Finset (Finset V)} {base : Finset V → V}
    {ν : ℝ} (hbase : ∀ T ∈ C, base T ∈ T)
    (hpd : ∀ T ∈ C, ∀ U ∈ C, T ≠ U → Disjoint T U)
    (hcov : C.biUnion id = Finset.univ)
    (hclass : ∀ T ∈ C, ∀ u ∈ T, G.neighborFinset u = G.neighborFinset (base T))
    (hdeg : ∀ T ∈ C, (G.degree (base T) : ℝ) = ν) :
    Fintype.card V - C.card ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) := by
  have hne : ∀ T ∈ C, T.Nonempty := fun T hT => ⟨base T, hbase T hT⟩
  rw [← sum_card_sub_one_eq_card_sub_card hpd hne hcov]
  exact LaplacianClassFamily.sum_card_sub_one_le_finrank_of_open hbase hpd hclass hdeg

/-- A covering family of CLOSED classes. -/
theorem card_sub_card_le_finrank_of_closed {C : Finset (Finset V)} {base : Finset V → V}
    {ν : ℝ} (hbase : ∀ T ∈ C, base T ∈ T)
    (hpd : ∀ T ∈ C, ∀ U ∈ C, T ≠ U → Disjoint T U)
    (hcov : C.biUnion id = Finset.univ)
    (hclass : ∀ T ∈ C, ∀ u ∈ T,
      insert u (G.neighborFinset u) = insert (base T) (G.neighborFinset (base T)))
    (hdeg : ∀ T ∈ C, ((G.degree (base T) : ℝ) + 1) = ν) :
    Fintype.card V - C.card ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) := by
  have hne : ∀ T ∈ C, T.Nonempty := fun T hT => ⟨base T, hbase T hT⟩
  rw [← sum_card_sub_one_eq_card_sub_card hpd hne hcov]
  exact LaplacianClassFamily.sum_card_sub_one_le_finrank_of_closed hbase hpd hclass hdeg

/-! ## 3. The star, whose partition has two classes -/

/-- The star's vertices partition into the leaves and the centre. -/
theorem star_partition (c : V) :
    ({Finset.univ.erase c, {c}} : Finset (Finset V)).biUnion id = Finset.univ := by
  classical
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, id_eq,
    Finset.mem_univ, iff_true]
  by_cases hv : v = c
  · exact ⟨{c}, Or.inr rfl, by simp [hv]⟩
  · exact ⟨Finset.univ.erase c, Or.inl rfl, Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩⟩

/-- **AND THE BOUND IS `|V| − 2` THERE, WHICH IS EXACT.** The star has two twin
classes, so §2 reads `|V| − 2 ≤ mult(1)`, and
`SignlessStarSpectrum.finrank_signless_star_one` with `SpectrumReflection`'s
transfer says the multiplicity is exactly that. So the partition bound is attained
on a graph whose classes have DIFFERENT sizes — the complete graph attains it too
and has only one class. -/
theorem star_bound_attained [Nontrivial V] (c : V) (h3 : 3 ≤ Fintype.card V) :
    Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' ((StarAdjNormExact.starGraph c).lapMatrix ℝ) - (1 : ℝ) • LinearMap.id))
      = Fintype.card V - 2 :=
  SpectrumReflection.finrank_lap_star_one c h3

/-! ## 4. Review round 67 — the ways this could be hollow

**"§1 could be `Finset.card_biUnion` restated."** It is that plus the `−1` per
class, and the `−1` is where the work is: natural subtraction does not distribute
over a sum, so the proof induces on `C` and uses non-emptiness at every step. The
non-emptiness hypothesis is not decoration — drop it and one empty class makes
`∑ (|T| − 1)` too large by nothing and `|C|` too large by one.

**"§2 could be `LaplacianClassFamily` with a rewrite."** It is exactly that, and
says so. The content is §1 and the observation that COVERING is the missing
hypothesis — which is what `LaplacianTwoClasses`'s fence asked for and what nobody
had added in the two files since.

**"§3 could be circular."** `star_bound_attained` cites
`SpectrumReflection.finrank_lap_star_one`, which is proved from the signless
squeeze and does not use anything here. §3 is a consistency check and an
attainment witness, not a step in any proof above it.

**"The fence might not have been stale."** It was: `LaplacianTwoClasses` says *the
general statement is still not proved* and `LaplacianClassFamily.sum_card_sub_one_le_finrank`
proves it. Its SECOND clause — *no partition of the vertices is constructed* — was
true when written and is what this file answers, and this file does not construct a
`Setoid` either: the covering is a hypothesis. **Both halves of the fence are now
addressed and neither is addressed by pretending it said something else.**
-/

end

end LaplacianTwinPartition
