/-
  SignlessTwinClass.lean — twin CLASSES and FAMILIES of them, for the signless
  Laplacian `Q = D + A`.

  WHY THIS FILE EXISTS. `SignlessTwins` proved that twins degenerate `Q` exactly
  as they degenerate `L`, and proved it for PAIRS: two disjoint twin pairs at one
  degree give `2 ≤ finrank`. The Laplacian side of the estate had already moved
  past that shape twice — `LaplacianTwinClass` handles a class of any size and
  `LaplacianClassFamily` a collection of disjoint classes — and the signless side
  never followed. This file removes the two hypotheses, one at a time: first
  *the class has exactly two elements*, then *there are exactly two classes*.

  Found by comparing the Laplacian and signless chains declaration by
  declaration, which is the instrument `ERRATUM 539` was found with. It did NOT
  transfer cleanly — the two chains share no naming convention the way the 1-d
  and n-d Gaussian chains share the `Pi` suffix, so the comparison produced 91
  candidates and every one had to be opened. The gap below was found by eye
  inside that list, and saying so matters: the instrument narrowed the search and
  did not make the finding.

  WHAT THIS FILE PROVES.

  1. `card_sub_one_le_finrank_signless` — a set `S` of vertices whose differences
     against a fixed `u₀` are all `Q`-eigenvectors at `ν` gives
     `|S| − 1 ≤ dim ker(Q − ν)`. The independence is
     `LaplacianTwinClass.linearIndependent_twinDiff_class`, which is a fact about
     indicator differences and mentions no operator, so it is reused verbatim.
  2. `card_sub_one_le_finrank_signless_of_open_class` at `ν = deg u₀`, and
     **`card_sub_one_le_finrank_signless_of_closed_class` at `ν = deg u₀ − 1`.**
     **THE TWO EIGENVALUES DIFFER AND THAT IS THE CONTENT, NOT A TRANSCRIPTION**:
     on a CLOSED twin difference `A` acts as `−1`, so `Q = L + 2A` sends
     `deg + 1` to `deg − 1`. Same eigenvector, same multiplicity, different
     eigenvalue — and on OPEN twins `A` kills the difference and the two operators
     agree outright.
  3. `not_injective_signless_of_open_class` / `_closed_class` — a class of THREE
     or more forces a repeated `Q`-eigenvalue, where the pair form of
     `SignlessTwins` needed two disjoint pairs and therefore four vertices.
     `not_injective_signless_top` recovers the complete graph at `n + 3` where
     `SignlessTwins.top_separates_nothing` needed `n + 4`.
  4. `sum_card_sub_one_le_finrank_signless` and its open and closed forms — a
     collection of pairwise disjoint classes contributes the SUM of its deficits.
  5. `six_le_finrank_signless_threeTriangles` — three disjoint triangles give a
     `Q`-eigenspace of dimension at least `6`, at eigenvalue `1`. The Laplacian
     twin of this statement sits at eigenvalue `3`; the graph, the classes and the
     multiplicity are identical and only the eigenvalue moves, which is item 2
     made concrete.

  WHAT IS NOT CLAIMED. No maximal class, no equivalence relation and no partition:
  `S` is any set of mutual twins of `u₀`, and nothing here constructs the quotient
  the multiplicities should really be read off. Twin classes remain SUFFICIENT for
  degeneracy and nowhere near necessary — the cycle is degenerate and has no twins.
  Neither is attempted and no cost is claimed (`ERRATUM 246`). The standing
  `UNLOCK_WATCHLIST` question — which graphs have a degenerate `Q` — does not move.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import SignlessTwins
import LaplacianClassFamily
import LaplacianTwinClass

namespace SignlessTwinClass

open SimpleGraph Matrix LaplacianSignless GraphLaplacian
open LaplacianTwins LaplacianClosedTwins SignlessTwins

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. One class of any size -/

/-- **THE COUNTING STEP FOR A WHOLE CLASS, FOR `Q`.** If every difference against a
fixed member of `S` is a `Q`-eigenvector at `ν`, then `dim ker(Q − ν) ≥ |S| − 1`.
The independence of the differences is `LaplacianTwinClass`'s, unchanged: it is a
statement about indicator functions and knows nothing about which operator is
acting on them. -/
theorem card_sub_one_le_finrank_signless {S : Finset V} {u₀ : V} {ν : ℝ}
    (heig : ∀ u ∈ S.erase u₀,
      signlessLap G *ᵥ CutTwins.twinDiff u u₀ = ν • CutTwins.twinDiff u u₀) :
    S.card - 1 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (signlessLap G) - ν • LinearMap.id)) := by
  have hsub : Submodule.span ℝ
      (Set.range (fun i : ↥(S.erase u₀) => CutTwins.twinDiff (i : V) u₀))
      ≤ LinearMap.ker (Matrix.toLin' (signlessLap G) - ν • LinearMap.id) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    exact (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr (heig (i : V) i.2)
  have hcard : Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun i : ↥(S.erase u₀) => CutTwins.twinDiff (i : V) u₀)))
      = (S.erase u₀).card := by
    rw [finrank_span_eq_card LaplacianTwinClass.linearIndependent_twinDiff_class,
      Fintype.card_coe]
  have hle := Submodule.finrank_mono hsub
  rw [hcard] at hle
  exact le_trans Finset.pred_card_le_card_erase hle

/-! ## 2. The two kinds of class, and the eigenvalue moves -/

/-- A class of OPEN twins, at `ν = deg u₀`. Here `Q` and `L` agree, because `A`
kills an open twin difference. -/
theorem card_sub_one_le_finrank_signless_of_open_class {S : Finset V} {u₀ : V}
    (hS : ∀ u ∈ S, G.neighborFinset u = G.neighborFinset u₀) :
    S.card - 1 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (signlessLap G) - (G.degree u₀ : ℝ) • LinearMap.id)) := by
  refine card_sub_one_le_finrank_signless (u₀ := u₀) fun u hu => ?_
  have hmem := Finset.mem_of_mem_erase hu
  have h := signlessLap_mulVec_twinDiff (Finset.ne_of_mem_erase hu) (hS u hmem)
  rwa [LaplacianTwins.degree_eq_of_neighborFinset_eq (hS u hmem)] at h

/-- A class of CLOSED twins, at **`ν = deg u₀ − 1`** — where the Laplacian
statement sits at `deg u₀ + 1`. On a closed twin difference `A` acts as `−1`, and
`Q = L + 2A` carries the eigenvalue down by two while leaving the eigenvector and
the count alone. -/
theorem card_sub_one_le_finrank_signless_of_closed_class {S : Finset V} {u₀ : V}
    (hS : ∀ u ∈ S, insert u (G.neighborFinset u) = insert u₀ (G.neighborFinset u₀)) :
    S.card - 1 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (signlessLap G) - ((G.degree u₀ : ℝ) - 1) • LinearMap.id)) := by
  refine card_sub_one_le_finrank_signless (u₀ := u₀) fun u hu => ?_
  have hmem := Finset.mem_of_mem_erase hu
  have h := signlessLap_mulVec_twinDiff_closed (Finset.ne_of_mem_erase hu) (hS u hmem)
  rwa [degree_eq_of_closed (hS u hmem)] at h

/-! ## 3. So a class of three or more forces a repeated eigenvalue -/

/-- **THREE MUTUAL OPEN TWINS MAKE `Q`'s SPECTRUM NON-SIMPLE.** `SignlessTwins`
needed two disjoint pairs, hence four vertices; a class needs three. -/
theorem not_injective_signless_of_open_class {S : Finset V} {u₀ : V}
    (hS : ∀ u ∈ S, G.neighborFinset u = G.neighborFinset u₀) (hcard : 3 ≤ S.card) :
    ¬ Function.Injective
      (LaplacianSignlessDefinite.signlessLap_isHermitian G).eigenvalues := by
  intro hinj
  have hdim := (FieldSimpleConverse.finrank_le_one_iff_injective
    (LaplacianSignlessDefinite.signlessLap_isHermitian G)).mpr hinj
  have h1 := hdim (G.degree u₀ : ℝ)
  have h2 := card_sub_one_le_finrank_signless_of_open_class hS
  omega

/-- The same for three mutual CLOSED twins, at the moved eigenvalue. -/
theorem not_injective_signless_of_closed_class {S : Finset V} {u₀ : V}
    (hS : ∀ u ∈ S, insert u (G.neighborFinset u) = insert u₀ (G.neighborFinset u₀))
    (hcard : 3 ≤ S.card) :
    ¬ Function.Injective
      (LaplacianSignlessDefinite.signlessLap_isHermitian G).eigenvalues := by
  intro hinj
  have hdim := (FieldSimpleConverse.finrank_le_one_iff_injective
    (LaplacianSignlessDefinite.signlessLap_isHermitian G)).mpr hinj
  have h1 := hdim ((G.degree u₀ : ℝ) - 1)
  have h2 := card_sub_one_le_finrank_signless_of_closed_class hS
  omega

/-- **AND THE COMPLETE GRAPH ON THREE VERTICES ALREADY SUFFICES**, where
`SignlessTwins.top_separates_nothing` needed four: the whole vertex set is one
closed twin class. -/
theorem not_injective_signless_top (n : ℕ) :
    ¬ Function.Injective (LaplacianSignlessDefinite.signlessLap_isHermitian
      (⊤ : SimpleGraph (Fin (n + 3)))).eigenvalues :=
  not_injective_signless_of_closed_class (S := Finset.univ) (u₀ := ⟨0, by omega⟩)
    (fun u _ => (closed_top u).trans (closed_top _).symm)
    (by simp)

/-! ## 4. A family of disjoint classes -/

/-- **DISJOINT CLASSES ADD, FOR `Q` AS FOR `L`.** A collection of pairwise disjoint
classes, all of whose differences against their own base points are `Q`-eigenvectors
at one `ν`, contributes the sum of their deficits. The independence across classes is
`LaplacianClassFamily.linearIndependent_family`, again an operator-free fact. -/
theorem sum_card_sub_one_le_finrank_signless {C : Finset (Finset V)}
    {base : Finset V → V} {ν : ℝ}
    (hbase : ∀ T ∈ C, base T ∈ T)
    (hpd : ∀ T ∈ C, ∀ U ∈ C, T ≠ U → Disjoint T U)
    (heig : ∀ T ∈ C, ∀ u ∈ T.erase (base T),
      signlessLap G *ᵥ CutTwins.twinDiff u (base T) = ν • CutTwins.twinDiff u (base T)) :
    ∑ T ∈ C, (T.card - 1) ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (signlessLap G) - ν • LinearMap.id)) := by
  have hsub : Submodule.span ℝ (Set.range
      (fun i : (Σ T : ↥C, ↥((T : Finset V).erase (base (T : Finset V)))) =>
        CutTwins.twinDiff ((i.2 : V)) (base (i.1 : Finset V))))
      ≤ LinearMap.ker (Matrix.toLin' (signlessLap G) - ν • LinearMap.id) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    rintro ⟨T, i⟩
    exact (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr
      (heig (T : Finset V) T.2 (i : V) i.2)
  have hcard : Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun i : (Σ T : ↥C, ↥((T : Finset V).erase (base (T : Finset V)))) =>
        CutTwins.twinDiff ((i.2 : V)) (base (i.1 : Finset V)))))
      = ∑ T ∈ C, (T.erase (base T)).card := by
    rw [finrank_span_eq_card (LaplacianClassFamily.linearIndependent_family hbase hpd),
      Fintype.card_sigma,
      show (∑ T : ↥C, Fintype.card ↥((T : Finset V).erase (base (T : Finset V))))
          = ∑ T : ↥C, ((T : Finset V).erase (base (T : Finset V))).card from
        Finset.sum_congr rfl fun T _ => Fintype.card_coe _]
    exact Finset.sum_attach C (fun T => (T.erase (base T)).card)
  have hle := Submodule.finrank_mono hsub
  rw [hcard] at hle
  exact le_trans (Finset.sum_le_sum fun T _ => Finset.pred_card_le_card_erase) hle

/-- A family of OPEN classes, all at one degree. -/
theorem sum_card_sub_one_le_finrank_signless_of_open {C : Finset (Finset V)}
    {base : Finset V → V} {ν : ℝ}
    (hbase : ∀ T ∈ C, base T ∈ T)
    (hpd : ∀ T ∈ C, ∀ U ∈ C, T ≠ U → Disjoint T U)
    (hclass : ∀ T ∈ C, ∀ u ∈ T, G.neighborFinset u = G.neighborFinset (base T))
    (hdeg : ∀ T ∈ C, (G.degree (base T) : ℝ) = ν) :
    ∑ T ∈ C, (T.card - 1) ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (signlessLap G) - ν • LinearMap.id)) := by
  refine sum_card_sub_one_le_finrank_signless hbase hpd fun T hT u hu => ?_
  have hmem := Finset.mem_of_mem_erase hu
  have h := signlessLap_mulVec_twinDiff (Finset.ne_of_mem_erase hu) (hclass T hT u hmem)
  rwa [LaplacianTwins.degree_eq_of_neighborFinset_eq (hclass T hT u hmem), hdeg T hT] at h

/-- A family of CLOSED classes, at `ν = deg − 1` rather than `deg + 1`. -/
theorem sum_card_sub_one_le_finrank_signless_of_closed {C : Finset (Finset V)}
    {base : Finset V → V} {ν : ℝ}
    (hbase : ∀ T ∈ C, base T ∈ T)
    (hpd : ∀ T ∈ C, ∀ U ∈ C, T ≠ U → Disjoint T U)
    (hclass : ∀ T ∈ C, ∀ u ∈ T,
      insert u (G.neighborFinset u) = insert (base T) (G.neighborFinset (base T)))
    (hdeg : ∀ T ∈ C, ((G.degree (base T) : ℝ) - 1) = ν) :
    ∑ T ∈ C, (T.card - 1) ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (signlessLap G) - ν • LinearMap.id)) := by
  refine sum_card_sub_one_le_finrank_signless hbase hpd fun T hT u hu => ?_
  have hmem := Finset.mem_of_mem_erase hu
  have h := signlessLap_mulVec_twinDiff_closed
    (Finset.ne_of_mem_erase hu) (hclass T hT u hmem)
  rwa [degree_eq_of_closed (hclass T hT u hmem), hdeg T hT] at h

/-! ## 5. Three triangles, and the eigenvalue that moved -/

set_option maxRecDepth 40000 in
/-- **SIX DIMENSIONS AT ONE `Q`-EIGENVALUE, FROM THREE CLASSES — AND THE EIGENVALUE
IS `1`, NOT `3`.** `LaplacianClassFamily.six_le_finrank_threeTriangles` is the same
graph, the same three classes and the same bound at `ν = 3`. Every triangle is a
closed twin class of degree `2`, so `L` sees `2 + 1` and `Q` sees `2 − 1`. The
multiplicity is a fact about the eigenVECTORS and transfers; the eigenvalue is not
and does not. -/
theorem six_le_finrank_signless_threeTriangles :
    6 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (signlessLap LaplacianClassFamily.threeTriangles)
        - (1 : ℝ) • LinearMap.id)) := by
  have h := sum_card_sub_one_le_finrank_signless_of_closed
    (G := LaplacianClassFamily.threeTriangles) (C := LaplacianClassFamily.classes)
    (base := LaplacianClassFamily.baseOf) (ν := 1) (by decide) (by decide) (by decide)
    (fun T _ => by rw [LaplacianClassFamily.threeTriangles_degrees]; norm_num)
  rwa [show (∑ T ∈ LaplacianClassFamily.classes, (T.card - 1)) = 6 from by decide] at h

/-! ## 6. Review round 60 — the ways this could be hollow

**"§1 could be `LaplacianTwinClass` with `L` replaced by `Q` throughout."** In §1
and §4 it is, and the files say so: the independence lemmas are imported rather
than restated precisely because they mention no operator. What is NOT a
substitution is §2. `Q = L + 2A`, so a transfer needs to know what `A` does to the
eigenvector, and `A` does two different things — it kills an open twin difference
and negates a closed one. That is why the open statement lands on the same
eigenvalue and the closed one lands two below, and why §5's eigenvalue is `1` where
its Laplacian twin is `3`.

**"§5 could be a restatement of the Laplacian instance."** It is the same graph and
the same bound at a different eigenvalue, which is the point — but it is proved
through §4, not transported from `LaplacianClassFamily.six_le_finrank_threeTriangles`,
and no theorem of that file is cited here. Transporting it would have needed a
statement relating the two spectra, which the estate does not have and which is
false in general.

**"The class theorems could be vacuous."** §3 exhibits a class of every size in the
complete graph (`not_injective_signless_top`), and §5 a family of three classes of
size three, both by `decide`. Neither is a constant, neither is empty.

**"`SignlessTwins`' pair theorems are now dead."** They are not subsumed: the pair
theorems take TWO classes of size two with a shared degree and are the `C.card = 2`,
`T.card = 2` case of §4 — but they are stated with four vertex inequalities rather
than a disjointness hypothesis on `Finset`s, and nothing here derives one spelling
from the other. Deriving it is bookkeeping and nothing consumes it, so it is not
done and no cost is claimed (`ERRATUM 246`).
-/

end SignlessTwinClass
