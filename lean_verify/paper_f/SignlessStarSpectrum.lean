/-
  SignlessStarSpectrum.lean — the star's signless spectrum, with multiplicities.

  WHY THIS FILE EXISTS, AND THE TABLE THAT CHOSE IT. `ERRATUM 541` was written
  because a unit claimed three novelties without counting. The count it produced —
  95 exact signless multiplicities across 30 files — was then sorted by GRAPH
  FAMILY, and the table has three empty rows. Two are empty because the graph is
  not in the estate at all. The third is the STAR, which this estate has studied
  hard: `StarAdjNormExact` computes its adjacency norm, `SignlessStarExact` its
  signless spectral radius, `SignlessStarConverse` characterises it by that radius.
  **And no theorem anywhere in `paper_f` states a multiplicity for it** — the word
  `finrank` and the word `starGraph` do not co-occur in a single statement.

  So the star has a spectral radius and no spectrum. This file gives it one.

  THE SPECTRUM. `Q = D + A` on `K_{1,n}` has three eigenvalues and this file proves
  all three multiplicities:

      |V|   with multiplicity 1        (the spectral radius, `SignlessStarExact`)
      1     with multiplicity |V| − 2  (the leaves, as a twin class)
      0     with multiplicity 1        (the star is connected and bipartite)

  and `1 + (|V| − 2) + 1 = |V|`, so the list is complete.

  HOW, AND EVERY STEP IS A THEOREM SOMEONE ELSE PROVED EXCEPT THE SQUEEZE.
  `HermitianDimensionSum.sum_finrank_image` says the eigenspace dimensions sum to
  `|V|`; three lower bounds that already add to `|V|` therefore cannot have slack.
  The lower bounds are `SignlessMultiplicityBound.one_le_finrank_topEigen` at the
  top, `SignlessColourableNecessary.finrank_ker_eq_iff_colorable` with
  `SignlessStarExact.starGraph_colorable_two` at `0`, and — the one that needs the
  recent work — **`SignlessTwinClass.card_sub_one_le_finrank_signless_of_open_class`
  at `1`**: the leaves all have neighbourhood `{c}`, so they are an open twin class
  of size `|V| − 1` and degree `1`, giving `|V| − 2`.

  **THE PAIR FORM COULD NOT HAVE DONE THIS EITHER.** `SignlessTwins`' two-pair
  theorem gives `2 ≤`, and the squeeze needs `|V| − 2`. The star is the second
  consumer of the class form, after `SignlessMultiplicityBound`, and it is the one
  that uses a class of unbounded size rather than the whole vertex set.

  WHAT IS NOT CLAIMED. `connected_starGraph` is proved here because the estate did
  not have it; it is four lines and is not the point. **No Laplacian twin**: the
  star's ordinary Laplacian spectrum is `{0, 1, |V|}` with the same multiplicities
  by the same argument, and it is not proved here — the family table says that row
  is empty too, and filling both halves in one file would hide which half needed
  which tool. **Nothing about a general tree**, which is where a reader might
  expect this to go; the star is the tree whose leaves form ONE twin class, and no
  other tree does.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import SignlessStarExact
import SignlessTwinClass
import SignlessMultiplicityBound
import HermitianDimensionSum
import GraphIsoSignlessSpectrum

namespace SignlessStarSpectrum

open Matrix SimpleGraph LaplacianSignless GraphLaplacian RayleighVariational
open StarAdjNormExact SignlessStarExact

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {c : V}

/-! ## 1. The star is connected -/

omit [Fintype V] [DecidableEq V] in
/-- Every vertex is the centre or adjacent to it, so the star is connected. The
estate did not have this; it is four lines and is not this file's content. -/
theorem connected_starGraph [Nonempty V] (c : V) : (starGraph c).Connected := by
  have hc : ∀ w : V, (starGraph c).Reachable w c := by
    intro w
    by_cases hw : w = c
    · exact hw ▸ SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable ((starGraph_adj_leaf hw).mpr rfl)
  have hpre : (starGraph c).Preconnected := fun u v => (hc u).trans (hc v).symm
  exact { preconnected := hpre, nonempty := ‹Nonempty V› }

/-! ## 2. The three eigenspaces, from below -/

/-- The alternating vector: `1` at the centre, `−1` at every leaf. -/
def altVec (c : V) : V → ℝ := fun v => if v = c then 1 else -1

omit [Fintype V] in
theorem altVec_ne_zero (c : V) : altVec c ≠ 0 := fun h => by
  have := congrFun h c
  simp [altVec] at this

/-- **`Q` KILLS IT.** At a leaf the row reads `1·(−1) + 1 = 0`; at the centre it
reads `(|V|−1)·1 + (|V|−1)·(−1) = 0`. **NO COLOURABILITY MACHINERY**: the star is
bipartite and `LaplacianSignlessKernel` would give the kernel's dimension from
that, but the squeeze in §3 needs only that `0` IS an eigenvalue, and exhibiting
one vector is cheaper than importing a theorem about component counts. -/
theorem signlessLap_mulVec_altVec [Nonempty V] (c : V) :
    signlessLap (starGraph c) *ᵥ altVec c = 0 := by
  classical
  funext v
  rw [GraphIsoSignlessSpectrum.signlessLap_mulVec_apply]
  by_cases hv : v = c
  · subst hv
    have h1 : 1 ≤ Fintype.card V := Fintype.card_pos
    rw [neighborFinset_centre, degree_centre]
    have hpt : ∀ u ∈ Finset.univ.erase v, altVec v u = (-1 : ℝ) := by
      intro u hu
      simp [altVec, Finset.ne_of_mem_erase hu]
    rw [Finset.sum_congr rfl hpt, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, nsmul_eq_mul]
    simp only [altVec, Pi.zero_apply]
    push_cast [Nat.cast_sub h1]
    ring
  · rw [neighborFinset_leaf hv, degree_leaf hv]
    simp [altVec, hv]

/-- **SO `0` IS AN EIGENVALUE OF THE STAR'S `Q`**, and its eigenspace is at least a
line. §3 turns this into exactly a line. -/
theorem one_le_finrank_ker_signless_star [Nonempty V] (c : V) :
    1 ≤ Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (starGraph c))
      - (0 : ℝ) • LinearMap.id)) := by
  have hmem : altVec c ∈ LinearMap.ker (Matrix.toLin' (signlessLap (starGraph c))
      - (0 : ℝ) • LinearMap.id) :=
    (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr (by
      rw [signlessLap_mulVec_altVec c, zero_smul])
  have hsub : Submodule.span ℝ {altVec c} ≤ LinearMap.ker
      (Matrix.toLin' (signlessLap (starGraph c)) - (0 : ℝ) • LinearMap.id) := by
    rw [Submodule.span_le, Set.singleton_subset_iff]; exact hmem
  have h := Submodule.finrank_mono hsub
  rwa [finrank_span_singleton (altVec_ne_zero c)] at h

/-- **AT `1`: at least `|V| − 2`.** Every leaf has neighbourhood `{c}`, so the
leaves are an open twin class of size `|V| − 1`, each of degree `1`. -/
theorem card_le_finrank_star_one_add_two [Nontrivial V] (c : V) :
    Fintype.card V ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (signlessLap (starGraph c)) - (1 : ℝ) • LinearMap.id)) + 2 := by
  classical
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : V, u₀ ≠ c := exists_ne c
  have hS : ∀ u ∈ (Finset.univ.erase c),
      (starGraph c).neighborFinset u = (starGraph c).neighborFinset u₀ := by
    intro u hu
    rw [neighborFinset_leaf (Finset.ne_of_mem_erase hu), neighborFinset_leaf hu₀]
  have h := SignlessTwinClass.card_sub_one_le_finrank_signless_of_open_class
    (G := starGraph c) (S := Finset.univ.erase c) (u₀ := u₀) hS
  rw [degree_leaf hu₀, Nat.cast_one] at h
  rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ] at h
  have h2 : 2 ≤ Fintype.card V := Fintype.one_lt_card
  omega

/-! ## 3. The squeeze -/

omit [DecidableEq V] in
/-- The three values are pairwise distinct once there are three vertices. -/
theorem three_distinct_star [Nontrivial V] (h3 : 3 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) ≠ 1 ∧ (Fintype.card V : ℝ) ≠ 0 ∧ (1 : ℝ) ≠ 0 := by
  refine ⟨?_, ?_, one_ne_zero⟩
  · intro h; rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) from by norm_num] at h
    exact absurd (Nat.cast_injective h) (by omega)
  · intro h; rw [show (0 : ℝ) = ((0 : ℕ) : ℝ) from by norm_num] at h
    exact absurd (Nat.cast_injective h) (by omega)

/-- **THE MULTIPLICITY AT `1` IS EXACTLY `|V| − 2`.** The three eigenspace
dimensions are each at least what §2 says, and `sum_finrank_image` caps their total
at `|V|`; since the lower bounds already total `|V|`, none has slack. -/
theorem finrank_signless_star_one [Nontrivial V] (c : V) (h3 : 3 ≤ Fintype.card V) :
    Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (signlessLap (starGraph c)) - (1 : ℝ) • LinearMap.id))
      = Fintype.card V - 2 := by
  classical
  set hQ := LaplacianSignlessDefinite.signlessLap_isHermitian (starGraph c) with hQdef
  set f : ℝ → ℕ := fun μ => Module.finrank ℝ (LinearMap.ker
    (Matrix.toLin' (signlessLap (starGraph c)) - μ • LinearMap.id)) with hf
  -- the three lower bounds
  have htop : 1 ≤ f (topEigen hQ) :=
    SignlessMultiplicityBound.one_le_finrank_topEigen hQ
  have hzero : 1 ≤ f 0 := one_le_finrank_ker_signless_star c
  have hone : Fintype.card V ≤ f 1 + 2 := card_le_finrank_star_one_add_two c
  have hval : topEigen hQ = (Fintype.card V : ℝ) := topEigen_signlessLap_star c
  rw [hval] at htop
  -- the three are in the image, being of positive dimension
  have hmem : ∀ μ : ℝ, 0 < f μ → μ ∈ Finset.univ.image hQ.eigenvalues := by
    intro μ hμ
    by_contra hno
    exact absurd (HermitianDimensionSum.finrank_eigenspace_eq_zero_of_notMem hQ hno)
      (by simpa [hf] using hμ.ne')
  obtain ⟨d1, d2, -⟩ := three_distinct_star (V := V) h3
  have hsub : ({(Fintype.card V : ℝ), 1, 0} : Finset ℝ)
      ⊆ Finset.univ.image hQ.eigenvalues := by
    intro μ hμ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hμ
    rcases hμ with rfl | rfl | rfl
    · exact hmem _ (by omega)
    · exact hmem _ (by omega)
    · exact hmem _ (by omega)
  have hcard : ({(Fintype.card V : ℝ), 1, 0} : Finset ℝ).sum f
      ≤ (Finset.univ.image hQ.eigenvalues).sum f :=
    Finset.sum_le_sum_of_subset hsub
  rw [HermitianDimensionSum.sum_finrank_image hQ] at hcard
  rw [Finset.sum_insert (by simp [d1, d2]), Finset.sum_insert (by simp), Finset.sum_singleton]
    at hcard
  -- `set` abstracts syntactically and the goal needs a beta step, so it was left alone;
  -- without this `show` the goal and `hcard` are two different atoms to `omega`.
  -- `set` leaves `f x` unapplied in some hypotheses and beta-reduced in
  -- others; `omega` counts those as different atoms, so unfold before calling it.
  simp only [hf] at htop hzero hone hcard
  omega

/-- **AND THEREFORE THE SPECTRAL RADIUS IS SIMPLE.** The same squeeze, read at the
other end. `SignlessPerronSimple.top_simple_connected` gives this too, from
connectivity; this route gives it from the count and needs no Perron theory. -/
theorem finrank_signless_star_top [Nontrivial V] (c : V) (h3 : 3 ≤ Fintype.card V) :
    Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (signlessLap (starGraph c))
        - (Fintype.card V : ℝ) • LinearMap.id)) = 1 := by
  classical
  set hQ := LaplacianSignlessDefinite.signlessLap_isHermitian (starGraph c) with hQdef
  set f : ℝ → ℕ := fun μ => Module.finrank ℝ (LinearMap.ker
    (Matrix.toLin' (signlessLap (starGraph c)) - μ • LinearMap.id)) with hf
  have htop : 1 ≤ f (topEigen hQ) :=
    SignlessMultiplicityBound.one_le_finrank_topEigen hQ
  have hzero : 1 ≤ f 0 := one_le_finrank_ker_signless_star c
  have hone : f 1 = Fintype.card V - 2 := finrank_signless_star_one c h3
  have hval : topEigen hQ = (Fintype.card V : ℝ) := topEigen_signlessLap_star c
  rw [hval] at htop
  have hmem : ∀ μ : ℝ, 0 < f μ → μ ∈ Finset.univ.image hQ.eigenvalues := by
    intro μ hμ
    by_contra hno
    exact absurd (HermitianDimensionSum.finrank_eigenspace_eq_zero_of_notMem hQ hno)
      (by simpa [hf] using hμ.ne')
  obtain ⟨d1, d2, -⟩ := three_distinct_star (V := V) h3
  have hsub : ({(Fintype.card V : ℝ), 1, 0} : Finset ℝ)
      ⊆ Finset.univ.image hQ.eigenvalues := by
    intro μ hμ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hμ
    rcases hμ with rfl | rfl | rfl
    · exact hmem _ (by omega)
    · exact hmem _ (by omega)
    · exact hmem _ (by omega)
  have hcard : ({(Fintype.card V : ℝ), 1, 0} : Finset ℝ).sum f
      ≤ (Finset.univ.image hQ.eigenvalues).sum f :=
    Finset.sum_le_sum_of_subset hsub
  rw [HermitianDimensionSum.sum_finrank_image hQ] at hcard
  rw [Finset.sum_insert (by simp [d1, d2]), Finset.sum_insert (by simp), Finset.sum_singleton]
    at hcard
  -- `set` leaves `f x` unapplied in some hypotheses and beta-reduced in
  -- others; `omega` counts those as different atoms, so unfold before calling it.
  simp only [hf] at htop hzero hone hcard
  omega

/-- **AND THE KERNEL IS EXACTLY A LINE.** §2 exhibited one vector in it; the same
squeeze says there is no second. This is where the colourability route would have
landed (`SignlessColourableNecessary.finrank_ker_eq_iff_colorable` with
`LaplacianSignlessKernel`'s component count), and it lands here for free. -/
theorem finrank_signless_star_zero [Nontrivial V] (c : V) (h3 : 3 ≤ Fintype.card V) :
    Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (signlessLap (starGraph c)) - (0 : ℝ) • LinearMap.id)) = 1 := by
  classical
  set hQ := LaplacianSignlessDefinite.signlessLap_isHermitian (starGraph c) with hQdef
  set f : ℝ → ℕ := fun μ => Module.finrank ℝ (LinearMap.ker
    (Matrix.toLin' (signlessLap (starGraph c)) - μ • LinearMap.id)) with hf
  have htop : 1 ≤ f (topEigen hQ) :=
    SignlessMultiplicityBound.one_le_finrank_topEigen hQ
  have hzero : 1 ≤ f 0 := one_le_finrank_ker_signless_star c
  have hone : f 1 = Fintype.card V - 2 := finrank_signless_star_one c h3
  have hval : topEigen hQ = (Fintype.card V : ℝ) := topEigen_signlessLap_star c
  rw [hval] at htop
  have hmem : ∀ μ : ℝ, 0 < f μ → μ ∈ Finset.univ.image hQ.eigenvalues := by
    intro μ hμ
    by_contra hno
    exact absurd (HermitianDimensionSum.finrank_eigenspace_eq_zero_of_notMem hQ hno)
      (by simpa [hf] using hμ.ne')
  obtain ⟨d1, d2, -⟩ := three_distinct_star (V := V) h3
  have hsub : ({(Fintype.card V : ℝ), 1, 0} : Finset ℝ)
      ⊆ Finset.univ.image hQ.eigenvalues := by
    intro μ hμ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hμ
    rcases hμ with rfl | rfl | rfl
    · exact hmem _ (by omega)
    · exact hmem _ (by omega)
    · exact hmem _ (by omega)
  have hcard : ({(Fintype.card V : ℝ), 1, 0} : Finset ℝ).sum f
      ≤ (Finset.univ.image hQ.eigenvalues).sum f :=
    Finset.sum_le_sum_of_subset hsub
  rw [HermitianDimensionSum.sum_finrank_image hQ] at hcard
  rw [Finset.sum_insert (by simp [d1, d2]), Finset.sum_insert (by simp), Finset.sum_singleton]
    at hcard
  -- `set` leaves `f x` unapplied in some hypotheses and beta-reduced in
  -- others; `omega` counts those as different atoms, so unfold before calling it.
  simp only [hf] at htop hzero hone hcard
  omega

/-- **THE SPECTRUM IS COMPLETE**: the three multiplicities account for every
dimension, so `{|V|, 1, 0}` is the whole spectrum and there is no fourth
eigenvalue to look for. -/
theorem sum_finrank_signless_star [Nontrivial V] (c : V) (h3 : 3 ≤ Fintype.card V) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap (starGraph c))
          - (Fintype.card V : ℝ) • LinearMap.id))
      + Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap (starGraph c)) - (1 : ℝ) • LinearMap.id))
      + Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap (starGraph c)) - (0 : ℝ) • LinearMap.id))
      = Fintype.card V := by
  rw [finrank_signless_star_top c h3, finrank_signless_star_one c h3,
    finrank_signless_star_zero c h3]
  omega

/-! ## 4. Review round 63 — the ways this could be hollow

**"The three multiplicities could be read off an existing spectrum."** They could
not: the estate has no multiplicity statement about the star at all, which is what
the family table found and what `grep starGraph | grep finrank` returns empty.
What it has is the spectral RADIUS (`SignlessStarExact.topEigen_signlessLap_star`),
and a radius is one number.

**"§3 could be Perron's theorem in disguise."** `finrank_signless_star_top` is
also a corollary of `SignlessPerronSimple.top_simple_connected`, and the docstring
says so. It is proved here by the count instead, because the same count is what
gives `1`'s multiplicity and there is no reason to import a second mechanism for
one of the three. The `0` and `1` multiplicities are not Perron's theorem in any
disguise.

**"The twin class might be the whole vertex set again."** It is not, and that is
the difference from `SignlessMultiplicityBound`: there the class was `univ` on a
complete graph, here it is `univ.erase c`, of size `|V| − 1`, on a graph where the
remaining vertex has a different degree. This is the first use of the class form
at a class that is neither a pair nor everything.

**"`h3` might be hiding a degenerate case."** At `|V| = 2` the star is a single
edge, `|V| = 2` and `1` collide as eigenvalues, and the three-term sum is not a sum
over distinct values — so the hypothesis is doing real work and is not decoration.
At `|V| = 1` there are no edges at all.

**"Completeness might not follow."** §3's last theorem is the sum, which is what
`HermitianDimensionSum.sum_finrank_image` compares against; equality there says the
three eigenspaces fill `ℝ^V`, hence no fourth eigenvalue. It does not name the
image as a Finset, which would be the other way to say it and is bookkeeping
nothing consumes (`ERRATUM 246`).
-/

end

end SignlessStarSpectrum
