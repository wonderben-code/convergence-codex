import CutRankWitness

/-!
# Twin half-sites, and the degenerate direction at the torus exhibited

`CutRank.not_strict_of_rank_lt` needs a **rank**, and `RE-SWEEP #23` recorded the cost of that
plainly: off a block cut a rank is a dimension and nothing in the estate makes it decidable by
enumeration. `CutRank.rank_lt_of_isolated` is one decidable sufficient condition — a half-site the
cut misses entirely. This is a second, and it reaches cases the first cannot.

> **`not_strict_of_twins`** — if two distinct half-sites have **the same cross-neighbours in the
> half**, the reflected form is not strict. Decidable on a finite graph; no block hypothesis, no
> diagonality, no semidefiniteness.

The reason is one line of linear algebra: equal columns of the cut matrix are a linear dependence,
and `CutRank.ker_cutRows` says a linear dependence among the columns **is** a reach-kernel vector.
`twinDiff` is that vector written down.

## The two certificates are independent, and both directions are witnessed

Neither condition implies the other, and this file proves it rather than saying it:

* **Twins without an isolated site** — the four-cycle's antipodal half. Both its sites meet the cut
  (`no_isolated_torusHalf`), so `CutRank.rank_lt_of_isolated` cannot fire there; they are twins
  (`twins_torusHalf`), so this one can.
* **An isolated site without twins** — `GreenLargeMass.stepGraph` on `Hs`. Site `2` meets the cut
  nowhere, and no two of the three half-sites have the same cross-neighbours (`no_twins_Hs`).

Both graphs were already in the estate. `ERRATUM 48`: a criterion producing no member it could not
produce before is a criterion whose usefulness is asserted, and the same test applied in both
directions is what "independent" has to mean.

## And the degeneracy at the torus stops being a number and becomes a vector

`TorusBlockCount.finrank_reachKer_torusHalf = 1` says the antipodal half degenerates in exactly one
direction and **exhibits no direction at all**.

> **`reachKer_torusHalf_eq_span`** — that space is spanned by `twinDiff` of the antipodal pair: the
> family that is `+1` at one site, `−1` at the other, and zero elsewhere.

So the estate's flagship non-strict half now has its degenerate direction written down, and the
reason it is degenerate is combinatorial — the two antipodal sites are joined to exactly the same
mirror images.

**No published tag moves**, `OS4` does not move, and no spectral gap is claimed.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CutTwins

open SimpleGraph GraphReflection GraphMirrorReflection CrossFormMatrix CrossBlockStructure
open CrossPosSemidef BlockCount NullSpaceDimension ReachKernelDimension CutRank

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {θ : V ≃ V} {H Mir : Finset V} {m : ℝ}
variable {s t : V}

/-! ## 1. Twins, and the vector they contribute -/

/-- **TWO HALF-SITES WITH THE SAME CROSS-NEIGHBOURS IN THE HALF.** A condition on vertices only,
so decidable on a finite graph. -/
def Twins (G : SimpleGraph V) (θ : V ≃ V) (H : Finset V) (s t : V) : Prop :=
  s ∈ H ∧ t ∈ H ∧ s ≠ t ∧ ∀ q ∈ H, (G.Adj q (θ s) ↔ G.Adj q (θ t))

instance : Decidable (Twins G θ H s t) :=
  inferInstanceAs (Decidable (s ∈ H ∧ t ∈ H ∧ s ≠ t ∧ ∀ q ∈ H, (G.Adj q (θ s) ↔ G.Adj q (θ t))))

/-- The difference of the two indicators: `+1` at `s`, `−1` at `t`, zero elsewhere. -/
def twinDiff (s t : V) : V → ℝ := fun p => if p = s then 1 else if p = t then -1 else 0

omit [Fintype V] in
/-- **TWINS HAVE EQUAL COLUMNS IN THE CUT MATRIX.** The definition says the two sites have the same
cross-neighbours; the matrix says the same thing with entries. -/
theorem cross_col_eq (htw : Twins G θ H s t) {s' : V} (hs' : s' ∈ H) :
    crossMatrix G θ H s' s = crossMatrix G θ H s' t := by
  obtain ⟨hs, ht, -, hadj⟩ := htw
  rw [crossMatrix, crossMatrix, if_pos ⟨hs', hs⟩, if_pos ⟨hs', ht⟩, crossAdj, crossAdj]
  by_cases hA : G.Adj s' (θ s)
  · rw [if_pos hA, if_pos ((hadj s' hs').mp hA)]
  · rw [if_neg hA, if_neg fun hc => hA ((hadj s' hs').mpr hc)]

omit [Fintype V] in
/-- Nonzero, and **`s ≠ t` is not needed for it**: the value at `s` is `1` from the first branch
whatever `t` is. The linter caught the hypothesis being carried and it is dropped rather than
kept for symmetry with `Twins`. -/
theorem twinDiff_ne_zero : twinDiff s t ≠ (0 : V → ℝ) := by
  intro hc
  have := congrFun hc s
  rw [twinDiff, if_pos rfl] at this
  exact one_ne_zero this

/-- **AND SO TWINS PUT A VECTOR IN THE REACH KERNEL.** Equal columns are a linear dependence, and
`CutRank.ker_cutRows` says a linear dependence among the columns is a reach-kernel vector. -/
theorem twinDiff_mem_reachKer (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (m : ℝ)
    (htw : Twins G θ H s t) : twinDiff s t ∈ reachKer G m H Mir := by
  classical
  have hs := htw.1
  have ht := htw.2.1
  have hne := htw.2.2.1
  rw [mem_reachKer, inReachKernel_iff_rows hM h m]
  refine ⟨fun p hp => ?_, fun s' hs' => ?_⟩
  · have hps : p ≠ s := by rintro rfl; exact hp hs
    have hpt : p ≠ t := by rintro rfl; exact hp ht
    rw [twinDiff, if_neg hps, if_neg hpt]
  · have hterm : ∀ q ∈ H, crossMatrix G θ H s' q * twinDiff s t q
        = (if q = s then crossMatrix G θ H s' s else 0)
          - (if q = t then crossMatrix G θ H s' t else 0) := by
      intro q _
      rw [twinDiff]
      by_cases hqs : q = s
      · subst hqs
        rw [if_pos rfl, if_pos rfl, if_neg hne, mul_one, sub_zero]
      · by_cases hqt : q = t
        · subst hqt
          rw [if_neg hqs, if_pos rfl, if_neg hqs, if_pos rfl, mul_neg, mul_one, zero_sub]
        · rw [if_neg hqs, if_neg hqt, if_neg hqs, if_neg hqt, mul_zero, sub_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' H s (fun _ => crossMatrix G θ H s' s),
      Finset.sum_ite_eq' H t (fun _ => crossMatrix G θ H s' t), if_pos hs, if_pos ht,
      cross_col_eq htw hs']
    exact sub_self _

/-! ## 2. The certificate -/

omit [Fintype V] in
/-- **TWINS MAKE THE CUT RANK-DEFICIENT.** -/
theorem rank_lt_of_twins [Finite V] (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (htw : Twins G θ H s t) :
    Module.finrank ℝ (LinearMap.range (cutRows G θ H)) < H.card := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hne : reachKer G (0 : ℝ) H Mir ≠ ⊥ := by
    intro hbot
    have hmem := twinDiff_mem_reachKer (Mir := Mir) hM h (0 : ℝ) htw
    rw [hbot, Submodule.mem_bot] at hmem
    exact twinDiff_ne_zero hmem
  have hpos : 0 < Module.finrank ℝ (reachKer G (0 : ℝ) H Mir) :=
    Nat.pos_of_ne_zero fun hz => hne (Submodule.finrank_eq_zero.mp hz)
  have hid := finrank_reachKer_add_rank (Mir := Mir) hM h (0 : ℝ)
  omega

/-- **A SECOND DECIDABLE NON-STRICTNESS CERTIFICATE.** No block hypothesis, no diagonality, no
semidefiniteness — and, unlike `CutRank.not_strict_of_isolated`, it fires when every half-site meets
the cut. -/
theorem not_strict_of_twins (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (htw : Twins G θ H s t) :
    ¬ (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c) :=
  not_strict_of_rank_lt hM h hm (rank_lt_of_twins (Mir := Mir) hM h htw)

/-! ## 3. The two certificates are independent, both ways -/

open ReflectedFormCongr TorusReflection in
/-- The two sites of the antipodal half are twins: each is joined to **both** mirror images. -/
theorem twins_torusHalf :
    Twins (torusGraph 1 4) torusRho torusHalf (torusFourEquiv.symm 0) (torusFourEquiv.symm 1) := by
  decide

open ReflectedFormCongr TorusReflection in
/-- **AND NEITHER OF THEM IS ISOLATED**, so `CutRank.rank_lt_of_isolated` cannot fire there. This is
the first half of the independence. -/
theorem no_isolated_torusHalf :
    ∀ s ∈ torusHalf, ¬ (∀ q ∈ torusHalf, ¬ (torusGraph 1 4).Adj q (torusRho s)) := by decide

open GreenLargeMass in
/-- **AND THE STEP GRAPH HAS AN ISOLATED SITE AND NO TWINS**, which is the other half. Together
with the line above: neither certificate subsumes the other, on two graphs the estate already
had. -/
theorem no_twins_Hs : ∀ s ∈ Hs, ∀ t ∈ Hs, ¬ Twins stepGraph sigma6 Hs s t := by decide

/-! ## 4. The degenerate direction at the torus, exhibited -/

open ReflectedFormCongr TorusReflection in
/-- **THE ANTIPODAL HALF'S DEGENERATE DIRECTION.** `TorusBlockCount.finrank_reachKer_torusHalf`
says the space is one-dimensional and exhibits nothing in it. This is the vector: `+1` at one site
of the antipodal pair, `−1` at the other.

**And it spans**, because the dimension is already known to be `1`. So the estate's flagship
non-strict half has its degeneracy written down, and the reason for it is combinatorial. -/
theorem reachKer_torusHalf_eq_span (m : ℝ) :
    reachKer (torusGraph 1 4) m torusHalf (∅ : Finset (BoxGraph.Site 1 4))
      = Submodule.span ℝ {twinDiff (torusFourEquiv.symm 0) (torusFourEquiv.symm 1)} := by
  have hmem := twinDiff_mem_reachKer (Mir := (∅ : Finset (BoxGraph.Site 1 4)))
    isMirrorHalf_torusHalf isRefl_torusRho m twins_torusHalf
  have hle : Submodule.span ℝ {twinDiff (torusFourEquiv.symm 0) (torusFourEquiv.symm 1)}
      ≤ reachKer (torusGraph 1 4) m torusHalf ∅ := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hmem
  have hspan : Module.finrank ℝ
      (Submodule.span ℝ {twinDiff (torusFourEquiv.symm 0) (torusFourEquiv.symm 1)}) = 1 :=
    finrank_span_singleton twinDiff_ne_zero
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [hspan, TorusBlockCount.finrank_reachKer_torusHalf m]

/-! ## 5. Where this certificate adds nothing, and why the torus is where it fires -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **ON A DIAGONAL CUT, TWINS ARE BOTH ISOLATED — SO THIS CERTIFICATE ADDS NOTHING THERE.**

If the only cross-cut adjacency inside the half is a site to its own mirror, then two sites with the
same cross-neighbours must have none: a neighbour of `θ s` inside the half can only be `s`, and the
twin condition would then force `s` adjacent to `θ t` and hence `s = t`.

**This is a negative result about the tool above and it is the point of this section.**
`GraphMirrorReflection.crossForm_nonpos_of_cross_diag` is the estate's only route to the coupling
hypothesis and it asks exactly for diagonality; every lattice family in the estate satisfies it
(`CrossBlockStructure.box_cross_diag_any` and its torus and lattice siblings). **So on every family
the estate actually studies, `not_strict_of_twins` is subsumed by
`CutRank.not_strict_of_isolated`,** and §3's independence is a statement about cuts the lattices do
not produce.

**Which is exactly where the torus's antipodal half sits.**
`HalfBlockStructure.not_crossDiag_torusHalf` says that cut is **not** diagonal — it is a block cut
with a block of size two — and that is why twins can fire there at all. The certificate is not
useless and it is not general: it is a tool for block cuts with blocks bigger than a point, and
this theorem is what pins that down. -/
theorem isolated_of_twins_of_diagonal
    (hdiag : ∀ p ∈ H, ∀ q ∈ H, G.Adj p (θ q) → p = q) (htw : Twins G θ H s t) :
    (∀ q ∈ H, ¬ G.Adj q (θ s)) ∧ (∀ q ∈ H, ¬ G.Adj q (θ t)) := by
  obtain ⟨hs, ht, hne, hadj⟩ := htw
  have key : ∀ q ∈ H, ¬ G.Adj q (θ s) := by
    intro q hq hA
    have hqs : q = s := hdiag q hq s hs hA
    rw [hqs] at hA
    exact hne (hdiag s hs t ht ((hadj s hs).mp hA))
  refine ⟨key, fun q hq hA => ?_⟩
  have hqt : q = t := hdiag q hq t ht hA
  rw [hqt] at hA
  exact key t ht ((hadj t ht).mpr hA)

/-! ## 6. On a block cut, twins are exactly co-membership of a block -/

omit [Fintype V] in
/-- **TWO MEMBERS OF THE SAME BLOCK ARE TWINS.** The block relation is transitive by
`IsCrossBlock.trans` and symmetric by `CrossFormMatrix.adj_cross_comm`, so a cross-neighbour of one
member is a cross-neighbour of every member. -/
theorem twins_of_mem_cls (h : IsRefl G θ) (hC : IsCrossBlock G θ H) {k : V}
    (hsk : s ∈ cls (crossMatrix G θ H) H k) (htk : t ∈ cls (crossMatrix G θ H) H k)
    (hne : s ≠ t) : Twins G θ H s t := by
  obtain ⟨⟨hsH, -⟩, hkH, hks⟩ := mem_cls_iff.mp hsk
  obtain ⟨⟨htH, -⟩, -, hkt⟩ := mem_cls_iff.mp htk
  have hsk' : G.Adj s (θ k) := (adj_cross_comm h k s).mp hks
  have htk' : G.Adj t (θ k) := (adj_cross_comm h k t).mp hkt
  have hst : G.Adj s (θ t) := hC.trans s k t ⟨hsH, hkH, hsk'⟩ ⟨hkH, htH, hkt⟩
  have hts : G.Adj t (θ s) := hC.trans t k s ⟨htH, hkH, htk'⟩ ⟨hkH, hsH, hks⟩
  refine ⟨hsH, htH, hne, fun q hq => ⟨fun hA => ?_, fun hA => ?_⟩⟩
  · exact hC.trans q s t ⟨hq, hsH, hA⟩ ⟨hsH, htH, hst⟩
  · exact hC.trans q t s ⟨hq, htH, hA⟩ ⟨htH, hsH, hts⟩

omit [Fintype V] in
/-- **AND ON A BLOCK CUT A HALF-SITE OUTSIDE `blk` MEETS THE CUT NOWHERE.** `IsCrossBlock.loop`
read contrapositively: a cross-neighbour would put the site in `blk`. -/
theorem isolated_of_notMem_blk (h : IsRefl G θ) (hC : IsCrossBlock G θ H) {s : V} (hs : s ∈ H)
    (hnb : s ∉ blk (crossMatrix G θ H) H) : ∀ q ∈ H, ¬ G.Adj q (θ s) := by
  intro q hq hA
  exact hnb (mem_blk_iff.mpr ⟨hs, hC.loop s q ⟨hs, hq, (adj_cross_comm h q s).mp hA⟩⟩)

omit [Fintype V] in
/-- **TWINS CANNOT STRADDLE.** If one twin meets the cut then so does the other, and they share a
block. -/
theorem mem_cls_of_twins (h : IsRefl G θ) (htw : Twins G θ H s t)
    (hs : s ∈ blk (crossMatrix G θ H) H) : t ∈ cls (crossMatrix G θ H) H s := by
  obtain ⟨hsH, htH, -, hadj⟩ := htw
  have hss : G.Adj s (θ s) := (mem_blk_iff.mp hs).2
  have hst : G.Adj s (θ t) := (hadj s hsH).mp hss
  have hts : G.Adj t (θ s) := (adj_cross_comm h s t).mp hst
  have htt : G.Adj t (θ t) := (hadj t htH).mp hts
  exact mem_cls_iff.mpr ⟨⟨htH, htt⟩, hsH, hst⟩

omit [Fintype V] in
/-- **THE CHARACTERISATION, AND IT MAKES THE TWO CERTIFICATES ONE THING.**

On a block cut, two distinct half-sites are twins exactly when they **share a block** or **both meet
the cut nowhere**. Read together with `CutRank.rank_lt_of_isolated`, both non-strictness
certificates in this chain say the same thing in different words: **the cut cannot tell the two
sites apart**, either because it joins them to the same places or because it joins them to nothing.

It also finishes §5's account, and §7 turns that into a theorem rather than a reading. -/
theorem twins_iff_block_or_isolated (h : IsRefl G θ) (hC : IsCrossBlock G θ H)
    (hs : s ∈ H) (ht : t ∈ H) (hne : s ≠ t) :
    Twins G θ H s t
      ↔ ((∃ k, s ∈ cls (crossMatrix G θ H) H k ∧ t ∈ cls (crossMatrix G θ H) H k)
          ∨ ((∀ q ∈ H, ¬ G.Adj q (θ s)) ∧ (∀ q ∈ H, ¬ G.Adj q (θ t)))) := by
  constructor
  · intro htw
    by_cases hb : s ∈ blk (crossMatrix G θ H) H
    · exact Or.inl ⟨s, self_mem_cls hb, mem_cls_of_twins h htw hb⟩
    · refine Or.inr ⟨isolated_of_notMem_blk h hC hs hb, fun q hq hA => ?_⟩
      exact isolated_of_notMem_blk h hC hs hb q hq ((htw.2.2.2 q hq).mpr hA)
  · rintro (⟨k, hsk, htk⟩ | ⟨hi, hj⟩)
    · exact twins_of_mem_cls h hC hsk htk hne
    · exact ⟨hs, ht, hne, fun q hq => ⟨fun hA => absurd hA (hi q hq),
        fun hA => absurd hA (hj q hq)⟩⟩

/-! ## 7. And on a block cut the two certificates are complete -/

/-- **NON-STRICTNESS ON A BLOCK CUT IS EXACTLY: AN ISOLATED SITE, OR A PAIR OF TWINS.**

`CrossBlockStructure.strict_iff_cut_perfect` says a block cut is strict exactly when
`∀ s q ∈ H, G.Adj s (θ q) ↔ s = q`. Read the two ways that can fail: the `←` direction fails at
some site joined to nothing (**isolated**), and the `→` direction fails at two distinct sites joined
across the cut, which §6 says is **twins**.

**So `CutRank.not_strict_of_isolated` and `not_strict_of_twins` are together the whole of
non-strictness on a block cut, and neither alone is** — §3 already exhibited a graph for each side.
Both hypotheses are decidable, so on a block cut non-strictness is decidable by enumeration through
this pair, which is what `RE-SWEEP #23` recorded as missing for a rank.

**It does NOT extend off a block cut.** The forward direction runs through `strict_iff_cut_perfect`,
which consumes `IsCrossBlock`, and `CutRankWitness.rank_full_not_strict_crossGraph` is a graph where
non-strictness has neither cause. -/
theorem not_strict_iff_isolated_or_twins (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hC : IsCrossBlock G θ H) :
    ¬ (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c)
      ↔ ((∃ s ∈ H, ∀ q ∈ H, ¬ G.Adj q (θ s))
          ∨ (∃ s ∈ H, ∃ t ∈ H, Twins G θ H s t)) := by
  classical
  rw [strict_iff_cut_perfect hM h hm hC]
  constructor
  · intro hno
    push Not at hno
    obtain ⟨s, hs, q, hq, hiff⟩ := hno
    rcases hiff with ⟨hA, hne⟩ | ⟨hA, hsq⟩
    · have h1 : crossMatrix G θ H s q = 1 := (crossMatrix_eq_one_iff s q).mpr ⟨hs, hq, hA⟩
      obtain ⟨hsb, hqb⟩ := mem_blk_of_entry h hC h1
      refine Or.inr ⟨s, hs, q, hq, twins_of_mem_cls h hC (self_mem_cls hsb) ?_ hne⟩
      exact mem_cls_iff.mpr ⟨⟨hq, (mem_blk_iff.mp hqb).2⟩, hs, hA⟩
    · rw [← hsq] at hA
      exact Or.inl ⟨s, hs, isolated_of_notMem_blk h hC hs fun hb => hA (mem_blk_iff.mp hb).2⟩
  · rintro (⟨s, hs, hiso⟩ | ⟨s, hs, t, ht, htw⟩) hperf
    · exact hiso s hs ((hperf s hs s hs).mpr rfl)
    · exact htw.2.2.1 ((hperf s hs t ht).mp ((htw.2.2.2 s hs).mp ((hperf s hs s hs).mpr rfl)))

end CutTwins
