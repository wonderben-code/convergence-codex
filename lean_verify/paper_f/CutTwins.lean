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
open NullSpaceDimension ReachKernelDimension CutRank

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

end CutTwins
