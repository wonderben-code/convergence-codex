import IsingNaiveBound
import PlusClassVanishes

/-!
# The shortest contour has length two, and a corner flip realises it

`UNLOCK_WATCHLIST` has carried an item called *"is the minimum contour length two?"* since
9 August, **opened rather than answered on purpose**: the review of `IsingNaiveBound` had
argued that its `e^{-4β}` bound was sharp by asserting that a configuration with exactly
**one** broken bond exists, and that assertion was unproved and looked false. The item named
what a proof would need — *"every bond lies in some unit square"* — and left it.

**That ingredient arrived the next day, in a file written for something else**
(`DualBonds.exists_side_eq`, built to make the dual lattice cover the primal bonds), and
nothing connected the two until the watchlist was re-swept. This file connects them.

## The bound

`IsingContourPlaquette.even_plaquette` says every unit square carries an **even** number of
broken bonds. A configuration with exactly one broken bond in the whole box would put that
bond on some square — by `exists_side_eq`, with no hypothesis — and the other three sides of
that square are different bonds, so they are unbroken and the square carries **one**.

> **`two_le_card_contour`** — every non-constant configuration breaks at least two bonds.

## The witness, because a bound with no witness is not a minimum

`cornerDown` is the configuration that is up everywhere except the corner. The corner has
exactly two neighbours, so it breaks exactly those two bonds, and
**`card_contour_cornerDown`** says the count is `2` — the lower bound above supplying one
half of the equality and a two-element superset the other.

## What it buys, and it is a constant rather than a theorem

`IsingNaiveBound.gibbs_le_of_not_const` reads `gibbs{σ} ≤ e^{-4β} gibbs{ground}`; with two
bonds instead of one it becomes **`gibbs_le_of_not_const_eight`**, `e^{-8β}`. And
**`gibbs_cornerDown`** shows the corner-flip configuration attains it exactly, so `8` cannot
be improved: it is the true single-configuration constant for this model, not an artefact of
the estimate.

**This does not rescue the union bound, and that is proved rather than said**:
**`naive_union_bound_fails_eight`** is the old failure at the new constant, obtained by
running the old theorem at `2β`. `2^{n²}` configurations against a *fixed* suppression is
hopeless at any constant, which is why the Peierls chain groups by contour length instead.

The value here is that an **unproved assertion in a review has been refuted**
(`card_contour_ne_one`: no configuration breaks exactly one bond, ever) and that the constant
the estate quotes is now known to be the right one.

`IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace MinimumContour

open IsingFiniteVolume IsingContourEnergy IsingContourSeparation IsingContourGibbs
open IsingContourPlaquette PlaquetteLattice DualBonds MeasureTheory

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. One broken bond would make a square odd -/

/-- Read `even_plaquette` in the `sideL/sideU/sideR/sideD` vocabulary `exists_side_eq`
answers in. -/
theorem even_plaquette_sides (σ : Config n) (P : Plaq n) :
    Even ((if sideL P ∈ contour σ then 1 else 0) + (if sideU P ∈ contour σ then 1 else 0)
      + (if sideR P ∈ contour σ then 1 else 0) + (if sideD P ∈ contour σ then 1 else 0)) := by
  simpa only [sideL, sideU, sideR, sideD] using even_plaquette σ P.i P.j P.hi P.hj

/-- **EVERY NON-CONSTANT CONFIGURATION BREAKS AT LEAST TWO BONDS.** One would sit on a unit
square whose other three sides are different bonds, hence unbroken, making that square's
count odd — and `even_plaquette` says it is even. -/
theorem two_le_card_contour (hn : 0 < n) {σ : Config n}
    (h1 : σ ≠ fun _ => true) (h2 : σ ≠ fun _ => false) :
    2 ≤ (contour σ).card := by
  classical
  by_contra hlt
  have hlt2 : (contour σ).card < 2 := Nat.lt_of_not_le hlt
  have hcard : (contour σ).card = 1 := by
    have := IsingNaiveBound.contour_card_pos hn h1 h2
    omega
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  have hiff : ∀ s : Sym2 (Site n), s ∈ contour σ ↔ s = e := by
    intro s; rw [he, Finset.mem_singleton]
  -- the single broken bond, as an adjacent pair
  have hmem : e ∈ contour σ := by rw [he]; exact Finset.mem_singleton_self e
  -- one side of some square is `e` and the other three are not, so the square counts one
  have hone : ∀ P : Plaq n, ∀ _ : sideL P = e ∨ sideU P = e ∨ sideR P = e ∨ sideD P = e,
      False := by
    intro P hP
    have heven := even_plaquette_sides σ P
    simp only [hiff] at heven
    rcases hP with hL | hU | hR | hD
    · rw [if_pos hL, if_neg fun hc => sideL_ne_sideU P (hL.trans hc.symm),
        if_neg fun hc => sideL_ne_sideR P (hL.trans hc.symm),
        if_neg fun hc => sideL_ne_sideD P (hL.trans hc.symm)] at heven
      simp at heven
    · rw [if_neg fun hc => sideL_ne_sideU P (hc.trans hU.symm), if_pos hU,
        if_neg fun hc => sideU_ne_sideR P (hU.trans hc.symm),
        if_neg fun hc => sideU_ne_sideD P (hU.trans hc.symm)] at heven
      simp at heven
    · rw [if_neg fun hc => sideL_ne_sideR P (hc.trans hR.symm),
        if_neg fun hc => sideU_ne_sideR P (hc.trans hR.symm), if_pos hR,
        if_neg fun hc => sideR_ne_sideD P (hR.trans hc.symm)] at heven
      simp at heven
    · rw [if_neg fun hc => sideL_ne_sideD P (hc.trans hD.symm),
        if_neg fun hc => sideU_ne_sideD P (hc.trans hD.symm),
        if_neg fun hc => sideR_ne_sideD P (hc.trans hD.symm), if_pos hD] at heven
      simp at heven
  induction e using Sym2.ind with
  | _ p q =>
    have hadj : adj p q := ((mem_contour σ p q).mp hmem).1
    rcases exists_side_eq hadj with ⟨P, hP⟩ | ⟨P, hP⟩ | ⟨P, hP⟩ | ⟨P, hP⟩
    · exact hone P (Or.inl hP)
    · exact hone P (Or.inr (Or.inl hP))
    · exact hone P (Or.inr (Or.inr (Or.inl hP)))
    · exact hone P (Or.inr (Or.inr (Or.inr hP)))

/-- **THE REVIEW'S ASSERTION, REFUTED.** No configuration whatever breaks exactly one bond:
a constant one breaks none and every other breaks at least two. That sentence — *"a
configuration with exactly one broken bond exists on a big enough box"* — is what the
watchlist item was opened to settle, and it is false. -/
theorem card_contour_ne_one (hn : 0 < n) (σ : Config n) : (contour σ).card ≠ 1 := by
  classical
  by_cases hconst : (σ = fun _ => true) ∨ (σ = fun _ => false)
  · have hempty : contour σ = ∅ :=
      (contour_eq_empty_iff hn σ).mpr ((const_iff_eq hn σ).mpr hconst)
    rw [hempty]
    simp
  · obtain ⟨hne1, hne2⟩ := not_or.mp hconst
    have := two_le_card_contour hn hne1 hne2
    omega

/-! ## 2. The corner flip, which breaks exactly two -/

/-- Up everywhere except the corner `(0,0)`. Written without a positivity hypothesis, so that
no proof term travels inside the definition. -/
def cornerDown (n : ℕ) : Config n :=
  fun p => !(decide (p.1.val = 0 ∧ p.2.val = 0))

theorem cornerDown_eq_false_iff (p : Site n) :
    cornerDown n p = false ↔ (p.1.val = 0 ∧ p.2.val = 0) := by
  simp [cornerDown]

theorem cornerDown_eq_true_iff (p : Site n) :
    cornerDown n p = true ↔ ¬ (p.1.val = 0 ∧ p.2.val = 0) := by
  simp only [cornerDown, Bool.not_eq_true', decide_eq_false_iff_not]

/-- **The corner has exactly two neighbours**, and they are the two sites one step along
each axis. No hypothesis on `n`: on a one-column box the corner has no neighbour at all and
`hadj` is already contradictory. -/
theorem adj_corner {p q : Site n} (hadj : adj p q)
    (hp : p.1.val = 0 ∧ p.2.val = 0) :
    (q.1.val = 0 ∧ q.2.val = 1) ∨ (q.1.val = 1 ∧ q.2.val = 0) := by
  have hq1 := q.1.isLt
  have hq2 := q.2.isLt
  simp only [adj, Fin.ext_iff] at hadj
  omega

theorem cornerDown_ne_allTrue (hn : 0 < n) : cornerDown n ≠ fun _ => true := by
  intro hcon
  have h := congrFun hcon ((⟨0, hn⟩ : Fin n), (⟨0, hn⟩ : Fin n))
  have hf : cornerDown n ((⟨0, hn⟩ : Fin n), (⟨0, hn⟩ : Fin n)) = false :=
    (cornerDown_eq_false_iff _).mpr ⟨rfl, rfl⟩
  rw [hf] at h
  exact Bool.noConfusion h

theorem cornerDown_ne_allFalse (hn : 1 < n) : cornerDown n ≠ fun _ => false := by
  intro hcon
  have h := congrFun hcon ((⟨0, by omega⟩ : Fin n), (⟨1, hn⟩ : Fin n))
  have ht : cornerDown n ((⟨0, by omega⟩ : Fin n), (⟨1, hn⟩ : Fin n)) = true :=
    (cornerDown_eq_true_iff _).mpr (by simp)
  rw [ht] at h
  exact Bool.noConfusion h

/-- At most two: a broken bond must have the corner as one endpoint, and the corner has two
neighbours. -/
theorem card_contour_cornerDown_le (hn : 1 < n) : (contour (cornerDown n)).card ≤ 2 := by
  classical
  have hn0 : 0 < n := by omega
  have hsub : contour (cornerDown n) ⊆
      {s(((⟨0, hn0⟩ : Fin n), (⟨0, hn0⟩ : Fin n)), ((⟨0, hn0⟩ : Fin n), (⟨1, hn⟩ : Fin n))),
        s(((⟨0, hn0⟩ : Fin n), (⟨0, hn0⟩ : Fin n)),
          ((⟨1, hn⟩ : Fin n), (⟨0, hn0⟩ : Fin n)))} := by
    intro z hz
    induction z using Sym2.ind with
    | _ p q =>
      obtain ⟨hadj, hne⟩ := (mem_contour _ p q).mp hz
      have hcase : (p.1.val = 0 ∧ p.2.val = 0) ∨ (q.1.val = 0 ∧ q.2.val = 0) := by
        by_contra hno
        obtain ⟨h1, h2⟩ := not_or.mp hno
        rw [(cornerDown_eq_true_iff p).mpr h1, (cornerDown_eq_true_iff q).mpr h2] at hne
        exact hne rfl
      simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
      rcases hcase with hp | hq
      · have hpc : p = ((⟨0, hn0⟩ : Fin n), (⟨0, hn0⟩ : Fin n)) :=
          Prod.ext (Fin.ext hp.1) (Fin.ext hp.2)
        rcases adj_corner hadj hp with hq | hq
        · exact Or.inl (Or.inl ⟨hpc, Prod.ext (Fin.ext hq.1) (Fin.ext hq.2)⟩)
        · exact Or.inr (Or.inl ⟨hpc, Prod.ext (Fin.ext hq.1) (Fin.ext hq.2)⟩)
      · have hqc : q = ((⟨0, hn0⟩ : Fin n), (⟨0, hn0⟩ : Fin n)) :=
          Prod.ext (Fin.ext hq.1) (Fin.ext hq.2)
        rcases adj_corner ((adj_symm p q).mp hadj) hq with hp | hp
        · exact Or.inl (Or.inr ⟨Prod.ext (Fin.ext hp.1) (Fin.ext hp.2), hqc⟩)
        · exact Or.inr (Or.inr ⟨Prod.ext (Fin.ext hp.1) (Fin.ext hp.2), hqc⟩)
  exact le_trans (Finset.card_le_card hsub)
    (le_trans (Finset.card_insert_le _ _) (by simp))

/-- **THE MINIMUM IS ATTAINED.** The corner flip breaks exactly two bonds — at most two
because the corner has two neighbours, at least two by `two_le_card_contour`. -/
theorem card_contour_cornerDown (hn : 1 < n) : (contour (cornerDown n)).card = 2 :=
  le_antisymm (card_contour_cornerDown_le hn)
    (two_le_card_contour (by omega) (cornerDown_ne_allTrue (by omega))
      (cornerDown_ne_allFalse hn))

/-! ## 3. So the single-configuration constant is eight, and it is sharp -/

/-- **`gibbs{σ} ≤ e^{-8β} gibbs{ground}`** for every non-constant `σ`: the same argument as
`IsingNaiveBound.gibbs_le_of_not_const` with the sharp contour bound in place of `1 ≤ |γ|`. -/
theorem gibbs_le_of_not_const_eight (hn : 0 < n) {β : ℝ} (hβ : 0 ≤ β) {σ : Config n}
    (h1 : σ ≠ fun _ => true) (h2 : σ ≠ fun _ => false) :
    FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n)) {σ}
      ≤ ENNReal.ofReal (Real.exp (-(8 * β)))
        * FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n))
            {(fun _ => true)} := by
  have hc : (2 : ℝ) ≤ ((contour σ).card : ℝ) := by
    exact_mod_cast two_le_card_contour hn h1 h2
  have hstep : ENNReal.ofReal (Real.exp (-(4 * β) * ((contour σ).card : ℝ)))
      ≤ ENNReal.ofReal (Real.exp (-(8 * β))) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))
  rw [gibbs_singleton_contour n β σ]
  exact mul_le_mul_left hstep _

/-- **AND THE UNION BOUND STILL FAILS**, so the sharper constant buys nothing there: the
same statement as `IsingNaiveBound.naive_union_bound_fails`, at `e^{-8β}`, obtained from it
by running it at `2β`. `2^{n²}` configurations against a **fixed** suppression is hopeless at
any constant, which is why the Peierls chain groups by contour length instead. -/
theorem naive_union_bound_fails_eight (β C : ℝ) :
    ∃ N : ℕ, 0 < N ∧ C < (2 : ℝ) ^ (N * N) * Real.exp (-(8 * β)) := by
  obtain ⟨N, hN, hlt⟩ := IsingNaiveBound.naive_union_bound_fails (2 * β) C
  exact ⟨N, hN, by rwa [show -(4 * (2 * β)) = -(8 * β) from by ring] at hlt⟩

/-- **AND EIGHT IS SHARP.** The corner-flip configuration attains it with equality, so no
argument improves the constant for this model. -/
theorem gibbs_cornerDown (hn : 1 < n) (β : ℝ) :
    FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n)) {cornerDown n}
      = ENNReal.ofReal (Real.exp (-(8 * β)))
        * FiniteGibbs.gibbs β (isingH n) (Measure.count : Measure (Config n))
            {(fun _ => true)} := by
  rw [gibbs_singleton_contour n β (cornerDown n), card_contour_cornerDown hn]
  have harg : (-(4 * β) * ((2 : ℕ) : ℝ)) = -(8 * β) := by push_cast; ring
  rw [harg]

end MinimumContour
