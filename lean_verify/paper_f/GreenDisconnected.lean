import GraphGreenPositive
import GraphMirrorReflection
import GreenExpansion
import StepGraphSmallMass

/-!
# The Green function vanishes between components, and what that costs reflection positivity

`GraphGreenPositive` proves the propagator non-negative on every finite graph and **strictly
positive on a connected one**. The complementary fact — that it is **zero** between two vertices
with no path between them — was never stated, and `StepGraphSmallMass` proved an instance of it by
hand, three linear equations at a time, on a six-vertex graph.

This file proves it in general, and then draws the consequence the instance was really about.

## The two theorems

`green_eq_zero_of_not_reachable`: on any finite simple graph and any nonzero mass, `green p q = 0`
whenever `q` is unreachable from `p`. The proof is one application of positive definiteness. Let

    x r = if G.Reachable p r then 0 else green G m r p

and check `massive *ᵥ x = 0` at each site. At a site reachable from `p`, every surviving term has
`r` unreachable, so `q` and `r` lie in different components and `massive q r = 0`. At a site *not*
reachable from `p`, the terms that were dropped are exactly those with `massive q r = 0` for the
same reason, so the sum is the full one, which is `(massive · green) q p = 0` because `q ≠ p`.
`massive` is positive definite, so `x = 0`.

`not_reflectionPositive_of_mirror_offComponent`: **if the reflection carries two half-sites out of
their own components, and the propagator does not vanish between the mirror of one and the other,
reflection positivity fails** — at that mass, with no further hypothesis on the graph.

## What this says about `StepGraphSmallMass`

That file's graph fails for exactly this reason, and `stepGraph_not_reflectionPositive_general`
re-derives its conclusion from the general statement. The hand computation is not wasted: it is now
a check on the general proof, by a route that shares only the graph.

**And it says what the failure is NOT.** It is a statement about *disconnection*, and a connected
graph satisfies its hypotheses nowhere — a reflection cannot move a site out of a component there.
So this closes off a family from the wall's remaining question rather than moving the question, and
`WALLS` §W1.2's fold-back says so in the same terms.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace GreenDisconnected

open Matrix GraphLaplacian GraphReflection GraphMirrorReflection

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The operator has no entry between components -/

/-- Vertices in different components are neither equal nor adjacent, so the massive operator's
entry between them is zero. -/
theorem massive_eq_zero_of_not_reachable {p q : V} (h : ¬ G.Reachable p q) :
    massive G m p q = 0 := by
  rw [massive_apply]
  have hne : p ≠ q := fun hpq => h (hpq ▸ SimpleGraph.Reachable.refl p)
  have hadj : ¬ G.Adj p q := fun ha => h ha.reachable
  simp [hne, hadj]

/-! ## 2. And neither does its inverse -/

/-- **THE PROPAGATOR VANISHES BETWEEN COMPONENTS.** The complement of
`GraphGreenPositive.green_pos`, which needs the graph connected; this needs nothing. -/
theorem green_eq_zero_of_not_reachable (hm : m ≠ 0) {p q : V} (h : ¬ G.Reachable p q) :
    green G m p q = 0 := by
  classical
  set x : V → ℝ := fun r => if G.Reachable p r then 0 else green G m r p with hxdef
  have hzero : massive G m *ᵥ x = 0 := by
    funext s
    simp only [Pi.zero_apply, Matrix.mulVec, dotProduct]
    by_cases hs : G.Reachable p s
    · -- every surviving term has `r` in another component from `s`
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : G.Reachable p r
      · simp [hxdef, hr]
      · have : ¬ G.Reachable s r := fun hsr => hr (hs.trans hsr)
        rw [massive_eq_zero_of_not_reachable G this, zero_mul]
    · -- the dropped terms are exactly the zero ones, so the sum is the full one
      have hfull : ∑ r, massive G m s r * green G m r p = 0 := by
        have hid := congrFun (congrFun (green_mul_massive (G := G) hm) p) s
        rw [Matrix.mul_apply] at hid
        have hps : p ≠ s := fun hh => hs (hh ▸ SimpleGraph.Reachable.refl p)
        rw [Matrix.one_apply_ne hps] at hid
        rw [← hid]
        refine Finset.sum_congr rfl fun r _ => ?_
        have h1 : massive G m s r = massive G m r s := (massive_isSymm G m).apply r s
        have h2 : green G m r p = green G m p r := (green_isSymm G hm).apply p r
        rw [h1, h2, mul_comm]
      rw [← hfull]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : G.Reachable p r
      · have : ¬ G.Reachable s r := fun hsr => hs (hr.trans hsr.symm)
        rw [massive_eq_zero_of_not_reachable G this, zero_mul, zero_mul]
      · simp [hxdef, hr]
  have hpd := massive_posDef (G := G) (m := m) hm
  by_contra hne
  have hx : x ≠ 0 := by
    intro hx0
    have hqp : green G m q p = 0 := by simpa [hxdef, h] using congrFun hx0 q
    exact hne (((green_isSymm G hm).apply q p).trans hqp)
  have := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hx
  rw [hzero] at this
  simp at this

/-! ## 3. What that costs reflection positivity -/

variable {θ : V ≃ V} {H Mir : Finset V}

/-- **A ZERO DIAGONAL IS FATAL UNLESS THE WHOLE THING IS ZERO.** If the reflected form's matrix
vanishes on the diagonal at two half-sites and not between them, one of `e_p ± e_q` makes the form
negative. -/
theorem not_reflectionPositive_of_zero_diag {p q : V} (hp : p ∈ H) (hq : q ∈ H)
    (hpp : green G m (θ p) p = 0) (hqq : green G m (θ q) q = 0)
    (hpq : green G m (θ p) q + green G m (θ q) p ≠ 0) :
    ¬ GraphReflection.ReflectionPositive G m θ H := by
  classical
  have hne' : p ≠ q := by
    rintro rfl
    rw [hpp] at hpq
    simp at hpq
  set S : ℝ := green G m (θ p) q + green G m (θ q) p with hSdef
  set ε : ℝ := if 0 < S then -1 else 1 with hεdef
  set c : V → ℝ := fun r => if r = p then 1 else if r = q then ε else 0 with hcdef
  intro hRP
  have hcs : ∀ r, r ∉ H → c r = 0 := by
    intro r hr
    rw [hcdef]
    have h1 : r ≠ p := fun h => hr (h ▸ hp)
    have h2 : r ≠ q := fun h => hr (h ▸ hq)
    simp [h1, h2]
  have hval := hRP c hcs
  have hzero : ∀ r, r ≠ p → r ≠ q → c r = 0 := by
    intro r h1 h2; simp [hcdef, h1, h2]
  have hexp : ∀ f : V → V → ℝ, (∑ r, ∑ t, c r * c t * f r t)
      = f p p + ε * f p q + ε * f q p + ε * ε * f q q := by
    intro f
    have inner : ∀ r, (∑ t, c r * c t * f r t) = c r * f r p + c r * ε * f r q := by
      intro r
      rw [Finset.sum_eq_add_of_mem p q (Finset.mem_univ p) (Finset.mem_univ q) hne'
        (fun t _ h => by rw [hzero t h.1 h.2]; ring)]
      simp [hcdef, hne'.symm]
    rw [Finset.sum_congr rfl fun r _ => inner r,
      Finset.sum_eq_add_of_mem p q (Finset.mem_univ p) (Finset.mem_univ q) hne'
        (fun t _ h => by rw [hzero t h.1 h.2]; ring)]
    simp [hcdef, hne'.symm]
    ring
  rw [hexp (fun r t => green G m (θ r) t), hpp, hqq] at hval
  rcases lt_trichotomy S 0 with hS | hS | hS
  · have : ε = 1 := by rw [hεdef, if_neg (by linarith)]
    rw [this] at hval
    rw [hSdef] at hS
    linarith
  · exact hpq (by rw [hSdef] at hS; exact hS)
  · have : ε = -1 := by rw [hεdef, if_pos hS]
    rw [this] at hval
    rw [hSdef] at hS
    linarith

/-! ## 4. And the six-vertex instance, re-derived from the general statement

`StepGraphSmallMass` proved its graph not reflection positive by three linear equations per
vanishing entry. Everything it needed is an instance of §§2–3, and the only extra ingredient is a
reason the two paths are separate components — here a parity invariant, since every edge of
`stepGraph` joins two sites of the same parity.

**The hand computation is not superseded, it is spent as a check.** `green_three_zero` and
`green_four_one` are re-proved below by a route sharing nothing with theirs, and
`stepGraph_two_routes_agree` states the agreement.
-/

section StepGraph

open GreenLargeMass

/-- Every edge of `stepGraph` joins two sites of the same parity: the edges are `{0,2}`, `{0,4}`,
`{1,3}`, `{3,5}`. -/
theorem stepGraph_adj_parity (u v : Fin 6) (h : stepGraph.Adj u v) : u.val % 2 = v.val % 2 := by
  revert h; revert u v; decide

/-- Hence reachability preserves parity, and the two paths are different components. -/
theorem stepGraph_reachable_parity {u v : Fin 6} (h : stepGraph.Reachable u v) :
    u.val % 2 = v.val % 2 := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hadj _ ih => exact (stepGraph_adj_parity _ _ hadj).trans ih

theorem stepGraph_not_reachable_three_zero : ¬ stepGraph.Reachable 3 0 := by
  intro h
  have := stepGraph_reachable_parity h
  simp at this

theorem stepGraph_not_reachable_four_one : ¬ stepGraph.Reachable 4 1 := by
  intro h
  have := stepGraph_reachable_parity h
  simp at this

/-- `green 3 0 = 0`, from the general theorem rather than from three linear equations. -/
theorem stepGraph_green_three_zero (hm : m ≠ 0) :
    GraphLaplacian.green stepGraph m 3 0 = 0 :=
  green_eq_zero_of_not_reachable stepGraph hm stepGraph_not_reachable_three_zero

/-- `green 4 1 = 0`, likewise. -/
theorem stepGraph_green_four_one (hm : m ≠ 0) :
    GraphLaplacian.green stepGraph m 4 1 = 0 :=
  green_eq_zero_of_not_reachable stepGraph hm stepGraph_not_reachable_four_one

/-- **AND THE TWO ROUTES AGREE.** `StepGraphSmallMass.green_three_zero` gets the same value from
three entries of `green · massive = 1`; this gets it from positive definiteness and a parity
invariant. Nothing is shared but the graph. -/
theorem stepGraph_two_routes_agree (hm : m ≠ 0) :
    GraphLaplacian.green stepGraph m 3 0 = 0 ∧ GraphLaplacian.green stepGraph m 3 0 = 0 :=
  ⟨stepGraph_green_three_zero hm, StepGraphSmallMass.green_three_zero hm⟩

/-- **THE CONCLUSION, FROM THE GENERAL CRITERION.** `StepGraphSmallMass.stepGraph_not_reflection
Positive` says the same thing; this derives it from §§2–3 with the graph appearing only through a
parity invariant and one strictly positive entry. -/
theorem stepGraph_not_reflectionPositive_general (hm : m ≠ 0) :
    ¬ GraphReflection.ReflectionPositive stepGraph m sigma6 Hs := by
  refine not_reflectionPositive_of_zero_diag stepGraph (θ := sigma6) (H := Hs)
    (p := 0) (q := 1) (by decide) (by decide) ?_ ?_ ?_
  · rw [show sigma6 0 = 3 from rfl]; exact stepGraph_green_three_zero hm
  · rw [show sigma6 1 = 4 from rfl]; exact stepGraph_green_four_one hm
  · rw [show sigma6 0 = 3 from rfl, show sigma6 1 = 4 from rfl]
    have h1 : 0 ≤ GraphLaplacian.green stepGraph m 3 1 :=
      GraphGreenPositive.green_nonneg stepGraph hm 3 1
    have h2 : 0 < GraphLaplacian.green stepGraph m 4 0 :=
      StepGraphSmallMass.green_four_zero_pos hm
    positivity

end StepGraph

/-! ## 5. And the two halves are one biconditional, with the connectedness hypothesis gone

`GraphGreenPositive.green_pos` says the propagator is strictly positive **on a connected graph**.
§2 says it is zero between components. Neither is the sharp statement, which needs no hypothesis on
the graph at all:

**`green_pos_iff_reachable`: `0 < green p q` if and only if `q` is reachable from `p`.**

`green_pos` is the case where every pair is reachable, and §2 is the other direction; the
connectedness hypothesis was doing nothing except making "reachable" trivially true.

The forward half is §2 in contrapositive. The reverse half re-runs `green_pos`'s own walk
induction, whose adjacency step is `private` in that file and is therefore re-derived here from
public API — `massive_mulVec_apply`, `green_nonneg` and `green_diag_pos`, with
`massive · green = 1` obtained from `green · massive = 1` by `Matrix.mul_eq_one_comm`.
-/

section Sharp

/-- The zero set of a column is closed under adjacency. `GraphGreenPositive` proves this and keeps
it `private`; the statement is re-derived rather than the file edited. -/
theorem green_zero_adj_of_pub (hm : m ≠ 0) (q : V) {s : V} (hs : green G m s q = 0)
    {r : V} (hadj : G.Adj s r) : green G m r q = 0 := by
  have hsq : s ≠ q := fun hc => by
    rw [hc] at hs; exact absurd hs (ne_of_gt (green_diag_pos G hm q))
  have hmg : massive G m * green G m = 1 :=
    mul_eq_one_comm.mp (green_mul_massive (G := G) hm)
  have hval : (massive G m *ᵥ fun u => green G m u q) s = 0 := by
    have := congrFun (congrFun hmg s) q
    rw [Matrix.mul_apply] at this
    rw [Matrix.mulVec, dotProduct, this, Matrix.one_apply_ne hsq]
  rw [GraphGreenPositive.massive_mulVec_apply, hs, mul_zero, zero_sub, neg_eq_zero] at hval
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun u _ => GraphGreenPositive.green_nonneg G hm u q)).mp hval r
    ((SimpleGraph.mem_neighborFinset _ _ _).mpr hadj)

/-- **THE SHARP STATEMENT.** No connectedness hypothesis: the propagator is strictly positive
exactly between vertices joined by a path. -/
theorem green_pos_iff_reachable (hm : m ≠ 0) (p q : V) :
    0 < green G m p q ↔ G.Reachable p q := by
  constructor
  · intro hpos
    by_contra hr
    rw [green_eq_zero_of_not_reachable G hm hr] at hpos
    exact lt_irrefl 0 hpos
  · intro hr
    rcases lt_or_eq_of_le (GraphGreenPositive.green_nonneg G hm p q) with hlt | heq
    · exact hlt
    · exfalso
      have hwalk : ∀ {a b : V}, G.Walk a b → green G m a q = 0 → green G m b q = 0 := by
        intro a b w
        induction w with
        | nil => exact id
        | cons hadj _ ih => exact fun ha => ih (green_zero_adj_of_pub G hm q ha hadj)
      obtain ⟨w⟩ := hr
      exact absurd (hwalk w heq.symm) (ne_of_gt (green_diag_pos G hm q))

/-- **AND `GraphGreenPositive.green_pos` IS THE SPECIAL CASE**, re-derived here so the
generalisation is checked against the theorem it generalises rather than asserted to contain it. -/
theorem green_pos_of_connected (hG : G.Connected) (hm : m ≠ 0) (p q : V) :
    0 < green G m p q :=
  (green_pos_iff_reachable G hm p q).mpr (hG.preconnected p q)

end Sharp

end GreenDisconnected
