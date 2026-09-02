import RemainderFormBound
import GreenExpansion

/-!
# W1's failing step without the regularity hypothesis

`GreenExpansion.reflectionPositive_iff_remainder` is the theorem `WALLS.md`'s W1 uses to state its
own gap: reflection positivity at `c` holds **exactly** when the remainder dominates the cross form.
It carries `hd : G.IsRegularOfDegree d`, and the regularity is not decoration — the proof runs
through `sq_smul_green`, an identity in which the scalar `s = d + m²` appears because every degree
is the same number.

`PROOF_STRATEGY` §7 rule 3 — *"take a result already proven under restrictive hypotheses and remove
one"*. This file removes that one.

**THE GENERAL IDENTITY WAS ALREADY THERE AND NOTHING HAD RUN THE CHAIN THROUGH IT.**
`GreenExpansion.green_eq_two_terms` is `sq_smul_green` at an arbitrary graph, with the diagonal
matrix `Dinv` in place of the scalar `s⁻¹`. Substituting it costs three things and no new
mathematics:

**⚠ THE HEADING ABOVE IS FALSE AND IS KEPT AS WRITTEN** (`ERRATUM 94`, `ERRATUM 427`).
**`GreenLargeMass.lean` §General ran this chain through `green_eq_two_terms` before this file
existed** — `Dinv_adj_Dinv_apply`, `green_mirror_general`, the split of the reflected form at an
arbitrary graph, and `reflectedForm_neg_of_crossForm_pos_general`. The clause is an absence claim
asserted without a probe, in a session that spent three hours re-probing other people's. **What
survives here**: the criterion as a named **iff** (§General has the split inline and the one-way
inequality, not the biconditional), and §4's `crossForm_smul` /
`crossForm_general_eq_of_regular`. `paper_f/ReflectionFailureSharper.lean` folds it back by proving
more.

* `Dinv` is diagonal, so at a **mirrored** entry `(θ p, q)` with `p, q ∈ H` its own term vanishes
  (`GreenExpansion.mirror_ne`) and the middle term is the adjacency entry with a weight on each
  side — `Matrix.diagonal_mul` and `Matrix.mul_diagonal`, nothing else.
* Those weights are `(deg + m²)⁻¹` at `θ p` and at `q`, and **`GraphReflection.IsRefl.degree` makes
  the first of them a weight at `p`** — a reflection preserves degrees, which is the fact that lets
  the two weights be absorbed into the vector.
* So the cross form appears **at the reweighted vector** `fun v => c v * invDeg G m v` rather than
  at `c`. On a regular graph the weight is a constant and `crossForm_smul` pulls it out squared,
  which is exactly the `s²` the old statement multiplies by — **§4 proves that, so the claim that
  this generalises the old theorem is checked and not asserted.**

**AND THE GENERAL STATEMENT IS CLEANER, WHICH IS WORTH SAYING BECAUSE IT IS UNUSUAL.** The old form
needs `hs : 0 < ((d : ℝ) + m ^ 2) ^ 2` to divide by; **the general one multiplies by nothing and
needs no such hypothesis.** Two hypotheses come off, not one.

**WHAT THIS IS NOT — W1 DOES NOT MOVE, AND THIS IS THE SEVENTH TIME TODAY.** The theorem is a
restatement of when reflection positivity holds, exactly as the regular one is; **no inequality is
proved and no cross form is estimated.** What it changes is the class of graphs on which the wall's
own statement of its gap is available, from regular graphs to all of them. The remainder it names,
`green · A · Dinv · A · Dinv`, is the one `NeumannTailBound` and `RemainderFormBound` bound — so the
day's bounds and the wall's statement now live at the same generality, which they did not this
morning. **Nothing here compares them**, and the missing object is unchanged: a lower bound on the
cross form. Not attempted, not costed (`ERRATUM 246`), not estimated (`ERRATUM 183`).

**`GreenExpansion.reflectionPositive_iff_remainder` IS KEPT AND NOT DELETED** (`ERRATUM 94`,
`ERRATUM 201`): it is the statement `WALLS.md` quotes, its shape is the one a regular graph makes
natural, and a caller who has regularity should not be handed a reweighted vector. **No published
tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace ReflectionRemainderGeneral

open Matrix GraphLaplacian GraphReflection GraphMirrorReflection CrossFormMatrix GreenExpansion

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {θ : V ≃ V} {H Mir : Finset V} {m : ℝ}

/-! ## 1. The weight -/

/-- The diagonal entry of `GreenExpansion.Dinv`, as a function. -/
noncomputable def invDeg (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (v : V) : ℝ :=
  ((G.degree v : ℝ) + m ^ 2)⁻¹

theorem dinv_eq_diagonal : Dinv G m = Matrix.diagonal (invDeg G m) := rfl

omit [DecidableEq V] in
/-- **A REFLECTION PRESERVES THE WEIGHT**, because it preserves degrees
(`GraphReflection.IsRefl.degree`). This is what lets the two weights of the middle term be absorbed
into one reweighted vector. -/
theorem invDeg_mirror (h : IsRefl G θ) (p : V) : invDeg G m (θ p) = invDeg G m p := by
  rw [invDeg, invDeg, h.degree p]

/-! ## 2. The mirrored entry, at an arbitrary graph -/

/-- `Dinv · A · Dinv` at any entry: a weight, the adjacency entry, a weight. -/
theorem dinv_adj_dinv_apply (p q : V) :
    (Dinv G m * G.adjMatrix ℝ * Dinv G m) p q
      = invDeg G m p * (G.adjMatrix ℝ) p q * invDeg G m q := by
  rw [dinv_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- **THE GREEN FUNCTION AT A MIRRORED ENTRY, WITH NO REGULARITY.** `green_eq_two_terms` read at
`(θ p, q)` for `p, q ∈ H`: the diagonal term vanishes because `θ p ≠ q`, the middle term is the
cross-cut adjacency with a weight from each side, and the weight at `θ p` is the weight at `p`. -/
theorem green_mirror_eq (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    {p q : V} (hp : p ∈ H) (hq : q ∈ H) :
    green G m (θ p) q
      = invDeg G m p * crossAdj G θ p q * invDeg G m q
        + (green G m * G.adjMatrix ℝ * Dinv G m * G.adjMatrix ℝ * Dinv G m) (θ p) q := by
  have hne : θ p ≠ q := mirror_ne hM hp hq
  have h2 := congrFun (congrFun (green_eq_two_terms (G := G) (m := m) hm) (θ p)) q
  have hw : invDeg G m (θ p) = invDeg G m p := invDeg_mirror h p
  rw [Matrix.add_apply, Matrix.add_apply, dinv_eq_diagonal, Matrix.diagonal_apply_ne _ hne,
    ← dinv_eq_diagonal, zero_add, dinv_adj_dinv_apply, adjMatrix_mirror h p q, hw] at h2
  exact h2

/-! ## 3. The identity and the criterion -/

/-- **THE IDENTITY AT AN ARBITRARY GRAPH.** The reflected form is the negated cross form **at the
reweighted vector** plus the remainder. Nothing is multiplied through, so no positivity hypothesis
on a scalar appears. -/
theorem reflectedForm_eq_general (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    {c : V → ℝ} (hc : ∀ p, p ∉ H → c p = 0) :
    reflectedForm G m θ c
      = - crossForm G m θ H (fun v => c v * invDeg G m v)
        + ∑ p ∈ H, ∑ q ∈ H,
            c p * c q * (green G m * G.adjMatrix ℝ * Dinv G m * G.adjMatrix ℝ * Dinv G m)
              (θ p) q := by
  classical
  rw [reflectedForm_eq_sum_half hc, crossForm_eq_neg_adj hM m (fun v => c v * invDeg G m v),
    neg_neg, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [green_mirror_eq hM h hm hp hq, crossAdj]
  ring

/-- **W1's FAILING STEP, ON EVERY GRAPH.** Reflection positivity at `c` holds precisely when the
remainder dominates the cross form **at the reweighted vector**. This is a restatement and not an
inequality: nothing here estimates either side. -/
theorem reflectionPositive_iff_remainder_general (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hm : m ≠ 0) {c : V → ℝ} (hc : ∀ p, p ∉ H → c p = 0) :
    0 ≤ reflectedForm G m θ c ↔
      crossForm G m θ H (fun v => c v * invDeg G m v) ≤
        ∑ p ∈ H, ∑ q ∈ H,
          c p * c q * (green G m * G.adjMatrix ℝ * Dinv G m * G.adjMatrix ℝ * Dinv G m)
            (θ p) q := by
  rw [reflectedForm_eq_general hM h hm hc, ← sub_nonneg
    (a := ∑ p ∈ H, ∑ q ∈ H,
      c p * c q * (green G m * G.adjMatrix ℝ * Dinv G m * G.adjMatrix ℝ * Dinv G m) (θ p) q)]
  constructor
  · intro hx; linarith
  · intro hx; linarith

/-! ## 4. It contains the regular case, proved rather than asserted -/

/-- The cross form is quadratic in its vector, which is what turns a constant weight into the `s²`
the regular statement multiplies by. -/
theorem crossForm_smul (t : ℝ) (c : V → ℝ) :
    crossForm G m θ H (fun v => c v * t) = t ^ 2 * crossForm G m θ H c := by
  rw [crossForm, crossForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

omit [DecidableEq V] in
/-- **ON A REGULAR GRAPH THE WEIGHT IS A CONSTANT**, so the general criterion's left-hand side is
`(d + m²)⁻²` times the regular one's. The two statements are the same inequality scaled by a
positive number, which is what *"generalises"* has to mean here and is checked rather than said. -/
theorem invDeg_regular {d : ℕ} (hd : G.IsRegularOfDegree d) (v : V) :
    invDeg G m v = ((d : ℝ) + m ^ 2)⁻¹ := by
  rw [invDeg, hd v]

theorem crossForm_general_eq_of_regular {d : ℕ} (hd : G.IsRegularOfDegree d) (c : V → ℝ) :
    crossForm G m θ H (fun v => c v * invDeg G m v)
      = (((d : ℝ) + m ^ 2)⁻¹) ^ 2 * crossForm G m θ H c := by
  have hfun : (fun v => c v * invDeg G m v) = fun v => c v * ((d : ℝ) + m ^ 2)⁻¹ :=
    funext fun v => by rw [invDeg_regular (G := G) (m := m) hd v]
  rw [hfun, crossForm_smul]

end ReflectionRemainderGeneral
