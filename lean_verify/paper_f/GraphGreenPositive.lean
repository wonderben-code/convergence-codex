/-
  GraphGreenPositive.lean — the propagator has no negative entries, and on a
  connected graph no zero ones either.

  WHY. `UNLOCK_WATCHLIST` records two routes to W1. Route two is "`green` is
  entrywise non-negative", identified as **the bottom rung** by
  `LatticeReflection.reflectionPositive_singleton_iff`: on a one-site half,
  reflection positivity IS non-negativity of one propagator entry, so any
  attack on the general statement has to prove this first. The watchlist
  costed it at "one to two units of normed-ring plumbing" — a Neumann series
  `(1 − N)⁻¹ = ∑ Nᵏ`, needing the scoped `Matrix.linftyOp` instances and a
  passage from a `tsum` of matrices to a `tsum` of entries.

  **THE COSTING WAS RIGHT ABOUT THE SERIES AND WRONG AS A COSTING OF THE
  ROUTE.** The series does need that plumbing; the route did not need the
  series. The consequence it was wanted for follows from a discrete maximum
  principle in half a page, with no series, no norms and no analysis. See
  §6.

  WHAT THIS FILE PROVES, for an arbitrary finite simple graph:
  1. **`nonneg_of_mulVec_nonneg`** — the maximum principle. If
     `(−Δ_G + m²)x ≥ 0` pointwise then `x ≥ 0`. One line of arithmetic at the
     site where `x` is smallest.
  2. **`green_nonneg`** — hence **the propagator has no negative entries**,
     on every finite simple graph and every `m ≠ 0`.
  3. **`green_pos`** — and on a CONNECTED graph, no zero entries either:
     `0 < green G m p q` for all `p, q`. The strong principle: the zero set of
     a column is closed under adjacency, so it is empty or everything, and
     `green_diag_pos` rules out everything.
  4. **`twoPoint_nonneg`, `twoPoint_pos`** — so the Gaussian field of a
     connected graph is **strictly positively correlated at every pair of
     sites**, which is the physical reading.
  5. **`reflectionPositive_singleton`** — every singleton half of the box is
     reflection-positive. `LatticeReflection.exists_reflectionPositive_singleton`
     produced one such half on odd boxes; this upgrades ∃ to ∀ on every box,
     which is a previous unit's result strengthened rather than restated.
  6. **`reflectionPositive_of_nonneg`** — and the reflected form is
     non-negative for every NON-NEGATIVE coefficient vector, on the whole
     box, with no support condition at all. **So what `ReflectionPositive`
     still asks for, and all it still asks for, is the sign-changing
     vectors.** That is the sharpest available statement of what is missing.

  WHAT THIS DOES NOT DO. **It is not reflection positivity and does not
  imply it.** `ReflectionPositive` quantifies over coefficient vectors `c` of
  ARBITRARY SIGN supported on a half; a kernel with non-negative entries says
  nothing about `∑ c_p c_q K(θp, q)` when the `c` may be negative. The
  singleton case falls only because `c_p·c_p ≥ 0` there. **W1's failing step
  is untouched.**

  Nor is this the random-walk representation. The route was named for the
  series; what is proved here is the CONSEQUENCE the series was wanted for.
  If a later step needs the expansion itself, it is still absent.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import BoxGraph
import LatticeReflection

namespace GraphGreenPositive

open MeasureTheory ProbabilityTheory Matrix Finset GraphLaplacian

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. What the massive operator does to a vector -/

/-- `(−Δ_G + m²)x` at a site: the mass-shifted degree times the value there,
    less the sum over neighbours. Everything below is this identity plus the
    observation that at a minimum the subtracted sum is too big. -/
theorem massive_mulVec_apply (m : ℝ) (x : V → ℝ) (p : V) :
    (massive G m *ᵥ x) p
      = ((G.degree p : ℝ) + m ^ 2) * x p - ∑ u ∈ G.neighborFinset p, x u := by
  rw [massive, Matrix.add_mulVec]
  simp only [Pi.add_apply, SimpleGraph.lapMatrix_mulVec_apply, Matrix.mulVec_diagonal]
  ring

/-! ## 2. The discrete maximum principle -/

/-- **THE MAXIMUM PRINCIPLE.** If `(−Δ_G + m²)x` is pointwise non-negative
    then so is `x`.

    The whole proof is one site. Let `p₀` minimise `x`. Every neighbour of
    `p₀` has `x ≥ x p₀`, so the neighbour sum is at least `deg p₀ · x p₀`,
    and §1 gives `0 ≤ (massive x) p₀ ≤ m²·x p₀`. With `m ≠ 0` that forces
    `x p₀ ≥ 0`, and `p₀` was the minimum. **The mass is doing real work: at
    `m = 0` the bound degenerates to `0 ≤ 0` and says nothing**, which is
    correct, since the massless operator is singular. -/
theorem nonneg_of_mulVec_nonneg {m : ℝ} (hm : m ≠ 0) {x : V → ℝ}
    (h : ∀ p, 0 ≤ (massive G m *ᵥ x) p) : ∀ p, 0 ≤ x p := by
  rcases isEmpty_or_nonempty V with hV | hV
  · exact fun p => (IsEmpty.false p).elim
  · obtain ⟨p₀, -, hmin⟩ :=
      Finset.exists_min_image Finset.univ x Finset.univ_nonempty
    have hdeg : ((G.degree p₀ : ℝ)) * x p₀ ≤ ∑ u ∈ G.neighborFinset p₀, x u := by
      calc ((G.degree p₀ : ℝ)) * x p₀
          = ∑ _u ∈ G.neighborFinset p₀, x p₀ := by
            rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
              nsmul_eq_mul]
        _ ≤ ∑ u ∈ G.neighborFinset p₀, x u :=
            Finset.sum_le_sum fun u _ => hmin u (Finset.mem_univ u)
    have hkey := h p₀
    rw [massive_mulVec_apply] at hkey
    have hm2 : (0:ℝ) < m ^ 2 := by positivity
    have hx0 : 0 ≤ x p₀ := by nlinarith
    exact fun p => le_trans hx0 (hmin p (Finset.mem_univ p))

/-! ## 3. The propagator -/

/-- A column of the propagator, as a vector. -/
private theorem massive_mulVec_green {m : ℝ} (hm : m ≠ 0) (q r : V) :
    (massive G m *ᵥ (fun s => green G m s q)) r = if r = q then 1 else 0 := by
  have hunit : IsUnit (massive G m).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (massive_isUnit G hm)
  have hmul : massive G m * green G m = 1 := Matrix.mul_nonsing_inv _ hunit
  have hcol : (massive G m *ᵥ (fun s => green G m s q)) r
      = (massive G m * green G m) r q := by
    simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]
  rw [hcol, hmul, Matrix.one_apply]

/-- **THE PROPAGATOR HAS NO NEGATIVE ENTRIES**, on every finite simple graph
    and every nonzero mass. This is the bottom rung
    `LatticeReflection.reflectionPositive_singleton_iff` named. -/
theorem green_nonneg {m : ℝ} (hm : m ≠ 0) (p q : V) : 0 ≤ green G m p q :=
  nonneg_of_mulVec_nonneg G hm
    (fun r => by rw [massive_mulVec_green G hm]; split_ifs <;> norm_num) p

/-- The zero set of a column of the propagator is closed under adjacency.

    At a site `s` where the column vanishes, §1 reads
    `0 = (massive x) s = −∑_{r ~ s} x r`, and the summands are non-negative
    by §3, so every neighbour vanishes too. The case `s = q` cannot occur,
    because the diagonal entry is strictly positive. -/
private theorem green_zero_adj {m : ℝ} (hm : m ≠ 0) (q : V) {s : V}
    (hs : green G m s q = 0) {r : V} (hadj : G.Adj s r) : green G m r q = 0 := by
  have hsq : s ≠ q := fun hc => by
    rw [hc] at hs; exact absurd hs (ne_of_gt (green_diag_pos G hm q))
  have hval := massive_mulVec_green G hm q s
  rw [if_neg hsq, massive_mulVec_apply, hs] at hval
  have hsum : ∑ u ∈ G.neighborFinset s, green G m u q = 0 := by linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg
    (fun u _ => green_nonneg G hm u q)).mp hsum
  exact this r ((SimpleGraph.mem_neighborFinset _ _ _).mpr hadj)

/-- **AND ON A CONNECTED GRAPH THE PROPAGATOR IS STRICTLY POSITIVE
    EVERYWHERE.** The strong maximum principle: a column's zero set is closed
    under adjacency, hence — on a connected graph — is empty or everything,
    and `green_diag_pos` rules out everything.

    This is the statement one would otherwise extract from the random-walk
    expansion, where positivity of `green p q` comes from the existence of a
    path from `p` to `q`. Here the path is used directly, and no series is
    summed. -/
theorem green_pos (hG : G.Connected) {m : ℝ} (hm : m ≠ 0) (p q : V) :
    0 < green G m p q := by
  rcases lt_or_eq_of_le (green_nonneg G hm p q) with hlt | heq
  · exact hlt
  · exfalso
    have hzero : green G m p q = 0 := heq.symm
    have hwalk : ∀ {a b : V}, G.Walk a b → green G m a q = 0 → green G m b q = 0 := by
      intro a b w
      induction w with
      | nil => exact id
      | cons hadj _ ih => exact fun ha => ih (green_zero_adj G hm q ha hadj)
    obtain ⟨w⟩ := hG.preconnected p q
    exact absurd (hwalk w hzero) (ne_of_gt (green_diag_pos G hm q))

/-! ## 4. What it says about the field -/

theorem twoPoint_nonneg {m : ℝ} (hm : m ≠ 0) (p q : V) :
    0 ≤ ∫ ω, ω p * ω q ∂(gaussianField G m) := by
  rw [GraphLaplacian.twoPoint G hm p q]
  exact green_nonneg G hm p q

/-- **THE GAUSSIAN FIELD OF A CONNECTED GRAPH IS STRICTLY POSITIVELY
    CORRELATED AT EVERY PAIR OF SITES.** Not only at coincident sites, which
    is `twoPoint_diag_pos` and is just non-degeneracy — at every pair,
    however far apart. -/
theorem twoPoint_pos (hG : G.Connected) {m : ℝ} (hm : m ≠ 0) (p q : V) :
    0 < ∫ ω, ω p * ω q ∂(gaussianField G m) := by
  rw [GraphLaplacian.twoPoint G hm p q]
  exact green_pos G hG hm p q

/-! ## 5. The box, four dimensions, and one rung of W1's ladder -/

section Box

open IsingFiniteVolume IsingContourSeparation LatticeReflection

theorem lattice_green_pos (n : ℕ) (hn : 0 < n) {m : ℝ} (hm : m ≠ 0)
    (p q : IsingFiniteVolume.Site n) : 0 < LatticeLaplacian.green n m p q := by
  rw [GraphLaplacian.green_box]
  exact green_pos _ (latticeGraph_connected hn) hm p q

/-- **EVERY SINGLETON HALF OF THE BOX IS REFLECTION-POSITIVE.**

    `LatticeReflection.exists_reflectionPositive_singleton` could only produce
    ONE such half, and only on odd boxes, by exhibiting a site the reflection
    fixes — where the criterion reduces to the strictly positive DIAGONAL
    entry. The off-diagonal entry `green (refl p) p` was exactly what was
    missing, and §3 supplies it. **∃ on odd boxes becomes ∀ on every box.** -/
theorem reflectionPositive_singleton (n : ℕ) (hn : 0 < n) {m : ℝ} (hm : m ≠ 0)
    (p : IsingFiniteVolume.Site n) : ReflectionPositive n m {p} :=
  (reflectionPositive_singleton_iff n m p).mpr
    (le_of_lt (lattice_green_pos n hn hm _ p))

/-- **THE REFLECTED FORM IS NON-NEGATIVE ON NON-NEGATIVE COEFFICIENTS**, on
    the whole box and with no support condition: every term is a product of
    three non-negative numbers. **This says exactly what `ReflectionPositive`
    has left to prove — the sign-changing coefficient vectors, and nothing
    else.** Compare `reflectionPositive_singleton`, which is the case of a
    vector supported at one site, where the sign cannot change. -/
theorem reflectionPositive_of_nonneg (n : ℕ) (hn : 0 < n) {m : ℝ} (hm : m ≠ 0)
    {c : IsingFiniteVolume.Site n → ℝ} (hc : ∀ p, 0 ≤ c p) :
    0 ≤ ∑ p, ∑ q, c p * c q * LatticeLaplacian.green n m (refl n p) q :=
  Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ =>
    mul_nonneg (mul_nonneg (hc p) (hc q))
      (le_of_lt (lattice_green_pos n hn hm _ q))

theorem green4_pos (n : ℕ) (hn : 0 < n) {m : ℝ} (hm : m ≠ 0)
    (p q : BoxGraph.Site 4 n) : 0 < BoxGraph.green4 n m p q :=
  green_pos _ (BoxGraph.boxGraph_connected 4 hn) hm p q

/-- The four-dimensional lattice field is strictly positively correlated. -/
theorem twoPoint4_pos (n : ℕ) (hn : 0 < n) {m : ℝ} (hm : m ≠ 0)
    (p q : BoxGraph.Site 4 n) : 0 < ∫ ω, ω p * ω q ∂(BoxGraph.field4 n m) :=
  twoPoint_pos _ (BoxGraph.boxGraph_connected 4 hn) hm p q

end Box

/-! ## 6. Review round 77 — the ways this could be hollow

**"A costing was corrected, so state it plainly."** `UNLOCK_WATCHLIST` costed
this at "one to two units of normed-ring plumbing", naming the scoped
`Matrix.linftyOp` instances and the `tsum`-of-matrices problem. **None of that
was needed and none of it appears here.** The maximum principle is finite,
algebraic and about half a page; the analysis in the costing was for the
random-walk SERIES, and what the route actually wanted was the series'
consequence. That is the ERRATUM 54 shape — a probe costing work the estate
could do more cheaply — and it is recorded rather than quietly benefited
from. **What is NOT corrected is the claim that the series itself is absent**:
it is, and if some later step needs the expansion rather than its
consequence, the plumbing is still to be done.

**"§3 could be claimed as W1."** It is one rung and the header says which.
`ReflectionPositive` quantifies over coefficient vectors of ARBITRARY SIGN
supported on a half. Non-negative kernel entries give nothing about
`∑_{p,q} c_p c_q K(θp, q)` when the `c` may be negative — the singleton case
falls only because there `c_p · c_p ≥ 0`, and that is exactly why
`reflectionPositive_singleton_iff` was a criterion about ONE entry.
**W1's failing step is where it was**, and
`reflectionPositive_of_nonneg` says precisely how much of it: the whole
remaining content is the sign-changing vectors.

**"§5 could be restating a previous unit."** It strengthens one, which is
the difference. `exists_reflectionPositive_singleton` produced a single half
on odd boxes, by finding a site the reflection FIXES so that the criterion
reduced to the diagonal — and that unit's own review flagged the result as
thin for exactly this reason. The off-diagonal entry was the gap; `green_pos`
closes it, so the statement becomes universal and needs no parity. **The
previous unit is not edited and its theorems still say what they said.**

**"`green_pos` could need connectivity it does not have."** It needs
`G.Connected` and takes it as a hypothesis; `green_nonneg` does not and does
not. On a disconnected graph `green p q` genuinely IS zero for `p` and `q` in
different components — the propagator does not propagate across a gap — so
the hypothesis is not technical, and the two theorems are separate on
purpose. `latticeGraph_connected` and `BoxGraph.boxGraph_connected` discharge
it for the boxes.

**"The mass hypothesis could be hiding something."** It is where the proof
lives. The maximum-principle inequality ends at `0 ≤ m²·x p₀`; at `m = 0`
that is `0 ≤ 0` and concludes nothing, which is correct rather than a defect,
since `GraphLaplacian.lapMatrix_not_posDef` says the massless operator is
singular and has no inverse to be non-negative.

**"`twoPoint_pos` could be an artefact of the Gaussian construction."** It is
a statement about the measure, obtained from `GraphLaplacian.twoPoint`, which
identifies `∫ ω_p ω_q` with the propagator entry. Positive correlation at
COINCIDENT sites is `twoPoint_diag_pos` and is merely non-degeneracy; the
content here is that it holds at every pair, however far apart, which is a
statement no positive-definiteness argument gives — a positive-definite
kernel can have negative off-diagonal entries.
-/

end GraphGreenPositive
