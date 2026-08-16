import GreenLargeMass
import GreenDisconnected
import LatticeGeneratingFunctional
import BoxDegree
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# The propagator decays exponentially in the graph distance

The `UNLOCK_WATCHLIST` item for the OS axioms has carried the same trigger since 10 August
(`codex-internal` `a51c3a3`, dated by `git log -S`, not recalled):

> REVISIT WHEN: … someone wants coordinate permutations, or **OS4 — which needs a decay estimate
> the estate does not have for `gaussianField`.**

The coordinate-permutation half of that trigger was discharged on 13 August by
`LatticePointGroup`. **This is the other half**: the decay estimate exists now.

**The absence was checked, not assumed.** `paper_f` was grepped for `SimpleGraph.dist`, `G.dist`
and `maxDegree`: the first two returned **zero hits**, the third one hit and it is a comment in
`EvenDegreeCycle`. So no theorem here had previously said anything about a propagator entry as a
function of how far apart its two sites are — the graph distance was not a notion this estate
used. The `exponential decay` and `clustering` hits in `paper_f` are all in the axiomatic cascade
files, where the decay rate is a **structure field** (`CascadeData.gap_decay`) supplied by the
caller rather than a theorem about any concrete measure.

## What is delivered

`green_abs_le_pow_dist`: on **every** finite simple graph, at **every** nonzero mass, with `Δ` any
bound on the degrees,

    |green G m p q|  ≤  (Δ / (Δ + m²)) ^ (G.dist p q) · (m²)⁻¹

and the base `Δ/(Δ+m²)` is `< 1` whenever `m ≠ 0` (`decayRate_lt_one`), so the right-hand side
really does decay geometrically in the distance.

**The point of carrying `Δ` rather than the graph's own maximum degree is the box.** For
`boxGraph d n` the degree bound is `2d` at every side length (`BoxDegree.boxGraph_degree_le`), so
`boxGraph_green_abs_le` gives a decay rate **that does not depend on `n`**. That is the shape an
infinite-volume argument needs: a bound uniform in the volume, not merely one bound per volume.
`boxGraph_uniform` says it in the form the limit would use — for every `ε`, a distance `N` chosen
from `d`, `m` and `ε` **alone**, beyond which every propagator entry of every box is below `ε`.

`covariance_abs_le` and `twoPoint_abs_le` carry the estimate across to the field, in the two
vocabularies the estate uses for the same quantity.

## The proof, in one paragraph

Read one row of `massive · green = 1` at `p ≠ q`: `(deg p + m²) · green p q = ∑_{r ∼ p} green r q`
(`green_row_of_ne`). Every neighbour `r` of `p` is at distance `≥ dist p q − 1` from `q`, so if
every entry at distance `≥ k` is below `C`, then `|green p q| ≤ deg p/(deg p + m²) · C` for every
`p` at distance `≥ k+1`, and `t ↦ t/(t+m²)` is increasing, so the factor is at most
`Δ/(Δ + m²)`. Induct on `k`, starting from `GreenLargeMass.green_abs_le`. **No Neumann series and
no matrix powers**: the geometric factor comes out of the row identity one step at a time.

## What this is NOT

**It is not OS4.** OS4 is clustering of the Schwinger functions of a *continuum, infinite-volume*
theory: every correlation factorises as the separation grows, for all orders at once. Three things
are missing here and none is bookkeeping:

* **the infinite-volume limit** — the watchlist's *"infinite-volume limit along periodic boxes
  (W2's first leg)"*, open; `WALLS` W2 itself is the wider wall, *"the continuum field and OS
  reconstruction"*;
* **the higher correlation functions — SUPERSEDED THE SAME DAY, see the note after this list.**
  Gaussian ⇒ Wick would give them from the two-point function, and **a first draft of this
  sentence said Wick's theorem is not in this estate, which is false.**
  `paper_f/GaussianMeasure.lean` has `wick_pairing_identity`, `wick_pairing_expanded`,
  `wick_check_k1`–`k3` and `wick_pairings_table`. What those prove is the
  **counting** identity `(2k)! = 2^k · k! · (2k−1)‼` — arithmetic about factorials, with no
  measure, no field and no Gaussian anywhere in the statement. **The moment formula**
  `E[X₁⋯X_{2k}] = ∑_{pairings} ∏ E[Xᵢ Xⱼ]`, which is the half a clustering argument would consume,
  is the one that is absent;

  *AMENDED 16 AUGUST 2026 (`ERRATUM 185`). "~~is the one that is absent~~" is **withdrawn at
  `k = 2`**: `LatticeIsserlisFour.isserlis_four` (`4d35d08`) is exactly this formula at `2k = 4`,
  at four arbitrary test functions and all three pairings. Above that it is present only in
  patterns — `LatticeWickTwo.wick_two` gives order six at `(a,b,f,f,f,f)` — and **the closed
  pairing sum at general order really is still absent**, for the carrier reason
  `LatticeMomentsGeneral` records. The clause "which is the half a clustering argument would
  consume" **is not withdrawn and has since been demonstrated**: that is precisely what
  `LatticeFourPointClustering` and `LatticeHigherClustering` consume it for.*
* **the continuum.**

**THE SECOND BULLET IS SUPERSEDED BY `GreenClustering`, WRITTEN THE SAME DAY AND KEPT HERE RATHER
THAN SILENTLY EDITED.** Its route is not Wick: `LatticeGeneratingFunctional.generatingFunctional`
already packages every order at once, and an exponential of a quadratic factorises exactly, so
`GreenClustering.clustering` bounds `Z(f+g) − Z(f)Z(g)` for **all** test functions living `N` steps
apart, using this file's estimate on the cross term and nothing else. **What survives of the bullet
is narrower and still true**: no *individual* higher correlation is written down, because
extracting one means differentiating under the integral and the identity that comes out *is* Wick's
formula. So the generating functional clusters; extraction does not follow. The first and third
bullets are untouched.

*AMENDED 16 AUGUST 2026 (`ERRATUM 184`). The two sentences struck through above — "~~no
individual higher correlation is written down~~" and "~~extraction does not follow~~" — are
**withdrawn**. **The diagnosis was right and the verdict is now wrong.** Extracting one did
mean differentiating under the integral, and the identity that came out IS Wick's formula —
`LatticeWickRecursion.wick_recursion` (`214454a`). Individual higher correlations now exist
**at every order** and, since `LatticeHigherClustering` (`da0390a`), **they cluster**: in the
pattern `(a, f^(n+1))` the whole correlation decays geometrically, with nothing to subtract,
and across components it is exactly zero. **What is NOT withdrawn is everything else in this
paragraph** — this file still does not prove any of that, `OS4` is untouched, and the
generating-functional route recorded here remains what this file does.*


**No theorem in this file should be recorded as OS4**, and the watchlist item keeps `OS4` open.
What changes is the sentence *"needs a decay estimate the estate does not have"*: the estate has
one now, for the two-point function, uniform in the volume.

**One caveat about Mathlib's `dist` convention, stated because it makes a theorem here weaker than
it looks.** `SimpleGraph.dist p q = 0` when `q` is unreachable from `p`, so at such a pair this
file's bound degrades to `(m²)⁻¹` and says nothing. The sharp statement there is already proved
and is stronger than anything below: `GreenDisconnected.green_eq_zero_of_not_reachable` gives
`green p q = 0` outright.

**AND ON 15 AUG 2026 THE CAVEAT WAS ACTED ON, WHICH IT HAD NOT BEEN.** The paragraph above was
written the day this file was, and then three statements were written underneath it that it
applies to, without the connection being made. Two consequences, neither visible from the caveat
as first phrased:

* **`green_abs_le_pow`'s hypothesis `k ≤ G.dist p q` is UNSATISFIABLE for `k ≥ 1` at an
  unreachable pair.** So the inductive estimate was not merely weak there — it was *silent*, and
  a hypothesis that fails on an infimum over the empty set looks exactly like one that holds
  narrowly, which is why this survived a header paragraph explicitly about the convention.
  **Where that silence actually cost something, and where it did not, was checked rather than
  assumed** (`ERRATUM 165`, which withdraws the first version of this bullet): it bit
  `GreenClustering.cross_abs_le`, stated for an *arbitrary* graph; it did **not** bite
  `boxGraph_uniform`, because `BoxGraph.boxGraph_connected` proves the box connected for `0 < n`
  and there are no unreachable pairs to be silent about; and for
  `TorusDecay.torusGraph_uniform` **the estate proves no such thing** — grepped
  `boxGraph.*Connected\|torusGraph.*Connected` over `paper_f/*.lean`, which returns
  `boxGraph_connected` and no torus counterpart — so whether its silence is vacuous is not
  established here and is not assumed.
* `green_abs_le_pow_dist` reads the inductive estimate at `k = G.dist p q = 0`, so it *does*
  degrade to `(m²)⁻¹` rather than vanishing. That much the caveat said, and it is still true.

The hypothesis is now `¬ G.Reachable p q ∨ k ≤ G.dist p q`, the new branch is one line of
`GreenDisconnected.green_eq_zero_of_not_reachable`, and **nothing is weakened** — the old
hypothesis implies the new one, so every earlier instance still applies.

**And the field-level uniform statement, which did not exist in any form.**
`exists_dist_uniform_covariance` and `exists_dist_uniform_twoPoint` say the `ε` statement about
the two-point function of the Gaussian field rather than about `green`. The estate had the field
bound pointwise and general (`covariance_abs_le`) and the `ε` form only for the propagator, so a
consumer asking *"is there a uniform correlation bound"* — which is a question about the field —
had to assemble one. Added 15 Aug 2026.

**The other half of the same amendment: uniformity was being stated per family.** `Δ` is a
parameter of the rate, so the distance `N` at which the propagator drops below `ε` depends on
`Δ`, `m` and `ε` and on nothing else — not on the graph, not on its vertex type, not on the
volume. The estate said so in prose and stated it only for boxes (`boxGraph_uniform`) and for tori
(`TorusDecay.torusGraph_uniform`). **`exists_dist_uniform` now says it for an arbitrary finite
graph of bounded degree**, with `N` produced before the graph is mentioned, and `boxGraph_uniform`
is an instance of it. `TorusDecay` is a separate file and is left for a separate unit; until then
its version stands on its own proof.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace GreenDecay

open GraphLaplacian MeasureTheory ProbabilityTheory Matrix Finset

universe u

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. One row of `massive · green = 1`

`GraphGreenPositive` has this as a `private` column identity in `mulVec` form, used there only to
feed a positivity argument. What the induction below needs is the *row*, entrywise, with the
diagonal coefficient and the neighbour sum separated — so it is proved here rather than unsealed.
-/

/-- **THE ROW IDENTITY.** `(deg p + m²) · green p q = δ_{pq} + ∑_{r ∼ p} green r q`. -/
theorem green_row (hm : m ≠ 0) (p q : V) :
    ((G.degree p : ℝ) + m ^ 2) * green G m p q
      = (if p = q then (1 : ℝ) else 0) + ∑ r ∈ G.neighborFinset p, green G m r q := by
  have hunit : IsUnit (massive G m).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (massive_isUnit G hm)
  have hmul : massive G m * green G m = 1 := Matrix.mul_nonsing_inv _ hunit
  have h : ∑ r, massive G m p r * green G m r q = (if p = q then (1 : ℝ) else 0) := by
    have hpq := congrArg (fun M : Matrix V V ℝ => M p q) hmul
    simpa [Matrix.mul_apply, Matrix.one_apply] using hpq
  have hnbr : ∑ r ∈ G.neighborFinset p, green G m r q
      = ∑ r, (if G.Adj p r then green G m r q else 0) := by
    rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  simp only [massive_apply, sub_mul, ite_mul, zero_mul, one_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  rw [hnbr]
  linarith

/-- The off-diagonal row identity, which is the one the induction uses: at `p ≠ q` the propagator
at `p` is a **weighted average of its values at the neighbours of `p`**, with total weight
`deg p / (deg p + m²) < 1`. That deficit is the whole source of the decay. -/
theorem green_row_of_ne (hm : m ≠ 0) {p q : V} (hpq : p ≠ q) :
    ((G.degree p : ℝ) + m ^ 2) * green G m p q = ∑ r ∈ G.neighborFinset p, green G m r q := by
  rw [green_row hm p q, if_neg hpq, zero_add]

/-! ## 2. The rate -/

/-- **THE DECAY RATE** at degree bound `Δ` and mass `m`: `Δ / (Δ + m²)`. -/
noncomputable def decayRate (Δ : ℕ) (m : ℝ) : ℝ := (Δ : ℝ) / ((Δ : ℝ) + m ^ 2)

theorem decayRate_nonneg (Δ : ℕ) {m : ℝ} (hm : m ≠ 0) : 0 ≤ decayRate Δ m := by
  have hd : (0 : ℝ) < (Δ : ℝ) + m ^ 2 := by positivity
  exact div_nonneg (Nat.cast_nonneg Δ) hd.le

/-- **THE RATE IS STRICTLY LESS THAN ONE**, which is what makes the estimate a decay estimate
rather than a bound. The mass is exactly what buys it. -/
theorem decayRate_lt_one (Δ : ℕ) {m : ℝ} (hm : m ≠ 0) : decayRate Δ m < 1 := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hd : (0 : ℝ) < (Δ : ℝ) + m ^ 2 := by positivity
  rw [decayRate, div_lt_one hd]
  linarith

/-- `t ↦ t/(t+m²)` is increasing, so a larger degree bound is a weaker (larger) rate. This is the
step that lets one uniform `Δ` serve a whole family of graphs. -/
theorem decayRate_mono {d Δ : ℕ} (h : d ≤ Δ) {m : ℝ} (hm : m ≠ 0) :
    decayRate d m ≤ decayRate Δ m := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hd : (0 : ℝ) < (d : ℝ) + m ^ 2 := by positivity
  have hD : (0 : ℝ) < (Δ : ℝ) + m ^ 2 := by positivity
  have hle : (d : ℝ) ≤ (Δ : ℝ) := Nat.cast_le.mpr h
  rw [decayRate, decayRate, div_le_div_iff₀ hd hD]
  nlinarith

/-! ## 3. The induction

The statement is *"every entry at distance at least `k` is below `ρ^k/m²`"*, and it is proved by
induction on `k`. Reading it at `k = dist p q` gives the theorem.
-/

/-- **THE DECAY ESTIMATE, IN INDUCTIVE FORM.** -/
theorem green_abs_le_pow (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) :
    ∀ (k : ℕ) (p q : V), (¬ G.Reachable p q ∨ k ≤ G.dist p q) →
      |green G m p q| ≤ decayRate Δ m ^ k * (m ^ 2)⁻¹ := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  intro k
  induction k with
  | zero => intro p q _; simpa using GreenLargeMass.green_abs_le (G := G) hm p q
  | succ k ih =>
    intro p q hk'
    set C : ℝ := decayRate Δ m ^ k * (m ^ 2)⁻¹ with hC
    have hC0 : 0 ≤ C := by
      have := decayRate_nonneg Δ (m := m) hm
      positivity
    -- the branch the original statement could not reach: across components the entry is zero
    rcases hk' with hnr | hk
    · rw [GreenDisconnected.green_eq_zero_of_not_reachable G hm hnr, abs_zero]
      have := decayRate_nonneg Δ (m := m) hm
      positivity
    -- `dist p q ≥ k+1 > 0` forces `p ≠ q` and reachability
    have hpos : 0 < G.dist p q := lt_of_lt_of_le (Nat.succ_pos k) hk
    have hnz : ¬ (p = q ∨ ¬ G.Reachable p q) := by
      intro hcon
      exact absurd ((SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable).mpr hcon) hpos.ne'
    have hne : p ≠ q := fun h => hnz (Or.inl h)
    have hreach : G.Reachable p q := by
      by_contra hc; exact hnz (Or.inr hc)
    -- every neighbour of `p` is one step closer to `q` at best
    have hnb : ∀ r ∈ G.neighborFinset p, |green G m r q| ≤ C := by
      intro r hr
      have hadj : G.Adj p r := (SimpleGraph.mem_neighborFinset _ _ _).mp hr
      have hrq : G.Reachable r q := (hadj.symm.reachable).trans hreach
      obtain ⟨w, hw⟩ := hrq.exists_walk_length_eq_dist
      have hstep : G.dist p q ≤ (SimpleGraph.Walk.cons hadj w).length :=
        SimpleGraph.dist_le _
      rw [SimpleGraph.Walk.length_cons, hw] at hstep
      exact ih r q (Or.inr (by omega))
    -- sum the neighbours
    have hsum : |∑ r ∈ G.neighborFinset p, green G m r q| ≤ (G.degree p : ℝ) * C := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum hnb).trans ?_
      rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
    -- transport through the row identity
    have hd : (0 : ℝ) < (G.degree p : ℝ) + m ^ 2 := by positivity
    have habs : ((G.degree p : ℝ) + m ^ 2) * |green G m p q| ≤ (G.degree p : ℝ) * C := by
      have hrow := green_row_of_ne (G := G) hm hne
      have heq : ((G.degree p : ℝ) + m ^ 2) * |green G m p q|
          = |∑ r ∈ G.neighborFinset p, green G m r q| := by
        rw [← hrow, abs_mul, abs_of_pos hd]
      rw [heq]; exact hsum
    have h3 : |green G m p q| ≤ decayRate (G.degree p) m * C := by
      rw [decayRate, div_mul_eq_mul_div, le_div_iff₀ hd]
      linarith
    have h4 : decayRate (G.degree p) m * C ≤ decayRate Δ m * C :=
      mul_le_mul_of_nonneg_right (decayRate_mono (hΔ p) hm) hC0
    calc |green G m p q| ≤ decayRate (G.degree p) m * C := h3
      _ ≤ decayRate Δ m * C := h4
      _ = decayRate Δ m ^ (k + 1) * (m ^ 2)⁻¹ := by rw [hC, pow_succ]; ring

/-- **THE DECAY ESTIMATE.** On every finite simple graph with degrees bounded by `Δ`, at every
nonzero mass, the propagator between two sites is at most `(Δ/(Δ+m²))^{dist} · m⁻²`. -/
theorem green_abs_le_pow_dist (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) (p q : V) :
    |green G m p q| ≤ decayRate Δ m ^ (G.dist p q) * (m ^ 2)⁻¹ :=
  green_abs_le_pow hm hΔ (G.dist p q) p q (Or.inr le_rfl)

/-- The same with the graph's own maximum degree, which needs no hypothesis. -/
theorem green_abs_le_maxDegree (hm : m ≠ 0) (p q : V) :
    |green G m p q| ≤ decayRate G.maxDegree m ^ (G.dist p q) * (m ^ 2)⁻¹ :=
  green_abs_le_pow_dist hm (fun v => G.degree_le_maxDegree v) p q

/-- **AND THE BOUND GOES TO ZERO**, at a rate fixed by `Δ`, `m` and `ε` and nothing else. -/
theorem exists_pow_lt (hm : m ≠ 0) (Δ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k, N ≤ k → decayRate Δ m ^ k * (m ^ 2)⁻¹ < ε := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have htend : Filter.Tendsto (fun k : ℕ => decayRate Δ m ^ k * (m ^ 2)⁻¹) Filter.atTop
      (nhds (0 * (m ^ 2)⁻¹)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (decayRate_nonneg Δ hm)
      (decayRate_lt_one Δ hm)).mul_const _
  rw [zero_mul] at htend
  exact Filter.eventually_atTop.mp (htend.eventually (gt_mem_nhds hε))

/-! ## 4. The same statement about the field

`GraphLaplacian.twoPoint` and `LatticeGeneratingFunctional.covariance_eval` are the two
vocabularies the estate uses for the two-point function; the estimate is stated in both so that
neither consumer has to translate.
-/

/-- **THE TWO-POINT FUNCTION OF THE LATTICE FIELD CLUSTERS EXPONENTIALLY IN THE GRAPH
DISTANCE.** -/
theorem covariance_abs_le (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) (p q : V) :
    |cov[fun ω : EuclideanSpace ℝ V => ω p, fun ω : EuclideanSpace ℝ V => ω q;
        gaussianField G m]|
      ≤ decayRate Δ m ^ (G.dist p q) * (m ^ 2)⁻¹ := by
  rw [LatticeGeneratingFunctional.covariance_eval (G := G) hm p q]
  exact green_abs_le_pow_dist hm hΔ p q

/-- The same in the integral vocabulary of `GraphLaplacian.twoPoint`. -/
theorem twoPoint_abs_le (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) (p q : V) :
    |∫ ω, ω p * ω q ∂(gaussianField G m)| ≤ decayRate Δ m ^ (G.dist p q) * (m ^ 2)⁻¹ := by
  rw [GraphLaplacian.twoPoint (G := G) hm p q]
  exact green_abs_le_pow_dist hm hΔ p q

/-! ## 5. Uniformity in the volume, which is the reason for §2

A bound per volume is worth nothing to an infinite-volume argument; a bound whose *rate* is the
same at every volume is the thing W2 would consume. On the box the degree bound is `2d` at every
side length, so that is exactly what comes out.
-/

open BoxGraph in
/-- **ON THE `n^d` BOX THE RATE DOES NOT DEPEND ON `n`.** -/
theorem boxGraph_green_abs_le (d n : ℕ) (hm : m ≠ 0) (p q : Site d n) :
    |green (boxGraph d n) m p q|
      ≤ decayRate (2 * d) m ^ ((boxGraph d n).dist p q) * (m ^ 2)⁻¹ :=
  green_abs_le_pow_dist hm (fun v => BoxDegree.boxGraph_degree_le v) p q

/-- **UNIFORMITY IS A PROPERTY OF THE DEGREE BOUND AND NOTHING ELSE**, so the statement should
not name a family of graphs — and until 15 Aug 2026 the only versions of it in the estate did
(`boxGraph_uniform` here, `TorusDecay.torusGraph_uniform` there). `N` is produced from `Δ`, `m`
and `ε` before the graph, the vertex type, or the two sites are mentioned; the family versions are
now instances rather than separate theorems.

The separation hypothesis is `¬ H.Reachable p q ∨ N ≤ H.dist p q` for the reason recorded on
`green_abs_le_pow`: `SimpleGraph.dist` is `0` across components, so the second disjunct alone
excludes exactly the pairs where the conclusion is sharpest. -/
theorem exists_dist_uniform (hm : m ≠ 0) (Δ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (∀ v : W, H.degree v ≤ Δ) → ∀ p q : W,
        (¬ H.Reachable p q ∨ N ≤ H.dist p q) → |green H m p q| < ε := by
  obtain ⟨N, hN⟩ := exists_pow_lt hm Δ hε
  refine ⟨N, fun W _ _ H _ hdeg p q hsep => ?_⟩
  exact lt_of_le_of_lt (green_abs_le_pow hm hdeg N p q hsep) (hN N le_rfl)

/-- **THE SAME UNIFORMITY, FOR THE FIELD RATHER THAN THE PROPAGATOR.** `exists_dist_uniform` is
about `green`, which is an intermediate object; a consumer asking whether the estate has a uniform
correlation bound is asking about the **covariance of the field**. What the estate had was
`covariance_abs_le` — general in the graph but **pointwise**, a bound at each pair rather than a
distance beyond which everything is below `ε` — and the `ε` form only at the propagator level.
**There was no `ε`-uniform statement about the field at all.** Same `N`, produced from `Δ`, `m`
and `ε` before the graph. -/
theorem exists_dist_uniform_covariance (hm : m ≠ 0) (Δ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (∀ v : W, H.degree v ≤ Δ) → ∀ p q : W,
        (¬ H.Reachable p q ∨ N ≤ H.dist p q) →
        |cov[fun ω : EuclideanSpace ℝ W => ω p, fun ω : EuclideanSpace ℝ W => ω q;
            gaussianField H m]| < ε := by
  obtain ⟨N, hN⟩ := exists_dist_uniform hm Δ hε
  refine ⟨N, fun W _ _ H _ hdeg p q hsep => ?_⟩
  rw [LatticeGeneratingFunctional.covariance_eval (G := H) hm p q]
  exact hN W H hdeg p q hsep

/-- And in `GraphLaplacian.twoPoint`'s vocabulary, so neither consumer has to translate. -/
theorem exists_dist_uniform_twoPoint (hm : m ≠ 0) (Δ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (∀ v : W, H.degree v ≤ Δ) → ∀ p q : W,
        (¬ H.Reachable p q ∨ N ≤ H.dist p q) →
        |∫ ω, ω p * ω q ∂(gaussianField H m)| < ε := by
  obtain ⟨N, hN⟩ := exists_dist_uniform hm Δ hε
  refine ⟨N, fun W _ _ H _ hdeg p q hsep => ?_⟩
  rw [GraphLaplacian.twoPoint (G := H) hm p q]
  exact hN W H hdeg p q hsep

open BoxGraph in
/-- **AND THEREFORE A DISTANCE CHOSEN FROM `d`, `m` AND `ε` ALONE WORKS AT EVERY SIDE LENGTH.**
The quantifier order is the content: `N` is produced before `n` is mentioned. Now an instance of
`exists_dist_uniform`, which produces `N` before the *graph* is mentioned. -/
theorem boxGraph_uniform (d : ℕ) (hm : m ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (n : ℕ) (p q : Site d n),
      (¬ (boxGraph d n).Reachable p q ∨ N ≤ (boxGraph d n).dist p q) →
      |green (boxGraph d n) m p q| < ε := by
  obtain ⟨N, hN⟩ := exists_dist_uniform (m := m) hm (2 * d) hε
  exact ⟨N, fun n p q hpq =>
    hN (Site d n) (boxGraph d n) (fun v => BoxDegree.boxGraph_degree_le v) p q hpq⟩

end GreenDecay
