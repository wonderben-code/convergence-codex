import CrossBlockStructure

/-!
# At large mass the coupling hypothesis is not merely sufficient — it is necessary

`UNLOCK_WATCHLIST`'s necessity item — *does `GraphReflection.ReflectionPositive` IMPLY `hcross`?* —
names one place to look and says it has not been looked at:

> *"the large-mass regime, where the Green function is close to a multiple of the identity, is the
> obvious place to look and has not been looked at."*

It is looked at here, and **there is no counterexample there.** At large mass reflection positivity
and the coupling hypothesis agree, so the refutation that item hopes for cannot live in the regime
the item points at.

## The statements

`reflectedForm_neg_of_crossForm_pos`: on a `d`-regular graph with a mirror reflection, if some `c`
supported on the half has `crossForm G m θ H c > 0` — that is, if `hcross` fails, and by
`CrossPosSemidef.hcross_iff_zeroSum` it then fails at some such `c` — then the reflected form is
**strictly negative** at `c` for every mass with

    d² · (∑_{p ∈ H} |c p|)²  <  m² · crossForm G m θ H c.

An explicit threshold, per witness, with no asymptotics in the statement. Hence
`not_reflectionPositive_of_crossForm_pos`, and then

`hcross_of_reflectionPositive_arbitrarily_large`: **a graph reflection positive at arbitrarily
large masses satisfies `hcross`.** That is the wall's converse in the large-mass regime, on every
regular graph, with no condition on `A²` — where
`CrossPosSemidef.reflectionPositive_iff_hcross_of_adjSq` needed `GreenExpansion` §9's class and got
every mass in exchange.

## Why it works

`GreenExpansion.sq_mul_reflectedForm` is exact: with `s = d + m²`,

    s² · reflectedForm c  =  − crossForm c  +  ∑∑ c p · c q · (green·A·A) (θ p) q.

`crossForm` does not depend on the mass at all
(`GraphMirrorReflection.crossForm_mass_independent`) while the remainder is built from `green` —
and **`green` is uniformly small at large mass.** `massive = L + m²` with `L` positive semidefinite,
so `m²·1 ≼ massive` (`massSq_le_massive`), so by antitonicity of inversion in the Loewner order
(`MatrixLoewner.posDef_inv_le_inv`, already in the estate) `green ≼ (m²)⁻¹·1`. Positive
semidefiniteness then bounds every entry, diagonal **and off** — `|green x y| ≤ (m²)⁻¹`
(`green_abs_le`), through `posSemidef_abs_le`, which Mathlib does not have: three differently
shaped probes of the pinned environment returned nothing, so it is proved here from the `e_x ± e_y`
test vectors.

One column sum of `A²` is `d²` on a `d`-regular graph (`adjSq_col_sum`), and `A²` has nonnegative
entries, so the whole remainder is at most `d²/m²` times `(∑_H |c|)²`.

## What this closes, and what it does not

* **Closed: the large-mass regime as a place a refutation could live.** It cannot.
* **Closed: the direction of the failure, which was not obvious.** One might expect a graph failing
  `hcross` to be *rescued* at large mass, the Green function becoming a multiple of the identity
  and the reflected form a sum of squares. It is the opposite: to leading order the reflected form
  is `−crossForm/s²`, so failing `hcross` **forces** reflection positivity to fail.
* **NOT closed: the wall.** `WALLS` W1's remaining leg wants a remainder bound good enough to
  decide the converse *at a fixed mass*; what is bounded here is good enough only once `m²` beats a
  constant built from the witness. Different questions, and this file settles the easier one.
* **NOT closed: small mass, which is now the only place left.** `GreenExpansion` §9's slack grows
  like `m⁻²`, so if a counterexample exists it is at small mass. **None is exhibited here and none
  is claimed to exist** — what changed is that the search has lost half its range.

## §6 — and at small mass, where the question now lives, the divergence misses its target

`PROOF_STRATEGY` §3's retry. §4 moves the search to small mass; §6 asks what is there, and the
answer is exact rather than asymptotic.

`GreenExpansion.green_mulVec_one` says every row of `green` sums to `m⁻²`. Subtracting
`(m²·|V|)⁻¹` times the all-ones matrix therefore leaves a matrix whose rows sum to **zero**
(`greenHat_row_sum`), and the reflected form splits with no error term at all
(`reflectedForm_split`):

    reflectedForm c  =  (the hat form at c)  +  (m²·|V|)⁻¹ · (∑ c)².

**All of the `m⁻²` divergence sits on the constant mode and nowhere else.** So on a sum-zero vector
it is simply absent (`reflectedForm_eq_hat_of_sum_zero`).

**Why that matters here.** `CrossPosSemidef.hcross_iff_zeroSum` says that if the coupling
hypothesis fails, it fails at a vector supported on the half that **sums to zero there** — hence on
all of `V`. So (`hcross_failure_is_orthogonal_to_the_slack`):

> **the growing slack that makes small mass the place to look is unavailable at every witness of
> the failure it would have to excuse.** The slack lives on the constant mode; the failures live
> orthogonally to it.

Both halves are exact; neither is an estimate. **This does not close the converse** — what remains
at such a `c` is whether the hat form can be nonnegative while the coupling form is positive, which
is the wall restated on a subspace of codimension one, with the `m⁻²` gone.

## Non-vacuity, checked on the estate's own witness — and the general theorem loses

`IndefiniteCoupling.crossGraph` is `1`-regular with `crossForm … wpos = 2` and `∑_H |wpos| = 2`, so
the threshold works out to `m² > 2` and §4 says reflection positivity fails past that mass
(`crossGraph_not_reflectionPositive_of_two_lt`). `IndefiniteCoupling.not_reflectionPositive` says
it fails at **every** nonzero mass. **So the general theorem is strictly weaker than the special
one on the only graph where both apply.** That is what a large-mass result should be, and saying it
is more useful than presenting the two as independent confirmations.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace GreenLargeMass

open Matrix GraphReflection GraphMirrorReflection
open scoped MatrixOrder

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. A positive semidefinite matrix is bounded off the diagonal by its diagonal -/

section PSD

variable {P : Matrix V V ℝ}

omit [DecidableEq V] in
/-- The quadratic form as a double sum, in the shape the two-point restriction below wants. -/
theorem quad_eq (P : Matrix V V ℝ) (v : V → ℝ) :
    v ⬝ᵥ (P *ᵥ v) = ∑ i, ∑ j, v i * v j * P i j := by
  rw [dotProduct]
  exact Finset.sum_congr rfl fun i _ => by
    rw [mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

-- `Matrix.PosSemidef` in this Mathlib quantifies over FINITELY SUPPORTED vectors, so the
-- statement below genuinely does not need `[Fintype V]` — but the proof does, because it goes
-- through `posSemidef_iff_dotProduct_mulVec` and a sum over `Finset.univ`. Suppressed here rather
-- than added to `ERRATUM 39`'s warning baseline, and said out loud rather than left as a puzzle.
set_option linter.unusedFintypeInType false in
omit [DecidableEq V] in
/-- **AN OFF-DIAGONAL ENTRY IS BOUNDED BY THE TWO DIAGONAL ONES.** `e_x ± e_y` gives
`P x x ± 2 P x y + P y y ≥ 0`, and the two together are the bound.

**Mathlib does not have this**, checked by three differently shaped probes of the pinned
environment (`ERRATUM 79`'s rule that an absence claim is only as good as its pattern):
`PosSemidef → … |…| ≤`, `PosSemidef → … ≤ … i i * … j j` and `PosSemidef → … x i j * x i j` all
return nothing, while `Matrix.PosSemidef.diag_nonneg` — the diagonal half — is there. -/
theorem posSemidef_abs_le (hP : P.PosSemidef) (x y : V) :
    |P x y| ≤ (P x x + P y y) / 2 := by
  classical
  have hdx : 0 ≤ P x x := hP.diag_nonneg (i := x)
  have hdy : 0 ≤ P y y := hP.diag_nonneg (i := y)
  by_cases hxy : x = y
  · subst hxy
    rw [abs_of_nonneg hdx]
    linarith
  -- the two-point test vector, at `t = 1` and `t = -1`
  have key : ∀ t : ℝ, 0 ≤ P x x + 2 * t * P x y + t ^ 2 * P y y := by
    intro t
    set v : V → ℝ := fun i => if i = x then 1 else if i = y then t else 0 with hvdef
    have hsupp : ∀ i, i ∉ ({x, y} : Finset V) → v i = 0 := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      rw [hvdef]; simp [hi.1, hi.2]
    have hnn := (posSemidef_iff_dotProduct_mulVec.mp hP).2 v
    rw [star_trivial, quad_eq P v] at hnn
    have hin : ∀ i : V, ∑ j, v i * v j * P i j = ∑ j ∈ ({x, y} : Finset V), v i * v j * P i j :=
      fun i => (Finset.sum_subset (Finset.subset_univ _)
        (fun j _ hj => by rw [hsupp j hj]; ring)).symm
    have hout : ∑ i, (∑ j ∈ ({x, y} : Finset V), v i * v j * P i j)
        = ∑ i ∈ ({x, y} : Finset V), ∑ j ∈ ({x, y} : Finset V), v i * v j * P i j :=
      (Finset.sum_subset (Finset.subset_univ _)
        (fun i _ hi => Finset.sum_eq_zero fun j _ => by rw [hsupp i hi]; ring)).symm
    rw [Finset.sum_congr rfl fun i _ => hin i, hout] at hnn
    have hyx : P y x = P x y := by
      have hh := congrFun (congrFun hP.1.eq y) x
      rw [Matrix.conjTranspose_apply, star_trivial] at hh
      exact hh.symm
    have hval : ∑ i ∈ ({x, y} : Finset V), ∑ j ∈ ({x, y} : Finset V), v i * v j * P i j
        = P x x + t * P x y + t * P y x + t ^ 2 * P y y := by
      rw [Finset.sum_insert (by simpa using hxy), Finset.sum_singleton,
        Finset.sum_insert (by simpa using hxy), Finset.sum_singleton,
        Finset.sum_insert (by simpa using hxy), Finset.sum_singleton]
      simp only [hvdef, if_neg hxy, if_neg (Ne.symm hxy), if_true]
      ring
    rw [hval, hyx] at hnn
    linarith
  have h1 := key 1
  have h2 := key (-1)
  rw [abs_le]
  constructor <;> nlinarith [h1, h2]

end PSD

/-! ## 2. The Green function is uniformly bounded by `m⁻²` -/

section Bound

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **`m²·1 ≼ massive`**, because the difference is the Laplacian. -/
theorem massSq_le_massive (m : ℝ) :
    (m ^ 2) • (1 : Matrix V V ℝ) ≤ GraphLaplacian.massive G m := by
  refine Matrix.le_iff.mpr ?_
  have hEq : GraphLaplacian.massive G m - (m ^ 2) • (1 : Matrix V V ℝ) = G.lapMatrix ℝ := by
    rw [GraphLaplacian.massive]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hEq]
  exact SimpleGraph.posSemidef_lapMatrix ℝ G

/-- **AND SO `green ≼ m⁻²·1`**, by antitonicity of inversion in the Loewner order. -/
theorem green_le_smul_one {m : ℝ} (hm : m ≠ 0) :
    GraphLaplacian.green G m ≤ (m ^ 2)⁻¹ • (1 : Matrix V V ℝ) := by
  have hpos : (0 : ℝ) < m ^ 2 := by positivity
  have hPD : ((m ^ 2) • (1 : Matrix V V ℝ)).PosDef :=
    (Matrix.PosDef.one (n := V) (R := ℝ)).smul hpos
  have hinv : ((m ^ 2) • (1 : Matrix V V ℝ))⁻¹ = (m ^ 2)⁻¹ • (1 : Matrix V V ℝ) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  have := MatrixLoewner.posDef_inv_le_inv hPD (massSq_le_massive G m)
  rwa [hinv] at this

variable {G}

/-- Every diagonal entry of the Green function is at most `m⁻²`. -/
theorem green_diag_le {m : ℝ} (hm : m ≠ 0) (x : V) :
    GraphLaplacian.green G m x x ≤ (m ^ 2)⁻¹ := by
  have h := Matrix.le_iff.mp (green_le_smul_one G hm)
  have := h.diag_nonneg (i := x)
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one] at this
  linarith

/-- **AND EVERY ENTRY, ON OR OFF THE DIAGONAL.** -/
theorem green_abs_le {m : ℝ} (hm : m ≠ 0) (x y : V) :
    |GraphLaplacian.green G m x y| ≤ (m ^ 2)⁻¹ := by
  have hb := posSemidef_abs_le (GraphLaplacian.green_posDef G hm).posSemidef x y
  have hx := green_diag_le (G := G) hm x
  have hy := green_diag_le (G := G) hm y
  linarith

end Bound

/-! ## 3. The remainder of the exact identity is `O(m⁻²)` -/

section Remainder

variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

omit [DecidableEq V] in
/-- Entries of `A²` are nonnegative — they count length-two walks. -/
theorem adjSq_nonneg (r q : V) : 0 ≤ (G.adjMatrix ℝ * G.adjMatrix ℝ) r q := by
  rw [Matrix.mul_apply]
  refine Finset.sum_nonneg fun t _ => mul_nonneg ?_ ?_ <;>
    · simp only [SimpleGraph.adjMatrix_apply]
      split_ifs <;> norm_num

omit [DecidableEq V] in
/-- Row sums of the adjacency matrix are the degree. -/
theorem adj_row_sum (r : V) : ∑ t, G.adjMatrix ℝ r t = (G.degree r : ℝ) := by
  have := SimpleGraph.adjMatrix_mulVec_const_apply (α := ℝ) (G := G) (a := 1) (v := r)
  rw [Matrix.mulVec, dotProduct] at this
  simpa using this

omit [DecidableEq V] in
/-- **A COLUMN SUM OF `A²` IS `d²` ON A `d`-REGULAR GRAPH.** -/
theorem adjSq_col_sum (hd : G.IsRegularOfDegree d) (q : V) :
    ∑ r, (G.adjMatrix ℝ * G.adjMatrix ℝ) r q = (d : ℝ) ^ 2 := by
  have hsym : ∀ r t : V, G.adjMatrix ℝ r t = G.adjMatrix ℝ t r := by
    intro r t
    simp only [SimpleGraph.adjMatrix_apply]
    by_cases hh : G.Adj r t
    · rw [if_pos hh, if_pos hh.symm]
    · rw [if_neg hh, if_neg (fun hc => hh hc.symm)]
  calc ∑ r, (G.adjMatrix ℝ * G.adjMatrix ℝ) r q
      = ∑ r, ∑ t, G.adjMatrix ℝ r t * G.adjMatrix ℝ t q :=
        Finset.sum_congr rfl fun r _ => Matrix.mul_apply
    _ = ∑ t, ∑ r, G.adjMatrix ℝ t r * G.adjMatrix ℝ t q :=
        (Finset.sum_comm).trans (Finset.sum_congr rfl fun t _ =>
          Finset.sum_congr rfl fun r _ => by rw [hsym r t])
    _ = ∑ t, (G.degree t : ℝ) * G.adjMatrix ℝ t q := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← Finset.sum_mul, adj_row_sum t]
    _ = (d : ℝ) * ∑ t, G.adjMatrix ℝ t q := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by rw [hd t]
    _ = (d : ℝ) ^ 2 := by
        have : ∑ t, G.adjMatrix ℝ t q = (d : ℝ) := by
          rw [Finset.sum_congr rfl fun t _ => hsym t q, adj_row_sum q, hd q]
        rw [this]; ring

/-- **THE REMAINDER'S ENTRIES ARE `O(m⁻²)`.** -/
theorem greenAdjSq_abs_le (hd : G.IsRegularOfDegree d) {m : ℝ} (hm : m ≠ 0) (x q : V) :
    |(GraphLaplacian.green G m * G.adjMatrix ℝ * G.adjMatrix ℝ) x q|
      ≤ (m ^ 2)⁻¹ * (d : ℝ) ^ 2 := by
  have hassoc : (GraphLaplacian.green G m * G.adjMatrix ℝ * G.adjMatrix ℝ) x q
      = ∑ r, GraphLaplacian.green G m x r * (G.adjMatrix ℝ * G.adjMatrix ℝ) r q := by
    rw [Matrix.mul_assoc, Matrix.mul_apply]
  rw [hassoc]
  calc |∑ r, GraphLaplacian.green G m x r * (G.adjMatrix ℝ * G.adjMatrix ℝ) r q|
      ≤ ∑ r, |GraphLaplacian.green G m x r * (G.adjMatrix ℝ * G.adjMatrix ℝ) r q| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r, (m ^ 2)⁻¹ * (G.adjMatrix ℝ * G.adjMatrix ℝ) r q := by
        refine Finset.sum_le_sum fun r _ => ?_
        rw [abs_mul, abs_of_nonneg (adjSq_nonneg r q)]
        exact mul_le_mul_of_nonneg_right (green_abs_le hm x r) (adjSq_nonneg r q)
    _ = (m ^ 2)⁻¹ * (d : ℝ) ^ 2 := by rw [← Finset.mul_sum, adjSq_col_sum hd q]

end Remainder

/-! ## 4. And so failing the coupling hypothesis kills reflection positivity at large mass -/

section Main

variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}
variable {d : ℕ} {c : V → ℝ}

/-- The remainder of `GreenExpansion.sq_mul_reflectedForm`, bounded. -/
theorem remainder_abs_le (hd : G.IsRegularOfDegree d) (hm : m ≠ 0) :
    |∑ p ∈ H, ∑ q ∈ H,
        c p * c q * (GraphLaplacian.green G m * G.adjMatrix ℝ * G.adjMatrix ℝ) (θ p) q|
      ≤ (m ^ 2)⁻¹ * (d : ℝ) ^ 2 * (∑ p ∈ H, |c p|) ^ 2 := by
  have hstep : ∀ p ∈ H, |∑ q ∈ H,
      c p * c q * (GraphLaplacian.green G m * G.adjMatrix ℝ * G.adjMatrix ℝ) (θ p) q|
      ≤ |c p| * ((m ^ 2)⁻¹ * (d : ℝ) ^ 2) * ∑ q ∈ H, |c q| := by
    intro p _
    calc |∑ q ∈ H, c p * c q * (GraphLaplacian.green G m * G.adjMatrix ℝ * G.adjMatrix ℝ) (θ p) q|
        ≤ ∑ q ∈ H,
            |c p * c q * (GraphLaplacian.green G m * G.adjMatrix ℝ * G.adjMatrix ℝ) (θ p) q| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ H, |c p| * |c q| * ((m ^ 2)⁻¹ * (d : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun q _ => ?_
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (greenAdjSq_abs_le hd hm (θ p) q)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = |c p| * ((m ^ 2)⁻¹ * (d : ℝ) ^ 2) * ∑ q ∈ H, |c q| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun q _ => by ring
  calc |∑ p ∈ H, ∑ q ∈ H,
        c p * c q * (GraphLaplacian.green G m * G.adjMatrix ℝ * G.adjMatrix ℝ) (θ p) q|
      ≤ ∑ p ∈ H, |∑ q ∈ H,
          c p * c q * (GraphLaplacian.green G m * G.adjMatrix ℝ * G.adjMatrix ℝ) (θ p) q| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ H, |c p| * ((m ^ 2)⁻¹ * (d : ℝ) ^ 2) * ∑ q ∈ H, |c q| :=
        Finset.sum_le_sum hstep
    _ = (m ^ 2)⁻¹ * (d : ℝ) ^ 2 * (∑ p ∈ H, |c p|) ^ 2 := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        ring

/-- **THE THEOREM.** A witness that the coupling hypothesis fails makes the reflected form
strictly negative at every mass past an explicit, witness-dependent threshold. -/
theorem reflectedForm_neg_of_crossForm_pos (hd : G.IsRegularOfDegree d)
    (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hcs : ∀ p, p ∉ H → c p = 0) (_hpos : 0 < crossForm G m θ H c)
    (hbig : (d : ℝ) ^ 2 * (∑ p ∈ H, |c p|) ^ 2 < m ^ 2 * crossForm G m θ H c) :
    reflectedForm G m θ c < 0 := by
  have hmsq : (0 : ℝ) < m ^ 2 := by positivity
  have hid := GreenExpansion.sq_mul_reflectedForm hd hM h hm hcs
  have hrem := remainder_abs_le (G := G) (H := H) (θ := θ) (c := c) hd hm
  have hsmall : (m ^ 2)⁻¹ * (d : ℝ) ^ 2 * (∑ p ∈ H, |c p|) ^ 2 < crossForm G m θ H c := by
    rw [inv_mul_eq_div, div_mul_eq_mul_div, div_lt_iff₀ hmsq]
    nlinarith [hbig]
  have hs : (0 : ℝ) < ((d : ℝ) + m ^ 2) ^ 2 := by positivity
  have hneg : ((d : ℝ) + m ^ 2) ^ 2 * reflectedForm G m θ c < 0 := by
    rw [hid]
    have := abs_le.mp hrem
    linarith [this.1, this.2]
  nlinarith [hneg, hs]

/-- The same, as a failure of the estate's own predicate. -/
theorem not_reflectionPositive_of_crossForm_pos (hd : G.IsRegularOfDegree d)
    (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hcs : ∀ p, p ∉ H → c p = 0) (hpos : 0 < crossForm G m θ H c)
    (hbig : (d : ℝ) ^ 2 * (∑ p ∈ H, |c p|) ^ 2 < m ^ 2 * crossForm G m θ H c) :
    ¬ GraphReflection.ReflectionPositive G m θ H := by
  intro hRP
  exact absurd (hRP c hcs)
    (not_le.mpr (reflectedForm_neg_of_crossForm_pos hd hM h hm hcs hpos hbig))

/-- Truncating a vector to the half does not change the coupling form, which only ever reads the
half's entries. -/
theorem crossForm_restrict (w : V → ℝ) :
    crossForm G m θ H (fun i => if i ∈ H then w i else 0) = crossForm G m θ H w := by
  classical
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
  simp only [if_pos hp, if_pos hq]

/-- **THE WALL'S CONVERSE, IN THE LARGE-MASS REGIME.** A graph reflection positive at arbitrarily
large masses satisfies the coupling hypothesis — on every regular graph, with no condition on `A²`
and no class hypothesis. The conclusion does not name a mass because `crossForm` does not depend on
one (`GraphMirrorReflection.crossForm_mass_independent`). -/
theorem hcross_of_reflectionPositive_arbitrarily_large (hd : G.IsRegularOfDegree d)
    (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hRP : ∀ M : ℝ, ∃ m' : ℝ, M < m' ∧ m' ≠ 0 ∧ GraphReflection.ReflectionPositive G m' θ H)
    (m₀ : ℝ) (w : V → ℝ) :
    crossForm G m₀ θ H w ≤ 0 := by
  classical
  by_contra hc
  rw [not_le] at hc
  set u : V → ℝ := fun i => if i ∈ H then w i else 0 with hudef
  have hus : ∀ p, p ∉ H → u p = 0 := fun p hp => by rw [hudef]; simp [hp]
  have hupos : ∀ m' : ℝ, 0 < crossForm G m' θ H u := by
    intro m'
    rw [hudef, crossForm_restrict w, crossForm_mass_independent hM m' m₀ w]
    exact hc
  set S : ℝ := ∑ p ∈ H, |u p| with hSdef
  set K : ℝ := (d : ℝ) ^ 2 * S ^ 2 / crossForm G m₀ θ H u with hKdef
  obtain ⟨m', hm'gt, hm'ne, hm'RP⟩ := hRP (max 1 K)
  have h1 : (1 : ℝ) < m' := lt_of_le_of_lt (le_max_left _ _) hm'gt
  have hK : K < m' := lt_of_le_of_lt (le_max_right _ _) hm'gt
  have hbig : (d : ℝ) ^ 2 * S ^ 2 < m' ^ 2 * crossForm G m' θ H u := by
    have hcf : crossForm G m' θ H u = crossForm G m₀ θ H u := crossForm_mass_independent hM m' m₀ u
    have hcf0 : 0 < crossForm G m₀ θ H u := hupos m₀
    have hmsq : m' < m' ^ 2 := by nlinarith [h1]
    have hKlt : K < m' ^ 2 := lt_trans hK hmsq
    rw [hKdef, div_lt_iff₀ hcf0] at hKlt
    rw [hcf]
    linarith [hKlt]
  exact not_reflectionPositive_of_crossForm_pos hd hM h hm'ne hus (hupos m') hbig hm'RP

/-- **AND SO, AT LARGE MASS, THE TWO CONDITIONS ARE THE SAME CONDITION.** One direction is the
estate's own theorem at every mass (`GraphMirrorReflection.reflectionPositive_mirror`); the other
is this file's, and it needs the mass to be large. Together: **being reflection positive at
arbitrarily large masses is exactly `hcross`.** -/
theorem reflectionPositive_arbitrarily_large_iff_hcross (hd : G.IsRegularOfDegree d)
    (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (m₀ : ℝ) :
    (∀ M : ℝ, ∃ m' : ℝ, M < m' ∧ m' ≠ 0 ∧ GraphReflection.ReflectionPositive G m' θ H)
      ↔ ∀ w : V → ℝ, crossForm G m₀ θ H w ≤ 0 := by
  constructor
  · intro hRP w
    exact hcross_of_reflectionPositive_arbitrarily_large hd hM h hRP m₀ w
  · intro hcross M
    refine ⟨max M 0 + 1, by have := le_max_left M 0; linarith, by positivity,
      fun c hcs => ?_⟩
    exact reflectionPositive_mirror hM h (by positivity) 
      (fun w => by rw [crossForm_mass_independent hM _ m₀ w]; exact hcross w)
      (fun p hp _ => hcs p hp)

end Main

/-! ## 5. Non-vacuity, on the estate's own witness -/

section Witness

open IndefiniteCoupling

/-- `crossGraph` is `1`-regular, so §4 applies to it. -/
theorem crossGraph_one_regular : crossGraph.IsRegularOfDegree 1 := degree_eq_one

/-- The refuting vector's `ℓ¹` mass on the half is `2`. -/
theorem wpos_abs_sum : ∑ p ∈ Hh, |wpos p| = 2 := by
  rw [show Hh = ({0, 1} : Finset (Fin 4)) from rfl]
  norm_num [wpos]

/-- **THE HYPOTHESES ARE INHABITED, AND THE ESTATE ALREADY KNOWS THE ANSWER THERE — WHICH IS THE
POINT OF CHECKING.** On `IndefiniteCoupling.crossGraph` the threshold works out to `m² > 2`, so §4
says reflection positivity fails past that mass. `IndefiniteCoupling.not_reflectionPositive` says
it fails at **every** nonzero mass. **So the general theorem is strictly weaker than the special
one on the only graph where both apply**, which is what a large-mass result should be, and saying
so is more useful than presenting the two as independent confirmations. -/
theorem crossGraph_not_reflectionPositive_of_two_lt {m : ℝ} (hm : m ≠ 0) (hm2 : 2 < m ^ 2) :
    ¬ GraphReflection.ReflectionPositive crossGraph m rho Hh := by
  refine not_reflectionPositive_of_crossForm_pos (c := wpos) crossGraph_one_regular
    isMirrorHalf_Hh isRefl_rho hm CrossBlockStructure.wpos_supported ?_ ?_
  · rw [crossForm_pos m]; norm_num
  · rw [crossForm_pos m, wpos_abs_sum]
    norm_num
    linarith

end Witness

/-! ## 6. And at small mass, where the question now lives, the divergence misses its target -/

section SmallMass

open GreenExpansion

variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

/-- The Green function with its constant mode removed. `green`'s row sums are all `m⁻²`
(`GreenExpansion.green_mulVec_one`), so subtracting `(m²·|V|)⁻¹` times the all-ones matrix leaves
a matrix that annihilates constants — and carries none of the `m⁻²` divergence. -/
noncomputable def greenHat (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) : Matrix V V ℝ :=
  GraphLaplacian.green G m - (m ^ 2 * (Fintype.card V : ℝ))⁻¹ • allOnes V

theorem greenHat_row_sum (hm : m ≠ 0) (hV : 0 < Fintype.card V) (x : V) :
    ∑ q, greenHat G m x q = 0 := by
  have hrow : ∑ q, GraphLaplacian.green G m x q = (m ^ 2)⁻¹ := by
    have hg := congrFun (green_mulVec_one (G := G) (m := m) hm) x
    rw [Matrix.mulVec, dotProduct] at hg
    simpa using hg
  have hVne : ((Fintype.card V : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hV.ne'
  have hm2 : (m : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ hm
  have hentry : ∀ q : V, greenHat G m x q
      = GraphLaplacian.green G m x q - (m ^ 2 * (Fintype.card V : ℝ))⁻¹ := by
    intro q
    simp only [greenHat, Matrix.sub_apply, Matrix.smul_apply, allOnes, smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl fun q _ => hentry q, Finset.sum_sub_distrib, hrow,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- **THE REFLECTED FORM SPLITS EXACTLY**, on every graph and at every nonzero mass: a part built
from a matrix whose rows sum to zero, plus the whole of the `m⁻²` divergence, which sits on the
constant mode and nowhere else. -/
theorem reflectedForm_split (c : V → ℝ) :
    GraphReflection.reflectedForm G m θ c
      = (∑ p, ∑ q, c p * c q * greenHat G m (θ p) q)
        + (m ^ 2 * (Fintype.card V : ℝ))⁻¹ * (∑ p, c p) ^ 2 := by
  have hsplit : ∀ p q : V, c p * c q * GraphLaplacian.green G m (θ p) q
      = c p * c q * greenHat G m (θ p) q
        + c p * c q * (m ^ 2 * (Fintype.card V : ℝ))⁻¹ := by
    intro p q
    simp only [greenHat, Matrix.sub_apply, Matrix.smul_apply, allOnes, smul_eq_mul, mul_one]
    ring
  have hconst : ∑ p, ∑ q, c p * c q * (m ^ 2 * (Fintype.card V : ℝ))⁻¹
      = (m ^ 2 * (Fintype.card V : ℝ))⁻¹ * (∑ p, c p) ^ 2 := by
    have hrow : ∀ p : V, ∑ q, c p * c q * (m ^ 2 * (Fintype.card V : ℝ))⁻¹
        = c p * ((∑ q, c q) * (m ^ 2 * (Fintype.card V : ℝ))⁻¹) := by
      intro p
      rw [show c p * ((∑ q, c q) * (m ^ 2 * (Fintype.card V : ℝ))⁻¹)
            = ∑ q, c p * (c q * (m ^ 2 * (Fintype.card V : ℝ))⁻¹) by
          rw [← Finset.mul_sum, ← Finset.sum_mul]]
      exact Finset.sum_congr rfl fun q _ => by ring
    rw [Finset.sum_congr rfl fun p _ => hrow p, ← Finset.sum_mul, sq]
    ring
  rw [GraphReflection.reflectedForm,
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => hsplit p q,
    Finset.sum_congr rfl fun p _ => Finset.sum_add_distrib, Finset.sum_add_distrib, hconst]

/-- **AND SO ON A SUM-ZERO VECTOR THE DIVERGENCE IS SIMPLY ABSENT.** -/
theorem reflectedForm_eq_hat_of_sum_zero {c : V → ℝ} (h0 : (∑ p, c p) = 0) :
    GraphReflection.reflectedForm G m θ c = ∑ p, ∑ q, c p * c q * greenHat G m (θ p) q := by
  rw [reflectedForm_split (θ := θ) c, h0]
  ring

/-- **THE POINT, AND IT IS WHY THE SMALL-MASS ROUTE IS NARROWER THAN IT LOOKS.** If the coupling
hypothesis fails then — by `CrossPosSemidef.hcross_iff_zeroSum` — it fails at a vector supported on
the half that **sums to zero there**, and hence on all of `V`. At such a vector the `m⁻²` term of
the split above is exactly zero.

So the growing slack that makes small mass the remaining place to look
(`GreenExpansion.reflectionPositive_iff_slack`, whose slack is `(γ/m²)·(∑_H c)²`) **is unavailable
at every witness of the failure it would have to excuse.** The slack lives on the constant mode;
the failures live orthogonally to it. Both facts are exact and neither is an estimate.

**This does not close the converse.** What remains at such a `c` is whether the hat form can be
nonnegative while the coupling form is positive, and that is a question about `greenHat` with no
`m⁻²` in it — the wall, restated on a smaller space. -/
theorem hcross_failure_is_orthogonal_to_the_slack (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (m : ℝ)
    (hfail : ¬ ∀ w : V → ℝ, crossForm G m θ H w ≤ 0) :
    ∃ c : V → ℝ, (∀ p, p ∉ H → c p = 0) ∧ (∑ p, c p) = 0 ∧ 0 < crossForm G m θ H c
      ∧ GraphReflection.reflectedForm G m θ c
          = ∑ p, ∑ q, c p * c q * greenHat G m (θ p) q := by
  classical
  rw [CrossPosSemidef.hcross_iff_zeroSum hM h m] at hfail
  push Not at hfail
  obtain ⟨c, hcs, hsum, hpos⟩ := hfail
  have hall : (∑ p, c p) = 0 := by
    rw [← Finset.sum_subset (Finset.subset_univ H) (fun p _ hp => hcs p hp)]
    exact hsum
  exact ⟨c, hcs, hall, hpos, reflectedForm_eq_hat_of_sum_zero hall⟩

end SmallMass

end GreenLargeMass
