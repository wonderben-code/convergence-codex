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

**That is an identity and it is the whole of what is proved here.** A sentence claiming more — that
the hat form therefore carries no `m⁻²` divergence — stood in this header for one commit and is
**false**; see §7 and `ERRATUM 152`. What survives, and is all §6 ever needed, is that on a
sum-zero vector the explicit `(∑ c)²` term is absent (`reflectedForm_eq_hat_of_sum_zero`).

**Why that matters here.** `CrossPosSemidef.hcross_iff_zeroSum` says that if the coupling
hypothesis fails, it fails at a vector supported on the half that **sums to zero there** — hence on
all of `V`. So (`hcross_failure_is_orthogonal_to_the_slack`):

> **the `(∑ c)²` term is exactly zero at every witness of the failure it would have to excuse.**

`GreenExpansion` §9's slack is `(γ/m²)·(∑_H c)²`, the same shape, and it vanishes on the same
vectors — which is what `CrossPosSemidef.hcross_of_reflectionPositive` already spends on §9's class.
**What this adds is that the vanishing is an identity about the Green function itself and needs no
class hypothesis.** It does NOT say the rest of the form is tame at small mass; §7 exhibits a graph
where it is not.

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

## And then the same theorem without the regularity hypothesis

§§1–5 are `d`-regular because `GreenExpansion.sq_mul_reflectedForm` is. §8 runs the whole argument
on `GreenExpansion.green_mirror_general` instead, which has no regularity, and asks only for a
degree ceiling `Δ` — which every finite graph has. The witness has to be reweighted by the
per-vertex weights the general identity carries, `c p = u p · (deg p + m²)`, and then the leading
term is *exactly* `−crossForm u` with an `O(m⁻⁶)` remainder. §9 checks the hypotheses are
satisfiable somewhere §4's are not, on a six-vertex graph that is regular of no degree.

§10 then takes the other direction and the degree ceiling too — the ceiling because every finite
graph has one. **`reflectionPositive_arbitrarily_large_iff_hcross_general`: on every finite graph
carrying a mirror reflection, with no regularity, no condition on `A²`, no class hypothesis and no
bound to supply, being reflection positive at arbitrarily large masses is EXACTLY the coupling
hypothesis.** §4's biconditional is the case `Δ = d` and is subsumed; what §4 keeps is the sharper
explicit threshold `d²S² < m²·crossForm` against §10's `4Δ²S² < m²·crossForm` with `Δ ≤ m²`.

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
arbitrarily large masses is exactly `hcross`.**

**SUBSUMED 2026-08-12 by §10's `reflectionPositive_arbitrarily_large_iff_hcross_general`**, which
drops `hd` entirely. This statement is kept because it is not merely a special case in strength:
§4's threshold `d²S² < m²·crossForm` is sharper than the general one, which pays a factor four and
asks `Δ ≤ m²` besides. Use this on a regular graph, §10 on any graph. -/
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

/-- The Green function with the GLOBAL constant mode removed. `green`'s row sums are all `m⁻²`
(`GreenExpansion.green_mulVec_one`), so subtracting `(m²·|V|)⁻¹` times the all-ones matrix leaves a
matrix whose rows sum to zero (`greenHat_row_sum`).

**THIS SENTENCE ONCE CONTINUED "— and carries none of the `m⁻²` divergence", AND THAT CLAUSE IS
FALSE** (`ERRATUM 152`, §7). Removing the all-ones matrix removes one line out of the Laplacian's
`0`-eigenspace, and that eigenspace has dimension equal to the number of components. On two points
with no edge `greenHat 0 0 = (2m²)⁻¹`, which is unbounded (`greenHat_bot_two_unbounded`) — while
its rows still sum to zero, so the counterexample refutes the sentence and none of the theorems. -/
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

So the slack of `GreenExpansion.reflectionPositive_iff_slack`, which is `(γ/m²)·(∑_H c)²`, **is
exactly zero at every witness of the failure it would have to excuse.** Both facts are exact and
neither is an estimate. **What this does NOT say is that the remaining form is tame at small
mass** — §7 exhibits a graph where the hat entries are unbounded as the mass falls.

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

/-! ## 7. And the sentence §6 was written with is FALSE — `greenHat` does not remove the divergence

`ERRATUM 152`. §6's definition was introduced with the words *"leaves a matrix that annihilates
constants — and carries none of the `m⁻²` divergence."* **The clause after the dash is not proved
and is not true.** What is proved is an algebraic identity and a row sum; boundedness as `m → 0` is
a spectral statement and it fails as soon as the graph is disconnected, because then the
`0`-eigenspace of the Laplacian has dimension greater than one and `allOnes` projects onto only a
line inside it.

The witness is as small as it can be: **two vertices and no edge.** There `green = m⁻²·1`, so
`greenHat 0 0 = m⁻² − (2m²)⁻¹ = (2m²)⁻¹`, which is unbounded — while its rows still sum to zero,
exactly as `greenHat_row_sum` says. So the counterexample is consistent with everything §6 proves
and refutes only the sentence §6 was described with.

**What survives untouched:** `reflectedForm_split`, `reflectedForm_eq_hat_of_sum_zero` and
`hcross_failure_is_orthogonal_to_the_slack` are identities and are unaffected. What is withdrawn is
the reading that the hat form is *tame* at small mass. It is not, in general.
-/

section Erratum152

open GreenExpansion

/-- The empty graph on two points: two vertices, no edge, so two components. -/
theorem massive_bot_two (m : ℝ) :
    GraphLaplacian.massive (⊥ : SimpleGraph (Fin 2)) m
      = (m ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hlap : (⊥ : SimpleGraph (Fin 2)).lapMatrix ℝ = 0 := by
    have hdeg : ∀ v : Fin 2, (⊥ : SimpleGraph (Fin 2)).degree v = 0 := by
      intro v
      simp [SimpleGraph.degree, SimpleGraph.neighborFinset, SimpleGraph.neighborSet]
    ext i j
    simp only [SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix,
      Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply, Matrix.zero_apply]
    by_cases hij : i = j
    · rw [if_pos hij, hdeg i, if_neg (by rw [hij]; exact fun hc => hc.ne rfl)]
      norm_num
    · rw [if_neg hij, if_neg (fun hc : (⊥ : SimpleGraph (Fin 2)).Adj i j => hc)]
      norm_num
  ext i j
  rw [GraphLaplacian.massive, hlap]
  by_cases hij : i = j <;> simp [hij]

theorem green_bot_two {m : ℝ} (hm : m ≠ 0) :
    GraphLaplacian.green (⊥ : SimpleGraph (Fin 2)) m
      = (m ^ 2)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hpos : (0 : ℝ) < m ^ 2 := by positivity
  rw [GraphLaplacian.green, massive_bot_two]
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

/-- **THE COUNTEREXAMPLE.** On the two-point empty graph the hat entry is `(2m²)⁻¹`, which is not
bounded as the mass falls — so subtracting the all-ones matrix does **not** remove the `m⁻²`
divergence. -/
theorem greenHat_bot_two {m : ℝ} (hm : m ≠ 0) :
    greenHat (⊥ : SimpleGraph (Fin 2)) m 0 0 = (2 * m ^ 2)⁻¹ := by
  have hpos : (0 : ℝ) < m ^ 2 := by positivity
  rw [greenHat, Matrix.sub_apply, green_bot_two hm]
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, allOnes, smul_eq_mul, mul_one,
    Fintype.card_fin]
  rw [show ((2 : ℕ) : ℝ) = 2 from by norm_num]
  field_simp
  ring

/-- **AND SO IT IS UNBOUNDED**, stated without limits: past every bound there is a nonzero mass at
which the hat entry exceeds it. -/
theorem greenHat_bot_two_unbounded (B : ℝ) :
    ∃ m : ℝ, m ≠ 0 ∧ B < greenHat (⊥ : SimpleGraph (Fin 2)) m 0 0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (2 * B) 2)
  have h2 : (2 : ℝ) < n := lt_of_le_of_lt (le_max_right (2 * B) 2) hn
  have hB2 : 2 * B < n := lt_of_le_of_lt (le_max_left (2 * B) 2) hn
  have hn0 : (0 : ℝ) < n := lt_trans (by norm_num) h2
  have hne : ((n : ℝ))⁻¹ ≠ 0 := by positivity
  refine ⟨(n : ℝ)⁻¹, hne, ?_⟩
  rw [greenHat_bot_two hne]
  have hval : (2 * ((n : ℝ)⁻¹) ^ 2)⁻¹ = (n : ℝ) ^ 2 / 2 := by
    field_simp
  rw [hval]
  nlinarith [hB2, h2, hn0]

/-- The rows still sum to zero there, so the counterexample refutes the sentence and not the
theorem. -/
theorem greenHat_bot_two_row_sum {m : ℝ} (hm : m ≠ 0) :
    ∑ q, greenHat (⊥ : SimpleGraph (Fin 2)) m 0 q = 0 :=
  greenHat_row_sum hm (by simp) 0

end Erratum152

/-! ## 8. The same theorem with REGULARITY REMOVED — queue item 4, on the file's own §4

§§1–5 assume the graph is `d`-regular, because `GreenExpansion.sq_mul_reflectedForm` does. That
file's §8 already removed regularity from the identity itself
(`GreenExpansion.green_mirror_general`): at a mirrored entry the Green function is the cross-cut
adjacency divided by `(deg p + m²)(deg q + m²)`, plus a remainder, and `IsRefl.degree` is what makes
the two weights match. **The large-mass argument runs on that identity verbatim once the remainder
is bounded, and the bound needs only a degree ceiling.**

The one change of shape: the leading term is now WEIGHTED, so the witness has to be reweighted. If
`crossForm u > 0` then the vector `c p = u p · (deg p + m²)` — supported on the half exactly when
`u` is — has `reflectedForm c = −crossForm u + remainder`, **exactly**, and the remainder is
`O(m⁻⁶)` against a leading term of order one.

**The general theorem is WEAKER on regular graphs than §4 is**, and that is stated rather than
hidden. §4's threshold, in the `ℓ¹` mass `S = ∑_H |c|` of the witness, is `d²S² < m²·crossForm`.
This one is stated in the *weighted* mass `S(m) = ∑_H |u p|(deg p + m²)`, which itself grows like
`m²`, so the two cannot be compared as written. **The comparison that means anything is the two
theorems on the SAME graph**, and §9 does it: on `IndefiniteCoupling.crossGraph`, which is
`1`-regular so both apply, §4 gives `m² > 2` and §8 gives `m² > 4`
(`crossGraph_not_reflectionPositive_general_of_four_lt`). **A factor of two is the honest price of
removing the hypothesis**, and it buys graphs §4 cannot be stated on at all.

§9 exhibits one, `stepGraph`, and exhibits it because the first draft of this paragraph asserted
one *without checking* — it named the box, on the true grounds that the box is not regular at its
boundary. That was false: `CrossBlockStructure.isCrossBlock_box` makes the box a block cut at every
side, so `hcross` HOLDS on the box and this theorem's hypothesis is unsatisfiable there. `ERRATA`
153.
-/

section General

open GreenExpansion

variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

omit [DecidableEq V] in
/-- Column sums of the adjacency matrix are the degree, `A` being symmetric. -/
theorem adj_col_sum (q : V) : ∑ s, G.adjMatrix ℝ s q = (G.degree q : ℝ) := by
  have hsym : ∀ s t : V, G.adjMatrix ℝ s t = G.adjMatrix ℝ t s := by
    intro s t
    simp only [SimpleGraph.adjMatrix_apply]
    by_cases hh : G.Adj s t
    · rw [if_pos hh, if_pos hh.symm]
    · rw [if_neg hh, if_neg (fun hc => hh hc.symm)]
  rw [Finset.sum_congr rfl fun s _ => hsym s q, adj_row_sum q]

theorem Dinv_diag_le (hm : m ≠ 0) (s : V) : Dinv G m s s ≤ (m ^ 2)⁻¹ := by
  have hpos : (0 : ℝ) < m ^ 2 := by positivity
  have hdeg : (0 : ℝ) ≤ (G.degree s : ℝ) := Nat.cast_nonneg _
  rw [Dinv, Matrix.diagonal_apply_eq]
  gcongr
  linarith

theorem Dinv_diag_nonneg (hm : m ≠ 0) (s : V) : 0 ≤ Dinv G m s s := by
  rw [Dinv, Matrix.diagonal_apply_eq]
  exact le_of_lt (inv_pos.mpr (weight_pos hm s))

/-- The weighted middle factor, off the mirror: `Dinv · A · Dinv` is diagonal-weighted adjacency. -/
theorem Dinv_adj_Dinv_apply (s q : V) :
    (Dinv G m * G.adjMatrix ℝ * Dinv G m) s q
      = Dinv G m s s * G.adjMatrix ℝ s q * Dinv G m q q := by
  rw [Matrix.mul_assoc, Dinv, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  ring

/-- One matrix product in: `green · A` is bounded by `m⁻²` times the degree. -/
theorem greenA_abs_le (hm : m ≠ 0) (x s : V) :
    |(GraphLaplacian.green G m * G.adjMatrix ℝ) x s| ≤ (m ^ 2)⁻¹ * (G.degree s : ℝ) := by
  rw [Matrix.mul_apply]
  calc |∑ r, GraphLaplacian.green G m x r * G.adjMatrix ℝ r s|
      ≤ ∑ r, |GraphLaplacian.green G m x r * G.adjMatrix ℝ r s| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r, (m ^ 2)⁻¹ * G.adjMatrix ℝ r s := by
        refine Finset.sum_le_sum fun r _ => ?_
        have hA : 0 ≤ G.adjMatrix ℝ r s := by
          simp only [SimpleGraph.adjMatrix_apply]; split_ifs <;> norm_num
        rw [abs_mul, abs_of_nonneg hA]
        exact mul_le_mul_of_nonneg_right (green_abs_le hm x r) hA
    _ = (m ^ 2)⁻¹ * (G.degree s : ℝ) := by rw [← Finset.mul_sum, adj_col_sum s]

/-- **THE GENERAL REMAINDER'S ENTRIES ARE `O(m⁻⁶)`**, with a degree ceiling and nothing else. -/
theorem generalRemainder_abs_le (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) (x q : V) :
    |(GraphLaplacian.green G m * G.adjMatrix ℝ * Dinv G m * G.adjMatrix ℝ * Dinv G m) x q|
      ≤ ((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) ^ 2 := by
  have hinvpos : (0 : ℝ) ≤ (m ^ 2)⁻¹ := by positivity
  have hD : (0 : ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _
  have hassoc : GraphLaplacian.green G m * G.adjMatrix ℝ * Dinv G m * G.adjMatrix ℝ * Dinv G m
      = (GraphLaplacian.green G m * G.adjMatrix ℝ) * (Dinv G m * G.adjMatrix ℝ * Dinv G m) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc, Matrix.mul_apply]
  have hterm : ∀ s : V, |(GraphLaplacian.green G m * G.adjMatrix ℝ) x s
      * (Dinv G m * G.adjMatrix ℝ * Dinv G m) s q|
      ≤ ((m ^ 2)⁻¹ * (Δ : ℝ)) * ((m ^ 2)⁻¹ * G.adjMatrix ℝ s q * (m ^ 2)⁻¹) := by
    intro s
    have hA : 0 ≤ G.adjMatrix ℝ s q := by
      simp only [SimpleGraph.adjMatrix_apply]; split_ifs <;> norm_num
    have h1 : |(GraphLaplacian.green G m * G.adjMatrix ℝ) x s| ≤ (m ^ 2)⁻¹ * (Δ : ℝ) :=
      le_trans (greenA_abs_le hm x s)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hΔ s) hinvpos)
    have h2 : |(Dinv G m * G.adjMatrix ℝ * Dinv G m) s q|
        ≤ (m ^ 2)⁻¹ * G.adjMatrix ℝ s q * (m ^ 2)⁻¹ := by
      rw [Dinv_adj_Dinv_apply, abs_of_nonneg
        (mul_nonneg (mul_nonneg (Dinv_diag_nonneg hm s) hA) (Dinv_diag_nonneg hm q))]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (Dinv_diag_le hm s) hA) (Dinv_diag_le hm q)
        (Dinv_diag_nonneg hm q) (mul_nonneg hinvpos hA)
    rw [abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hinvpos hD)
  calc |∑ s, (GraphLaplacian.green G m * G.adjMatrix ℝ) x s
          * (Dinv G m * G.adjMatrix ℝ * Dinv G m) s q|
      ≤ ∑ s, |(GraphLaplacian.green G m * G.adjMatrix ℝ) x s
          * (Dinv G m * G.adjMatrix ℝ * Dinv G m) s q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, ((m ^ 2)⁻¹ * (Δ : ℝ)) * ((m ^ 2)⁻¹ * G.adjMatrix ℝ s q * (m ^ 2)⁻¹) :=
        Finset.sum_le_sum fun s _ => hterm s
    _ = ((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) * ∑ s, G.adjMatrix ℝ s q := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
    _ ≤ ((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) * (Δ : ℝ) := by
        rw [adj_col_sum q]
        have : (G.degree q : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ q
        have hc : (0 : ℝ) ≤ ((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left this hc
    _ = ((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) ^ 2 := by ring

/-- The cross-cut adjacency summed against a vector is minus the coupling form. -/
theorem sum_crossAdj_eq (hM : IsMirrorHalf θ H Mir) (m : ℝ) (u : V → ℝ) :
    ∑ p ∈ H, ∑ q ∈ H, u p * u q * CrossFormMatrix.crossAdj G θ p q = - crossForm G m θ H u := by
  rw [crossForm_eq_neg_adj hM m u, neg_neg]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
    rw [CrossFormMatrix.crossAdj]

/-- **THE LARGE-MASS CONVERSE, WITH REGULARITY REMOVED.** The witness has to be reweighted by the
per-vertex weights the general identity carries — `c p = u p · (deg p + m²)` — and then the leading
term is *exactly* `−crossForm u`, with a remainder that is `O(m⁻⁶)`. Only a degree ceiling is
assumed, and every finite graph has one. -/
theorem reflectedForm_neg_of_crossForm_pos_general (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ)
    {u : V → ℝ} (hus : ∀ p, p ∉ H → u p = 0)
    (hbig : ((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) ^ 2
              * (∑ p ∈ H, |u p * ((G.degree p : ℝ) + m ^ 2)|) ^ 2 < crossForm G m θ H u) :
    GraphReflection.reflectedForm G m θ (fun p => u p * ((G.degree p : ℝ) + m ^ 2)) < 0 := by
  classical
  set c : V → ℝ := fun p => u p * ((G.degree p : ℝ) + m ^ 2) with hcdef
  have hcs : ∀ p, p ∉ H → c p = 0 := fun p hp => by rw [hcdef]; simp [hus p hp]
  set R : Matrix V V ℝ :=
    GraphLaplacian.green G m * G.adjMatrix ℝ * Dinv G m * G.adjMatrix ℝ * Dinv G m with hRdef
  -- the exact split, term by term
  have hterm : ∀ p ∈ H, ∀ q ∈ H, c p * c q * GraphLaplacian.green G m (θ p) q
      = u p * u q * CrossFormMatrix.crossAdj G θ p q + c p * c q * R (θ p) q := by
    intro p hp q hq
    rw [green_mirror_general hM h hm hp hq, ← hRdef, hcdef]
    have hp0 : ((G.degree p : ℝ) + m ^ 2) ≠ 0 := ne_of_gt (weight_pos hm p)
    have hq0 : ((G.degree q : ℝ) + m ^ 2) ≠ 0 := ne_of_gt (weight_pos hm q)
    field_simp
  have hsplit : GraphReflection.reflectedForm G m θ c
      = - crossForm G m θ H u + ∑ p ∈ H, ∑ q ∈ H, c p * c q * R (θ p) q := by
    rw [reflectedForm_eq_sum_half hcs,
      Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => hterm p hp q hq,
      Finset.sum_congr rfl fun p _ => Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_crossAdj_eq hM m u]
  -- and the remainder is small
  have hrem : |∑ p ∈ H, ∑ q ∈ H, c p * c q * R (θ p) q|
      ≤ ((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) ^ 2 * (∑ p ∈ H, |c p|) ^ 2 := by
    have hstep : ∀ p ∈ H, |∑ q ∈ H, c p * c q * R (θ p) q|
        ≤ |c p| * (((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) ^ 2) * ∑ q ∈ H, |c q| := by
      intro p _
      calc |∑ q ∈ H, c p * c q * R (θ p) q|
          ≤ ∑ q ∈ H, |c p * c q * R (θ p) q| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ q ∈ H, |c p| * |c q| * (((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) ^ 2) := by
            refine Finset.sum_le_sum fun q _ => ?_
            rw [abs_mul, abs_mul]
            exact mul_le_mul_of_nonneg_left (generalRemainder_abs_le hm hΔ (θ p) q)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = |c p| * (((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) ^ 2) * ∑ q ∈ H, |c q| := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun q _ => by ring
    calc |∑ p ∈ H, ∑ q ∈ H, c p * c q * R (θ p) q|
        ≤ ∑ p ∈ H, |∑ q ∈ H, c p * c q * R (θ p) q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ H, |c p| * (((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) ^ 2) * ∑ q ∈ H, |c q| :=
          Finset.sum_le_sum hstep
      _ = ((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) ^ 2 * (∑ p ∈ H, |c p|) ^ 2 := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          ring
  rw [hsplit]
  have := abs_le.mp hrem
  linarith [this.1, this.2, hbig]

/-- The same, as a failure of the estate's own predicate. -/
theorem not_reflectionPositive_of_crossForm_pos_general (hM : IsMirrorHalf θ H Mir)
    (h : IsRefl G θ) (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ)
    {u : V → ℝ} (hus : ∀ p, p ∉ H → u p = 0)
    (hbig : ((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) ^ 2
              * (∑ p ∈ H, |u p * ((G.degree p : ℝ) + m ^ 2)|) ^ 2 < crossForm G m θ H u) :
    ¬ GraphReflection.ReflectionPositive G m θ H := by
  intro hRP
  have hcs : ∀ p, p ∉ H → u p * ((G.degree p : ℝ) + m ^ 2) = 0 := fun p hp => by
    simp [hus p hp]
  exact absurd (hRP _ hcs)
    (not_le.mpr (reflectedForm_neg_of_crossForm_pos_general hM h hm hΔ hus hbig))

end General


/-! ## 9. Non-vacuity for §8, on a graph that is genuinely NOT regular

§8 is only worth having if its hypotheses are satisfiable somewhere §4's are not, and the first
draft of §8's header asserted that without checking it — it named *the box*, on the true grounds
that the box is not regular at its boundary. **That was false**, and `CrossBlockStructure` already
contained the refutation: `isCrossBlock_box` says the box cut is a block cut at *every* side and
every dimension, so by `hcross_iff_isCrossBlock` the box satisfies `hcross`, `crossForm ≤ 0`
everywhere on it, and §8's hypothesis `0 < crossForm u` is **unsatisfiable** there. §8 says nothing
whatever about the box. `ERRATA` 153.

So here is a witness that is checked instead of asserted. `stepGraph` is two three-vertex paths,
`2 – 0 – 4` and `1 – 3 – 5`, exchanged by `p ↦ p + 3`:

* it is **not regular** — `stepGraph_degree_zero` is `2` and `stepGraph_degree_one` is `1`, so
  `stepGraph_not_regular`, and §4 cannot be *stated* here, let alone applied;
* it has a degree ceiling of `2`, which is all §8 asks;
* and it fails `hcross` at `us = (1, −1, 0, …)`, with `crossForm = 2`, because `0` is joined to
  `σ 1 = 4` and `1` to `σ 0 = 3` while neither is joined to its own mirror — the same
  intransitive triple that refutes `crossGraph`, now carrying a pendant that breaks the regularity.

Hence `stepGraph_not_reflectionPositive_of_large`: reflection positivity fails on `stepGraph` for
every `m² > 100` — a constant with a clean arithmetic certificate rather than a sharp one; §8's
hypothesis here is `2(3 + 2m²)² < (m²)³`, which first holds near `m² = 11`, and nothing here
computes the boundary. Unlike §5 — where the general theorem was deliberately checked against a case
already known, and came out strictly weaker — no other route in the estate reaches this graph. That
is a checkable claim and it was checked: every theorem in `paper_f` whose *conclusion* is a failure
of `ReflectionPositive` is either about `IndefiniteCoupling.crossGraph` by name
(`IndefiniteCoupling.not_reflectionPositive`, `GreenExpansion` §7, `CrossBlockStructure` §5) or
carries `IsRegularOfDegree` as a hypothesis (§4 above); the one remaining occurrence,
`CrossFormMatrix.not_converse_of_mass_dependent`, takes such a failure as *input*. `stepGraph` is
regular of no degree, so none of them applies.

Two things are deliberately NOT claimed. This is a *large-mass* statement, so what happens on
`stepGraph` at small mass is exactly as open as the general question in §6. And `stepGraph` is two
paths — a hand computation of its Green function, in the style `IndefiniteCoupling` does for
`crossGraph`, would very likely settle it at every mass. §8 is the first route *in the estate* that
reaches it, which is a smaller claim than being the only possible one.
-/

section NonRegularWitness

open GreenExpansion CrossBlockStructure

/-- **TWO THREE-VERTEX PATHS, EXCHANGED BY `+3`.** Adjacency is one arithmetic fact: the labels
differ by `2` and at least one of them is a path centre (`0` or `3`, the multiples of three). That
makes `2 – 0 – 4` and `1 – 3 – 5` edges while `1 – 5` and `2 – 4`, which also differ by `2`, are
not; and it makes the two centres have degree `2` against the leaves' `1`. -/
def stepGraph : SimpleGraph (Fin 6) where
  Adj p q := (p - q = 2 ∨ q - p = 2) ∧ (p.val % 3 = 0 ∨ q.val % 3 = 0)
  symm := by rintro p q ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩
  loopless := ⟨by
    intro p hp
    have h : (0 : Fin 6) = 2 := by rcases hp.1 with h | h <;> rwa [sub_self] at h
    exact absurd h (by decide)⟩

instance : DecidableRel stepGraph.Adj := fun p q =>
  inferInstanceAs (Decidable ((p - q = 2 ∨ q - p = 2) ∧ (p.val % 3 = 0 ∨ q.val % 3 = 0)))

/-- The reflection: add three, which swaps `0 ↔ 3`, `1 ↔ 4`, `2 ↔ 5` and carries one path to the
other. -/
def sigma6 : Fin 6 ≃ Fin 6 := Equiv.addRight 3

@[simp] theorem sigma6_apply (p : Fin 6) : sigma6 p = p + 3 := rfl

/-- The half: one whole path. -/
def Hs : Finset (Fin 6) := {0, 1, 2}

/-- The refuting vector — the same opposite signs as `IndefiniteCoupling.wpos`, now with a third
coordinate on the half that it does not need and does not use. -/
def us : Fin 6 → ℝ := ![1, -1, 0, 0, 0, 0]

theorem isRefl_sigma6 : GraphReflection.IsRefl stepGraph sigma6 where
  invol := by intro p; revert p; decide
  adj := by intro p q; revert p q; decide

theorem isMirrorHalf_Hs : IsMirrorHalf sigma6 Hs (∅ : Finset (Fin 6)) where
  fixed := by decide
  disj := by decide
  split := by decide

/-- The half has three sites, so every sum over it is three terms. -/
theorem sum_Hs (f : Fin 6 → ℝ) : ∑ p ∈ Hs, f p = f 0 + f 1 + f 2 := by
  rw [show Hs = ({0, 1, 2} : Finset (Fin 6)) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-! ### The graph is not regular -/

theorem stepGraph_degree_zero : stepGraph.degree 0 = 2 := by decide

theorem stepGraph_degree_one : stepGraph.degree 1 = 1 := by decide

/-- **AND SO §4 DOES NOT APPLY HERE AT ALL.** -/
theorem stepGraph_not_regular : ¬ ∃ d : ℕ, stepGraph.IsRegularOfDegree d := by
  rintro ⟨d, hd⟩
  have h0 := hd 0
  have h1 := hd 1
  rw [stepGraph_degree_zero] at h0
  rw [stepGraph_degree_one] at h1
  omega

/-- The degree ceiling §8 asks for. -/
theorem stepGraph_degree_le (v : Fin 6) : stepGraph.degree v ≤ 2 := by revert v; decide

/-! ### And it fails the coupling hypothesis -/

/-- The cut relation on `stepGraph` is intransitive at `(0, 1, 0)`, exactly as on `crossGraph`. -/
theorem not_isCrossBlock_stepGraph : ¬ IsCrossBlock stepGraph sigma6 Hs := by decide

/-- **THE COUPLING IS `+2` HERE TOO.** Only the two off-diagonal terms survive: `0` is joined to
`σ 1 = 4` and `1` to `σ 0 = 3`, while `0` is not joined to `σ 0 = 3` nor `1` to `σ 1 = 4`. The
pendant sites contribute nothing — `us` vanishes at `2`, and `2` is joined to no mirror at all. -/
theorem crossForm_step_pos (m : ℝ) : crossForm stepGraph m sigma6 Hs us = 2 := by
  have h := sum_crossAdj_eq (G := stepGraph) (θ := sigma6) (H := Hs)
    (Mir := (∅ : Finset (Fin 6))) isMirrorHalf_Hs m us
  have hs : ∑ p ∈ Hs, ∑ q ∈ Hs, us p * us q * CrossFormMatrix.crossAdj stepGraph sigma6 p q
      = -2 := by
    simp only [sum_Hs, CrossFormMatrix.crossAdj, sigma6_apply]
    norm_num [us, show ((1 : Fin 6) + 3) = 4 from rfl, show ((2 : Fin 6) + 3) = 5 from rfl,
      show ((0 : Fin 6) + 3) = 3 from rfl,
      show ¬ stepGraph.Adj 0 3 by decide, show stepGraph.Adj 0 4 by decide,
      show ¬ stepGraph.Adj 0 5 by decide, show stepGraph.Adj 1 3 by decide,
      show ¬ stepGraph.Adj 1 4 by decide, show ¬ stepGraph.Adj 1 5 by decide,
      show ¬ stepGraph.Adj 2 3 by decide, show ¬ stepGraph.Adj 2 4 by decide,
      show ¬ stepGraph.Adj 2 5 by decide]
  rw [hs] at h
  linarith

theorem us_supported : ∀ p, p ∉ Hs → us p = 0 := by
  intro p hp
  fin_cases p <;> simp_all [us, Hs]

/-- The `ℓ¹` mass §8's threshold is measured against, computed exactly: the weights are the two
degrees, `2` at the centre and `1` at the leaf. -/
theorem us_weighted_sum (m : ℝ) :
    ∑ p ∈ Hs, |us p * ((stepGraph.degree p : ℝ) + m ^ 2)| = 3 + 2 * m ^ 2 := by
  have hm : (0 : ℝ) ≤ m ^ 2 := sq_nonneg m
  have e0 : us 0 = 1 := by simp [us]
  have e1 : us 1 = -1 := by simp [us]
  have e2 : us 2 = 0 := by simp [us]
  rw [sum_Hs (fun p => |us p * ((stepGraph.degree p : ℝ) + m ^ 2)|), e0, e1, e2,
    stepGraph_degree_zero, stepGraph_degree_one, show stepGraph.degree 2 = 1 by decide]
  push_cast
  rw [one_mul, zero_mul, abs_zero,
    abs_of_nonneg (show (0 : ℝ) ≤ 2 + m ^ 2 by linarith),
    show (-1 : ℝ) * (1 + m ^ 2) = -(1 + m ^ 2) by ring, abs_neg,
    abs_of_nonneg (show (0 : ℝ) ≤ 1 + m ^ 2 by linarith)]
  ring

/-! ### The like-for-like cost of removing the hypothesis, on the one graph where both apply -/

open IndefiniteCoupling in
/-- The weighted `ℓ¹` mass of `crossGraph`'s refuting vector: the graph is `1`-regular, so every
weight is `1 + m²`. -/
theorem wpos_weighted_sum (m : ℝ) :
    ∑ p ∈ Hh, |wpos p * ((crossGraph.degree p : ℝ) + m ^ 2)| = 2 * (1 + m ^ 2) := by
  have hm : (0 : ℝ) ≤ m ^ 2 := sq_nonneg m
  rw [show Hh = ({0, 1} : Finset (Fin 4)) from rfl,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    show wpos 0 = 1 by simp [wpos], show wpos 1 = -1 by simp [wpos],
    degree_eq_one, degree_eq_one]
  push_cast
  rw [one_mul, abs_of_nonneg (show (0 : ℝ) ≤ 1 + m ^ 2 by linarith),
    show (-1 : ℝ) * (1 + m ^ 2) = -(1 + m ^ 2) by ring, abs_neg,
    abs_of_nonneg (show (0 : ℝ) ≤ 1 + m ^ 2 by linarith)]
  ring

open IndefiniteCoupling in
/-- **THE GENERAL THEOREM ON `crossGraph`, WHICH IS WHERE THE COST OF REMOVING THE HYPOTHESIS CAN
ACTUALLY BE READ.** §5 compares §4's threshold on this graph with `IndefiniteCoupling`'s hand solve.
The comparison that measures *what regularity was buying* is a different one: **§4 and §8 on the
SAME graph.** §4 gives `m² > 2` (`crossGraph_not_reflectionPositive_of_two_lt`); §8 gives `m² > 4`.
**A factor of two, and that is the honest price** — not the ratio between §4 here and §8 on the
six-vertex graph below, which are different graphs and measure nothing. -/
theorem crossGraph_not_reflectionPositive_general_of_four_lt {m : ℝ} (hm : 4 < m ^ 2) :
    ¬ GraphReflection.ReflectionPositive crossGraph m rho Hh := by
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hm
    norm_num at hm
  have ht : (0 : ℝ) < m ^ 2 := by linarith
  refine not_reflectionPositive_of_crossForm_pos_general (u := wpos) (Δ := 1)
    isMirrorHalf_Hh isRefl_rho hm0 (fun v => le_of_eq (degree_eq_one v))
    CrossBlockStructure.wpos_supported ?_
  rw [crossForm_pos, wpos_weighted_sum]
  have hcube : (0 : ℝ) < (m ^ 2) ^ 3 := by positivity
  have hrw : (m ^ 2)⁻¹ ^ 3 * ((1 : ℕ) : ℝ) ^ 2 * (2 * (1 + m ^ 2)) ^ 2
      = (4 * (1 + m ^ 2) ^ 2) / ((m ^ 2) ^ 3) := by
    push_cast
    rw [inv_pow]
    field_simp
    ring
  rw [hrw, div_lt_iff₀ hcube]
  nlinarith [ht, mul_pos (show (0 : ℝ) < m ^ 2 - 4 by linarith) ht]

/-- **§8 FIRES ON A GRAPH §4 CANNOT SEE.** The constant `100` is a value with a clean arithmetic
certificate, **not this theorem's threshold**: §8's hypothesis here is `2(3 + 2m²)² < (m²)³`, which
first holds somewhere near `m² = 11`. Nothing below computes the sharp boundary and nothing claims
to. -/
theorem stepGraph_not_reflectionPositive_of_large {m : ℝ} (hm : 100 < m ^ 2) :
    ¬ GraphReflection.ReflectionPositive stepGraph m sigma6 Hs := by
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hm
    norm_num at hm
  refine not_reflectionPositive_of_crossForm_pos_general (u := us) (Δ := 2)
    isMirrorHalf_Hs isRefl_sigma6 hm0 stepGraph_degree_le us_supported ?_
  rw [crossForm_step_pos, us_weighted_sum]
  have ht : (0 : ℝ) < m ^ 2 := by linarith
  have hcube : (0 : ℝ) < (m ^ 2) ^ 3 := by positivity
  have hrw : (m ^ 2)⁻¹ ^ 3 * ((2 : ℕ) : ℝ) ^ 2 * (3 + 2 * m ^ 2) ^ 2
      = (4 * (3 + 2 * m ^ 2) ^ 2) / ((m ^ 2) ^ 3) := by
    push_cast
    rw [inv_pow]
    field_simp
    ring
  rw [hrw, div_lt_iff₀ hcube]
  nlinarith [hm, ht, mul_pos (show (0 : ℝ) < m ^ 2 - 100 by linarith) ht]

end NonRegularWitness

/-! ## 10. And so the BICONDITIONAL holds with no hypothesis on the graph at all

`PROOF_STRATEGY` §3: the moment a rung lands, re-attempt the next one before returning to the
queue. §8 removed regularity from one direction; this section removes it from the other, and then
discharges the degree ceiling internally — **because every finite graph has one.**

`reflectionPositive_arbitrarily_large_iff_hcross_general` is therefore the file's headline with its
hypotheses gone: on **every** finite graph carrying a mirror reflection, being reflection positive
at arbitrarily large masses is **exactly** the coupling hypothesis. §4's biconditional is the
special case `Δ = d`, and is now subsumed — what §4 keeps that this does not is the sharp explicit
threshold `d²S² < m²·crossForm`, against this section's `4Δ²S² < m²·crossForm` and `Δ ≤ m²`.
Neither statement is deleted; the file records which is stronger in which respect.

**This does not move `WALLS` W1.** The remaining leg there wants the converse at a FIXED mass, and
every threshold here is witness-dependent. What has changed since §4 is only the class of graphs
the large-mass half applies to, which is now all of them.
-/

section GeneralBiconditional

open GreenExpansion

variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

omit [DecidableEq V] in
/-- Once the mass beats the degree ceiling, the weighted `ℓ¹` mass the general threshold is
measured in is at most twice the plain one. -/
theorem weighted_sum_le {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) (hmΔ : (Δ : ℝ) ≤ m ^ 2)
    (u : V → ℝ) :
    ∑ p ∈ H, |u p * ((G.degree p : ℝ) + m ^ 2)| ≤ 2 * m ^ 2 * ∑ p ∈ H, |u p| := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have hdp : ((G.degree p : ℝ)) ≤ (Δ : ℝ) := by exact_mod_cast hΔ p
  have hnn : (0 : ℝ) ≤ (G.degree p : ℝ) + m ^ 2 := by positivity
  rw [abs_mul, abs_of_nonneg hnn]
  have : ((G.degree p : ℝ) + m ^ 2) ≤ 2 * m ^ 2 := by linarith
  calc |u p| * ((G.degree p : ℝ) + m ^ 2) ≤ |u p| * (2 * m ^ 2) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = 2 * m ^ 2 * |u p| := by ring

/-- **THE THRESHOLD IN THE PLAIN `ℓ¹` MASS.** §8's hypothesis is stated in the weighted mass, which
itself grows like `m²` and so is awkward to quantify over. This converts it into a condition on the
*unweighted* mass `S = ∑_H |u|`, at the cost of a factor four: `4Δ²S² < m²·crossForm u` and
`Δ ≤ m²` suffice. -/
theorem threshold_of_plain (hm : 0 < m ^ 2) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ)
    (hmΔ : (Δ : ℝ) ≤ m ^ 2) {u : V → ℝ}
    (hbig : 4 * (Δ : ℝ) ^ 2 * (∑ p ∈ H, |u p|) ^ 2 < m ^ 2 * crossForm G m θ H u) :
    ((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) ^ 2 * (∑ p ∈ H, |u p * ((G.degree p : ℝ) + m ^ 2)|) ^ 2
      < crossForm G m θ H u := by
  set S : ℝ := ∑ p ∈ H, |u p| with hSdef
  set T : ℝ := ∑ p ∈ H, |u p * ((G.degree p : ℝ) + m ^ 2)| with hTdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hT : 0 ≤ T := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hTle : T ≤ 2 * m ^ 2 * S := weighted_sum_le hΔ hmΔ u
  have hsq : T ^ 2 ≤ (2 * m ^ 2 * S) ^ 2 := by
    nlinarith [hT, hTle]
  have hcoef : (0 : ℝ) ≤ ((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) ^ 2 := by positivity
  have hstep : ((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) ^ 2 * T ^ 2
      ≤ ((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) ^ 2 * (2 * m ^ 2 * S) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hcoef
  have hclose : ((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) ^ 2 * (2 * m ^ 2 * S) ^ 2
      = (4 * (Δ : ℝ) ^ 2 * S ^ 2) / m ^ 2 := by
    field_simp
    ring
  rw [hclose] at hstep
  have hfin : (4 * (Δ : ℝ) ^ 2 * S ^ 2) / m ^ 2 < crossForm G m θ H u := by
    rw [div_lt_iff₀ hm]
    linarith [hbig]
  linarith [hstep, hfin]

omit [DecidableEq V] in
/-- Every finite graph has a degree ceiling, and the crudest one will do. -/
theorem degree_le_card (v : V) : G.degree v ≤ Fintype.card V :=
  Finset.card_le_univ _

/-- **THE WALL'S CONVERSE AT LARGE MASS, WITH NO HYPOTHESIS ON THE GRAPH.** §4 asked the graph to
be regular; nothing here does. The conclusion names no mass because `crossForm` names none
(`GraphMirrorReflection.crossForm_mass_independent`). -/
theorem hcross_of_reflectionPositive_arbitrarily_large_general (hM : IsMirrorHalf θ H Mir)
    (h : IsRefl G θ)
    (hRP : ∀ M : ℝ, ∃ m' : ℝ, M < m' ∧ m' ≠ 0 ∧ GraphReflection.ReflectionPositive G m' θ H)
    (m₀ : ℝ) (w : V → ℝ) :
    crossForm G m₀ θ H w ≤ 0 := by
  classical
  by_contra hc
  rw [not_le] at hc
  set Δ : ℕ := Fintype.card V with hΔdef
  have hΔ : ∀ v : V, G.degree v ≤ Δ := fun v => degree_le_card v
  set u : V → ℝ := fun i => if i ∈ H then w i else 0 with hudef
  have hus : ∀ p, p ∉ H → u p = 0 := fun p hp => by rw [hudef]; simp [hp]
  have hupos : ∀ m' : ℝ, 0 < crossForm G m' θ H u := by
    intro m'
    rw [hudef, crossForm_restrict w, crossForm_mass_independent hM m' m₀ w]
    exact hc
  set S : ℝ := ∑ p ∈ H, |u p| with hSdef
  set K : ℝ := 4 * (Δ : ℝ) ^ 2 * S ^ 2 / crossForm G m₀ θ H u with hKdef
  obtain ⟨m', hm'gt, hm'ne, hm'RP⟩ := hRP (max (max 1 (Δ : ℝ)) K)
  have h1 : (1 : ℝ) < m' := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hm'gt
  have hΔlt : (Δ : ℝ) < m' := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hm'gt
  have hK : K < m' := lt_of_le_of_lt (le_max_right _ _) hm'gt
  have hmsq : m' < m' ^ 2 := by nlinarith [h1]
  have hm2 : (0 : ℝ) < m' ^ 2 := by nlinarith [h1]
  have hmΔ : (Δ : ℝ) ≤ m' ^ 2 := le_of_lt (lt_trans hΔlt hmsq)
  have hcf0 : 0 < crossForm G m₀ θ H u := hupos m₀
  have hbig : 4 * (Δ : ℝ) ^ 2 * S ^ 2 < m' ^ 2 * crossForm G m' θ H u := by
    have hcf : crossForm G m' θ H u = crossForm G m₀ θ H u := crossForm_mass_independent hM m' m₀ u
    have hKlt : K < m' ^ 2 := lt_trans hK hmsq
    rw [hKdef, div_lt_iff₀ hcf0] at hKlt
    rw [hcf]
    linarith [hKlt]
  exact not_reflectionPositive_of_crossForm_pos_general hM h hm'ne hΔ hus
    (threshold_of_plain hm2 hΔ hmΔ hbig) hm'RP

/-- **THE FILE'S HEADLINE, WITH ITS HYPOTHESES GONE.** On every finite graph carrying a mirror
reflection — no regularity, no condition on `A²`, no class hypothesis, no degree bound to supply —
**being reflection positive at arbitrarily large masses is exactly the coupling hypothesis.** One
direction is the estate's own theorem at every mass
(`GraphMirrorReflection.reflectionPositive_mirror`); the other is §8's, and it needs the mass to be
large. §4's `reflectionPositive_arbitrarily_large_iff_hcross` is the case `Δ = d` and is subsumed;
what §4 keeps is the sharper explicit threshold. -/
theorem reflectionPositive_arbitrarily_large_iff_hcross_general (hM : IsMirrorHalf θ H Mir)
    (h : IsRefl G θ) (m₀ : ℝ) :
    (∀ M : ℝ, ∃ m' : ℝ, M < m' ∧ m' ≠ 0 ∧ GraphReflection.ReflectionPositive G m' θ H)
      ↔ ∀ w : V → ℝ, crossForm G m₀ θ H w ≤ 0 := by
  constructor
  · intro hRP w
    exact hcross_of_reflectionPositive_arbitrarily_large_general hM h hRP m₀ w
  · intro hcross M
    refine ⟨max M 0 + 1, by have := le_max_left M 0; linarith, by positivity,
      fun c hcs => ?_⟩
    exact reflectionPositive_mirror hM h (by positivity)
      (fun w => by rw [crossForm_mass_independent hM _ m₀ w]; exact hcross w)
      (fun p hp _ => hcs p hp)

/-- **AND `stepGraph` IS NOW DECIDED IN BOTH DIRECTIONS.** §9 gave the failure at every `m² > 100`
(a proved sufficient value, not a sharp threshold);
the biconditional turns that into the statement that it is not reflection positive at arbitrarily
large masses **because** it fails `hcross`, with the two conditions identified rather than merely
compared. Still open at small mass, exactly as §9 says. -/
theorem stepGraph_not_reflectionPositive_arbitrarily_large :
    ¬ ∀ M : ℝ, ∃ m' : ℝ, M < m' ∧ m' ≠ 0 ∧
        GraphReflection.ReflectionPositive stepGraph m' sigma6 Hs := by
  intro hRP
  have := (reflectionPositive_arbitrarily_large_iff_hcross_general (Mir := (∅ : Finset (Fin 6)))
    isMirrorHalf_Hs isRefl_sigma6 1).mp hRP us
  rw [crossForm_step_pos] at this
  norm_num at this

end GeneralBiconditional

/-! ## 11. The dichotomy §10 forces, and where it puts the remaining search

`PROOF_STRATEGY` §3 again: §10 landed, so the next rung before the queue. It is short, because §10
did the work — but the statements are ones the estate does not have, and they are the shape the
open question is asked in.

Two theorems bracket every graph. `GraphMirrorReflection.reflectionPositive_mirror` says `hcross`
gives reflection positivity **at every mass**. §10 says failing `hcross` costs it **at every large
mass**. Together, `reflectionPositive_all_or_bounded`: on every finite graph with a mirror
reflection, **either it is reflection positive at every nonzero mass, or there is a threshold past
which it is at none.** There is no third behaviour — no graph is reflection positive on an
unbounded set of masses and fails on another unbounded set.

**That is the sharpest form of where the wall's counterexample can live.**
`CrossFormMatrix.not_converse_of_mass_dependent` says a refutation of the converse is a graph
reflection positive at one mass and not at another. `refutation_is_bounded_above` says any such
graph has its reflection-positive masses **bounded above** — so the search is over a bounded window,
and `not_converse_of_mass_dependent`'s "at another mass" is always a *large* one. §6 reached the
same place from the other side, by showing the slack that would excuse a failure is exactly zero at
every witness of it; this reaches it from the masses rather than from the vectors.

**What this is not.** It does not bound the window, exhibit a graph in it, or show one exists. The
threshold in `exists_threshold_of_not_hcross` is produced by contradiction and is not extracted, so
nothing here is computable from a graph. `WALLS` W1's leg — the converse at a fixed mass — is
untouched for the fourth consecutive section, which is said here rather than left to be noticed.
-/

section Dichotomy

variable {G : SimpleGraph V} [DecidableRel G.Adj] {θ : V ≃ V} {H Mir : Finset V}

/-- **FAILING THE COUPLING HYPOTHESIS COSTS REFLECTION POSITIVITY AT EVERY LARGE MASS**, not merely
at arbitrarily large ones. The threshold is produced by contradiction from §10 and is deliberately
not extracted — see the section header. -/
theorem exists_threshold_of_not_hcross (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (m₀ : ℝ)
    (hnot : ¬ ∀ w : V → ℝ, crossForm G m₀ θ H w ≤ 0) :
    ∃ M : ℝ, ∀ m : ℝ, M < m → m ≠ 0 → ¬ GraphReflection.ReflectionPositive G m θ H := by
  by_contra hc
  push Not at hc
  refine hnot (fun w => hcross_of_reflectionPositive_arbitrarily_large_general hM h ?_ m₀ w)
  intro M
  obtain ⟨m', hgt, hne, hrp⟩ := hc M
  exact ⟨m', hgt, hne, hrp⟩

/-- **THE DICHOTOMY: ALL MASSES, OR A BOUNDED SET OF THEM.** On every finite graph carrying a mirror
reflection, reflection positivity either holds at every nonzero mass or fails past a threshold.
**There is no third behaviour** — no graph holds it on an unbounded set of masses and fails on
another unbounded set. The first branch is `GraphMirrorReflection.reflectionPositive_mirror` and the
second is §10; what is new is that they exhaust the cases. -/
theorem reflectionPositive_all_or_bounded (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) :
    (∀ m : ℝ, m ≠ 0 → GraphReflection.ReflectionPositive G m θ H)
      ∨ ∃ M : ℝ, ∀ m : ℝ, M < m → m ≠ 0 → ¬ GraphReflection.ReflectionPositive G m θ H := by
  by_cases hc : ∀ w : V → ℝ, crossForm G 1 θ H w ≤ 0
  · refine Or.inl fun m hm c hcs => ?_
    exact reflectionPositive_mirror hM h hm
      (fun w => by rw [crossForm_mass_independent hM m 1 w]; exact hc w)
      (fun p hp _ => hcs p hp)
  · exact Or.inr (exists_threshold_of_not_hcross hM h 1 hc)

/-- **AND SO THE WALL'S COUNTEREXAMPLE, IF IT EXISTS, LIVES IN A BOUNDED WINDOW OF MASSES.**
`CrossFormMatrix.not_converse_of_mass_dependent` says a refutation of the converse is a graph
reflection positive at one mass and not at another. This says the masses where it IS reflection
positive are bounded above — so the "other mass" is always a large one, and the search is over a
bounded window. **Nothing here bounds the window or shows one is inhabited.** -/
theorem refutation_is_bounded_above (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hrefute : ∃ m : ℝ, m ≠ 0 ∧ GraphReflection.ReflectionPositive G m θ H
      ∧ ¬ ∀ w : V → ℝ, crossForm G m θ H w ≤ 0) :
    ∃ M : ℝ, ∀ m : ℝ, M < m → m ≠ 0 → ¬ GraphReflection.ReflectionPositive G m θ H := by
  obtain ⟨m, _, _, hnot⟩ := hrefute
  exact exists_threshold_of_not_hcross hM h m hnot

/-- **THE DICHOTOMY LANDS ON `stepGraph`'s SECOND BRANCH**, which §9 already knew with an explicit
threshold of `100`. Stated so that the general theorem is checked against a case where the answer is
independently known, as §5 does for §4. -/
theorem stepGraph_bounded_branch :
    ∃ M : ℝ, ∀ m : ℝ, M < m → m ≠ 0 →
      ¬ GraphReflection.ReflectionPositive stepGraph m sigma6 Hs := by
  refine exists_threshold_of_not_hcross (Mir := (∅ : Finset (Fin 6)))
    isMirrorHalf_Hs isRefl_sigma6 1 ?_
  intro hall
  have := hall us
  rw [crossForm_step_pos] at this
  norm_num at this

end Dichotomy

/-! ## 12. And so reflection positivity at large mass is DECIDABLE

`PROOF_STRATEGY` §6's first question — *what did this unlock?* — and the answer is not another
inequality. §10 identifies "reflection positive at arbitrarily large masses" with `hcross`, on every
finite graph. `CrossBlockStructure.hcross_iff_isCrossBlock` identifies `hcross` with a condition on
the cut that has no vectors, no mass and no real numbers in it, and
`CrossBlockStructure.instDecidableIsCrossBlock` is a real `Decidable` instance for it.

Composing the two: **`reflectionPositive_arbitrarily_large_iff_isCrossBlock`, and then
`decidableLargeMassRP` — on a concrete finite graph, whether it is reflection positive at large mass
is settled by `decide`.** An analytic property of the inverse of an operator, decided by inspecting
the adjacency relation.

Three instances are closed that way and nothing else: `crossGraph` and `stepGraph` fail, `bipGraph`
holds. Each proof is one rewrite along the biconditional followed by `decide`, with no lemma cited
in between — the decidability is used rather than described. **No new case is decided by §12** — §9
already had `stepGraph` with an explicit threshold, `IndefiniteCoupling` had `crossGraph` at every
mass, and `bipGraph` was reflection positive from `hcross` at every mass. What is new is the
*route*: three hand arguments become three `decide`s, and a fourth graph would cost nothing.

**The honest limit, and it is the same one as §§8–11.** This decides the *large-mass* behaviour.
`reflectionPositive_all_or_bounded` says that is the whole of the dichotomy — so what `decide`
settles is which branch a graph is on, and on the bounded branch it says nothing about where the
threshold is or what happens below it. `WALLS` W1's leg is untouched for the fifth consecutive
section.
-/

section Decidable

open CrossBlockStructure

variable {G : SimpleGraph V} [DecidableRel G.Adj] {θ : V ≃ V} {H Mir : Finset V}

/-- **REFLECTION POSITIVITY AT LARGE MASS IS A CONDITION ON THE CUT.** No vectors, no mass, no real
numbers: the half-sites joined across the cut form a disjoint union of complete blocks. -/
theorem reflectionPositive_arbitrarily_large_iff_isCrossBlock (hM : IsMirrorHalf θ H Mir)
    (h : IsRefl G θ) :
    (∀ M : ℝ, ∃ m' : ℝ, M < m' ∧ m' ≠ 0 ∧ GraphReflection.ReflectionPositive G m' θ H)
      ↔ IsCrossBlock G θ H :=
  (reflectionPositive_arbitrarily_large_iff_hcross_general hM h 1).trans
    (hcross_iff_isCrossBlock hM h 1)

/-- **AND SO IT IS DECIDABLE.** The instance is `CrossBlockStructure.instDecidableIsCrossBlock`
transported across the biconditional; the three examples below are closed by `decide` alone. -/
def decidableLargeMassRP (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) :
    Decidable (∀ M : ℝ, ∃ m' : ℝ, M < m' ∧ m' ≠ 0 ∧
        GraphReflection.ReflectionPositive G m' θ H) :=
  decidable_of_iff _ (reflectionPositive_arbitrarily_large_iff_isCrossBlock hM h).symm

/-! ### Three graphs, three `decide`s, no new case decided -/

open IndefiniteCoupling in
/-- `crossGraph` is on the bounded branch. `IndefiniteCoupling.not_reflectionPositive` already knew
it at every mass, by a hand solve; this is the same verdict by inspection of the cut. -/
theorem crossGraph_not_reflectionPositive_arbitrarily_large :
    ¬ ∀ M : ℝ, ∃ m' : ℝ, M < m' ∧ m' ≠ 0 ∧
        GraphReflection.ReflectionPositive crossGraph m' rho Hh := by
  rw [reflectionPositive_arbitrarily_large_iff_isCrossBlock isMirrorHalf_Hh isRefl_rho]
  decide

open IndefiniteCoupling in
/-- `bipGraph` is on the every-mass branch — one block of size two, and the cut is not diagonal, so
this is not the estate's original sufficient condition in disguise. -/
theorem bipGraph_reflectionPositive_arbitrarily_large :
    ∀ M : ℝ, ∃ m' : ℝ, M < m' ∧ m' ≠ 0 ∧
        GraphReflection.ReflectionPositive bipGraph m' rho Hh := by
  rw [reflectionPositive_arbitrarily_large_iff_isCrossBlock isMirrorHalf_Hh isRefl_rho_bip]
  decide

/-- §9's witness, now by `decide` rather than by a threshold computation. The two agree, which is
the point of doing it twice: §9 says *not past `m² = 100`*, this says *not past some threshold*,
and neither says anything below one. -/
theorem stepGraph_not_reflectionPositive_arbitrarily_large_by_decide :
    ¬ ∀ M : ℝ, ∃ m' : ℝ, M < m' ∧ m' ≠ 0 ∧
        GraphReflection.ReflectionPositive stepGraph m' sigma6 Hs := by
  rw [reflectionPositive_arbitrarily_large_iff_isCrossBlock (Mir := (∅ : Finset (Fin 6)))
    isMirrorHalf_Hs isRefl_sigma6]
  decide

end Decidable

end GreenLargeMass
