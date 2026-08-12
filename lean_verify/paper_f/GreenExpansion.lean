import CrossFormMatrix

/-!
# The reflected form IS the cross form, plus a remainder, exactly

`CrossFormMatrix` §6 left the wall's necessity question open — does reflection positivity imply
`hcross`? — with one constraint proved and one attack named. This file supplies the algebra
underneath both, and it does so with **no limit, no asymptotics and no analysis**.

## The identity

For a `d`-regular graph the massive operator is a scalar minus the adjacency matrix,
`massive G m = s • 1 - A` with `s = d + m²`. So `green * massive = 1` reads `s • green = 1 +
green * A`, and substituting that into itself once gives

> **`sq_smul_green`** — `s² • green = s • 1 + A + green * A * A`.

Read at the entry `(θ p, q)` with `p, q` in the half, the `s • 1` term vanishes (a mirror image
is never in the half) and the `A` term is **exactly the cross-cut adjacency**, because
`A (θ p) q = A p (θ q)` when `θ` is a reflection. Summing against a vector supported on the half:

> **`sq_mul_reflectedForm`** —
> `s² * reflectedForm G m θ c = - crossForm G m θ H c + remainder`,
> with `remainder = ∑_{p,q ∈ H} c p * c q * (green * A * A) (θ p) q`.

## What that settles and what it does not

**It settles what the leading term IS.** The heuristic behind the necessity question — *at large
mass the Green function is nearly a multiple of the identity, so the reflected form is governed
by the cross-cut adjacency* — is now an exact algebraic identity rather than a limit argument.
The cross form is not merely correlated with the reflected form; it is the first term of it,
with an error written down in closed form.

**IT SETTLES THE NECESSITY QUESTION ON ONE CLASS, AND THAT IS §6.** The remainder is
`green * A * A`, so it collapses whenever `A²` does — and on a **`1`-regular graph, a perfect
matching, `A² = 1`**. The identity then becomes a solved equation, `(s² − 1) • green = s • 1 + A`,
and **reflection positivity holds if and only if `hcross` does**
(`reflectionPositive_iff_hcross_of_one_regular`). That is the first proved case of the wall's open
converse. It is not a toy class: it is exactly where `IndefiniteCoupling.crossGraph` lives, and §7
re-derives that file's `not_reflectionPositive` from the general theorem — an independent route to
a fact previously obtained by a hand solve, agreeing down to the denominator.

**It does not settle the necessity question in general, and the gap is exactly one bound.** The
remainder is not sign-definite and nothing here estimates it: `green` has all entries positive on
a connected graph (`GraphGreenPositive`) and `A * A` has nonnegative entries, but `c p * c q`
does not, so no sign follows. **What would close the converse is a bound making the remainder
smaller than the cross form's negative direction** — that is an estimate, which is analysis,
which this file deliberately does not attempt.

**AND §9 FINDS THE SECOND WAY THE REMAINDER CLOSES, WHICH IS WHERE A COUNTEREXAMPLE WOULD HAVE
TO LIVE.** The Laplacian kills constants, so the Green function's row sums are `m⁻²`
(`green_mulVec_one`) and `green * J = m⁻² • J`. With that, the remainder closes whenever `A²` lies
in the span of `1`, `A` **and the all-ones matrix `J`** — and the criterion it produces is **not**
`hcross`:

> **`reflectionPositive_iff_slack`** — reflection positivity at `c` is
> `crossForm c ≤ (γ / m²) · (∑_{p ∈ H} c p)²`.

`hcross` implies that for `γ ≥ 0` (`slack_of_hcross`) and is **strictly stronger**. So a
counterexample to the converse must use the slack: a graph in this class whose cross form is
positive somewhere but never by more than it. **None is exhibited and none is claimed to exist** —
what has changed is that the search has an address, and that the slack grows like `m⁻²`, so small
mass is where to look. The class is inhabited beyond §6's matchings by
`IndefiniteCoupling.bipGraph` — `K₂,₂`, `2`-regular, `A² = 2•J − 2•A` — where the cross form and
the slack have the *same* sign and so add rather than fight (`reflectedForm_bipGraph`), which is
why that graph is reflection positive and is not the counterexample.

**REGULARITY RESTRICTS §§1–7 AND §9, AND §8 REMOVES IT FOR THE IDENTITY.** The scalar `s` only
exists because every degree is the same. For a general graph the same two substitutions give
`green = Dinv + Dinv A Dinv + green A Dinv A Dinv`, where `Dinv = diagonal ((deg · + m²)⁻¹)`, and
the leading term becomes `C p q / ((m² + deg p) * (m² + deg q))` — `IsRefl.degree` makes the two
weights match under the mirror, without which that coefficient would not even be symmetric in `p`
and `q`. **§8 proves that version**, so the restriction is gone from the identity; §6's converse
still needs `1`-regularity, which is a stronger thing and is not affected.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace GreenExpansion

open Matrix GraphReflection GraphMirrorReflection CrossFormMatrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}
variable {d : ℕ}

set_option linter.style.openClassical false
open scoped Classical

/-! ## 1. On a regular graph the massive operator is a scalar minus the adjacency -/

theorem massive_eq_of_regular (hd : G.IsRegularOfDegree d) (m : ℝ) :
    GraphLaplacian.massive G m
      = ((d : ℝ) + m ^ 2) • (1 : Matrix V V ℝ) - G.adjMatrix ℝ := by
  ext p q
  rw [GraphLaplacian.massive_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    SimpleGraph.adjMatrix_apply]
  by_cases h : p = q
  · subst h; simp [hd p]
  · simp [h]

/-! ## 2. One substitution, then two -/

/-- **`s • green = 1 + green * A`.** Immediate from `green * massive = 1` and §1. -/
theorem smul_green (hd : G.IsRegularOfDegree d) (hm : m ≠ 0) :
    ((d : ℝ) + m ^ 2) • GraphLaplacian.green G m
      = 1 + GraphLaplacian.green G m * G.adjMatrix ℝ := by
  have h1 : GraphLaplacian.green G m * GraphLaplacian.massive G m = 1 :=
    GraphLaplacian.green_mul_massive G hm
  rw [massive_eq_of_regular hd m, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one] at h1
  rw [← h1]
  abel

/-- **`s² • green = s • 1 + A + green * A * A`**, by substituting the previous identity into
itself. This is the whole content of the file: two terms of the Neumann series made exact, with
the tail written down rather than estimated. -/
theorem sq_smul_green (hd : G.IsRegularOfDegree d) (hm : m ≠ 0) :
    (((d : ℝ) + m ^ 2) ^ 2) • GraphLaplacian.green G m
      = ((d : ℝ) + m ^ 2) • (1 : Matrix V V ℝ) + G.adjMatrix ℝ
        + GraphLaplacian.green G m * G.adjMatrix ℝ * G.adjMatrix ℝ := by
  have h := smul_green hd hm
  have h2 : ((d : ℝ) + m ^ 2) • (GraphLaplacian.green G m * G.adjMatrix ℝ)
      = G.adjMatrix ℝ + GraphLaplacian.green G m * G.adjMatrix ℝ * G.adjMatrix ℝ := by
    rw [← Matrix.smul_mul, h, Matrix.add_mul, Matrix.one_mul]
  calc (((d : ℝ) + m ^ 2) ^ 2) • GraphLaplacian.green G m
      = ((d : ℝ) + m ^ 2) • (((d : ℝ) + m ^ 2) • GraphLaplacian.green G m) := by
        rw [smul_smul, sq]
    _ = ((d : ℝ) + m ^ 2) • (1 + GraphLaplacian.green G m * G.adjMatrix ℝ) := by rw [h]
    _ = ((d : ℝ) + m ^ 2) • (1 : Matrix V V ℝ)
          + ((d : ℝ) + m ^ 2) • (GraphLaplacian.green G m * G.adjMatrix ℝ) := by
        rw [smul_add]
    _ = _ := by rw [h2, add_assoc]

/-! ## 3. Read at a mirrored entry, the second term is the cross-cut adjacency -/

omit [Fintype V] [DecidableEq V] in
/-- A mirror image is never in the half, so the identity term drops. -/
theorem mirror_ne (hM : IsMirrorHalf θ H Mir) {p q : V} (hp : p ∈ H) (hq : q ∈ H) :
    θ p ≠ q := fun hc => hM.notMem_of_mem hp (hc ▸ hq)

omit [Fintype V] [DecidableEq V] in
/-- **THE ADJACENCY TERM IS THE CROSS-CUT ADJACENCY.** `A (θ p) q = A p (θ q)` is
`CrossFormMatrix.adj_cross_comm` in matrix form. -/
theorem adjMatrix_mirror (h : IsRefl G θ) (p q : V) :
    (G.adjMatrix ℝ) (θ p) q = crossAdj G θ p q := by
  have hiff : G.Adj (θ p) q ↔ G.Adj p (θ q) :=
    ((adj_cross_comm h p q).trans (G.adj_comm q (θ p))).symm
  rw [SimpleGraph.adjMatrix_apply, crossAdj]
  by_cases hpq : G.Adj p (θ q)
  · rw [if_pos (hiff.mpr hpq), if_pos hpq]
  · rw [if_neg fun hc => hpq (hiff.mp hc), if_neg hpq]

/-- **THE GREEN FUNCTION AT A MIRRORED ENTRY, EXACTLY.** -/
theorem sq_mul_green_mirror (hd : G.IsRegularOfDegree d) (hM : IsMirrorHalf θ H Mir)
    (h : IsRefl G θ) (hm : m ≠ 0) {p q : V} (hp : p ∈ H) (hq : q ∈ H) :
    (((d : ℝ) + m ^ 2) ^ 2) * GraphLaplacian.green G m (θ p) q
      = crossAdj G θ p q
        + (GraphLaplacian.green G m * G.adjMatrix ℝ * G.adjMatrix ℝ) (θ p) q := by
  have := congrFun (congrFun (sq_smul_green (G := G) (m := m) hd hm) (θ p)) q
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, if_neg (mirror_ne hM hp hq), smul_zero, zero_add,
    adjMatrix_mirror h p q] at this
  exact this

/-! ## 4. The reflected form -/

/-- The reflected form of a vector supported on the half is a double sum over the half. -/
theorem reflectedForm_eq_sum_half {c : V → ℝ} (hc : ∀ p, p ∉ H → c p = 0) :
    reflectedForm G m θ c
      = ∑ p ∈ H, ∑ q ∈ H, c p * c q * GraphLaplacian.green G m (θ p) q := by
  classical
  rw [reflectedForm,
    ← Finset.sum_subset (Finset.subset_univ H) fun p _ hp =>
      Finset.sum_eq_zero fun q _ => by rw [hc p hp]; ring]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_subset (Finset.subset_univ H) fun q _ hq => by rw [hc q hq]; ring]

/-- **THE IDENTITY.** The reflected form is the negated cross form plus a remainder, exactly,
with `s = d + m²`. No limit is taken and nothing is estimated. -/
theorem sq_mul_reflectedForm (hd : G.IsRegularOfDegree d) (hM : IsMirrorHalf θ H Mir)
    (h : IsRefl G θ) (hm : m ≠ 0) {c : V → ℝ} (hc : ∀ p, p ∉ H → c p = 0) :
    (((d : ℝ) + m ^ 2) ^ 2) * reflectedForm G m θ c
      = - crossForm G m θ H c
        + ∑ p ∈ H, ∑ q ∈ H,
            c p * c q * (GraphLaplacian.green G m * G.adjMatrix ℝ * G.adjMatrix ℝ) (θ p) q := by
  classical
  rw [reflectedForm_eq_sum_half hc, crossForm_eq_neg_adj hM m c, neg_neg, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hg := sq_mul_green_mirror hd hM h hm hp hq
  have : (((d : ℝ) + m ^ 2) ^ 2) * (c p * c q * GraphLaplacian.green G m (θ p) q)
      = c p * c q * ((((d : ℝ) + m ^ 2) ^ 2) * GraphLaplacian.green G m (θ p) q) := by ring
  rw [this, hg, crossAdj]
  ring

/-! ## 5. What the identity does not do

Stated as a theorem rather than a paragraph, because "the remainder is not controlled" is the
kind of sentence that turns into "the remainder is small" on a second reading. -/

/-- **THE REMAINDER IS THE WHOLE GAP, AND IT IS THE WHOLE GAP EXACTLY.** Reflection positivity
holds at this `c` precisely when the remainder dominates the cross form there — which is a
restatement, and is the point: no inequality has been proved, and the identity converts the
necessity question into one estimate and no more. -/
theorem reflectionPositive_iff_remainder (hd : G.IsRegularOfDegree d)
    (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0) {c : V → ℝ}
    (hc : ∀ p, p ∉ H → c p = 0) (hs : 0 < ((d : ℝ) + m ^ 2) ^ 2) :
    0 ≤ reflectedForm G m θ c ↔
      crossForm G m θ H c ≤
        ∑ p ∈ H, ∑ q ∈ H,
          c p * c q * (GraphLaplacian.green G m * G.adjMatrix ℝ * G.adjMatrix ℝ) (θ p) q := by
  rw [← mul_nonneg_iff_of_pos_left hs, sq_mul_reflectedForm hd hM h hm hc,
    ← sub_nonneg (a := ∑ p ∈ H, ∑ q ∈ H,
      c p * c q * (GraphLaplacian.green G m * G.adjMatrix ℝ * G.adjMatrix ℝ) (θ p) q)]
  constructor
  · intro hx; linarith
  · intro hx; linarith

/-! ## 6. Where the remainder closes: a perfect matching, and the converse is TRUE there

The remainder is `green * A * A`, so it collapses whenever `A * A` does. **On a `1`-regular graph
— a perfect matching — `A² = 1`**: the only walk of length two from a vertex is out to its
partner and back. So the remainder is the reflected form itself, the identity becomes a solved
equation, and the wall's open converse is settled on that class:

> **`reflectionPositive_iff_hcross_of_one_regular`** — for a perfect matching,
> reflection positivity holds **if and only if** `hcross` does.

This is the first proved case of the necessity question, and it is not a toy: it is exactly the
class `IndefiniteCoupling.crossGraph` lives in. That file computed `(dd m ^ 2 - 1) * reflectedForm
= -2` by hand, clearing a denominator by inspection; here `dd m = 1 + m²` is `s`, and the hand
computation is the general identity read at one vector.
-/

/-- **A PERFECT MATCHING SQUARES TO THE IDENTITY.** Two steps from `p` go to its unique partner
and back, so the only length-two walk returns. -/
theorem adjMatrix_sq_of_one_regular (hd : G.IsRegularOfDegree 1) :
    G.adjMatrix ℝ * G.adjMatrix ℝ = 1 := by
  classical
  ext p q
  have hcp : (G.neighborFinset p).card = 1 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hd p
  obtain ⟨n, hn⟩ := Finset.card_eq_one.mp hcp
  have hnbr : ∀ x : V, G.Adj p x ↔ x = n := by
    intro x
    rw [← SimpleGraph.mem_neighborFinset, hn, Finset.mem_singleton]
  have hpn : G.Adj p n := (hnbr n).mpr rfl
  have hcn : (G.neighborFinset n).card = 1 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hd n
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcn
  have hnbrn : ∀ x : V, G.Adj n x ↔ x = r := by
    intro x
    rw [← SimpleGraph.mem_neighborFinset, hr, Finset.mem_singleton]
  have hrp : r = p := ((hnbrn p).mp hpn.symm).symm
  subst hrp
  rw [Matrix.mul_apply, Finset.sum_eq_single n]
  · rw [SimpleGraph.adjMatrix_apply, if_pos hpn, one_mul, SimpleGraph.adjMatrix_apply,
      Matrix.one_apply]
    by_cases hq : G.Adj n q
    · rw [if_pos hq, if_pos ((hnbrn q).mp hq).symm]
    · rw [if_neg hq, if_neg fun hc => hq ((hnbrn q).mpr hc.symm)]
  · intro j _ hj
    rw [SimpleGraph.adjMatrix_apply, if_neg fun hc => hj ((hnbr j).mp hc), zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ n) hcon

/-- **THE IDENTITY SOLVES ON A PERFECT MATCHING**: `(s² − 1) • green = s • 1 + A`. -/
theorem sq_sub_one_smul_green_of_one_regular (hd : G.IsRegularOfDegree 1) (hm : m ≠ 0) :
    (((1 : ℝ) + m ^ 2) ^ 2 - 1) • GraphLaplacian.green G m
      = ((1 : ℝ) + m ^ 2) • (1 : Matrix V V ℝ) + G.adjMatrix ℝ := by
  have h := sq_smul_green (d := 1) hd hm
  rw [Matrix.mul_assoc, adjMatrix_sq_of_one_regular hd, Matrix.mul_one, Nat.cast_one] at h
  rw [sub_smul, one_smul, h]
  abel

/-- `crossForm` reads its argument only on the half. -/
theorem crossForm_restrict (m : ℝ) (w : V → ℝ) :
    crossForm G m θ H (fun p => if p ∈ H then w p else 0) = crossForm G m θ H w := by
  classical
  rw [crossForm, crossForm]
  exact Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => by
    rw [if_pos hp, if_pos hq]

/-- **THE CONVERSE, PROVED, ON PERFECT MATCHINGS.** Reflection positivity holds if and only if
the coupling hypothesis does — so on this class `GraphMirrorReflection.reflectionPositive_mirror`
is a characterisation and not merely an implication.

The scale factor `(1 + m²)² − 1 = m²(m² + 2)` is strictly positive for `m ≠ 0`, which is where
the mass hypothesis is used and the only place it is. -/
theorem reflectionPositive_iff_hcross_of_one_regular (hd : G.IsRegularOfDegree 1)
    (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive G m θ H ↔ ∀ w : V → ℝ, crossForm G m θ H w ≤ 0 := by
  classical
  have hspos : (0 : ℝ) < ((1 : ℝ) + m ^ 2) ^ 2 - 1 := by
    have : (0 : ℝ) < m ^ 2 := by positivity
    nlinarith
  -- the identity, at every vector supported on the half
  have key : ∀ c : V → ℝ, (∀ p, p ∉ H → c p = 0) →
      (((1 : ℝ) + m ^ 2) ^ 2 - 1) * reflectedForm G m θ c = - crossForm G m θ H c := by
    intro c hc
    rw [reflectedForm_eq_sum_half hc, crossForm_eq_neg_adj hM m c, neg_neg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hg := congrFun (congrFun (sq_sub_one_smul_green_of_one_regular
      (G := G) (m := m) hd hm) (θ p)) q
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      if_neg (mirror_ne hM hp hq), smul_zero, zero_add, adjMatrix_mirror h p q] at hg
    rw [show (((1 : ℝ) + m ^ 2) ^ 2 - 1) * (c p * c q * GraphLaplacian.green G m (θ p) q)
        = c p * c q * ((((1 : ℝ) + m ^ 2) ^ 2 - 1) * GraphLaplacian.green G m (θ p) q) from by
      ring, hg, crossAdj]
  constructor
  · intro hrp w
    have hsupp : ∀ p, p ∉ H → (fun p => if p ∈ H then w p else 0) p = 0 := fun p hp => if_neg hp
    have := hrp _ hsupp
    rw [← reflectedForm] at this
    have hk := key _ hsupp
    rw [crossForm_restrict m w] at hk
    nlinarith [mul_nonneg (le_of_lt hspos) this]
  · intro hc c hcs
    have hk := key c hcs
    have : 0 ≤ - crossForm G m θ H c := neg_nonneg.mpr (hc c)
    rw [← hk] at this
    rw [← reflectedForm]
    nlinarith [this]

/-! ## 7. The estate's own witness is an instance, and that is a cross-check

`IndefiniteCoupling.crossGraph` is the perfect matching `0–3`, `1–2` on `Fin 4`, so it is
`1`-regular and §6 applies to it. Its `not_reflectionPositive` was proved there by an explicit
solve — guessing the vector, clearing the denominator `(1+m²)² − 1` by hand and verifying by
multiplication. **Deriving the same fact from the general theorem is an independent route to it,
and the two agree**, including the denominator: `dd m = 1 + m²` in that file is `s` here.
-/

theorem crossGraph_one_regular : IndefiniteCoupling.crossGraph.IsRegularOfDegree 1 := by
  change ∀ v, IndefiniteCoupling.crossGraph.degree v = 1
  intro v
  have hnb : IndefiniteCoupling.crossGraph.neighborFinset v
      = {(⟨3 - v.val, by omega⟩ : Fin 4)} := by
    ext u
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton,
      IndefiniteCoupling.crossGraph]
    constructor
    · rintro ⟨hs, -⟩
      apply Fin.ext
      dsimp only
      omega
    · rintro rfl
      refine ⟨by dsimp only; omega, fun hc => ?_⟩
      rw [Fin.ext_iff] at hc
      dsimp only at hc
      omega
  rw [SimpleGraph.degree, hnb, Finset.card_singleton]

/-- **RE-DERIVED FROM THE GENERAL IDENTITY.** `IndefiniteCoupling.not_reflectionPositive` proved
this by a hand solve; this proof knows nothing about the graph beyond that it is a perfect
matching and that `hcross` fails on it. -/
theorem crossGraph_not_reflectionPositive {m : ℝ} (hm : m ≠ 0) :
    ¬ GraphReflection.ReflectionPositive IndefiniteCoupling.crossGraph m
        IndefiniteCoupling.rho IndefiniteCoupling.Hh :=
  fun hrp => IndefiniteCoupling.not_hcross m
    ((reflectionPositive_iff_hcross_of_one_regular crossGraph_one_regular
      IndefiniteCoupling.isMirrorHalf_Hh IndefiniteCoupling.isRefl_rho hm).mp hrp)

/-- And the converse direction is live too, not just the failure: on a perfect matching where the
cross matrix IS positive semidefinite, reflection positivity follows — with no Green function
computed at all. Stated through `CrossFormMatrix`'s criterion, so the hypothesis is a matrix
condition end to end. -/
theorem reflectionPositive_of_posSemidef_of_one_regular (hd : G.IsRegularOfDegree 1)
    (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hps : (crossMatrix G θ H).PosSemidef) :
    GraphReflection.ReflectionPositive G m θ H :=
  (reflectionPositive_iff_hcross_of_one_regular hd hM h hm).mpr
    ((crossForm_nonpos_iff_posSemidef hM h m).mpr hps)

/-! ## 8. Regularity removed

§§1–4 need a scalar `s`, which exists only because the degrees agree. They do not have to. Write
`Dm` for the diagonal matrix of `deg p + m²` and `Dinv` for its entrywise reciprocal — no general
matrix inverse is used, the two are shown mutually inverse by one diagonal multiplication — and
the same two substitutions run:

> **`green_eq_two_terms`** — `green = Dinv + Dinv * A * Dinv + green * A * Dinv * A * Dinv`.

At a mirrored entry the first term still vanishes and the second is still the cross-cut
adjacency, now **weighted**: `crossAdj p q / ((m² + deg p) * (m² + deg q))`. The two weights come
out matched because `IsRefl.degree` says a mirror image has the same degree as its original —
without that the leading term would not even be symmetric in `p` and `q`.

This is the restriction the file's own header used to name as not removed. The consumer is the
BOX, which is not regular at its boundary; the torus and the cycle were already covered.
-/

/-- The diagonal of `massive`: degree plus mass squared. -/
noncomputable def Dm (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) : Matrix V V ℝ :=
  Matrix.diagonal fun p => (G.degree p : ℝ) + m ^ 2

/-- Its entrywise reciprocal. Positive for `m ≠ 0`, so no general matrix inverse is needed. -/
noncomputable def Dinv (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) : Matrix V V ℝ :=
  Matrix.diagonal fun p => ((G.degree p : ℝ) + m ^ 2)⁻¹

omit [DecidableEq V] in
theorem weight_pos (hm : m ≠ 0) (p : V) : (0 : ℝ) < (G.degree p : ℝ) + m ^ 2 := by
  have h1 : (0 : ℝ) ≤ (G.degree p : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) < m ^ 2 := by positivity
  linarith

theorem Dm_mul_Dinv (hm : m ≠ 0) : Dm G m * Dinv G m = 1 := by
  rw [Dm, Dinv, Matrix.diagonal_mul_diagonal]
  rw [show (fun p => ((G.degree p : ℝ) + m ^ 2) * ((G.degree p : ℝ) + m ^ 2)⁻¹) = fun _ => (1 : ℝ)
    from funext fun p => mul_inv_cancel₀ (ne_of_gt (weight_pos hm p))]
  exact Matrix.diagonal_one

theorem massive_eq_Dm_sub_adj (m : ℝ) :
    GraphLaplacian.massive G m = Dm G m - G.adjMatrix ℝ := by
  ext p q
  rw [GraphLaplacian.massive_apply, Matrix.sub_apply, Dm, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply]

/-- **ONE SUBSTITUTION, WITHOUT REGULARITY**: `green = Dinv + green * A * Dinv`. -/
theorem green_eq_one_term (hm : m ≠ 0) :
    GraphLaplacian.green G m
      = Dinv G m + GraphLaplacian.green G m * G.adjMatrix ℝ * Dinv G m := by
  have h1 : GraphLaplacian.green G m * GraphLaplacian.massive G m = 1 :=
    GraphLaplacian.green_mul_massive G hm
  rw [massive_eq_Dm_sub_adj m, Matrix.mul_sub, sub_eq_iff_eq_add] at h1
  calc GraphLaplacian.green G m
      = GraphLaplacian.green G m * (Dm G m * Dinv G m) := by rw [Dm_mul_Dinv hm, Matrix.mul_one]
    _ = (GraphLaplacian.green G m * Dm G m) * Dinv G m := by rw [Matrix.mul_assoc]
    _ = (1 + GraphLaplacian.green G m * G.adjMatrix ℝ) * Dinv G m := by rw [h1]
    _ = _ := by rw [Matrix.add_mul, Matrix.one_mul]

/-- **TWO SUBSTITUTIONS, WITHOUT REGULARITY.** The general form of `sq_smul_green`. -/
theorem green_eq_two_terms (hm : m ≠ 0) :
    GraphLaplacian.green G m
      = Dinv G m + Dinv G m * G.adjMatrix ℝ * Dinv G m
        + GraphLaplacian.green G m * G.adjMatrix ℝ * Dinv G m * G.adjMatrix ℝ * Dinv G m := by
  conv_lhs => rw [green_eq_one_term hm]
  conv_lhs => rw [green_eq_one_term hm]
  rw [Matrix.add_mul, Matrix.add_mul, add_assoc]

/-- **THE WEIGHTED LEADING TERM.** `IsRefl.degree` is what makes the two weights match: a mirror
image has the same degree as its original, so the coefficient is symmetric in `p` and `q`. -/
theorem Dinv_adj_Dinv_mirror (h : IsRefl G θ) (p q : V) :
    (Dinv G m * G.adjMatrix ℝ * Dinv G m) (θ p) q
      = crossAdj G θ p q * (((G.degree p : ℝ) + m ^ 2) * ((G.degree q : ℝ) + m ^ 2))⁻¹ := by
  rw [Matrix.mul_assoc, Dinv, Matrix.diagonal_mul, Matrix.mul_diagonal, adjMatrix_mirror h p q,
    h.degree p]
  rw [mul_inv]
  ring

/-- **THE GREEN FUNCTION AT A MIRRORED ENTRY, WITH NO REGULARITY.** -/
theorem green_mirror_general (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    {p q : V} (hp : p ∈ H) (hq : q ∈ H) :
    GraphLaplacian.green G m (θ p) q
      = crossAdj G θ p q * (((G.degree p : ℝ) + m ^ 2) * ((G.degree q : ℝ) + m ^ 2))⁻¹
        + (GraphLaplacian.green G m * G.adjMatrix ℝ * Dinv G m * G.adjMatrix ℝ * Dinv G m)
            (θ p) q := by
  have hg := congrFun (congrFun (green_eq_two_terms (G := G) (m := m) hm) (θ p)) q
  rw [Matrix.add_apply, Matrix.add_apply, Dinv, Matrix.diagonal_apply,
    if_neg (mirror_ne hM hp hq), zero_add, ← Dinv, Dinv_adj_Dinv_mirror h p q] at hg
  exact hg

/-! ## 9. The all-ones direction, and a wider class where the remainder closes

§6 closes the remainder when `A² = 1`. There is a second way it can close, and it needs one fact
the estate did not have: **the Green function's row sums are `m⁻²`.** The Laplacian kills
constants, so `massive *ᵥ 1⃗ = m² • 1⃗`, so `green *ᵥ 1⃗ = m⁻² • 1⃗` — hence `green * J = m⁻² • J`
for the all-ones matrix `J`.

With that, the remainder closes whenever `A²` lies in the span of `1`, `A` **and `J`**:

> **`smul_green_of_adjSq`** — if `A * A = α • 1 + β • A + γ • J` then
> `(s² − α − β s) • green = (s − β) • 1 + A + (γ / m²) • J`.

**And the criterion it produces is NOT `hcross`.** Read at a mirrored entry and summed against a
vector supported on the half, it says reflection positivity at `c` is

    crossForm c  ≤  (γ / m²) * (∑_{p ∈ H} c p)²

— which `hcross` implies and which is **strictly weaker whenever `γ > 0`**. So this class is
exactly where a counterexample to the wall's converse would have to live: a graph in it whose
cross form is positive somewhere, but never by more than the slack. **No such graph is exhibited
here and none is claimed to exist.** What has changed is that the search has an address.

**The class is inhabited and the witness was already in the estate.** `IndefiniteCoupling.bipGraph`
is `K₂,₂`, is `2`-regular, and has `A² = 2 • J − 2 • A` — two vertices of the same part have both
of the others as common neighbours, two of different parts have none. That is `α = 0`, `β = −2`,
`γ = 2`, and §6's matching class is the disjoint case `α = 1, β = γ = 0`.
-/

/-- **THE MASSIVE OPERATOR ON CONSTANTS.** The Laplacian kills them, so only the mass survives. -/
theorem massive_mulVec_one (m : ℝ) :
    GraphLaplacian.massive G m *ᵥ (fun _ => (1 : ℝ)) = fun _ => m ^ 2 := by
  rw [GraphLaplacian.massive, Matrix.add_mulVec, G.lapMatrix_mulVec_const_eq_zero]
  ext p
  simp [Matrix.mulVec, Matrix.diagonal, dotProduct]

/-- **AND SO THE GREEN FUNCTION'S ROW SUMS ARE `m⁻²`.** -/
theorem green_mulVec_one (hm : m ≠ 0) :
    GraphLaplacian.green G m *ᵥ (fun _ => (1 : ℝ)) = fun _ => (m ^ 2)⁻¹ := by
  have hm2 : (m : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ hm
  have key : GraphLaplacian.green G m *ᵥ
      (GraphLaplacian.massive G m *ᵥ (fun _ => (1 : ℝ))) = fun _ => (1 : ℝ) := by
    rw [Matrix.mulVec_mulVec, GraphLaplacian.green_mul_massive G hm, Matrix.one_mulVec]
  rw [massive_mulVec_one (G := G) m,
    show (fun _ : V => m ^ 2) = (m ^ 2) • (fun _ : V => (1 : ℝ)) from by ext p; simp,
    Matrix.mulVec_smul] at key
  ext p
  have hp := congrFun key p
  simp only [Pi.smul_apply, smul_eq_mul] at hp
  field_simp
  linarith [hp]

/-- The all-ones matrix. -/
noncomputable def allOnes (V : Type*) : Matrix V V ℝ := fun _ _ => 1

theorem green_mul_allOnes (hm : m ≠ 0) :
    GraphLaplacian.green G m * allOnes V = (m ^ 2)⁻¹ • allOnes V := by
  ext p q
  have hp := congrFun (green_mulVec_one (G := G) (m := m) hm) p
  simp only [Matrix.mulVec, dotProduct, mul_one] at hp
  simp only [Matrix.mul_apply, allOnes, Matrix.smul_apply, smul_eq_mul, mul_one]
  exact hp

/-- **THE IDENTITY SOLVES WHENEVER `A²` IS IN THE SPAN OF `1`, `A` AND `J`.** -/
theorem smul_green_of_adjSq (hd : G.IsRegularOfDegree d) (hm : m ≠ 0) {α β γ : ℝ}
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V) :
    (((d : ℝ) + m ^ 2) ^ 2 - α - β * ((d : ℝ) + m ^ 2)) • GraphLaplacian.green G m
      = (((d : ℝ) + m ^ 2) - β) • (1 : Matrix V V ℝ) + G.adjMatrix ℝ
        + (γ * (m ^ 2)⁻¹) • allOnes V := by
  have hs := smul_green hd hm
  have hGA : GraphLaplacian.green G m * G.adjMatrix ℝ
      = ((d : ℝ) + m ^ 2) • GraphLaplacian.green G m - 1 := by
    rw [hs]; abel
  have h2 := sq_smul_green hd hm
  rw [Matrix.mul_assoc, hA, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.mul_one, hGA, green_mul_allOnes hm] at h2
  rw [sub_smul, sub_smul, h2, smul_sub, smul_smul]
  module

/-! ### The criterion this produces, and why it is not `hcross` -/

/-- **THE GREEN FUNCTION AT A MIRRORED ENTRY, ON THIS CLASS.** The `1` term drops as always; what
survives beside the cross-cut adjacency is a constant `γ / m²`, the same at every entry. -/
theorem green_mirror_of_adjSq (hd : G.IsRegularOfDegree d) (hM : IsMirrorHalf θ H Mir)
    (h : IsRefl G θ) (hm : m ≠ 0) {α β γ : ℝ}
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V)
    {p q : V} (hp : p ∈ H) (hq : q ∈ H) :
    (((d : ℝ) + m ^ 2) ^ 2 - α - β * ((d : ℝ) + m ^ 2)) * GraphLaplacian.green G m (θ p) q
      = crossAdj G θ p q + γ * (m ^ 2)⁻¹ := by
  have hg := congrFun (congrFun (smul_green_of_adjSq (G := G) (m := m) hd hm hA) (θ p)) q
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, if_neg (mirror_ne hM hp hq), smul_zero, zero_add, adjMatrix_mirror h p q,
    Matrix.smul_apply, allOnes, smul_eq_mul, mul_one] at hg
  exact hg

/-- **THE REFLECTED FORM ON THIS CLASS, EXACTLY**: the cross form, plus a slack proportional to
the SQUARE OF THE SUM of the coefficients over the half. -/
theorem reflectedForm_of_adjSq (hd : G.IsRegularOfDegree d) (hM : IsMirrorHalf θ H Mir)
    (h : IsRefl G θ) (hm : m ≠ 0) {α β γ : ℝ}
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V)
    {c : V → ℝ} (hc : ∀ p, p ∉ H → c p = 0) :
    (((d : ℝ) + m ^ 2) ^ 2 - α - β * ((d : ℝ) + m ^ 2)) * reflectedForm G m θ c
      = - crossForm G m θ H c + (γ * (m ^ 2)⁻¹) * (∑ p ∈ H, c p) ^ 2 := by
  classical
  set K := ((d : ℝ) + m ^ 2) ^ 2 - α - β * ((d : ℝ) + m ^ 2) with hKdef
  have hlhs : K * reflectedForm G m θ c
      = ∑ p ∈ H, ∑ q ∈ H, c p * c q * (crossAdj G θ p q + γ * (m ^ 2)⁻¹) := by
    rw [reflectedForm_eq_sum_half hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [show K * (c p * c q * GraphLaplacian.green G m (θ p) q)
        = c p * c q * (K * GraphLaplacian.green G m (θ p) q) from by ring,
      hKdef, green_mirror_of_adjSq hd hM h hm hA hp hq]
  rw [hlhs, crossForm_eq_neg_adj hM m c, neg_neg,
    show (∑ p ∈ H, c p) ^ 2 = (∑ p ∈ H, c p) * (∑ q ∈ H, c q) from sq _,
    Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [crossAdj]
  ring

/-! ### The class is inhabited, and the witness was already in the estate -/

theorem bipGraph_two_regular : IndefiniteCoupling.bipGraph.IsRegularOfDegree 2 := by
  change ∀ v, IndefiniteCoupling.bipGraph.degree v = 2
  intro v
  have hnb : ∀ u : Fin 4, IndefiniteCoupling.bipGraph.Adj v u ↔ (v.val < 2) ≠ (u.val < 2) :=
    fun _ => Iff.rfl
  have : IndefiniteCoupling.bipGraph.neighborFinset v
      = Finset.univ.filter fun u => (v.val < 2) ≠ (u.val < 2) := by
    ext u
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter, hnb u]
    exact ⟨fun h => ⟨Finset.mem_univ u, h⟩, fun h => h.2⟩
  rw [SimpleGraph.degree, this]
  fin_cases v <;> rfl

/-- **`K₂,₂` SQUARES INTO THE SPAN.** Two vertices of the same part have both of the others as
common neighbours; two of different parts have none. So `A² = 2 • J − 2 • A`, which is
`α = 0`, `β = −2`, `γ = 2`. -/
theorem bipGraph_adjSq :
    IndefiniteCoupling.bipGraph.adjMatrix ℝ * IndefiniteCoupling.bipGraph.adjMatrix ℝ
      = (0 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)
        + (-2 : ℝ) • IndefiniteCoupling.bipGraph.adjMatrix ℝ + (2 : ℝ) • allOnes (Fin 4) := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, SimpleGraph.adjMatrix_apply, allOnes,
      IndefiniteCoupling.bipGraph] <;> norm_num

/-- **THE REFLECTED FORM ON `K₂,₂`, EXACTLY.** Every cross pair is adjacent, so the cross form is
`−(c₀+c₁)²` and the slack is `(2/m²)(c₀+c₁)²`: the two add rather than fight, which is why this
graph is reflection positive and is *not* a counterexample to the converse. It is the witness that
the class of §9 is inhabited beyond §6's matchings. -/
theorem reflectedForm_bipGraph (hm : m ≠ 0) {c : Fin 4 → ℝ}
    (hc : ∀ p, p ∉ IndefiniteCoupling.Hh → c p = 0) :
    (((2 : ℝ) + m ^ 2) ^ 2 - 0 - (-2) * ((2 : ℝ) + m ^ 2))
        * reflectedForm IndefiniteCoupling.bipGraph m IndefiniteCoupling.rho c
      = (c 0 + c 1) ^ 2 + (2 * (m ^ 2)⁻¹) * (∑ p ∈ IndefiniteCoupling.Hh, c p) ^ 2 := by
  have h := reflectedForm_of_adjSq (d := 2) (H := IndefiniteCoupling.Hh)
    (Mir := (∅ : Finset (Fin 4))) bipGraph_two_regular IndefiniteCoupling.isMirrorHalf_Hh
    IndefiniteCoupling.isRefl_rho_bip hm bipGraph_adjSq hc
  push_cast at h
  rw [h, IndefiniteCoupling.crossForm_bip m c, neg_neg]

/-! ### And the criterion this class satisfies is NOT `hcross`

Stated as a theorem so the difference cannot soften into a remark. Reflection positivity at `c` is
`crossForm c ≤ (γ/m²)(∑_H c)²`, and `hcross` is `crossForm c ≤ 0`. The first follows from the
second whenever `γ ≥ 0`, and the two differ exactly by the slack. **A counterexample to the wall's
converse, if one exists, must use that slack**: a graph in this class whose cross form is positive
somewhere but never by more than `(γ/m²)(∑_H c)²`. None is exhibited here.
-/

/-- **THE EXACT CRITERION ON THIS CLASS.** -/
theorem reflectionPositive_iff_slack (hd : G.IsRegularOfDegree d) (hM : IsMirrorHalf θ H Mir)
    (h : IsRefl G θ) (hm : m ≠ 0) {α β γ : ℝ}
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V)
    (hK : 0 < ((d : ℝ) + m ^ 2) ^ 2 - α - β * ((d : ℝ) + m ^ 2)) :
    GraphReflection.ReflectionPositive G m θ H ↔
      ∀ c : V → ℝ, (∀ p, p ∉ H → c p = 0) →
        crossForm G m θ H c ≤ (γ * (m ^ 2)⁻¹) * (∑ p ∈ H, c p) ^ 2 := by
  constructor
  · intro hrp c hcs
    have hr := reflectedForm_of_adjSq hd hM h hm hA hcs
    have h0 : (0 : ℝ) ≤ reflectedForm G m θ c := hrp c hcs
    nlinarith [mul_nonneg (le_of_lt hK) h0]
  · intro hslack c hcs
    have hr := reflectedForm_of_adjSq hd hM h hm hA hcs
    have := hslack c hcs
    rw [← reflectedForm]
    nlinarith [hr, this]

/-- **AND `hcross` IS STRICTLY THE STRONGER CONDITION when `γ ≥ 0`.** The implication is one line;
what matters is that it is only an implication, and that the gap is exactly the slack. -/
theorem slack_of_hcross (hγ : 0 ≤ γ) (hm : m ≠ 0)
    (hc : ∀ w : V → ℝ, crossForm G m θ H w ≤ 0) (c : V → ℝ) :
    crossForm G m θ H c ≤ (γ * (m ^ 2)⁻¹) * (∑ p ∈ H, c p) ^ 2 := by
  have h1 : (0 : ℝ) ≤ (γ * (m ^ 2)⁻¹) * (∑ p ∈ H, c p) ^ 2 := by
    have : (0 : ℝ) ≤ (m ^ 2)⁻¹ := by positivity
    have := mul_nonneg hγ this
    positivity
  linarith [hc c]

end GreenExpansion
