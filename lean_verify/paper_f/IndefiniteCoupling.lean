import StrictBiconditional

/-!
# The coupling hypothesis is not free, and here is the graph that breaks it

Every reflection-positivity result on this wall carries the same hypothesis: that the
cross-coupling form is nowhere positive,

  `hcross : ∀ w, crossForm G m θ H w ≤ 0`.

**Four files assume it and none exhibits a graph that fails it.** The only route to it in the
estate is `GraphMirrorReflection.crossForm_nonpos_of_cross_diag`, which asks that cross-cut
adjacency be *diagonal* — `p, q ∈ H` and `G.Adj p (θ q)` force `p = q` — and every lattice in the
estate satisfies that, so the hypothesis has always been discharged and never tested.

`StrictBiconditional` §3b removed `hcross` from the forward half of its biconditional, on the
grounds that the resulting statements *"survive exactly where §3 does not: an indefinite
coupling"*. **That claim was about a regime nothing in the estate inhabited.** A generalisation
into an empty regime proves nothing — which is `DualGraph` §8's standard, stated there as *"a
conditional theorem whose hypothesis nothing satisfies proves nothing"* — so this file inhabits it.

> **`crossForm_pos`** — for the four-vertex graph below, the half `{0, 1}` and the reflection
> `p ↦ p + 2`, the cross-coupling is **`+2` at an explicit vector**. Hence
> **`not_hcross`**: the standing hypothesis is FALSE here.

> And then §§4–5 decide the graph and turn that into a **necessity** result — see *What this does
> and does not settle* below.

## Why it takes four vertices and two edges, and why no lattice does this

`crossForm G m θ H w = ∑_{p ∈ H} ∑_{q ∈ H} w p · w q · massive p (θ q)`, and off the diagonal
`massive p (θ q)` is `−1` across an edge and `0` otherwise. So every term with `p = q` contributes
`−(w p)² ≤ 0` and can never break the hypothesis. **The sign can only turn on a term with
`p ≠ q`** — two *different* sites of the half, adjacent across the cut — and then
`w p · w q · (−1)` is positive whenever `w p` and `w q` have opposite signs.

That is exactly the configuration `crossForm_nonpos_of_cross_diag` excludes, and it is exactly
what a lattice reflection cannot produce: a site's mirror image sits directly across the cut from
it, so the only cross-cut edge at `p` runs to `θ p` and the coupling is diagonal. **The hypothesis
is free on every lattice for a structural reason, and this graph is not a lattice.**

The graph is the perfect matching `0 – 3`, `1 – 2` on `Fin 4`; the reflection is `p ↦ p + 2`,
which swaps `0 ↔ 2` and `1 ↔ 3` and carries each edge to the other; the half is `{0, 1}` and the
mirror is empty. Site `0` is joined to `3 = θ 1` and site `1` to `2 = θ 0` — each half-site is
adjacent to the *other* one's mirror image, which is the whole of the construction.

## What this does and does not settle

**It makes §3b's generality real rather than notional**: `not_strict_of_supportedIsotropic` is a
statement about graphs, and there is now a graph in the estate where it applies and
`strict_iff_not_supportedIsotropic` cannot be stated at all.

**SUPERSEDED WITHIN THE UNIT, and the superseded text is kept because the plan it records was
wrong about its own difficulty.** It read:

> *It does not exhibit a supported isotropic vector here, so it does not decide whether this graph
> is strict, and it makes no claim either way — deciding it means deciding whether such a vector
> exists, which is a computation this file does not do. **NOT ATTEMPTED**.*

`PROOF_STRATEGY` §3 says to re-attempt the next rung the moment one lands rather than banking it,
so the computation was attempted immediately, and it is short. §§4–5 now decide the graph
completely, and the answer is better than the question:

> **`not_supportedIsotropic`** — no supported isotropic vector exists here. The *reach* clause
> alone empties the condition: the massive operator reads off `−v 1` at site `2` and `−v 0` at
> site `3`, so requiring it to vanish outside the half kills both coordinates. Nothing about the
> coupling is used.

> **`reflectedForm_cvec_neg`** — and the reflected form is nevertheless **strictly negative**, at
> the same `(1, −1)` that made the coupling positive in §2. So the graph is not strict; it is not
> even reflection positive.

> **`backward_direction_fails`** — together: **the coupling hypothesis is NECESSARY in
> `strict_iff_not_supportedIsotropic`, not merely used.** Its backward implication says *no
> supported isotropic vector ⟹ strict*, and here the premise holds and the conclusion fails.
> `StrictBiconditional` §8's *"an indefinite coupling breaks the equivalence and this file does
> not claim otherwise"* is now a theorem rather than a caveat.

**The forward direction is untouched and still holds here** — that is §3b, which carries no
coupling hypothesis, and §3 of this file records that it applies. What fails is the converse, and
only the converse.

**No matrix is inverted.** `green` is `massive⁻¹`, but the solve of `massive *ᵥ w = cvec` is done
by hand on the two `2 × 2` blocks and carried with its denominator cleared (`vraw`), so every
verification is a polynomial identity in `m` and `green_mul_massive` turns the checked solve
around. That is why §5 has no side conditions to discharge beyond `m ≠ 0`.

**And it does not weaken anything.** No existing theorem loses a hypothesis and no lattice result
is touched; what changes is that a hypothesis assumed four times is now known to be a real
restriction rather than a formality.

**AND §7 CLOSES THE OTHER SIDE.** §§2–6 show the hypothesis is *necessary*. §7 shows the estate's
only *sufficient condition* for it is **not**: `crossForm_nonpos_of_cross_diag` asks cross-cut
adjacency to be diagonal, and on `K₂,₂` the coupling is nonpositive with the adjacency wide open
(`cross_diag_not_necessary`). `GraphMirrorReflection.crossForm_eq_neg_adj` is what makes that a
one-line computation and also explains it: the coupling is `−wᵀAw` for the cross-adjacency matrix
`A`, so `hcross` says exactly *`A` is positive semidefinite*, and diagonal `0/1` matrices are only
some of those. **No better test is offered** — reducing `hcross` to a PSD check is exact but is
linear algebra per graph rather than a combinatorial criterion, and finding one is NOT ATTEMPTED.
-/

namespace IndefiniteCoupling

open Finset Matrix GraphLaplacian GraphReflection GraphHalfSpace GraphMirrorReflection

/-! ## 1. The graph, the reflection, the half -/

/-- The perfect matching `0 – 3`, `1 – 2` on four vertices. Written as *the labels sum to three*
so that adjacency, symmetry and looplessness are all one arithmetic fact. -/
def crossGraph : SimpleGraph (Fin 4) where
  Adj p q := p.val + q.val = 3 ∧ p ≠ q
  symm := by
    rintro p q ⟨hs, hne⟩
    exact ⟨by omega, hne.symm⟩
  loopless := ⟨fun p h => h.2 rfl⟩

instance : DecidableRel crossGraph.Adj := fun p q =>
  inferInstanceAs (Decidable (p.val + q.val = 3 ∧ p ≠ q))

/-- The reflection: add two, which swaps `0 ↔ 2` and `1 ↔ 3`. -/
def rho : Fin 4 ≃ Fin 4 := Equiv.addRight 2

@[simp] theorem rho_apply (p : Fin 4) : rho p = p + 2 := rfl

/-- The half: the two vertices the reflection moves onto the other pair. -/
def Hh : Finset (Fin 4) := {0, 1}

/-- **THE REFLECTION IS A GRAPH AUTOMORPHISM AND AN INVOLUTION.** It carries each edge to the
other one: `{0,3} ↦ {2,1}` and `{1,2} ↦ {3,0}`. -/
theorem isRefl_rho : GraphReflection.IsRefl crossGraph rho where
  invol := by intro p; revert p; decide
  adj := by intro p q; revert p q; decide

/-- **AND `{0,1}` IS A MIRROR HALF WITH AN EMPTY MIRROR**, because `p ↦ p + 2` has no fixed
point on `Fin 4`. -/
theorem isMirrorHalf_Hh : IsMirrorHalf rho Hh (∅ : Finset (Fin 4)) where
  fixed := by decide
  disj := by decide
  split := by decide

/-! ## 2. The coupling is positive at an explicit vector -/

/-- The test vector: `+1` at site `0`, `−1` at site `1`, zero elsewhere. The opposite signs are
the point — with equal signs the same graph gives `−2`. -/
def wpos : Fin 4 → ℝ := ![1, -1, 0, 0]

/-- **THE CROSS-COUPLING IS `+2` HERE.** Only the two off-diagonal terms survive: site `0` is
adjacent to `3 = rho 1` and site `1` to `2 = rho 0`, each contributing `−(w 0)(w 1) = +1`, while
both diagonal terms vanish because `0` is not adjacent to `2` nor `1` to `3`. -/
theorem crossForm_pos (m : ℝ) : crossForm crossGraph m rho Hh wpos = 2 := by
  classical
  -- the four entries, each off the diagonal, so the mass never enters
  have e01 : GraphLaplacian.massive crossGraph m 0 (rho 1) = -1 := by
    rw [show rho 1 = (3 : Fin 4) from rfl, GraphLaplacian.massive_apply]
    norm_num [show ¬ ((0 : Fin 4) = 3) by decide,
      show crossGraph.Adj 0 3 by decide]
  have e10 : GraphLaplacian.massive crossGraph m 1 (rho 0) = -1 := by
    rw [show rho 0 = (2 : Fin 4) from rfl, GraphLaplacian.massive_apply]
    norm_num [show ¬ ((1 : Fin 4) = 2) by decide,
      show crossGraph.Adj 1 2 by decide]
  have e00 : GraphLaplacian.massive crossGraph m 0 (rho 0) = 0 := by
    rw [show rho 0 = (2 : Fin 4) from rfl, GraphLaplacian.massive_apply]
    norm_num [show ¬ ((0 : Fin 4) = 2) by decide,
      show ¬ crossGraph.Adj 0 2 by decide]
  have e11 : GraphLaplacian.massive crossGraph m 1 (rho 1) = 0 := by
    rw [show rho 1 = (3 : Fin 4) from rfl, GraphLaplacian.massive_apply]
    norm_num [show ¬ ((1 : Fin 4) = 3) by decide,
      show ¬ crossGraph.Adj 1 3 by decide]
  have hsum : ∀ f : Fin 4 → ℝ, ∑ p ∈ Hh, f p = f 0 + f 1 := by
    intro f; simp [Hh]
  rw [crossForm, hsum (fun p => ∑ q ∈ Hh, wpos p * wpos q * _)]
  rw [hsum (fun q => wpos 0 * wpos q * GraphLaplacian.massive crossGraph m 0 (rho q)),
    hsum (fun q => wpos 1 * wpos q * GraphLaplacian.massive crossGraph m 1 (rho q)),
    e00, e01, e10, e11]
  norm_num [wpos]

/-- **SO THE STANDING HYPOTHESIS IS FALSE ON THIS GRAPH.** The first configuration in the estate
that fails it. -/
theorem not_hcross (m : ℝ) : ¬ ∀ w : Fin 4 → ℝ, crossForm crossGraph m rho Hh w ≤ 0 := by
  intro hall
  have := hall wpos
  rw [crossForm_pos m] at this
  linarith

/-! ## 3. What that does to the two theorems -/

/-- **`strict_iff_not_supportedIsotropic` CANNOT BE APPLIED HERE**, and this says so as a theorem
rather than as a remark: its coupling hypothesis is exactly what §2 refutes. -/
theorem biconditional_hypothesis_fails (m : ℝ) :
    ¬ ∀ w : Fin 4 → ℝ, crossForm crossGraph m rho Hh w ≤ 0 :=
  not_hcross m

/-- **AND §3b STILL APPLIES**, which is the point of the file: `not_strict_of_supportedIsotropic`
asks for `IsMirrorHalf`, `IsRefl` and `m ≠ 0`, all of which hold here, and asks nothing about the
coupling. Stated as the instantiated implication rather than proved vacuously — no supported
isotropic vector is exhibited for this graph, and none is claimed. -/
theorem section3b_applies {m : ℝ} (hm : m ≠ 0)
    (hiso : StrictBiconditional.SupportedIsotropic crossGraph m rho Hh ∅) :
    ¬ (∀ c : Fin 4 → ℝ, c ≠ 0 → (∀ p, p ∉ Hh → p ∉ (∅ : Finset (Fin 4)) → c p = 0) →
        0 < GraphReflection.reflectedForm crossGraph m rho c) :=
  StrictBiconditional.not_strict_of_supportedIsotropic isMirrorHalf_Hh isRefl_rho hm hiso


/-! ## 4. No supported isotropic vector lives here

The reach clause alone empties the condition: at site `2` the massive operator reads off `−v 1`
and at site `3` it reads off `−v 0`, so demanding it vanish outside the half kills both
coordinates. Nothing about the coupling is used. -/

theorem massive_mulVec_apply_two {v : Fin 4 → ℝ} (m : ℝ) (h2 : v 2 = 0) (h3 : v 3 = 0) :
    (GraphLaplacian.massive crossGraph m *ᵥ v) 2 = - v 1 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, GraphLaplacian.massive_apply, h2, h3]
  norm_num [show ¬ ((2 : Fin 4) = 0) by decide, show ¬ crossGraph.Adj 2 0 by decide,
    show ¬ ((2 : Fin 4) = 1) by decide, show crossGraph.Adj 2 1 by decide,
    show ((2 : Fin 4) = 2) by decide]

theorem massive_mulVec_apply_three {v : Fin 4 → ℝ} (m : ℝ) (h2 : v 2 = 0) (h3 : v 3 = 0) :
    (GraphLaplacian.massive crossGraph m *ᵥ v) 3 = - v 0 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, GraphLaplacian.massive_apply, h2, h3]
  norm_num [show ¬ ((3 : Fin 4) = 0) by decide, show crossGraph.Adj 3 0 by decide,
    show ¬ ((3 : Fin 4) = 1) by decide, show ¬ crossGraph.Adj 3 1 by decide,
    show ((3 : Fin 4) = 3) by decide]

/-- **THE CONDITION IS EMPTY HERE.** -/
theorem not_supportedIsotropic (m : ℝ) :
    ¬ StrictBiconditional.SupportedIsotropic crossGraph m rho Hh (∅ : Finset (Fin 4)) := by
  rintro ⟨v, hv0, hvsupp, -, hreach⟩
  have h2 : v 2 = 0 := hvsupp 2 (by decide)
  have h3 : v 3 = 0 := hvsupp 3 (by decide)
  have r2 := hreach 2 (by decide) (by simp)
  have r3 := hreach 3 (by decide) (by simp)
  rw [massive_mulVec_apply_two m h2 h3] at r2
  rw [massive_mulVec_apply_three m h2 h3] at r3
  refine hv0 (funext fun p => ?_)
  fin_cases p
  · simpa using neg_eq_zero.mp r3
  · simpa using neg_eq_zero.mp r2
  · simpa using h2
  · simpa using h3

/-! ## 5. And the reflected form is NEGATIVE — so the hypothesis is necessary, not merely used

`StrictBiconditional` §8 says *"an indefinite coupling breaks the equivalence and this file does
not claim otherwise"*. §4 gives one side of that; this gives the other, and together they turn the
caveat into a theorem.

**No matrix inverse is computed.** `green` is `massive⁻¹`, and rather than invert a `4 × 4` matrix
the solve is done by hand and checked: `wsol` is exhibited, `massive *ᵥ wsol = cvec` is verified
entrywise, and `green_mul_massive` turns that into `green *ᵥ cvec = wsol`. -/

/-- The diagonal entry of the massive operator here: degree one plus the mass. -/
noncomputable def dd (m : ℝ) : ℝ := 1 + m ^ 2

theorem dd_sq_sub_one_pos {m : ℝ} (hm : m ≠ 0) : 0 < dd m ^ 2 - 1 := by
  have h : 0 < m ^ 2 := by positivity
  simp only [dd]
  nlinarith

/-- Every vertex of a perfect matching has one neighbour. -/
theorem degree_eq_one (p : Fin 4) : crossGraph.degree p = 1 := by revert p; decide

/-- The coefficient family: `+1` and `−1` on the half. Opposite signs again — the same feature
that made the coupling positive in §2. Written with `if` rather than `![…]` so that evaluating at
`rho p` is a decidable comparison rather than a list projection. -/
def cvec : Fin 4 → ℝ := fun p => if p = 0 then 1 else if p = 1 then -1 else 0

/-- The solve of `massive *ᵥ w = cvec`, **cleared of its denominator**: on the block `{0,3}` the
matrix is `[[d,−1],[−1,d]]` against `(1,0)` and on `{1,2}` the same against `(−1,0)`, so the
solution is `(d,−d,−1,1)` over `d² − 1`. Carrying the numerator alone keeps every verification
below a polynomial identity — no inverse is ever written and no denominator ever has to be
discharged. -/
noncomputable def vraw (m : ℝ) : Fin 4 → ℝ := fun p =>
  if p = 0 then dd m else if p = 1 then -dd m else if p = 2 then -1 else 1

/-- **THE SOLVE, CHECKED ENTRYWISE.** Four polynomial identities in `m`. -/
theorem massive_mulVec_vraw (m : ℝ) :
    GraphLaplacian.massive crossGraph m *ᵥ vraw m = (dd m ^ 2 - 1) • cvec := by
  funext p
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, GraphLaplacian.massive_apply,
    degree_eq_one, vraw, cvec, dd, Pi.smul_apply, smul_eq_mul]
  fin_cases p <;> norm_num [crossGraph, Fin.ext_iff] <;> ring

/-- And so the Green function's action on `cvec` is known without inverting anything:
`green_mul_massive` turns the checked solve around. -/
theorem green_mulVec_cvec {m : ℝ} (hm : m ≠ 0) :
    (dd m ^ 2 - 1) • (GraphLaplacian.green crossGraph m *ᵥ cvec) = vraw m := by
  rw [← Matrix.mulVec_smul, ← massive_mulVec_vraw m, Matrix.mulVec_mulVec,
    GraphLaplacian.green_mul_massive crossGraph hm, Matrix.one_mulVec]

/-- **THE REFLECTED FORM, CLEARED OF ITS DENOMINATOR.** Only two of the sixteen terms survive:
`cvec` is supported on `{0,1}`, `rho 0 = 2` and `rho 1 = 3`, and `vraw` is `−1` at `2` and `+1`
at `3`. -/
theorem reflectedForm_cvec_scaled {m : ℝ} (hm : m ≠ 0) :
    (dd m ^ 2 - 1) * GraphReflection.reflectedForm crossGraph m rho cvec = -2 := by
  have key : ∀ p : Fin 4,
      ∑ q, cvec p * cvec q * GraphLaplacian.green crossGraph m (rho p) q
        = cvec p * (GraphLaplacian.green crossGraph m *ᵥ cvec) (rho p) := by
    intro p
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hg : ∀ p : Fin 4,
      (dd m ^ 2 - 1) * (GraphLaplacian.green crossGraph m *ᵥ cvec) p = vraw m p := by
    intro p
    have := congrFun (green_mulVec_cvec hm) p
    simpa [Pi.smul_apply, smul_eq_mul] using this
  have hc1 : cvec 1 = -1 := rfl
  have hc2 : cvec 2 = 0 := rfl
  have hc3 : cvec 3 = 0 := rfl
  have hv2 : vraw m 2 = -1 := rfl
  have hv3 : vraw m 3 = 1 := rfl
  have e2 := hg 2
  have e3 := hg 3
  rw [hv2] at e2
  rw [hv3] at e3
  simp only [GraphReflection.reflectedForm, key, Fin.sum_univ_four,
    show ((rho 0 : Fin 4)) = 2 from rfl, show ((rho 1 : Fin 4)) = 3 from rfl,
    show ((rho 2 : Fin 4)) = 0 from rfl, show ((rho 3 : Fin 4)) = 1 from rfl,
    show cvec 0 = 1 from rfl, hc1, hc2, hc3]
  ring_nf
  ring_nf at e2 e3
  linarith [e2, e3]

theorem reflectedForm_cvec_neg {m : ℝ} (hm : m ≠ 0) :
    GraphReflection.reflectedForm crossGraph m rho cvec < 0 := by
  have hpos := dd_sq_sub_one_pos hm
  have h := reflectedForm_cvec_scaled hm
  nlinarith [h, hpos]

/-- **AND SO THE FORM IS NOT STRICT** — indeed not even nonnegative, so this graph is not
reflection positive either. -/
theorem not_strict {m : ℝ} (hm : m ≠ 0) :
    ¬ (∀ c : Fin 4 → ℝ, c ≠ 0 → (∀ p, p ∉ Hh → p ∉ (∅ : Finset (Fin 4)) → c p = 0) →
        0 < GraphReflection.reflectedForm crossGraph m rho c) := by
  intro hstrict
  have hne : cvec ≠ 0 := fun hc => by
    have := congrFun hc 0
    norm_num [cvec] at this
  have hsupp : ∀ p, p ∉ Hh → p ∉ (∅ : Finset (Fin 4)) → cvec p = 0 := by
    intro p hp _
    fin_cases p
    · exact absurd (by decide : (0 : Fin 4) ∈ Hh) hp
    · exact absurd (by decide : (1 : Fin 4) ∈ Hh) hp
    · norm_num [cvec]
    · norm_num [cvec]
  exact absurd (hstrict cvec hne hsupp) (not_lt.mpr (reflectedForm_cvec_neg hm).le)

/-! ## 6. And the same witness settles the wall's MAIN theorem

`strict_iff_not_supportedIsotropic` is a refinement. `reflectionPositive_mirror` is the theorem
this wall rests on, and it carries the same hypothesis. One line of §5 settles that too, and it is
the stronger statement of the two. -/

/-- **`GraphReflection.ReflectionPositive` FAILS HERE**, stated against the estate's own predicate.
The mirror is empty, so *supported on `H ∪ Mir`* is exactly `ReflectionPositive`'s support
condition and the two line up without adjustment. -/
theorem not_reflectionPositive {m : ℝ} (hm : m ≠ 0) :
    ¬ GraphReflection.ReflectionPositive crossGraph m rho Hh := by
  intro hrp
  have hsupp : ∀ p, p ∉ Hh → cvec p = 0 := by
    intro p hp
    fin_cases p
    · exact absurd (by decide : (0 : Fin 4) ∈ Hh) hp
    · exact absurd (by decide : (1 : Fin 4) ∈ Hh) hp
    · norm_num [cvec]
    · norm_num [cvec]
  exact absurd (hrp cvec hsupp) (not_le.mpr (reflectedForm_cvec_neg hm))

/-- **SO `hcross` IS NECESSARY IN `reflectionPositive_mirror` TOO**, and that is the sharper of the
two necessity results: `strict_iff_not_supportedIsotropic` is a refinement of the wall, and
`reflectionPositive_mirror` is the wall. Its other three hypotheses all hold here
(`isMirrorHalf_Hh`, `isRefl_rho`, `hm`), so the coupling hypothesis is the only thing standing
between them and a false conclusion. -/
theorem hcross_necessary_for_positivity {m : ℝ} (hm : m ≠ 0) :
    IsMirrorHalf rho Hh (∅ : Finset (Fin 4))
      ∧ GraphReflection.IsRefl crossGraph rho
      ∧ ¬ (∀ w : Fin 4 → ℝ, crossForm crossGraph m rho Hh w ≤ 0)
      ∧ ¬ GraphReflection.ReflectionPositive crossGraph m rho Hh :=
  ⟨isMirrorHalf_Hh, isRefl_rho, not_hcross m, not_reflectionPositive hm⟩

/-- **THE COUPLING HYPOTHESIS IS NECESSARY IN `strict_iff_not_supportedIsotropic`, NOT MERELY
USED.** Both sides of its backward implication are settled here and they disagree: no supported
isotropic vector exists, and the form is still not strict. So `hcross` cannot be dropped from that
direction, and `StrictBiconditional` §8's *"an indefinite coupling breaks the equivalence and this
file does not claim otherwise"* is now a theorem rather than a caveat.

**What is NOT claimed.** The forward direction is untouched — `StrictBiconditional` §3b proves it
with no coupling hypothesis at all, and §3 of this file records that it applies here. What fails
is the converse, and only the converse. -/
theorem backward_direction_fails {m : ℝ} (hm : m ≠ 0) :
    ¬ StrictBiconditional.SupportedIsotropic crossGraph m rho Hh (∅ : Finset (Fin 4))
      ∧ ¬ (∀ c : Fin 4 → ℝ, c ≠ 0 → (∀ p, p ∉ Hh → p ∉ (∅ : Finset (Fin 4)) → c p = 0) →
            0 < GraphReflection.reflectedForm crossGraph m rho c) :=
  ⟨not_supportedIsotropic m, not_strict hm⟩

/-! ## 7. The other side: the estate's only route to `hcross` is strictly narrower than `hcross`

§§2–6 showed the hypothesis is **necessary**. This shows the estate's only *sufficient condition*
for it is **not**.

`GraphMirrorReflection.crossForm_nonpos_of_cross_diag` asks that cross-cut adjacency be diagonal —
`p, q ∈ H` with `G.Adj p (θ q)` force `p = q` — and it is the one route to `hcross` anywhere here.
`crossForm_eq_neg_adj` (`dd7ecb4`) says why it works and also why it is not the whole story: the
coupling is `−wᵀAw` for the cross-adjacency matrix `A`, so **`hcross` says exactly that `A` is
positive semidefinite**, and diagonal `0/1` matrices are only some of those.

The complete bipartite graph `K₂,₂` gives `A` the all-ones matrix. Non-diagonal, and PSD because
`wᵀJw = (w₀ + w₁)²`. -/

/-- `K₂,₂` on `Fin 4`: joined exactly when one endpoint is in `{0,1}` and the other is not. -/
def bipGraph : SimpleGraph (Fin 4) where
  Adj p q := (p.val < 2) ≠ (q.val < 2)
  symm := by intro p q h; exact h.symm
  loopless := ⟨fun p h => h rfl⟩

instance : DecidableRel bipGraph.Adj := fun p q =>
  inferInstanceAs (Decidable ((p.val < 2) ≠ (q.val < 2)))

theorem isRefl_rho_bip : GraphReflection.IsRefl bipGraph rho where
  invol := by intro p; revert p; decide
  adj := by intro p q; revert p q; decide

/-- **THE CROSS-ADJACENCY IS NOT DIAGONAL HERE**, so
`crossForm_nonpos_of_cross_diag` cannot be applied: site `0` is joined to `3 = rho 1`. -/
theorem cross_not_diagonal :
    ¬ (∀ p ∈ Hh, ∀ q ∈ Hh, bipGraph.Adj p (rho q) → p = q) := by
  intro h
  have : (0 : Fin 4) = 1 := h 0 (by decide) 1 (by decide) (by decide)
  exact absurd this (by decide)

/-- **AND THE COUPLING IS NONPOSITIVE ANYWAY**, because the all-ones matrix is positive
semidefinite: the form is `−(w 0 + w 1)²`. Computed through `crossForm_eq_neg_adj`, so the mass
never appears — which is the point of that lemma. -/
theorem crossForm_bip (m : ℝ) (w : Fin 4 → ℝ) :
    crossForm bipGraph m rho Hh w = -((w 0 + w 1) ^ 2) := by
  classical
  rw [GraphMirrorReflection.crossForm_eq_neg_adj isMirrorHalf_Hh m w]
  have hH : Hh = ({0, 1} : Finset (Fin 4)) := rfl
  rw [hH]
  simp only [Finset.sum_insert (by decide : (0 : Fin 4) ∉ ({1} : Finset (Fin 4))),
    Finset.sum_singleton, rho_apply,
    show ((0 : Fin 4) + 2) = 2 from rfl, show ((1 : Fin 4) + 2) = 3 from rfl]
  norm_num [show bipGraph.Adj 0 2 by decide, show bipGraph.Adj 0 3 by decide,
    show bipGraph.Adj 1 2 by decide, show bipGraph.Adj 1 3 by decide]
  ring

theorem hcross_bip (m : ℝ) : ∀ w : Fin 4 → ℝ, crossForm bipGraph m rho Hh w ≤ 0 := by
  intro w
  rw [crossForm_bip m w]
  simpa using sq_nonneg (w 0 + w 1)

/-- **SO THE SUFFICIENT CONDITION IS STRICTLY SUFFICIENT.** `hcross` holds on `K₂,₂` and the
estate's only route to it does not apply. Together with §6 the picture is complete: the hypothesis
cannot be dropped, and the test for it cannot be the last word.

**What this does NOT say.** It gives no better test. `crossForm_eq_neg_adj` reduces `hcross` to
*the cross-adjacency matrix is positive semidefinite*, which is exact but is linear algebra per
graph, not a combinatorial criterion — and finding one is **NOT ATTEMPTED** (`ERRATUM 71`
addendum 3): nothing was tried. What is now known is that any such criterion must be strictly
weaker than diagonality. -/
theorem cross_diag_not_necessary (m : ℝ) :
    GraphReflection.IsRefl bipGraph rho
      ∧ IsMirrorHalf rho Hh (∅ : Finset (Fin 4))
      ∧ (∀ w : Fin 4 → ℝ, crossForm bipGraph m rho Hh w ≤ 0)
      ∧ ¬ (∀ p ∈ Hh, ∀ q ∈ Hh, bipGraph.Adj p (rho q) → p = q) :=
  ⟨isRefl_rho_bip, isMirrorHalf_Hh, hcross_bip m, cross_not_diagonal⟩

end IndefiniteCoupling
