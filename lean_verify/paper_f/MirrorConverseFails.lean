import ReflectionConverse

/-!
# The converse is false once the reflection has fixed points

(And seven vertices is the smallest place it can be.)

`ReflectionConverse` proves that reflection positivity is equivalent to `hcross` on every finite
graph whose reflection is **fixed-point-free**, at every mass. Its §2 spends that hypothesis and
nothing else does. The obvious question — is it load-bearing, or an artefact of the route? — is
answered here, and the answer is that it is load-bearing.

`mirGraph` has seven vertices, a two-site half, and a **three-site mirror layer**. It

* **fails `hcross`** (§3), at the same shape of vector every other witness in the estate uses;
* **is reflection positive at `m = 1/2`** (§5), so `ReflectionConverse`'s conclusion is false here;
* **is not reflection positive at `m = 11`** (§6).

So the equivalence fails with a mirror, and `GraphMirrorReflection.reflectionPositive_mirror`
carrying `Mir` through is not evidence that the converse does too — sufficiency and necessity part
company exactly at the fixed layer.

## The second thing it settles, which the estate had framed and never fed

`CrossFormMatrix` §7 wrote down what a graph would have to look like to refute a converse:

> `not_converse_of_mass_dependent` — a graph reflection positive at one nonzero mass and not at
> another.

None was known, and `GreenLargeMass.reflectionPositive_all_or_bounded` had narrowed the
possibilities to *positive at every mass* or *positive only below a threshold* without deciding
which graphs do the latter. **`mirGraph` does the latter**, and §7 states the mass-dependence as
one theorem. Reflection positivity is genuinely a function of the mass — but only once the
reflection has fixed points, since `ReflectionConverse.reflectionPositive_mass_independent` rules
it out otherwise. The two results are each other's sharpness.

## Why seven, and how that was established

Write `n = 2|H| + |Mir|`. Two vertices in the half are forced — a one-by-one cut matrix is a
single nonnegative entry, so `hcross` cannot fail there — and every involution with a given
`|H|` and `|Mir|` is conjugate to a standard one, the invariant graphs being carried along, so
fixing one representative `σ` per case loses nothing. Four cases sit below seven vertices:

* `(|H|,|Mir|) = (2,0)` at `n = 4` and `(3,0)` at `n = 6` need **no computation at all** — they
  are `ReflectionConverse`'s theorem;
* `(2,1)` at `n = 5`, with 24 graphs failing `hcross`, and `(2,2)` at `n = 6`, with 192, were
  decided **exactly and at every mass**. When `|H| = 2` the Green function is entrywise
  nonnegative, so reflection positivity reduces to the single condition `det Y(t) ≥ 0`, and
  `det Y(t) · det(N(t))²` is a polynomial in `t = m²` over `ℚ`. It was interpolated exactly and
  its sign on `t > 0` settled by a **Sturm sequence**, not by sampling. It is negative
  throughout, in all 216 cases.

At `n = 7` the case `(2,3)` breaks it, in exactly 56 of the 3072 graphs that fail `hcross` — the
same 56 an independent mass-grid search returns, which is what cross-checks the polynomial code.
Those that break it with the fewest edges have nine. `mirGraph` is one of them.

That computation is **not part of the formal development**. What is proved below is that this one
graph is a counterexample; the minimality claim is recorded in `WALLS` as computation, marked as
such.

## How reflection positivity is proved without inverting a seven-by-seven matrix

`StepGraphSmallMass` established its Green-function entries by solving the defining linear system
column by column. Nothing like that is needed here, because reflection positivity never asks for
the inverse — it asks for two energies, and `GraphReflection.reflectedForm_eq` says the reflected
form is their difference.

An energy `⟪y, N⁻¹y⟫` is computed **exactly** by exhibiting one vector: if `N x = y` then
`⟪y, N⁻¹y⟫ = ⟪y, x⟫` (§1). The symmetric and antisymmetric parts of a vector supported on the
half are two explicit one-parameter-per-site families, and the two vectors that `N` maps onto them
are written down in §4 with rational coefficients and verified by seven multiplications each. The
reflected form is then an explicit binary quadratic form,

    4 · reflectedForm(c) = (19712 a² + 42368 ab + 24768 b²) / 9635,

whose discriminant is `−157859840`, and §5 is that sign. No matrix is inverted anywhere in this
file.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace MirrorConverseFails

open Matrix GraphLaplacian GraphReflection GraphMirrorReflection

/-! ## 1. An energy is exact as soon as one vector is exhibited

The companion of `GraphMirrorReflection.dotProduct_inv_le`. That lemma bounds `⟪y, N⁻¹y⟫` below
by completing the square at an arbitrary test vector; this one says the bound is an equality, and
identifies the value, as soon as the test vector actually solves `N x = y`. It is the only reason
this file needs no inverse.
-/

theorem dotProduct_inv_of_mulVec {V : Type*} [Fintype V] [DecidableEq V] {N : Matrix V V ℝ}
    (hN : N.PosDef) {x y : V → ℝ} (h : N *ᵥ x = y) : y ⬝ᵥ (N⁻¹ *ᵥ y) = y ⬝ᵥ x := by
  have hdet : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp hN.isUnit
  rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-! ## 2. The graph, the reflection, the half and the mirror

`τ` swaps `0 ↔ 2` and `1 ↔ 3` and fixes `4, 5, 6`. The half is `{0, 1}`, its image is `{2, 3}`,
and the mirror layer is the other three. The cut is what matters: `1` is joined to **both** mirror
images, `0` only to the image of `1` — so the cut relation is not transitive, which is precisely
`hcross` failing. Each mirror vertex is joined to `0` and to its image `2`, and it is those nine
edges that let the fixed layer pay for the failure.
-/

/-- Adjacency, as a table. Nine edges, listed in both directions. -/
def mirE (p q : Fin 7) : Bool :=
  match p.val, q.val with
  | 0, 3 | 3, 0 | 0, 4 | 4, 0 | 0, 5 | 5, 0 | 0, 6 | 6, 0
  | 1, 2 | 2, 1 | 1, 3 | 3, 1
  | 2, 4 | 4, 2 | 2, 5 | 5, 2 | 2, 6 | 6, 2 => true
  | _, _ => false

/-- **THE COUNTEREXAMPLE.** Seven vertices, nine edges. -/
def mirGraph : SimpleGraph (Fin 7) where
  Adj p q := mirE p q = true
  symm := by
    have h : ∀ p q : Fin 7, mirE p q = true → mirE q p = true := by decide
    intro p q hpq
    exact h p q hpq
  loopless := ⟨by
    have h : ∀ p : Fin 7, mirE p p ≠ true := by decide
    intro p hp
    exact h p hp⟩

instance : DecidableRel mirGraph.Adj := fun p q => inferInstanceAs (Decidable (mirE p q = true))

/-- The reflection, as an involution of `Fin 7` with three fixed points. -/
def tauFun : Fin 7 → Fin 7 := ![2, 3, 0, 1, 4, 5, 6]

theorem tauFun_invol : Function.Involutive tauFun := by intro p; revert p; decide

/-- `τ : 0 ↔ 2`, `1 ↔ 3`, fixing `4, 5, 6`. -/
def tau : Fin 7 ≃ Fin 7 := Function.Involutive.toPerm tauFun tauFun_invol

@[simp] theorem tau_apply (p : Fin 7) : tau p = tauFun p := rfl

/-- The half. -/
def Hm : Finset (Fin 7) := {0, 1}

/-- The fixed layer. Three vertices, and §5 shows the third one is doing real work. -/
def Mirm : Finset (Fin 7) := {4, 5, 6}

theorem isRefl_tau : GraphReflection.IsRefl mirGraph tau where
  invol := tauFun_invol
  adj := by intro p q; revert p q; decide

theorem isMirrorHalf_Hm : IsMirrorHalf tau Hm Mirm where
  fixed := by decide
  disj := by decide
  split := by decide

/-- **AND IT IS NOT A HALF IN THE ESTATE'S OTHER SENSE**, which is exactly why
`ReflectionConverse` does not apply: `τ` fixes `4`. -/
theorem not_isHalf_Hm : ¬ GraphHalfSpace.IsHalf tau Hm := by
  intro h
  have := h 4
  revert this
  decide

theorem sum_Hm (f : Fin 7 → ℝ) : ∑ p ∈ Hm, f p = f 0 + f 1 := by
  simp [Hm]

theorem degree_zero : mirGraph.degree 0 = 4 := by decide
theorem degree_one : mirGraph.degree 1 = 2 := by decide
theorem degree_two : mirGraph.degree 2 = 4 := by decide
theorem degree_three : mirGraph.degree 3 = 2 := by decide
theorem degree_le_four (v : Fin 7) : mirGraph.degree v ≤ 4 := by revert v; decide

/-! ## 3. The cut is intransitive, so `hcross` fails

`0` is joined to `τ 1` and `1` is joined to `τ 0`, but `0` is not joined to `τ 0`. That is the
`diag` clause of `CrossBlockStructure.IsCrossBlock` failing, and the refuting vector is the same
`(1, −1)` the estate uses everywhere.
-/

/-- The refuting vector for the coupling. -/
def wm : Fin 7 → ℝ := ![1, -1, 0, 0, 0, 0, 0]

theorem wm_supported : ∀ p, p ∉ Hm → wm p = 0 := by
  intro p hp
  fin_cases p <;> simp_all [wm, Hm]

theorem not_isCrossBlock_mirGraph : ¬ CrossBlockStructure.IsCrossBlock mirGraph tau Hm := by
  decide

/-- **THE COUPLING IS `+1`.** Mass-free, as `crossForm_mass_independent` requires. -/
theorem crossForm_mir_pos (m : ℝ) : crossForm mirGraph m tau Hm wm = 1 := by
  have t0 : tau 0 = 2 := rfl
  have t1 : tau 1 = 3 := rfl
  have w0 : wm 0 = 1 := rfl
  have w1 : wm 1 = -1 := rfl
  simp only [crossForm, sum_Hm, t0, t1, w0, w1, GraphLaplacian.massive_apply,
    if_neg (show ¬ ((0 : Fin 7) = 2) by decide), if_neg (show ¬ ((0 : Fin 7) = 3) by decide),
    if_neg (show ¬ ((1 : Fin 7) = 2) by decide), if_neg (show ¬ ((1 : Fin 7) = 3) by decide),
    if_neg (show ¬ mirGraph.Adj 0 2 by decide), if_pos (show mirGraph.Adj 0 3 by decide),
    if_pos (show mirGraph.Adj 1 2 by decide), if_pos (show mirGraph.Adj 1 3 by decide)]
  ring

theorem hcross_fails (m : ℝ) : ¬ ∀ w : Fin 7 → ℝ, crossForm mirGraph m tau Hm w ≤ 0 := by
  intro h
  have := h wm
  rw [crossForm_mir_pos] at this
  norm_num at this

/-! ## 4. The operator applied to the two explicit solutions

Seven row identities, each a single `decide` on the adjacency plus arithmetic, and then the two
vectors that `N` carries onto the symmetric and antisymmetric parts. The odd solution is a
two-by-two solve, because `N` preserves the odd sector and that sector is spanned by the half; the
even solution is a five-by-five one, and the three equal entries on the mirror are why the fixed
layer changes the answer.
-/

variable {mm : ℝ}

theorem row0 (v : Fin 7 → ℝ) :
    (massive mirGraph mm *ᵥ v) 0 = (4 + mm ^ 2) * v 0 - v 3 - v 4 - v 5 - v 6 := by
  simp +decide [Matrix.mulVec, dotProduct, Fin.sum_univ_seven,
    GraphLaplacian.massive_apply, degree_zero]
  ring

theorem row1 (v : Fin 7 → ℝ) :
    (massive mirGraph mm *ᵥ v) 1 = (2 + mm ^ 2) * v 1 - v 2 - v 3 := by
  simp +decide [Matrix.mulVec, dotProduct, Fin.sum_univ_seven,
    GraphLaplacian.massive_apply, degree_one]
  ring

theorem row2 (v : Fin 7 → ℝ) :
    (massive mirGraph mm *ᵥ v) 2 = (4 + mm ^ 2) * v 2 - v 1 - v 4 - v 5 - v 6 := by
  simp +decide [Matrix.mulVec, dotProduct, Fin.sum_univ_seven,
    GraphLaplacian.massive_apply, degree_two]
  ring

theorem row3 (v : Fin 7 → ℝ) :
    (massive mirGraph mm *ᵥ v) 3 = (2 + mm ^ 2) * v 3 - v 0 - v 1 := by
  simp +decide [Matrix.mulVec, dotProduct, Fin.sum_univ_seven,
    GraphLaplacian.massive_apply, degree_three]
  ring

theorem row4 (v : Fin 7 → ℝ) :
    (massive mirGraph mm *ᵥ v) 4 = (2 + mm ^ 2) * v 4 - v 0 - v 2 := by
  simp +decide [Matrix.mulVec, dotProduct, Fin.sum_univ_seven,
    GraphLaplacian.massive_apply, show mirGraph.degree 4 = 2 by decide]
  ring

theorem row5 (v : Fin 7 → ℝ) :
    (massive mirGraph mm *ᵥ v) 5 = (2 + mm ^ 2) * v 5 - v 0 - v 2 := by
  simp +decide [Matrix.mulVec, dotProduct, Fin.sum_univ_seven,
    GraphLaplacian.massive_apply, show mirGraph.degree 5 = 2 by decide]
  ring

theorem row6 (v : Fin 7 → ℝ) :
    (massive mirGraph mm *ᵥ v) 6 = (2 + mm ^ 2) * v 6 - v 0 - v 2 := by
  simp +decide [Matrix.mulVec, dotProduct, Fin.sum_univ_seven,
    GraphLaplacian.massive_apply, show mirGraph.degree 6 = 2 by decide]
  ring

/-- The vector `N` carries onto the **antisymmetric** part of `(a, b)`. Odd, so it vanishes on the
mirror; the two-by-two system has determinant `m⁴ + 7m² + 11`, which is `205/16` at `m = 1/2`. -/
noncomputable def oddSol (a b : ℝ) : Fin 7 → ℝ :=
  ![(52 * a - 16 * b) / 205, (-16 * a + 68 * b) / 205,
    -((52 * a - 16 * b) / 205), -((-16 * a + 68 * b) / 205), 0, 0, 0]

/-- The vector `N` carries onto the **symmetric** part of `(a, b)`. Even, and **nonzero on the
mirror** — that entry is the whole difference between this file and `ReflectionConverse`. -/
noncomputable def evenSol (a b : ℝ) : Fin 7 → ℝ :=
  ![(60 * a + 48 * b) / 47, (48 * a + 76 * b) / 47,
    (60 * a + 48 * b) / 47, (48 * a + 76 * b) / 47,
    (480 * a + 384 * b) / 423, (480 * a + 384 * b) / 423, (480 * a + 384 * b) / 423]

/-- The vector supported on the half with values `a` at `0` and `b` at `1`. -/
def cvec (a b : ℝ) : Fin 7 → ℝ := ![a, b, 0, 0, 0, 0, 0]

theorem cvec_of_supported {c : Fin 7 → ℝ} (hc : ∀ p, p ∉ Hm → c p = 0) : c = cvec (c 0) (c 1) := by
  funext p
  fin_cases p <;> simp only [cvec] <;>
    first
      | rfl
      | exact hc _ (by decide)

theorem anti_cvec (a b : ℝ) :
    GraphReflection.anti tau (cvec a b) = ![a, b, -a, -b, 0, 0, 0] := by
  funext p
  fin_cases p <;> simp [GraphReflection.anti, cvec, tauFun]

theorem sym_cvec (a b : ℝ) :
    GraphReflection.sym tau (cvec a b) = ![a, b, a, b, 0, 0, 0] := by
  funext p
  fin_cases p <;> simp [GraphReflection.sym, cvec, tauFun]

private theorem oddVals (a b : ℝ) :
    oddSol a b 0 = (52 * a - 16 * b) / 205 ∧ oddSol a b 1 = (-16 * a + 68 * b) / 205
      ∧ oddSol a b 2 = -((52 * a - 16 * b) / 205) ∧ oddSol a b 3 = -((-16 * a + 68 * b) / 205)
      ∧ oddSol a b 4 = 0 ∧ oddSol a b 5 = 0 ∧ oddSol a b 6 = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem evenVals (a b : ℝ) :
    evenSol a b 0 = (60 * a + 48 * b) / 47 ∧ evenSol a b 1 = (48 * a + 76 * b) / 47
      ∧ evenSol a b 2 = (60 * a + 48 * b) / 47 ∧ evenSol a b 3 = (48 * a + 76 * b) / 47
      ∧ evenSol a b 4 = (480 * a + 384 * b) / 423 ∧ evenSol a b 5 = (480 * a + 384 * b) / 423
      ∧ evenSol a b 6 = (480 * a + 384 * b) / 423 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mulVec_oddSol (a b : ℝ) :
    massive mirGraph (1 / 2) *ᵥ oddSol a b = GraphReflection.anti tau (cvec a b) := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := oddVals a b
  rw [anti_cvec]
  have h0 : (massive mirGraph (1 / 2) *ᵥ oddSol a b) 0 = (a : ℝ) := by
    rw [row0, e0, e3, e4, e5, e6]; ring
  have h1 : (massive mirGraph (1 / 2) *ᵥ oddSol a b) 1 = (b : ℝ) := by
    rw [row1, e1, e2, e3]; ring
  have h2 : (massive mirGraph (1 / 2) *ᵥ oddSol a b) 2 = (-a : ℝ) := by
    rw [row2, e1, e2, e4, e5, e6]; ring
  have h3 : (massive mirGraph (1 / 2) *ᵥ oddSol a b) 3 = (-b : ℝ) := by
    rw [row3, e0, e1, e3]; ring
  have h4 : (massive mirGraph (1 / 2) *ᵥ oddSol a b) 4 = (0 : ℝ) := by
    rw [row4, e0, e2, e4]; ring
  have h5 : (massive mirGraph (1 / 2) *ᵥ oddSol a b) 5 = (0 : ℝ) := by
    rw [row5, e0, e2, e5]; ring
  have h6 : (massive mirGraph (1 / 2) *ᵥ oddSol a b) 6 = (0 : ℝ) := by
    rw [row6, e0, e2, e6]; ring
  funext p
  fin_cases p <;> assumption

theorem mulVec_evenSol (a b : ℝ) :
    massive mirGraph (1 / 2) *ᵥ evenSol a b = GraphReflection.sym tau (cvec a b) := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := evenVals a b
  rw [sym_cvec]
  have h0 : (massive mirGraph (1 / 2) *ᵥ evenSol a b) 0 = (a : ℝ) := by
    rw [row0, e0, e3, e4, e5, e6]; ring
  have h1 : (massive mirGraph (1 / 2) *ᵥ evenSol a b) 1 = (b : ℝ) := by
    rw [row1, e1, e2, e3]; ring
  have h2 : (massive mirGraph (1 / 2) *ᵥ evenSol a b) 2 = (a : ℝ) := by
    rw [row2, e1, e2, e4, e5, e6]; ring
  have h3 : (massive mirGraph (1 / 2) *ᵥ evenSol a b) 3 = (b : ℝ) := by
    rw [row3, e0, e1, e3]; ring
  have h4 : (massive mirGraph (1 / 2) *ᵥ evenSol a b) 4 = (0 : ℝ) := by
    rw [row4, e0, e2, e4]; ring
  have h5 : (massive mirGraph (1 / 2) *ᵥ evenSol a b) 5 = (0 : ℝ) := by
    rw [row5, e0, e2, e5]; ring
  have h6 : (massive mirGraph (1 / 2) *ᵥ evenSol a b) 6 = (0 : ℝ) := by
    rw [row6, e0, e2, e6]; ring
  funext p
  fin_cases p <;> assumption

/-! ## 5. Reflection positive at `m = 1/2`

The two energies are read off §4, their difference is an explicit binary quadratic form, and the
form is positive definite. This is the theorem `ReflectionConverse` forbids on a fixed-point-free
reflection.
-/

/-- The symmetric energy, evaluated. -/
theorem dot_even (a b : ℝ) :
    (![a, b, a, b, 0, 0, 0] : Fin 7 → ℝ) ⬝ᵥ evenSol a b
      = (120 * a ^ 2 + 192 * a * b + 152 * b ^ 2) / 47 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := evenVals a b
  have v0 : (![a, b, a, b, 0, 0, 0] : Fin 7 → ℝ) 0 = a := rfl
  have v1 : (![a, b, a, b, 0, 0, 0] : Fin 7 → ℝ) 1 = b := rfl
  have v2 : (![a, b, a, b, 0, 0, 0] : Fin 7 → ℝ) 2 = a := rfl
  have v3 : (![a, b, a, b, 0, 0, 0] : Fin 7 → ℝ) 3 = b := rfl
  have v4 : (![a, b, a, b, 0, 0, 0] : Fin 7 → ℝ) 4 = 0 := rfl
  have v5 : (![a, b, a, b, 0, 0, 0] : Fin 7 → ℝ) 5 = 0 := rfl
  have v6 : (![a, b, a, b, 0, 0, 0] : Fin 7 → ℝ) 6 = 0 := rfl
  rw [dotProduct, Fin.sum_univ_seven, v0, v1, v2, v3, v4, v5, v6, e0, e1, e2, e3, e4, e5, e6]
  ring

/-- The antisymmetric energy, evaluated. -/
theorem dot_odd (a b : ℝ) :
    (![a, b, -a, -b, 0, 0, 0] : Fin 7 → ℝ) ⬝ᵥ oddSol a b
      = (104 * a ^ 2 - 64 * a * b + 136 * b ^ 2) / 205 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := oddVals a b
  have v0 : (![a, b, -a, -b, 0, 0, 0] : Fin 7 → ℝ) 0 = a := rfl
  have v1 : (![a, b, -a, -b, 0, 0, 0] : Fin 7 → ℝ) 1 = b := rfl
  have v2 : (![a, b, -a, -b, 0, 0, 0] : Fin 7 → ℝ) 2 = -a := rfl
  have v3 : (![a, b, -a, -b, 0, 0, 0] : Fin 7 → ℝ) 3 = -b := rfl
  have v4 : (![a, b, -a, -b, 0, 0, 0] : Fin 7 → ℝ) 4 = 0 := rfl
  have v5 : (![a, b, -a, -b, 0, 0, 0] : Fin 7 → ℝ) 5 = 0 := rfl
  have v6 : (![a, b, -a, -b, 0, 0, 0] : Fin 7 → ℝ) 6 = 0 := rfl
  rw [dotProduct, Fin.sum_univ_seven, v0, v1, v2, v3, v4, v5, v6, e0, e1, e2, e3, e4, e5, e6]
  ring

/-- **THE REFLECTED FORM, IN CLOSED FORM.** No estimate anywhere: both energies are exact. -/
theorem reflectedForm_mir (a b : ℝ) :
    4 * GraphReflection.reflectedForm mirGraph (1 / 2) tau (cvec a b)
      = (19712 * a ^ 2 + 42368 * a * b + 24768 * b ^ 2) / 9635 := by
  have hm : (1 : ℝ) / 2 ≠ 0 := by norm_num
  have hpd : (massive mirGraph (1 / 2)).PosDef := massive_posDef mirGraph hm
  have hgreen : GraphLaplacian.green mirGraph (1 / 2) = (massive mirGraph (1 / 2))⁻¹ := rfl
  have heven : GraphReflection.energy mirGraph (1 / 2) (GraphReflection.sym tau (cvec a b))
      = GraphReflection.sym tau (cvec a b) ⬝ᵥ evenSol a b := by
    rw [energy_eq_dotProduct, hgreen]
    exact dotProduct_inv_of_mulVec hpd (mulVec_evenSol a b)
  have hodd : GraphReflection.energy mirGraph (1 / 2) (GraphReflection.anti tau (cvec a b))
      = GraphReflection.anti tau (cvec a b) ⬝ᵥ oddSol a b := by
    rw [energy_eq_dotProduct, hgreen]
    exact dotProduct_inv_of_mulVec hpd (mulVec_oddSol a b)
  rw [GraphReflection.reflectedForm_eq isRefl_tau, heven, hodd, sym_cvec, anti_cvec,
    dot_even, dot_odd]
  ring

/-- **REFLECTION POSITIVE AT `m = 1/2`.** The quadratic form above has leading coefficient `19712`
and discriminant `42368² − 4·19712·24768 = −157859840`. -/
theorem reflectionPositive_half :
    GraphReflection.ReflectionPositive mirGraph (1 / 2) tau Hm := by
  intro c hc
  obtain ⟨a, b, rfl⟩ : ∃ a b, c = cvec a b := ⟨c 0, c 1, cvec_of_supported hc⟩
  have key : (0 : ℝ) ≤ GraphReflection.reflectedForm mirGraph (1 / 2) tau (cvec a b) := by
    nlinarith [reflectedForm_mir a b, sq_nonneg (308 * a + 331 * b), sq_nonneg b]
  exact key

/-! ## 6. Not reflection positive at `m = 11`

By the estate's own large-mass estimate, unchanged. The coupling is `1`, the degree ceiling is
`4`, and the weighted mass of the refuting vector is `6 + 2m²`.
-/

theorem not_reflectionPositive_eleven :
    ¬ GraphReflection.ReflectionPositive mirGraph 11 tau Hm := by
  refine GreenLargeMass.not_reflectionPositive_of_crossForm_pos_general (u := wm) (Δ := 4)
    isMirrorHalf_Hm isRefl_tau (by norm_num) degree_le_four wm_supported ?_
  rw [crossForm_mir_pos]
  have hsum : ∑ p ∈ Hm, |wm p * ((mirGraph.degree p : ℝ) + (11 : ℝ) ^ 2)| = 248 := by
    rw [sum_Hm, degree_zero, degree_one]
    norm_num [wm]
  rw [hsum]
  norm_num

/-! ## 7. What the two masses say together -/

/-- **THE CONVERSE IS FALSE WITH A MIRROR.** `ReflectionConverse.reflectionPositive_iff_hcross`
holds on every fixed-point-free reflection; this says its hypothesis cannot be relaxed to
`IsMirrorHalf`, which is the hypothesis `reflectionPositive_mirror` carries for sufficiency. -/
theorem converse_fails_with_mirror :
    IsMirrorHalf tau Hm Mirm
      ∧ GraphReflection.IsRefl mirGraph tau
      ∧ GraphReflection.ReflectionPositive mirGraph (1 / 2) tau Hm
      ∧ ¬ ∀ w : Fin 7 → ℝ, crossForm mirGraph (1 / 2) tau Hm w ≤ 0 :=
  ⟨isMirrorHalf_Hm, isRefl_tau, reflectionPositive_half, hcross_fails _⟩

/-- **AND SO REFLECTION POSITIVITY REALLY DOES DEPEND ON THE MASS.**
`CrossFormMatrix.not_converse_of_mass_dependent` was written to take exactly this as input and
never received one; `GreenLargeMass.reflectionPositive_all_or_bounded` said such a graph must be
positive only below a threshold, and this one is. -/
theorem mass_dependent :
    GraphReflection.ReflectionPositive mirGraph (1 / 2) tau Hm
      ∧ ¬ GraphReflection.ReflectionPositive mirGraph 11 tau Hm :=
  ⟨reflectionPositive_half, not_reflectionPositive_eleven⟩

/-- **THE TWO RESULTS ARE EACH OTHER'S SHARPNESS.** No fixed point forbids mass-dependence; a
fixed layer permits it. Stated as one theorem so that neither can be quoted without the other. -/
theorem sharpness (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj] (θ : Fin 7 ≃ Fin 7)
    (H : Finset (Fin 7)) (hH : GraphHalfSpace.IsHalf θ H) (h : GraphReflection.IsRefl G θ)
    {m m' : ℝ} (hm : m ≠ 0) (hm' : m' ≠ 0) :
    (GraphReflection.ReflectionPositive G m θ H ↔ GraphReflection.ReflectionPositive G m' θ H)
      ∧ (GraphReflection.ReflectionPositive mirGraph (1 / 2) tau Hm
          ∧ ¬ GraphReflection.ReflectionPositive mirGraph 11 tau Hm) :=
  ⟨ReflectionConverse.reflectionPositive_mass_independent hH h hm hm', mass_dependent⟩

end MirrorConverseFails
