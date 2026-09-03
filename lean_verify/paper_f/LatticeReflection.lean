/-
  LatticeReflection.lean — the reflection on the box, the invariance of the
  Green function under it, and W1's failing step as a named object.

  WHY. `LatticeField` established, by attempting it, that the OS2 layer needs
  a reflection on `Site n` and that **the estate has none**. It also said —
  deliberately, so as not to over-correct — that nothing suggested such a map
  would be hard to write. **That sentence was a claim, not a hedge**, and
  this file discharges it: the map is four lines, the automorphism property
  is `Fin` arithmetic, and the invariance of the covariance follows from two
  Mathlib lemmas.

  WHAT THIS FILE PROVES:
  1. **`refl`** — reflection of the box in its first coordinate, as an
     involutive `Equiv`.
  2. **`adj_refl`** — it is a GRAPH AUTOMORPHISM: adjacency is preserved.
     This is the only step with arithmetic in it, and the arithmetic is the
     interesting part — a step UP in the first coordinate becomes a step
     DOWN, so the two disjuncts of `adj` exchange.
  3. **`lattLap_refl`, `massive_refl`, `green_refl`** — hence the Laplacian,
     the massive operator and **the Green function are all
     reflection-invariant**: `green n m (refl p) (refl q) = green n m p q`.
     The first structural property of this covariance.
  4. **`ReflectionPositive`** — W1's failing step as a named `def`, exactly
     as `IsingBoundaryField.MagnetisationBound` names W3's. The statement
     one would try to prove now exists as an object in the estate rather
     than as a sentence about one.

  WHAT THIS DOES NOT DO, and it is the whole of W1.
  **It does not prove `ReflectionPositive`.** Naming a gap is not closing
  it. And the gap is not narrow: **invariance is not positivity.** The
  OU-product covariance is reflection-invariant too, and proving ITS
  positivity took the Schur product theorem and four files
  (`SchurProduct` → `OS2ProductField` → `OS2ExpKernel` → `OS2Exponential`).
  W1's own diagnosis — that the factorisation carrying that programme is
  structurally unavailable here — is untouched by anything in this file.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import LatticeField

namespace LatticeReflection

open IsingFiniteVolume IsingContourSeparation LatticeLaplacian Matrix

variable {n : ℕ}

/-! ## 1. The reflection -/

/-- **Reflection of the box in its first coordinate.** `Fin.rev` does the
    work; the point of bundling it as an `Equiv` is that
    `Matrix.inv_submatrix_equiv` in §3 needs one. -/
def refl (n : ℕ) : Site n ≃ Site n where
  toFun p := (p.1.rev, p.2)
  invFun p := (p.1.rev, p.2)
  left_inv p := by simp
  right_inv p := by simp

@[simp] theorem refl_apply (p : Site n) : refl n p = (p.1.rev, p.2) := rfl

theorem refl_involutive (n : ℕ) : Function.Involutive (refl n) := by
  intro p
  simp

/-! ## 2. It is a graph automorphism

The only arithmetic in the file, and the step the probe named as the risk.
Reflecting the first coordinate turns a step UP into a step DOWN, so the two
halves of the first disjunct of `adj` exchange; the second disjunct is
untouched because the second coordinate is fixed.
-/

theorem adj_refl (p q : Site n) : adj (refl n p) (refl n q) ↔ adj p q := by
  have hp := p.1.isLt
  have hq := q.1.isLt
  unfold adj
  simp only [refl_apply, Fin.val_rev]
  constructor
  · rintro (⟨he, hstep⟩ | ⟨he, hstep⟩)
    · exact Or.inl ⟨by simpa using congrArg Fin.rev he, hstep⟩
    · exact Or.inr ⟨he, by omega⟩
  · rintro (⟨he, hstep⟩ | ⟨he, hstep⟩)
    · exact Or.inl ⟨congrArg Fin.rev he, hstep⟩
    · exact Or.inr ⟨he, by omega⟩

theorem latticeGraph_adj_refl (p q : Site n) :
    (latticeGraph n).Adj (refl n p) (refl n q) ↔ (latticeGraph n).Adj p q :=
  adj_refl p q

theorem degree_refl (p : Site n) :
    (latticeGraph n).degree (refl n p) = (latticeGraph n).degree p := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  have himg : (latticeGraph n).neighborFinset (refl n p)
      = ((latticeGraph n).neighborFinset p).image (refl n) := by
    ext q
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image]
    constructor
    · intro hq
      exact ⟨refl n q,
        (latticeGraph_adj_refl p (refl n q)).mp (by rw [refl_involutive n q]; exact hq),
        refl_involutive n q⟩
    · rintro ⟨r, hr, rfl⟩
      exact (latticeGraph_adj_refl p r).mpr hr
  rw [himg, Finset.card_image_of_injective _ (refl n).injective]

/-! ## 3. The covariance is reflection-invariant -/

theorem lattLap_refl (p q : Site n) :
    lattLap n (refl n p) (refl n q) = lattLap n p q := by
  classical
  have hinj : (refl n p = refl n q) ↔ (p = q) :=
    ⟨fun h => (refl n).injective h, fun h => by rw [h]⟩
  simp only [lattLap, SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix,
    Matrix.diagonal_apply, SimpleGraph.adjMatrix_apply, degree_refl, hinj,
    latticeGraph_adj_refl]

theorem lattLap_submatrix_refl (n : ℕ) :
    (lattLap n).submatrix (refl n) (refl n) = lattLap n := by
  ext p q
  exact lattLap_refl p q

theorem massive_submatrix_refl (n : ℕ) (m : ℝ) :
    (massive n m).submatrix (refl n) (refl n) = massive n m := by
  classical
  ext p q
  have hinj : (refl n p = refl n q) ↔ (p = q) :=
    ⟨fun h => (refl n).injective h, fun h => by rw [h]⟩
  simp only [massive, Matrix.submatrix_apply, Matrix.add_apply, Matrix.diagonal_apply,
    lattLap_refl p q, hinj]

/-- **THE LATTICE GREEN FUNCTION IS REFLECTION-INVARIANT.** The first
    structural property of this covariance. Carried from §2 by
    `Matrix.inv_submatrix_equiv`. -/
theorem green_refl (n : ℕ) (m : ℝ) (p q : Site n) :
    green n m (refl n p) (refl n q) = green n m p q := by
  have h : (green n m).submatrix (refl n) (refl n) = green n m := by
    rw [green, ← Matrix.inv_submatrix_equiv, massive_submatrix_refl]
  exact congrFun (congrFun h p) q

/-! ## 4. W1's failing step, as an object

`IsingBoundaryField.MagnetisationBound` names W3's gap as a `def` so that its
absence is a thing in the estate rather than a sentence in a document. This
does the same for W1.
-/

/-- **REFLECTION POSITIVITY of the lattice Green function** — W1's failing
    step, written down. For every family of coefficients supported on one
    side of the reflection, the reflected quadratic form is non-negative.

    **THIS IS A DEFINITION, NOT A THEOREM.** Nothing in this estate proves
    it, and `WALLS.md` W1 explains why: the factorisation that carried the
    OU-product programme is structurally unavailable for this covariance.

    **⚠ *"NOTHING IN THIS ESTATE PROVES IT"* HAS BEEN FALSE SINCE 2026-08-09
    AND THE PARAGRAPH IS KEPT AS WRITTEN** (`ERRATUM 94`, **`ERRATUM 430`**).
    `LatticeReflectionPositive.reflectionPositive_lattice` concludes exactly
    this predicate, for a box of even side, nonzero mass and any region inside
    the first-coordinate half; `_compl` is the other side, and `WALLS.md`'s W1
    row says so in its first sentence. **The correction was written the same
    day — in the proving file's own docstring, which QUOTES this sentence
    verbatim and then says *"Something in this estate now proves it"* — and it
    was never brought back here**, to the definition the wall is named for and
    the place a reader meets first. -/
def ReflectionPositive (n : ℕ) (m : ℝ) (half : Finset (Site n)) : Prop :=
  ∀ c : Site n → ℝ, (∀ p, p ∉ half → c p = 0) →
    0 ≤ ∑ p, ∑ q, c p * c q * green n m (refl n p) q

/-- At `half = ∅` the support hypothesis forces `c = 0`, so the statement
    holds and holds for a trivial reason. Recorded as a WARNING, not a
    reassurance: it says the definition has a degenerate corner, so any
    future proof must be checked to do its work somewhere else. -/
theorem reflectionPositive_empty (n : ℕ) (m : ℝ) :
    ReflectionPositive n m ∅ := by
  intro c hc
  have : ∀ p : Site n, c p = 0 := fun p => hc p (by simp)
  simp [this]

/-! ## 5. The smallest instance, and what it identifies

`reflectionPositive_empty` is free. The next case up is a singleton half,
and it is not free: it says exactly one thing, and that thing is the bottom
rung of the ladder recorded in `UNLOCK_WATCHLIST.md`.
-/

/-- **THE SINGLETON CRITERION.** Reflection positivity on a one-site half is
    EXACTLY non-negativity of one entry of the Green function — the entry
    joining a site to its mirror image.

    This is worth stating because it identifies the bottom rung: any attack
    on the general statement has to prove the propagator non-negative first,
    and that is the random-walk representation `WALLS.md` W1 names as its
    second route. -/
theorem reflectionPositive_singleton_iff (n : ℕ) (m : ℝ) (p : Site n) :
    ReflectionPositive n m {p} ↔ 0 ≤ green n m (refl n p) p := by
  classical
  constructor
  · intro h
    have := h (fun q => if q = p then 1 else 0) (by
      intro q hq
      simp only [Finset.mem_singleton] at hq
      simp [hq])
    simpa using this
  · intro hg c hc
    have hzero : ∀ q, q ≠ p → c q = 0 := fun q hq => hc q (by simpa using hq)
    rw [Finset.sum_eq_single p (fun q _ hq => by simp [hzero q hq])
      (fun h => absurd (Finset.mem_univ p) h)]
    rw [Finset.sum_eq_single p (fun q _ hq => by simp [hzero q hq])
      (fun h => absurd (Finset.mem_univ p) h)]
    have : c p * c p = (c p) ^ 2 := by ring
    rw [this]
    exact mul_nonneg (sq_nonneg _) hg

/-- **A NON-VACUOUS INSTANCE.** At a site the reflection FIXES, the entry in
    question is a diagonal one, and `green_diag_pos` makes it positive. So
    reflection positivity genuinely holds somewhere — unlike
    `reflectionPositive_empty`, this one is not true for a degenerate
    reason. Fixed sites exist exactly when `n` is odd (`Fin.rev i = i`
    forces `2i = n − 1`). -/
theorem reflectionPositive_singleton_of_fixed (n : ℕ) {m : ℝ} (hm : m ≠ 0)
    {p : Site n} (hfix : refl n p = p) :
    ReflectionPositive n m {p} := by
  rw [reflectionPositive_singleton_iff, hfix]
  exact le_of_lt (LatticeField.green_diag_pos n hm p)

/-- Fixed sites exist exactly when `n` is odd, and here is one: the middle
    row. Proved rather than remarked, because without it
    `reflectionPositive_singleton_of_fixed` is a statement about a possibly
    empty hypothesis. -/
theorem exists_fixed_of_odd {k : ℕ} : ∃ p : Site (2 * k + 1), refl (2 * k + 1) p = p := by
  refine ⟨(⟨k, by omega⟩, ⟨k, by omega⟩), ?_⟩
  simp only [refl_apply, Prod.mk.injEq, and_true]
  exact Fin.ext (by simp [Fin.val_rev]; omega)

/-- **SO REFLECTION POSITIVITY GENUINELY HOLDS SOMEWHERE.** On an odd box
    there is a half — a single fixed site — for which the property is a
    theorem. That is what makes `ReflectionPositive` a statement with
    content rather than one whose only known instances are degenerate. -/
theorem exists_reflectionPositive_singleton {k : ℕ} {m : ℝ} (hm : m ≠ 0) :
    ∃ p : Site (2 * k + 1), ReflectionPositive (2 * k + 1) m {p} := by
  obtain ⟨p, hp⟩ := exists_fixed_of_odd (k := k)
  exact ⟨p, reflectionPositive_singleton_of_fixed _ hm hp⟩

/-! ## 6. Review round 73 — the ways this could be hollow

**"The reflection could be the wrong map."** `adj_refl` is the check that
matters and it is not automatic: reflecting the first coordinate turns
`p.1 + 1 = q.1` into `q.1 + 1 = p.1`, so the disjuncts exchange, and a map
that failed to be an automorphism would break there. `degree_refl` is a
consequence and is used by §3.

**"§3 could be invariance of the wrong object."** `green_refl` is proved
from `massive_submatrix_refl` through `Matrix.inv_submatrix_equiv`, so it
inherits whatever `massive` is; and `massive` was pinned in
`LatticeLaplacian` by `trace_lattLap` against `IsingContourEnergy.bondCount`.
The chain of identifications is unbroken back to the 2×2 anchor.

**"§4 could be presented as progress on W1."** It is the opposite of that
and the header says so twice. A named `def` is an absence made visible, not
an absence removed — the same move `IsingBoundaryField.MagnetisationBound`
made for W3, and that gap is still open after seven units of work on it.
**And the specific thing to not conclude: INVARIANCE IS NOT POSITIVITY.**
The OU-product covariance is reflection-invariant too, and proving its
positivity took `SchurProduct` → `OS2ProductField` → `OS2ExpKernel` →
`OS2Exponential`. What W1 says is missing is not a symmetry, it is an
estimate.

**"The only instances could be degenerate."** That was true of the first
draft, whose only theorem about `ReflectionPositive` was that it holds on
the empty half. §5 fixes it: `reflectionPositive_singleton_iff` says the
one-site case is EXACTLY non-negativity of one Green-function entry — which
identifies the bottom rung of the ladder in `UNLOCK_WATCHLIST.md`, since any
attack on the general statement must prove the propagator non-negative — and
`exists_reflectionPositive_singleton` produces a genuine instance on every
odd box, via a fixed site that is exhibited rather than asserted.

**"`ReflectionPositive` could be stated so weakly that it is trivial."** The
first draft of it WAS defective, and in the way this project keeps finding:
it carried a support hypothesis `∀ p ∉ half, c p = 0` while summing `∑ p ∈
half, ∑ q ∈ half`, **so the hypothesis constrained nothing at all** — the
sums never looked at `c` outside `half`. A hypothesis that reads as a
restriction and is not one is worse than no hypothesis, because a later
reader budgets for it. Corrected to sum over ALL sites, which is what makes
the support condition do the work, and which is the standard form.

Two further shape checks on it. The reflection is applied on ONE side only —
`green (refl p) q` — which is the form OS2 uses; applying it to both sides
would give something `green_refl` alone settles, i.e. the easy statement
rather than the wanted one. And `reflectionPositive_empty` records that the
empty half is free: a warning that the definition has a degenerate corner,
so any future proof must be checked to do its work elsewhere.
-/

end LatticeReflection
