import AlgebraicCurvature
import Mathlib.Tactic.LinearCombination

/-!
# The three projections: Weyl ⊕ traceless-Ricci ⊕ scalar

The `UNLOCK_WATCHLIST` item for Lovelock in `n ≥ 3` records where that classification stops and
then says, in its own `REVISIT WHEN` and `LIKELY OUTCOME` lines:

> **The hand route is real and this estate could write the projections**; what it does not shorten
> is proving they exhaust, which is the classification again.
> LIKELY OUTCOME: the projections and their orthogonality, plus a statement of the classification
> that is still open … **Worth doing anyway, because the projections are the vocabulary `a₂` needs
> regardless.**

**This is that unit, and it delivers exactly what that line predicts and nothing more.** The
exhaustion half — that nothing outside the span of `ricci` and `scal • δ` is equivariant — is
untouched and stays open for the reason the item gives: no decomposition into irreducibles over
`ℝ` without compactness of `O(n)` and Haar averaging, neither of which Mathlib has.

## What is delivered

For every algebraic curvature tensor `R` on `Fin n` with `n ≥ 3`:

    R  =  weylPart R  +  ricciPart R  +  scalPart R          (`decomposition`)

with

* `scalPart R = (scal R / (n(n−1))) · knSquare δ` — carrying all of the scalar curvature;
* `ricciPart R = (1/(n−2)) · kn (tracefreeRicci R) δ` — carrying all of the traceless Ricci;
* `weylPart R` — **totally Ricci-flat**, `ricci (weylPart R) = 0` (`ricci_weylPart`), hence
  `scal (weylPart R) = 0`.

Each of the three is itself an algebraic curvature tensor, and the traces of the first two are
computed exactly (`ricci_scalPart`, `ricci_ricciPart`), so the decomposition is verified rather
than asserted.

Two pieces of general vocabulary arrive with it, both absent before and both wanted by anything
that manipulates these tensors:

* **`IsAlgCurv` is a linear condition** — `isAlgCurv_add`, `isAlgCurv_sub`, `isAlgCurv_smul`,
  `isAlgCurv_zero`. `AlgebraicCurvature` establishes `IsAlgCurv` of a named tensor **four** times
  (`isAlgCurv_constCurv`, `isAlgCurv_knSquare`, `isAlgCurv_projOffCurv`, `isAlgCurv_act` —
  `grep -n "theorem isAlgCurv_"`) and never once that the class is closed under sums or scalars;
  `isAlgCurv_add`, `IsAlgCurv.add`, `isAlgCurv_smul`, `IsAlgCurv.smul`, `isAlgCurv_sub` and
  `isAlgCurv_zero` all return zero there. **A draft of this sentence said "eight times",** which
  was the count of a grep that also matched every `: IsAlgCurv` appearing as a *hypothesis*;
  corrected before commit by running the narrower search.
* **The Kulkarni–Nomizu product**, `kn h k`, of which the file's existing `knSquare h` is the case
  `k = h` up to the factor two (`kn_self`). `ricci_kn` computes its Ricci trace in general and
  `ricci_kn_delta` specialises to `k = δ`, which is the identity the whole decomposition turns on:
  **`ricci (kn h δ) = (tr h) δ + (n−2) h`**, so at a traceless `h` the Kulkarni–Nomizu product with
  the metric is `(n−2)` times `h` itself.

## A hypothesis that was written down and turned out not to be needed

Both facts above were first stated for **symmetric** `h`, and both were then found not to use it.
`ricci_kn_delta` holds for an arbitrary `h`: the two contractions `∑ₐ h a c · δ b a` and
`∑ₐ δ a c · h b a` each collapse to `h b c` by the position of the Kronecker delta alone, and
neither needs `h a b = h b a`. Symmetry survives only where it is genuinely used —
`isAlgCurv_kn`, whose pair-symmetry and Bianchi clauses do need it.

**The larger version of the same observation, and it is the strongest statement in the file.**
`ricci_scalPart`, `ricci_ricciPart`, `ricci_weylPart` and `scal_weylPart` were all drafted with an
`IsAlgCurv R` hypothesis, and **not one of them uses it** — the linter said so and the proofs
confirm it. The trace identities hold for **any** four-index array of reals: they are consequences
of the linearity of the contraction and of the two Kronecker collapses, and nothing about
antisymmetry, pair symmetry or Bianchi enters. So *"the Weyl part of `R` is Ricci-flat"* is a fact
about arrays, not about curvature tensors. `IsAlgCurv R` is needed for exactly one family of
statements — `isAlgCurv_scalPart`, `isAlgCurv_ricciPart`, `isAlgCurv_weylPart`, that the three
pieces stay inside the symmetry class — and for `tracefreeRicci_symm`, which is where `ricci_symm`
is spent. **`n ≥ 3` is likewise spent in exactly one place**, `ricci_ricciPart`, and reaches
`ricci_weylPart` and `scal_weylPart` only by being passed along.

## Constants checked outside Lean before being written

`ERRATUM 108`'s habit: the three coefficients were verified by exact rational arithmetic on
generic algebraic curvature tensors at `n = 3, 4, 5` — generic meaning built by projecting a random
four-index array onto the symmetry class and then checking all four `IsAlgCurv` clauses hold —
before any of them was typed into a `def`. The check confirmed `ricci (weylPart R) = 0` exactly.
The compiler is the authority; the arithmetic was to stop a wrong constant reaching a statement.

## What this does NOT settle

* **Not Lovelock.** The classification is that the equivariant maps are *spanned* by `ricci` and
  `scal • δ`, and that is an **exhaustion** statement. Nothing here proves any map is in that span.
  The item stays open.
* **Not orthogonality as an inner-product statement.** The item's `LIKELY OUTCOME` says
  "the projections and their orthogonality". What is proved here is the **algebraic** form of the
  splitting: the three pieces sum to `R`, and the Ricci trace separates them — `weylPart` has trace
  zero, `ricciPart` has trace the traceless Ricci, `scalPart` has trace the pure-trace part. That
  the three summands are mutually orthogonal for the natural inner product on four-index arrays is
  **not proved here**, and this estate has no inner product on that space to state it against.
  Named rather than quietly dropped.
* **Not `a₂`, and not a manifold.** Everything below is a four-index array of reals, as in
  `AlgebraicCurvature` throughout. `WALLS` W5 fails at the differential geometry and this moves it
  no closer.
* **Not equivariance of the projections.** `AlgebraicCurvature` §12 proves `ricci` and `scal` are
  equivariant, and `act_constCurv` proves the generator is fixed; making the three projections
  equivariant needs one more lemma, `act Q (kn h k) = kn (act2 Q h) (act2 Q k)`, which is the
  factorisation of a quadruple sum into two double sums. **That is the remaining leg and it is
  written down here rather than left implicit** (`PROOF_STRATEGY` §3).

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockProjections

open AlgebraicCurvature Finset

variable {n : ℕ}

/-! ## 0. `IsAlgCurv` is a linear condition

Every clause of the structure is an equation linear in `R`, so the class is a subspace. The file
that defines `IsAlgCurv` establishes it for eight individual tensors and never states this.
-/

theorem isAlgCurv_zero : IsAlgCurv (fun _ _ _ _ => (0 : ℝ) : Fin n → Fin n → Fin n → Fin n → ℝ)
    where
  antisymm_left _ _ _ _ := by simp
  antisymm_right _ _ _ _ := by simp
  pair_symm _ _ _ _ := rfl
  bianchi _ _ _ _ := by simp

theorem isAlgCurv_add {R S : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hR : IsAlgCurv R) (hS : IsAlgCurv S) :
    IsAlgCurv (fun a b c d => R a b c d + S a b c d) where
  antisymm_left a b c d := by rw [hR.antisymm_left a b c d, hS.antisymm_left a b c d]; ring
  antisymm_right a b c d := by rw [hR.antisymm_right a b c d, hS.antisymm_right a b c d]; ring
  pair_symm a b c d := by rw [hR.pair_symm a b c d, hS.pair_symm a b c d]
  bianchi a b c d := by
    have h1 := hR.bianchi a b c d
    have h2 := hS.bianchi a b c d
    linarith

theorem isAlgCurv_smul (lam : ℝ) {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R) :
    IsAlgCurv (fun a b c d => lam * R a b c d) where
  antisymm_left a b c d := by rw [hR.antisymm_left a b c d]; ring
  antisymm_right a b c d := by rw [hR.antisymm_right a b c d]; ring
  pair_symm a b c d := by rw [hR.pair_symm a b c d]
  bianchi a b c d := by
    have h := hR.bianchi a b c d
    linear_combination lam * h

theorem isAlgCurv_sub {R S : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hR : IsAlgCurv R) (hS : IsAlgCurv S) :
    IsAlgCurv (fun a b c d => R a b c d - S a b c d) := by
  have h := isAlgCurv_add hR (isAlgCurv_smul (-1) hS)
  simpa [sub_eq_add_neg] using h

/-! ## 1. The Kulkarni–Nomizu product

`AlgebraicCurvature.knSquare h` is the case `k = h`, halved: `kn h h = 2 • knSquare h`
(`kn_self`). The general product is what the decomposition needs, because the Ricci piece is built
from the traceless Ricci **against the metric**, not against itself. Symmetry of the two arguments
is required only by `isAlgCurv_kn`; the trace identity below does without it.
-/

/-- **THE KULKARNI–NOMIZU PRODUCT**, `h ⊙ k`. -/
def kn (h k : Fin n → Fin n → ℝ) (a b c d : Fin n) : ℝ :=
  h a d * k b c + k a d * h b c - h a c * k b d - k a c * h b d

theorem kn_comm (h k : Fin n → Fin n → ℝ) (a b c d : Fin n) :
    kn h k a b c d = kn k h a b c d := by simp only [kn]; ring

/-- The existing `knSquare` is this at `k = h`, halved. -/
theorem kn_self (h : Fin n → Fin n → ℝ) (a b c d : Fin n) :
    kn h h a b c d = 2 * knSquare h a b c d := by simp only [kn, knSquare]; ring

/-- **THE PRODUCT OF TWO SYMMETRIC FORMS IS AN ALGEBRAIC CURVATURE TENSOR.** -/
theorem isAlgCurv_kn {h k : Fin n → Fin n → ℝ}
    (hh : ∀ a b, h a b = h b a) (hk : ∀ a b, k a b = k b a) : IsAlgCurv (kn h k) where
  antisymm_left a b c d := by simp only [kn]; ring
  antisymm_right a b c d := by simp only [kn]; ring
  pair_symm a b c d := by
    simp only [kn]
    rw [hh c b, hh d a, hh c a, hh d b, hk c b, hk d a, hk c a, hk d b]; ring
  bianchi a b c d := by
    simp only [kn]
    rw [hh c a, hh b a, hh c b, hk c a, hk b a, hk c b]; ring

/-- **THE RICCI TRACE OF A KULKARNI–NOMIZU PRODUCT.** -/
theorem ricci_kn (h k : Fin n → Fin n → ℝ) (b c : Fin n) :
    ricci (kn h k) b c
      = (∑ a, h a a) * k b c + (∑ a, k a a) * h b c
          - (∑ a, h a c * k b a) - ∑ a, k a c * h b a := by
  simp only [ricci, kn]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul]

/-- **THE IDENTITY THE DECOMPOSITION TURNS ON.** Against the metric, the Kulkarni–Nomizu product
returns the trace of `h` on the metric plus `(n − 2)` copies of `h` itself. At a **traceless** `h`
the first term vanishes and the product is `(n − 2) · h`, which is the reason `n ≥ 3` is needed at
all. **No symmetry hypothesis**: each contraction collapses by the position of the Kronecker delta,
and a first draft carried `∀ a b, h a b = h b a` that the proof never touched. -/
theorem ricci_kn_delta (h : Fin n → Fin n → ℝ) (b c : Fin n) :
    ricci (kn h delta) b c = (∑ a, h a a) * delta b c + ((n : ℝ) - 2) * h b c := by
  rw [ricci_kn]
  have e1 : ∑ a : Fin n, (delta a a : ℝ) = (n : ℝ) := by simp [delta]
  have e2 : ∑ a, h a c * delta b a = h b c := by
    have hstep : ∀ a : Fin n, h a c * delta b a = delta a b * h a c := by
      intro a; rw [delta_symm b a]; ring
    simp only [hstep]
    exact sum_delta_left b (fun a => h a c)
  have e3 : ∑ a, (delta a c : ℝ) * h b a = h b c := sum_delta_left c (fun a => h b a)
  linear_combination (h b c) * e1 - e2 - e3

/-! ## 2. The traceless Ricci, and the three pieces -/

/-- **THE TRACE-FREE PART OF THE RICCI TENSOR.** -/
noncomputable def tracefreeRicci (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) : ℝ :=
  ricci R b c - (scal R / (n : ℝ)) * delta b c

theorem tracefreeRicci_symm {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R)
    (b c : Fin n) : tracefreeRicci R b c = tracefreeRicci R c b := by
  simp only [tracefreeRicci]
  rw [ricci_symm hR b c, delta_symm b c]

/-- **AND IT IS TRACELESS**, which needs `n ≠ 0` and nothing else. -/
theorem trace_tracefreeRicci (hn : (n : ℝ) ≠ 0) (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ b, tracefreeRicci R b b = 0 := by
  have e1 : ∑ b : Fin n, (delta b b : ℝ) = (n : ℝ) := by simp [delta]
  have e2 : ∑ b, ricci R b b = scal R := rfl
  simp only [tracefreeRicci, Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2]
  field_simp
  ring

/-- **THE SCALAR PIECE.** -/
noncomputable def scalPart (R : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) : ℝ :=
  (scal R / ((n : ℝ) * ((n : ℝ) - 1))) * knSquare delta a b c d

/-- **THE TRACELESS-RICCI PIECE.** -/
noncomputable def ricciPart (R : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) : ℝ :=
  (1 / ((n : ℝ) - 2)) * kn (tracefreeRicci R) delta a b c d

/-- **THE WEYL PIECE**, defined as what is left. Its content is `ricci_weylPart` below. -/
noncomputable def weylPart (R : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) : ℝ :=
  R a b c d - ricciPart R a b c d - scalPart R a b c d

/-- **THE DECOMPOSITION**, which is a rearrangement and carries no hypothesis. -/
theorem decomposition (R : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    R a b c d = weylPart R a b c d + ricciPart R a b c d + scalPart R a b c d := by
  simp only [weylPart]; ring

/-! ## 3. The traces, computed -/

/-- **THE SCALAR PIECE CARRIES THE PURE-TRACE PART OF THE RICCI TENSOR.** -/
theorem ricci_scalPart (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) :
    ricci (scalPart R) b c = (scal R / (n : ℝ)) * delta b c := by
  have hlin : ricci (scalPart R) b c
      = (scal R / ((n : ℝ) * ((n : ℝ) - 1))) * ricci (constCurv n) b c := by
    simp only [ricci, scalPart, knSquare_delta, Finset.mul_sum]
  rw [hlin, ricci_constCurv]
  field_simp

/-- **THE RICCI PIECE CARRIES THE TRACELESS PART**, exactly, and this is the one statement in the
file that spends `n ≥ 3`. -/
theorem ricci_ricciPart (hn0 : (n : ℝ) ≠ 0) (hn2 : (n : ℝ) - 2 ≠ 0)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) :
    ricci (ricciPart R) b c = tracefreeRicci R b c := by
  have hlin : ricci (ricciPart R) b c
      = (1 / ((n : ℝ) - 2)) * ricci (kn (tracefreeRicci R) delta) b c := by
    simp only [ricci, ricciPart, Finset.mul_sum]
  rw [hlin, ricci_kn_delta (tracefreeRicci R), trace_tracefreeRicci hn0 R]
  field_simp
  ring

/-- **THE WEYL PIECE IS RICCI-FLAT.** This is the theorem the decomposition exists for. -/
theorem ricci_weylPart (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0) (hn2 : (n : ℝ) - 2 ≠ 0)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) :
    ricci (weylPart R) b c = 0 := by
  have hlin : ricci (weylPart R) b c
      = ricci R b c - ricci (ricciPart R) b c - ricci (scalPart R) b c := by
    simp only [ricci, weylPart, Finset.sum_sub_distrib]
  rw [hlin, ricci_ricciPart hn0 hn2 R, ricci_scalPart hn0 hn1, tracefreeRicci]
  ring

/-- **HENCE ITS SCALAR CURVATURE VANISHES TOO.** -/
theorem scal_weylPart (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0) (hn2 : (n : ℝ) - 2 ≠ 0)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    scal (weylPart R) = 0 := by
  simp only [scal]
  rw [Finset.sum_congr rfl fun b _ => ricci_weylPart hn0 hn1 hn2 R b b]
  simp

/-! ## 4. Each piece is itself an algebraic curvature tensor -/

theorem isAlgCurv_scalPart (R : Fin n → Fin n → Fin n → Fin n → ℝ) : IsAlgCurv (scalPart R) :=
  isAlgCurv_smul _ (isAlgCurv_knSquare delta_symm)

theorem isAlgCurv_ricciPart {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R) :
    IsAlgCurv (ricciPart R) :=
  isAlgCurv_smul _ (isAlgCurv_kn (tracefreeRicci_symm hR) delta_symm)

theorem isAlgCurv_weylPart {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R) :
    IsAlgCurv (weylPart R) :=
  isAlgCurv_sub (isAlgCurv_sub hR (isAlgCurv_ricciPart hR)) (isAlgCurv_scalPart R)

/-! ## 5. The two degenerate dimensions, stated so that the hypotheses are not mistaken for
bookkeeping

`n = 2` is not an oversight: there the traceless Ricci is identically zero, so the middle piece has
nothing to carry and `1/(n−2)` is meaningless. `AlgebraicCurvature.ricci_eq_half_scal_two` is the
reason, and it is already proved there.
-/

/-- **AT `n = 2` THE MIDDLE PIECE IS EMPTY**, so the missing `n ≥ 3` is a fact about the
mathematics and not a limitation of the argument: there is nothing for `ricciPart` to carry. -/
theorem tracefreeRicci_eq_zero_two {R : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ} (hR : IsAlgCurv R)
    (b c : Fin 2) : tracefreeRicci R b c = 0 := by
  have h := ricci_eq_half_scal_two hR b c
  simp only [tracefreeRicci]
  rw [h]
  norm_num
  ring

/-! ## 6. The remaining leg, named

`PROOF_STRATEGY` §3: the chain may be left only with the next step written down. The step is one
lemma:

    act Q (kn h k) = kn (act2 Q h) (act2 Q k)      for `IsOrth Q`

which is the statement that the quadruple sum defining `act` factorises into the two double sums
defining `act2` — true because each of the four terms of `kn` pairs the indices `(a,d)` with
`(b,c)`. With it, `AlgebraicCurvature.ricci_act`, `scal_act` and `act_constCurv` (all proved
there) make all three projections `O(n)`-equivariant in one line each, which is the form the
classification would consume. **It is not proved here.**
-/

end LovelockProjections
