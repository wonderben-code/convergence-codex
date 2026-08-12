import CrossBlockStructure

/-!
# The `A²` class was never a class of regular graphs — it is a class that FORCES regularity

`CrossPosSemidef.reflectionPositive_iff_hcross_of_adjSq` is the wall's converse on
`GreenExpansion` §9's class, and it carries five hypotheses. One of them is not a hypothesis.

    hd : G.IsRegularOfDegree d
    hA : A * A = α • 1 + β • A + γ • allOnes V

**`hA` implies `hd`.** Read the identity at a diagonal entry. The left side is
`SimpleGraph.adjMatrix_mul_self_apply_self`, the number of walks of length two from `p` to itself,
which is `G.degree p`. The right side is `α · 1 + β · 0 + γ · 1`, because a simple graph has no
loops and the all-ones matrix is one everywhere. So

    G.degree p = α + γ    for EVERY vertex p,

with no reference to `p` on the right. The degree is constant, and it is not merely constant — **it
is determined by the coefficients**, which is the sharper statement and the one that lets `hK` be
restated without mentioning `d` at all.

## What this is, and what it is not

**It is not a deepening.** The theorem below applies to exactly the graphs the original applies to,
because the hypothesis removed was never excluding anything. Saying that plainly matters more than
the theorem: a redundant hypothesis makes a class look narrower than it is, and this one made the
estate's central converse look like a statement about regular graphs satisfying a matrix identity
when it is a statement about graphs satisfying a matrix identity, full stop.

**What it does buy**, and these are small and real: the caller supplies one fewer input; `hK`'s `d`
is revealed as over-determined and is replaced by `α + γ`, so the threshold is a condition on the
coefficients and the mass alone; and the class is now known to be a class of regular graphs rather
than defined as one — which is the standard fact about the adjacency algebra of a strongly regular
graph, here proved from the identity rather than cited.

## Checked against two graphs the estate already measured

`IndefiniteCoupling.bipGraph` has `α = 0, γ = 2` (`GreenExpansion.bipGraph_adjSq`), so the formula
predicts degree `2`, and `GreenExpansion.bipGraph_two_regular` proves degree `2` by an independent
route. `IndefiniteCoupling.crossGraph` is a perfect matching with `A² = 1`, so `α = 1, γ = 0`, and
the formula predicts degree `1` against `IndefiniteCoupling.degree_eq_one`. **Two predictions, two
matches, neither of them used in the proof.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace AdjSqForcesRegular

open Matrix GraphReflection GraphMirrorReflection GreenExpansion

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {α β γ : ℝ}

/-! ## 1. The diagonal of the identity is the degree -/

/-- **THE WHOLE CONTENT, IN ONE LINE OF ALGEBRA.** At a diagonal entry the `A²` identity says the
degree equals `α + γ`, because `A` has no diagonal and the all-ones matrix is all ones. -/
theorem degree_eq_of_adjSq
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V) (p : V) :
    (G.degree p : ℝ) = α + γ := by
  have h := congrFun (congrFun hA p) p
  rw [SimpleGraph.adjMatrix_mul_self_apply_self] at h
  simpa [allOnes, Matrix.one_apply_eq] using h

/-- Hence any two degrees agree. -/
theorem degree_eq_degree_of_adjSq
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V) (p q : V) :
    G.degree p = G.degree q := by
  have : (G.degree p : ℝ) = (G.degree q : ℝ) := by
    rw [degree_eq_of_adjSq hA p, degree_eq_of_adjSq hA q]
  exact_mod_cast this

/-- **THE HYPOTHESIS `hd` IS IMPLIED BY `hA`.** On a nonempty vertex type the common degree is the
degree of any vertex; the empty case is `exists_isRegularOfDegree_of_adjSq` below. -/
theorem isRegularOfDegree_of_adjSq [Nonempty V]
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V) :
    G.IsRegularOfDegree (G.degree (Classical.arbitrary V)) :=
  fun v => degree_eq_degree_of_adjSq hA v _

/-- The same with no nonemptiness assumption: an empty graph is regular of every degree, so `0`
does. -/
theorem exists_isRegularOfDegree_of_adjSq
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V) :
    ∃ d : ℕ, G.IsRegularOfDegree d := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · exact ⟨0, fun v => (hV.false v).elim⟩
  · exact ⟨_, isRegularOfDegree_of_adjSq hA⟩

/-- **AND THE DEGREE IS NOT MERELY CONSTANT, IT IS DETERMINED BY THE COEFFICIENTS**, which is what
lets the threshold below drop its `d`. -/
theorem cast_degree_eq_of_adjSq [Nonempty V]
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V) :
    ((G.degree (Classical.arbitrary V) : ℕ) : ℝ) = α + γ :=
  degree_eq_of_adjSq hA _

/-! ## 2. The wall's converse, with the hypothesis dropped and the threshold in the coefficients -/

/-- **THE ESTATE'S CENTRAL CONVERSE WITHOUT ITS REGULARITY HYPOTHESIS**, and with the threshold
stated in the coefficients rather than in a degree the coefficients already fix. Compare
`CrossPosSemidef.reflectionPositive_iff_hcross_of_adjSq`, which is this with `hd` supplied by the
caller and `hK` written in `d`. **The two apply to the same graphs** — see the header. -/
theorem reflectionPositive_iff_hcross_of_adjSq' [Nonempty V] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}
    (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0) (hγ : 0 ≤ γ)
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V)
    (hK : 0 < (α + γ + m ^ 2) ^ 2 - α - β * (α + γ + m ^ 2)) :
    GraphReflection.ReflectionPositive G m θ H ↔ ∀ w : V → ℝ, crossForm G m θ H w ≤ 0 := by
  have hdeg := cast_degree_eq_of_adjSq hA (α := α) (β := β) (γ := γ)
  refine CrossPosSemidef.reflectionPositive_iff_hcross_of_adjSq
    (isRegularOfDegree_of_adjSq hA) hM h hm hγ hA ?_
  rw [hdeg]
  exact hK

/-! ## 3. Two predictions, checked against degrees the estate proved by other routes -/

/-- `bipGraph` has `α = 0` and `γ = 2`, so the formula says degree `2`. -/
theorem bipGraph_degree_from_coeffs (p : Fin 4) :
    (IndefiniteCoupling.bipGraph.degree p : ℝ) = 0 + 2 :=
  degree_eq_of_adjSq bipGraph_adjSq p

/-- And `GreenExpansion.bipGraph_two_regular` says degree `2`, by counting neighbours. **The
formula and the count agree**, and neither is used to prove the other. -/
theorem bipGraph_prediction_matches (p : Fin 4) :
    (IndefiniteCoupling.bipGraph.degree p : ℝ) = 0 + 2
      ∧ IndefiniteCoupling.bipGraph.degree p = 2 :=
  ⟨bipGraph_degree_from_coeffs p, bipGraph_two_regular p⟩

/-- `crossGraph` is a perfect matching, so `A² = 1` — that is `α = 1`, `β = 0`, `γ = 0`. -/
theorem crossGraph_adjSq :
    IndefiniteCoupling.crossGraph.adjMatrix ℝ * IndefiniteCoupling.crossGraph.adjMatrix ℝ
      = (1 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)
        + (0 : ℝ) • IndefiniteCoupling.crossGraph.adjMatrix ℝ + (0 : ℝ) • allOnes (Fin 4) := by
  rw [adjMatrix_sq_of_one_regular crossGraph_one_regular]
  simp

/-- So the formula predicts degree `1`, and `IndefiniteCoupling.degree_eq_one` proves degree `1`.
**Second prediction, second match.** -/
theorem crossGraph_prediction_matches (p : Fin 4) :
    (IndefiniteCoupling.crossGraph.degree p : ℝ) = 1 + 0
      ∧ IndefiniteCoupling.crossGraph.degree p = 1 :=
  ⟨degree_eq_of_adjSq crossGraph_adjSq p, IndefiniteCoupling.degree_eq_one p⟩

/-! ## 4. And the DECIDABLE form sheds it too — which buys a verdict at a FIXED mass

`PROOF_STRATEGY` §3: §§1–3 landed, so the next rung before the queue.
`CrossBlockStructure.reflectionPositive_iff_isCrossBlock` carries the same two hypotheses and the
same redundancy, and it is the version whose right-hand side is **decidable**. Dropping `hd` there
gives a decision procedure with one fewer input — and, unlike `GreenLargeMass` §12, **it decides
reflection positivity at a FIXED mass**, because this equivalence holds at every mass rather than
only asymptotically. The price is that it applies only on the `A²` class, where §12 applies to every
finite graph. Two different trades, and the file states both rather than presenting the newer one as
strictly better.

`bipGraph` is the instance. Its coefficients are `α = 0, β = −2, γ = 2`, so the threshold is
`0 < (2 + m²)(4 + m²)`, which holds at every mass — the condition is discharged once, by
`positivity`, rather than per mass. What is left is `IsCrossBlock`, and that is `decide`.
-/

section DecidableFixedMass

open CrossBlockStructure

variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

/-- **THE DECIDABLE EQUIVALENCE WITHOUT `hd`**, and with the threshold in the coefficients. -/
theorem reflectionPositive_iff_isCrossBlock' [Nonempty V]
    (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0) (hγ : 0 ≤ γ)
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V)
    (hK : 0 < (α + γ + m ^ 2) ^ 2 - α - β * (α + γ + m ^ 2)) :
    GraphReflection.ReflectionPositive G m θ H ↔ IsCrossBlock G θ H := by
  have hdeg := cast_degree_eq_of_adjSq hA (α := α) (β := β) (γ := γ)
  refine CrossBlockStructure.reflectionPositive_iff_isCrossBlock
    (isRegularOfDegree_of_adjSq hA) hM h hm hγ hA ?_
  rw [hdeg]
  exact hK

/-- **AND SO, ON THIS CLASS, REFLECTION POSITIVITY AT A GIVEN MASS IS DECIDABLE.**
`GreenLargeMass` §12 decides the *large-mass* behaviour of every finite graph; this decides a
*fixed* mass on the `A²` class. Neither contains the other. -/
def decidableRP_of_adjSq [Nonempty V]
    (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0) (hγ : 0 ≤ γ)
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V)
    (hK : 0 < (α + γ + m ^ 2) ^ 2 - α - β * (α + γ + m ^ 2)) :
    Decidable (GraphReflection.ReflectionPositive G m θ H) :=
  decidable_of_iff _ (reflectionPositive_iff_isCrossBlock' hM h hm hγ hA hK).symm

/-! ### `K₂,₂` at every nonzero mass, by `decide` -/

open IndefiniteCoupling in
/-- The threshold is discharged once and for all masses: with `α = 0`, `β = −2`, `γ = 2` it reads
`0 < (2 + m²)(4 + m²)`. -/
theorem bipGraph_hK (m : ℝ) :
    0 < ((0 : ℝ) + 2 + m ^ 2) ^ 2 - 0 - (-2) * ((0 : ℝ) + 2 + m ^ 2) := by
  have h : (0 : ℝ) ≤ m ^ 2 := sq_nonneg m
  nlinarith [h]

open IndefiniteCoupling in
/-- **`K₂,₂` IS REFLECTION POSITIVE AT EVERY NONZERO MASS, AND THE PROOF IS `decide`.** The estate
had this from `hcross` (`GreenExpansion.reflectionPositive_bipGraph` and the criterion route); what
is new is that no hypothesis about the graph's degree is supplied and no vector is exhibited —
the whole verdict, at a fixed mass, comes from inspecting the cut. -/
theorem bipGraph_reflectionPositive_of_ne {m : ℝ} (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive bipGraph m rho Hh := by
  refine (reflectionPositive_iff_isCrossBlock' (α := 0) (β := -2) (γ := 2)
    isMirrorHalf_Hh isRefl_rho_bip hm (by norm_num) bipGraph_adjSq ?_).mpr ?_
  · exact bipGraph_hK m
  · decide

end DecidableFixedMass

end AdjSqForcesRegular
