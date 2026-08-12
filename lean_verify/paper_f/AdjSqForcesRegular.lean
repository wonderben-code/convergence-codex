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

/-! ## 5. The SECOND hypothesis is redundant too — off the diagonal, and with a real exception

§1 read the identity on the diagonal. Read it at an entry `(p, q)` with `p ≠ q` and `p` not
adjacent to `q`: the identity term vanishes, the adjacency term vanishes, and the all-ones term is
one. So

    γ = the number of common neighbours of p and q,

a **count** — which settles `hγ : 0 ≤ γ` without assuming it. Both of the class's hypotheses about
the coefficients are therefore consequences of the identity, on any graph that has two distinct
non-adjacent vertices.

**AND THE EXCEPTION IS REAL, NOT A TECHNICALITY, WHICH IS WHY IT IS PROVED RATHER THAN NOTED.** On a
complete graph there is no such pair, and worse: `J = A + 1`, so `1`, `A` and `J` are linearly
dependent and **the coefficients are not determined by the graph at all.** `completeThree_gamma_one`
and `completeThree_gamma_neg_one` exhibit the same three-vertex graph written both with `γ = 1` and
with `γ = −1`. So on complete graphs `hγ` is a genuine condition — on the *representation chosen*,
not on the graph — and `gamma_nonneg_of_adjSq` cannot be extended to cover them.

**What is invariant even there:** `α + γ` is the degree in every representation, `2` in both of the
two above. §1's conclusion survives the non-uniqueness that kills §5's.
-/

section GammaRedundant

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **`γ` IS A COUNT.** At a non-adjacent pair of distinct vertices the identity reads
`γ = |{common neighbours}|`, so `γ` is determined by the graph and is a cast of a natural number. -/
theorem gamma_eq_common_of_adjSq
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V)
    {p q : V} (hpq : p ≠ q) (hadj : ¬ G.Adj p q) :
    γ = (({x ∈ G.neighborFinset q | G.Adj p x} : Finset V).card : ℝ) := by
  have h := congrFun (congrFun hA p) q
  simp [allOnes, Matrix.one_apply_ne hpq, SimpleGraph.adjMatrix_apply, hadj] at h
  exact h.symm

/-- **HENCE `hγ` IS REDUNDANT**, on any graph with two distinct non-adjacent vertices. -/
theorem gamma_nonneg_of_adjSq
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V)
    {p q : V} (hpq : p ≠ q) (hadj : ¬ G.Adj p q) :
    0 ≤ γ := by
  rw [gamma_eq_common_of_adjSq hA hpq hadj]
  positivity

/-- **THE CONVERSE WITH BOTH COEFFICIENT HYPOTHESES GONE.** What is left is the identity, the
reflection data, a nonzero mass, the threshold, and the one structural fact that the graph is not
complete. -/
theorem reflectionPositive_iff_hcross_of_adjSq'' [Nonempty V] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}
    (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V)
    (hnc : ∃ p q : V, p ≠ q ∧ ¬ G.Adj p q)
    (hK : 0 < (α + γ + m ^ 2) ^ 2 - α - β * (α + γ + m ^ 2)) :
    GraphReflection.ReflectionPositive G m θ H ↔ ∀ w : V → ℝ, crossForm G m θ H w ≤ 0 := by
  obtain ⟨p, q, hpq, hadj⟩ := hnc
  exact reflectionPositive_iff_hcross_of_adjSq' hM h hm (gamma_nonneg_of_adjSq hA hpq hadj) hA hK

/-- And the decidable form the same way. -/
theorem reflectionPositive_iff_isCrossBlock'' [Nonempty V] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}
    (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V)
    (hnc : ∃ p q : V, p ≠ q ∧ ¬ G.Adj p q)
    (hK : 0 < (α + γ + m ^ 2) ^ 2 - α - β * (α + γ + m ^ 2)) :
    GraphReflection.ReflectionPositive G m θ H ↔ CrossBlockStructure.IsCrossBlock G θ H := by
  obtain ⟨p, q, hpq, hadj⟩ := hnc
  exact reflectionPositive_iff_isCrossBlock' hM h hm (gamma_nonneg_of_adjSq hA hpq hadj) hA hK

/-! ### The exception, proved in general: on a complete graph the coefficients form a LINE -/

/-- The complete graph's adjacency matrix is the all-ones matrix minus the identity. -/
theorem top_adjMatrix_eq (V : Type*) [DecidableEq V] :
    (⊤ : SimpleGraph V).adjMatrix ℝ = allOnes V - 1 := by
  ext p q
  by_cases hpq : p = q
  · subst hpq; simp [allOnes, SimpleGraph.adjMatrix_apply]
  · simp [allOnes, SimpleGraph.adjMatrix_apply, Matrix.one_apply_ne hpq, hpq]

/-- The all-ones matrix is `|V|` times idempotent. -/
theorem allOnes_mul_allOnes (V : Type*) [Fintype V] :
    allOnes V * allOnes V = (Fintype.card V : ℝ) • allOnes V := by
  ext p q
  simp [allOnes, Matrix.mul_apply, Finset.card_univ]

/-- **AND SO THE COEFFICIENTS OF A COMPLETE GRAPH ARE A ONE-PARAMETER FAMILY.** `J = A + 1` makes
`1`, `A` and `J` linearly dependent, so the identity holds for **every** real `t`:

    A² = (1 + t)·1 + t·A + (|V| − 2 − t)·J.

`γ = |V| − 2 − t` therefore takes every real value, and `hγ : 0 ≤ γ` is a condition on the
representation rather than on the graph. **`gamma_nonneg_of_adjSq` cannot be extended here**, and
this is why it asks for a non-adjacent pair rather than for something weaker. -/
theorem top_adjSq_family (V : Type*) [Fintype V] [DecidableEq V] (t : ℝ) :
    (⊤ : SimpleGraph V).adjMatrix ℝ * (⊤ : SimpleGraph V).adjMatrix ℝ
      = (1 + t) • (1 : Matrix V V ℝ) + t • (⊤ : SimpleGraph V).adjMatrix ℝ
        + ((Fintype.card V : ℝ) - 2 - t) • allOnes V := by
  rw [top_adjMatrix_eq]
  simp only [sub_mul, mul_sub, allOnes_mul_allOnes, Matrix.one_mul, Matrix.mul_one]
  module

/-- `K₃` with `γ = 1`, from the family at `t = 0`. -/
theorem completeThree_gamma_one :
    (⊤ : SimpleGraph (Fin 3)).adjMatrix ℝ * (⊤ : SimpleGraph (Fin 3)).adjMatrix ℝ
      = (1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + (0 : ℝ) • (⊤ : SimpleGraph (Fin 3)).adjMatrix ℝ + (1 : ℝ) • allOnes (Fin 3) := by
  have h := top_adjSq_family (Fin 3) 0
  rw [show ((1 : ℝ) + 0) = 1 by norm_num,
    show ((Fintype.card (Fin 3) : ℝ) - 2 - 0) = 1 by norm_num [Fintype.card_fin]] at h
  exact h

/-- **AND THE SAME GRAPH WITH `γ = −1`**, from the family at `t = 2`. Two representations of one
graph, so no function of the coefficients alone can be a property of the graph — which is exactly
what `gamma_nonneg_of_adjSq` would have to be if it held here. -/
theorem completeThree_gamma_neg_one :
    (⊤ : SimpleGraph (Fin 3)).adjMatrix ℝ * (⊤ : SimpleGraph (Fin 3)).adjMatrix ℝ
      = (3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + (2 : ℝ) • (⊤ : SimpleGraph (Fin 3)).adjMatrix ℝ + (-1 : ℝ) • allOnes (Fin 3) := by
  have h := top_adjSq_family (Fin 3) 2
  rw [show ((1 : ℝ) + 2) = 3 by norm_num,
    show ((Fintype.card (Fin 3) : ℝ) - 2 - 2) = -1 by norm_num [Fintype.card_fin]] at h
  exact h

/-- **`α + γ` IS THE DEGREE IN BOTH**, which is §1 surviving the non-uniqueness that defeats §5:
`1 + 1 = 2` and `3 + (−1) = 2`, and `K₃` is `2`-regular. **One conclusion of the diagonal argument
is invariant under a change the off-diagonal argument does not survive**, and that asymmetry is the
content of this section. -/
theorem completeThree_alpha_add_gamma (p : Fin 3) :
    ((⊤ : SimpleGraph (Fin 3)).degree p : ℝ) = 1 + 1
      ∧ ((⊤ : SimpleGraph (Fin 3)).degree p : ℝ) = 3 + (-1) :=
  ⟨degree_eq_of_adjSq completeThree_gamma_one p,
   degree_eq_of_adjSq completeThree_gamma_neg_one p⟩

end GammaRedundant

/-! ## 6. All three entries read: the class is the STRONGLY REGULAR GRAPHS, in their own parameters

§1 read the identity on the diagonal and §5 at a non-adjacent pair. The third case is an
**adjacent** pair, and it completes the picture: there `(A²) p q` is again a count of common
neighbours, and the right-hand side is `α · 0 + β · 1 + γ · 1`. So

| entry read                | left side is                        | equals    |
|---------------------------|-------------------------------------|-----------|
| `p = q`                   | the degree                          | `α + γ`   |
| `p ≠ q`, not adjacent     | common neighbours of a NON-edge     | `γ`       |
| `p ≠ q`, adjacent         | common neighbours of an EDGE        | `β + γ`   |

**That is the definition of a strongly regular graph**, in the classical parameters
`(k, λ, μ)` = (degree, common neighbours of an edge, common neighbours of a non-edge). The estate's
`(α, β, γ)` is `(k − μ, λ − μ, μ)`, and the identity `A² = α·1 + β·A + γ·J` is the textbook
`A² = k·1 + λ·A + μ·(J − 1 − A)` rearranged.

**Why this is worth writing down rather than remarking.** `GreenExpansion` §9 introduced its class
by an algebraic condition chosen because the expansion needed it, and nothing in the estate says
what that class *is*. It is not an ad-hoc family: **it is the strongly regular graphs**, and the
three hypotheses the estate carried about it — regularity, `0 ≤ γ`, and now `0 ≤ β + γ` — are all
three the statement that a count is a count.

**The same exception applies and is not restated in each case:** on a complete graph there are no
non-edges and the coefficients are a line (§5), so `μ` is not defined by the graph. `λ` is, because
edges exist; `β + γ` is therefore pinned even there, while `γ` alone is not.
-/

section StronglyRegular

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **THE THIRD ENTRY.** At an adjacent pair the identity reads `β + γ = |common neighbours|`. -/
theorem beta_add_gamma_eq_common_of_adjSq
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V)
    {p q : V} (hpq : p ≠ q) (hadj : G.Adj p q) :
    β + γ = (({x ∈ G.neighborFinset q | G.Adj p x} : Finset V).card : ℝ) := by
  have h := congrFun (congrFun hA p) q
  simp [allOnes, Matrix.one_apply_ne hpq, SimpleGraph.adjMatrix_apply, hadj] at h
  linarith [h]

/-- Hence `0 ≤ β + γ` — the third hypothesis about the coefficients that is a count in disguise,
and it is pinned even on a complete graph, where `γ` alone is not (§5). -/
theorem beta_add_gamma_nonneg_of_adjSq
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V)
    {p q : V} (hpq : p ≠ q) (hadj : G.Adj p q) :
    0 ≤ β + γ := by
  rw [beta_add_gamma_eq_common_of_adjSq hA hpq hadj]
  positivity

/-- **THE DICTIONARY, IN ONE STATEMENT.** The estate's `(α, β, γ)` are the classical strongly
regular parameters: `k = α + γ` is the degree, `λ = β + γ` counts the common neighbours of an edge,
`μ = γ` counts those of a non-edge. Stated with both a non-edge and an edge supplied, since each
clause needs its own witness and the complete and empty graphs have only one of the two. -/
theorem srg_parameters
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V)
    {p q r t : V} (hpq : p ≠ q) (hnon : ¬ G.Adj p q) (hrt : r ≠ t) (hedge : G.Adj r t) (v : V) :
    (G.degree v : ℝ) = α + γ
      ∧ γ = (({x ∈ G.neighborFinset q | G.Adj p x} : Finset V).card : ℝ)
      ∧ β + γ = (({x ∈ G.neighborFinset t | G.Adj r x} : Finset V).card : ℝ) :=
  ⟨degree_eq_of_adjSq hA v, gamma_eq_common_of_adjSq hA hpq hnon,
   beta_add_gamma_eq_common_of_adjSq hA hrt hedge⟩

/-- `K₂,₂` in the classical parameters: degree `2`, an edge's endpoints share `0` neighbours, a
non-edge's share `2`. In the estate's coefficients that is `α = 0`, `β = −2`, `γ = 2`
(`GreenExpansion.bipGraph_adjSq`), and **the dictionary turns one into the other**: `k = 0 + 2 = 2`,
`λ = −2 + 2 = 0`, `μ = 2`. The negative `β` that looks odd on its own is `λ − μ`. -/
theorem bipGraph_srg :
    ((0 : ℝ) + 2 = 2) ∧ ((-2 : ℝ) + 2 = 0) ∧ ((2 : ℝ) = 2) := by
  norm_num

end StronglyRegular

end AdjSqForcesRegular
