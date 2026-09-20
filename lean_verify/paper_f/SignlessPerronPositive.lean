import SignlessSecondEigen

/-!
# The Perron eigenvector of a connected graph's signless Laplacian is nowhere zero

This estate has a great deal of Perron–Frobenius machinery and **all of it consumes a positive
eigenvector rather than producing one**. `PerronDominant.abs_le_of_pos_eigenvector`,
`PerronDominant.abs_lt_of_not_signConstant`, `PerronDominant.abs_lt_of_not_proportional` and
`PerronCollatzWielandt.le_of_subinvariant` each take `∀ i, 0 < v i` as a hypothesis; grepped
before writing, and no declaration anywhere concludes it for `Q = D + A`. So the chain has the
consequences of Perron positivity and not the fact.

## What is proved

**`mv_absVec_eq`** — the step the rest rests on. If `v` is a top eigenvector of `Q` then so is
`|v|`, the vector of absolute values. `PerronGap.abs_smul_le_mv_absVec` gives
`topEigen · |v|ᵢ ≤ (Q|v|)ᵢ` entrywise for a matrix with non-negative entries, which pairs with
`|v| ≥ 0` into `⟪|v|, Q|v|⟫ ≥ topEigen ⟪|v|, |v|⟫`; `RayleighVariational.quadForm_le_topEigen`
is the reverse inequality; and `RayleighMatrix.mv_eq_smul_of_quadForm_eq` turns the resulting
equality in the quadratic form into the eigenvector equation. **No connectivity is used here**
and the matrix is only asked to be symmetric with non-negative entries, which is why the proof
is stated for `Q` and not for a general such matrix only by choice of where it lives.

**`absVec_pos`** — and on a **connected** graph `|v|` is strictly positive.
`SignlessPerronSimple.pow_mulVec_of_eigen` raises the eigenvector equation to the power `|V|`,
`SignlessPrimitive.pow_card_pos` says `Q ^ |V|` has every entry strictly positive, and a
strictly positive matrix applied to a non-negative non-zero vector has every entry strictly
positive. Dividing by `topEigen ^ |V|`, which is positive because `Q` has a positive entry on a
connected graph with two or more vertices, gives `0 < |v|ᵢ`.

**`top_eigenvector_ne_zero`** — hence no coordinate of a top eigenvector vanishes, and
**`top_eigenvector_signConstant`** — hence it is sign-constant, every entry `≥ 0` or every entry
`≤ 0`. The second uses unit 143's `finrank_eigenspace_topEigen_signlessLap_eq_one`: the top
eigenspace is a line, `|v|` and `v` both lie on it, so `v = c • |v|` and the sign of `c` decides
every coordinate at once.

## What is NOT here

* **NO EXISTENCE STATEMENT BEYOND WHAT THE SPECTRAL THEOREM ALREADY GIVES.** These are all
  conditional on being handed an eigenvector; that one exists is
  `SignlessPerronSimple.exists_topEigen` together with Mathlib's eigenvector basis, and nothing
  new is claimed about it.
* **NOTHING FOR A DISCONNECTED GRAPH.** Connectivity is load-bearing and not cosmetic: on two
  disjoint edges the top eigenspace is two-dimensional and contains vectors supported on one
  component, which vanish on the other.
* **NO IRREDUCIBILITY IN THE ABSTRACT.** The argument runs through
  `SignlessPrimitive.pow_card_pos`, which is about `Q` on a graph; the general statement for an
  irreducible non-negative matrix is not formulated and is **not attempted** (`ERRATUM 246`).
  Naming it is not a claim that it is short (`ERRATUM 194`).
* **NO PERRON ROOT CHARACTERISATION.** Collatz–Wielandt as a `sInf`/`sSup` formula is untouched;
  `PerronCollatzWielandt` holds the two inequalities and this file adds neither.
* **Nothing over `ℂ`. No wall moves and no published tag moves.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a finite vertex type with decidable
equality and decidable adjacency throughout; `Nontrivial V` and `G.Connected` for everything
after `mv_absVec_eq`, which takes neither.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SignlessPerronPositive

open Matrix Finset SimpleGraph LaplacianSignless RayleighVariational RayleighMatrix PerronVector

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Abbreviation for the Hermitian witness, which every statement below carries. -/
local notation "hQ" => LaplacianSignlessDefinite.signlessLap_isHermitian G

/-- **IF `v` IS A TOP EIGENVECTOR THEN SO IS `|v|`.** The inequality
`topEigen · |v|ᵢ ≤ (Q|v|)ᵢ` holds entrywise for any matrix with non-negative entries; pairing it
with `|v| ≥ 0` gives `⟪|v|, Q|v|⟫ ≥ topEigen ⟪|v|,|v|⟫`, and the Rayleigh bound is the reverse.
Equality in the quadratic form is an eigenvector equation. **Connectivity is not used.** -/
theorem mv_absVec_eq [Nonempty V] {v : EuclideanSpace ℝ V}
    (hv : mv (signlessLap G) v = topEigen hQ • v) :
    mv (signlessLap G) (absVec v) = topEigen hQ • absVec v := by
  classical
  have hnn : 0 ≤ topEigen hQ := by
    obtain ⟨i, hi⟩ := SignlessPerronSimple.exists_topEigen hQ
    exact hi ▸ (LaplacianSignlessDefinite.signlessLap_posSemidef G).eigenvalues_nonneg i
  have hstep : ∀ i, topEigen hQ * (WithLp.ofLp (absVec v)) i
      ≤ (WithLp.ofLp (mv (signlessLap G) (absVec v))) i := by
    intro i
    have := PerronGap.abs_smul_le_mv_absVec (A := signlessLap G)
      (SignlessPrimitive.sl_nonneg G) hv i
    rwa [abs_of_nonneg hnn] at this
  -- the quadratic form is at least `topEigen ‖|v|‖²`, because `|v| ≥ 0`
  have hge : topEigen hQ * inner ℝ (absVec v) (absVec v)
      ≤ inner ℝ (absVec v) (mv (signlessLap G) (absVec v)) := by
    rw [inner_expand, inner_expand, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have habs : (0 : ℝ) ≤ (WithLp.ofLp (absVec v)) i := by
      rw [absVec_apply]; exact abs_nonneg _
    calc topEigen hQ * ((WithLp.ofLp (absVec v)) i * (WithLp.ofLp (absVec v)) i)
        = (WithLp.ofLp (absVec v)) i * (topEigen hQ * (WithLp.ofLp (absVec v)) i) := by ring
      _ ≤ (WithLp.ofLp (absVec v)) i
            * (WithLp.ofLp (mv (signlessLap G) (absVec v))) i := by
          exact mul_le_mul_of_nonneg_left (hstep i) habs
  -- and at most that, by the Rayleigh bound
  have hle : inner ℝ (absVec v) (mv (signlessLap G) (absVec v))
      ≤ topEigen hQ * inner ℝ (absVec v) (absVec v) := by
    have := quadForm_le_topEigen hQ (WithLp.ofLp (absVec v))
    rw [inner_expand, inner_expand]
    simpa [dotProduct, Matrix.mulVec, mv, Finset.mul_sum, mul_comm] using this
  exact mv_eq_smul_of_quadForm_eq hQ (SignlessPerronSimple.le_topEigen hQ)
    (le_antisymm hle hge)

/-- The same in `mulVec` form, which is what the power lemma and the kernel bridge speak. -/
theorem mulVec_absVec_eq [Nonempty V] {v : EuclideanSpace ℝ V}
    (hv : mv (signlessLap G) v = topEigen hQ • v) :
    (signlessLap G).mulVec (WithLp.ofLp (absVec v))
      = topEigen hQ • (WithLp.ofLp (absVec v)) :=
  congrArg WithLp.ofLp (mv_absVec_eq G hv)

/-- **AND ON A CONNECTED GRAPH `|v|` HAS EVERY COORDINATE STRICTLY POSITIVE.** Raise the
eigenvector equation to the power `|V|` (`SignlessPerronSimple.pow_mulVec_of_eigen`), where
`SignlessPrimitive.pow_card_pos` makes every entry of the matrix strictly positive; a strictly
positive matrix applied to a non-negative non-zero vector is strictly positive in every
coordinate, and `0 < c * |v|ᵢ` with `|v|ᵢ ≥ 0` forces `|v|ᵢ > 0`. **The positivity of
`topEigen` is not needed as an input** — it falls out of the same inequality. -/
theorem absVec_pos [Nontrivial V] (hconn : G.Connected) {v : EuclideanSpace ℝ V}
    (hv : mv (signlessLap G) v = topEigen hQ • v) (hne : v ≠ 0) (i : V) :
    0 < (WithLp.ofLp (absVec v)) i := by
  classical
  set w : V → ℝ := WithLp.ofLp (absVec v) with hw
  have hwnn : ∀ j, 0 ≤ w j := fun j => by rw [hw, absVec_apply]; exact abs_nonneg _
  obtain ⟨j₀, hj₀⟩ : ∃ j, 0 < w j := by
    have hv0 : WithLp.ofLp v ≠ 0 := fun h => hne (by ext j; simpa using congrFun h j)
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
    exact ⟨j, by rw [hw, absVec_apply]; exact abs_pos.2 hj⟩
  have hpow := SignlessPerronSimple.pow_mulVec_of_eigen (mulVec_absVec_eq G hv) (Fintype.card V)
  have hrow : 0 < ((signlessLap G ^ Fintype.card V).mulVec w) i := by
    rw [Matrix.mulVec, dotProduct]
    refine Finset.sum_pos' (fun j _ => ?_) ⟨j₀, Finset.mem_univ j₀, ?_⟩
    · exact mul_nonneg (SignlessPrimitive.pow_card_pos G hconn i j).le (hwnn j)
    · exact mul_pos (SignlessPrimitive.pow_card_pos G hconn i j₀) hj₀
  rw [hpow] at hrow
  have hrow' : 0 < topEigen hQ ^ Fintype.card V * w i := by simpa using hrow
  refine lt_of_le_of_ne (hwnn i) (Ne.symm ?_)
  intro h0
  rw [h0, mul_zero] at hrow'
  exact lt_irrefl 0 hrow'

/-- **SO NO COORDINATE OF A TOP EIGENVECTOR VANISHES.** -/
theorem top_eigenvector_ne_zero [Nontrivial V] (hconn : G.Connected)
    {v : EuclideanSpace ℝ V} (hv : mv (signlessLap G) v = topEigen hQ • v) (hne : v ≠ 0)
    (i : V) : (WithLp.ofLp v) i ≠ 0 := by
  have := absVec_pos G hconn hv hne i
  rw [absVec_apply] at this
  exact abs_pos.1 this

/-- **AND IT IS SIGN-CONSTANT**: every coordinate `≥ 0`, or every coordinate `≤ 0`. This is
where unit 143's `finrank_eigenspace_topEigen_signlessLap_eq_one` is spent — the top eigenspace
is a LINE, `|v|` and `v` both lie on it and `|v|` is non-zero, so `v = c • |v|` and the single
scalar `c` decides every coordinate at once. -/
theorem top_eigenvector_signConstant [Nontrivial V] (hconn : G.Connected)
    {v : EuclideanSpace ℝ V} (hv : mv (signlessLap G) v = topEigen hQ • v) (hne : v ≠ 0) :
    (∀ i, 0 ≤ (WithLp.ofLp v) i) ∨ (∀ i, (WithLp.ofLp v) i ≤ 0) := by
  classical
  set w : V → ℝ := WithLp.ofLp (absVec v) with hw
  have hwpos : ∀ i, 0 < w i := absVec_pos G hconn hv hne
  have hw0 : w ≠ 0 := fun h => absurd (h ▸ hwpos (Classical.arbitrary V)) (lt_irrefl 0)
  have hvmul : (signlessLap G).mulVec (WithLp.ofLp v) = topEigen hQ • (WithLp.ofLp v) :=
    congrArg WithLp.ofLp hv
  obtain ⟨c, hc⟩ := SignlessSecondEigen.exists_smul_of_mulVec_eq_topEigen G hconn
    (mulVec_absVec_eq G hv) hw0 hvmul
  rcases le_total 0 c with hcpos | hcneg
  · exact Or.inl fun i => by
      rw [← congrFun hc i]; exact mul_nonneg hcpos (hwpos i).le
  · refine Or.inr fun i => ?_
    rw [← congrFun hc i]
    calc c * w i ≤ 0 * w i := mul_le_mul_of_nonneg_right hcneg (hwpos i).le
      _ = 0 := zero_mul _

end SignlessPerronPositive
