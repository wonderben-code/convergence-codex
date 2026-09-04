import NonnegPerronNorm
import PerronVector

/-!
# The quadratic form under an entrywise absolute value, both sides, and the two halves connected

For a matrix with nonnegative entries, replacing a vector by its entrywise absolute value can only
increase the quadratic form — in **both** directions, since the same termwise estimate
`±(xᵢ Aᵢⱼ xⱼ) ≤ |xᵢ| Aᵢⱼ |xⱼ|` gives each. **This estate holds one half in each of two vector APIs
and neither file knows about the other**:

* `PerronVector.quadForm_absVec_ge` — `⟪v, Av⟫ ≤ ⟪|v|, A|v|⟫`, in `EuclideanSpace` and `inner`,
  proved weeks ago and used by `PerronGap`;
* `NonnegPerronNorm.neg_quadForm_le_quadForm_abs` — `−(xᵀAx) ≤ |x|ᵀA|x|`, in `dotProduct`, proved
  2026-09-04 without knowing of the first.

**They are not duplicates. They are the two halves of one inequality**, and `ERRATUM 446`'s addendum
recorded the wrong relationship: it caught that `dotProduct_abs_self` restates
`PerronVector.normSq_absVec` and did not notice that the main lemma has a sibling. Had the older
half been found, the natural thing to write was the two-sided statement once.

## What this file does

`le_quadForm_abs` supplies the missing half **in `dotProduct`**, and
`abs_quadForm_le_quadForm_abs` joins it to the 2026-09-04 half:

```
|x ⬝ᵥ A *ᵥ x|  ≤  |x| ⬝ᵥ A *ᵥ |x|          entries of `A` nonnegative, no symmetry needed
```

**Nothing is superseded** (`ERRATUM 337`). `PerronVector`'s statement is in `EuclideanSpace` and its
consumers are there; this one is in `dotProduct` and so are the operator-norm chain's; the two
cannot replace each other without a bridge, and building that bridge is not what this file is for.
What changes is that each now names the other.

## The instrument gap, measured and deliberately not filled

`check_ledger.py --shape` searches the **statements** of every theorem in the pinned environment by
regex — **316,986** of them — which is exactly the tool for *"does a theorem of this shape already
exist"*. Run on this estate's own names it returns nothing: `absVec` **0 matches**, `sqrtStar`
**0 matches**, both being `paper_f` declarations. **The estate has statement-level search for the
library and none for itself**, and the duplication `ERRATUM 446` records happened entirely inside
the estate. That is a measurement, not a proposal (`ERRATUM 433`); `RE-SWEEP #35` is the standing
reason not to build an instrument on a small number of instances.

**What does work, and is recorded because it worked twice**: searching by *shape* over `paper_f` by
hand. The 2026-09-03 log entry found `quadForm_absVec_ge` that way — *"under a name I found by
searching for the shape rather than the name I would have given it"* — and this file was found the
same way, from that entry.

## What is NOT here

**No new mathematics.** Both halves are the same two-line termwise estimate; only the second half in
this API and the join are new, and neither is difficult. The file exists for the connection.

**Not a bridge between the vector APIs.** `EuclideanSpace`-versus-`dotProduct` is a real seam this
estate crosses by hand each time; nothing here makes it automatic.

**No wall moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace QuadFormAbsTwoSided

open Matrix Finset
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- The double-sum form of the quadratic form, shared by both halves. -/
theorem quadForm_expand (A : Matrix V V ℝ) (y : V → ℝ) :
    y ⬝ᵥ A *ᵥ y = ∑ i : V, ∑ j : V, y i * (A i j * y j) := by
  rw [dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [mulVec, dotProduct, Finset.mul_sum]

omit [DecidableEq V] in
/-- **`xᵀAx ≤ |x|ᵀA|x|` — the half this API was missing.**
`PerronVector.quadForm_absVec_ge` is the same statement in `EuclideanSpace` and `inner`; this is it
in `dotProduct`, where the operator-norm chain lives. Neither replaces the other
(`ERRATUM 337`). -/
theorem le_quadForm_abs {A : Matrix V V ℝ} (hA : ∀ i j, 0 ≤ A i j) (x : V → ℝ) :
    x ⬝ᵥ A *ᵥ x ≤ (fun i => |x i|) ⬝ᵥ A *ᵥ (fun i => |x i|) := by
  rw [quadForm_expand, quadForm_expand]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h1 : x i * (A i j * x j) ≤ |x i * (A i j * x j)| := le_abs_self _
  have h2 : |x i * (A i j * x j)| = |x i| * (A i j * |x j|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (hA i j)]
  linarith [h1, h2.le, h2.ge]

omit [DecidableEq V] in
/-- **BOTH SIDES AT ONCE**: `|xᵀAx| ≤ |x|ᵀA|x|`, for any matrix with nonnegative entries and with
no symmetry hypothesis. The upper half is `le_quadForm_abs` above; the lower is
`NonnegPerronNorm.neg_quadForm_le_quadForm_abs`, proved on 2026-09-04 in ignorance of
`PerronVector.quadForm_absVec_ge`, which is this file's occasion (`ERRATUM 446`). -/
theorem abs_quadForm_le_quadForm_abs {A : Matrix V V ℝ} (hA : ∀ i j, 0 ≤ A i j) (x : V → ℝ) :
    |x ⬝ᵥ A *ᵥ x| ≤ (fun i => |x i|) ⬝ᵥ A *ᵥ (fun i => |x i|) :=
  abs_le.mpr ⟨neg_le_of_neg_le (NonnegPerronNorm.neg_quadForm_le_quadForm_abs hA x),
    le_quadForm_abs hA x⟩

end QuadFormAbsTwoSided
