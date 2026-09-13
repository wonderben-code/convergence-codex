import BoxLapBasis
import TorusMultiplicity

/-!
# The box's multiplicities are exact fibre counts, and clause (c) was false as filed

**THE SIGNLESS FRONTIER ITEM'S THIRD CLAUSE IS FALSE, AND WAS FALSE ELEVEN DAYS BEFORE IT WAS
WRITTEN** (`ERRATUM 528`). Filed 2026-09-11 as *on the box that is `n^d` exhibited modes with no
exhaustion claim (`BoxLapSpectrum`) and multiplicities bounded only below (`BoxLapMultiplicity`)*,
it names as missing something `BoxLapBasis` had supplied on **2026-08-31**: the modes are a
**basis**, and `lapEigenvalue_iff` is the exhaustion. **All three of that item's original clauses
are now false as filed** — (a) by `ERRATUM 511`, (b) by `ERRATUM 506`, (c) here — and this file
answers the half that really was open.

**THE MULTIPLICITY HALF, AND WHY IT WAS ONE GENERALISATION AWAY.**
`TorusMultiplicity.finrank_eigenspace_of_basis` turns an eigenbasis into exact multiplicities: the
eigenspace at `μ` is the span of the basis vectors whose eigenvalue is `μ`, so its dimension is the
**fibre count**. It was stated over `ℂ` and the box's basis is real. **Nothing in it used `ℂ`** —
the proof is `sub_eq_zero`, a span computation and `finrank_span_eq_card` — so it and
`eigenspace_eq_span_of_basis` are now stated over a field, **generalised in place with their proof
bodies unchanged**, which is `RE-SWEEP #53`'s result (i) and `ERRATUM 511`'s pattern applied a
second time.

## What is proved

**`finrank_eigenspace_boxLap`** — **`L`'s multiplicity at `μ` on the free-boundary box is exactly
the number of frequency vectors `k` with `boxLapEig k = μ`.** Five lines on top of the
generalisation, and it converts `BoxLapMultiplicity.multinomial_le_card_eigFibre` from a bound on
a fibre into a bound on a **multiplicity**.

**`finrank_eigenspace_boxLap_one`** — at `d = 1` every multiplicity is `0` or `1`, because
`BoxLapBasis.lapEigenvalue_injective` makes the frequency-to-eigenvalue map injective there. The
spectrum of a path's free-boundary Laplacian is **simple**, which the chain knew for the path graph
by another route and not for this presentation of it.

## What is NOT here

* **NO EXACT MULTIPLICITY AT `d ≥ 2`, as of 2026-09-13 (entry 68).** The fibre count is now the
  right object but nothing computes it: `BoxLapMultiplicity` bounds it below by a multinomial
  coefficient — the permutation orbit — and its own `sporadic_eq` shows the orbit is not
  everything, `boxLapEig 2 6 ![0,3] = boxLapEig 2 6 ![2,2]` with `sporadic_not_perm`. **Counting
  the fibre is a question about sums of `2 − 2cos(kπ/n)` colliding**, which is number theory this
  estate has not touched. Not attempted (`ERRATUM 246`).
* **NOTHING ABOUT `Q` ON THE BOX IS ADDED HERE, as of 2026-09-13 (entry 68).** The box is
  two-colourable and `SignlessBipartite.charpoly_signlessLap_eq_of_colorable` transfers `L`'s
  characteristic polynomial to `Q`; **that composition is not made in this file** and no
  declaration here mentions `signlessLap`.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the box theorems take a dimension and a
side length and nothing else; the generalised pair takes a `Field`. **No mass, no propagator, no
metric.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace BoxLapMultiplicityExact

open Matrix SimpleGraph BoxGraph BoxLapSpectrum BoxLapBasis

/-! ## 1. The multiplicity is the fibre count -/

/-- **`L`'s MULTIPLICITY ON THE FREE-BOUNDARY BOX, EXACTLY.** -/
theorem finrank_eigenspace_boxLap (d m : ℕ) (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        ((boxGraph d (m + 1)).lapMatrix ℝ) - μ • LinearMap.id))
      = Nat.card {k : Site d (m + 1) // boxLapEig d (m + 1) (fun i => (k i).val) = μ} :=
  TorusMultiplicity.finrank_eigenspace_of_basis _ (boxLapBasis d m)
    (fun k => boxLapEig d (m + 1) fun i => (k i).val)
    (fun k => by rw [boxLapBasis_apply]; exact lapMatrix_mulVec_siteLapVec d m k) μ

/-! ## 2. So at `d = 1` the spectrum is simple -/

/-- **AT ONE DIMENSION EVERY MULTIPLICITY IS AT MOST ONE**, the frequency-to-eigenvalue map being
injective there. -/
theorem finrank_eigenspace_boxLap_one (m : ℕ) (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        ((boxGraph 1 (m + 1)).lapMatrix ℝ) - μ • LinearMap.id)) ≤ 1 := by
  classical
  rw [finrank_eigenspace_boxLap 1 m μ, Nat.card_eq_fintype_card]
  refine Fintype.card_le_one_iff.mpr fun a b => ?_
  have hab : boxLapEig 1 (m + 1) (fun i => (a.1 i).val)
      = boxLapEig 1 (m + 1) (fun i => (b.1 i).val) := by rw [a.2, b.2]
  simp only [boxLapEig, Finset.univ_unique, Finset.sum_singleton] at hab
  have := lapEigenvalue_injective m hab
  exact Subtype.ext (funext fun i => by
    have hi : i = default := Subsingleton.elim _ _
    subst hi; exact this)

end BoxLapMultiplicityExact
