import SignlessRegularSimple

/-!
# `K_{1,3,3}`'s signless spectrum is exactly `{1, 4, 9}`

**ENTRY 173 FENCED THIS AND NAMED THE WRONG ROUTE.** It computed the three multiplicities at
`K_{1,3,3}` — `1` at `1`, `5` at `4`, `1` at `9`, adding to the seven vertices — and then wrote:
*three eigenspaces for distinct eigenvalues are independent and their dimensions add to `N`, so no
fourth eigenvalue can exist, **but that inference is not in Lean here**; the
characteristic-polynomial route used for the diamond would do it and is not written.*

**The inference was in Lean, and not by that route.**
`HermitianFibreCount.mem_of_isEigenvalue_of_sum_eq` says, for **every** real Hermitian matrix, that
a table of eigenspace dimensions adding to the dimension of the space leaves no room for another
eigenvalue. It has been in the estate since before this chain began, `UnbalancedMultipartiteTable`
cites it by name, and applying it here is three lines. The fence was right that the statement was
missing from that file and wrong about what it would cost, which is the same error the last five
entries have been finding in other people's fences and is here in one of my own.

## What is proved

**`sum_finrank_part133`** — the three multiplicities entry 173 computed add to the vertex count,
`1 + 5 + 1 = 7`, as a `Finset` sum over `{1, 4, 9}` rather than as arithmetic in a docstring.

**`isEigenvalue_signless_part133`** — so a real `μ` is an eigenvalue of `Q` on `K_{1,3,3}`
**exactly when** it is `1`, `4` or `9`. Entry 173's gap, closed.

**`image_eigenvalues_signless_part133`, `charpoly_signlessLap_part133`** — the eigenvalue image and
`Q`'s characteristic polynomial, `(X − 1)(X − 4)^5(X − 9)`. **The exponent `5` is the overlap made
visible**: four of those dimensions come from the two parts of size three and the fifth from the
secular root that sits on the part value, which is what entry 173 exhibited and what
`finrank_signless_size_secular_one`'s `+ 1` counts.

## What is NOT here

* **NOTHING NEW ABOUT THE POLE `5`.** Entry 173 already showed it is not an eigenvalue; the
  completeness statement re-confirms that from the other side and adds nothing to it.
* **STILL ONE GRAPH.** Nothing here says when a part value is a secular root, and there is still no
  family in which the coincidence occurs — entry 173's fence on that point stands unchanged.
* **THE OTHER MULTIPARTITE LEFTOVERS ARE UNTOUCHED**: the exact count of the spectrum in general,
  whether the `3s` bound is ever attained, the complement case with no half-sized part, and the
  root values.
* **NOTHING OVER `ℂ`, AND THAT WAS PRICED RATHER THAN ASSUMED.** The Hermitian multiplicity chain
  this file leans on — `HermitianFibreCount` and `HermitianRootMultiplicity` — is stated over `ℝ`
  throughout, and Mathlib's `Matrix.IsHermitian` is `RCLike`-general, so the generalisation is the
  same shape as the four this run has taken. **It is declined here for want of a consumer**: a grep
  finds complex Hermitian matrices in `HermitianNotLie` and `HiggsBridge` only, and neither wants an
  eigenvalue multiplicity. Generalising with no caller is the kind of work that looks like progress,
  and the four generalisations that paid this run each had one (`ERRATUM 246`).
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and
  `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): **none** — every statement is about the one
explicit graph `Part133`, and the only input is entry 173's three multiplicities together with the
Hermitian-ness of `Q`, which `LaplacianSignlessDefinite.signlessLap_isHermitian` supplies for every
graph. **No mass, no propagator, and no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessPart133Complete

open Matrix Finset SimpleGraph LaplacianSignless Polynomial
open UnbalancedMultipartite SecularRootAtPartValue

/-! ## 1. The three multiplicities add to the vertex count, so there is no fourth eigenvalue -/

theorem sum_finrank_part133 :
    ∑ μ ∈ ({1, 4, 9} : Finset ℝ), Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap (completeMultipartiteGraph Part133)) - μ • LinearMap.id))
      = Fintype.card (Σ i, Part133 i) := by
  have h1 : (1 : ℝ) ∉ ({4, 9} : Finset ℝ) := by norm_num
  have h4 : (4 : ℝ) ∉ ({9} : Finset ℝ) := by norm_num
  rw [Finset.sum_insert h1, Finset.sum_insert h4, Finset.sum_singleton,
    finrank_signless_part133_one, finrank_signless_part133_four,
    finrank_signless_part133_nine, card_part133]
  norm_num

/-- **THE SPECTRUM IS EXACTLY `{1, 4, 9}`.** -/
theorem isEigenvalue_signless_part133 (μ : ℝ) :
    (∃ x : (Σ i, Part133 i) → ℝ, x ≠ 0
        ∧ signlessLap (completeMultipartiteGraph Part133) *ᵥ x = μ • x)
      ↔ μ = 1 ∨ μ = 4 ∨ μ = 9 := by
  constructor
  · rintro ⟨x, hx0, hx⟩
    have := HermitianFibreCount.mem_of_isEigenvalue_of_sum_eq
      (LaplacianSignlessDefinite.signlessLap_isHermitian (completeMultipartiteGraph Part133))
      ({1, 4, 9} : Finset ℝ) sum_finrank_part133 hx0 hx
    simpa using this
  · intro h
    rw [UnbalancedMultipartiteSecularEquation.isEigenvector_iff_finrank_pos]
    rcases h with h | h | h
    · rw [h, finrank_signless_part133_one]; norm_num
    · rw [h, finrank_signless_part133_four]; norm_num
    · rw [h, finrank_signless_part133_nine]; norm_num

/-! ## 2. The eigenvalue image and the characteristic polynomial -/

theorem image_eigenvalues_signless_part133 :
    Finset.univ.image (LaplacianSignlessDefinite.signlessLap_isHermitian
        (completeMultipartiteGraph Part133)).eigenvalues = {1, 4, 9} := by
  ext μ
  rw [HermitianCharpoly.mem_image_eigenvalues_iff, isEigenvalue_signless_part133]
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- **`Q`'S CHARACTERISTIC POLYNOMIAL AT `K_{1,3,3}`**, with the overlap visible as the exponent
`5` — four dimensions from the two parts of size three and one from the secular root. -/
theorem charpoly_signlessLap_part133 :
    (signlessLap (completeMultipartiteGraph Part133)).charpoly
      = (X - C (1 : ℝ)) * (X - C (4 : ℝ)) ^ 5 * (X - C (9 : ℝ)) := by
  have hA := LaplacianSignlessDefinite.signlessLap_isHermitian
    (completeMultipartiteGraph Part133)
  have h1 : (1 : ℝ) ∉ ({4, 9} : Finset ℝ) := by norm_num
  have h4 : (4 : ℝ) ∉ ({9} : Finset ℝ) := by norm_num
  rw [HermitianCharpoly.charpoly_eq_prod_pow_finrank hA, image_eigenvalues_signless_part133,
    Finset.prod_insert h1, Finset.prod_insert h4, Finset.prod_singleton,
    finrank_signless_part133_one, finrank_signless_part133_four,
    finrank_signless_part133_nine]
  ring

end SignlessPart133Complete
