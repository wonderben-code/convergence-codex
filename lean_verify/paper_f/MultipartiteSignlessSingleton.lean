import MultipartiteSignlessCharpoly

/-!
# Parts of one vertex: the two-factor case, and the criterion's first satisfying instance

**THE PREVIOUS UNIT'S HYPOTHESIS, REMOVED.** `MultipartiteSignlessCharpoly` takes `t ≥ 2` and said
why in its own list: at `t = 1` the third exponent `rt − r` is zero, the third value stops being an
eigenvalue, and the product has two factors instead of three, *a different shape, not given*. This
is that shape — the standing queue's *deepen existing results by removing one restrictive
hypothesis at a time*, applied to a hypothesis one unit old.

## What is proved

**`finrank_part_singleton`** — at `t = 1` the eigenspace at `(r−1)t` is trivial, from
`MultipartiteEigenspace`'s own identification of it with `ker partForm` and `rt − r = 0`.
**`top_ne_mid_singleton`, `image_eigenvalues_signlessLap_singleton`** — so the image of the
eigenvalue enumeration has **two** elements, the third value being excluded *because its
multiplicity is zero* rather than because it coincides with another.

**`charpoly_signlessLap_singleton`** — `(X − 2(r−1))·(X − (r−2))^{r−1}` for `r ≥ 2`, degree `r`.

**`nodup_roots_charpoly_signlessLap_edge`** — **at `r = 2` the signless spectrum is simple**, and
that is the first time this chain puts a graph through
`SimpleSpectrumCharpoly.nodup_roots_charpoly_signlessLap_iff` on the **satisfying** side; the
previous unit's only instance was negative. **`not_nodup_roots_charpoly_signlessLap_singleton`** —
and at `r ≥ 3` it is not simple, so at parts of one vertex the answer is a clean dichotomy at
`r = 2`.

## What is NOT here

* **THE GRAPH IS `K_r`, AND THE ESTATE HOLDS IT UNDER ANOTHER NAME.** `CompleteSignlessSpectrum`
  works with `⊤ : SimpleGraph V`. **It is not a duplicate**: that file proves the two
  characteristic polynomials **differ** on `K_n` and factorises neither, so no product form for
  `Q` existed there. But `completeEquipartiteGraph r 1` and `⊤` are the same graph on different
  index types and **no isomorphism between them is formalised**, as everywhere in this chain, so
  nothing here transfers to that file's statements or back.
* **`r = 2` IS NOT A NEW EXAMPLE ON THE SATISFYING SIDE.** `K₂` is the path on two vertices and is
  already on the standing item's satisfying list. What is new is only that the criterion has been
  used in that direction at all — and it is used on the **signless** Laplacian, where the standing
  item is about the ordinary one, so it adds nothing to that item.
* **NOTHING AT `r ≤ 1`**, where the graph is edgeless or empty and the two values collide with the
  third.
* **NOTHING FOR THE ORDINARY LAPLACIAN HERE EITHER**, for the reason the previous unit gives: its
  polynomial in this estate lives on the sigma type.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0`
  and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `2 ≤ r` on the polynomial and the eigenvalue
set, `3 ≤ r` on the non-simplicity, and none at all on the `r = 2` instance, which is a closed
statement about one graph. **No mass, no propagator, and no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace MultipartiteSignlessSingleton

open Matrix Polynomial SimpleGraph LaplacianSignless
open MultipartiteSpectrum MultipartiteEigenspace MultipartiteMultiplicity
open UnbalancedMultipartiteSecularEquation

variable {r : ℕ}

/-! ## 1. At parts of one vertex the third eigenvalue drops out -/

theorem finrank_part_singleton (hr : 2 ≤ r) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (completeEquipartiteGraph r 1))
      - (((r : ℝ) - 1) * (1 : ℕ)) • LinearMap.id)) = 0 := by
  rw [eigenspace_signlessLap_multi_eq hr, finrank_ker_partForm (le_refl 1)]
  omega

theorem top_ne_mid_singleton (hr : 2 ≤ r) :
    2 * ((r : ℝ) - 1) * ((1 : ℕ) : ℝ) ≠ ((r : ℝ) - 2) * ((1 : ℕ) : ℝ) := by
  have h1 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  intro h; norm_num at h; linarith

/-! ## 2. So the eigenvalue set has two elements, not three -/

theorem image_eigenvalues_signlessLap_singleton (hr : 2 ≤ r) :
    Finset.univ.image (LaplacianSignlessDefinite.signlessLap_isHermitian
        (completeEquipartiteGraph r 1)).eigenvalues
      = {2 * ((r : ℝ) - 1) * ((1 : ℕ) : ℝ), ((r : ℝ) - 2) * ((1 : ℕ) : ℝ)} := by
  ext μ
  rw [HermitianCharpoly.mem_image_eigenvalues_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx0, hx⟩
    rcases eigenvalue_signlessLap_multi hx0 hx with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hpos : 0 < Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (signlessLap (completeEquipartiteGraph r 1))
            - (((r : ℝ) - 1) * (1 : ℕ)) • LinearMap.id)) := by
        rw [← isEigenvector_iff_finrank_pos]
        exact ⟨x, hx0, by rw [← h]; exact hx⟩
      rw [finrank_part_singleton hr] at hpos
      exact lt_irrefl 0 hpos
  · rintro (rfl | rfl)
    · rw [isEigenvector_iff_finrank_pos,
        finrank_eigenspace_signlessLap_multi_top hr (le_refl 1)]
      norm_num
    · rw [isEigenvector_iff_finrank_pos,
        finrank_eigenspace_signlessLap_multi_mid (by omega) (le_refl 1)]
      omega

/-! ## 3. The characteristic polynomial, with two factors -/

/-- **`Q`'S CHARACTERISTIC POLYNOMIAL AT PARTS OF ONE VERTEX**, where the previous unit's
three-factor product degenerates to two. -/
theorem charpoly_signlessLap_singleton (hr : 2 ≤ r) :
    (signlessLap (completeEquipartiteGraph r 1)).charpoly
      = (X - C (2 * ((r : ℝ) - 1) * ((1 : ℕ) : ℝ)))
        * (X - C (((r : ℝ) - 2) * ((1 : ℕ) : ℝ))) ^ (r - 1) := by
  have hA := LaplacianSignlessDefinite.signlessLap_isHermitian (completeEquipartiteGraph r 1)
  have hne : 2 * ((r : ℝ) - 1) * ((1 : ℕ) : ℝ)
      ∉ ({((r : ℝ) - 2) * ((1 : ℕ) : ℝ)} : Finset ℝ) := by
    simp only [Finset.mem_singleton]
    exact top_ne_mid_singleton hr
  rw [HermitianCharpoly.charpoly_eq_prod_pow_finrank hA,
    image_eigenvalues_signlessLap_singleton hr, Finset.prod_insert hne, Finset.prod_singleton,
    finrank_eigenspace_signlessLap_multi_top hr (le_refl 1),
    finrank_eigenspace_signlessLap_multi_mid (by omega) (le_refl 1)]
  ring

/-! ## 4. And at two parts of one vertex the signless spectrum is simple -/

/-- **THE FIRST GRAPH THIS CHAIN PUTS THROUGH THE CRITERION ON THE SATISFYING SIDE.** -/
theorem nodup_roots_charpoly_signlessLap_edge :
    (signlessLap (completeEquipartiteGraph 2 1)).charpoly.roots.Nodup := by
  rw [SimpleSpectrumCharpoly.nodup_roots_charpoly_signlessLap_iff]
  intro μ
  by_cases hpos : 0 < Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (signlessLap (completeEquipartiteGraph 2 1)) - μ • LinearMap.id))
  · obtain ⟨x, hx0, hx⟩ := (isEigenvector_iff_finrank_pos _ μ).mpr hpos
    rcases eigenvalue_signlessLap_multi hx0 hx with h | h | h
    · subst h
      rw [finrank_eigenspace_signlessLap_multi_top (le_refl 2) (le_refl 1)]
    · subst h
      rw [finrank_eigenspace_signlessLap_multi_mid (by omega) (le_refl 1)]
    · subst h
      rw [finrank_part_singleton (le_refl 2)]
      omega
  · omega

/-- **AND AT THREE PARTS OR MORE IT IS NOT**, so at parts of one vertex the signless spectrum is
simple exactly when there are two of them. -/
theorem not_nodup_roots_charpoly_signlessLap_singleton (hr : 3 ≤ r) :
    ¬ (signlessLap (completeEquipartiteGraph r 1)).charpoly.roots.Nodup := by
  rw [SimpleSpectrumCharpoly.nodup_roots_charpoly_signlessLap_iff]
  intro h
  have hle := h (((r : ℝ) - 2) * ((1 : ℕ) : ℝ))
  rw [finrank_eigenspace_signlessLap_multi_mid (by omega) (le_refl 1)] at hle
  omega

end MultipartiteSignlessSingleton
