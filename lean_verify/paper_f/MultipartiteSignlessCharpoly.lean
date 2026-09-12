import SimpleSpectrumCharpoly

/-!
# The signless Laplacian's characteristic polynomial on the equipartite family

**A FENCE WHOSE STATED REASON WAS RETRACTED AND WHOSE ABSENCE WAS NOT.** `MultipartiteMultiplicity`
computed all three of `Q`'s multiplicities on `completeEquipartiteGraph r t` — `1` at `2(r−1)t`,
`r − 1` at `(r−2)t`, `rt − r` at `(r−1)t` — and proved they add to `rt`, then fenced with *no
characteristic polynomial: that step needs diagonalisability and these arguments avoid it.* The
reason is annotated in that file as false (`ERRATUM 508`) and the polynomial still was not there.
**It is here**, and the only new work is the eigenvalue **set**: everything else is that file's
three numbers fed to `HermitianCharpoly.charpoly_eq_prod_pow_finrank`.

**AND IT IS A FAMILY, NOT A GRAPH.** For `r ≥ 3` the equipartite graph is **not two-colourable**
(`MultipartiteSpectrum.not_colorable_two_multi`), so this is an infinite family of non-bipartite
graphs with a complete signless characteristic polynomial — where the previous units of this chain
reached one graph at a time.

## What is proved

**`top_ne_mid`, `top_ne_part`, `mid_ne_part`** — the three values are distinct once `r ≥ 2` and
`t ≥ 2`, which is what lets the product be written as three factors.

**`image_eigenvalues_signlessLap_multi`** — **the new step**: the image of Mathlib's eigenvalue
enumeration is exactly `{2(r−1)t, (r−2)t, (r−1)t}`. One direction is
`MultipartiteSpectrum.eigenvalue_signlessLap_multi`, which says there is nothing else; the other is
that each of the three eigenspaces is non-trivial, which is that file's own dimension count read
through `UnbalancedMultipartiteSecularEquation.isEigenvector_iff_finrank_pos`.

**`charpoly_signlessLap_multi`** —
`(X − 2(r−1)t)·(X − (r−2)t)^{r−1}·(X − (r−1)t)^{rt−r}`, for `r ≥ 2` and `t ≥ 2`. Checked by hand at
`r = 3, t = 2`: `(X − 8)(X − 2)²(X − 4)³`, the octahedron, whose signless Laplacian is `4I + A` and
whose adjacency spectrum is `4, 0, 0, 0, −2, −2`.

**`rootMultiplicity_signlessLap_multi_top`, `_mid`, `_part`** — and each exponent **is** a root
multiplicity, through the previous unit's general theorem, at the weaker hypotheses those three
dimension counts carry.

**`not_nodup_roots_charpoly_signlessLap_multi`** — **the first graph put through the criterion the
previous unit left uninstantiated**: at `r ≥ 2`, `t ≥ 2` the spectrum is not simple, because
`rt − r ≥ 2`.

## What is NOT here

* **NOTHING FOR THE ORDINARY LAPLACIAN ON THIS FAMILY.** `MultipartiteCharpoly` writes `L`'s
  polynomial for `completeMultipartiteGraph`, on the sigma type; `completeEquipartiteGraph` is a
  product type and **no isomorphism between them is formalised** anywhere in this chain, so that
  result does not transfer here. `L`'s `0` and `rt` eigenspaces are, as `MultipartiteMultiplicity`
  says in its own fence, not written for this graph. Not attempted (`ERRATUM 246`).
* **`t = 1` AND `r = 1` ARE EXCLUDED FROM THE POLYNOMIAL, AND NOT BY OVERSIGHT.** At `t = 1` the
  third exponent `rt − r` is zero and the third value stops being an eigenvalue, so the product has
  two factors and not three; the statement would need a different shape and is not given one. The
  three root-multiplicity statements are proved at the weaker `t ≥ 1`, where they still hold.

⚠ **THE `t = 1` SHAPE IS GIVEN THE NEXT UNIT (2026-09-12, entry 163), AND THE PARAGRAPH IS KEPT AS
WRITTEN** (`ERRATUM 94`). `MultipartiteSignlessSingleton.charpoly_signlessLap_singleton` is the
two-factor product `(X − 2(r−1))·(X − (r−2))^{r−1}` for `r ≥ 2`, with the third value excluded
because its multiplicity is **zero** rather than because it collides. **`r = 1` is still excluded**,
there and here.
* **NO CLAIM THAT THIS POLYNOMIAL IS NEW.** It is classical — `K_{r×t}` is a standard example — and
  what is new is only that it is proved here from the estate's own multiplicities, with no
  spectral theorem beyond Mathlib's diagonalisation of a Hermitian matrix.
* **NO SIMPLE-SPECTRUM CONSEQUENCE BEYOND THE NEGATIVE ONE.** The criterion is instantiated once,
  to say the spectrum is **not** simple. No graph is put through it on the satisfying side, here
  or anywhere.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0`
  and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `2 ≤ r` and `2 ≤ t` on the polynomial and
on the distinctness and non-simplicity statements; `1 ≤ t` with `1 ≤ r` or `2 ≤ r` on the three
root multiplicities, exactly as the dimension counts they quote carry them. **No mass, no
propagator, and no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace MultipartiteSignlessCharpoly

open Matrix Polynomial SimpleGraph LaplacianSignless
open MultipartiteSpectrum MultipartiteEigenspace MultipartiteMultiplicity
open UnbalancedMultipartiteSecularEquation

variable {r t : ℕ}

/-! ## 1. The three values are distinct once there are two parts of two -/

theorem top_ne_mid (hr : 2 ≤ r) (ht : 2 ≤ t) :
    2 * ((r : ℝ) - 1) * t ≠ ((r : ℝ) - 2) * t := by
  have h1 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have h2 : (2 : ℝ) ≤ t := by exact_mod_cast ht
  intro h; nlinarith

theorem top_ne_part (hr : 2 ≤ r) (ht : 2 ≤ t) :
    2 * ((r : ℝ) - 1) * t ≠ ((r : ℝ) - 1) * t := by
  have h1 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have h2 : (2 : ℝ) ≤ t := by exact_mod_cast ht
  intro h; nlinarith

theorem mid_ne_part (ht : 2 ≤ t) :
    ((r : ℝ) - 2) * t ≠ ((r : ℝ) - 1) * t := by
  have h2 : (2 : ℝ) ≤ t := by exact_mod_cast ht
  intro h; nlinarith

/-! ## 2. So the eigenvalue set is exactly those three -/

theorem image_eigenvalues_signlessLap_multi (hr : 2 ≤ r) (ht : 2 ≤ t) :
    Finset.univ.image (LaplacianSignlessDefinite.signlessLap_isHermitian
        (completeEquipartiteGraph r t)).eigenvalues
      = {2 * ((r : ℝ) - 1) * t, ((r : ℝ) - 2) * t, ((r : ℝ) - 1) * t} := by
  ext μ
  rw [HermitianCharpoly.mem_image_eigenvalues_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx0, hx⟩
    exact eigenvalue_signlessLap_multi hx0 hx
  · rintro (rfl | rfl | rfl)
    · rw [isEigenvector_iff_finrank_pos, finrank_eigenspace_signlessLap_multi_top hr (by omega)]
      norm_num
    · rw [isEigenvector_iff_finrank_pos,
        finrank_eigenspace_signlessLap_multi_mid (by omega) (by omega)]
      omega
    · rw [isEigenvector_iff_finrank_pos, eigenspace_signlessLap_multi_eq hr,
        finrank_ker_partForm (by omega)]
      have h1 : r ≤ r * t := Nat.le_mul_of_pos_right r (by omega)
      have h2 : r * 2 ≤ r * t := Nat.mul_le_mul_left r ht
      omega

/-! ## 3. The characteristic polynomial -/

/-- **`Q`'S CHARACTERISTIC POLYNOMIAL ON THE EQUIPARTITE FAMILY.** -/
theorem charpoly_signlessLap_multi (hr : 2 ≤ r) (ht : 2 ≤ t) :
    (signlessLap (completeEquipartiteGraph r t)).charpoly
      = (X - C (2 * ((r : ℝ) - 1) * t))
        * (X - C (((r : ℝ) - 2) * t)) ^ (r - 1)
        * (X - C (((r : ℝ) - 1) * t)) ^ (r * t - r) := by
  have hA := LaplacianSignlessDefinite.signlessLap_isHermitian (completeEquipartiteGraph r t)
  have hne1 : 2 * ((r : ℝ) - 1) * t
      ∉ ({((r : ℝ) - 2) * t, ((r : ℝ) - 1) * t} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact top_ne_mid hr ht h
    · exact top_ne_part hr ht h
  have hne2 : ((r : ℝ) - 2) * t ∉ ({((r : ℝ) - 1) * t} : Finset ℝ) := by
    simp only [Finset.mem_singleton]
    exact mid_ne_part ht
  rw [HermitianCharpoly.charpoly_eq_prod_pow_finrank hA,
    image_eigenvalues_signlessLap_multi hr ht, Finset.prod_insert hne1,
    Finset.prod_insert hne2, Finset.prod_singleton,
    finrank_eigenspace_signlessLap_multi_top hr (by omega),
    finrank_eigenspace_signlessLap_multi_mid (by omega) (by omega),
    eigenspace_signlessLap_multi_eq hr, finrank_ker_partForm (by omega)]
  ring

/-! ## 4. The three root multiplicities, and the spectrum is not simple -/

theorem rootMultiplicity_signlessLap_multi_top (hr : 2 ≤ r) (ht : 1 ≤ t) :
    Polynomial.rootMultiplicity (2 * ((r : ℝ) - 1) * t)
        (signlessLap (completeEquipartiteGraph r t)).charpoly = 1 := by
  rw [HermitianRootMultiplicity.rootMultiplicity_charpoly_signlessLap,
    finrank_eigenspace_signlessLap_multi_top hr ht]

theorem rootMultiplicity_signlessLap_multi_mid (hr : 1 ≤ r) (ht : 1 ≤ t) :
    Polynomial.rootMultiplicity (((r : ℝ) - 2) * t)
        (signlessLap (completeEquipartiteGraph r t)).charpoly = r - 1 := by
  rw [HermitianRootMultiplicity.rootMultiplicity_charpoly_signlessLap,
    finrank_eigenspace_signlessLap_multi_mid hr ht]

theorem rootMultiplicity_signlessLap_multi_part (hr : 2 ≤ r) (ht : 1 ≤ t) :
    Polynomial.rootMultiplicity (((r : ℝ) - 1) * t)
        (signlessLap (completeEquipartiteGraph r t)).charpoly = r * t - r := by
  rw [HermitianRootMultiplicity.rootMultiplicity_charpoly_signlessLap,
    eigenspace_signlessLap_multi_eq hr, finrank_ker_partForm ht]

/-- **AND THE SPECTRUM IS NOT SIMPLE**, put through the previous unit's criterion. -/
theorem not_nodup_roots_charpoly_signlessLap_multi (hr : 2 ≤ r) (ht : 2 ≤ t) :
    ¬ (signlessLap (completeEquipartiteGraph r t)).charpoly.roots.Nodup := by
  rw [SimpleSpectrumCharpoly.nodup_roots_charpoly_signlessLap_iff]
  intro h
  have hle := h (((r : ℝ) - 1) * t)
  rw [eigenspace_signlessLap_multi_eq hr, finrank_ker_partForm (by omega)] at hle
  have h2 : r * 2 ≤ r * t := Nat.mul_le_mul_left r ht
  omega

end MultipartiteSignlessCharpoly
