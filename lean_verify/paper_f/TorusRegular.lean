import RegularBipartiteSharp
import RegularSelfEmbedding

/-!
# The degree bound is exactly right on the periodic lattice, in every dimension

`RegularBipartiteSharp` proved that a `Δ`-regular graph carrying a `±1` labelling that flips across
every edge has `massive ≼ c·1` **iff** `2Δ + m² ≤ c`. The periodic lattice is two-colourable at
even side length in every dimension (`TorusBipartite.torusGraph_colorable_two`) and is `2d`-regular
at side length at least three (`RegularSelfEmbedding.torusGraph_isRegularOfDegree`), so both
hypotheses hold there and **`massive_torus_le_smul_one_iff`** follows:

```
massive (torusGraph d n) m ≼ c·1   ↔   4d + m² ≤ c
```

at every even side length at least four and in every dimension, with
**`le_inv_of_smul_one_le_green_torus`** on the propagator side — the side
`LaplacianDegreeBound`'s withdrawn sentence was about. **So the constant `2Δ + m²` is now known
exact on the family this project's field actually lives on**, and not only on cycles.

## The regularity was already in the estate, and this file first re-proved it

**`ERRATUM 336`.** A first version of this file proved `torusGraph_degree`, `torusGraph_isRegular`,
`stepT_adj`, `stepT_injective` and two `stepT` lemmas from scratch, and `RegularBipartiteSharp`'s
header asserted that the estate had only `TorusDecay.torusGraph_degree_le`, an inequality.
**All six already existed** — in `TorusEmbeddingAllDims`, with `RegularSelfEmbedding` packaging the
regularity as `IsRegularOfDegree` — and three of them under the **same names**. The duplicates are
gone from this file, the false sentence is corrected where it stands, and the erratum records the
cause: a probe truncated by `head -6` was read as an exhaustive one.

## What is proved

* `nonempty_site` — the site type is inhabited once the side length is positive;
* **`massive_torus_le_smul_one_iff`** — the sharpness, in every dimension;
* **`le_inv_of_smul_one_le_green_torus`** — and the propagator's lower bound cannot be raised.

**AND THE SAME DICHOTOMY IS IN THE OPERATOR NORM SINCE 2026-09-03**:
`TorusNormSharp.norm_massive_torus_eq_iff_even` gives `‖massive (torusGraph d n) m‖ = 4d + m²`
**iff** `n` is even, at `0 < d` and `3 ≤ n`, and `norm_lapMatrix_torus_eq_iff_even` says the same
at `m = 0`. It is a currency and not a strengthening — the even half is this file's theorem and
the odd half is `LaplacianSharpEquality`'s — and it is named here so a reader of this file
arrives at it.

## What this is NOT

**The box is not the torus and is not reached.** `boxGraph` has a boundary, is **not** regular, and
is not two-colourable-and-regular; only `RegularBipartiteSharp`'s averaged statement would apply to
it, and that is not instantiated here.

**Even side length is a hypothesis, not a convenience.** It is where the two-colouring comes from
(`TorusBipartite.torusGraph_colorable_two` assumes it), and at odd side length the periodic lattice
is not two-colourable — `CycleSpectralBound` proves the `d = 1` case of exactly that failure, and
**nothing here says whether the bound is attained at odd side length in higher dimensions.**

> **^ BOTH HALVES OF THAT SENTENCE ARE NOW THEOREMS, 2026-08-29.** The non-colourability was
> asserted here and proved nowhere; `LaplacianSharpEquality.torus_not_colorable_two_of_odd` proves
> it in every dimension, by embedding `cycleGraph n` in `torusGraph (d+1) n` as a graph
> homomorphism (`axisHom`) and pulling back Mathlib's `chromaticNumber_cycleGraph_of_odd`. And
> `torus_odd_no_attaining_vector` answers what this file said nothing about: **at every odd side
> length at least three, in every dimension, no vector attains the bound** — with no spectrum
> computed. The paragraph is kept because it was exact when written (`ERRATUM 94`).

**It is a statement about a matrix, not about a field.** No measure appears; `gaussianField` is not
mentioned; `OS4` does not move and no published tag moves.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusRegular

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection
open scoped MatrixOrder

variable {d n : ℕ}

instance nonempty_site (hn : 1 ≤ n) : Nonempty (Site d n) := ⟨fun _ => ⟨0, by omega⟩⟩

/-- **THE CONSTANT `2Δ + m²` IS EXACTLY RIGHT ON THE PERIODIC LATTICE, IN EVERY DIMENSION.** -/
theorem massive_torus_le_smul_one_iff (hn : 3 ≤ n) (hev : Even n) (m c : ℝ) :
    massive (torusGraph d n) m ≤ c • (1 : Matrix (Site d n) (Site d n) ℝ)
      ↔ 4 * (d : ℝ) + m ^ 2 ≤ c := by
  classical
  obtain ⟨σ, hσ⟩ := RegularBipartiteSharp.exists_signColouring_of_colorable
    (TorusBipartite.torusGraph_colorable_two (d := d) hev)
  haveI : Nonempty (Site d n) := nonempty_site (by omega)
  have h := RegularBipartiteSharp.massive_le_smul_one_iff_of_regular (torusGraph d n)
    (RegularSelfEmbedding.torusGraph_isRegularOfDegree hn) hσ m c
  rw [h]
  push_cast
  constructor <;> intro hc <;> linarith

/-- **AND THE PROPAGATOR'S LOWER BOUND CANNOT BE RAISED THERE**, which is the side of the
statement `LaplacianDegreeBound` is about. -/
theorem le_inv_of_smul_one_le_green_torus (hn : 3 ≤ n) (hev : Even n) {m : ℝ} (hm : m ≠ 0)
    {c : ℝ} (hc : 0 < c)
    (h : c • (1 : Matrix (Site d n) (Site d n) ℝ) ≤ green (torusGraph d n) m) :
    c ≤ (4 * (d : ℝ) + m ^ 2)⁻¹ := by
  have hpos : (0 : ℝ) < 4 * (d : ℝ) + m ^ 2 := by positivity
  have hcPD : (c • (1 : Matrix (Site d n) (Site d n) ℝ)).PosDef :=
    (Matrix.PosDef.one).smul hc
  have hinv := MatrixLoewner.posDef_inv_le_inv hcPD h
  have hg : (green (torusGraph d n) m)⁻¹ = massive (torusGraph d n) m := by
    rw [green, Matrix.nonsing_inv_nonsing_inv]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (massive_isUnit _ hm)
  have hd : (c • (1 : Matrix (Site d n) (Site d n) ℝ))⁻¹
      = c⁻¹ • (1 : Matrix (Site d n) (Site d n) ℝ) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ (ne_of_gt hc), one_smul]
  rw [hg, hd] at hinv
  have hkey := (massive_torus_le_smul_one_iff hn hev m c⁻¹).mp hinv
  have h2 : c * (4 * (d : ℝ) + m ^ 2) ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hkey (le_of_lt hc)
    rwa [mul_inv_cancel₀ (ne_of_gt hc)] at hmul
  calc c = (c * (4 * (d : ℝ) + m ^ 2)) * (4 * (d : ℝ) + m ^ 2)⁻¹ := by
        field_simp
    _ ≤ 1 * (4 * (d : ℝ) + m ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right h2 (le_of_lt (inv_pos.mpr hpos))
    _ = (4 * (d : ℝ) + m ^ 2)⁻¹ := one_mul _

end TorusRegular
