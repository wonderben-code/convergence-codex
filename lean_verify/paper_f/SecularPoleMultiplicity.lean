import SecularRootExact

/-!
# `Q`'s multiplicity at a pole, exactly

**THE PREVIOUS UNIT NAMED THIS GAP AND IT TURNS OUT TO BE ONE INCLUSION.** Entry 169 ended by
pointing out that an eigenvalue of `Q` which is itself a **pole** of the secular sum is counted by
nothing in this chain — with `K_r` as the concrete case, where `N − 2` is an eigenvalue of
multiplicity `r − 1`. Entry 156 had already bounded that multiplicity above; **what was missing was
the reverse inclusion, and it is three lines.**

## What is proved

**`inf_le_ker_secularMap`** — a vector supported on the half-sized parts with vanishing total **is**
in the secular kernel: at a half-sized part the diagonal coefficient is zero, off them the
coordinate is zero, and the total's contribution vanishes. Entry 156 proved the other inclusion and
did not need this one.

**`ker_secularMap_eq_inf`, `finrank_ker_secularMap_eq_half`** — so the secular kernel at a pole is
**exactly** that space, of dimension `|T| − 1` where `T` is the set of half-sized parts. Entry 156's
`≤` is an `=`.

**`finrank_signless_size_eq_half`** — hence **`Q`'s multiplicity at `N − n`, when some part has half
that size, is exactly `kₙ(n − 1) + |T| − 1`.** Together with entry 157's criterion off the poles,
every part value's multiplicity is now an equality rather than a bound.

**`diamond_agrees`** — and the formula reproduces the one multiplicity this chain computed by a
different route: at `K₄` minus an edge it gives `1·1 + (2 − 1) = 2`, which is
`UnbalancedMultipartiteSecular.finrank_signless_eigenspace_diamond`.

## What is NOT here

* **`n = N` IS STILL EXCLUDED, AND AT TWO PARTS THAT BITES.** The statement inherits `n ≠ N` from
  the split it rests on, and `n = 2nᵢ₀` reaches `N` exactly when the graph has two parts of equal
  size — `K_{t,t}`. So the complete bipartite graph on equal parts is **not** covered, which is
  worth naming because it is the smallest family anyone would test. Not attempted
  (`ERRATUM 246`).

⚠ **CLOSED 2026-09-12 (entry 171), AND THE PARAGRAPH IS KEPT AS WRITTEN** (`ERRATUM 94`).
`SecularPoleNotPartValue` covers `n = N`, and **neither exclusion was needed**: `n = 0` is vacuous
under nonemptiness (`ne_zero_of_pole`), and at `n = N` the side condition that replaces the split
holds automatically (`card_ne_of_eq_card_sigma`), so `finrank_signless_kernel_half_part` gives the
multiplicity of `0` as `|T| − 1` with nothing added. `finrank_signless_balanced_two_zero` is
`K_{t,t}`, and `balanced_two_agrees` checks it against
`LaplacianSignlessKernel.card_bipartiteComponent_eq_finrank_ker`, **which already held that value
by another route** — so the estimate above was right that the family was uncovered here and wrong
to suggest the number was unknown. **This paragraph's other two fences stand**: the three counts
are still not added, and there are still no root values.

* **THE THREE COUNTS ARE STILL NOT ADDED.** Entry 169's gap was in two halves and only one closes
  here: the multiplicity at a pole is now known, but **no statement anywhere combines the part
  values, the secular roots and the poles into a count of `Q`'s spectrum**, and nothing rules out a
  part value coinciding with a secular root.

⚠ **NARROWED, NOT CLOSED, 2026-09-12 (entry 174), AND THE PARAGRAPH IS KEPT AS WRITTEN**
(`ERRATUM 94`). `SignlessSpectrumTrichotomy.eigenvalue_trichotomy` supplies what the addition was
missing — **there is nothing else**: every eigenvalue of `Q` is a part value, a pole, or a secular
root, which entry 157's criterion says as a contrapositive and nobody had read that way. With it,
`exists_spectrum_bracket` puts the number of **distinct** eigenvalues between `s` and `3s` for `s`
the number of distinct part sizes, and `pole_isEigen_iff` makes the pole family decidable — a pole
off the part values is an eigenvalue exactly when two parts have half its `n`. **Entry 174 does
not write the exact count**, and the factor of three is real: at `K_{1,3,3}` one part value **is** a
secular root (`SecularRootAtPartValue.part_value_eq_secular_root`) and the other **is not**
(`SignlessSpectrumTrichotomy.secularSum_part133_six_ne`), so the overlap is neither absent nor
uniform, and nothing characterises when it occurs. So this paragraph is narrowed to a bracket, not
answered.

⚠ **CLOSED 2026-09-12 (entry 173), AND THE PARAGRAPH IS KEPT AS WRITTEN** (`ERRATUM 94`).
`SecularRootAtPartValue.part_value_eq_secular_root` settles it the other way: **nothing rules the
coincidence out because it happens.** At `K_{1,3,3}` the part value `N − 3 = 4` satisfies the
secular equation, and `finrank_signless_part133_four` computes the multiplicity there as
`k₃(3 − 1) + 1 = 5` — the first use anywhere in the estate of
`UnbalancedMultipartiteSecularEquation.finrank_signless_size_secular_one`, whose `+ 1` **is** the
overlap. So the sentence above was right that no unit had ruled it out, and the reason was not that
nobody had checked: a count of `Q`'s spectrum must be inclusion–exclusion, not addition.
* **NO ROOT VALUES**, as everywhere in this chain.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0`
  and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances; a witness `i₀` with `2nᵢ₀ = n`, which is what makes `N − n` a pole; `∀ i, Nonempty (V i)`
where entry 156's dimension count needs it; `n ≠ 0` and `n ≠ N` on the multiplicity. **No mass, no
propagator, and no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SecularPoleMultiplicity

open Matrix Finset SimpleGraph LaplacianSignless
open UnbalancedMultipartite UnbalancedMultipartiteFibre UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. The inclusion the previous bound did not need -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem inf_le_ker_secularMap {n : ℕ} :
    LinearMap.ker (offValues (V := V) n) ⊓ LinearMap.ker (totalForm (ι := ι))
      ≤ LinearMap.ker (secularMap (V := V) ((Fintype.card (Σ i, V i) : ℝ) - n)) := by
  intro P hP
  rw [Submodule.mem_inf, mem_ker_offValues_iff, LinearMap.mem_ker] at hP
  obtain ⟨hsupp, htot⟩ := hP
  have hS : ∑ j, P j = 0 := by
    rwa [totalForm_apply] at htot
  rw [mem_ker_secularMap_iff]
  intro i
  rw [hS, mul_zero, add_zero]
  by_cases hi : 2 * Fintype.card (V i) = n
  · have hc : ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)
        - ((Fintype.card (Σ i, V i) : ℝ) - n)) = 0 := by
      have : (2 : ℝ) * Fintype.card (V i) = n := by exact_mod_cast hi
      linarith
    rw [hc, zero_mul]
  · rw [hsupp i hi, mul_zero]

/-! ## 2. So the secular kernel at a pole is exactly `|T| − 1` -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem ker_secularMap_eq_inf {n : ℕ} (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (h0 : 2 * Fintype.card (V i₀) = n) :
    LinearMap.ker (secularMap (V := V) ((Fintype.card (Σ i, V i) : ℝ) - n))
      = LinearMap.ker (offValues (V := V) n) ⊓ LinearMap.ker (totalForm (ι := ι)) :=
  le_antisymm (ker_secularMap_le_inf hne i₀ h0) inf_le_ker_secularMap

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **THE SECULAR KERNEL AT A POLE, EXACTLY** — the previous bound's `≤` is an `=`. -/
theorem finrank_ker_secularMap_eq_half {n : ℕ} (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (h0 : 2 * Fintype.card (V i₀) = n) :
    Module.finrank ℝ (LinearMap.ker (secularMap (V := V)
        ((Fintype.card (Σ i, V i) : ℝ) - n)))
      = Fintype.card {i : ι // 2 * Fintype.card (V i) = n} - 1 := by
  rw [ker_secularMap_eq_inf hne i₀ h0, finrank_inf_ker_totalForm (V := V) i₀ h0]

/-! ## 3. And so the multiplicity at a pole, exactly -/

/-- **`Q`'S MULTIPLICITY AT A PART VALUE WITH A HALF-SIZED PART, EXACTLY.** -/
theorem finrank_signless_size_eq_half {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n ≠ Fintype.card (Σ i, V i)) (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (h0 : 2 * Fintype.card (V i₀) = n) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
        - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id))
      = Fintype.card {i : ι // Fintype.card (V i) = n} * (n - 1)
        + (Fintype.card {i : ι // 2 * Fintype.card (V i) = n} - 1) := by
  rw [finrank_signless_size_eq hn0 hnN hne, finrank_ker_secularMap_eq_half hne i₀ h0]

/-! ## 4. Checked against the one graph whose multiplicity was computed directly -/

/-- The formula agrees with `UnbalancedMultipartiteSecular.finrank_signless_eigenspace_diamond`. -/
theorem diamond_agrees :
    Fintype.card {i : Fin 3 // Fintype.card (Fin (i.1 / 2 + 1)) = 2} * (2 - 1)
        + (Fintype.card {i : Fin 3 // 2 * Fintype.card (Fin (i.1 / 2 + 1)) = 2} - 1)
      = Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
          (signlessLap (completeMultipartiteGraph (fun i : Fin 3 => Fin (i.1 / 2 + 1))))
        - (2 : ℝ) • LinearMap.id)) := by
  rw [UnbalancedMultipartiteSecular.finrank_signless_eigenspace_diamond]
  decide

end SecularPoleMultiplicity
