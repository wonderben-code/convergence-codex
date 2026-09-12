import SecularPoleNotPartValue

/-!
# `Q`'s kernel on the whole complete multipartite family

**ENTRY 171 REFUSED TWO THINGS AND NAMED THEM; THIS IS BOTH.** It proved the multiplicity of `0`
at a pole to be `|T| − 1` for `T` the parts holding half the vertices, checked that against the
bipartite-component count at `K_{t,t}` and at `K_{1,2}`, and then said plainly what it had not
done: **`|T| ≤ 2` is not proved**, so nothing bounded the kernel across the family, and **the
cross-check is at two parts only** — leaving unchecked the `r ≥ 3` side, *where both routes should
say `0` and a disagreement would be most visible*. Both are done here, and they agree.

## What is proved

**`card_half_le_two`** — **at most two parts can hold half the vertices.** Summing `2nᵢ = N` over
`T` gives `|T| · N = 2∑_{T} nᵢ ≤ 2N`, and `N > 0`. Three lines of arithmetic, and it is the
statement entry 171 said it could see how to prove.

**`card_half_le_one_of_three_parts`** — **and past two parts, at most one.** Two half-sized parts
fill the graph between them, so any third part is empty, which nonemptiness forbids.

**`finrank_signless_kernel_le_one`, `finrank_signless_kernel_zero_of_three_parts`** — so entry
171's formula collapses: with a half-sized part present, `Q`'s kernel is **at most a line** for
every complete multipartite graph with all parts nonempty, and is **zero** as soon as there are
three parts or more.

**`supp_eq_univ`, `card_bipComp_eq_zero_of_three_parts`** — the same two answers from the other
side. A connected graph has one component and it is the whole graph, and at three parts or more the
whole graph is not two-colourable (`UnbalancedMultipartiteSignless.not_colorable_two_unbal`), so no
component is. **This half needs no half-sized part**: it is the component route and does not go
through a pole.

**`finrank_ker_signless_zero_of_three_parts`, `finrank_ker_signless_multi`** — read as a dimension
through `LaplacianSignlessKernel.card_bipartiteComponent_eq_finrank_ker`, that is **the dichotomy
for the family**: with every part nonempty, `Q`'s kernel is a line when there are two parts and
zero when there are more. Entry 171's `finrank_ker_signless_two_parts` supplies the first case.

**`three_parts_agrees`, `diamond_agrees_zero`** — and the cross-check entry 171 left open now
closes on the side it named. Both routes say `0` at three parts or more, **and the hypothesis is
not vacuous**: `K₄` minus an edge has parts of sizes `1, 1, 2` with `2 · 2 = 4` the vertex count,
its kernel was computed by the secular **equation** in `UnbalancedMultipartiteDiamond`, and the
component count agrees. That is the third graph on which these two routes have now been made to
meet, after `K_{t,t}` and the three-vertex path.

## What is NOT here

* **THE DICHOTOMY IS THE COMPONENT ROUTE'S, NOT THE SECULAR CHAIN'S**, and the honest reading of
  §3 is that it is the stronger tool for this one eigenvalue. The secular statements in §2 still
  need a half-sized part; without one, `T` is empty and they say nothing, and
  `UnbalancedMultipartiteSecularEquation.ker_secularMap_eq_bot` would need `secularSum 0 ≠ −1`,
  which is not established. **So §2 and §3 do not cover the same graphs**, and the agreement in §4
  is on their overlap. Not attempted (`ERRATUM 246`).

⚠ **CLOSED 2026-09-12 (entry 181), AND THE PARAGRAPH IS KEPT AS WRITTEN** (`ERRATUM 94`).
`SecularSumZero.secularSum_zero_ne_neg_one` establishes exactly the missing fact, at three or more
nonempty parts with no half-sized part, and `ker_secularMap_zero_eq_bot` is the consequence this
bullet asks for. **The proof is graph theory, not arithmetic**: the component count gives `Q`'s
kernel as zero, the identification off the part values makes that the secular kernel, and a
nontrivial secular kernel is what `secularSum 0 = −1` would force. `K_{1,3}`, where the sum **is**
`−1`, shows the three-parts hypothesis is doing the work.
* **NOTHING HERE IS ABOUT ANY EIGENVALUE BUT `0`.** What the secular chain has that the component
  count does not is every other eigenvalue, and this file adds nothing there.
* **THE THREE COUNTS ARE STILL NOT ADDED**, as at entries 169, 170 and 171: no statement anywhere
  combines the part values, the secular roots and the poles into a count of `Q`'s spectrum, and
  nothing rules out a part value coinciding with a secular root.

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
instances; `∀ i, Nonempty (V i)` on everything, which is what makes an empty part impossible and is
the whole content of §1's second half; `3 ≤ Fintype.card ι` where the answer is `0`;
`2 ≤ Fintype.card ι` on the dichotomy; and a witness `i₀` with `2nᵢ₀ = N` on the two statements
that go through a pole, and on neither of the component ones. **No mass, no propagator, and no
metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace MultipartiteSignlessKernel

open Matrix Finset SimpleGraph LaplacianSignless
open UnbalancedMultipartite UnbalancedMultipartiteSecular SecularPoleNotPartValue

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. Two half-sized parts already fill the graph -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **AT MOST TWO PARTS CAN HOLD HALF THE VERTICES.** Summing `2nᵢ = N` over `T` gives
`|T| · N = 2∑_{T} nᵢ ≤ 2N`, and `N > 0`. -/
theorem card_half_le_two (hne : ∀ i, Nonempty (V i)) :
    Fintype.card {i : ι // 2 * Fintype.card (V i) = Fintype.card (Σ i, V i)} ≤ 2 := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Fintype.card_eq_zero]
  · have hN : 0 < Fintype.card (Σ i, V i) :=
      Fintype.card_pos_iff.mpr ⟨⟨Classical.arbitrary ι, (hne _).some⟩⟩
    set T : Finset ι := Finset.univ.filter
      (fun i => 2 * Fintype.card (V i) = Fintype.card (Σ i, V i)) with hT
    have hcard : Fintype.card {i : ι // 2 * Fintype.card (V i) = Fintype.card (Σ i, V i)}
        = T.card := Fintype.card_subtype _
    rw [hcard]
    have h1 : ∑ i ∈ T, Fintype.card (V i) ≤ Fintype.card (Σ i, V i) := by
      rw [Fintype.card_sigma]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have h2 : 2 * ∑ i ∈ T, Fintype.card (V i) = T.card * Fintype.card (Σ i, V i) := by
      rw [Finset.mul_sum,
        Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2), Finset.sum_const,
        smul_eq_mul]
    have h3 : T.card * Fintype.card (Σ i, V i) ≤ 2 * Fintype.card (Σ i, V i) := by omega
    exact Nat.le_of_mul_le_mul_right h3 hN

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **AND AT THREE PARTS OR MORE, AT MOST ONE.** Two of them fill the graph between them, so a
third part is empty, which nonemptiness forbids. -/
theorem card_half_le_one_of_three_parts (hne : ∀ i, Nonempty (V i))
    (h3 : 3 ≤ Fintype.card ι) :
    Fintype.card {i : ι // 2 * Fintype.card (V i) = Fintype.card (Σ i, V i)} ≤ 1 := by
  classical
  by_contra hcon
  rw [not_le, Fintype.card_subtype] at hcon
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcon
  rw [Finset.mem_filter] at hi hj
  obtain ⟨-, hi⟩ := hi
  obtain ⟨-, hj⟩ := hj
  obtain ⟨k, hk⟩ : ∃ k, k ∉ ({i, j} : Finset ι) := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    have hle := Finset.card_le_card (fun x _ => hc x : (Finset.univ : Finset ι) ⊆ {i, j})
    rw [Finset.card_univ, Finset.card_insert_of_notMem (by simp [hij]),
      Finset.card_singleton] at hle
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  obtain ⟨hki, hkj⟩ := hk
  have hpos : 0 < Fintype.card (V k) := Fintype.card_pos_iff.mpr (hne k)
  have hmem : i ∉ ({j, k} : Finset ι) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hij, fun h => hki h.symm⟩
  have htrip : ∑ x ∈ ({i, j, k} : Finset ι), Fintype.card (V x)
      = Fintype.card (V i) + Fintype.card (V j) + Fintype.card (V k) := by
    rw [Finset.sum_insert hmem, Finset.sum_pair (Ne.symm hkj)]
    ring
  have hle : ∑ x ∈ ({i, j, k} : Finset ι), Fintype.card (V x) ≤ Fintype.card (Σ i, V i) := by
    rw [Fintype.card_sigma]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [htrip] at hle
  omega

/-! ## 2. So `Q`'s kernel is a line at best, and vanishes past two parts -/

/-- **THE KERNEL IS AT MOST A LINE**, for every complete multipartite graph with a half-sized
part. -/
theorem finrank_signless_kernel_le_one (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (h0 : 2 * Fintype.card (V i₀) = Fintype.card (Σ i, V i)) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph V)) - (0 : ℝ) • LinearMap.id)) ≤ 1 := by
  rw [finrank_signless_kernel_half_part hne i₀ h0]
  have := card_half_le_two (V := V) hne
  omega

/-- **AND IT VANISHES AT THREE PARTS OR MORE.** -/
theorem finrank_signless_kernel_zero_of_three_parts (hne : ∀ i, Nonempty (V i))
    (h3 : 3 ≤ Fintype.card ι) (i₀ : ι)
    (h0 : 2 * Fintype.card (V i₀) = Fintype.card (Σ i, V i)) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph V)) - (0 : ℝ) • LinearMap.id)) = 0 := by
  rw [finrank_signless_kernel_half_part hne i₀ h0]
  have := card_half_le_one_of_three_parts (V := V) hne h3
  omega

/-! ## 3. The same two answers, counted by two-colourable components -/

/-- A connected graph has one component and it is everything. -/
theorem supp_eq_univ {W : Type*} {G : SimpleGraph W} (h : G.Preconnected)
    (C : G.ConnectedComponent) : C.supp = Set.univ :=
  Set.eq_univ_of_forall fun _v => h.subsingleton_connectedComponent.elim _ _

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **NO TWO-COLOURABLE COMPONENT AT THREE PARTS OR MORE**: the single component is the whole
graph, and the whole graph is not two-colourable. -/
theorem card_bipComp_eq_zero_of_three_parts (hne : ∀ i, Nonempty (V i))
    (h3 : 3 ≤ Fintype.card ι) :
    Fintype.card (LaplacianSignlessKernel.BipComp (completeMultipartiteGraph V)) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun C => ?_⟩
  have hconn := UnbalancedMultipartiteTable.connected_multi hne (by omega)
  have hcol := C.2
  rw [supp_eq_univ hconn.preconnected C.1] at hcol
  exact UnbalancedMultipartiteSignless.not_colorable_two_unbal hne h3
    (Colorable.of_hom (SimpleGraph.induceUnivIso _).symm.toEmbedding.toHom hcol)

/-- Read as a dimension. **No half-sized part is needed here** — this is the component route, and
it does not go through a pole. -/
theorem finrank_ker_signless_zero_of_three_parts (hne : ∀ i, Nonempty (V i))
    (h3 : 3 ≤ Fintype.card ι) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
      (signlessLap (completeMultipartiteGraph V)))) = 0 := by
  rw [← LaplacianSignlessKernel.card_bipartiteComponent_eq_finrank_ker,
    card_bipComp_eq_zero_of_three_parts hne h3]

/-- **THE DICHOTOMY FOR THE WHOLE FAMILY**: with every part nonempty, `Q`'s kernel is a line when
there are two parts and is zero when there are more. Entry 171's `finrank_ker_signless_two_parts`
is the first case and the section above is the second. -/
theorem finrank_ker_signless_multi (hne : ∀ i, Nonempty (V i)) (h2 : 2 ≤ Fintype.card ι) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph V))))
      = if Fintype.card ι = 2 then 1 else 0 := by
  by_cases h : Fintype.card ι = 2
  · rw [if_pos h, finrank_ker_signless_two_parts hne h]
  · rw [if_neg h, finrank_ker_signless_zero_of_three_parts hne (by omega)]

/-! ## 4. The two routes agree past two parts, and at the one graph already computed -/

/-- **THE `r ≥ 3` HALF OF THE CROSS-CHECK**, which entry 171 named as the case where a
disagreement would be most visible. Both routes say `0`. -/
theorem three_parts_agrees (hne : ∀ i, Nonempty (V i)) (h3 : 3 ≤ Fintype.card ι) (i₀ : ι)
    (h0 : 2 * Fintype.card (V i₀) = Fintype.card (Σ i, V i)) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph V)) - (0 : ℝ) • LinearMap.id))
      = Fintype.card (LaplacianSignlessKernel.BipComp (completeMultipartiteGraph V)) := by
  rw [finrank_signless_kernel_zero_of_three_parts hne h3 i₀ h0,
    card_bipComp_eq_zero_of_three_parts hne h3]

/-- **AND THE HYPOTHESIS IS NOT VACUOUS**: `K₄` minus an edge has three parts, of sizes `1, 1, 2`,
and `2 · 2 = 4` is the vertex count. Its kernel was computed by the secular equation in
`UnbalancedMultipartiteDiamond`; the component count agrees. -/
theorem diamond_agrees_zero :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph UnbalancedMultipartiteDiamond.DiamondPart))
      - (0 : ℝ) • LinearMap.id))
      = Fintype.card (LaplacianSignlessKernel.BipComp
          (completeMultipartiteGraph UnbalancedMultipartiteDiamond.DiamondPart)) := by
  rw [UnbalancedMultipartiteDiamond.finrank_signless_diamond_zero,
    card_bipComp_eq_zero_of_three_parts (fun _ => ⟨⟨0, Nat.succ_pos _⟩⟩) (by simp)]

end MultipartiteSignlessKernel
