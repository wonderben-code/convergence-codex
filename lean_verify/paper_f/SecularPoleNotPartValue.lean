import SecularPoleMultiplicity

/-!
# The top pole, and `Q`'s kernel on `K_{t,t}`

**THE PREVIOUS UNIT FENCED ITSELF AGAINST `n = N` AND THE FENCE WAS TOO CAUTIOUS.** Entry 170
recorded that `finrank_signless_size_eq_half` inherits `n ≠ 0` and `n ≠ N` from the split it rests
on, and named what that costs: `K_{t,t}`, "the smallest family anyone would test". **Neither
hypothesis was needed.** The split is what carries them, and there is a route that does not use the
split.

## What is proved

**`finrank_signless_at_pole_off_part_values`** — at a pole `N − n` which is not a part value, `Q`'s
multiplicity is `|T| − 1`, with `T` the parts of size `n/2`. **No `n ≠ 0` and no `n ≠ N`.** This is
**not** a strict generalisation of entry 170's formula: it trades those two hypotheses for `hval`,
that no part has exactly `n` vertices, which is the case `kₙ = 0`. Where both apply they agree,
because entry 170's `kₙ(n − 1)` term vanishes there.

**`ne_zero_of_pole`** — and `n = 0` was never a case. The pole condition `2nᵢ₀ = 0` empties `V i₀`,
which nonemptiness forbids, so that exclusion is **vacuous** rather than open.

**`card_ne_of_eq_card_sigma`, `finrank_signless_kernel_half_part`** — **and at `n = N` the price of
the trade is nothing.** If a part had all `N` vertices then every other part is empty, which
nonemptiness forbids unless there are no others; and with no others the pole condition
`2nᵢ₀ = N = nᵢ₀` empties `V i₀` in turn. So `hval` holds automatically at the top pole, and the
multiplicity of the eigenvalue `0` — which is what `N − n` is when `n = N` — is `|T| − 1` under
nothing but nonemptiness and a half-sized part. **Entry 170's gap is closed, not narrowed.**

**`finrank_signless_balanced_two_zero`** — hence `Q`'s kernel on `K_{t,t}` is a line: both parts are
half-sized, so `|T| = 2`.

**`card_bipComp_two_parts`, `balanced_two_agrees`** — **and that number was already in the estate by
a different route, so the last section checks the two against each other rather than leaving them
to agree.** `LaplacianSignlessKernel.card_bipartiteComponent_eq_finrank_ker` counts `Q`'s kernel by
two-colourable components, for every finite graph; `K_{t,t}` is connected
(`UnbalancedMultipartiteTable.connected_multi`) and two-coloured by `Sigma.fst`
(Mathlib's `completeMultipartiteGraph.coloring`), so that count is `1` as well. **§3 is therefore
not new mathematics** — it is the secular chain arriving at a value the estate already had, and §4
is the arrival being checked. The secular route does not pass through the component count, so the
agreement is evidence and not bookkeeping.

**`finrank_ker_signless_two_parts`, `path_agrees`** — **and the two routes do not have the same
reach**, which the adversarial pass turned up and which is the more useful half of §4. The
component count covers `K_{a,b}` at **every** pair of sizes; §2's route needs a half-sized part, so
at two parts it reaches only `a = b`. That gap is not empty in this chain: the three-vertex path is
`K_{1,2}`, and `UnbalancedMultipartiteSecularEquation.finrank_signless_path_zero` already had its
kernel, by the secular **equation** rather than by a pole. So there is a second agreement to check,
at unequal parts and through a third route, and it holds. **Stated plainly: for the kernel alone
the component count is strictly the stronger tool**, and what the secular chain has that it does
not is every eigenvalue other than `0`.

## What is NOT here

* **`|T| ≤ 2` IS NOT PROVED**, so nothing here bounds `Q`'s kernel across the family. The argument
  is the one already written in `card_ne_of_eq_card_sigma` — two half-sized parts fill `N` between
  them — and it would give kernel dimension `≤ 1` for every complete multipartite graph with all
  parts nonempty, hence `0` at three or more parts. **So the cross-check in §4 is at two parts
  only**, and the `r ≥ 3` side, where both routes should say `0` and a disagreement would be most
  visible, is unchecked. Not attempted (`ERRATUM 246`).

⚠ **CLOSED 2026-09-12 (entry 172), AND THE PARAGRAPH IS KEPT AS WRITTEN** (`ERRATUM 94`).
`MultipartiteSignlessKernel` proves `card_half_le_two` by the arithmetic this bullet describes,
`card_half_le_one_of_three_parts` past two parts, and hence the kernel `≤ 1` everywhere and `0` at
three parts or more; `three_parts_agrees` is the `r ≥ 3` side of the cross-check, and
`diamond_agrees_zero` shows the hypothesis is inhabited at `K₄` minus an edge. **The estimate above
was right about the argument and right that it was short.** The bullet below it still stands: the
statements needing a half-sized part are still silent without one, so the two routes cover
different graphs and the agreement is on their overlap.

* **THE COMPLEMENT OF §2 IS OPEN.** When no part is half-sized `T` is empty and this file says
  nothing at all; `UnbalancedMultipartiteSecularEquation.ker_secularMap_eq_bot` would need
  `secularSum 0 ≠ −1`, which is not established here.

⚠ **CLOSED 2026-09-12 (entry 181), AND THE PARAGRAPH IS KEPT AS WRITTEN** (`ERRATUM 94`).
`SecularSumZero.secularSum_zero_ne_neg_one` establishes exactly the missing fact, at three or more
nonempty parts with no half-sized part, and `ker_secularMap_zero_eq_bot` is the consequence this
bullet asks for. **The proof is graph theory, not arithmetic**: the component count gives `Q`'s
kernel as zero, the identification off the part values makes that the secular kernel, and a
nontrivial secular kernel is what `secularSum 0 = −1` would force. `K_{1,3}`, where the sum **is**
`−1`, shows the three-parts hypothesis is doing the work.
* **THE THREE COUNTS ARE STILL NOT ADDED**, exactly as at entry 170: no statement anywhere combines
  the part values, the secular roots and the poles into a count of `Q`'s spectrum, and nothing
  rules out a part value coinciding with a secular root.

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
instances; `∀ i, Nonempty (V i)` on everything; a witness `i₀` with `2nᵢ₀ = n`, which is what makes
`N − n` a pole at all; `hval` on §1 alone, discharged in §2; `Fintype.card ι = 2` in §4; and `t ≠ 0`
on the two `K_{t,t}` statements. **No mass, no propagator, and no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SecularPoleNotPartValue

open Matrix Finset SimpleGraph LaplacianSignless
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation SecularPoleMultiplicity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. At a pole that is not a part value, the multiplicity is `|T| − 1` -/

/-- **NO `n ≠ 0` AND NO `n ≠ N` HERE**: the split that carries those two hypotheses is not used,
and what replaces it is `hval`, which says no part has exactly `n` vertices. Where entry 170's
formula also applies the two agree, since `hval` makes its `kₙ` factor zero. -/
theorem finrank_signless_at_pole_off_part_values {n : ℕ} (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (h0 : 2 * Fintype.card (V i₀) = n)
    (hval : ∀ i : ι, ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i))
      ≠ (Fintype.card (Σ i, V i) : ℝ) - n) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
        - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id))
      = Fintype.card {i : ι // 2 * Fintype.card (V i) = n} - 1 := by
  rw [finrank_signless_eigenspace_of_ne hne hval, finrank_ker_secularMap_eq_half hne i₀ h0]

/-! ## 2. At `n = N` the side condition is free, so that case closes outright -/

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **AND `n = 0` WAS NEVER A CASE.** The pole condition `2nᵢ₀ = 0` empties `V i₀`, so entry 170's
other exclusion is vacuous rather than open. -/
theorem ne_zero_of_pole (hne : ∀ i, Nonempty (V i)) {n : ℕ} (i₀ : ι)
    (h0 : 2 * Fintype.card (V i₀) = n) : n ≠ 0 := by
  have hpos : 0 < Fintype.card (V i₀) := Fintype.card_pos_iff.mpr (hne i₀)
  omega

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **THE SIDE CONDITION COSTS NOTHING AT THE TOP POLE.** If a part had all `N` vertices then
every other part is empty, which the nonemptiness hypothesis forbids unless there are no others;
and with no others the pole condition `2nᵢ₀ = N = nᵢ₀` empties `V i₀` too. -/
theorem card_ne_of_eq_card_sigma (hne : ∀ i, Nonempty (V i)) {n : ℕ} (i₀ : ι)
    (h0 : 2 * Fintype.card (V i₀) = n) (hN : n = Fintype.card (Σ i, V i)) (i : ι) :
    Fintype.card (V i) ≠ n := by
  classical
  have hpos : 0 < Fintype.card (V i₀) := Fintype.card_pos_iff.mpr (hne i₀)
  intro hcon
  by_cases hii : i = i₀
  · subst hii; omega
  · have hpair : ∑ j ∈ ({i, i₀} : Finset ι), Fintype.card (V j)
        = Fintype.card (V i) + Fintype.card (V i₀) := Finset.sum_pair hii
    have hsum : Fintype.card (V i) + Fintype.card (V i₀) ≤ Fintype.card (Σ i, V i) := by
      rw [Fintype.card_sigma, ← hpair]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    omega

/-- **THE CASE ENTRY 170 HAD TO EXCLUDE, WITH NOTHING ADDED.** At `n = N` the pole `N − n` is the
eigenvalue `0`, and the multiplicity of `0` is `|T| − 1` for `T` the parts of size `N/2`. -/
theorem finrank_signless_kernel_half_part (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (h0 : 2 * Fintype.card (V i₀) = Fintype.card (Σ i, V i)) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph V)) - (0 : ℝ) • LinearMap.id))
      = Fintype.card {i : ι // 2 * Fintype.card (V i) = Fintype.card (Σ i, V i)} - 1 := by
  have h := finrank_signless_at_pole_off_part_values (V := V) (n := Fintype.card (Σ i, V i))
    hne i₀ h0 (fun i => by
      have hn := card_ne_of_eq_card_sigma hne i₀ h0 rfl i
      intro hcon
      exact hn (by exact_mod_cast (by linarith :
        (Fintype.card (V i) : ℝ) = (Fintype.card (Σ i, V i) : ℝ))))
  rw [sub_self] at h
  exact h

/-! ## 3. The smallest case anyone would test: `K_{t,t}` -/

theorem card_balanced_two (t : ℕ) : Fintype.card (Σ _i : Fin 2, Fin t) = 2 * t := by
  simp [Fintype.card_sigma, mul_comm]

/-- **`Q`'s KERNEL ON `K_{t,t}` IS A LINE.** Both parts are half-sized, so `|T| = 2`. -/
theorem finrank_signless_balanced_two_zero {t : ℕ} (ht : t ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph (fun _ : Fin 2 => Fin t)))
      - (0 : ℝ) • LinearMap.id)) = 1 := by
  have h := finrank_signless_kernel_half_part (V := fun _ : Fin 2 => Fin t)
    (fun _ => ⟨⟨0, Nat.pos_of_ne_zero ht⟩⟩) 0 (by simp)
  rw [h]
  have hk : Fintype.card {i : Fin 2 //
      2 * Fintype.card (Fin t) = Fintype.card (Σ _i : Fin 2, Fin t)} = 2 := by
    simp
  rw [hk]

/-! ## 4. The same number, counted a second way: by two-colourable components -/

omit [DecidableEq ι] [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] in
/-- Two parts, so `Sigma.fst` is already a two-colouring. -/
theorem colorable_two_of_card_two (h2 : Fintype.card ι = 2) :
    (completeMultipartiteGraph V).Colorable 2 := by
  have h := SimpleGraph.completeMultipartiteGraph.colorable V
  rwa [h2] at h

omit [DecidableEq ι] [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] in
/-- Restricting that colouring to a component. -/
theorem induce_colorable_two (h2 : Fintype.card ι = 2)
    (C : (completeMultipartiteGraph V).ConnectedComponent) :
    ((completeMultipartiteGraph V).induce C.supp).Colorable 2 :=
  Colorable.of_hom (SimpleGraph.Embedding.induce _).toHom (colorable_two_of_card_two h2)

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **ONE COMPONENT, AND IT IS TWO-COLOURABLE.** -/
theorem card_bipComp_two_parts (hne : ∀ i, Nonempty (V i)) (h2 : Fintype.card ι = 2) :
    Fintype.card (LaplacianSignlessKernel.BipComp (completeMultipartiteGraph V)) = 1 := by
  have hconn := UnbalancedMultipartiteTable.connected_multi hne (by omega)
  have hsub : Subsingleton (completeMultipartiteGraph V).ConnectedComponent :=
    hconn.preconnected.subsingleton_connectedComponent
  obtain ⟨v⟩ := hconn.nonempty
  rw [Fintype.card_eq_one_iff]
  exact ⟨⟨(completeMultipartiteGraph V).connectedComponentMk v, induce_colorable_two h2 _⟩,
    fun y => Subtype.ext (Subsingleton.elim _ _)⟩

/-- The component count, read as a dimension. -/
theorem finrank_ker_signless_two_parts (hne : ∀ i, Nonempty (V i)) (h2 : Fintype.card ι = 2) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
      (signlessLap (completeMultipartiteGraph V)))) = 1 := by
  rw [← LaplacianSignlessKernel.card_bipartiteComponent_eq_finrank_ker,
    card_bipComp_two_parts hne h2]

/-- **THE TWO ROUTES AGREE ON `K_{t,t}`.** -/
theorem balanced_two_agrees {t : ℕ} (ht : t ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph (fun _ : Fin 2 => Fin t)))
      - (0 : ℝ) • LinearMap.id))
      = Fintype.card (LaplacianSignlessKernel.BipComp
          (completeMultipartiteGraph (fun _ : Fin 2 => Fin t))) := by
  rw [finrank_signless_balanced_two_zero ht,
    card_bipComp_two_parts (fun _ => ⟨⟨0, Nat.pos_of_ne_zero ht⟩⟩) (by simp)]

/-- **AND THE TWO ROUTES DO NOT HAVE THE SAME REACH.** `finrank_ker_signless_two_parts` covers
`K_{a,b}` at **every** pair of sizes, while §2's route needs a half-sized part and so reaches only
`a = b`. The gap between them is not empty in the chain: the three-vertex path is `K_{1,2}`, and
`UnbalancedMultipartiteSecularEquation.finrank_signless_path_zero` gets its kernel by the secular
**equation** rather than by a pole. So there is a second agreement to check, at unequal parts. -/
theorem path_agrees :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph (fun i : Fin 2 => Fin (i.1 + 1))))
      - (0 : ℝ) • LinearMap.id))
      = Fintype.card (LaplacianSignlessKernel.BipComp
          (completeMultipartiteGraph (fun i : Fin 2 => Fin (i.1 + 1)))) := by
  rw [UnbalancedMultipartiteSecularEquation.finrank_signless_path_zero,
    card_bipComp_two_parts (fun i => ⟨⟨0, Nat.succ_pos _⟩⟩) (by simp)]

end SecularPoleNotPartValue
