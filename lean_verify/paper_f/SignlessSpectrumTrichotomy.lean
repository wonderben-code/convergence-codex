import SecularRootAtPartValue

/-!
# Every eigenvalue of `Q` is a part value, a pole, or a secular root

**FIVE ENTRIES HAVE WRITTEN THAT NO STATEMENT ANYWHERE COUNTS `Q`'s SPECTRUM.** Entries 169 to 173
each end by saying that the part values, the secular roots and the poles are three counts nobody
has added. **The obstacle was never the addition.** What was missing is the statement that there is
nothing else — and entry 157 had already proved the `iff` that gives it, stated *off* the part
values and the poles, which read as a contrapositive says exactly that. That reading had not been
taken, and taking it is one `by_cases` on each side.

## What is proved

**`eigenvalue_trichotomy`** — **every eigenvalue of `Q` on a complete multipartite graph is a part
value `N − nᵢ`, a pole `N − 2nᵢ`, or a root of the secular equation.** If it is neither of the
first two, entry 157's criterion applies at it and says it is the third.

**`partValues`, `card_partValues_eq_card_sizes`** — the part values as a `Finset`, mirroring
`SecularRootCount.poles`, and there are exactly `s` of them for `s` the number of distinct part
sizes, `n ↦ N − n` being injective. That is the same count the poles have.

**`pole_isEigen_iff`** — **and one of the three families becomes a decidable criterion.** A pole
that is not a part value is an eigenvalue **exactly when at least two parts have half its `n`**,
which is entry 171's multiplicity `|T| − 1` being positive. The pole family is no longer a list of
candidates.

**`exists_spectrum_cover`, `exists_spectrum_bracket`** — so the eigenvalues lie in an explicit
finite set of size at most `3s`, and with entry 168's secular roots — one above each pole, so at
least `s` of them, all eigenvalues — **the number of distinct eigenvalues of `Q` is between `s` and
`3s`.** That is the first statement in this chain that counts anything about the spectrum rather
than one eigenvalue at a time.

## What is NOT here

* **IT IS A BRACKET AND NOT A COUNT, AND THE FACTOR OF THREE IS NOT LAZINESS.** The three families
  genuinely overlap — entry 173 exhibits a part value at `K_{1,3,3}` that is also a secular root —
  and they genuinely can be disjoint, and **nothing here says which happens when**. Closing the
  bracket to an equality needs three things: which part values are eigenvalues (entry 157's
  criterion decides it, and is not assembled into a count here), which poles are (`pole_isEigen_iff`
  now decides it, likewise not assembled), and the size of the overlaps (nothing). Not attempted
  (`ERRATUM 246`).
* **`3s` IS NOT CLAIMED TO BE ATTAINED.** No graph is exhibited where the eigenvalues number `3s`,
  and the `K_{1,3,3}` of entry 173 has `s = 2` with three eigenvalues, comfortably inside the
  bracket. Whether the upper bound is ever tight is open.

  ⚠ **CLOSED THE SAME DAY, AND THE PARAGRAPH IS KEPT AS WRITTEN** (`ERRATUM 94`).
  `SignlessBracketAttained`: at `K_{2,2}` — one distinct part size, so `s = 1` and `3s = 3` — the
  part value is `2`, the pole is `0`, and `4` is neither, so it is a secular root; the three
  families are non-empty and disjoint and `bracket_attained` gives `S.card = 3`. **The smallest
  balanced graph is the tight one**, which is why this chain's earlier witnesses missed it: they are
  all unbalanced and all slack. `spectrum_B22` names the spectrum, `{0, 2, 4}`. **What stays open is
  the stronger question**: whether every `s` admits a tight graph.
* **NOTHING HERE IS A MULTIPLICITY.** The bracket counts **distinct** eigenvalues. The
  multiplicities are what entries 156, 157, 170 and 171 compute, and adding them to `N` at a general
  graph is a separate statement that does not appear.
* **NO ROOT VALUES**, as everywhere in this chain — the secular roots are located and counted, never
  evaluated.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0`
  and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances; `∀ i, Nonempty (V i)` throughout; `Nonempty ι` on the two counting statements, which is
where entry 168's root construction needs it; on `pole_isEigen_iff` a witness `i₀` with `2nᵢ₀ = n`
and the hypothesis that `N − n` is not a part value, both inherited from entry 171. **No mass, no
propagator, and no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessSpectrumTrichotomy

open Matrix Finset SimpleGraph LaplacianSignless
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation SecularRootCount SecularRootExact

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. The part values as a finite set, mirroring `SecularRootCount.poles` -/

/-- The part values `N − nᵢ`. -/
noncomputable def partValues (V : ι → Type*) [Fintype ι] [∀ i, Fintype (V i)] : Finset ℝ := by
  classical
  exact Finset.image (fun i : ι => (Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i))
    Finset.univ

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem mem_partValues_iff (x : ℝ) :
    x ∈ partValues V ↔ ∃ i : ι, (Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i) = x := by
  classical
  rw [partValues]; simp

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- There are exactly as many part values as distinct part sizes, `n ↦ N − n` being injective —
the same count `SecularRootCount.card_poles_eq_card_sizes` gives for the poles. -/
theorem card_partValues_eq_card_sizes :
    (partValues V).card = (Finset.univ.image (fun i : ι => Fintype.card (V i))).card := by
  classical
  have hφ : Function.Injective (fun n : ℕ => (Fintype.card (Σ i, V i) : ℝ) - n) := by
    intro a b hab
    simp only at hab
    have : (a : ℝ) = b := by linarith
    exact_mod_cast this
  rw [partValues, ← Finset.card_image_of_injective (Finset.univ.image
    (fun i : ι => Fintype.card (V i))) hφ, Finset.image_image]
  rfl

/-! ## 2. Every eigenvalue is one of the three kinds -/

/-- `μ` is an eigenvalue of `Q`, in the concrete `mulVec` sense this chain uses. -/
def IsEigen (V : ι → Type*) [Fintype ι] [DecidableEq ι] [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)] (μ : ℝ) : Prop :=
  ∃ x : (Σ i, V i) → ℝ, x ≠ 0 ∧ signlessLap (completeMultipartiteGraph V) *ᵥ x = μ • x

/-- **EVERY EIGENVALUE OF `Q` IS A PART VALUE, A POLE, OR A SECULAR ROOT.** Entry 157 proved the
criterion as an `iff` **off** the part values and the poles; read as a contrapositive it says there
is nothing else, and that reading had not been taken. -/
theorem eigenvalue_trichotomy {μ : ℝ} (hne : ∀ i, Nonempty (V i)) (i₀ : ι) (hx : IsEigen V μ) :
    (∃ i, ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) = μ)
      ∨ (∃ i, ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)) = μ)
      ∨ secularSum (V := V) μ = -1 := by
  classical
  by_cases hval : ∃ i, ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) = μ
  · exact Or.inl hval
  by_cases hpole : ∃ i, ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)) = μ
  · exact Or.inr (Or.inl hpole)
  refine Or.inr (Or.inr ?_)
  rw [← isEigenvalue_signless_iff_secular hne i₀ (by simpa using not_exists.mp hval) ?_]
  · exact hx
  · intro i h
    exact (not_exists.mp hpole) i (by linarith)

/-! ## 3. Which poles count -/

/-- **ONE OF THE THREE FAMILIES BECOMES A DECIDABLE CRITERION.** A pole that is not a part value is
an eigenvalue **exactly when at least two parts have half its `n`** — immediate from entry 171's
multiplicity `|T| − 1`, which is positive precisely then. -/
theorem pole_isEigen_iff {n : ℕ} (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (h0 : 2 * Fintype.card (V i₀) = n)
    (hval : ∀ i : ι, ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i))
      ≠ (Fintype.card (Σ i, V i) : ℝ) - n) :
    IsEigen V ((Fintype.card (Σ i, V i) : ℝ) - n)
      ↔ 2 ≤ Fintype.card {i : ι // 2 * Fintype.card (V i) = n} := by
  rw [IsEigen, isEigenvector_iff_finrank_pos,
    SecularPoleNotPartValue.finrank_signless_at_pole_off_part_values hne i₀ h0 hval]
  omega

/-! ## 4. The cover, and the bracket it gives -/

/-- **EVERY EIGENVALUE LIES IN AN EXPLICIT FINITE SET OF SIZE AT MOST `3s`**, with `s` the number
of distinct part sizes. -/
theorem exists_spectrum_cover (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) :
    ∃ S : Finset ℝ,
      S.card ≤ 3 * (Finset.univ.image (fun i : ι => Fintype.card (V i))).card
        ∧ ∀ μ : ℝ, IsEigen V μ → μ ∈ S := by
  classical
  obtain ⟨R, hRcard, hR⟩ := exists_roots_finset_exact (V := V) hne hι
  refine ⟨partValues V ∪ poles V ∪ R, ?_, ?_⟩
  · have h1 := Finset.card_union_le (partValues V ∪ poles V) R
    have h2 := Finset.card_union_le (partValues V) (poles V)
    rw [card_partValues_eq_card_sizes] at h2
    rw [card_poles_eq_card_sizes] at h2
    omega
  · rintro μ ⟨x, hx0, hxe⟩
    rcases eigenvalue_trichotomy hne (Classical.choice hι) ⟨x, hx0, hxe⟩ with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((mem_partValues_iff _).mpr h))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((mem_poles_iff _).mpr h))
    · by_cases hd : ∀ k : ι,
          ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) - μ) ≠ 0
      · exact Finset.mem_union_right _ ((hR μ).mpr ⟨h, hd⟩)
      · obtain ⟨k, hk⟩ := not_forall.mp hd
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          ((mem_poles_iff _).mpr ⟨k, by linarith [not_not.mp hk]⟩))

/-- **THE BRACKET.** `Q` has at least `s` and at most `3s` distinct eigenvalues, `s` the number of
distinct part sizes. The lower bound is entry 168's secular roots, one above each pole; the upper
is the trichotomy. -/
theorem exists_spectrum_bracket (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen V μ)
      ∧ (Finset.univ.image (fun i : ι => Fintype.card (V i))).card ≤ S.card
      ∧ S.card ≤ 3 * (Finset.univ.image (fun i : ι => Fintype.card (V i))).card := by
  classical
  obtain ⟨C, hCcard, hC⟩ := exists_spectrum_cover (V := V) hne hι
  obtain ⟨R, hRcard, hR⟩ := exists_eigenvalues_finset_exact (V := V) hne hι
  refine ⟨C.filter (fun μ => IsEigen V μ), fun μ => ?_, ?_, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hC μ h, h⟩⟩
  · rw [← hRcard]
    refine Finset.card_le_card (fun μ hμ => ?_)
    have he : IsEigen V μ := hR μ hμ
    exact Finset.mem_filter.mpr ⟨hC μ he, he⟩
  · exact le_trans (Finset.card_filter_le _ _) hCcard

/-! ## 5. The overlap is real and it is not uniform -/

open SecularRootAtPartValue in
/-- **AND AT THE SAME GRAPH THE OTHER PART VALUE IS NOT A SECULAR ROOT.** Entry 173 showed
`N − 3 = 4` satisfies the secular equation at `K_{1,3,3}`; here `N − 1 = 6` gives
`1/(5 − 6) + 3/(1 − 6) + 3/(1 − 6) = −11/5`. So one part value of one graph is a secular root and
the other is not, and **nothing about the overlap is uniform** — which is why the count above is a
bracket. -/
theorem secularSum_part133_six_ne : secularSum (V := Part133) 6 ≠ -1 := by
  unfold secularSum
  rw [Fin.sum_univ_three, card_part133]
  norm_num

end SignlessSpectrumTrichotomy
