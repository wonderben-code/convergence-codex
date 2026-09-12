import UnbalancedMultipartiteSecularBound

/-!
# The secular equation, as a theorem — and one graph's whole signless spectrum

**THREE UNITS HAVE NOW CALLED THIS A SECULAR EQUATION AND NONE HAD PROVED IT WAS ONE.**
`UnbalancedMultipartiteSignless` wrote `∑ₖ nₖ/(N − 2nₖ − μ) = −1` in prose and fenced it;
`UnbalancedMultipartiteSecular` turned the prose into an `r × r` map and reduced `Q`'s multiplicity
to that map's kernel, exactly; `UnbalancedMultipartiteSecularBound` bounded the kernel above in
both cases. **What none of them proved is that the kernel is non-trivial precisely when the sum
equals `−1`.** That is here, as an `iff`, together with the vector that witnesses it.

## What is proved

**`secularSum μ = ∑ᵢ nᵢ/(N − 2nᵢ − μ)`.** Whenever no denominator vanishes:
**`ker_secularMap_eq_bot`** — if `secularSum μ ≠ −1` the kernel is **trivial**; the proof reads each
row as `Pᵢ = −S·nᵢ/dᵢ`, sums it to `S = −S·secularSum μ`, and cancels.
**`secularVec`, `mem_ker_secularVec`, `secularVec_ne_zero`** — and if `secularSum μ = −1` the
explicit vector `Pᵢ = −nᵢ/dᵢ` **is** in the kernel and is non-zero, because its total is `1` by the
equation itself. **`finrank_ker_secularMap_eq_one`** — with the previous unit's `≤ 1`, the kernel is
then exactly a line.

**`finrank_signless_eigenspace_secular_one/_zero`, `isEigenvalue_signless_iff_secular`** — so off
the part values `Q`'s multiplicity at `μ` is `1` or `0` according to the equation, and **`μ` is an
eigenvalue of `Q` if and only if `∑ᵢ nᵢ/(N − 2nᵢ − μ) = −1`**. **`finrank_signless_size_secular_one`
and `_zero`** — and *at* a part value `N − n` with no part of half that size, the multiplicity is
`kₙ(n − 1) + 1` or `kₙ(n − 1)` by the same equation. **Between them these cover every `μ` at which
no part is half-sized**, which is every `μ` outside a set of at most `r` numbers.

**`isEigenvector_iff_finrank_pos`** — a general bridge, for an arbitrary real square matrix, between
*having a non-zero eigenvector* and *the eigenspace having positive dimension*. It belongs upstream
and is here because this is where it was first needed.

**`secularSum_path`, `secularSum_path_eq_neg_one`, `isEigenvalue_signless_path`,
`finrank_signless_path_add`** — **THE WHOLE SIGNLESS SPECTRUM OF ONE GRAPH, FROM THE GENERAL
THEOREMS.** Parts of sizes `1` and `2` — the three-vertex graph this chain has used since
`UnbalancedMultipartite.path_example_spectrum` — has `secularSum μ = 1/(1 − μ) + 2/(−1 − μ)`, and
that equals `−1` exactly at `μ = 0` and `μ = 3`, a quadratic solved here. The part value `1` is an
eigenvalue with multiplicity one (the previous unit's unique-half-part case); the part value `2`
and the excluded value `−1` are **not** eigenvalues. So `Q`'s eigenvalues are exactly `0`, `1`, `3`,
each **simple**, and the three multiplicities **sum to the vertex count**, which is what makes the
list complete.

## What is NOT here

* **THE EQUATION IS A CRITERION, NOT A SOLUTION.** Deciding `secularSum μ = −1` at a general family
  is finding the roots of a polynomial of degree at most `r`, and nothing here does that in
  general. At the graph of `§8`–`§11` it is a quadratic and is solved; that is one family, not a
  method. Naming the criterion is not a claim that solving it is short (`ERRATUM 194`).

⚠ **THAT CLAUSE IS STILL TRUE AND IS NOT WHAT IT SOUNDS LIKE** (2026-09-12, entry 164;
`ERRATUM 94`'s convention used here for a clarification rather than a correction).
`SecularRootLocation` does **not** solve the equation and does not contradict a word above — and it
still gets a root out of it: above the largest pole every term is negative and increasing, two
explicit values bracket `−1`, and the intermediate value theorem does the rest, so there is exactly
one root there and it is an eigenvalue of `Q`. **The reading this paragraph invites — that nothing
general is available until the polynomial is solved — is the one to avoid.** What remains genuinely
out of reach is the root's *value*, and the count of the roots between consecutive poles.
* **NOTHING NEW AT A HALF-SIZED VALUE.** Every statement here needs `N − 2nᵢ ≠ μ` for every `i`;
  at the at-most-`r` values where that fails, what is known is what the two previous units left:
  `≤ |T| − 1` with the `|T| = 1` equality, and `finrank_ker_secular_diamond`'s exact computation at
  the one concrete graph. Those values are excluded here, not covered.
* **THE GRAPH IN `§8`–`§11` IS TWO-COLOURABLE, SO ITS ANSWER WAS NEVER IN DOUBT** — mathematically
  `Q` and `L` are conjugate there and `path_example_spectrum` already gives `{0, 1, 3}`. **What the
  estate could not do is derive it**: the two-colourability of the two-part family is not
  formalised anywhere here (the chain proves only the *negative*, for three or more parts), so
  `SignlessBipartite` cannot be applied to it. These sections are therefore a **check of the
  machinery against an independently known answer**, and are stated as such rather than as new
  reach.
* **NO CHARACTERISTIC POLYNOMIAL FOR `Q`** on the family, which needs the secular roots in general.
* **NOTHING AT AN EMPTY PART**, and **nothing over `ℂ`**.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and
  `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances; `∀ i, (N − 2nᵢ − μ) ≠ 0` on everything about the equation; an index `i₀` and
`∀ i, Nonempty (V i)` wherever a dimension is claimed to be one rather than at most one;
`∀ i, (N − nᵢ) ≠ μ` off the part values and `n ≠ 0`, `n ≠ N` at one. **No mass, no propagator, and
no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace UnbalancedMultipartiteSecularEquation

open Matrix Finset SimpleGraph LaplacianSignless
open UnbalancedMultipartite UnbalancedMultipartiteFibre UnbalancedMultipartiteTable
open UnbalancedMultipartiteSignless UnbalancedMultipartiteSecular

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. The secular sum -/

noncomputable def secularSum (μ : ℝ) : ℝ :=
  ∑ i, (Fintype.card (V i) : ℝ)
    / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ)

/-! ## 2. If the equation fails the kernel is trivial -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem ker_secularMap_eq_bot {μ : ℝ}
    (hd : ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ) ≠ 0)
    (hsum : secularSum (V := V) μ ≠ -1) :
    LinearMap.ker (secularMap (V := V) μ) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro P hP
  have hrow := (mem_ker_secularMap_iff (V := V) μ P).mp hP
  have hPi : ∀ i, P i
      = -(∑ j, P j) * ((Fintype.card (V i) : ℝ)
        / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ)) := by
    intro i
    have h : -(∑ j, P j) * ((Fintype.card (V i) : ℝ)
          / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ))
        = (-((Fintype.card (V i) : ℝ) * ∑ j, P j))
          / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ) := by
      ring
    rw [h, eq_div_iff (hd i)]
    linear_combination hrow i
  have hcirc : (∑ j, P j) = -(∑ j, P j) * secularSum (V := V) μ := by
    conv_lhs => rw [show (∑ j, P j) = ∑ i, P i from rfl]
    rw [secularSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hPi i
  have hS : ∑ j, P j = 0 := by
    have h : (∑ j, P j) * (1 + secularSum (V := V) μ) = 0 := by linear_combination hcirc
    refine (mul_eq_zero.mp h).resolve_right fun hz => hsum ?_
    linarith
  funext i
  have h := hrow i
  rw [hS, mul_zero, add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (hd i)

/-! ## 3. If the equation holds, an explicit nonzero point of the kernel -/

/-- The vector the secular equation makes an eigenvector: `Pᵢ = −nᵢ/(N − 2nᵢ − μ)`. -/
noncomputable def secularVec (μ : ℝ) : ι → ℝ := fun i =>
  -((Fintype.card (V i) : ℝ)
    / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ))

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem sum_secularVec (μ : ℝ) : ∑ i, secularVec (V := V) μ i = -secularSum (V := V) μ := by
  rw [secularSum, ← Finset.sum_neg_distrib]
  rfl

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem mem_ker_secularVec {μ : ℝ}
    (hd : ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ) ≠ 0)
    (hsum : secularSum (V := V) μ = -1) :
    secularVec (V := V) μ ∈ LinearMap.ker (secularMap (V := V) μ) := by
  rw [mem_ker_secularMap_iff]
  intro i
  rw [sum_secularVec, hsum, neg_neg, mul_one, secularVec]
  have h : ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ)
      * -((Fintype.card (V i) : ℝ)
        / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ))
      = -(Fintype.card (V i) : ℝ) := by
    have hdi := hd i
    field_simp
  rw [h]
  ring

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem secularVec_ne_zero {μ : ℝ} (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (hd : ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ) ≠ 0) :
    secularVec (V := V) μ ≠ 0 := by
  intro h0
  have h := congrFun h0 i₀
  rw [secularVec, Pi.zero_apply, neg_eq_zero, div_eq_zero_iff] at h
  rcases h with h | h
  · exact (Nat.cast_ne_zero.mpr (card_part_ne_zero (V := V) hne i₀)) h
  · exact hd i₀ h

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem ker_secularMap_ne_bot {μ : ℝ} (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (hd : ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ) ≠ 0)
    (hsum : secularSum (V := V) μ = -1) :
    LinearMap.ker (secularMap (V := V) μ) ≠ ⊥ := by
  intro hbot
  have hmem := mem_ker_secularVec (V := V) hd hsum
  rw [hbot, Submodule.mem_bot] at hmem
  exact secularVec_ne_zero hne i₀ hd hmem

/-! ## 4. So the multiplicity, exactly, on both sides of the equation -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem finrank_ker_secularMap_eq_one {μ : ℝ} (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (hd : ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ) ≠ 0)
    (hsum : secularSum (V := V) μ = -1) :
    Module.finrank ℝ (LinearMap.ker (secularMap (V := V) μ)) = 1 := by
  have hle := finrank_ker_secularMap_le_one (V := V) hd
  have hnz : Module.finrank ℝ (LinearMap.ker (secularMap (V := V) μ)) ≠ 0 := by
    rw [Ne, Submodule.finrank_eq_zero]
    exact ker_secularMap_ne_bot hne i₀ hd hsum
  omega

/-! ## 5. The secular equation, as `Q`'s eigenvalue criterion -/

theorem finrank_signless_eigenspace_secular_one {μ : ℝ} (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (hval : ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) ≠ μ)
    (hd : ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ) ≠ 0)
    (hsum : secularSum (V := V) μ = -1) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
        - μ • LinearMap.id)) = 1 := by
  rw [finrank_signless_eigenspace_of_ne hne hval, finrank_ker_secularMap_eq_one hne i₀ hd hsum]

theorem finrank_signless_eigenspace_secular_zero {μ : ℝ} (hne : ∀ i, Nonempty (V i))
    (hval : ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) ≠ μ)
    (hd : ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ) ≠ 0)
    (hsum : secularSum (V := V) μ ≠ -1) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
        - μ • LinearMap.id)) = 0 := by
  rw [finrank_signless_eigenspace_of_ne hne hval, ker_secularMap_eq_bot hd hsum, finrank_bot]

/-- **THE SECULAR EQUATION, AS A THEOREM.** -/
theorem isEigenvalue_signless_iff_secular {μ : ℝ} (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (hval : ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) ≠ μ)
    (hd : ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ) ≠ 0) :
    (∃ x : (Σ i, V i) → ℝ, x ≠ 0
        ∧ signlessLap (completeMultipartiteGraph V) *ᵥ x = μ • x)
      ↔ secularSum (V := V) μ = -1 := by
  rw [isEigenvalue_signless_iff_of_ne hne hval]
  constructor
  · rintro ⟨P, hP0, hP⟩
    by_contra hs
    refine hP0 ?_
    have hmem : P ∈ LinearMap.ker (secularMap (V := V) μ) := LinearMap.mem_ker.mpr hP
    rw [ker_secularMap_eq_bot hd hs, Submodule.mem_bot] at hmem
    exact hmem
  · intro hs
    exact ⟨secularVec (V := V) μ, secularVec_ne_zero hne i₀ hd,
      LinearMap.mem_ker.mp (mem_ker_secularVec hd hs)⟩

/-! ## 6. And at a part value too, when no part is half-sized -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem sub_ne_zero_of_no_half {n : ℕ} (hhalf : ∀ i, 2 * Fintype.card (V i) ≠ n) (i : ι) :
    ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)
      - ((Fintype.card (Σ i, V i) : ℝ) - n)) ≠ 0 := by
  intro hz
  exact hhalf i (by exact_mod_cast (by linarith : (2 : ℝ) * Fintype.card (V i) = n))

theorem finrank_signless_size_secular_one {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n ≠ Fintype.card (Σ i, V i)) (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (hhalf : ∀ i, 2 * Fintype.card (V i) ≠ n)
    (hsum : secularSum (V := V) ((Fintype.card (Σ i, V i) : ℝ) - n) = -1) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
        - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id))
      = Fintype.card {i : ι // Fintype.card (V i) = n} * (n - 1) + 1 := by
  rw [finrank_signless_size_eq hn0 hnN hne,
    finrank_ker_secularMap_eq_one hne i₀ (sub_ne_zero_of_no_half hhalf) hsum]

theorem finrank_signless_size_secular_zero {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n ≠ Fintype.card (Σ i, V i)) (hne : ∀ i, Nonempty (V i))
    (hhalf : ∀ i, 2 * Fintype.card (V i) ≠ n)
    (hsum : secularSum (V := V) ((Fintype.card (Σ i, V i) : ℝ) - n) ≠ -1) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
        - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id))
      = Fintype.card {i : ι // Fintype.card (V i) = n} * (n - 1) := by
  rw [finrank_signless_size_eq hn0 hnN hne,
    ker_secularMap_eq_bot (sub_ne_zero_of_no_half hhalf) hsum, finrank_bot, add_zero]

/-! ## 7. Eigenvalue-hood and the dimension count, for any real matrix -/

theorem isEigenvector_iff_finrank_pos {K : Type*} [Field K] {m : Type*} [Fintype m]
    [DecidableEq m] (A : Matrix m m K) (μ : K) :
    (∃ x : m → K, x ≠ 0 ∧ A *ᵥ x = μ • x)
      ↔ 0 < Module.finrank K (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)) := by
  rw [Module.finrank_pos_iff]
  constructor
  · rintro ⟨x, hx0, hx⟩
    refine ⟨⟨x, (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr hx⟩, 0, ?_⟩
    intro h
    exact hx0 (congrArg Subtype.val h)
  · intro h
    obtain ⟨⟨x, hx⟩, hx0⟩ :=
      exists_ne (0 : LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id))
    exact ⟨x, fun h0 => hx0 (Subtype.ext h0),
      (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mp hx⟩

/-! ## 8. The whole secular equation at one graph -/

theorem secularSum_path (μ : ℝ) :
    secularSum (V := fun i : Fin 2 => Fin (i.1 + 1)) μ = 1 / (1 - μ) + 2 / (-1 - μ) := by
  rw [secularSum, card_path_example]
  rw [Fin.sum_univ_two]
  norm_num

theorem secularSum_path_eq_neg_one {μ : ℝ} (h1 : μ ≠ 1) (h2 : μ ≠ -1) :
    secularSum (V := fun i : Fin 2 => Fin (i.1 + 1)) μ = -1 ↔ μ = 0 ∨ μ = 3 := by
  have ha : (1 : ℝ) - μ ≠ 0 := fun h => h1 (by linarith)
  have hb : (-1 : ℝ) - μ ≠ 0 := fun h => h2 (by linarith)
  rw [secularSum_path]
  constructor
  · intro h
    field_simp at h
    have hq : μ * (μ - 3) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hq with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

/-! ## 9. The three part-value cases at that graph -/

theorem finrank_signless_path_one :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph (fun i : Fin 2 => Fin (i.1 + 1))))
      - (1 : ℝ) • LinearMap.id)) = 1 := by
  have hval : ((Fintype.card (Σ i : Fin 2, Fin (i.1 + 1)) : ℝ) - ((2 : ℕ) : ℝ)) = 1 := by
    rw [card_path_example]; norm_num
  have h := UnbalancedMultipartiteSecularBound.finrank_signless_size_eq_of_unique_half
    (V := fun i : Fin 2 => Fin (i.1 + 1)) (n := 2) (by norm_num)
    (by rw [card_path_example]; norm_num) (fun _ => ⟨0⟩) 0 (by decide) (by decide)
  rw [hval] at h
  rw [h]
  decide

theorem finrank_signless_path_neg_one :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph (fun i : Fin 2 => Fin (i.1 + 1))))
      - (-1 : ℝ) • LinearMap.id)) = 0 := by
  have hval : ((Fintype.card (Σ i : Fin 2, Fin (i.1 + 1)) : ℝ) - ((4 : ℕ) : ℝ)) = -1 := by
    rw [card_path_example]; norm_num
  have h := UnbalancedMultipartiteSecularBound.finrank_signless_size_eq_of_unique_half
    (V := fun i : Fin 2 => Fin (i.1 + 1)) (n := 4) (by norm_num)
    (by rw [card_path_example]; norm_num) (fun _ => ⟨0⟩) 1 (by decide) (by decide)
  rw [hval] at h
  rw [h]
  decide

theorem finrank_signless_path_two :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph (fun i : Fin 2 => Fin (i.1 + 1))))
      - (2 : ℝ) • LinearMap.id)) = 0 := by
  have hval : ((Fintype.card (Σ i : Fin 2, Fin (i.1 + 1)) : ℝ) - ((1 : ℕ) : ℝ)) = 2 := by
    rw [card_path_example]; norm_num
  have hd : ∀ i : Fin 2, ((Fintype.card (Σ i : Fin 2, Fin (i.1 + 1)) : ℝ)
      - 2 * Fintype.card (Fin (i.1 + 1)) - 2) ≠ 0 := by
    intro i
    rw [card_path_example, Fintype.card_fin]
    fin_cases i <;> norm_num
  have hs : secularSum (V := fun i : Fin 2 => Fin (i.1 + 1)) 2 ≠ -1 := by
    rw [secularSum_path]
    norm_num
  have h := finrank_signless_size_eq (V := fun i : Fin 2 => Fin (i.1 + 1)) (n := 1)
    (by norm_num) (by rw [card_path_example]; norm_num) (fun _ => ⟨0⟩)
  rw [hval, ker_secularMap_eq_bot hd hs, finrank_bot] at h
  rw [h]
  decide

/-! ## 10. And so the whole signless spectrum of that graph -/

theorem isEigenvalue_signless_path (μ : ℝ) :
    (∃ x : (Σ i : Fin 2, Fin (i.1 + 1)) → ℝ, x ≠ 0 ∧
        signlessLap (completeMultipartiteGraph (fun i : Fin 2 => Fin (i.1 + 1))) *ᵥ x = μ • x)
      ↔ μ = 0 ∨ μ = 1 ∨ μ = 3 := by
  by_cases h1 : μ = 1
  · subst h1
    refine iff_of_true ?_ (Or.inr (Or.inl rfl))
    rw [isEigenvector_iff_finrank_pos, finrank_signless_path_one]
    norm_num
  by_cases h2 : μ = 2
  · subst h2
    refine iff_of_false (fun hex => ?_) (by norm_num)
    rw [isEigenvector_iff_finrank_pos, finrank_signless_path_two] at hex
    exact lt_irrefl 0 hex
  by_cases hm : μ = -1
  · subst hm
    refine iff_of_false (fun hex => ?_) (by norm_num)
    rw [isEigenvector_iff_finrank_pos, finrank_signless_path_neg_one] at hex
    exact lt_irrefl 0 hex
  have hval : ∀ i : Fin 2,
      ((Fintype.card (Σ i : Fin 2, Fin (i.1 + 1)) : ℝ) - Fintype.card (Fin (i.1 + 1))) ≠ μ := by
    intro i
    rw [card_path_example, Fintype.card_fin]
    fin_cases i
    · intro h; exact h2 (by norm_num at h; linarith)
    · intro h; exact h1 (by norm_num at h; linarith)
  have hd : ∀ i : Fin 2, ((Fintype.card (Σ i : Fin 2, Fin (i.1 + 1)) : ℝ)
      - 2 * Fintype.card (Fin (i.1 + 1)) - μ) ≠ 0 := by
    intro i
    rw [card_path_example, Fintype.card_fin]
    fin_cases i
    · intro h; exact h1 (by norm_num at h; linarith)
    · intro h; exact hm (by norm_num at h; linarith)
  rw [isEigenvalue_signless_iff_secular (fun _ => ⟨0⟩) 0 hval hd,
    secularSum_path_eq_neg_one h1 hm]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl h
    · exact absurd h h1
    · exact Or.inr h

/-! ## 11. Every multiplicity, and they exhaust the vertex count -/

theorem finrank_signless_path_secular {μ : ℝ} (h1 : μ ≠ 1) (h2 : μ ≠ 2) (hm : μ ≠ -1)
    (hs : secularSum (V := fun i : Fin 2 => Fin (i.1 + 1)) μ = -1) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph (fun i : Fin 2 => Fin (i.1 + 1))))
      - μ • LinearMap.id)) = 1 := by
  refine finrank_signless_eigenspace_secular_one (fun _ => ⟨0⟩) 0 (fun i => ?_) (fun i => ?_) hs
  · rw [card_path_example, Fintype.card_fin]
    fin_cases i
    · intro h; exact h2 (by norm_num at h; linarith)
    · intro h; exact h1 (by norm_num at h; linarith)
  · rw [card_path_example, Fintype.card_fin]
    fin_cases i
    · intro h; exact h1 (by norm_num at h; linarith)
    · intro h; exact hm (by norm_num at h; linarith)

theorem finrank_signless_path_zero :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph (fun i : Fin 2 => Fin (i.1 + 1))))
      - (0 : ℝ) • LinearMap.id)) = 1 :=
  finrank_signless_path_secular (by norm_num) (by norm_num) (by norm_num)
    (by rw [secularSum_path]; norm_num)

theorem finrank_signless_path_three :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph (fun i : Fin 2 => Fin (i.1 + 1))))
      - (3 : ℝ) • LinearMap.id)) = 1 :=
  finrank_signless_path_secular (by norm_num) (by norm_num) (by norm_num)
    (by rw [secularSum_path]; norm_num)

/-- **THE THREE MULTIPLICITIES EXHAUST THE VERTEX COUNT**, so the list above is the whole
spectrum and every eigenvalue is simple. -/
theorem finrank_signless_path_add :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph (fun i : Fin 2 => Fin (i.1 + 1))))
      - (0 : ℝ) • LinearMap.id))
    + Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph (fun i : Fin 2 => Fin (i.1 + 1))))
      - (1 : ℝ) • LinearMap.id))
    + Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph (fun i : Fin 2 => Fin (i.1 + 1))))
      - (3 : ℝ) • LinearMap.id))
      = Fintype.card (Σ i : Fin 2, Fin (i.1 + 1)) := by
  rw [finrank_signless_path_zero, finrank_signless_path_one, finrank_signless_path_three,
    card_path_example]

end UnbalancedMultipartiteSecularEquation
