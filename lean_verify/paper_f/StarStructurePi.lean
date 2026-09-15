/-
  StarStructurePi: **THE `n`-FACTOR DICHOTOMY.** A `⋆`-structure on a finite product of rings,
  each having only the trivial central idempotents, PERMUTES the minimal central idempotents:
  `s (e i) = e (σ i)` for a permutation `σ` of the index type. `StarStructureProduct`'s
  `prod_dichotomy` is the case of two factors, where a permutation of a two-element set is
  exactly *fixes or swaps*; this is the residue `UNLOCK_WATCHLIST` entry 266 left after that
  unit, in its own words: *"what is left of (2) is the `n`-factor induction alone"*.

  **IT IS NOT AN INDUCTION, and that is the only interesting thing about the proof.** The
  watchlist called it an induction because the two-factor case was proved by a four-way case
  split on a pair of trivial-central-idempotent dichotomies, and iterating that is what an
  induction on the number of factors would do. The `n`-factor statement does not need it. The
  images `s (e i)` have supports that are pairwise DISJOINT (distinct minimal central
  idempotents multiply to `0`, `s` is anti-multiplicative, so their images multiply to `0`, and
  two `1`s at one coordinate cannot), NONEMPTY (`s` is injective and `e i ≠ 0`), and COVERING
  (the identity of a finite product is the SUM of the `e i`, `s` is additive and `s 1 = 1`).
  Those three facts make `τ : j ↦ the factor whose image covers j` a well-defined SURJECTION
  from the index to itself, and **a surjective self-map of a finite type is a bijection**. The
  permutation is that bijection's inverse. No case split, no induction, no hypothesis on the
  number of factors.

  WHERE FINITENESS OF THE INDEX IS USED, all three places, because it is the only substantive
  hypothesis beyond the two-factor case's:
  * `Finset.univ` in the definition of `supp`;
  * `univ_sum_single`, that `∑ i, e i = 1` — false for an infinite product, where the identity
    is not a finite sum of the minimal idempotents;
  * `factorOf_bijective`, surjective-implies-bijective.

  **`exists_factorPerm`, the existential form, needs only `Finite ι`** — `Fintype.ofFinite`
  supplies the rest inside the proof, because an `∃` over permutations cannot see which
  enumeration built them. Mathlib's `linter.unusedFintypeInType` is what pointed that out, and
  it is the sharper statement, so it is the one kept.

  WHAT IS PROVED.
  * **`map_sum`** — a `⋆`-structure is additive over a `Finset` sum. Two lines by induction on
    the `Finset`, and the estate had no such lemma because `StarStr` carries only `map_add`.
  * **`center_pi_apply`, `isIdem_pi_apply`, `apply_eq_zero_or_one`** — the componentwise half:
    a central idempotent of `∏ B i` has every component a central idempotent of its factor,
    hence `0` or `1`. These are `StarStructureProduct`'s `center_prod_left`/`center_prod_right`
    and `isIdem_prod` at `n` factors, and the proofs are the same one probe vector,
    `Pi.single i b`, in place of `(b, 0)` and `(0, c)`.
  * **`single_mem_center`, `single_isIdem`, `single_mul_single_of_ne`, `single_one_ne_zero`,
    `univ_sum_single`** — the minimal central idempotents and their arithmetic.
  * **`supp`, `mem_supp_iff`, `not_mem_supp_iff`** — the support of `s (e i)`, and the fact that
    membership is the same as the component being `1` rather than merely nonzero. **The `1 ≠ 0`
    hypothesis on each factor is what makes those two statements equivalent** and it is carried
    explicitly, not assumed away.
  * **`supp_disjoint`, `supp_nonempty`, `exists_mem_supp`** — the three facts above.
  * **`factorOf`, `mem_supp_factorOf`, `eq_factorOf`, `factorOf_surjective`,
    `factorOf_bijective`, `factorPerm`,
    `factorPerm_eq_iff`** — the map and its inverse.
  * **`map_single_eq`, `exists_factorPerm`** — the theorem, in pointwise and existential form.
  * **`factorPerm_involutive`** — **AND `σ` IS FORCED TO BE AN INVOLUTION.** Two lines: apply
    `s` twice to `e i`, `map_involutive` returns it, `map_single_eq` says the result is
    `e (σ(σ i))`, and distinct minimal central idempotents differ somewhere. **This was in this
    file's own *what is not proved* list**, as *"no constraint on which `σ` arise is proved"*,
    and the adversarial review the standing orders ask for is what took it out.
  * **`single_mul_single_same`, `map_single_apply_eq_zero`, `blockMap`,
    `map_single_eq_single_blockMap`, `blockMap_add`, `blockMap_mul`, `blockMap_one`** — **`s`
    CARRIES BLOCK `i` INTO BLOCK `σ i`**, by an additive, ANTI-multiplicative, unital map. This
    is the `restrictLeft`/`restrictRight` analogue the first draft listed as missing, and it is
    **strictly stronger than the shape that list asked for**: it assumes nothing about whether
    `σ` fixes `i`, so the fixed factors and the swapped pairs are ONE statement, and the
    “cycles of length `≥ 3` needing their own statement” clause was answering a question that
    `factorPerm_involutive` shows cannot arise.
  * **`complex_onlyTrivial`, `conjPermStar`, `conjPermStar_single`, `factorPerm_conjPermStar`,
    `exists_conjPerm_iff`** — **AND EVERY INVOLUTION OCCURS, so the answer is EXACTLY THE
    INVOLUTIONS.** On `∏_{i∈ι} ℂ`, `s x = fun j ↦ conj (x (σ j))` is a `⋆`-structure — additive
    because `conj` is, anti-multiplicative because `ℂ` is commutative, and involutive **exactly
    because `σ` is**, which is where `factorPerm_involutive`'s necessity becomes this
    construction's hypothesis — and its `factorPerm` is `σ`. **The asymmetry between the two
    directions is real and kept**: the CONSTRAINT holds for every product of rings with trivial
    central idempotents, and the REALISATION is exhibited on one family. `ℂ` qualifies off the
    estate's own `onlyTrivialCentralIdem_of_isDomain`, which was checked by a grep of the index
    before this section was written and not assumed.

  WHAT IS **NOT** PROVED.
  * ~~**The `n`-factor analogue of `restrictLeft`/`restrictRight` is NOT here.**~~ ~~**No
    permutation is computed, and no constraint on which `σ` arise is proved.**~~ **BOTH WERE
    FALSE WITHIN THE HOUR, and the adversarial review the standing orders ask for after every
    new proof file is what found them.** `factorPerm_involutive` is the constraint — `σ² = 1`,
    two lines — and `map_single_apply_eq_zero` with the `blockMap` family is the
    `restrictLeft`/`restrictRight` analogue, in a form that needed no case split on whether `σ`
    fixes `i`. **The transferable shape: a *what is not proved* list is a list of CLAIMS, and
    two of mine were refuted by the file they were written about.** Section 7 above.
  * **`blockMap` is not shown BIJECTIVE.** Its inverse ought to be `blockMap` at `σ i`, which
    lands in `B (σ(σ i))`; `factorPerm_involutive` makes that `B i` — but as a PROPOSITIONAL
    equality, so composing the two maps needs a transport along it, and the composite's
    statement is then about a transported map rather than about `blockMap` itself. **Measured,
    not guessed: the obstruction is dependent-type plumbing and not mathematics**, and it is
    left for a unit that wants to pay for it.
  * ~~**No `σ` is REALISED, so the classification is one-sided.**~~ **WALKED IN THE SAME UNIT**,
    and the route was the one named: section 8, `exists_conjPerm_iff`. The grep it asked for
    returned `onlyTrivialCentralIdem_of_isDomain`, so `ℂ` cost one line. **What the closed
    classification still does NOT say**: the realisation is on `∏ ℂ` only, so nothing here rules
    out a family of factors on which some involution is NOT realised — the `⇐` direction is an
    existence statement about one family, not a statement about every family, and the header
    above says so where it is proved.
  * **The hypothesis that each factor has only trivial central idempotents is not discharged
    here.** For matrix algebras it is `CentralIdemInvariant`'s business, and this file takes it
    as given, exactly as `prod_dichotomy` does.
  * **Nothing about the real-form fork.** Entry 266's item (1) residue — the constant `c` with
    `Pᴴ = c • P`, whose two signs over `ℝ` separate `Mₙ(ℝ)` from `Mₙ(ℍ)` — is untouched, and so
    is its item (3).
  * **No `⋆`-structure on a product is constructed.** Every statement here is about a given `s`.

  0 sorry. 0 new axioms. 38 declarations, none on any axiom outside
  `[propext, Classical.choice, Quot.sound]` — and `single_mul_single_same` needs only two of the
  three, which is counted rather than rounded up.
-/

import StarStructureProduct

namespace StarStructurePi

open StarStructureProduct CentralIdemInvariant

noncomputable section

/-! ## 1. `⋆`-structures respect finite sums -/

/-- A `⋆`-structure is additive, hence additive over a `Finset` sum. Needed because the
identity of a finite product is a SUM of the minimal central idempotents, and that is how the
covering half of the partition argument gets its hands on `s 1 = 1`. -/
theorem map_sum {A : Type*} [Ring A] (s : StarStr A) {κ : Type*} (t : Finset κ) (f : κ → A) :
    s.map (∑ x ∈ t, f x) = ∑ x ∈ t, s.map (f x) := by
  classical
  induction t using Finset.induction with
  | empty => simp [map_zero s]
  | insert a t ha ih => rw [Finset.sum_insert ha, s.map_add, ih, Finset.sum_insert ha]

/-! ## 2. Central idempotents of a finite product are componentwise trivial -/

variable {ι : Type*} {B : ι → Type*} [∀ i, Ring (B i)]

theorem center_pi_apply {e : ∀ i, B i} (he : e ∈ Set.center (∀ i, B i)) (i : ι) :
    e i ∈ Set.center (B i) := by
  classical
  refine Semigroup.mem_center_iff.mpr fun b => ?_
  have h := Semigroup.mem_center_iff.mp he (Pi.single i b)
  simpa using congrFun h i

theorem isIdem_pi_apply {e : ∀ i, B i} (he : e * e = e) (i : ι) : e i * e i = e i :=
  congrFun he i

/-- Each component of a central idempotent is `0` or `1`, given that each factor has only the
trivial central idempotents. This is the `n`-factor form of `isIdem_prod` plus
`center_prod_left`/`center_prod_right` together. -/
theorem apply_eq_zero_or_one (htriv : ∀ i, OnlyTrivialCentralIdem (B i))
    {e : ∀ i, B i} (hc : e ∈ Set.center (∀ i, B i)) (hi : e * e = e) (i : ι) :
    e i = 0 ∨ e i = 1 :=
  htriv i (e i) (center_pi_apply hc i) (isIdem_pi_apply hi i)

/-! ## 3. The minimal central idempotents of a finite product -/

variable [DecidableEq ι]

theorem single_mem_center (i : ι) : (Pi.single i (1 : B i)) ∈ Set.center (∀ i, B i) := by
  refine Semigroup.mem_center_iff.mpr fun y => ?_
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem single_isIdem (i : ι) :
    (Pi.single i (1 : B i)) * (Pi.single i (1 : B i)) = Pi.single i (1 : B i) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem single_mul_single_of_ne {i j : ι} (h : i ≠ j) :
    (Pi.single i (1 : B i)) * (Pi.single j (1 : B j)) = 0 := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [Pi.single_eq_of_ne h]
  · simp [Pi.single_eq_of_ne hk]

theorem single_one_ne_zero {i : ι} (hone : (1 : B i) ≠ 0) : (Pi.single i (1 : B i)) ≠ 0 := by
  intro h
  exact hone (by simpa using congrFun h i)

variable [Fintype ι]

theorem univ_sum_single : (∑ i : ι, Pi.single i (1 : B i)) = 1 := by
  simpa using Finset.univ_sum_single (fun i : ι => (1 : B i))

/-! ## 4. The support of the image of a minimal central idempotent -/

variable (s : StarStr (∀ i, B i))

open scoped Classical in
/-- The set of coordinates at which `s` sends the `i`-th minimal central idempotent to `1`. -/
def supp (i : ι) : Finset ι :=
  Finset.univ.filter (fun j => s.map (Pi.single i (1 : B i)) j ≠ 0)

omit [Fintype ι] in
theorem apply_single_eq_zero_or_one (htriv : ∀ i, OnlyTrivialCentralIdem (B i)) (i j : ι) :
    s.map (Pi.single i (1 : B i)) j = 0 ∨ s.map (Pi.single i (1 : B i)) j = 1 :=
  apply_eq_zero_or_one htriv (map_mem_center s (single_mem_center i))
    (map_isIdem s (single_isIdem i)) j

theorem mem_supp_iff (htriv : ∀ i, OnlyTrivialCentralIdem (B i)) (hone : ∀ i, (1 : B i) ≠ 0)
    (i j : ι) : j ∈ supp s i ↔ s.map (Pi.single i (1 : B i)) j = 1 := by
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases apply_single_eq_zero_or_one s htriv i j with h | h
  · simp only [h, ne_eq, not_true_eq_false, false_iff]
    exact fun hc => hone j hc.symm
  · simp [h, hone j]

theorem not_mem_supp_iff (htriv : ∀ i, OnlyTrivialCentralIdem (B i))
    (hone : ∀ i, (1 : B i) ≠ 0) (i j : ι) :
    j ∉ supp s i ↔ s.map (Pi.single i (1 : B i)) j = 0 := by
  rcases apply_single_eq_zero_or_one s htriv i j with h | h
  · simp [supp, h]
  · simp [(mem_supp_iff s htriv hone i j).mpr h, h, hone j]

/-! ## 5. The supports are DISJOINT, NONEMPTY, and COVER -/

/-- **Disjoint**, because distinct minimal central idempotents multiply to `0` and `s` is
anti-multiplicative, so their images do too — and two `1`s at the same coordinate cannot. -/
theorem supp_disjoint (htriv : ∀ i, OnlyTrivialCentralIdem (B i)) (hone : ∀ i, (1 : B i) ≠ 0)
    {i i' : ι} (hne : i ≠ i') {j : ι} (h : j ∈ supp s i) (h' : j ∈ supp s i') : False := by
  have hmul : s.map (Pi.single i' (1 : B i')) * s.map (Pi.single i (1 : B i)) = 0 := by
    rw [← s.map_mul, single_mul_single_of_ne hne, map_zero s]
  have hj := congrFun hmul j
  simp only [Pi.mul_apply, Pi.zero_apply] at hj
  rw [(mem_supp_iff s htriv hone i j).mp h, (mem_supp_iff s htriv hone i' j).mp h'] at hj
  exact hone j (by simpa using hj)

/-- **Nonempty**, because `s` is injective and the minimal central idempotent is not `0`. -/
theorem supp_nonempty (htriv : ∀ i, OnlyTrivialCentralIdem (B i)) (hone : ∀ i, (1 : B i) ≠ 0)
    (i : ι) : (supp s i).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hemp
  have hz : s.map (Pi.single i (1 : B i)) = 0 := by
    funext j
    exact (not_mem_supp_iff s htriv hone i j).mp (by simp [hemp])
  have : Pi.single i (1 : B i) = 0 := map_injective s (by rw [hz, map_zero s])
  exact single_one_ne_zero (hone i) this

/-- **They cover**, because the identity of a finite product is the SUM of the minimal central
idempotents, `s` is additive and `s 1 = 1`. -/
theorem exists_mem_supp (htriv : ∀ i, OnlyTrivialCentralIdem (B i)) (hone : ∀ i, (1 : B i) ≠ 0)
    (j : ι) : ∃ i, j ∈ supp s i := by
  by_contra hcon
  simp only [not_exists] at hcon
  have hz : ∀ i, s.map (Pi.single i (1 : B i)) j = 0 :=
    fun i => (not_mem_supp_iff s htriv hone i j).mp (hcon i)
  have h1 : (∑ i : ι, s.map (Pi.single i (1 : B i))) j = (1 : ∀ i, B i) j := by
    rw [← map_sum s Finset.univ, univ_sum_single, map_one s]
  rw [Finset.sum_apply] at h1
  simp only [hz, Finset.sum_const_zero, Pi.one_apply] at h1
  exact hone j h1.symm

/-! ## 6. Hence a PERMUTATION of the factors -/

/-- The factor whose image contains the coordinate `j`. Well defined by section 5. -/
def factorOf (htriv : ∀ i, OnlyTrivialCentralIdem (B i)) (hone : ∀ i, (1 : B i) ≠ 0) (j : ι) : ι :=
  (exists_mem_supp s htriv hone j).choose

theorem mem_supp_factorOf (htriv : ∀ i, OnlyTrivialCentralIdem (B i)) (hone : ∀ i, (1 : B i) ≠ 0)
    (j : ι) : j ∈ supp s (factorOf s htriv hone j) :=
  (exists_mem_supp s htriv hone j).choose_spec

theorem eq_factorOf (htriv : ∀ i, OnlyTrivialCentralIdem (B i)) (hone : ∀ i, (1 : B i) ≠ 0)
    {i j : ι} (h : j ∈ supp s i) : i = factorOf s htriv hone j := by
  by_contra hne
  exact supp_disjoint s htriv hone hne h (mem_supp_factorOf s htriv hone j)

/-- `factorOf` is SURJECTIVE, because every support is nonempty — and a surjective self-map of a
finite type is a bijection, which is where finiteness of the index does its only work. -/
theorem factorOf_surjective (htriv : ∀ i, OnlyTrivialCentralIdem (B i))
    (hone : ∀ i, (1 : B i) ≠ 0) :
    Function.Surjective (factorOf s htriv hone) := by
  intro i
  obtain ⟨j, hj⟩ := supp_nonempty s htriv hone i
  exact ⟨j, (eq_factorOf s htriv hone hj).symm⟩

theorem factorOf_bijective (htriv : ∀ i, OnlyTrivialCentralIdem (B i)) (hone : ∀ i, (1 : B i) ≠ 0) :
    Function.Bijective (factorOf s htriv hone) :=
  Finite.surjective_iff_bijective.mp (factorOf_surjective s htriv hone)

/-- **THE PERMUTATION OF THE FACTORS.** -/
def factorPerm (htriv : ∀ i, OnlyTrivialCentralIdem (B i)) (hone : ∀ i, (1 : B i) ≠ 0) :
    Equiv.Perm ι :=
  (Equiv.ofBijective _ (factorOf_bijective s htriv hone)).symm

theorem factorPerm_eq_iff (htriv : ∀ i, OnlyTrivialCentralIdem (B i))
    (hone : ∀ i, (1 : B i) ≠ 0) (i j : ι) :
    factorPerm s htriv hone i = j ↔ factorOf s htriv hone j = i := by
  rw [factorPerm, Equiv.symm_apply_eq]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- **THE `n`-FACTOR DICHOTOMY, as a permutation.** A `⋆`-structure on a finite product of rings
each having only the trivial central idempotents PERMUTES the minimal central idempotents:
`s (e i) = e (σ i)` for a permutation `σ` of the index. `prod_dichotomy` is the case of two
factors, where a permutation of a two-element set is exactly *fixes or swaps*. -/
theorem map_single_eq (htriv : ∀ i, OnlyTrivialCentralIdem (B i)) (hone : ∀ i, (1 : B i) ≠ 0)
    (i : ι) :
    s.map (Pi.single i (1 : B i)) = Pi.single (factorPerm s htriv hone i) (1 : B _) := by
  have hmem' : factorPerm s htriv hone i ∈ supp s i := by
    have ht : factorOf s htriv hone (factorPerm s htriv hone i) = i :=
      (factorPerm_eq_iff s htriv hone i (factorPerm s htriv hone i)).mp rfl
    have h0 := mem_supp_factorOf s htriv hone (factorPerm s htriv hone i)
    rwa [ht] at h0
  funext j
  by_cases h : j = factorPerm s htriv hone i
  · rw [h, (mem_supp_iff s htriv hone i _).mp hmem', Pi.single_eq_same]
  · have hnot : j ∉ supp s i := fun hmem =>
      h ((factorPerm_eq_iff s htriv hone i j).mpr (eq_factorOf s htriv hone hmem).symm).symm
    rw [(not_mem_supp_iff s htriv hone i j).mp hnot, Pi.single_eq_of_ne h]

omit [Fintype ι] in
/-- **And the two-factor statement is the `n = 2` case**: a permutation of the index either
fixes `i` or does not, which is `prod_dichotomy`'s *fixes or swaps* once the index has two
elements. Stated as an `∃` over permutations so nothing has to be said about `σ`'s cycle type. -/
theorem exists_factorPerm [Finite ι] (htriv : ∀ i, OnlyTrivialCentralIdem (B i))
    (hone : ∀ i, (1 : B i) ≠ 0) :
    ∃ σ : Equiv.Perm ι, ∀ i : ι, s.map (Pi.single i (1 : B i)) = Pi.single (σ i) (1 : B _) := by
  haveI := Fintype.ofFinite ι
  exact ⟨factorPerm s htriv hone, map_single_eq s htriv hone⟩

/-! ## 7. The permutation is an INVOLUTION, and `s` carries each block into its image -/

/-- **THE PERMUTATION IS AN INVOLUTION**, and this was in the first draft's *what is not
proved* list as *"no constraint on which `σ` arise is proved"*. It is two lines: apply `s` twice
to the `i`-th minimal central idempotent, `map_involutive` returns it, and `map_single_eq` says
the result is the `σ(σ i)`-th — so `σ(σ i) = i`, because two distinct minimal central idempotents
differ at a coordinate where one is `1` and the other `0`. -/
theorem factorPerm_involutive (htriv : ∀ i, OnlyTrivialCentralIdem (B i))
    (hone : ∀ i, (1 : B i) ≠ 0) (i : ι) :
    factorPerm s htriv hone (factorPerm s htriv hone i) = i := by
  have h1 : s.map (s.map (Pi.single i (1 : B i)))
      = Pi.single (factorPerm s htriv hone (factorPerm s htriv hone i)) (1 : B _) := by
    rw [map_single_eq s htriv hone i, map_single_eq s htriv hone _]
  rw [s.map_involutive] at h1
  by_contra hne
  have := congrFun h1 i
  rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)] at this
  exact hone i this

omit [Fintype ι] in
/-- `Pi.single i b` is its own product with the `i`-th minimal central idempotent, which is the
`n`-factor form of `(b, 0) = (b, 0) * (1, 0)` — the identity `StarStructureProduct`'s
`snd_eq_zero_of_fixes` turns on. -/
theorem single_mul_single_same (i : ι) (b : B i) :
    Pi.single i b = Pi.single i b * Pi.single i (1 : B i) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

/-- **`s` CARRIES BLOCK `i` INTO BLOCK `σ i`.** Off `single_mul_single_same`: applying `s` puts
`s (e i) = e (σ i)` on the LEFT, and that kills every coordinate but `σ i`. This is the
`n`-factor analogue of `restrictLeft`/`restrictRight`, **and it is strictly stronger than the
shape the first draft's residue asked for**: it needs no assumption that `σ` fixes `i`, so the
fixed factors and the swapped pairs are one statement rather than two, and cycles of length
`≥ 3` — which `factorPerm_involutive` now rules out anyway — needed no separate treatment. -/
theorem map_single_apply_eq_zero (htriv : ∀ i, OnlyTrivialCentralIdem (B i))
    (hone : ∀ i, (1 : B i) ≠ 0) (i : ι) (b : B i) {j : ι}
    (h : j ≠ factorPerm s htriv hone i) : s.map (Pi.single i b) j = 0 := by
  have h1 : s.map (Pi.single i b)
      = Pi.single (factorPerm s htriv hone i) (1 : B _) * s.map (Pi.single i b) := by
    conv_lhs => rw [single_mul_single_same i b]
    rw [s.map_mul, map_single_eq s htriv hone i]
  have h2 := congrFun h1 j
  rw [Pi.mul_apply, Pi.single_eq_of_ne h, zero_mul] at h2
  exact h2

/-- The induced map on the `i`-th block, landing in the `σ i`-th. -/
def blockMap (htriv : ∀ i, OnlyTrivialCentralIdem (B i)) (hone : ∀ i, (1 : B i) ≠ 0)
    (i : ι) (b : B i) : B (factorPerm s htriv hone i) :=
  s.map (Pi.single i b) (factorPerm s htriv hone i)

/-- And `s` on the `i`-th block IS that map, placed at `σ i`. -/
theorem map_single_eq_single_blockMap (htriv : ∀ i, OnlyTrivialCentralIdem (B i))
    (hone : ∀ i, (1 : B i) ≠ 0) (i : ι) (b : B i) :
    s.map (Pi.single i b) = Pi.single (factorPerm s htriv hone i) (blockMap s htriv hone i b) := by
  funext j
  by_cases h : j = factorPerm s htriv hone i
  · subst h; rw [Pi.single_eq_same]; rfl
  · rw [map_single_apply_eq_zero s htriv hone i b h, Pi.single_eq_of_ne h]

/-- The block map is ADDITIVE. -/
theorem blockMap_add (htriv : ∀ i, OnlyTrivialCentralIdem (B i)) (hone : ∀ i, (1 : B i) ≠ 0)
    (i : ι) (b b' : B i) :
    blockMap s htriv hone i (b + b') = blockMap s htriv hone i b + blockMap s htriv hone i b' := by
  have hsplit : Pi.single i (b + b') = Pi.single i b + Pi.single i b' := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  simp only [blockMap, hsplit, s.map_add, Pi.add_apply]

/-- And ANTI-multiplicative, so each block map is an anti-homomorphism onto its target block —
which is what *"the involution either fixes a factor or swaps two"* was reaching for. -/
theorem blockMap_mul (htriv : ∀ i, OnlyTrivialCentralIdem (B i)) (hone : ∀ i, (1 : B i) ≠ 0)
    (i : ι) (b b' : B i) :
    blockMap s htriv hone i (b * b') = blockMap s htriv hone i b' * blockMap s htriv hone i b := by
  have hsplit : Pi.single i (b * b') = Pi.single i b * Pi.single i b' := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  simp only [blockMap, hsplit, s.map_mul, Pi.mul_apply]

/-- And unital. -/
theorem blockMap_one (htriv : ∀ i, OnlyTrivialCentralIdem (B i)) (hone : ∀ i, (1 : B i) ≠ 0)
    (i : ι) : blockMap s htriv hone i 1 = 1 := by
  simp only [blockMap, map_single_eq s htriv hone i, Pi.single_eq_same]

/-! ## 8. Which permutations occur: EXACTLY the involutions -/

section Realisation

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

omit [Fintype ι] in
/-- `ℂ` has only the trivial central idempotents, because it is a domain. The estate's own
`onlyTrivialCentralIdem_of_isDomain`, named here so section 8 has a factor to work with. -/
theorem complex_onlyTrivial : OnlyTrivialCentralIdem ℂ := onlyTrivialCentralIdem_of_isDomain

/-- **Conjugate-and-permute**, for an involution `σ`: `s x = fun j ↦ conj (x (σ j))`. Additive
because `conj` is; ANTI-multiplicative because `ℂ` is commutative, so anti- and multiplicative
coincide; and involutive **exactly because `σ` is** — which is where `factorPerm_involutive`'s
necessity turns into this construction's hypothesis. -/
def conjPermStar (σ : Equiv.Perm ι) (hσ : ∀ i, σ (σ i) = i) : StarStr (∀ _ : ι, ℂ) where
  map x := fun j => (starRingEnd ℂ) (x (σ j))
  map_add x y := by funext j; simp
  map_mul x y := by funext j; simp [mul_comm]
  map_involutive x := by funext j; simp [hσ j]

omit [Fintype ι] in
theorem conjPermStar_single (σ : Equiv.Perm ι) (hσ : ∀ i, σ (σ i) = i) (i : ι) :
    (conjPermStar σ hσ).map (Pi.single i (1 : ℂ)) = Pi.single (σ i) (1 : ℂ) := by
  funext j
  by_cases h : j = σ i
  · subst h
    simp only [conjPermStar]
    rw [hσ i, Pi.single_eq_same, _root_.map_one, Pi.single_eq_same]
  · have hne : σ j ≠ i := by
      intro hc
      exact h (by rw [← hc, hσ j])
    simp only [conjPermStar, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne h, _root_.map_zero]

/-- **AND ITS PERMUTATION IS `σ`.** Off `map_single_eq`'s uniqueness: two `Pi.single`s with value
`1` at different coordinates differ at one of them. -/
theorem factorPerm_conjPermStar (σ : Equiv.Perm ι) (hσ : ∀ i, σ (σ i) = i) (i : ι) :
    factorPerm (conjPermStar σ hσ) (fun _ => complex_onlyTrivial) (fun _ => one_ne_zero) i
      = σ i := by
  have h1 := map_single_eq (conjPermStar σ hσ) (fun _ => complex_onlyTrivial)
    (fun _ => one_ne_zero) i
  rw [conjPermStar_single σ hσ i] at h1
  by_contra hne
  have h2 := congrFun h1 (σ i)
  rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)] at h2
  exact one_ne_zero h2

/-- **THE CLASSIFICATION, both directions.** On `∏_{i∈ι} ℂ` the permutations a `⋆`-structure can
induce on the minimal central idempotents are **exactly the involutions** — `⇒` is
`factorPerm_involutive`, proved for an arbitrary family of factors, and `⇐` is `conjPermStar`, which
needs a concrete one. The asymmetry is real and worth keeping: the CONSTRAINT holds for every
product of rings with trivial central idempotents, and the REALISATION is exhibited on one. -/
theorem exists_conjPerm_iff (σ : Equiv.Perm ι) :
    (∃ s : StarStr (∀ _ : ι, ℂ), ∀ i,
        factorPerm s (fun _ => complex_onlyTrivial) (fun _ => one_ne_zero) i = σ i)
      ↔ ∀ i, σ (σ i) = i := by
  constructor
  · rintro ⟨s, hs⟩ i
    have h := factorPerm_involutive s (fun _ => complex_onlyTrivial) (fun _ => one_ne_zero) i
    rw [hs i, hs (σ i)] at h
    exact h
  · intro hσ
    exact ⟨conjPermStar σ hσ, factorPerm_conjPermStar σ hσ⟩

end Realisation

end

end StarStructurePi
