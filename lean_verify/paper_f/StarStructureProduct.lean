/-
  StarStructureProduct: a ⋆-structure on a product either FIXES the two factors or SWAPS them —
  now a theorem rather than a claim about the shape of the work

  SPINE LINKS L6 and L11. `UNLOCK_WATCHLIST` 266's item (2).

  WHAT THIS DISCHARGES, and it is my own flagged non-theorem. `StarStructureMatrix`'s header
  opened by saying that the single-factor case *"is the whole of the difficulty: the product
  case is a direct sum and the involution either fixes a factor or swaps two"*, and its
  WHAT-IS-NOT-CLAIMED list then said in so many words that **this is a claim about the shape of
  the remaining work, not a theorem**. `UNLOCK_WATCHLIST` 266 repeated the flag. **This file
  proves it.**

  AND IT REMOVES TWO HYPOTHESES RATHER THAN ONE. `StarStructureMatrix.StarStructure` is a
  conjugate-linear involution of `Mₙ(ℂ)` specifically. The dichotomy needs **neither** the base
  field **nor** the matrix algebra:

  * **`StarStr A`** is an anti-multiplicative additive involution of an arbitrary RING. **There
    is no `map_smul` field** — the scalars play no part in the argument, and carrying them would
    have hidden that.

  AND THE MATRIX FILE NOW CONSUMES THIS ONE, not the other way round. The first draft imported
  `StarStructureMatrix` and ended with a forgetful bridge into it, which left `map_bijective` and
  `map_one` PROVED TWICE with the same names and the same statements — caught by `dupname_scan`,
  which is exactly the defect `ERRATUM 270` exists for. The direction is reversed:
  `StarStructureMatrix` imports this file, carries a `toStarStr` forgetful map, and its
  `map_bijective` and `map_one` are one-line references to the general ones. **The scalar-free
  notion is the base and the matrix one is a special case**, which is what the first bullet above
  asserts; having the imports point the other way contradicted it.

  THE ARGUMENT, and every step of it is about idempotents.
  * **`map_one`** — unitality is derived, not assumed: `map 1` is a left identity on a surjective
    image. **This is the estate's only DERIVATION of unitality for an anti-automorphism** — every
    other `map_one` in the estate is Mathlib's, about a hom that is unital by definition — and
    the matrix file's `map_one` cites this one rather than repeating it.
  * **`map_mem_center`** and **`map_isIdem`** — an anti-automorphism preserves the centre (the
    two sides of `x y = y x` simply trade places) and preserves idempotency.
  * **`center_prod_left`**, **`isIdem_prod`** — centrality and idempotency in a product are
    componentwise, so with `OnlyTrivialCentralIdem` on each factor the central idempotents of
    `B × C` are exactly the four obvious ones.
  * **`prod_dichotomy`** — therefore `s (1, 0)` is a central idempotent, is not `0` (because
    `s` is injective and fixes `0`) and is not `1` (because `s` fixes `1`), so:

    > `s (1, 0) = (1, 0)` **or** `s (1, 0) = (0, 1)`.

  * **`snd_eq_zero_of_fixes`** and **`restrictLeft`** — in the fixing case `s` maps `B × 0` into
    itself, because `(b, 0) = (b, 0) * (1, 0)` and applying `s` puts `s (1, 0) = (1, 0)` on the
    left, which kills the second component. So `s` **restricts to a `StarStr B`**.
  * **`map_zero_one_of_fixes`**, **`fst_eq_zero_of_fixes`** and **`restrictRight`** — the mirror,
    and it costs **no second hypothesis**: `(0, 1) = 1 - (1, 0)`, `s` is additive and `map_one`
    gives `s 1 = 1`, so fixing `(1, 0)` already forces `s (0, 1) = (0, 1)`, and the same
    multiplication argument run against that kills the FIRST component on `0 × C`. **So the
    fixing case restricts to a `StarStr` on BOTH factors**, which is what makes "the
    single-factor classification applies to each factor separately" a statement about this file
    rather than a hope.
  * **`exists_antiIso_of_swaps`** — in the swapping case `s` carries `B × 0` onto `0 × C`, which
    gives an additive anti-multiplicative bijection `B → C`. **So the two factors are
    anti-isomorphic**, and a product of two factors that are not can only carry a
    factor-fixing ⋆-structure.

  WHAT IS **NOT** CLAIMED.
  * **Two factors, not `n`.** The dichotomy is proved for `B × C`. `∏ᵢ Mₐᵢ(Dᵢ)` with `n` factors
    needs an induction that is not written here, and the permutation of `n` minimal central
    idempotents is a different statement from a two-element case split.
  * **The swap case is not classified.** `exists_antiIso_of_swaps` produces an anti-isomorphism
    and stops. It is **not** shown that `B ≃ C`, nor — for matrix factors — that the two sizes
    agree; `Mₘ(ℂ) ≃ Mₙ(ℂ)ᵐᵒᵖ` forcing `m = n` is a dimension count this file does not do.
  * **The restrictions are not composed with the single-factor result.** `restrictLeft` and
    `restrictRight` reduce the fixing case to two instances of `StarStructureMatrix`'s problem
    and stop there; that composition is left to a later unit, and nothing here states the
    combined classification of ⋆-structures on `Mₘ(ℂ) × Mₙ(ℂ)`. They also produce a `StarStr`,
    which has **forgotten the conjugate-linearity** — recovering a
    `StarStructureMatrix.StarStructure` on each factor needs `map_smul` carried through the
    restriction, and that is not done.
  * **Nothing about the cascade is cut.** `a·b·c = 16` keeps every alternative
    (`ASSUMPTIONS_LEDGER` 5, 10, 11, 30, 35), and L6's rung 2 is not climbed.

  0 sorry. 0 new axioms. **And fewer than the usual three for 15 of the 28 declarations**, which
  is worth recording because it is evidence for the header's first claim that the scalars play no
  part. `#print axioms` on every declaration, each resting on a SUBSET of
  `[propext, Classical.choice, Quot.sound]`:
  * **nothing at all** (5): `StarStr` itself, `map_isIdem`, `center_prod_left`,
    `center_prod_right`, `isIdem_prod`.
  * **`propext` alone** (3): `map_zero`, `one_zero_mem_center`, `one_zero_isIdem`.
  * **`Classical.choice` alone** (4): `map_bijective`, `map_injective`, `map_one`,
    `map_mem_center`.
  * **`propext` and `Quot.sound`** (3): `snd_eq_zero_of_fixes`, `restrictLeft`,
    `restrictLeft_map`.
  * **the full three** (13): `prod_dichotomy`, the mirror restriction and its three lemmas,
    `exists_antiIso_of_swaps`, the two realisations with their two lemmas, the two restriction
    computations, and `matrixProd_dichotomy`.
-/

import CentralIdemInvariant

namespace StarStructureProduct

noncomputable section

/-! ## 1. A ⋆-structure on an arbitrary ring -/

/-- An **anti-multiplicative additive involution of a ring**. `StarStructureMatrix.StarStructure`
is this plus conjugate-linearity plus `A = Mₙ(ℂ)`; **the dichotomy below needs none of that**,
which is why there is no `map_smul` field here. -/
structure StarStr (A : Type*) [Ring A] where
  /-- The involution. -/
  map : A → A
  /-- Additive. -/
  map_add : ∀ x y, map (x + y) = map x + map y
  /-- ANTI-multiplicative. -/
  map_mul : ∀ x y, map (x * y) = map y * map x
  /-- Involutive, hence bijective. -/
  map_involutive : ∀ x, map (map x) = x

variable {A : Type*} [Ring A] (s : StarStr A)

theorem map_bijective : Function.Bijective s.map :=
  Function.bijective_iff_has_inverse.mpr ⟨s.map, s.map_involutive, s.map_involutive⟩

theorem map_injective : Function.Injective s.map := (map_bijective s).injective

/-- Unitality is a consequence: `map 1 * map x = map (x * 1) = map x` for every `x`, and `map`
is onto, so `map 1` is a left identity on all of `A`. -/
theorem map_one : s.map 1 = 1 := by
  have h : ∀ y, s.map 1 * y = y := by
    intro y
    obtain ⟨x, hx⟩ := (map_bijective s).surjective y
    rw [← hx, ← s.map_mul, mul_one]
  simpa using h 1

theorem map_zero : s.map 0 = 0 := by
  have h := s.map_add 0 0
  rw [add_zero] at h
  have h2 := sub_eq_zero.mpr h
  simpa using h2

/-- **An anti-automorphism preserves the centre**: the two sides of `x * y = y * x` trade
places and the statement is symmetric. -/
theorem map_mem_center {x : A} (hx : x ∈ Set.center A) : s.map x ∈ Set.center A := by
  refine Semigroup.mem_center_iff.mpr fun y => ?_
  refine map_injective s ?_
  rw [s.map_mul, s.map_mul, s.map_involutive]
  exact (Semigroup.mem_center_iff.mp hx (s.map y)).symm

/-- and it preserves idempotency. -/
theorem map_isIdem {x : A} (hx : x * x = x) : s.map x * s.map x = s.map x := by
  rw [← s.map_mul, hx]

/-! ## 2. Central idempotents of a product are componentwise -/

variable {B C : Type*} [Ring B] [Ring C]

theorem center_prod_left {e : B × C} (he : e ∈ Set.center (B × C)) : e.1 ∈ Set.center B := by
  refine Semigroup.mem_center_iff.mpr fun b => ?_
  have h := Semigroup.mem_center_iff.mp he (b, 0)
  exact congrArg Prod.fst h

theorem center_prod_right {e : B × C} (he : e ∈ Set.center (B × C)) : e.2 ∈ Set.center C := by
  refine Semigroup.mem_center_iff.mpr fun c => ?_
  have h := Semigroup.mem_center_iff.mp he (0, c)
  exact congrArg Prod.snd h

theorem isIdem_prod {e : B × C} (he : e * e = e) : e.1 * e.1 = e.1 ∧ e.2 * e.2 = e.2 :=
  ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

theorem one_zero_mem_center : ((1 : B), (0 : C)) ∈ Set.center (B × C) := by
  refine Semigroup.mem_center_iff.mpr fun y => ?_
  refine Prod.ext ?_ ?_ <;> simp

theorem one_zero_isIdem : ((1 : B), (0 : C)) * ((1 : B), (0 : C)) = ((1 : B), (0 : C)) := by
  refine Prod.ext ?_ ?_ <;> simp

/-! ## 3. The dichotomy -/

/-- **THE THEOREM `StarStructureMatrix`'s header flagged as not one.** A ⋆-structure on a
product of two factors, each with only the trivial central idempotents, either **fixes** the
minimal central idempotent `(1, 0)` or **swaps** it with `(0, 1)`. Nothing here uses scalars,
matrices, or finiteness. -/
theorem prod_dichotomy (s : StarStr (B × C))
    (hB : CentralIdemInvariant.OnlyTrivialCentralIdem B)
    (hC : CentralIdemInvariant.OnlyTrivialCentralIdem C)
    (hB1 : (1 : B) ≠ 0) (hC1 : (1 : C) ≠ 0) :
    s.map ((1 : B), (0 : C)) = ((1 : B), (0 : C))
      ∨ s.map ((1 : B), (0 : C)) = ((0 : B), (1 : C)) := by
  set e : B × C := ((1 : B), (0 : C)) with he
  have hcen : s.map e ∈ Set.center (B × C) := map_mem_center s one_zero_mem_center
  have hidem : s.map e * s.map e = s.map e := map_isIdem s one_zero_isIdem
  obtain ⟨hi1, hi2⟩ := isIdem_prod hidem
  have h1 := hB _ (center_prod_left hcen) hi1
  have h2 := hC _ (center_prod_right hcen) hi2
  -- `s e ≠ 0` and `s e ≠ 1`, because `s` fixes both and is injective
  have hne0 : s.map e ≠ 0 := by
    intro h
    have : e = 0 := map_injective s (by rw [h, map_zero s])
    rw [he] at this
    exact hB1 (congrArg Prod.fst this)
  have hne1 : s.map e ≠ 1 := by
    intro h
    have : e = 1 := map_injective s (by rw [h, map_one s])
    rw [he] at this
    exact hC1 (congrArg Prod.snd this).symm
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (Prod.ext h1 h2) hne0
  · exact Or.inr (Prod.ext h1 h2)
  · exact Or.inl (Prod.ext h1 h2)
  · exact absurd (Prod.ext h1 h2) hne1

/-! ## 4. The fixing case restricts to each factor -/

/-- In the fixing case `s` maps `B × 0` into itself: `(b, 0) = (b, 0) * (1, 0)`, and applying
`s` puts `s (1, 0) = (1, 0)` on the LEFT, which kills the second component. -/
theorem snd_eq_zero_of_fixes (s : StarStr (B × C))
    (hfix : s.map ((1 : B), (0 : C)) = ((1 : B), (0 : C))) (b : B) :
    (s.map (b, (0 : C))).2 = 0 := by
  have hb : (b, (0 : C)) = (b, (0 : C)) * ((1 : B), (0 : C)) := by
    refine Prod.ext ?_ ?_ <;> simp
  have h : s.map (b, (0 : C)) = ((1 : B), (0 : C)) * s.map (b, (0 : C)) := by
    conv_lhs => rw [hb]
    rw [s.map_mul, hfix]
  have h2 := congrArg Prod.snd h
  simpa using h2

/-- **So `s` restricts to a `StarStr B`**, and the single-factor classification applies to each
factor separately. This is the content of *"the involution either fixes a factor or swaps
two"*. -/
def restrictLeft (s : StarStr (B × C))
    (hfix : s.map ((1 : B), (0 : C)) = ((1 : B), (0 : C))) : StarStr B where
  map b := (s.map (b, (0 : C))).1
  map_add x y := by
    have h : ((x + y : B), (0 : C)) = (x, (0 : C)) + (y, (0 : C)) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [h, s.map_add]
    rfl
  map_mul x y := by
    have h : ((x * y : B), (0 : C)) = (x, (0 : C)) * (y, (0 : C)) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [h, s.map_mul]
    rfl
  map_involutive x := by
    have h : ((s.map (x, (0 : C))).1, (0 : C)) = s.map (x, (0 : C)) :=
      Prod.ext rfl (snd_eq_zero_of_fixes s hfix x).symm
    rw [h, s.map_involutive]

@[simp] theorem restrictLeft_map (s : StarStr (B × C))
    (hfix : s.map ((1 : B), (0 : C)) = ((1 : B), (0 : C))) (b : B) :
    (restrictLeft s hfix).map b = (s.map (b, (0 : C))).1 := rfl

/-- **The fixing case fixes the other unit too.** `(0, 1)` is `1 - (1, 0)`, `s` is additive and
`map_one` gives `s 1 = 1`, so no second hypothesis is needed for the mirror. -/
theorem map_zero_one_of_fixes (s : StarStr (B × C))
    (hfix : s.map ((1 : B), (0 : C)) = ((1 : B), (0 : C))) :
    s.map ((0 : B), (1 : C)) = ((0 : B), (1 : C)) := by
  have hsum : ((1 : B), (0 : C)) + ((0 : B), (1 : C)) = (1 : B × C) := by
    refine Prod.ext ?_ ?_ <;> simp
  have h := s.map_add ((1 : B), (0 : C)) ((0 : B), (1 : C))
  rw [hsum, map_one s, hfix] at h
  have h2 : ((0 : B), (1 : C)) = (1 : B × C) - ((1 : B), (0 : C)) := by
    refine Prod.ext ?_ ?_ <;> simp
  conv_rhs => rw [h2]
  rw [eq_sub_iff_add_eq]
  exact (add_comm _ _).trans h.symm

/-- The mirror of `snd_eq_zero_of_fixes`: `s` maps `0 × C` into itself, by the same argument run
against `s (0, 1) = (0, 1)`. -/
theorem fst_eq_zero_of_fixes (s : StarStr (B × C))
    (hfix : s.map ((1 : B), (0 : C)) = ((1 : B), (0 : C))) (c : C) :
    (s.map ((0 : B), c)).1 = 0 := by
  have hc : ((0 : B), c) = ((0 : B), c) * ((0 : B), (1 : C)) := by
    refine Prod.ext ?_ ?_ <;> simp
  have h : s.map ((0 : B), c) = ((0 : B), (1 : C)) * s.map ((0 : B), c) := by
    conv_lhs => rw [hc]
    rw [s.map_mul, map_zero_one_of_fixes s hfix]
  have h2 := congrArg Prod.fst h
  simpa using h2

/-- **The mirror restriction**, so the fixing case really does reduce to the single-factor
problem on BOTH factors and not just on the left one. -/
def restrictRight (s : StarStr (B × C))
    (hfix : s.map ((1 : B), (0 : C)) = ((1 : B), (0 : C))) : StarStr C where
  map c := (s.map ((0 : B), c)).2
  map_add x y := by
    have h : ((0 : B), (x + y : C)) = ((0 : B), x) + ((0 : B), y) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [h, s.map_add]
    rfl
  map_mul x y := by
    have h : ((0 : B), (x * y : C)) = ((0 : B), x) * ((0 : B), y) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [h, s.map_mul]
    rfl
  map_involutive x := by
    have h : ((0 : B), (s.map ((0 : B), x)).2) = s.map ((0 : B), x) :=
      Prod.ext (fst_eq_zero_of_fixes s hfix x).symm rfl
    rw [h, s.map_involutive]

@[simp] theorem restrictRight_map (s : StarStr (B × C))
    (hfix : s.map ((1 : B), (0 : C)) = ((1 : B), (0 : C))) (c : C) :
    (restrictRight s hfix).map c = (s.map ((0 : B), c)).2 := rfl

/-! ## 5. The swapping case makes the factors anti-isomorphic -/

/-- In the swapping case `s` carries `B × 0` onto `0 × C`, so `b ↦ (s (b, 0)).2` is an additive
ANTI-multiplicative bijection `B → C`. **A product of two factors that are not anti-isomorphic
can therefore only carry a factor-fixing ⋆-structure.** The map is produced and nothing is
claimed about it beyond these three properties. -/
theorem exists_antiIso_of_swaps (s : StarStr (B × C))
    (hswap : s.map ((1 : B), (0 : C)) = ((0 : B), (1 : C))) :
    ∃ f : B → C, Function.Bijective f ∧ (∀ x y, f (x + y) = f x + f y)
      ∧ (∀ x y, f (x * y) = f y * f x) := by
  have hfst : ∀ b : B, (s.map (b, (0 : C))).1 = 0 := by
    intro b
    have hb : (b, (0 : C)) = (b, (0 : C)) * ((1 : B), (0 : C)) := by
      refine Prod.ext ?_ ?_ <;> simp
    have h : s.map (b, (0 : C)) = ((0 : B), (1 : C)) * s.map (b, (0 : C)) := by
      conv_lhs => rw [hb]
      rw [s.map_mul, hswap]
    have h2 := congrArg Prod.fst h
    simpa using h2
  have hsnd : ∀ c : C, (s.map ((0 : B), c)).2 = 0 := by
    intro c
    have hone : s.map ((0 : B), (1 : C)) = ((1 : B), (0 : C)) := by
      have := s.map_involutive ((1 : B), (0 : C))
      rw [hswap] at this
      exact this
    have hc : ((0 : B), c) = ((0 : B), c) * ((0 : B), (1 : C)) := by
      refine Prod.ext ?_ ?_ <;> simp
    have h : s.map ((0 : B), c) = ((1 : B), (0 : C)) * s.map ((0 : B), c) := by
      conv_lhs => rw [hc]
      rw [s.map_mul, hone]
    have h2 := congrArg Prod.snd h
    simpa using h2
  refine ⟨fun b => (s.map (b, (0 : C))).2, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro x y hxy
    dsimp only at hxy
    have h : s.map (x, (0 : C)) = s.map (y, (0 : C)) :=
      Prod.ext (by rw [hfst, hfst]) hxy
    exact congrArg Prod.fst (map_injective s h)
  · intro c
    refine ⟨(s.map ((0 : B), c)).1, ?_⟩
    dsimp only
    have h : ((s.map ((0 : B), c)).1, (0 : C)) = s.map ((0 : B), c) :=
      Prod.ext rfl (hsnd c).symm
    rw [h, s.map_involutive]
  · intro x y
    dsimp only
    have h : ((x + y : B), (0 : C)) = (x, (0 : C)) + (y, (0 : C)) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [h, s.map_add]
    rfl
  · intro x y
    dsimp only
    have h : ((x * y : B), (0 : C)) = (x, (0 : C)) * (y, (0 : C)) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [h, s.map_mul]
    rfl

/-! ## 6. Both branches are realised, so the dichotomy is not half-empty -/

/-- The componentwise conjugate transpose on `Mₘ(ℂ) × Mₙ(ℂ)` — a ⋆-structure that **FIXES**
the factors. -/
def prodConjTranspose (m k : ℕ) :
    StarStr (Matrix (Fin m) (Fin m) ℂ × Matrix (Fin k) (Fin k) ℂ) where
  map X := (Matrix.conjTranspose X.1, Matrix.conjTranspose X.2)
  map_add X Y := by
    refine Prod.ext ?_ ?_ <;> simp [Matrix.conjTranspose_add]
  map_mul X Y := by
    refine Prod.ext ?_ ?_ <;> simp [Matrix.conjTranspose_mul]
  map_involutive X := by
    refine Prod.ext ?_ ?_ <;> simp

theorem prodConjTranspose_fixes (m k : ℕ) :
    (prodConjTranspose m k).map (1, 0) = (1, 0) := by
  refine Prod.ext ?_ ?_ <;> simp [prodConjTranspose]

/-- The **SWAPPING** branch, realised at equal sizes: `(X, Y) ↦ (Yᴴ, Xᴴ)`. So neither branch
of `prod_dichotomy` is empty, and the case split is a real one. -/
def prodSwapTranspose (m : ℕ) :
    StarStr (Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ) where
  map X := (Matrix.conjTranspose X.2, Matrix.conjTranspose X.1)
  map_add X Y := by
    refine Prod.ext ?_ ?_ <;> simp [Matrix.conjTranspose_add]
  map_mul X Y := by
    refine Prod.ext ?_ ?_ <;> simp [Matrix.conjTranspose_mul]
  map_involutive X := by
    refine Prod.ext ?_ ?_ <;> simp

theorem prodSwapTranspose_swaps (m : ℕ) :
    (prodSwapTranspose m).map (1, 0) = (0, 1) := by
  refine Prod.ext ?_ ?_ <;> simp [prodSwapTranspose]

/-- **The restrictions are applied to something in this file, and they compute** (`ERRATUM 557`).
On the componentwise conjugate transpose the left restriction is the conjugate transpose on
`Mₘ(ℂ)` and the right one is the conjugate transpose on `Mₖ(ℂ)` — so `restrictLeft` and
`restrictRight` are not definitions that nothing ever feeds, and what they return is the expected
⋆-structure and not merely some ⋆-structure. Both hold by unfolding; the content is that the
statement is even well-formed, which needs `prodConjTranspose_fixes`. -/
theorem restrictLeft_prodConjTranspose (m k : ℕ) (X : Matrix (Fin m) (Fin m) ℂ) :
    (restrictLeft (prodConjTranspose m k) (prodConjTranspose_fixes m k)).map X
      = Matrix.conjTranspose X := rfl

theorem restrictRight_prodConjTranspose (m k : ℕ) (Y : Matrix (Fin k) (Fin k) ℂ) :
    (restrictRight (prodConjTranspose m k) (prodConjTranspose_fixes m k)).map Y
      = Matrix.conjTranspose Y := rfl

/-- **The dichotomy at matrix factors**, with `CentralIdemInvariant.matrix_onlyTrivialCentralIdem`
supplying both hypotheses and `onlyTrivialCentralIdem_of_isDomain` the base field. -/
theorem matrixProd_dichotomy {m k : ℕ} [NeZero m] [NeZero k]
    (s : StarStr (Matrix (Fin m) (Fin m) ℂ × Matrix (Fin k) (Fin k) ℂ)) :
    s.map (1, 0) = (1, 0) ∨ s.map (1, 0) = (0, 1) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩⟩
  haveI : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩⟩
  refine prod_dichotomy s
    (CentralIdemInvariant.matrix_onlyTrivialCentralIdem
      (CentralIdemInvariant.onlyTrivialCentralIdem_of_isDomain (R := ℂ)))
    (CentralIdemInvariant.matrix_onlyTrivialCentralIdem
      (CentralIdemInvariant.onlyTrivialCentralIdem_of_isDomain (R := ℂ)))
    ?_ ?_
  · exact one_ne_zero
  · exact one_ne_zero

end

end StarStructureProduct
