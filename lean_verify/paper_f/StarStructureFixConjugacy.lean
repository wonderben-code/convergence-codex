/-
  StarStructureFixConjugacy.lean — the fixing branch of `Mₙ(ℂ) × Mₙ(ℂ)` up to inner conjugacy is
  the PAIR of single-factor classes, and the whole count follows: exactly `(n/2 + 1)² + 1`
  ⋆-structures on `Mₙ(ℂ) × Mₙ(ℂ)` up to inner conjugacy, with an explicit complete and irredundant
  family of representatives.

  SPINE L11 (Pati–Salam uniqueness, OPEN) and L6 / `WALLS` §W9 — the first bullet of unit 157's
  NOT list, written. Hardening unit 160, 2026-09-20.

  WHY. Unit 157 (`StarStructureSwapConjugacy`) made the swapping branch one inner-conjugacy class
  and said what it had not done: *the fixing classes should be pairs of single-factor classes —
  `(n/2 + 1)²` by `card_achievable` — but that count is not composed here*. This file composes it.
  A unit of the product is a pair `(a, b)` of units and conjugates the two twists separately, so
  inner conjugacy of two fixing normal forms is conjugacy factor by factor, and unit 75's
  `conjugate_iff_usignature` turns each factor into an equality of unordered signatures. The
  representatives are the `±1` diagonal twists with `p` and `q` plus signs, `p, q ≤ n/2`, together
  with the plain swap; `matrixProd_classification_eq` and `mem_achievable_of_unit` make the family
  complete, `Sym2.eq_iff` makes it irredundant, and unit 157's
  `not_innerConjugate_of_fixes_of_swaps` keeps the two branches apart.

  WHAT IS PROVED.
  * `fixTwist P Q` — the fixing normal form `(X, Y) ↦ (twist P X, twist Q Y)` as a `StarStrC`;
    `fixTwist_fixes`; **`fixing_iff`** — fixing ⟺ `fixTwist P Q` for Hermitian units `P`, `Q`.
  * **`fixTwist_innerConjugate_iff`** — `fixTwist P Q ~ fixTwist P' Q'` (inner) iff
    `hermitianStar P ~ hermitianStar P'` and `hermitianStar Q ~ hermitianStar Q'`; no `[NeZero n]`.
  * **`fixTwist_innerConjugate_iff_usignature`**, `fixing_innerConjugate_iff` — iff both unordered
    signatures agree: the fixing branch's complete invariant is the PAIR
    `(usignature P, usignature Q)`.
  * `halfTwist p`, `usignature_halfTwist` — the `±1` twist with `p` plus signs has unordered
    signature `s(2p, 2(n-p))`; `exists_le_half_of_mem_achievable`, `halfPair_inj`.
  * `ClassIndex n = Fin (n/2+1) × Fin (n/2+1) ⊕ Unit`, `classRep`, **`classRep_complete`**,
    **`classRep_injective`**, `card_classIndex` — a complete irredundant family of representatives
    indexed by a type of `(n/2 + 1)² + 1` elements.
  * **`classification_count`** — the count as one statement: `∃ ι` finite of that cardinality and
    `r : ι → StarStrC`, every ⋆-structure inner-conjugate to some `r i`, `r i ~ r j → i = j`.
  * `card_achievable_sq` — `(achievable n ×ˢ achievable n).card = (n/2 + 1)²`;
    `card_classIndex_two` (five classes on `M₂ × M₂`), `card_classIndex_four` (ten on `M₄ × M₄`).

  WHAT IS **NOT** PROVED, said exactly.
  * The count under ALL automorphisms of the product. `InnerConjugate` is inner conjugacy only; the
    factor exchange `(X, Y) ↦ (Y, X)` is an automorphism that is not inner and would identify a
    fixing pair `(u, v)` with `(v, u)`. Nothing here counts the classes it leaves.
  * A quotient. The count is a family of representatives, complete and irredundant; no `Setoid` on
    `StarStrC`, no `Quotient`, no `Fintype` instance on a set of classes is formed.
  * Anything at more than two factors, anything real or quaternionic, and — as the two-spine-links
    block says — anything about the cascade: that the ⋆-structures on `M₂ ⊗ M₂ ≅ M₄` are counted
    does not prefer that factorisation, and the count on the cascade's own algebra is not this one.
  * At `n = 0` the two branches coincide (the algebra is `0`), which is why `[NeZero n]` stands on
    `classRep_complete`, `classRep_injective` and `classification_count`.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import StarStructureSwapConjugacy
import HermitianSignatureClassification

namespace StarStructureFixConjugacy

open Matrix StarStructureProduct StarStructureProductMatrix StarStructureSwapNormalForm
  StarStructureSwapConjugacy StarStructureTwistFibre StarStructureInequivalent
  HermitianSignatureClassification HermitianRealForm

variable {n : ℕ}

/-! ## 1. The fixing normal form as a `StarStrC` -/

/-- **The factor-fixing normal form as a `StarStrC`**: `(X, Y) ↦ (twist P X, twist Q Y)`, built
field by field from `hermitianStar P` and `hermitianStar Q`. Unit 35's `fixing_classification`
produced this map pointwise; here it is an object, so that it can be conjugated. -/
noncomputable def fixTwist (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ)) :
    StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) where
  map p := ((hermitianStar P hP).map p.1, (hermitianStar Q hQ).map p.2)
  map_add p q := by
    refine Prod.ext ?_ ?_
    · exact (hermitianStar P hP).map_add p.1 q.1
    · exact (hermitianStar Q hQ).map_add p.2 q.2
  map_mul p q := by
    refine Prod.ext ?_ ?_
    · exact (hermitianStar P hP).map_mul p.1 q.1
    · exact (hermitianStar Q hQ).map_mul p.2 q.2
  map_involutive p := by
    refine Prod.ext ?_ ?_
    · exact (hermitianStar P hP).map_involutive p.1
    · exact (hermitianStar Q hQ).map_involutive p.2
  map_smul c p := by
    refine Prod.ext ?_ ?_
    · exact (hermitianStar P hP).map_smul c p.1
    · exact (hermitianStar Q hQ).map_smul c p.2

/-- `fixTwist` is the pair of single-factor twists, definitionally. -/
theorem fixTwist_apply (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ))
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    (fixTwist P Q hP hQ).map (X, Y) = (twist P X, twist Q Y) := rfl

/-- Every `fixTwist P Q` fixes the factors, so every Hermitian pair occurs in the fixing branch. -/
theorem fixTwist_fixes (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ)) :
    (fixTwist P Q hP hQ).map (1, 0) = (1, 0) := by
  rw [fixTwist_apply]
  refine Prod.ext ?_ ?_ <;> simp

/-- **FIXING ⟺ A PAIR OF TWISTS**, the mirror of unit 156's `swapping_iff`: `s` fixes the factors
iff it is `fixTwist P Q` (as a map) for Hermitian units `P`, `Q`. -/
theorem fixing_iff [NeZero n]
    (s : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) :
    s.map (1, 0) = (1, 0)
      ↔ ∃ (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ)
          (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
          (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ)),
          ∀ X Y : Matrix (Fin n) (Fin n) ℂ, s.map (X, Y) = (fixTwist P Q hP hQ).map (X, Y) := by
  constructor
  · intro hfix
    obtain ⟨P, Q, hP, hQ, h⟩ := fixing_classification s hfix
    exact ⟨P, Q, hP, hQ, fun X Y => by rw [h, fixTwist_apply]⟩
  · rintro ⟨P, Q, hP, hQ, h⟩
    rw [h, fixTwist_fixes]

/-! ## 2. Units of the product are pairs, and inner conjugacy of two fixing normal forms is
conjugacy factor by factor -/

/-- The unit `(S, T)` of the product — the units of `Mₙ(ℂ) × Mₙ(ℂ)` are exactly such pairs, and
the converse (a unit of the product has unit components) is used by destructuring in
`fixTwist_innerConjugate_iff`. -/
def unitPair (S T : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)ˣ where
  val := ((S : Matrix (Fin n) (Fin n) ℂ), (T : Matrix (Fin n) (Fin n) ℂ))
  inv := (((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ),
    ((T⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
  val_inv := by refine Prod.ext ?_ ?_ <;> simp
  inv_val := by refine Prod.ext ?_ ?_ <;> simp

/-- Two ⋆-structures with the same map are inner-conjugate (by the unit `1`). -/
theorem innerConjugate_of_map_eq
    {s t : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)}
    (h : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, s.map (X, Y) = t.map (X, Y)) :
    InnerConjugate s t :=
  ⟨1, fun p => by obtain ⟨X, Y⟩ := p; simp [h]⟩

/-- **INNER CONJUGACY OF TWO FIXING NORMAL FORMS IS CONJUGACY FACTOR BY FACTOR.** A unit
`U = (a, b)` of the product conjugates the two twists separately, so `fixTwist P Q` and
`fixTwist P' Q'` are inner-conjugate iff `hermitianStar P ~ hermitianStar P'` and
`hermitianStar Q ~ hermitianStar Q'` in unit 71's sense (`StarStructureInequivalent.Conjugate`).
No `[NeZero n]`: this is algebra, not classification. -/
theorem fixTwist_innerConjugate_iff (P Q P' Q' : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ))
    (hP' : (P' : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P' : Matrix (Fin n) (Fin n) ℂ))
    (hQ' : (Q' : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q' : Matrix (Fin n) (Fin n) ℂ)) :
    InnerConjugate (fixTwist P Q hP hQ) (fixTwist P' Q' hP' hQ')
      ↔ Conjugate (hermitianStar P hP) (hermitianStar P' hP')
        ∧ Conjugate (hermitianStar Q hQ) (hermitianStar Q' hQ') := by
  constructor
  · rintro ⟨U, hU⟩
    obtain ⟨⟨a, b⟩, ⟨a', b'⟩, hv, hi⟩ := U
    have ha : a * a' = 1 := congrArg Prod.fst hv
    have hai : a' * a = 1 := congrArg Prod.fst hi
    have hb : b * b' = 1 := congrArg Prod.snd hv
    have hbi : b' * b = 1 := congrArg Prod.snd hi
    refine ⟨⟨Units.mk a a' ha hai, fun X => ?_⟩, ⟨Units.mk b b' hb hbi, fun Y => ?_⟩⟩
    · have h := congrArg Prod.fst (hU (X, 0))
      simpa [fixTwist_apply] using h
    · have h := congrArg Prod.snd (hU (0, Y))
      simpa [fixTwist_apply] using h
  · rintro ⟨⟨S, hS⟩, ⟨T, hT⟩⟩
    refine ⟨unitPair S T, fun p => ?_⟩
    obtain ⟨X, Y⟩ := p
    refine Prod.ext ?_ ?_
    · simpa [fixTwist_apply, unitPair] using hS X
    · simpa [fixTwist_apply, unitPair] using hT Y

/-- **THE FIXING BRANCH'S COMPLETE INVARIANT**: two fixing normal forms are inner-conjugate iff
both unordered signatures agree — unit 75's `conjugate_iff_usignature`, applied to each factor. -/
theorem fixTwist_innerConjugate_iff_usignature [NeZero n] (P Q P' Q' : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ))
    (hP' : (P' : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P' : Matrix (Fin n) (Fin n) ℂ))
    (hQ' : (Q' : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q' : Matrix (Fin n) (Fin n) ℂ)) :
    InnerConjugate (fixTwist P Q hP hQ) (fixTwist P' Q' hP' hQ')
      ↔ usignature (P' : Matrix (Fin n) (Fin n) ℂ) = usignature (P : Matrix (Fin n) (Fin n) ℂ)
        ∧ usignature (Q' : Matrix (Fin n) (Fin n) ℂ)
          = usignature (Q : Matrix (Fin n) (Fin n) ℂ) := by
  rw [fixTwist_innerConjugate_iff, conjugate_iff_usignature, conjugate_iff_usignature]

/-- The same for ANY two fixing ⋆-structures, given their normal forms from
`fixing_classification`: `InnerConjugate s t ↔ usignature P' = usignature P ∧ usignature Q' =
usignature Q`. -/
theorem fixing_innerConjugate_iff [NeZero n]
    {s t : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)}
    (P Q P' Q' : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ))
    (hP' : (P' : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P' : Matrix (Fin n) (Fin n) ℂ))
    (hQ' : (Q' : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q' : Matrix (Fin n) (Fin n) ℂ))
    (hs : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, s.map (X, Y) = (twist P X, twist Q Y))
    (ht : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, t.map (X, Y) = (twist P' X, twist Q' Y)) :
    InnerConjugate s t
      ↔ usignature (P' : Matrix (Fin n) (Fin n) ℂ) = usignature (P : Matrix (Fin n) (Fin n) ℂ)
        ∧ usignature (Q' : Matrix (Fin n) (Fin n) ℂ)
          = usignature (Q : Matrix (Fin n) (Fin n) ℂ) := by
  have hs' : InnerConjugate s (fixTwist P Q hP hQ) :=
    innerConjugate_of_map_eq fun X Y => by rw [hs, fixTwist_apply]
  have ht' : InnerConjugate t (fixTwist P' Q' hP' hQ') :=
    innerConjugate_of_map_eq fun X Y => by rw [ht, fixTwist_apply]
  rw [← fixTwist_innerConjugate_iff_usignature P Q P' Q' hP hQ hP' hQ']
  constructor
  · intro h
    exact innerConjugate_trans (innerConjugate_symm hs') (innerConjugate_trans h ht')
  · intro h
    exact innerConjugate_trans hs' (innerConjugate_trans h (innerConjugate_symm ht'))

/-! ## 3. Representatives and the count -/

/-- The `±1` diagonal twist with `+1` on the first `p` coordinates: unit 75's `setTwist` on the
initial segment, so its unordered signature is `s(2p, 2(n-p))` (`usignature_halfTwist`). -/
noncomputable def halfTwist (p : ℕ) : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  setTwist (Finset.univ.filter fun i : Fin n => i.val < p)

/-- `halfTwist p` is Hermitian, so it presents a ⋆-structure. -/
theorem halfTwist_hermitian (p : ℕ) :
    ((halfTwist p : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
      = ((halfTwist p : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) :=
  setTwist_hermitian _

/-- The initial segment of `Fin n` of length `p ≤ n` has `p` elements
(`Fin.card_filter_val_lt`). -/
theorem card_filter_lt_of_le (p : ℕ) (hp : p ≤ n) :
    (Finset.univ.filter fun i : Fin n => i.val < p).card = p := by
  rw [Fin.card_filter_val_lt, min_eq_right hp]

/-- The unordered signature of `halfTwist p` at `p ≤ n`. -/
theorem usignature_halfTwist (p : ℕ) (hp : p ≤ n) :
    usignature ((halfTwist p : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = s(2 * p, 2 * (n - p)) := by
  rw [halfTwist, usignature, signature_setTwist, card_filter_lt_of_le p hp]

/-- Every achievable unordered signature is `s(2p, 2(n-p))` for a `p ≤ n/2` — the half of unit
75's `card_achievable` argument that this file needs as a statement. -/
theorem exists_le_half_of_mem_achievable {u : Sym2 ℕ} (hu : u ∈ achievable n) :
    ∃ p, p ≤ n / 2 ∧ u = s(2 * p, 2 * (n - p)) := by
  rw [achievable, Finset.mem_image] at hu
  obtain ⟨p, hp, rfl⟩ := hu
  rw [Finset.mem_range] at hp
  by_cases hle : p ≤ n / 2
  · exact ⟨p, hle, rfl⟩
  · refine ⟨n - p, by omega, ?_⟩
    have hnp : n - (n - p) = p := by omega
    rw [hnp, Sym2.eq_swap]

/-- Below `n/2` the parameter is read off the unordered pair. -/
theorem halfPair_inj {p q : ℕ} (hp : p ≤ n / 2) (hq : q ≤ n / 2)
    (h : s(2 * p, 2 * (n - p)) = s(2 * q, 2 * (n - q))) : p = q := by
  rw [Sym2.eq_iff] at h
  omega

/-- **The index of classes**: a pair of half-counts `(p, q)`, both at most `n/2`, for the fixing
branch, and one point for the swapping branch. -/
abbrev ClassIndex (n : ℕ) := Fin (n / 2 + 1) × Fin (n / 2 + 1) ⊕ Unit

/-- **The representatives**: `fixTwist (halfTwist p) (halfTwist q)` on the fixing index, the plain
swap `swapTwist 1 = prodSwapTransposeC` on the swapping point. -/
noncomputable def classRep :
    ClassIndex n → StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)
  | Sum.inl (p, q) =>
      fixTwist (halfTwist p.val) (halfTwist q.val) (halfTwist_hermitian p.val)
        (halfTwist_hermitian q.val)
  | Sum.inr () => swapTwist 1

/-- `classRep` on the fixing index, by definition. -/
theorem classRep_inl (p q : Fin (n / 2 + 1)) :
    classRep (Sum.inl (p, q))
      = fixTwist (halfTwist p.val) (halfTwist q.val) (halfTwist_hermitian p.val)
          (halfTwist_hermitian q.val) := rfl

/-- `classRep` on the swapping point, by definition. -/
theorem classRep_inr : classRep (n := n) (Sum.inr ()) = swapTwist 1 := rfl

/-- **COMPLETENESS**: every ⋆-structure on `Mₙ(ℂ) × Mₙ(ℂ)` is inner-conjugate to a representative.
Fixing: `fixing_classification` gives Hermitian `P`, `Q`; `mem_achievable_of_unit` puts each
unordered signature in `achievable n`, so at some `p, q ≤ n/2`; then
`fixTwist_innerConjugate_iff_usignature`.
Swapping: unit 157's `swapTwist_innerConjugate_one`. -/
theorem classRep_complete [NeZero n]
    (s : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) :
    ∃ i : ClassIndex n, InnerConjugate (classRep i) s := by
  rcases matrixProd_classification_eq s with ⟨P, Q, hP, hQ, h⟩ | ⟨S, hS⟩
  · obtain ⟨p, hp, hup⟩ := exists_le_half_of_mem_achievable (mem_achievable_of_unit P hP)
    obtain ⟨q, hq, huq⟩ := exists_le_half_of_mem_achievable (mem_achievable_of_unit Q hQ)
    refine ⟨Sum.inl (⟨p, by omega⟩, ⟨q, by omega⟩), ?_⟩
    have hs : InnerConjugate (fixTwist P Q hP hQ) s :=
      innerConjugate_of_map_eq fun X Y => by rw [h, fixTwist_apply]
    refine innerConjugate_trans ?_ hs
    rw [classRep_inl, fixTwist_innerConjugate_iff_usignature]
    exact ⟨hup.trans (usignature_halfTwist p (by omega)).symm,
      huq.trans (usignature_halfTwist q (by omega)).symm⟩
  · refine ⟨Sum.inr (), ?_⟩
    have hs : InnerConjugate (swapTwist S) s :=
      innerConjugate_of_map_eq fun X Y => by rw [hS]
    exact innerConjugate_trans (swapTwist_innerConjugate_one S) hs

/-- **IRREDUNDANCY**: two representatives are inner-conjugate only if they are the same index. Two
fixing representatives: equal unordered signatures, so equal half-counts (`halfPair_inj`). A fixing
and a swapping one: never (`not_innerConjugate_of_fixes_of_swaps`). -/
theorem classRep_injective [NeZero n] {i j : ClassIndex n}
    (h : InnerConjugate (classRep i) (classRep j)) : i = j := by
  rcases i with ⟨p, q⟩ | ⟨⟩ <;> rcases j with ⟨p', q'⟩ | ⟨⟩
  · rw [classRep_inl, classRep_inl, fixTwist_innerConjugate_iff_usignature] at h
    obtain ⟨h1, h2⟩ := h
    rw [usignature_halfTwist p'.val (by omega), usignature_halfTwist p.val (by omega)] at h1
    rw [usignature_halfTwist q'.val (by omega), usignature_halfTwist q.val (by omega)] at h2
    have hp := halfPair_inj (by omega) (by omega) h1
    have hq := halfPair_inj (by omega) (by omega) h2
    rw [(Fin.ext hp : p' = p), (Fin.ext hq : q' = q)]
  · exact absurd h
      (not_innerConjugate_of_fixes_of_swaps (fixTwist_fixes _ _ _ _) (swapTwist_swaps 1))
  · exact absurd (innerConjugate_symm h)
      (not_innerConjugate_of_fixes_of_swaps (fixTwist_fixes _ _ _ _) (swapTwist_swaps 1))
  · rfl

/-- The index has `(n/2 + 1)² + 1` elements. -/
theorem card_classIndex : Fintype.card (ClassIndex n) = (n / 2 + 1) ^ 2 + 1 := by
  simp [ClassIndex, sq]

/-- The fixing branch's invariants, as a `Finset`: `(n/2 + 1)²` pairs — the count unit 157's NOT
list said was *not composed*. -/
theorem card_achievable_sq : (achievable n ×ˢ achievable n).card = (n / 2 + 1) ^ 2 := by
  rw [Finset.card_product, card_achievable, sq]

/-- **THE COUNT ON `Mₙ(ℂ) × Mₙ(ℂ)`, `n ≥ 1`: EXACTLY `(n/2 + 1)² + 1` ⋆-STRUCTURES UP TO INNER
CONJUGACY** — a complete and irredundant family of representatives indexed by a finite type of
that cardinality. This is the form of the count; no quotient of the set of ⋆-structures is
formed. -/
theorem classification_count [NeZero n] :
    ∃ (ι : Type) (_ : Fintype ι)
      (r : ι → StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)),
      Fintype.card ι = (n / 2 + 1) ^ 2 + 1
        ∧ (∀ s, ∃ i, InnerConjugate (r i) s)
        ∧ (∀ i j, InnerConjugate (r i) (r j) → i = j) :=
  ⟨ClassIndex n, inferInstance, classRep, card_classIndex, classRep_complete,
    fun _ _ => classRep_injective⟩

/-- `M₂(ℂ) × M₂(ℂ)`: five classes — four fixing (two unordered signatures per factor) and one
swapping. -/
theorem card_classIndex_two : Fintype.card (ClassIndex 2) = 5 := by
  rw [card_classIndex]; norm_num

/-- `M₄(ℂ) × M₄(ℂ)`: ten classes — nine fixing and one swapping. -/
theorem card_classIndex_four : Fintype.card (ClassIndex 4) = 10 := by
  rw [card_classIndex]; norm_num

end StarStructureFixConjugacy
