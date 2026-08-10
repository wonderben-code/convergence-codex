/-
  GraphMirrorReflection.lean — reflections that FIX a layer, and the even-side
  restriction removed.

  WHY. Every reflection-positivity result on this wall carries `Even n`, and
  the reason is structural rather than incidental: `GraphHalfSpace.IsHalf`
  says `p ∈ H ↔ θ p ∉ H`, and `IsHalf.no_fixed` turns that into a theorem —
  **a half exists only when the reflection has no fixed point.** On a box of
  odd side the middle layer is fixed, so there is no half, so none of the
  machinery applies. The restriction is honest and it is also the last
  artefact of the machinery on this chain: the mathematics does not need it.

  **THE OBSTACLE WAS THE INDEXING, NOT THE MATHEMATICS.** The engine in
  `GraphReflectionPositive` builds two matrices `A ± B` indexed by `H` and
  compares their inverses in the Loewner order. That works because `IsHalf`
  makes `V = H ⊔ θH`, so a symmetric and an antisymmetric vector are each
  determined by their restriction to `H`. With a fixed layer `Mir` this fails:
  `V = H ⊔ Mir ⊔ θH`, an antisymmetric vector still lives on `H` but a
  symmetric one carries independent values on `Mir`, and the two operators stop
  sharing an index type.

  WHAT THIS FILE DOES INSTEAD. It throws away the block matrices and proves
  reflection positivity by **completing the square**, which never mentions
  the splitting at all:

    §1  `dotProduct_inv_le` — for `N` positive definite,
        `2⟪ξ,y⟫ − ⟪ξ,Nξ⟫ ≤ ⟪y,N⁻¹y⟫`, with equality at `ξ = N⁻¹y`. One line
        of mathematics — `0 ≤ ⟪ξ−N⁻¹y, N(ξ−N⁻¹y)⟫` expanded — and it is
        the whole engine. **Searched for in Mathlib before writing:** the
        nearest thing is `Matrix.schur_complement_eq₁₁`, which performs the
        same completing-the-square move but states it for a BLOCK matrix
        against a `Sum.elim` vector; the index-free inequality is not there.
        Scope searched: every `.lean` under `Mathlib/LinearAlgebra/Matrix/`
        and `Mathlib/Analysis/Matrix.lean`, by shape rather than by expected
        name (ERRATUM 62). Flagged as an upstreaming candidate on that
        basis, not on a failure to find a guessed name.
    §6  the test vector. Take `ξ = G·anti`, which makes the bound an
        equality for the antisymmetric energy (`dotProduct_inv_eq`). Feed the
        SAME `ξ`, sign-flipped off the half, into the bound for the symmetric
        energy. The two pairings agree (§4), the two quadratic forms differ
        by exactly four times the cross-coupling (§5), and the
        cross-coupling is the hypothesis.

  **`Mir` NEVER APPEARS IN THE ESTIMATE.** The sign-flipped test vector
  vanishes on the fixed layer, so the fixed layer contributes nothing to
  either side. That is why the criterion for a mirror reflection is the same
  criterion as for a fixed-point-free one, and it is the substance of this
  file: not a harder theorem with an extra hypothesis, but the same theorem
  with one hypothesis deleted.

  WHAT THIS FILE PROVES:
  1. **`dotProduct_inv_le`** — the variational inequality (§1).
  2. **`IsMirrorHalf`** — the three-way splitting `V = H ⊔ Mir ⊔ θH`, and
     **`isMirrorHalf_of_isHalf`**, which exhibits every existing half as the
     `Mir = ∅` case. The new notion strictly generalises the old one, and that
     is checked rather than asserted.
  3. **`evenify`** and its two properties: it turns an odd function into an
     even one (§3), and it pairs with anything supported on `H ∪ Mir` exactly
     as the original did (§4).
  4. **`quadDiff`** — the sign-flip changes the massive quadratic form by
     precisely `4 ×` the cross-coupling form (§5). Exact identity, no
     inequality.
  5. **`reflectionPositive_mirror`** — reflection positivity for a
     reflection with a fixed layer, from cross-coupling nonpositivity alone
     (§6).
  6. **`reflectionPositive_mirror_of_isHalf`** and
     **`reflectionPositive_of_crossOp_nonpos'`** — the fixed-point-free case
     recovered, and then `GraphReflectionPositive.reflectionPositive_of_crossOp_nonpos`
     RE-PROVED from this file's route, under that theorem's own hypothesis,
     verbatim. **The claim "this gives a second proof of X" is discharged by
     proving X** rather than by asserting the hypotheses match (ERRATUM 48).
     Both proofs are kept: the original goes through the Loewner order on
     `A ± B` and this one never forms those matrices.

  WHAT THIS DOES NOT DO.
  * **It does not remove `Even n` from any existing theorem.** Those state
    `IsHalf`-indexed conclusions and are untouched. What it removes is the
    obstruction to STATING the odd case; the odd box itself is the next unit,
    and until that lands this file's generality is unwitnessed on the box.
  * **No strictness.** The hypothesis is `≤ 0` and the conclusion is `0 ≤`.
    The numerical evidence is that the mirror case is never strict — a fixed
    layer supplies a null direction the way the innermost layer does in
    `BoxNotStrict` — but nothing here proves that.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import GraphReflectionPositive

namespace GraphMirrorReflection

open Finset Matrix GraphLaplacian GraphReflection GraphHalfSpace

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

/-! ## 1. The variational inequality

The only analytic input in the file. For a positive definite `N` the
quadratic `ξ ↦ 2⟪ξ,y⟫ − ⟪ξ,Nξ⟫` is maximised at `ξ = N⁻¹y`, where its value
is `⟪y,N⁻¹y⟫`. Proving the inequality needs no calculus: the difference is a
perfect square.
-/

/-- **COMPLETING THE SQUARE.** For every `ξ`, the linear-minus-quadratic
    expression is bounded by the inverse form, with equality at `ξ = N⁻¹y`
    (`dotProduct_inv_eq`). -/
theorem dotProduct_inv_le {N : Matrix V V ℝ} (hN : N.PosDef) (y ξ : V → ℝ) :
    2 * (ξ ⬝ᵥ y) - ξ ⬝ᵥ (N *ᵥ ξ) ≤ y ⬝ᵥ (N⁻¹ *ᵥ y) := by
  classical
  have hdet : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp hN.isUnit
  set z : V → ℝ := N⁻¹ *ᵥ y with hz
  have hNz : N *ᵥ z = y := by
    rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hdet, Matrix.one_mulVec]
  -- `0 ≤ ⟪ξ − z, N (ξ − z)⟫`
  have hsq : 0 ≤ (ξ - z) ⬝ᵥ (N *ᵥ (ξ - z)) := by
    have := hN.posSemidef.dotProduct_mulVec_nonneg (ξ - z)
    simpa using this
  -- expand it
  have hexp : (ξ - z) ⬝ᵥ (N *ᵥ (ξ - z))
      = ξ ⬝ᵥ (N *ᵥ ξ) - 2 * (ξ ⬝ᵥ y) + y ⬝ᵥ (N⁻¹ *ᵥ y) := by
    have hsym : z ⬝ᵥ (N *ᵥ ξ) = ξ ⬝ᵥ y := by
      have h1 : z ⬝ᵥ (N *ᵥ ξ) = (N *ᵥ z) ⬝ᵥ ξ := by
        rw [dotProduct_mulVec, ← Matrix.mulVec_transpose,
          show Nᵀ = N from hN.isHermitian.eq]
      rw [h1, hNz, dotProduct_comm]
    have hzy : z ⬝ᵥ y = y ⬝ᵥ (N⁻¹ *ᵥ y) := by rw [hz, dotProduct_comm]
    rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hNz,
      hsym, hzy]
    ring
  linarith [hexp ▸ hsq]

/-- The bound of `dotProduct_inv_le` is ATTAINED, so nothing is lost by
    using it. Recorded because a one-sided estimate that is never sharp would
    make §6's argument lossy, and it is not. -/
theorem dotProduct_inv_eq {N : Matrix V V ℝ} (hN : N.PosDef) (y : V → ℝ) :
    2 * ((N⁻¹ *ᵥ y) ⬝ᵥ y) - (N⁻¹ *ᵥ y) ⬝ᵥ (N *ᵥ (N⁻¹ *ᵥ y))
      = y ⬝ᵥ (N⁻¹ *ᵥ y) := by
  classical
  have hdet : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp hN.isUnit
  have hNz : N *ᵥ (N⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hdet, Matrix.one_mulVec]
  rw [hNz, dotProduct_comm (N⁻¹ *ᵥ y) y]
  ring

/-! ## 2. Energies as pairings, and the mirror splitting -/

theorem energy_eq_dotProduct (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (v : V → ℝ) :
    GraphReflection.energy G m v = v ⬝ᵥ (GraphLaplacian.green G m *ᵥ v) := by
  simp only [GraphReflection.energy, GraphReflection.bil, dotProduct, Matrix.mulVec,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- `f` is odd for `θ`. -/
def IsOddFun (θ : V ≃ V) (f : V → ℝ) : Prop := ∀ p, f (θ p) = -f p

/-- `f` is even for `θ`. -/
def IsEvenFun (θ : V ≃ V) (f : V → ℝ) : Prop := ∀ p, f (θ p) = f p

/-- **THE THREE-WAY SPLITTING `V = H ⊔ Mir ⊔ θH`.** `Mir` is exactly the fixed
    set, `H` misses it, and off `Mir` the reflection swaps `H` with its
    complement. `IsHalf` is the case `Mir = ∅` (`isMirrorHalf_of_isHalf`). -/
structure IsMirrorHalf (θ : V ≃ V) (H Mir : Finset V) : Prop where
  /-- `Mir` is precisely the fixed set of `θ`. -/
  fixed : ∀ p, p ∈ Mir ↔ θ p = p
  /-- a site of the half is not on the mirror. -/
  disj : ∀ p ∈ H, p ∉ Mir
  /-- off the mirror, `θ` exchanges the half with its complement. -/
  split : ∀ p, p ∉ Mir → (p ∈ H ↔ θ p ∉ H)

omit [Fintype V] [DecidableEq V] in
/-- **THE NEW NOTION CONTAINS THE OLD ONE.** Every half in the estate's sense
    is a mirror half with an empty mirror — so §6 applies to everything §1–§7
    of `GraphReflectionPositive` applies to, and the generalisation is
    checked rather than claimed. -/
theorem isMirrorHalf_of_isHalf (hH : GraphHalfSpace.IsHalf θ H) :
    IsMirrorHalf θ H (∅ : Finset V) where
  fixed p := by
    simp only [Finset.notMem_empty, false_iff]
    exact hH.no_fixed p
  disj p _ := Finset.notMem_empty p
  split p _ := hH p

variable {ξ : V → ℝ}

omit [Fintype V] [DecidableEq V] in
theorem IsMirrorHalf.notMem_of_mem (hM : IsMirrorHalf θ H Mir) {p : V} (hp : p ∈ H) :
    θ p ∉ H := (hM.split p (hM.disj p hp)).mp hp

omit [Fintype V] [DecidableEq V] in
theorem IsMirrorHalf.mem_of_notMem (hM : IsMirrorHalf θ H Mir) {p : V}
    (hp : p ∉ H) (hMir : p ∉ Mir) : θ p ∈ H := by
  by_contra hc
  exact hp ((hM.split p hMir).mpr hc)

omit [Fintype V] [DecidableEq V] in
/-- An odd function vanishes on the mirror. Not a hypothesis anywhere: it is
    forced, and it is why `Mir` drops out of every estimate below. -/
theorem IsOddFun.eq_zero_on_fixed (hM : IsMirrorHalf θ H Mir) (hξ : IsOddFun θ ξ)
    {p : V} (hp : p ∈ Mir) : ξ p = 0 := by
  have h := hξ p
  rw [(hM.fixed p).mp hp] at h
  linarith

/-! ## 3. The sign flip -/

/-- Flip the sign off the half. On an odd function this produces an even
    one; on the mirror it produces zero, because an odd function is already
    zero there. -/
def evenify (H : Finset V) (ξ : V → ℝ) : V → ℝ := fun p => if p ∈ H then ξ p else -ξ p

omit [Fintype V] in
theorem evenify_of_mem {p : V} (hp : p ∈ H) : evenify H ξ p = ξ p := if_pos hp

omit [Fintype V] in
theorem evenify_of_notMem {p : V} (hp : p ∉ H) : evenify H ξ p = -ξ p := if_neg hp

omit [Fintype V] in
/-- **THE SIGN FLIP TURNS ODD INTO EVEN.** -/
theorem evenify_isEven (hM : IsMirrorHalf θ H Mir) (hξ : IsOddFun θ ξ) :
    IsEvenFun θ (evenify H ξ) := by
  intro p
  by_cases hp : p ∈ H
  · rw [evenify_of_notMem (hM.notMem_of_mem hp), evenify_of_mem hp, hξ p, neg_neg]
  · by_cases hMir : p ∈ Mir
    · rw [(hM.fixed p).mp hMir]
    · rw [evenify_of_mem (hM.mem_of_notMem hp hMir), evenify_of_notMem hp, hξ p]

/-! ## 4. The two pairings agree

The odd test vector pairs with the antisymmetrisation exactly as its
sign-flipped twin pairs with the symmetrisation. This is where the support
hypothesis on `c` is spent, and it is the only place `Mir` could have caused
trouble: it does not, because both functions vanish there.
-/

omit [DecidableEq V] in
private theorem sum_comp_refl (θ : V ≃ V) (f : V → ℝ) :
    ∑ p, f (θ p) = ∑ p, f p :=
  Fintype.sum_equiv θ _ _ fun _ => rfl

omit [DecidableEq V] in
/-- Pairing an odd function against an antisymmetrisation doubles the plain
    pairing. **No involutivity is needed** — only that `θ` is a bijection —
    which is why this and `dotProduct_sym` take none. -/
theorem dotProduct_anti (hξ : IsOddFun θ ξ) (c : V → ℝ) :
    ξ ⬝ᵥ GraphReflection.anti θ c = 2 * (ξ ⬝ᵥ c) := by
  have hmir : ∑ p, ξ p * c (θ p) = -∑ p, ξ p * c p := by
    calc ∑ p, ξ p * c (θ p) = ∑ p, -(ξ (θ p) * c (θ p)) :=
          Finset.sum_congr rfl fun p _ => by rw [hξ p]; ring
      _ = -∑ p, ξ (θ p) * c (θ p) := by rw [Finset.sum_neg_distrib]
      _ = -∑ p, ξ p * c p := by rw [sum_comp_refl θ (fun p => ξ p * c p)]
  simp only [dotProduct, GraphReflection.anti, mul_sub, Finset.sum_sub_distrib, hmir]
  ring

omit [DecidableEq V] in
theorem dotProduct_sym {η : V → ℝ} (hη : IsEvenFun θ η)
    (c : V → ℝ) : η ⬝ᵥ GraphReflection.sym θ c = 2 * (η ⬝ᵥ c) := by
  have hmir : ∑ p, η p * c (θ p) = ∑ p, η p * c p := by
    calc ∑ p, η p * c (θ p) = ∑ p, η (θ p) * c (θ p) :=
          Finset.sum_congr rfl fun p _ => by rw [hη p]
      _ = ∑ p, η p * c p := sum_comp_refl θ (fun p => η p * c p)
  simp only [dotProduct, GraphReflection.sym, mul_add, Finset.sum_add_distrib, hmir]
  ring

/-- **THE SIGN FLIP IS INVISIBLE TO ANYTHING SUPPORTED ON `H ∪ Mir`.** -/
theorem dotProduct_evenify_eq (hM : IsMirrorHalf θ H Mir) (hξ : IsOddFun θ ξ)
    {c : V → ℝ} (hc : ∀ p, p ∉ H → p ∉ Mir → c p = 0) :
    evenify H ξ ⬝ᵥ c = ξ ⬝ᵥ c := by
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p ∈ H
  · rw [evenify_of_mem hp]
  · by_cases hMir : p ∈ Mir
    · rw [evenify_of_notMem hp, hξ.eq_zero_on_fixed hM hMir]; ring
    · rw [hc p hp hMir, mul_zero, mul_zero]

/-! ## 5. The sign flip costs exactly the cross-coupling

An exact identity, not an estimate. `Mir` contributes nothing to either side.
-/

/-- The cross-coupling form: the massive operator between the half and its
    mirror image. Matches `GraphHalfSpace.crossOp` on `H`. -/
noncomputable def crossForm (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (θ : V ≃ V)
    (H : Finset V) (w : V → ℝ) : ℝ :=
  ∑ p ∈ H, ∑ q ∈ H, w p * w q * GraphLaplacian.massive G m p (θ q)

private theorem sum_compl_eq (hM : IsMirrorHalf θ H Mir) (hξ : IsOddFun θ ξ) (p : V) :
    ∑ q ∈ Hᶜ, ξ q * GraphLaplacian.massive G m p q
      = -∑ q ∈ H, ξ q * GraphLaplacian.massive G m p (θ q) := by
  classical
  -- reindex the complement by `θ` onto `H ∪ Mir`
  have hmem : ∀ r : V, r ∈ H ∪ Mir ↔ θ r ∈ Hᶜ := by
    intro r
    simp only [Finset.mem_union, Finset.mem_compl]
    constructor
    · rintro (hr | hr)
      · exact hM.notMem_of_mem hr
      · rw [(hM.fixed r).mp hr]
        exact fun hc => hM.disj r hc hr
    · intro hr
      by_cases hMir : r ∈ Mir
      · exact Or.inr hMir
      · exact Or.inl (by by_contra hc; exact hr (hM.mem_of_notMem hc hMir))
  have hre : ∑ r ∈ H ∪ Mir, ξ (θ r) * GraphLaplacian.massive G m p (θ r)
      = ∑ q ∈ Hᶜ, ξ q * GraphLaplacian.massive G m p q :=
    Finset.sum_equiv θ hmem fun _ _ => rfl
  rw [← hre]
  -- the mirror part vanishes, because an odd function is zero there
  have hsub : ∑ r ∈ H ∪ Mir, ξ (θ r) * GraphLaplacian.massive G m p (θ r)
      = ∑ r ∈ H, ξ (θ r) * GraphLaplacian.massive G m p (θ r) := by
    refine (Finset.sum_subset Finset.subset_union_left fun x hx hxH => ?_).symm
    have hxMir : x ∈ Mir := (Finset.mem_union.mp hx).resolve_left hxH
    rw [(hM.fixed x).mp hxMir, hξ.eq_zero_on_fixed hM hxMir, zero_mul]
  rw [hsub, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun r _ => by rw [hξ r]; ring

/-- The massive form as a double sum, the shape §5 does its bookkeeping in. -/
private theorem dot_massive_eq (u v : V → ℝ) :
    u ⬝ᵥ (GraphLaplacian.massive G m *ᵥ v)
      = ∑ p, ∑ q, u p * v q * GraphLaplacian.massive G m p q := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- Split a double sum over `V × V` into the four blocks cut out by `H`. -/
private theorem sum_split_half (H : Finset V) (f : V → V → ℝ) :
    ∑ p, ∑ q, f p q
      = ((∑ p ∈ H, ∑ q ∈ H, f p q) + (∑ p ∈ H, ∑ q ∈ Hᶜ, f p q))
        + ((∑ p ∈ Hᶜ, ∑ q ∈ H, f p q) + (∑ p ∈ Hᶜ, ∑ q ∈ Hᶜ, f p q)) := by
  classical
  rw [← Finset.sum_add_sum_compl H (fun p => ∑ q, f p q)]
  congr 1 <;>
    · rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ => (Finset.sum_add_sum_compl H (f p)).symm

/-- **THE EXACT COST OF THE SIGN FLIP.** Not an estimate: the sign flip
    changes the massive quadratic form by precisely four times the
    cross-coupling, and the mirror layer contributes nothing. -/
theorem quadDiff (hM : IsMirrorHalf θ H Mir) (hξ : IsOddFun θ ξ) :
    evenify H ξ ⬝ᵥ (GraphLaplacian.massive G m *ᵥ evenify H ξ)
        - ξ ⬝ᵥ (GraphLaplacian.massive G m *ᵥ ξ)
      = 4 * crossForm G m θ H ξ := by
  classical
  set F : V → V → ℝ :=
    fun p q => (evenify H ξ p * evenify H ξ q - ξ p * ξ q) * GraphLaplacian.massive G m p q
    with hF
  have hdiff : evenify H ξ ⬝ᵥ (GraphLaplacian.massive G m *ᵥ evenify H ξ)
      - ξ ⬝ᵥ (GraphLaplacian.massive G m *ᵥ ξ) = ∑ p, ∑ q, F p q := by
    rw [dot_massive_eq, dot_massive_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by simp only [hF]; ring
  -- the two same-side blocks vanish: the sign flip is a global sign there
  have hHH : ∑ p ∈ H, ∑ q ∈ H, F p q = 0 :=
    Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => by
      simp only [hF, evenify_of_mem hp, evenify_of_mem hq]; ring
  have hCC : ∑ p ∈ Hᶜ, ∑ q ∈ Hᶜ, F p q = 0 :=
    Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => by
      simp only [hF, evenify_of_notMem (Finset.mem_compl.mp hp),
        evenify_of_notMem (Finset.mem_compl.mp hq)]
      ring
  -- each mixed block is `−2 ξ ξ M`
  have hHC : ∀ p ∈ H, ∀ q ∈ Hᶜ,
      F p q = -2 * (ξ p * ξ q * GraphLaplacian.massive G m p q) := fun p hp q hq => by
    simp only [hF, evenify_of_mem hp, evenify_of_notMem (Finset.mem_compl.mp hq)]; ring
  have hCH : ∀ p ∈ Hᶜ, ∀ q ∈ H,
      F p q = -2 * (ξ p * ξ q * GraphLaplacian.massive G m p q) := fun p hp q hq => by
    simp only [hF, evenify_of_notMem (Finset.mem_compl.mp hp), evenify_of_mem hq]; ring
  -- and the two mixed blocks agree, by symmetry of the massive operator
  have hmix : ∑ p ∈ Hᶜ, ∑ q ∈ H, F p q = ∑ p ∈ H, ∑ q ∈ Hᶜ, F p q := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
    rw [hCH q hq p hp, hHC p hp q hq,
      show GraphLaplacian.massive G m q p = GraphLaplacian.massive G m p q from
        congrFun (congrFun (GraphLaplacian.massive_isSymm G m) p) q]
    ring
  -- the surviving block, rewritten by the reindexing of §5
  have hrow : ∑ p ∈ H, ∑ q ∈ Hᶜ, F p q = 2 * crossForm G m θ H ξ := by
    rw [crossForm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have h1 : ∑ q ∈ Hᶜ, F p q
        = -2 * ξ p * ∑ q ∈ Hᶜ, ξ q * GraphLaplacian.massive G m p q := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q hq => by rw [hHC p hp q hq]; ring
    have h2 : (2:ℝ) * ∑ q ∈ H, ξ p * ξ q * GraphLaplacian.massive G m p (θ q)
        = 2 * ξ p * ∑ q ∈ H, ξ q * GraphLaplacian.massive G m p (θ q) := by
      simp only [Finset.mul_sum, mul_assoc]
    rw [h1, sum_compl_eq hM hξ p, h2]
    ring
  rw [hdiff, sum_split_half H F, hHH, hCC, hmix, hrow]
  ring

/-- **THE CRITERION, FOR A MIRROR HALF.** If the only cut-crossing edges join
    a site to its own mirror, the cross-coupling form is nonpositive. This is
    `TorusReflection.crossOp_nonpos_of_cross_diag` with `IsHalf` weakened to
    `IsMirrorHalf`, and it is stated here rather than there because it is
    about the splitting and not about any particular graph.

    **ADDED 2026-08-10**, when the torus at odd side needed it: there the
    cross-coupling is NOT zero — the wrap-around edge still crosses the cut —
    but it is diagonal, which is exactly what this consumes. -/
theorem crossForm_nonpos_of_cross_diag (hM : IsMirrorHalf θ H Mir)
    (hcross : ∀ p ∈ H, ∀ q ∈ H, G.Adj p (θ q) → p = q) (w : V → ℝ) :
    crossForm G m θ H w ≤ 0 := by
  classical
  refine Finset.sum_nonpos fun p hp => Finset.sum_nonpos fun q hq => ?_
  have hne : p ≠ θ q := fun hc => hM.notMem_of_mem hq (hc ▸ hp)
  rw [GraphLaplacian.massive_apply, if_neg hne]
  by_cases hpq : p = q
  · subst hpq
    by_cases hadj : G.Adj p (θ p)
    · simp only [if_pos hadj]
      nlinarith [sq_nonneg (w p)]
    · simp [hadj]
  · have : ¬ G.Adj p (θ q) := fun hc => hpq (hcross p hp q hq hc)
    simp [this]

/-! ## 6. Reflection positivity with a mirror

The pieces assemble with no further mathematics. Take the test vector that
makes §1 an equality for the antisymmetric energy; sign-flip it; §4 says the
linear terms are unchanged and §5 says the quadratic term only improves.
-/

/-- **REFLECTION POSITIVITY FOR A REFLECTION THAT FIXES A LAYER.** The
    hypothesis is the same cross-coupling condition as in the fixed-point-free
    case, and the fixed layer `Mir` costs nothing. -/
theorem reflectionPositive_mirror (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hcross : ∀ w : V → ℝ, crossForm G m θ H w ≤ 0)
    {c : V → ℝ} (hc : ∀ p, p ∉ H → p ∉ Mir → c p = 0) :
    0 ≤ GraphReflection.reflectedForm G m θ c := by
  classical
  set N := GraphLaplacian.massive G m with hN
  have hNpd : N.PosDef := GraphLaplacian.massive_posDef G hm
  have hdet : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp hNpd.isUnit
  set a := GraphReflection.anti θ c with ha
  set s := GraphReflection.sym θ c with hs
  set ξ : V → ℝ := N⁻¹ *ᵥ a with hξdef
  -- the test vector is odd, because the Green function commutes with the reflection
  have hξodd : IsOddFun θ ξ := by
    intro p
    have hgreen : ∀ x y, GraphLaplacian.green G m (θ x) (θ y) = GraphLaplacian.green G m x y :=
      fun x y => GraphReflection.green_aut h m x y
    have haodd : ∀ q, a (θ q) = -a q := by
      intro q
      simp only [ha, GraphReflection.anti, h.invol q]
      ring
    have hNinv : N⁻¹ = GraphLaplacian.green G m := rfl
    simp only [hξdef, hNinv, Matrix.mulVec, dotProduct]
    rw [← Fintype.sum_equiv θ (fun q => GraphLaplacian.green G m (θ p) (θ q) * a (θ q))
      (fun q => GraphLaplacian.green G m (θ p) q * a q) (fun _ => rfl)]
    simp only [hgreen, haodd, mul_neg, Finset.sum_neg_distrib]
  -- §1 is an equality for the antisymmetric energy, at this `ξ`
  have hAeq : GraphReflection.energy G m a = 2 * (ξ ⬝ᵥ a) - ξ ⬝ᵥ (N *ᵥ ξ) := by
    rw [energy_eq_dotProduct, hξdef]
    exact (dotProduct_inv_eq hNpd a).symm
  -- §1 is an inequality for the symmetric energy, at the sign-flipped `ξ`
  have hSle : 2 * (evenify H ξ ⬝ᵥ s) - evenify H ξ ⬝ᵥ (N *ᵥ evenify H ξ)
      ≤ GraphReflection.energy G m s := by
    rw [energy_eq_dotProduct]
    exact dotProduct_inv_le hNpd s (evenify H ξ)
  -- §4: the linear terms coincide
  have hlin : evenify H ξ ⬝ᵥ s = ξ ⬝ᵥ a := by
    rw [hs, ha, dotProduct_sym (evenify_isEven hM hξodd) c,
      dotProduct_anti hξodd c, dotProduct_evenify_eq hM hξodd hc]
  -- §5: the quadratic term only improves
  have hquad : evenify H ξ ⬝ᵥ (N *ᵥ evenify H ξ) ≤ ξ ⬝ᵥ (N *ᵥ ξ) := by
    have := quadDiff (G := G) (m := m) hM hξodd
    have hle := hcross ξ
    linarith
  have hEle : GraphReflection.energy G m a ≤ GraphReflection.energy G m s := by
    rw [hlin] at hSle
    linarith
  have h4 := GraphReflection.reflectedForm_eq (G := G) (m := m) h c
  rw [← hs, ← ha] at h4
  linarith

/-- **THE FIXED-POINT-FREE CASE, RE-PROVED.** A second route to
    `GraphReflectionPositive.reflectionPositive_of_crossOp_nonpos`: no
    Loewner order, no block matrices, no matrix inverses beyond the Green
    function itself. Kept alongside the original because the two proofs fail
    in different places when a hypothesis is dropped, and that is worth
    having on the record. -/
theorem reflectionPositive_mirror_of_isHalf (hH : GraphHalfSpace.IsHalf θ H)
    (h : IsRefl G θ) (hm : m ≠ 0) (hcross : ∀ w : V → ℝ, crossForm G m θ H w ≤ 0) :
    GraphReflection.ReflectionPositive G m θ H := by
  intro c hc
  exact reflectionPositive_mirror (Mir := (∅ : Finset V)) (isMirrorHalf_of_isHalf hH) h hm
    hcross (c := c) (fun p hp _ => hc p hp)

/-- **THE ENGINE'S OWN THEOREM, RE-PROVED BY THIS FILE'S ROUTE.** The
    hypothesis is `GraphReflectionPositive.reflectionPositive_of_crossOp_nonpos`'s,
    copied unchanged — subtype-indexed test vectors and `crossOp` rather than
    `massive ∘ θ`. Stating that the two hypotheses "are the same" would be an
    assertion; deriving the conclusion is a check, and this is the check. -/
theorem reflectionPositive_of_crossOp_nonpos' (hH : GraphHalfSpace.IsHalf θ H)
    (h : IsRefl G θ) (hm : m ≠ 0)
    (hB : ∀ w : H → ℝ, ∑ p, ∑ q, w p * w q * GraphHalfSpace.crossOp G m θ ↑p ↑q ≤ 0) :
    GraphReflection.ReflectionPositive G m θ H := by
  refine reflectionPositive_mirror_of_isHalf hH h hm fun w => ?_
  have hcoe : crossForm G m θ H w
      = ∑ p : H, ∑ q : H, w ↑p * w ↑q * GraphHalfSpace.crossOp G m θ ↑p ↑q := by
    rw [crossForm, ← Finset.sum_coe_sort H
      (fun p => ∑ q ∈ H, w p * w q * GraphLaplacian.massive G m p (θ q))]
    exact Finset.sum_congr rfl fun p _ =>
      (Finset.sum_coe_sort H
        (fun q => w ↑p * w q * GraphLaplacian.massive G m ↑p (θ q))).symm
  rw [hcoe]
  exact hB (fun p => w ↑p)

/-! ## 8. Review — the ways this could be hollow

**"Is the mirror case actually harder, or did the estimate just not notice
it?"** It did not notice it, and that is the result rather than a gap in the
argument. The reason is exhibited and not hand-waved: the test vector is odd,
an odd function vanishes on a fixed point (`IsOddFun.eq_zero_on_fixed`), and
the sign flip therefore produces zero on the mirror. So the mirror layer
contributes nothing to the linear term (§4) and nothing to the quadratic term
(§5). **A reader who expected the fixed layer to cost something is right to
be suspicious and wrong on the mathematics**, and the two lemmas are where to
check it.

**"Is the hypothesis vacuous — could `crossForm ≤ 0` be automatic?"** No. For
an unweighted graph the cross entries are `0` or `−1`, which is entrywise
nonpositive but NOT negative semidefinite: two disjoint edges `p—θq` and
`q—θp` with neither `p—θp` nor `q—θq` give the cross block `!![0,-1;-1,0]`,
whose eigenvalues are `±1`. The hypothesis genuinely fails there, and so does
the conclusion. **This was checked numerically before the file was written,
not argued afterwards**, and it is why the criterion is stated as a
hypothesis rather than proved for all graphs.

**"Does the generalisation actually contain the old case, or is it a
different statement wearing the same words?"** `reflectionPositive_of_crossOp_nonpos'`
settles it: the engine's theorem, with the engine's own hypothesis in the
engine's own vocabulary, follows from §6. Nothing was reformulated to make
the containment work.

**"§1 is an inequality — is anything lost?"** No: `dotProduct_inv_eq` says
the bound is attained, and §6 attains it on the antisymmetric side by
construction. What is one-sided is the SYMMETRIC side, where the sign-flipped
vector is a guess rather than the optimum — and §5 says the cost of that
guess is exactly the cross-coupling, which the hypothesis controls. **The
slack is named and it is the hypothesis**, which is the only honest place for
it to be.

**"What is still restricted?"** The graph is finite, the field is free and
Gaussian, `m ≠ 0` is genuinely needed (at `m = 0` the massive operator is
singular and `green` does not exist), and — the live one — **no instance is
supplied**. `IsMirrorHalf` has exactly one witness in the estate, the empty
mirror, which is the old case. Until an odd-side box is exhibited, everything
above is a theorem about a hypothesis nothing is yet known to satisfy
non-trivially. That is the next unit and it is written down here so the chain
is not left dangling.
-/

end GraphMirrorReflection
