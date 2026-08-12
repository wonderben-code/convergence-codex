import GraphMirrorReflection

/-!
# When the completing-the-square bound is tight, and what that gives the odd side

`GraphMirrorReflection` removed the `Even n` restriction from reflection **positivity** by
throwing away the block matrices and completing the square instead. Its engine is
`dotProduct_inv_le`, and it comes with `dotProduct_inv_eq`: *the bound is attained at
`ξ = N⁻¹y`*, recorded there so a reader knows the estimate is not lossy.

`UNLOCK_WATCHLIST`'s odd-side **strictness** item says that route is unavailable to it:

> the same obstruction `GraphMirrorReflection` removed for POSITIVITY, and removed by avoiding
> blocks entirely (completing the square). **Strictness cannot avoid the blocks the same way**:
> it needs the attaining vector, not just the sign.

**The reason given is wrong, and this file says exactly how.** The attaining vector is precisely
what `dotProduct_inv_eq` supplies, and `reflectionPositive_mirror` already *uses* it — that is how
the antisymmetric energy enters as an equality rather than an estimate. What is genuinely missing
is smaller and is supplied here:

> **`dotProduct_inv_eq_iff`** — the bound is tight **if and only if** `ξ = N⁻¹y`. The estate had
> one direction; strictness needs the other, because a null direction is a place where an
> inequality is forced to be tight rather than one where it happens to be.

With it, `reflectionPositive_mirror`'s chain becomes an equality analysis rather than an estimate,
and this file carries that out one step:

> **`reflectedForm_pos_of_ne`** — under the same hypotheses, if the sign-flipped test vector is
> **not** the Green transform of the symmetric part, the reflected form is **strictly** positive.

## What this does not do, and the item stays open

**It does not settle the odd-side strictness item.** That item asks for the converse direction —
to *exhibit* a null direction on an odd box — and this gives a criterion a witness must satisfy,
not a witness. The remaining leg is the one this file makes precise for the first time: find `c`,
supported off the mirror-complement, with `evenify H (N⁻¹ *ᵥ anti θ c) = N⁻¹ *ᵥ sym θ c` **and**
`crossForm G m θ H` vanishing at it. **The measurement the item already records says such a `c`
exists** — every odd box tested is non-strict — so this is a search with a known answer, not a
question. It is **NOT ATTEMPTED** here (`ERRATUM 71` addendum 3): nothing was tried.

**And the three-block route the item maps is not needed for this half.** That route
(`S = [[2(A+B), 2C], [2Cᵀ, D]]`, Schur complement, `Matrix.schur_complement_eq₁₁`) was written
before `GraphMirrorReflection` existed and duplicates work that file already did index-free. The
item is corrected there rather than here.
-/

namespace MirrorNullDirection

open Finset Matrix GraphLaplacian GraphReflection GraphHalfSpace GraphMirrorReflection

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The engine, as a biconditional -/

/-- **THE SQUARE, WITHOUT DISCARDING IT.** `GraphMirrorReflection.dotProduct_inv_le` proves
`0 ≤ ⟪ξ − N⁻¹y, N(ξ − N⁻¹y)⟫` and then throws the square away to keep the inequality. Kept, it is
an identity, and it is what an equality analysis needs. -/
theorem sq_expand {N : Matrix V V ℝ} (hN : N.PosDef) (y ξ : V → ℝ) :
    (ξ - N⁻¹ *ᵥ y) ⬝ᵥ (N *ᵥ (ξ - N⁻¹ *ᵥ y))
      = y ⬝ᵥ (N⁻¹ *ᵥ y) - (2 * (ξ ⬝ᵥ y) - ξ ⬝ᵥ (N *ᵥ ξ)) := by
  classical
  have hdet : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp hN.isUnit
  set z : V → ℝ := N⁻¹ *ᵥ y with hz
  have hNz : N *ᵥ z = y := by
    rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hdet, Matrix.one_mulVec]
  have hsym : z ⬝ᵥ (N *ᵥ ξ) = ξ ⬝ᵥ y := by
    have h1 : z ⬝ᵥ (N *ᵥ ξ) = (N *ᵥ z) ⬝ᵥ ξ := by
      rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, show Nᵀ = N from hN.isHermitian.eq]
    rw [h1, hNz, dotProduct_comm]
  have hzy : z ⬝ᵥ y = y ⬝ᵥ (N⁻¹ *ᵥ y) := by rw [hz, dotProduct_comm]
  rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hNz, hsym, hzy]
  ring

/-- **THE BOUND IS TIGHT EXACTLY AT THE MINIMISER.** The estate had the `←` direction
(`dotProduct_inv_eq`); this is the `→` one, which is the direction a null-direction argument runs
in. Positive-definiteness enters here and nowhere else: a quadratic form that vanishes at a
nonzero vector is not positive definite. -/
theorem dotProduct_inv_eq_iff {N : Matrix V V ℝ} (hN : N.PosDef) (y ξ : V → ℝ) :
    2 * (ξ ⬝ᵥ y) - ξ ⬝ᵥ (N *ᵥ ξ) = y ⬝ᵥ (N⁻¹ *ᵥ y) ↔ ξ = N⁻¹ *ᵥ y := by
  classical
  constructor
  · intro heq
    by_contra hne
    have hsub : ξ - N⁻¹ *ᵥ y ≠ 0 := sub_ne_zero_of_ne hne
    have hpos : 0 < star (ξ - N⁻¹ *ᵥ y) ⬝ᵥ (N *ᵥ (ξ - N⁻¹ *ᵥ y)) :=
      hN.dotProduct_mulVec_pos hsub
    rw [show star (ξ - N⁻¹ *ᵥ y) = ξ - N⁻¹ *ᵥ y from rfl, sq_expand hN y ξ, heq] at hpos
    simp at hpos
  · rintro rfl
    exact dotProduct_inv_eq hN y

/-- **AND SO THE ESTIMATE IS STRICT OFF THE MINIMISER**, which is the form the chain consumes. -/
theorem dotProduct_inv_lt_of_ne {N : Matrix V V ℝ} (hN : N.PosDef) (y ξ : V → ℝ)
    (hne : ξ ≠ N⁻¹ *ᵥ y) :
    2 * (ξ ⬝ᵥ y) - ξ ⬝ᵥ (N *ᵥ ξ) < y ⬝ᵥ (N⁻¹ *ᵥ y) :=
  lt_of_le_of_ne (dotProduct_inv_le hN y ξ) ((dotProduct_inv_eq_iff hN y ξ).not.mpr hne)

/-! ## 2. What that gives the mirror form

`reflectionPositive_mirror` bounds the reflected form below by chaining two facts: the symmetric
energy is bounded by the completing-the-square estimate at the sign-flipped test vector, and the
quadratic term only improves. Making the first strict makes the conclusion strict. -/

variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

/-- **THE REFLECTED FORM IS STRICTLY POSITIVE UNLESS THE TEST VECTOR IS EXACTLY THE MINIMISER.**
Same hypotheses as `reflectionPositive_mirror`, one extra, and a strict conclusion.

*This is a criterion a null direction must satisfy, not a null direction.* It says where to look
and it does not look: the odd-side strictness item's own measurement says a witness exists on
every odd box tested, and finding one is **not attempted here**. -/
theorem reflectedForm_pos_of_ne (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hcross : ∀ w : V → ℝ, crossForm G m θ H w ≤ 0)
    {c : V → ℝ} (hc : ∀ p, p ∉ H → p ∉ Mir → c p = 0)
    (hne : evenify H (GraphLaplacian.green G m *ᵥ GraphReflection.anti θ c)
      ≠ GraphLaplacian.green G m *ᵥ GraphReflection.sym θ c) :
    0 < GraphReflection.reflectedForm G m θ c := by
  classical
  set N := GraphLaplacian.massive G m with hN
  have hNpd : N.PosDef := GraphLaplacian.massive_posDef G hm
  have hNinv : N⁻¹ = GraphLaplacian.green G m := rfl
  set a := GraphReflection.anti θ c with ha
  set s := GraphReflection.sym θ c with hs
  set ξ : V → ℝ := N⁻¹ *ᵥ a with hξdef
  have hξodd : IsOddFun θ ξ := by
    intro p
    have hgreen : ∀ x y, GraphLaplacian.green G m (θ x) (θ y) = GraphLaplacian.green G m x y :=
      fun x y => GraphReflection.green_aut h m x y
    have haodd : ∀ q, a (θ q) = -a q := by
      intro q
      simp only [ha, GraphReflection.anti, h.invol q]
      ring
    simp only [hξdef, hNinv, Matrix.mulVec, dotProduct]
    rw [← Fintype.sum_equiv θ (fun q => GraphLaplacian.green G m (θ p) (θ q) * a (θ q))
      (fun q => GraphLaplacian.green G m (θ p) q * a q) (fun _ => rfl)]
    simp only [hgreen, haodd, mul_neg, Finset.sum_neg_distrib]
  have hAeq : GraphReflection.energy G m a = 2 * (ξ ⬝ᵥ a) - ξ ⬝ᵥ (N *ᵥ ξ) := by
    rw [energy_eq_dotProduct, hξdef]
    exact (dotProduct_inv_eq hNpd a).symm
  -- THE ONE CHANGED STEP: strict, by §1, because the test vector is not the minimiser
  have hSlt : 2 * (evenify H ξ ⬝ᵥ s) - evenify H ξ ⬝ᵥ (N *ᵥ evenify H ξ)
      < GraphReflection.energy G m s := by
    rw [energy_eq_dotProduct]
    exact dotProduct_inv_lt_of_ne hNpd s (evenify H ξ) (by rw [← hNinv] at hne; exact hne)
  have hlin : evenify H ξ ⬝ᵥ s = ξ ⬝ᵥ a := by
    rw [hs, ha, dotProduct_sym (evenify_isEven hM hξodd) c,
      dotProduct_anti hξodd c, dotProduct_evenify_eq hM hξodd hc]
  have hquad : evenify H ξ ⬝ᵥ (N *ᵥ evenify H ξ) ≤ ξ ⬝ᵥ (N *ᵥ ξ) := by
    have hqd := quadDiff (G := G) (m := m) hM hξodd
    have := hcross ξ
    simp only [hN] at hqd ⊢
    linarith
  -- `reflectedForm_eq` gives `4 * reflectedForm = energy s - energy a`, so a STRICT gap
  -- between the two energies is a strict positivity for the form.
  have hElt : GraphReflection.energy G m a < GraphReflection.energy G m s := by
    rw [hlin] at hSlt
    linarith
  have h4 := GraphReflection.reflectedForm_eq (G := G) (m := m) h c
  rw [← hs, ← ha] at h4
  linarith

end MirrorNullDirection
