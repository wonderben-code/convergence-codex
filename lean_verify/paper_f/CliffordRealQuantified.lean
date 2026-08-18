import CliffordRealDiagonals
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# The converse of Sylvester's law, and the real Clifford results quantified by signature

`CliffordRealDiagonals` ends with a paragraph saying what it does **not** do: its isomorphisms are
stated at *named* forms, and turning them into statements about *every* real form of a given
signature would need Sylvester's law — which Mathlib has, and which that file does not apply. This
file applies it.

## What is proved

Mathlib supplies both halves of the forward direction: every nondegenerate real form is equivalent
to a `±1`-weighted sum of squares (`QuadraticForm.equivalent_one_neg_one_weighted_sum_squared`),
and the number of positive weights is an invariant of the equivalence class
(`QuadraticForm.sigPos_of_equiv_weightedSumSquares`). It does **not** supply the step back:

> **`equivalent_of_sigPos_eq`** — two nondegenerate real quadratic forms on finite-dimensional
> spaces of equal dimension, with equal `sigPos`, are `Equivalent`.

That is the converse of Sylvester's law, and the whole of its content is a permutation:
`exists_perm_comp_eq` says two `±1` weight vectors with the same number of `+1`s differ by a
reindexing of coordinates, and `reindexIsometry` says reindexing is an isometry. Everything else
is transport.

Composing with `CliffordAlgebra.equivOfIsometry` gives the statement the previous file could not
make:

> **`cliffordEquiv_of_sigPos_eq`** — the isomorphism class of a real Clifford algebra depends only
> on the dimension and the signature of its form, not on the form.

## What this does NOT do

**It does not move the wall.** `WALLS §W7.2` records the wall as the four residue classes
`p − q ≡ 1, 3, 4, 5`, which have no base case at all. Quantification widens the binder on the
diagonals already reachable and reaches no new one. Nothing here supplies a base case.

**It does not compute the signature of any named form.** The results below take `sigPos` as a
*hypothesis*. Connecting them to `equivM2R`, `equivM2C`, `equivM4H` and `equivM8R` needs the
signature of `QextHyp` — that `Qhyp = CliffordAlgebraQuaternion.Q 1 (-1)` contributes `(1,1)` and
that signatures add across `QuadraticMap.prod` — and neither is proved here. That is a separate
arithmetic step and it is recorded as such rather than assumed.

**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordRealQuantified

open QuadraticForm QuadraticMap

noncomputable section

/-! ## Reindexing is an isometry -/

/-- Precomposing the coordinates with an equivalence carries a weighted sum of squares to the
weighted sum of squares of the reindexed weights. -/
def reindexIsometry {ι κ : Type*} [Fintype ι] [Fintype κ] (w : ι → ℝ) (σ : κ ≃ ι) :
    (weightedSumSquares ℝ w).IsometryEquiv (weightedSumSquares ℝ (w ∘ σ)) where
  __ := LinearEquiv.funCongrLeft ℝ ℝ σ
  map_app' x := by
    simp only [weightedSumSquares_apply, smul_eq_mul, Function.comp_apply]
    exact σ.sum_comp fun i => w i * (x i * x i)

/-! ## The permutation

Two `±1` vectors with the same number of `+1`s differ by a permutation. This is the entire content
of the converse of Sylvester's law. -/

variable {n : ℕ}

/-- Two `±1`-valued weight vectors with the same number of positive entries differ by a
permutation of the index set. Built from the two fibre bijections and `Equiv.sumCompl`. -/
theorem exists_perm_comp_eq {w v : Fin n → ℝ}
    (hw : ∀ i, w i = -1 ∨ w i = 1) (hv : ∀ i, v i = -1 ∨ v i = 1)
    (hcard : Fintype.card {i // 0 < w i} = Fintype.card {i // 0 < v i}) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, v (σ i) = w i := by
  have hcompl : Fintype.card {i // ¬ (0 < w i)} = Fintype.card {i // ¬ (0 < v i)} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hcard]
  set e := Fintype.equivOfCardEq hcard with he
  set e' := Fintype.equivOfCardEq hcompl with he'
  refine ⟨(Equiv.sumCompl fun i => 0 < w i).symm.trans
    ((e.sumCongr e').trans (Equiv.sumCompl fun i => 0 < v i)), fun i => ?_⟩
  by_cases hi : 0 < w i
  · have hσ : ((Equiv.sumCompl fun i => 0 < w i).symm.trans
        ((e.sumCongr e').trans (Equiv.sumCompl fun i => 0 < v i))) i
        = (e ⟨i, hi⟩ : Fin n) := by
      rw [Equiv.trans_apply, Equiv.trans_apply,
        Equiv.sumCompl_symm_apply_of_pos (p := fun i => 0 < w i) hi,
        Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    have hvv : v (e ⟨i, hi⟩ : Fin n) = 1 := by
      have h1 : (0:ℝ) < v (e ⟨i, hi⟩ : Fin n) := (e ⟨i, hi⟩).2
      rcases hv ((e ⟨i, hi⟩ : Fin n)) with h | h
      · rw [h] at h1; exact absurd h1 (by norm_num)
      · exact h
    have hww : w i = 1 := by
      rcases hw i with h | h
      · rw [h] at hi; exact absurd hi (by norm_num)
      · exact h
    rw [hσ, hvv, hww]
  · have hσ : ((Equiv.sumCompl fun i => 0 < w i).symm.trans
        ((e.sumCongr e').trans (Equiv.sumCompl fun i => 0 < v i))) i
        = (e' ⟨i, hi⟩ : Fin n) := by
      rw [Equiv.trans_apply, Equiv.trans_apply,
        Equiv.sumCompl_symm_apply_of_neg (p := fun i => 0 < w i) hi,
        Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    have hvv : v (e' ⟨i, hi⟩ : Fin n) = -1 := by
      have h1 : ¬ (0:ℝ) < v (e' ⟨i, hi⟩ : Fin n) := (e' ⟨i, hi⟩).2
      rcases hv ((e' ⟨i, hi⟩ : Fin n)) with h | h
      · exact h
      · rw [h] at h1; exact absurd (by norm_num : (0:ℝ) < 1) h1
    have hww : w i = -1 := by
      rcases hw i with h | h
      · exact h
      · rw [h] at hi; exact absurd (by norm_num : (0:ℝ) < 1) hi
    rw [hσ, hvv, hww]

/-- The positive-weight count as a `Fintype.card`, which is the shape `exists_perm_comp_eq`
consumes; `sigPos` states it as a `Set.ncard`. Stated over an arbitrary finite index type because
`SignatureArithmetic` needs it on a sum type. -/
theorem ncard_eq_card_pos' {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    {i | 0 < w i}.ncard = Fintype.card {i // 0 < w i} := by
  classical
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  exact Fintype.card_congr (Equiv.refl _)

/-- The `Fin n` case, which is the shape the permutation lemma consumes. -/
theorem ncard_eq_card_pos (w : Fin n → ℝ) :
    {i | 0 < w i}.ncard = Fintype.card {i // 0 < w i} := ncard_eq_card_pos' w

/-! ## The converse of Sylvester's law -/

/-- **Converse of Sylvester's law of inertia.** Two nondegenerate real quadratic forms on
finite-dimensional spaces of the same dimension, with the same `sigPos`, are equivalent.

Mathlib has the normal form and the invariance of the count; this is the step back from equal
invariants to equivalent forms, and it is the permutation of `exists_perm_comp_eq`. -/
theorem equivalent_of_sigPos_eq {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ W}
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W)
    (hsig : sigPos Q = sigPos Q') :
    Q.Equivalent Q' := by
  obtain ⟨w, hw, hwe⟩ := Q.equivalent_one_neg_one_weighted_sum_squared hQ
  obtain ⟨v, hv, hve⟩ := Q'.equivalent_one_neg_one_weighted_sum_squared hQ'
  -- move `w`'s index type onto `W`'s dimension
  set τ : Fin (Module.finrank ℝ W) ≃ Fin (Module.finrank ℝ V) := finCongr hdim.symm with hτ
  set w' : Fin (Module.finrank ℝ W) → ℝ := w ∘ τ with hw'def
  have hw' : ∀ j, w' j = -1 ∨ w' j = 1 := fun j => hw _
  have hreindex : (weightedSumSquares ℝ w).Equivalent (weightedSumSquares ℝ w') :=
    ⟨reindexIsometry w τ⟩
  have hQw' : Q.Equivalent (weightedSumSquares ℝ w') := hwe.trans hreindex
  -- the two counts agree
  have h1 : sigPos Q = {i | 0 < w' i}.ncard := sigPos_of_equiv_weightedSumSquares hQw'
  have h2 : sigPos Q' = {i | 0 < v i}.ncard := sigPos_of_equiv_weightedSumSquares hve
  have hcard : Fintype.card {i // 0 < w' i} = Fintype.card {i // 0 < v i} := by
    rw [← ncard_eq_card_pos, ← ncard_eq_card_pos, ← h1, ← h2, hsig]
  obtain ⟨σ, hσ⟩ := exists_perm_comp_eq hw' hv hcard
  have hvσ : v ∘ σ = w' := funext hσ
  have hfin : (weightedSumSquares ℝ w').Equivalent (weightedSumSquares ℝ v) := by
    refine ⟨?_⟩
    have := reindexIsometry v σ
    rw [hvσ] at this
    exact this.symm
  exact hQw'.trans (hfin.trans hve.symm)

/-! ## Transport to the Clifford algebra -/

/-- **The isomorphism class of a real Clifford algebra depends only on the dimension and the
signature of its form.** This is the statement `CliffordRealDiagonals` records as unavailable to
it, and the reason it was unavailable was `equivalent_of_sigPos_eq`. -/
theorem cliffordEquiv_of_sigPos_eq {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ W}
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W)
    (hsig : sigPos Q = sigPos Q') :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] CliffordAlgebra Q') := by
  obtain ⟨i⟩ := equivalent_of_sigPos_eq hQ hQ' hdim hsig
  exact ⟨CliffordAlgebra.equivOfIsometry i⟩

/-- A nondegenerate form has trivial radical, so the radical term in Sylvester's dimension count
drops. Stated separately because it is what lets `cliffordEquiv_of_sigNeg_eq` below take
nondegeneracy as its only hypothesis rather than nondegeneracy *and* a vanishing radical. -/
theorem finrank_radical_eq_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : QuadraticForm ℝ V} (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft) :
    Module.finrank ℝ Q.radical = 0 := by
  rw [QuadraticMap.radical_eq_ker_associated, LinearMap.separatingLeft_iff_ker_eq_bot.mp hQ]
  exact finrank_bot ℝ V

/-- The same statement with `sigNeg` in place of `sigPos`: for nondegenerate forms the two
determine each other once the dimension is fixed, so either may be quoted.

The vanishing of the radical is **derived** from nondegeneracy rather than assumed — an earlier
draft carried it as two extra hypotheses, which `finrank_radical_eq_zero` makes redundant. -/
theorem cliffordEquiv_of_sigNeg_eq {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ W}
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W)
    (hsig : sigNeg Q = sigNeg Q') :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] CliffordAlgebra Q') := by
  refine cliffordEquiv_of_sigPos_eq hQ hQ' hdim ?_
  have e1 := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  have e2 := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q')
  rw [finrank_radical_eq_zero hQ] at e1
  rw [finrank_radical_eq_zero hQ'] at e2
  omega

end

end CliffordRealQuantified
