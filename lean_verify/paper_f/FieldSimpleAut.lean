import FieldSignGroup
import FieldAutInvariance

/-!
# A fact about GRAPHS, out of the field's symmetry group: at a simple spectrum every automorphism
is an involution

An hour ago the count `2^|V|` and the group `(ℤ/2)^V` were generalised off the line to any graph
whose propagator has a **simple spectrum**, and the item filed alongside asked for a
**characterisation** of such graphs rather than another example. This is not that characterisation.
It is the first thing the generalisation buys: **a statement about graphs, derived from the
symmetry group of the field on them.**

## What is proved

**`trans_self_of_mem_symmetries`** — **the symmetry group has exponent two.** At a simple spectrum
every isometric symmetry is a sign pattern (`FieldSimpleCriterion.gaussianField_map_iff_signs` and
`exists_signIsometry_eq`), and a sign pattern applied twice is the identity
(`FieldSignGroup.signIsometry_trans_self`).

**`eq_of_permField_trans_self`** — a vertex permutation whose action on field configurations
squares to the identity is itself an involution. Evaluated at a single indicator, by the idiom
`FieldSignFlip.signFlip_ne_permField` uses. **Takes no mass, no graph and no `[DecidableEq V]`.**

**`graphAut_involutive`** — **SO ON A GRAPH WHOSE PROPAGATOR HAS A SIMPLE SPECTRUM, EVERY
AUTOMORPHISM IS AN INVOLUTION.** A graph automorphism acts on the field
(`FieldAutInvariance.gaussianField_map_perm`), hence lands in the symmetry group, hence squares to
the identity there, hence squares to the identity as a permutation.

**`graphAut_involutive_line`** — and the line is the instance: every automorphism of a path graph
is an involution.

## What is NOT here

**THIS IS THE PROPAGATOR'S SPECTRUM, NOT THE LAPLACIAN'S.** The classical statement of this fact is
about the **Laplacian** or **adjacency** spectrum. Those hypotheses are equivalent to this one —
`green` is `(L + m²)⁻¹` and `t ↦ (t + m²)⁻¹` is injective — **and that equivalence is not proved
here.** Making it a theorem means relating `Matrix.IsHermitian.eigenvalues` of `green` to those of
`G.lapMatrix ℝ`, which is the index-matching `FieldSimpleCriterion` found a way *around* rather than
through. Not attempted, no cost claimed (`ERRATUM 246`).

**IT BOUNDS THE EXPONENT; IT DOES NOT COMPUTE `Aut G`.** Nothing here counts automorphisms, and
nothing says a graph with a simple spectrum has few of them — only that each one squares to the
identity. A graph with `2^k` commuting involutions is not excluded by anything here.

**THE EMBEDDING OF `Aut G` INTO THE SYMMETRY GROUP IS NOT SHOWN INJECTIVE.** `permField` carries
automorphisms into the symmetries, and **that it is injective is not proved**, so no statement of
the form *`Aut G` is a subgroup of `(ℤ/2)^V`* is made here — which is what would give a bound on the
number of automorphisms rather than on their order.

**AND THE SIMPLE-SPECTRUM HYPOTHESIS IS STILL DISCHARGED ONLY ON THE LINE.**
`FieldSimpleCriterion.eigenvalues_injective_line` remains the estate's only proof that any graph has
one, so `graphAut_involutive_line` is the only graph this bites on — the same position recorded on
`UNLOCK_WATCHLIST` an hour ago.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): a non-zero mass is taken by
`trans_self_of_mem_symmetries`, `graphAut_involutive` and `graphAut_involutive_line` — **three of
the four**. **Simplicity of the spectrum** is taken by the first two; `graphAut_involutive_line`
does not take it but **discharges** it. `eq_of_permField_trans_self` takes none of them and `omit`s
`[DecidableEq V]`: it is a statement about a permutation and its action, with no field in it.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldSimpleAut

open Matrix GraphLaplacian FieldSimpleSpectrum FieldSimpleCriterion FieldLineCount
  FieldSignGroup FieldAutInvariance MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. At a simple spectrum every symmetry is an involution -/

/-- **THE SYMMETRY GROUP HAS EXPONENT TWO.** -/
theorem trans_self_of_mem_symmetries (hm : m ≠ 0) (hH : (green G m).IsHermitian)
    (hsimple : Function.Injective hH.eigenvalues)
    {T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V} (hT : T ∈ symmetries G m) :
    T.trans T = LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ V) := by
  obtain ⟨s, hs⟩ := exists_signIsometry_eq hH
    ((gaussianField_map_iff_signs hm hH hsimple T).mp hT)
  rw [← hs]
  exact signIsometry_trans_self hH s

/-! ## 2. A vertex permutation whose field action is trivial is trivial -/

omit [DecidableEq V] in
theorem eq_of_permField_trans_self {θ : V ≃ V}
    (h : (permField θ).trans (permField θ)
      = LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ V)) (p : V) :
    θ.symm (θ.symm p) = p := by
  classical
  by_cases hpq : p = θ.symm (θ.symm p)
  · exact hpq.symm
  · exfalso
    have hfd := DFunLike.congr_fun h
      (WithLp.toLp 2 (Pi.single (θ.symm (θ.symm p)) (1 : ℝ)) : EuclideanSpace ℝ V)
    have hval := congrFun (congrArg (fun x : EuclideanSpace ℝ V => WithLp.ofLp x) hfd) p
    dsimp only at hval
    rw [LinearIsometryEquiv.trans_apply, permField_apply, permField_apply] at hval
    simp only [Pi.single_eq_same, PiLp.toLp_single, LinearIsometryEquiv.coe_refl, id_eq,
      PiLp.single_apply, left_eq_ite_iff, one_ne_zero, imp_false, Decidable.not_not] at hval
    exact hpq hval

/-! ## 3. So every graph automorphism is an involution -/

/-- **ON A GRAPH WHOSE PROPAGATOR HAS A SIMPLE SPECTRUM, EVERY AUTOMORPHISM IS AN INVOLUTION.** -/
theorem graphAut_involutive (hm : m ≠ 0) (hH : (green G m).IsHermitian)
    (hsimple : Function.Injective hH.eigenvalues) {θ : V ≃ V} (hθ : IsGraphAut G θ) (p : V) :
    θ (θ p) = p := by
  have hmem : permField θ ∈ symmetries G m := gaussianField_map_perm hθ hm
  have hinv := eq_of_permField_trans_self (trans_self_of_mem_symmetries hm hH hsimple hmem)
  have h1 : θ.symm (θ.symm (θ (θ p))) = p := by
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [hinv (θ (θ p))] at h1
  exact h1

open BoxGraph in
/-- **THE LINE IS THE INSTANCE**: every automorphism of a path graph is an involution. -/
theorem graphAut_involutive_line {k : ℕ} {mass : ℝ} (hmass : mass ≠ 0)
    {θ : Site 1 (k + 1) ≃ Site 1 (k + 1)} (hθ : IsGraphAut (boxGraph 1 (k + 1)) θ)
    (p : Site 1 (k + 1)) : θ (θ p) = p :=
  graphAut_involutive hmass (green_posDef (boxGraph 1 (k + 1)) hmass).isHermitian
    (eigenvalues_injective_line hmass (green_posDef (boxGraph 1 (k + 1)) hmass).isHermitian) hθ p

end FieldSimpleAut
