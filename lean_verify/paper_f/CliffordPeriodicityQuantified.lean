import CliffordPeriodicityEight
import CliffordComplexImmaterial

/-!
# The eight-fold periodicity, quantified over forms

`CliffordPeriodicityEight` proves the periodicity for a **particular** tower,
`Q ⊥ ⟨1,1⟩^⊥⁴`. Its header, `WALLS §W7.2` amendment 9 and `PROGRESS_LOG` entry 32 all say the
same thing about what was missing: that every nondegenerate real form of signature `(p+8, q)` is
isometric to such a tower, so that the isomorphism applies to an arbitrary form and not only to a
built one. **That is this file, and it is one application of a tool the estate already had.**

> **`clifford_periodicity_eight`** — for nondegenerate real `Q` on `V` and `Q'` on `W` with
> `finrank W = finrank V + 8` and `sigPos Q' = sigPos Q + 8`,
> `Cl Q' ≃ₐ[ℝ] M₁₆(Cl Q)`.
>
> **`clifford_periodicity_eight_neg`** — the mirror, with `sigNeg` in place of `sigPos`.

The proof is: the tower is nondegenerate (`separatingLeft_prod` carries nondegeneracy across an
orthogonal sum, and both `⟨1,1⟩` and `⟨−1,−1⟩` are nondegenerate), it has the right dimension and
the right signature (`sigPos_eight`, `sigNeg_eight_neg`), so
`CliffordRealQuantified.cliffordEquiv_of_sigPos_eq` identifies `Cl Q'` with the tower's Clifford
algebra, and `equivEight` finishes.
-/

namespace CliffordPeriodicityQuantified

open CliffordTensorTwo CliffordPeriodicityEight CliffordRealQuantified
open QuadraticMap CliffordRealSignatures
open scoped TensorProduct Quaternion

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ### The two-dimensional factors are nondegenerate -/

theorem sep_N_pos : (QuadraticMap.associated (R := ℝ) (N 1 1)).SeparatingLeft :=
  CliffordRealTwoZero.sep_Q₂₀

theorem sep_N_neg : (QuadraticMap.associated (R := ℝ) (N (-1) (-1))).SeparatingLeft := by
  refine separatingLeft_of_sig ?_
  simp [N]

/-! ### …and the step preserves nondegeneracy -/

theorem sep_Qext_pos {Q : QuadraticForm ℝ V}
    (h : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft) :
    (QuadraticMap.associated (R := ℝ) (Qext Q 1 1)).SeparatingLeft :=
  CliffordComplexImmaterial.separatingLeft_prod h sep_N_pos

theorem sep_Qext_neg {Q : QuadraticForm ℝ V}
    (h : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft) :
    (QuadraticMap.associated (R := ℝ) (Qext Q (-1) (-1))).SeparatingLeft :=
  CliffordComplexImmaterial.separatingLeft_prod h sep_N_neg

/-! ### The eight-fold towers -/

/-- Eight positive directions. -/
abbrev tower (Q : QuadraticForm ℝ V) : QuadraticForm ℝ ((((V × (ℝ × ℝ)) × (ℝ × ℝ)) ×
    (ℝ × ℝ)) × (ℝ × ℝ)) := Qext (Qext (Qext (Qext Q 1 1) 1 1) 1 1) 1 1

/-- Eight negative directions. -/
abbrev towerNeg (Q : QuadraticForm ℝ V) : QuadraticForm ℝ ((((V × (ℝ × ℝ)) × (ℝ × ℝ)) ×
    (ℝ × ℝ)) × (ℝ × ℝ)) := Qext (Qext (Qext (Qext Q (-1) (-1)) (-1) (-1)) (-1) (-1)) (-1) (-1)

theorem sep_tower {Q : QuadraticForm ℝ V}
    (h : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft) :
    (QuadraticMap.associated (R := ℝ) (tower Q)).SeparatingLeft :=
  sep_Qext_pos (sep_Qext_pos (sep_Qext_pos (sep_Qext_pos h)))

theorem sep_towerNeg {Q : QuadraticForm ℝ V}
    (h : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft) :
    (QuadraticMap.associated (R := ℝ) (towerNeg Q)).SeparatingLeft :=
  sep_Qext_neg (sep_Qext_neg (sep_Qext_neg (sep_Qext_neg h)))

variable (V) in
theorem finrank_tower_space [FiniteDimensional ℝ V] :
    Module.finrank ℝ ((((V × (ℝ × ℝ)) × (ℝ × ℝ)) × (ℝ × ℝ)) × (ℝ × ℝ))
      = Module.finrank ℝ V + 8 := by
  simp [Module.finrank_prod]

/-! ### The quantified statements -/

variable [FiniteDimensional ℝ V]

/-- **The eight-fold periodicity, for every form.** Adding `8` to the positive index of a
nondegenerate real form multiplies its Clifford algebra by `M₁₆`. -/
theorem clifford_periodicity_eight {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ W}
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft)
    (hdim : Module.finrank ℝ W = Module.finrank ℝ V + 8)
    (hsig : sigPos Q' = sigPos Q + 8) :
    Nonempty (CliffordAlgebra Q' ≃ₐ[ℝ] Matrix (Fin 16) (Fin 16) (CliffordAlgebra Q)) := by
  obtain ⟨e⟩ := cliffordEquiv_of_sigPos_eq hQ' (sep_tower hQ)
    (by rw [hdim, finrank_tower_space V]) (by rw [hsig, sigPos_eight])
  exact ⟨e.trans (equivEight Q)⟩

/-- **The mirror.** Adding `8` to the negative index does the same. -/
theorem clifford_periodicity_eight_neg {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ W}
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft)
    (hdim : Module.finrank ℝ W = Module.finrank ℝ V + 8)
    (hsig : sigNeg Q' = sigNeg Q + 8) :
    Nonempty (CliffordAlgebra Q' ≃ₐ[ℝ] Matrix (Fin 16) (Fin 16) (CliffordAlgebra Q)) := by
  obtain ⟨e⟩ := cliffordEquiv_of_sigNeg_eq hQ' (sep_towerNeg hQ)
    (by rw [hdim, finrank_tower_space V]) (by rw [hsig, sigNeg_eight_neg])
  exact ⟨e.trans (equivEightNeg Q)⟩

/-! ### The two-step relations, also quantified

These are the same transport applied to `CliffordTensorTwo`'s two relations rather than to the
eight-fold chain, and they matter for a reason that has nothing to do with periodicity:
**they are moves on the diagonal `p − q` that the estate's reach analysis has never included.**
Mathlib's `QuadraticForm.sigPos_neg` and `sigNeg_neg` say `−Q` has signature `(q, p)`, so in
signature terms these read

* `Cl(p+2, q) ≅ M₂(Cl(q, p))` — the diagonal `d = p − q` goes to `2 − d`;
* `Cl(p, q+2) ≅ Cl(q, p) ⊗ ℍ` — the diagonal goes to `−d − 2`.

Neither is `d ↦ d`, which is the only move `WALLS §W7.2`'s reach figure was computed from. -/

/-- **The `(+2, 0)` step, for every form.** -/
theorem clifford_step_pos {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ W}
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft)
    (hdim : Module.finrank ℝ W = Module.finrank ℝ V + 2)
    (hsig : sigPos Q' = sigPos Q + 2) :
    Nonempty (CliffordAlgebra Q' ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) (CliffordAlgebra (-Q))) := by
  obtain ⟨e⟩ := cliffordEquiv_of_sigPos_eq hQ' (sep_Qext_pos hQ)
    (by rw [hdim]; simp [Module.finrank_prod]) (by rw [hsig, sigPos_Qext_pos])
  exact ⟨e.trans (equivMatrixTwo Q)⟩

/-- **The `(0, +2)` step, for every form.** -/
theorem clifford_step_neg {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {Q : QuadraticForm ℝ V} {Q' : QuadraticForm ℝ W}
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft)
    (hdim : Module.finrank ℝ W = Module.finrank ℝ V + 2)
    (hsig : sigNeg Q' = sigNeg Q + 2) :
    Nonempty (CliffordAlgebra Q' ≃ₐ[ℝ] CliffordAlgebra (-Q) ⊗[ℝ] ℍ[ℝ]) := by
  obtain ⟨e⟩ := cliffordEquiv_of_sigNeg_eq hQ' (sep_Qext_neg hQ)
    (by rw [hdim]; simp [Module.finrank_prod]) (by rw [hsig, sigNeg_Qext_neg])
  exact ⟨e.trans (equivQuatTwo Q)⟩

/-! ### A witness that the reach figure's NEGATIVE half was wrong

`WALLS §W7.2` says *"not reachable — every `Cl(p,q)` with `p − q ≥ 5` or `p − q ≤ −4`"*. That
sentence was derived from a move set containing only the hyperbolic step, which fixes `p − q`.
`clifford_step_pos` sends `d ↦ 2 − d`, so from the estate's `Cl(0,3)` — which has `d = −3` and is
`ℍ × ℍ` — it reaches `d = 5`. Here is that case, in full, as a theorem about **every**
nondegenerate real form of dimension `5` with `sigPos = 5`. -/

theorem clifford_five_zero {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (Q' : QuadraticForm ℝ W) (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft)
    (hdim : Module.finrank ℝ W = 5) (hsig : sigPos Q' = 5) :
    Nonempty (CliffordAlgebra Q' ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) (ℍ[ℝ] × ℍ[ℝ])) := by
  have hneg : (QuadraticMap.associated (R := ℝ) (-CliffordRealPauli.Q₃₀)).SeparatingLeft := by
    refine separatingLeft_of_sig ?_
    simp [CliffordRealPauli.sigPos_Q₃₀, CliffordRealPauli.sigNeg_Q₃₀]
  obtain ⟨e⟩ := clifford_step_pos CliffordRealPauli.sep_Q₃₀ hQ'
    (by simp [hdim]) (by rw [hsig, CliffordRealPauli.sigPos_Q₃₀])
  obtain ⟨f⟩ := CliffordRealSplitQuat.clifford_iso_quatSplit_of_sig
    (-CliffordRealPauli.Q₃₀) hneg (by simp) (by simp [CliffordRealPauli.sigNeg_Q₃₀])
  exact ⟨e.trans (AlgEquiv.mapMatrix f)⟩

end

end CliffordPeriodicityQuantified
