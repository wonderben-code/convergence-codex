import CliffordModelResidues
import CliffordHyperbolicStep

/-!
# The five moves the reach computation applies, as theorems about the models

`formalisation/reach_closure.py` produces this estate's headline Clifford figure — **3321 states
with `p + q ≤ 80`, `0` undetermined, `0` disagreeing with the classical eightfold table**
(`WALLS §W7.2`, amendment 11). It gets there by indexing algebras by their signature `(p, q)` and
applying five moves, which are these lines of its `named` routine:

```
ans[(p,q)] = _mat(2,  ans[(p-1, q-1)])      -- hyperbolic
ans[(p,q)] = _mat(2,  ans[(q,   p-2)])      -- the (+2, 0) step
ans[(p,q)] = _tensorH(ans[(q-2, p)])        -- the (0, +2) step
ans[(p,q)] = _mat(16, ans[(p-8, q)])        -- eight-fold
ans[(p,q)] = _mat(16, ans[(p,   q-8)])      -- its mirror
```

**Every one of those five was proved in this estate for a general form, and none of them was
stated at the signature index the script uses.** `clifford_step_hyp`, `clifford_step_pos`,
`clifford_step_neg`, `clifford_periodicity_eight` and its mirror are all quantified over an
arbitrary `Q'` with a hypothesis on `sigPos` or `sigNeg`; turning that into a statement about
`sigForm (p+2) q` needs an extra ingredient in every case, and nobody had supplied it. So the
figure rested on a translation that was correct and unwritten.

**This file writes it.** Nothing new about Clifford algebras is proved: each theorem is the
existing quantified step instantiated at the models, composed where needed with
`CliffordModelResidues.clifford_neg_model` — *negating a model transposes its signature*.

## Why it was not done, and why that reason was false

The watch-list block for the quantified classification records the obstruction:

> *"Turning `equivMatrixTwo` into `Cl(p+2,q) ≅ M₂(Cl(q,p))` needs `sigPos (−Q) = sigNeg Q` and its
> twin, which this estate does not have either."*

**Both named blockers are discharged and one was never a blocker.** `sigPos_neg` and `sigNeg_neg`
are **Mathlib** lemmas in the **root** namespace — `CliffordPeriodicityQuantified`'s own header
says so and `ERRATUM 224` is about their spelling — and `clifford_neg_model` has been in the
build since 24 August. The other, `QuadraticMap.neg_prod`, is absent from Mathlib and proved here
as `CliffordPeriodicityEight.neg_prod`. `ERRATUM 262`.

## What is proved

* `clifford_sig_step_hyp` — `Cl(p+1, q+1) ≅ M₂(Cl(p, q))`.
* `clifford_sig_step_pos` — `Cl(p+2, q) ≅ M₂(Cl(q, p))`.
* `clifford_sig_step_neg` — `Cl(p, q+2) ≅ Cl(q, p) ⊗ ℍ`.
* `clifford_sig_periodicity_eight`, `clifford_sig_periodicity_eight_neg` —
  `Cl(p+8, q) ≅ M₁₆(Cl(p, q))` and `Cl(p, q+8) ≅ M₁₆(Cl(p, q))`.

Those five are the script's five, in order.

* `clifford_sig_step_four` — composing the two-steps: `Cl(p+4, q) ≅ M₂(Cl(p, q) ⊗ ℍ)`.
  **This is not a new move**: `d ↦ d − 4` is already in the closure of the move set the figure
  was computed from, and saying otherwise would be a reach claim this file has not earned. What
  is new is the **algebra on the right**, which no theorem here named before.
* `clifford_sig_step_eight`, `quat_matrix_reconcile` — the `+4` step twice, and hence that the two
  routes to `Cl(p+8, q)` agree: `M₂(M₂(A ⊗ ℍ) ⊗ ℍ) ≅ M₁₆(A)` for `A = Cl(p, q)`, every `p, q`. A
  consistency check between two independently built pieces, free by transitivity.

## What is NOT proved

`quat_matrix_reconcile` composes two isomorphisms with a common source, so it exhibits **no map**:
`QuaternionTensor.equivM4` (`ℍ ⊗ ℍ ≅ M₄(ℝ)`) is the classical route and is not what proves it.
It is an existence statement, which is what `Nonempty` says and all it says.

Nothing here is a single classification theorem quantified over `p` and `q`; the eight targets are
different types and that is `ASSUMPTIONS 49`'s presentation decision, untouched. And nothing here
re-derives the figure — it supplies the moves the script applies, at the index it applies them.
-/

namespace CliffordSignatureStep

open CliffordSignatureModel CliffordPeriodicityQuantified CliffordModelResidues
open CliffordHyperbolicStep
open QuadraticForm QuadraticMap
open scoped Quaternion TensorProduct

noncomputable section

/-! ## 1. The five moves, at the signature index -/

/-- **`Cl(p+1, q+1) ≅ M₂(Cl(p, q))`** — the hyperbolic step. `reach_closure.py`'s first line. -/
theorem clifford_sig_step_hyp (p q : ℕ) :
    Nonempty (CliffordAlgebra (sigForm (p + 1) (q + 1)) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) (CliffordAlgebra (sigForm p q))) :=
  clifford_step_hyp (Q := sigForm p q) (Q' := sigForm (p + 1) (q + 1))
    (sep_sigForm p q) (sep_sigForm (p + 1) (q + 1))
    (by rw [finrank_sigSpace, finrank_sigSpace]; omega)
    (by rw [sigPos_sigForm, sigPos_sigForm])

/-- **`Cl(p+2, q) ≅ M₂(Cl(q, p))`**, for every `p` and `q`.

`clifford_step_pos` lands on `Cl(−(sigForm p q))`, and `clifford_neg_model` is exactly the
statement that this is the model of the transposed signature. -/
theorem clifford_sig_step_pos (p q : ℕ) :
    Nonempty (CliffordAlgebra (sigForm (p + 2) q) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) (CliffordAlgebra (sigForm q p))) := by
  obtain ⟨e⟩ := clifford_step_pos (Q := sigForm p q) (Q' := sigForm (p + 2) q)
    (sep_sigForm p q) (sep_sigForm (p + 2) q)
    (by rw [finrank_sigSpace, finrank_sigSpace]; omega)
    (by rw [sigPos_sigForm, sigPos_sigForm])
  obtain ⟨f⟩ := clifford_neg_model p q
  exact ⟨e.trans (AlgEquiv.mapMatrix f)⟩

/-- **`Cl(p, q+2) ≅ Cl(q, p) ⊗ ℍ`**, for every `p` and `q`.

The asymmetry with the positive step is real and not an artefact: `ℍ` is not a matrix algebra
over `ℝ`, so the factor cannot be absorbed — `CliffordTensorTwo.equivQuatTwo`'s docstring says
why, and it is why the script's third line is `_tensorH` and not `_mat`. -/
theorem clifford_sig_step_neg (p q : ℕ) :
    Nonempty (CliffordAlgebra (sigForm p (q + 2)) ≃ₐ[ℝ]
      CliffordAlgebra (sigForm q p) ⊗[ℝ] ℍ[ℝ]) := by
  obtain ⟨e⟩ := clifford_step_neg (Q := sigForm p q) (Q' := sigForm p (q + 2))
    (sep_sigForm p q) (sep_sigForm p (q + 2))
    (by rw [finrank_sigSpace, finrank_sigSpace]; omega)
    (by rw [sigNeg_sigForm, sigNeg_sigForm])
  obtain ⟨f⟩ := clifford_neg_model p q
  exact ⟨e.trans (Algebra.TensorProduct.congr f AlgEquiv.refl)⟩

/-- **`Cl(p+8, q) ≅ M₁₆(Cl(p, q))`** — the eight-fold periodicity at the models. -/
theorem clifford_sig_periodicity_eight (p q : ℕ) :
    Nonempty (CliffordAlgebra (sigForm (p + 8) q) ≃ₐ[ℝ]
      Matrix (Fin 16) (Fin 16) (CliffordAlgebra (sigForm p q))) :=
  clifford_periodicity_eight (Q := sigForm p q) (Q' := sigForm (p + 8) q)
    (sep_sigForm p q) (sep_sigForm (p + 8) q)
    (by rw [finrank_sigSpace, finrank_sigSpace]; omega)
    (by rw [sigPos_sigForm, sigPos_sigForm])

/-- **`Cl(p, q+8) ≅ M₁₆(Cl(p, q))`** — its mirror, the script's fifth line. -/
theorem clifford_sig_periodicity_eight_neg (p q : ℕ) :
    Nonempty (CliffordAlgebra (sigForm p (q + 8)) ≃ₐ[ℝ]
      Matrix (Fin 16) (Fin 16) (CliffordAlgebra (sigForm p q))) :=
  clifford_periodicity_eight_neg (Q := sigForm p q) (Q' := sigForm p (q + 8))
    (sep_sigForm p q) (sep_sigForm p (q + 8))
    (by rw [finrank_sigSpace, finrank_sigSpace]; omega)
    (by rw [sigNeg_sigForm, sigNeg_sigForm])

/-! ## 2. Composing the two-steps: the `+4` relation

Neither two-step alone stays on the diagonal — each transposes the signature. **Two of them
return it.** The composite is not a new *move* (the reach closure already contains `d ↦ d − 4`);
what it adds is the algebra on the right-hand side. -/

/-- **`Cl(p+4, q) ≅ M₂(Cl(p, q) ⊗ ℍ)`**, for every `p` and `q`. -/
theorem clifford_sig_step_four (p q : ℕ) :
    Nonempty (CliffordAlgebra (sigForm (p + 4) q) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) (CliffordAlgebra (sigForm p q) ⊗[ℝ] ℍ[ℝ])) := by
  obtain ⟨e⟩ := clifford_sig_step_pos (p + 2) q
  obtain ⟨f⟩ := clifford_sig_step_neg q p
  have hp : p + 2 + 2 = p + 4 := by omega
  rw [hp] at e
  exact ⟨e.trans (AlgEquiv.mapMatrix f)⟩

/-! ## 3. Two routes to `Cl(p+8, q)`, and they agree -/

/-- **`Cl(p+8, q) ≅ M₂(M₂(Cl(p, q) ⊗ ℍ) ⊗ ℍ)`** — the `+4` step applied twice. -/
theorem clifford_sig_step_eight (p q : ℕ) :
    Nonempty (CliffordAlgebra (sigForm (p + 8) q) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2)
        (Matrix (Fin 2) (Fin 2) (CliffordAlgebra (sigForm p q) ⊗[ℝ] ℍ[ℝ]) ⊗[ℝ] ℍ[ℝ])) := by
  obtain ⟨e⟩ := clifford_sig_step_four (p + 4) q
  obtain ⟨f⟩ := clifford_sig_step_four p q
  have hp : p + 4 + 4 = p + 8 := by omega
  rw [hp] at e
  exact ⟨e.trans (AlgEquiv.mapMatrix (Algebra.TensorProduct.congr f AlgEquiv.refl))⟩

/-- **THE TWO ROUTES AGREE**: `M₂(M₂(A ⊗ ℍ) ⊗ ℍ) ≅ M₁₆(A)` for `A = Cl(p, q)`, every `p` and `q`.

A consistency check between the eight-fold chain and the two-step relations, built three days
apart and never compared. It costs nothing but transitivity through the common source
`Cl(p+8, q)` — and for that reason it exhibits no map. -/
theorem quat_matrix_reconcile (p q : ℕ) :
    Nonempty (Matrix (Fin 2) (Fin 2)
        (Matrix (Fin 2) (Fin 2) (CliffordAlgebra (sigForm p q) ⊗[ℝ] ℍ[ℝ]) ⊗[ℝ] ℍ[ℝ]) ≃ₐ[ℝ]
      Matrix (Fin 16) (Fin 16) (CliffordAlgebra (sigForm p q))) := by
  obtain ⟨e⟩ := clifford_sig_step_eight p q
  obtain ⟨f⟩ := clifford_sig_periodicity_eight p q
  exact ⟨e.symm.trans f⟩

end

end CliffordSignatureStep
