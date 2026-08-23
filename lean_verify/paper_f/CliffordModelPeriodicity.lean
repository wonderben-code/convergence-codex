/-
  CliffordModelPeriodicity.lean — every model reduces to one of eight, by the eight-fold
  periodicity applied to the family `CliffordSignatureModel` built.

  WHY. `CliffordSignatureModel.clifford_reduce_posDef` / `_negDef` say that every real Clifford
  algebra of a nondegenerate form is `M_{2^k}` over `Cl (sigForm m 0)` or `Cl (sigForm 0 n)`. They
  do not say what those are, and that is the whole of what is left of the real classification.
  This file removes the `m` and leaves `m % 8`.

  THE ROUTE WAS PROBED BEFORE IT WAS TAKEN (`ERRATUM 40`, `ERRATUM 42`).
  `CliffordPeriodicityQuantified.clifford_periodicity_eight` was READ: it takes an arbitrary
  nondegenerate `Q` on `V` and `Q'` on `W`, each carrier in its own universe, with
  `finrank W = finrank V + 8` and `sigPos Q' = sigPos Q + 8`. The model family satisfies both by
  arithmetic — `finrank (sigSpace (n+8) 0) = n + 8` and `sigPos (sigForm (n+8) 0) = n + 8` — so the
  step needs no new mathematics. **What it needs is the tower, and the tower needs a flattening.**

  WHAT IS BUILT.

  * **`matrixPowFlatten`** — `M_m(M_{m^k}(A)) ≃ₐ[ℝ] M_{m^(k+1)}(A)`, for EVERY `m`.
    `CliffordHypTower.matrixTwoPowFlatten` is the case `m = 2` **on the nose**:
    `matrixTwoPowFlatten_eq` is `rfl`, which is the instantiation `ERRATUM 201` asks for and is
    also the check that the generalisation did not quietly change the statement;
  * `clifford_model_periodicity` and `_neg` — the `+8` step inside the model family;
  * **`clifford_model_pow`** and `_neg` — `Cl (sigForm (8k+r) 0) ≃ₐ[ℝ] M_{16^k}(Cl (sigForm r 0))`,
    by induction on `k`;
  * **`clifford_model_mod_eight`** and `_neg` — the same with `k = m / 8` and `r = m % 8`, which is
    the statement one wants: **every definite model is `M_{16^(m/8)}` over one of eight algebras.**
  * `clifford_reduce_mod_eight` — the two chains composed, so that an ARBITRARY nondegenerate real
    form reaches an `m % 8` base in one statement rather than two.

  WHAT IS STILL NOT PROVED, AND IT IS NOW EXACTLY SIXTEEN ALGEBRAS — EIGHT ON EACH SIDE.
  `Cl (sigForm r 0)` and `Cl (sigForm 0 r)` for `r = 0, …, 7`. Every base case this estate has is
  already stated over EVERY form of its dimension and signature, so each one applies to the model
  with no work. **Counted by grepping every `hdim`/`hsig` pair in `paper_f`, not recalled** — a
  first draft of this paragraph said "six of the eight" from memory, silently meant the positive
  side only, and was wrong about the negative one:

  * positive, `(r,0)`: `r = 0` (`clifford_iso_R_of_sig`, dimension `0`, no signature hypothesis),
    `1` (`clifford_iso_split_of_sig`), `2` (`clifford_iso_M2Real_of_sig`), `3`
    (`clifford_iso_pauli_of_sig`), `4` (`clifford_iso_quatFour_of_sig`), `5` (`clifford_five_zero`).
    **`6` and `7` are absent.**
  * negative, `(0,r)`: `r = 0`, `1` (`clifford_iso_C_of_sig`), `2` (`clifford_iso_H_of_sig`),
    `3` (`clifford_iso_quatSplit_of_sig`), `4` (`clifford_iso_M2H_zero_four`).
    **`5`, `6` and `7` are absent.**

  Matching the eleven present cases to the models and naming the five absent ones is the next unit,
  not this one, and no claim is made here about how hard the five are.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import CliffordSignatureModel

namespace CliffordModelPeriodicity

open CliffordPeriodicityQuantified CliffordRealQuantified CliffordRealSignatures
open CliffordHypTower CliffordSignatureModel
open QuadraticForm QuadraticMap

noncomputable section

/-! ## 1. Flattening at an arbitrary size

`CliffordHypTower` needed `M₂(M_{2^k}(A)) ≃ M_{2^(k+1)}(A)` and built exactly that. Nothing in its
proof used the `2`. -/

/-- **`M_m(M_{m^k}(A)) ≃ₐ[ℝ] M_{m^(k+1)}(A)`, for every `m`.** -/
def matrixPowFlatten (A : Type*) [Semiring A] [Algebra ℝ A] (m k : ℕ) :
    Matrix (Fin m) (Fin m) (Matrix (Fin (m ^ k)) (Fin (m ^ k)) A)
      ≃ₐ[ℝ] Matrix (Fin (m ^ (k + 1))) (Fin (m ^ (k + 1))) A :=
  (Matrix.compAlgEquiv (Fin m) (Fin (m ^ k)) A ℝ).trans
    (Matrix.reindexAlgEquiv ℝ A (finProdFinEquiv.trans (finCongr (by ring))))

/-- The generalisation is instantiated, and by `rfl` (`ERRATUM 201`): `matrixTwoPowFlatten` is not
merely *equivalent to* the case `m = 2`, it **is** it. That also checks that generalising did not
change the statement, which is the failure mode a `Nonempty`-level instantiation would hide. -/
theorem matrixTwoPowFlatten_eq (A : Type*) [Semiring A] [Algebra ℝ A] (k : ℕ) :
    matrixTwoPowFlatten A k = matrixPowFlatten A 2 k := rfl

/-! ## 2. The `+8` step inside the model family -/

/-- **Eight more positive directions is sixteen-by-sixteen matrices.** -/
theorem clifford_model_periodicity (n : ℕ) :
    Nonempty (CliffordAlgebra (sigForm (n + 8) 0) ≃ₐ[ℝ]
      Matrix (Fin 16) (Fin 16) (CliffordAlgebra (sigForm n 0))) :=
  clifford_periodicity_eight (sep_sigForm n 0) (sep_sigForm (n + 8) 0)
    (by rw [finrank_sigSpace, finrank_sigSpace])
    (by rw [sigPos_sigForm, sigPos_sigForm])

/-- **The mirror**, on the negative-definite family. -/
theorem clifford_model_periodicity_neg (n : ℕ) :
    Nonempty (CliffordAlgebra (sigForm 0 (n + 8)) ≃ₐ[ℝ]
      Matrix (Fin 16) (Fin 16) (CliffordAlgebra (sigForm 0 n))) :=
  clifford_periodicity_eight_neg (sep_sigForm 0 n) (sep_sigForm 0 (n + 8))
    (by rw [finrank_sigSpace, finrank_sigSpace]; omega)
    (by rw [sigNeg_sigForm, sigNeg_sigForm])

/-! ## 3. The tower -/

/-- **`k` periods.** `Cl (sigForm (8k+r) 0) ≃ₐ[ℝ] M_{16^k}(Cl (sigForm r 0))`. -/
theorem clifford_model_pow (r k : ℕ) :
    Nonempty (CliffordAlgebra (sigForm (8 * k + r) 0) ≃ₐ[ℝ]
      Matrix (Fin (16 ^ k)) (Fin (16 ^ k)) (CliffordAlgebra (sigForm r 0))) := by
  induction k with
  | zero =>
      have h : 8 * 0 + r = r := by omega
      rw [h, pow_zero]
      exact ⟨(matrixFinOneAlgEquiv (CliffordAlgebra (sigForm r 0))).symm⟩
  | succ k ih =>
      obtain ⟨e⟩ := ih
      obtain ⟨p⟩ := clifford_model_periodicity (8 * k + r)
      have h : 8 * (k + 1) + r = 8 * k + r + 8 := by omega
      rw [h]
      exact ⟨(p.trans e.mapMatrix).trans (matrixPowFlatten (CliffordAlgebra (sigForm r 0)) 16 k)⟩

/-- **The mirror.** -/
theorem clifford_model_pow_neg (r k : ℕ) :
    Nonempty (CliffordAlgebra (sigForm 0 (8 * k + r)) ≃ₐ[ℝ]
      Matrix (Fin (16 ^ k)) (Fin (16 ^ k)) (CliffordAlgebra (sigForm 0 r))) := by
  induction k with
  | zero =>
      have h : 8 * 0 + r = r := by omega
      rw [h, pow_zero]
      exact ⟨(matrixFinOneAlgEquiv (CliffordAlgebra (sigForm 0 r))).symm⟩
  | succ k ih =>
      obtain ⟨e⟩ := ih
      obtain ⟨p⟩ := clifford_model_periodicity_neg (8 * k + r)
      have h : 8 * (k + 1) + r = 8 * k + r + 8 := by omega
      rw [h]
      exact ⟨(p.trans e.mapMatrix).trans (matrixPowFlatten (CliffordAlgebra (sigForm 0 r)) 16 k)⟩

/-! ## 4. Every definite model, in terms of eight -/

/-- **EVERY POSITIVE-DEFINITE MODEL IS `M_{16^(m/8)}` OVER ONE OF EIGHT.** -/
theorem clifford_model_mod_eight (m : ℕ) :
    Nonempty (CliffordAlgebra (sigForm m 0) ≃ₐ[ℝ]
      Matrix (Fin (16 ^ (m / 8))) (Fin (16 ^ (m / 8)))
        (CliffordAlgebra (sigForm (m % 8) 0))) := by
  have h : 8 * (m / 8) + m % 8 = m := Nat.div_add_mod m 8
  have hp := clifford_model_pow (m % 8) (m / 8)
  rwa [h] at hp

/-- **The mirror.** -/
theorem clifford_model_mod_eight_neg (n : ℕ) :
    Nonempty (CliffordAlgebra (sigForm 0 n) ≃ₐ[ℝ]
      Matrix (Fin (16 ^ (n / 8))) (Fin (16 ^ (n / 8)))
        (CliffordAlgebra (sigForm 0 (n % 8)))) := by
  have h : 8 * (n / 8) + n % 8 = n := Nat.div_add_mod n 8
  have hp := clifford_model_pow_neg (n % 8) (n / 8)
  rwa [h] at hp

/-! ## 5. The two chains composed

`CliffordSignatureModel` reduces an arbitrary form to a definite model; §4 reduces a definite model
to one of eight. Composing them is what a reader of the classification wants to see, and it is also
where the two matrix sizes multiply. -/

/-- **AN ARBITRARY NONDEGENERATE REAL FORM, ALL THE WAY DOWN**, when it has at least as many
positive directions as negative ones: `Cl Q' ≃ₐ[ℝ] M_{2^q}(M_{16^(d/8)}(Cl (sigForm (d % 8) 0)))`
with `d = sigPos Q' − sigNeg Q'`. The two matrix layers are left unflattened on purpose — the sizes
`2^q` and `16^(d/8)` are the two separate facts, and `matrixPowFlatten` is not the right tool to
merge them because they are powers of different bases. -/
theorem clifford_reduce_mod_eight {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] {Q' : QuadraticForm ℝ W}
    (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft)
    (hle : sigNeg Q' ≤ sigPos Q') :
    Nonempty (CliffordAlgebra Q' ≃ₐ[ℝ]
      Matrix (Fin (2 ^ sigNeg Q')) (Fin (2 ^ sigNeg Q'))
        (Matrix (Fin (16 ^ ((sigPos Q' - sigNeg Q') / 8)))
          (Fin (16 ^ ((sigPos Q' - sigNeg Q') / 8)))
          (CliffordAlgebra (sigForm ((sigPos Q' - sigNeg Q') % 8) 0)))) := by
  obtain ⟨e⟩ := clifford_reduce_posDef hQ' hle
  obtain ⟨f⟩ := clifford_model_mod_eight (sigPos Q' - sigNeg Q')
  exact ⟨e.trans f.mapMatrix⟩

/-- **The mirror**, when the negative directions are at least as many. -/
theorem clifford_reduce_mod_eight_neg {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] {Q' : QuadraticForm ℝ W}
    (hQ' : (QuadraticMap.associated (R := ℝ) Q').SeparatingLeft)
    (hle : sigPos Q' ≤ sigNeg Q') :
    Nonempty (CliffordAlgebra Q' ≃ₐ[ℝ]
      Matrix (Fin (2 ^ sigPos Q')) (Fin (2 ^ sigPos Q'))
        (Matrix (Fin (16 ^ ((sigNeg Q' - sigPos Q') / 8)))
          (Fin (16 ^ ((sigNeg Q' - sigPos Q') / 8)))
          (CliffordAlgebra (sigForm 0 ((sigNeg Q' - sigPos Q') % 8))))) := by
  obtain ⟨e⟩ := clifford_reduce_negDef hQ' hle
  obtain ⟨f⟩ := clifford_model_mod_eight_neg (sigNeg Q' - sigPos Q')
  exact ⟨e.trans f.mapMatrix⟩

end

end CliffordModelPeriodicity
