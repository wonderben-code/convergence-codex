/-
  ToyTripleIsKOSixAtOne.lean — the coordinate permutation carrying `ConnesNCG`'s toy onto
  `KOSixSpectralTriple` at `n = 1`; and the KO-dimension is a property of the real structure, not
  of the operators: the toy's own `(γ, D)` carry BOTH a KO-6 and a KO-0 real structure.

  SPINE L18 (spectral triple, PARTIAL) — the Caesar order's item 5, *`toy_triple_is_kosix_at_one`:
  the coordinate permutation carrying `ConnesNCG`'s toy onto `KOSixSpectralTriple` at `n = 1`,
  retiring the KO-0 record as an object rather than as a claim* — called **still unbuilt** by the
  20 September re-count and by `KOSixAlgebraAction`'s NOT list. Hardening unit 155, 2026-09-20.

  WHY. `ConnesNCG.lean` (July) has a `4 × 4` chirality `diag(1, 1, −1, −1)` and a Dirac operator
  `diracOp m` pairing coordinates `0 ↔ 2` and `1 ↔ 3`, and a data record `cascade_ko_signs =
  (+1, +1, +1)` — KO-dimension 0 — justified in prose by *"real structure = transpose"*, a `J`
  that file never defines (`grep -n 'def.*J' paper_f/ConnesNCG.lean` → nothing). Its reconciliation
  note says the toy's `J` is the non-physical one and that a `J` with `Jγ = −γJ` is OPEN.
  `KOSixSpectralTriple` (September) has, at every `n`, a four-block space with `gamma`, `D M`, and
  an antiunitary `J` of KO-dimension 6. **At `n = 1` the two files' operators are the same
  operators**, up to a permutation of the four coordinates — and once that is a theorem, the KO-6
  `J` transports to the toy's space and sits beside the KO-0 one on the same `(γ, D)`.

  WHAT IS PROVED.
  * `toToy : Hf 1 → (Fin 4 → ℂ)` and `ofToy`, mutually inverse (`toToy_bijective`): toy coordinate
    `0 ↤` particle-left, `1 ↤` antiparticle-right, `2 ↤` particle-right, `3 ↤` antiparticle-left.
  * `toToy_gamma` — `toToy (gamma v) = chiralityOp *ᵥ toToy v`, for every `v`, no hypothesis.
  * `toToy_D` — `toToy (D (one m) v) = diracOp m *ᵥ toToy v` for **real** `m` (`conj m = m`), and
    `toToy_D_iff`: that hypothesis is exactly what the identification needs — the KO-6 `D` acts by
    `conj m` on two of the four blocks and the toy's by `m` on all four.
  * `diracOp_isHermitian_iff` — the same hypothesis is exactly self-adjointness of the toy's `D`;
    `ConnesNCG.dirac_symmetric` (`Dᵀ = D`) holds for every `m` and is the weaker statement.
  * `Jtoy` — antidiagonal conjugation `w ↦ ![conj w₃, conj w₂, conj w₁, conj w₀]`, which is
    `KOSixSpectralTriple.J` in the toy's coordinates (`toToy_J`); **`toy_ko_six_signs`**: on
    `chiralityOp` and `diracOp m` (real `m`) it is an involution, commutes with `D` and
    anticommutes with `γ` — `(ε, ε', ε'') = (+1, +1, −1)`, the table `sm_ko_signs` records.
  * `Jzero` — entrywise conjugation, the `J` the toy's prose meant; **`toy_ko_zero_signs`**: on the
    SAME two operators it is an involution commuting with both — `(+1, +1, +1)`, the table
    `cascade_ko_signs` records. So the KO-0 record is now the sign table of a defined map, and the
    KO-dimension of the toy is a choice of `J`, with both choices realised.
  * **`toy_triple_is_kosix_at_one`** — the four clauses together: bijection, `gamma`, `D`, `J`.

  WHAT IS **NOT** PROVED, said exactly.
  * Anything at `n ≥ 2`, or about the cascade's `M₄(ℂ)`, `CascadeHilbert` or the 96: this is the
    `n = 1` identification the Caesar item asked for and nothing larger (L18's standing residue).
  * An algebra action on the toy. `ConnesNCG` has none — its `SpectralTripleData` carries `n`,
    `mass` and four matrix identities and no representation — so nothing here is a spectral triple
    with an algebra, and no commutant or order-one statement is made.
  * That `Jzero` or `Jtoy` is antiunitary for an inner product on the toy's space;
    `KOSixSpectralTriple.J_antiunitary` is for the four-block `ip`, not transported here.
  * That either `J` is *the* real structure of anything physical. The finding is that the
    operators do not decide; which `J` the theory means is `ASSUMPTIONS_LEDGER` 18/48 and
    `DECISIONS NEEDED` 8, untouched.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import ConnesNCG
import KOSixSpectralTriple

namespace ToyTripleIsKOSixAtOne

open Matrix ComplexConjugate KOSixSpectralTriple
open KOSixRealStructure (cvec)

/-- The `1 × 1` matrix with entry `m`. -/
def one (m : ℂ) : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => m

/-- **The coordinate permutation** `Hf 1 → ℂ⁴`: toy `0 ↤` particle-left, `1 ↤`
antiparticle-right, `2 ↤` particle-right, `3 ↤` antiparticle-left — so that `gamma`'s signs
`(+, −, −, +)` land on `chiralityOp`'s `(+, +, −, −)`. -/
def toToy (v : Hf 1) : Fin 4 → ℂ := ![v.1.1 0, v.2.2 0, v.1.2 0, v.2.1 0]

/-- Its inverse. -/
def ofToy (w : Fin 4 → ℂ) : Hf 1 := ((fun _ => w 0, fun _ => w 2), (fun _ => w 3, fun _ => w 1))

theorem toToy_ofToy (w : Fin 4 → ℂ) : toToy (ofToy w) = w := by
  funext i; fin_cases i <;> rfl

theorem ofToy_toToy (v : Hf 1) : ofToy (toToy v) = v := by
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> funext i <;>
    rw [Subsingleton.elim i 0] <;> rfl

theorem toToy_bijective : Function.Bijective toToy :=
  ⟨Function.LeftInverse.injective ofToy_toToy, Function.RightInverse.surjective toToy_ofToy⟩

/-- **The KO-6 real structure in the toy's coordinates**: antidiagonal conjugation. This is
`KOSixSpectralTriple.J` transported along `toToy` (`toToy_J`). -/
def Jtoy (w : Fin 4 → ℂ) : Fin 4 → ℂ := ![conj (w 3), conj (w 2), conj (w 1), conj (w 0)]

/-- **The KO-0 real structure the toy's prose meant**: plain entrywise conjugation. -/
def Jzero (w : Fin 4 → ℂ) : Fin 4 → ℂ := fun i => conj (w i)

/-! ## The permutation intertwines the three operators -/

theorem toToy_gamma (v : Hf 1) : toToy (gamma v) = chiralityOp *ᵥ toToy v := by
  funext i; fin_cases i <;> simp [toToy, gamma, chiralityOp, mulVec_diagonal]

theorem toToy_J (v : Hf 1) : toToy (J v) = Jtoy (toToy v) := by
  funext i; fin_cases i <;> simp [toToy, Jtoy, J, cvec]

theorem toToy_D (m : ℂ) (hm : conj m = m) (v : Hf 1) :
    toToy (D (one m) v) = diracOp m *ᵥ toToy v := by
  funext i
  fin_cases i <;>
    simp [toToy, D, one, diracOp, mulVec, dotProduct, Fin.sum_univ_four, mbar,
      conjTranspose_apply, transpose_apply, hm]

/-- The realness hypothesis is exactly what the Dirac identification needs. -/
theorem toToy_D_iff (m : ℂ) :
    (∀ v : Hf 1, toToy (D (one m) v) = diracOp m *ᵥ toToy v) ↔ conj m = m := by
  refine ⟨fun h => ?_, toToy_D m⟩
  have h2 := congrFun (h (ofToy (Pi.single 0 1))) 2
  simpa [toToy, ofToy, D, one, diracOp, mulVec, dotProduct, Fin.sum_univ_four, mbar,
    conjTranspose_apply, transpose_apply, Complex.star_def] using h2

/-- And it is exactly what makes the toy's Dirac operator self-adjoint rather than merely
symmetric (`dirac_symmetric` is `Dᵀ = D`, for every `m`). -/
theorem diracOp_isHermitian_iff (m : ℂ) : (diracOp m).IsHermitian ↔ conj m = m := by
  constructor
  · intro h
    have h02 := congrFun (congrFun h 0) 2
    simpa [diracOp, conjTranspose_apply, Complex.star_def] using h02
  · intro hm
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diracOp, conjTranspose_apply, hm]

/-! ## The KO-6 sign table, on the toy's own operators -/

theorem Jtoy_involutive (w : Fin 4 → ℂ) : Jtoy (Jtoy w) = w := by
  funext i; fin_cases i <;> simp [Jtoy]

theorem Jtoy_antilinear (c : ℂ) (w : Fin 4 → ℂ) : Jtoy (c • w) = conj c • Jtoy w := by
  funext i; fin_cases i <;> simp [Jtoy]

theorem Jtoy_anticomm_chirality (w : Fin 4 → ℂ) :
    Jtoy (chiralityOp *ᵥ w) = -(chiralityOp *ᵥ Jtoy w) := by
  funext i; fin_cases i <;> simp [Jtoy, chiralityOp, mulVec_diagonal]

theorem Jtoy_comm_dirac (m : ℂ) (hm : conj m = m) (w : Fin 4 → ℂ) :
    Jtoy (diracOp m *ᵥ w) = diracOp m *ᵥ Jtoy w := by
  funext i
  fin_cases i <;> simp [Jtoy, diracOp, mulVec, dotProduct, Fin.sum_univ_four, hm]

/-- **KO-DIMENSION 6 ON THE TOY**: `(ε, ε', ε'') = (+1, +1, −1)`, the table `sm_ko_signs`
records, realised by `Jtoy` on `chiralityOp` and `diracOp m` for real `m`. -/
theorem toy_ko_six_signs (m : ℂ) (hm : conj m = m) :
    (∀ w : Fin 4 → ℂ, Jtoy (Jtoy w) = w)
      ∧ (∀ w : Fin 4 → ℂ, Jtoy (diracOp m *ᵥ w) = diracOp m *ᵥ Jtoy w)
      ∧ (∀ w : Fin 4 → ℂ, Jtoy (chiralityOp *ᵥ w) = -(chiralityOp *ᵥ Jtoy w)) :=
  ⟨Jtoy_involutive, Jtoy_comm_dirac m hm, Jtoy_anticomm_chirality⟩

/-! ## The KO-0 sign table, on the same operators -/

theorem Jzero_involutive (w : Fin 4 → ℂ) : Jzero (Jzero w) = w := by
  funext i; simp [Jzero]

theorem Jzero_comm_chirality (w : Fin 4 → ℂ) :
    Jzero (chiralityOp *ᵥ w) = chiralityOp *ᵥ Jzero w := by
  funext i; fin_cases i <;> simp [Jzero, chiralityOp, mulVec_diagonal]

theorem Jzero_comm_dirac (m : ℂ) (hm : conj m = m) (w : Fin 4 → ℂ) :
    Jzero (diracOp m *ᵥ w) = diracOp m *ᵥ Jzero w := by
  funext i
  fin_cases i <;> simp [Jzero, diracOp, mulVec, dotProduct, Fin.sum_univ_four, hm]

/-- **KO-DIMENSION 0 ON THE TOY**: `(+1, +1, +1)`, the table `cascade_ko_signs` records,
realised by `Jzero` on the same two operators. -/
theorem toy_ko_zero_signs (m : ℂ) (hm : conj m = m) :
    (∀ w : Fin 4 → ℂ, Jzero (Jzero w) = w)
      ∧ (∀ w : Fin 4 → ℂ, Jzero (diracOp m *ᵥ w) = diracOp m *ᵥ Jzero w)
      ∧ (∀ w : Fin 4 → ℂ, Jzero (chiralityOp *ᵥ w) = chiralityOp *ᵥ Jzero w) :=
  ⟨Jzero_involutive, Jzero_comm_dirac m hm, Jzero_comm_chirality⟩

/-! ## The theorem the Caesar order named -/

/-- **`toy_triple_is_kosix_at_one`.** For real `m`, the coordinate permutation `toToy` is a
bijection `Hf 1 → ℂ⁴` carrying the KO-6 triple's `gamma`, `D (one m)` and `J` onto the toy's
`chiralityOp`, `diracOp m` and the antidiagonal conjugation `Jtoy`. So the toy's operators ARE the
KO-6 triple's at `n = 1`, and the KO-dimension is a property of the real structure chosen on them
— `Jtoy` gives 6 (`toy_ko_six_signs`), `Jzero` gives 0 (`toy_ko_zero_signs`) — not of the
operators. -/
theorem toy_triple_is_kosix_at_one (m : ℂ) (hm : conj m = m) :
    Function.Bijective toToy
      ∧ (∀ v : Hf 1, toToy (gamma v) = chiralityOp *ᵥ toToy v)
      ∧ (∀ v : Hf 1, toToy (D (one m) v) = diracOp m *ᵥ toToy v)
      ∧ (∀ v : Hf 1, toToy (J v) = Jtoy (toToy v)) :=
  ⟨toToy_bijective, toToy_gamma, toToy_D m hm, toToy_J⟩

end ToyTripleIsKOSixAtOne
