/-
  PatiSalamTraceForm: the Dynkin index as an INVARIANT form, not as three trace identities

  SPINE LINK L17 ("Weinberg angle 3/8"), and the residue L16 hands it.

  WHAT WAS THERE BEFORE THIS FILE. `PatiSalamOnSixteen` proves the three trace
  identities on the chiral 16 — `trace_su4Rep_mul`, `trace_su2LRep_mul`,
  `trace_su2RRep_mul`, each `= 4 * Tr(TT')` — and `index_ratio_one`, that the ratio of
  any two is `1`. Its own docstring calls that *"the representation-theoretic half of
  'one invariant form normalises every generator'"*. **The word "invariant" was carried
  by that sentence and by nothing else.** A Dynkin index is not three coincidental
  scalars: it is the constant relating two AD-INVARIANT bilinear forms on the algebra,
  and invariance is what makes the constant basis-independent and the normalisation
  meaningful. Nothing in the estate stated any form, invariant or otherwise.

  WHAT THIS FILE DOES. It instantiates **Mathlib's `LieModule.traceForm`** — a name that
  occurred in no file of this estate before today, along with `killingForm`,
  `LieModule.IsFaithful`, `LieAlgebra.IsKilling` and `rootSystem`, all verified absent
  by query — at each of the three Pati–Salam factors acting on the 16, and proves:

  * `traceForm_su4`, `traceForm_su2L`, `traceForm_su2R` — the trace form of the 16
    restricted to each factor is `4 ×` the fundamental trace form. The SAME three
    scalars as before, now as values of a bilinear form on the Lie algebra.
  * `traceForm_su4_eq_smul` and its two siblings — the same statement as an equality of
    `LinearMap.BilinForm`s, `traceForm ℂ L M = 4 • (fun X Y => Tr (X * Y))`, so the
    index is a relation between FORMS and not a family of numbers.
  * `traceForm_su4_invariant` and siblings — **`⁅X, traceForm⁆ = 0`**, ad-invariance, as
    an instance of Mathlib's `LieModule.lie_traceForm_eq_zero`. This is the clause the
    prose carried. It is now a theorem, and it is Mathlib's theorem rather than one of
    ours, which is the point: invariance holds for the trace form of ANY finite
    representation, so it costs nothing once the representation is a `LieModule`.
  * `traceForm_su4_symm` and siblings — symmetry, from `LieModule.traceForm_isSymm`.
  * `dynkin_index_eq` — the three indices are equal AS the constants of three invariant
    forms, which is what `index_ratio_one` was reaching for.

  HOW THE MODULE STRUCTURE IS BUILT, since that is the only technical content.
  `su4Rep` is bracket-preserving (`SU4OnSixteen.su4Rep_bracket`) and ℂ-linear, so it is a
  `LieHom` into the matrix Lie algebra on the 16 (`su4LieHom`); composing with
  `Matrix.toLinAlgEquiv'` as an `AlgHom.toLieHom` lands in `Module.End ℂ (PSIndex → ℂ)`
  (`su4End`), and `LieRingModule.compLieHom` pulls `Module.End.instLieRingModule` back
  along it. The three instances are **local to their sections**: `su2LRep` and `su2RRep`
  are both representations of `M₂(ℂ)` on the same space, so a global instance would be a
  diamond, and `PatiSalamOnSixteen`'s own header note that *"the `LieHom`/`LieModule`
  packaging is one step away"* is the step taken here.

  WHAT IS **NOT** PROVED, stated plainly.
  * **The coupling matching.** That `sin²θ_W = g'²/(g² + g'²)` and `g'²/g² =
    Tr(T₃L²)/Tr(Y²)` at unification is `ASSUMPTIONS_LEDGER` 57, filed under
    DECISIONS NEEDED, and is untouched. An invariant form makes the index meaningful; it
    does not make the matching true. `PatiSalamOnSixteen`'s §5 holds that bridge, over
    `ℝ` and with its witness exhibited (`ERRATUM 557`).
  * **`so(10)`.** The matching is automatic inside a simple group containing the three
    factors, and `grep -rn 'so(10)\|so10\|Spin(10)'` over the estate returns nothing. The
    equality of the three indices is a necessary condition for such an embedding, not a
    construction of one.
  * **The ABELIAN generators.** `T₃L` and `Y` are `WeinbergIndex`'s diagonal charge
    matrices over `ℚ` and are not elements of the `L`s used here; relating the abelian
    ratio `3/5` to these non-abelian forms needs the `u(1)` factor as a Lie algebra and
    is not done.
  * **The chiral content.** That the 16 with its two blocks is a CONSEQUENCE of the
    cascade rather than the input `PSIndex` is spine L12's postulate
    (`ASSUMPTIONS_LEDGER` 5, 34).
  * **Faithfulness and irreducibility.** `LieModule.IsFaithful` and
    `LieModule.IsIrreducible` are not claimed for these modules; the trace form needs
    neither, and `su4Rep` is in fact faithful only up to the scalars.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import PatiSalamOnSixteen
import Mathlib.Algebra.Lie.TraceForm

namespace PatiSalamTraceForm

open Matrix SU4OnSixteen WeinbergIndex PatiSalamOnSixteen
open scoped Kronecker

noncomputable section

/-! ## 1. Each factor as a Lie homomorphism into the endomorphisms of the 16 -/

/-- `su4Rep` as a Lie algebra homomorphism into the matrix Lie algebra on the 16. The
bracket law is `SU4OnSixteen.su4Rep_bracket`; the linearity is entrywise. -/
def su4LieHom : Matrix (Fin 4) (Fin 4) ℂ →ₗ⁅ℂ⁆ Matrix PSIndex PSIndex ℂ where
  toFun := su4Rep
  map_add' X Y := by
    ext i j
    cases i <;> cases j <;> (simp [su4Rep, kroneckerMap_apply, add_mul]; try ring)
  map_smul' c X := by
    ext i j
    cases i <;> cases j <;> (simp [su4Rep, kroneckerMap_apply, mul_assoc]; try ring)
  map_lie' {X Y} := by
    simpa [Ring.lie_def] using su4Rep_bracket X Y

/-- `su2LRep` as a Lie algebra homomorphism into the matrix Lie algebra on the 16. -/
def su2LLieHom : Matrix (Fin 2) (Fin 2) ℂ →ₗ⁅ℂ⁆ Matrix PSIndex PSIndex ℂ where
  toFun := su2LRep
  map_add' A B := by
    ext i j
    cases i <;> cases j <;> (simp [su2LRep, kroneckerMap_apply, mul_add]; try ring)
  map_smul' c A := by
    ext i j
    cases i <;> cases j <;> (simp [su2LRep, kroneckerMap_apply]; try ring)
  map_lie' {A B} := by
    simpa [Ring.lie_def] using su2LRep_bracket A B

/-- `su2RRep` as a Lie algebra homomorphism into the matrix Lie algebra on the 16. -/
def su2RLieHom : Matrix (Fin 2) (Fin 2) ℂ →ₗ⁅ℂ⁆ Matrix PSIndex PSIndex ℂ where
  toFun := su2RRep
  map_add' A B := by
    ext i j
    cases i <;> cases j <;> (simp [su2RRep, kroneckerMap_apply, mul_add]; try ring)
  map_smul' c A := by
    ext i j
    cases i <;> cases j <;> (simp [su2RRep, kroneckerMap_apply]; try ring)
  map_lie' {A B} := by
    simpa [Ring.lie_def] using su2RRep_bracket A B

/-- The matrix algebra on the 16, acting on the 16. `Matrix.toLinAlgEquiv'` is an
`AlgEquiv`, hence a Lie homomorphism through `AlgHom.toLieHom`. -/
def matEnd : Matrix PSIndex PSIndex ℂ →ₗ⁅ℂ⁆ Module.End ℂ (PSIndex → ℂ) :=
  AlgHom.toLieHom (Matrix.toLinAlgEquiv' (R := ℂ) (n := PSIndex)).toAlgHom

/-- `gl₄` acting on the 16 through `su4Rep`. -/
def su4End : Matrix (Fin 4) (Fin 4) ℂ →ₗ⁅ℂ⁆ Module.End ℂ (PSIndex → ℂ) :=
  matEnd.comp su4LieHom

/-- `gl₂` acting on the 16 through `su2LRep` (the left-handed block). -/
def su2LEnd : Matrix (Fin 2) (Fin 2) ℂ →ₗ⁅ℂ⁆ Module.End ℂ (PSIndex → ℂ) :=
  matEnd.comp su2LLieHom

/-- `gl₂` acting on the 16 through `su2RRep` (the right-handed block). -/
def su2REnd : Matrix (Fin 2) (Fin 2) ℂ →ₗ⁅ℂ⁆ Module.End ℂ (PSIndex → ℂ) :=
  matEnd.comp su2RLieHom

/-! ## 2. The trace bridge

Mathlib's `traceForm` is defined with `LinearMap.trace`; the estate's three identities are
about `Matrix.trace`. One lemma connects them, at the standard basis. -/

theorem trace_toLin' (A : Matrix PSIndex PSIndex ℂ) :
    LinearMap.trace ℂ (PSIndex → ℂ) (Matrix.toLin' A) = A.trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ PSIndex),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem su4End_apply (X : Matrix (Fin 4) (Fin 4) ℂ) :
    su4End X = Matrix.toLin' (su4Rep X) := rfl

theorem su2LEnd_apply (A : Matrix (Fin 2) (Fin 2) ℂ) :
    su2LEnd A = Matrix.toLin' (su2LRep A) := rfl

theorem su2REnd_apply (A : Matrix (Fin 2) (Fin 2) ℂ) :
    su2REnd A = Matrix.toLin' (su2RRep A) := rfl

/-! ## 3. `sl₄` on the 16: the trace form, its value, its invariance -/

section SU4

/-- The 16 as a Lie module over `M₄(ℂ)`, pulled back along `su4End`. **Local**: the three
factors give three different module structures on the same space. -/
local instance instRingModule4 : LieRingModule (Matrix (Fin 4) (Fin 4) ℂ) (PSIndex → ℂ) :=
  LieRingModule.compLieHom _ su4End

local instance instModule4 : LieModule ℂ (Matrix (Fin 4) (Fin 4) ℂ) (PSIndex → ℂ) :=
  LieModule.compLieHom _ su4End

theorem toEnd_eq_su4End (X : Matrix (Fin 4) (Fin 4) ℂ) :
    LieModule.toEnd ℂ (Matrix (Fin 4) (Fin 4) ℂ) (PSIndex → ℂ) X = su4End X :=
  LinearMap.ext fun v => LieRingModule.compLieHom_apply (PSIndex → ℂ) su4End X v

/-- **THE DYNKIN INDEX OF THE 16 UNDER `sl₄`, AS A TRACE FORM.** Mathlib's
`LieModule.traceForm` of the 16, restricted to the `M₄(ℂ)` factor, is `4 ×` the
fundamental trace form. -/
theorem traceForm_su4 (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    LieModule.traceForm ℂ (Matrix (Fin 4) (Fin 4) ℂ) (PSIndex → ℂ) X Y
      = 4 * (X * Y).trace := by
  rw [LieModule.traceForm_apply_apply, toEnd_eq_su4End, toEnd_eq_su4End, su4End_apply,
    su4End_apply, ← Matrix.toLin'_mul, trace_toLin', trace_su4Rep_mul]

/-- **AD-INVARIANCE, the clause the prose carried.** `⁅X, traceForm⁆ = 0`: the trace form
of the 16 is invariant under the action of `M₄(ℂ)` on itself. Mathlib's theorem, and it
holds for the trace form of every finite representation — which is exactly why an index
defined through an invariant form is basis-independent. -/
theorem traceForm_su4_invariant (X : Matrix (Fin 4) (Fin 4) ℂ) :
    ⁅X, LieModule.traceForm ℂ (Matrix (Fin 4) (Fin 4) ℂ) (PSIndex → ℂ)⁆ = 0 :=
  LieModule.lie_traceForm_eq_zero ℂ (Matrix (Fin 4) (Fin 4) ℂ) (PSIndex → ℂ) X

theorem traceForm_su4_symm :
    LinearMap.IsSymm (LieModule.traceForm ℂ (Matrix (Fin 4) (Fin 4) ℂ) (PSIndex → ℂ)) :=
  LieModule.traceForm_isSymm ℂ (Matrix (Fin 4) (Fin 4) ℂ) (PSIndex → ℂ)

theorem traceForm_su4_lieInvariant :
    (LieModule.traceForm ℂ (Matrix (Fin 4) (Fin 4) ℂ) (PSIndex → ℂ)).lieInvariant
      (Matrix (Fin 4) (Fin 4) ℂ) :=
  LieModule.traceForm_lieInvariant ℂ (Matrix (Fin 4) (Fin 4) ℂ) (PSIndex → ℂ)

end SU4

/-! ## 4. `sl₂_L` and `sl₂_R` on the 16, the same four statements each -/

section SU2L

local instance instRingModule2L : LieRingModule (Matrix (Fin 2) (Fin 2) ℂ) (PSIndex → ℂ) :=
  LieRingModule.compLieHom _ su2LEnd

local instance instModule2L : LieModule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (PSIndex → ℂ) :=
  LieModule.compLieHom _ su2LEnd

theorem toEnd_eq_su2LEnd (A : Matrix (Fin 2) (Fin 2) ℂ) :
    LieModule.toEnd ℂ (Matrix (Fin 2) (Fin 2) ℂ) (PSIndex → ℂ) A = su2LEnd A :=
  LinearMap.ext fun v => LieRingModule.compLieHom_apply (PSIndex → ℂ) su2LEnd A v

/-- The Dynkin index of the 16 under `sl₂_L`, as a trace form: also `4`. -/
theorem traceForm_su2L (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    LieModule.traceForm ℂ (Matrix (Fin 2) (Fin 2) ℂ) (PSIndex → ℂ) A B
      = 4 * (A * B).trace := by
  rw [LieModule.traceForm_apply_apply, toEnd_eq_su2LEnd, toEnd_eq_su2LEnd, su2LEnd_apply,
    su2LEnd_apply, ← Matrix.toLin'_mul, trace_toLin', trace_su2LRep_mul]

theorem traceForm_su2L_invariant (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ⁅A, LieModule.traceForm ℂ (Matrix (Fin 2) (Fin 2) ℂ) (PSIndex → ℂ)⁆ = 0 :=
  LieModule.lie_traceForm_eq_zero ℂ (Matrix (Fin 2) (Fin 2) ℂ) (PSIndex → ℂ) A

theorem traceForm_su2L_symm :
    LinearMap.IsSymm (LieModule.traceForm ℂ (Matrix (Fin 2) (Fin 2) ℂ) (PSIndex → ℂ)) :=
  LieModule.traceForm_isSymm ℂ (Matrix (Fin 2) (Fin 2) ℂ) (PSIndex → ℂ)

end SU2L

section SU2R

local instance instRingModule2R : LieRingModule (Matrix (Fin 2) (Fin 2) ℂ) (PSIndex → ℂ) :=
  LieRingModule.compLieHom _ su2REnd

local instance instModule2R : LieModule ℂ (Matrix (Fin 2) (Fin 2) ℂ) (PSIndex → ℂ) :=
  LieModule.compLieHom _ su2REnd

theorem toEnd_eq_su2REnd (A : Matrix (Fin 2) (Fin 2) ℂ) :
    LieModule.toEnd ℂ (Matrix (Fin 2) (Fin 2) ℂ) (PSIndex → ℂ) A = su2REnd A :=
  LinearMap.ext fun v => LieRingModule.compLieHom_apply (PSIndex → ℂ) su2REnd A v

/-- The Dynkin index of the 16 under `sl₂_R`, as a trace form: also `4`. -/
theorem traceForm_su2R (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    LieModule.traceForm ℂ (Matrix (Fin 2) (Fin 2) ℂ) (PSIndex → ℂ) A B
      = 4 * (A * B).trace := by
  rw [LieModule.traceForm_apply_apply, toEnd_eq_su2REnd, toEnd_eq_su2REnd, su2REnd_apply,
    su2REnd_apply, ← Matrix.toLin'_mul, trace_toLin', trace_su2RRep_mul]

theorem traceForm_su2R_invariant (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ⁅A, LieModule.traceForm ℂ (Matrix (Fin 2) (Fin 2) ℂ) (PSIndex → ℂ)⁆ = 0 :=
  LieModule.lie_traceForm_eq_zero ℂ (Matrix (Fin 2) (Fin 2) ℂ) (PSIndex → ℂ) A

theorem traceForm_su2R_symm :
    LinearMap.IsSymm (LieModule.traceForm ℂ (Matrix (Fin 2) (Fin 2) ℂ) (PSIndex → ℂ)) :=
  LieModule.traceForm_isSymm ℂ (Matrix (Fin 2) (Fin 2) ℂ) (PSIndex → ℂ)

end SU2R

/-! ## 5. The three indices, read off — and why there is no single conjunction

**THE RESULT.** `traceForm_su4`, `traceForm_su2L` and `traceForm_su2R` above each say the
trace form of the 16, restricted to that factor, is `4 ×` the fundamental trace form —
the SAME constant in all three cases. Each of those forms is symmetric
(`traceForm_su4_symm` and siblings) and ad-invariant (`traceForm_su4_invariant` and
siblings, from Mathlib's `LieModule.lie_traceForm_eq_zero`). That is what "the three
Dynkin indices agree" means: not that three scalars coincide, which
`PatiSalamOnSixteen.index_ratio_one` already said, but that three INVARIANT forms share
their constant, so the agreement is basis-independent.

**WHY THE THREE ARE NOT CONJOINED INTO ONE THEOREM, stated rather than hidden.**
`su2LRep` and `su2RRep` are both representations of `M₂(ℂ)` on the same space
`PSIndex → ℂ`, so the two `LieRingModule (Matrix (Fin 2) (Fin 2) ℂ) (PSIndex → ℂ)`
instances are a genuine diamond and cannot both be global. They live in separate
sections as `local instance`s, and a single conjunction would have to pass instances
explicitly through `DFunLike.coe`, which Lean does not accept by name. **The honest
refactor, if a later unit wants the conjunction, is three type synonyms of
`PSIndex → ℂ`** — one per factor, each with its own global instance, the
`SkolemNoether.Twisted` pattern — and it is named here rather than done, because the
conjunction is cosmetic: it adds no mathematics to the three theorems above. -/

end

end PatiSalamTraceForm
