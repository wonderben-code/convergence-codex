/-
  SL2Quotient.lean — the SL₂(ℂ) double cover as a single isomorphism, and
  the first map BETWEEN the two chains.

  WHY. The estate has two independent routes to SO⁺(1,3):

    the SL₂ chain    SL₂(ℂ) --Λ--> SO⁺(1,3)   surjective, kernel {±1}
    the spin chain   Spin(1,3) --ρ--> SO⁺(1,3)   injective mod {±1}, ONTO?

  and — this is the thing — **no theorem relates them.** `SpinQuotient`'s
  §4 says so in as many words ("that is a different map, and no theorem
  relates the two"). The two chains have been built past each other for
  five files.

  Applying PROOF_STRATEGY §6's CAESAR question to `SpinQuotient` — *what
  did I just build that unlocks something elsewhere?* — gives the answer.
  What `SpinQuotient` built was the passage from "kernel is {±1}
  pointwise" to "the quotient by a subgroup object embeds". **The SL₂
  side has exactly the same gap**: `LorentzSurjectivity.double_cover` is
  a CONJUNCTION OF FIVE FACTS, not a `MulEquiv`, so there is no object in
  the estate whose type is "SL₂(ℂ) mod ±1 is SO⁺(1,3)". Build that
  object and the two chains have a common codomain that is a group
  quotient on both sides — and then they compose.

  WHAT THIS FILE PROVES:
  1. **`sl2_surjective`** — `Function.Surjective lorentzSOplusHom`, the
     bundled-hom form of `SOplus13_surjective` (which quantifies over
     matrices and det-proofs separately, so it cannot be fed to any
     Mathlib API that wants a surjection).
  2. **`sl2PmOne`** and **`ker_lorentzSOplusHom_eq_sl2PmOne`** — {±1} in
     SL₂(ℂ) as a subgroup object, and the kernel as an EQUALITY OF
     SUBGROUPS. Same step `SpinQuotient` §1–2 took on the spin side.
  3. **`sl2QuotEquiv : SL₂(ℂ) ⧸ {±1} ≃* SO⁺(1,3)`** — the double cover
     as ONE object. Five conjuncts become one isomorphism.
  4. **`spinQuotToSL2Quot`** and **`spinQuotToSL2Quot_injective`** —
     `Spin(1,3) ⧸ {±1}` embeds in `SL₂(ℂ) ⧸ {±1}`. `SpinMeetsSL2` related
     the two chains at two hand-picked elements and said so ("two
     elements are not a group"); this relates them in general.
  5. **`spin_realised_by_sl2`** — and the pointwise statement in general
     too: EVERY spinor's Lorentz transformation is induced by some
     `A ∈ SL₂(ℂ)`. One line, once §1 exists. `SpinMeetsSL2`'s restriction
     to `R₁₂'` and `B'` is retired.
  6. **`surjectivity_iff_matches_sl2`** — and the remaining gap becomes
     concrete. W7 step (d)'s missing half is now EQUIVALENT to the
     CONVERSE of item 5: for every `A ∈ SL₂(ℂ)` there is a spinor `g`
     with `ρ(g) = Λ(A)`. That is a statement about matching two
     explicitly given families, not about surjectivity onto an
     abstractly specified subgroup — and putting items 5 and 6 side by
     side is the sharpest statement of what is missing that the estate
     has.
  7. **`chains_agree_at_R₁₂'`** — the match exhibited by NAME at a
     nontrivial point: the spin π-rotation and `U_z(0,1) ∈ SL₂(ℂ)` induce
     the same Lorentz matrix, `diag(1,−1,−1,1)`. `SpinMeetsSL2` had this
     only as an existential.

  WHAT THIS DOES NOT DO — and the header says it plainly because this is
  the exact place where a reader wants to over-read. **An injection into
  `SL₂(ℂ) ⧸ {±1}` is not an isomorphism onto it.** Nothing here proves
  the spin map is onto; §5 restates that gap in better coordinates and
  does not close it. `SurjectivityStatement` is still a `def`.

  **SUPERSEDED 8 AUG 2026** — the sentence above was true when written
  and is now false: `SpinSurjective.spin_surjective` proves the spin map
  onto SO⁺(1,3), and `SpinSurjective.spinDoubleCover` bundles W7 step (d)
  as `Spin(1,3) ⧸ {±1} ≃* SO⁺(1,3)`. Left standing per the house rule;
  what remains open is the TOPOLOGICAL reading (ASSUMPTIONS 41 and 42),
  not the algebraic one.
  `spinQuotToSL2Quot` is a bijection — `SpinSurjective.spinEquivSL2Quot`
  is the isomorphism — so §5's `bijective_iff` is a discharged
  hypothesis. **The restatement in §5 is what made the closure findable**,
  which is the argument for restating a gap even when the restatement
  proves nothing.

  WHAT ROUND 31 ADDED: the non-vacuity checks that make §§3–5 mean
  something — `sl2PmOne` has two members and is neither ⊥ nor ⊤,
  `SL₂(ℂ) ⧸ {±1}` is nonabelian (proved by transporting
  `spinQuot_nonabelian` ACROSS the new map, which is the first use of it
  for anything), the quotient map is not injective, `sl2QuotEquiv` agrees
  with the hand computation Λ(U_y(3/5,4/5)) = rotY(−7/25, 24/25), and §7:
  §6's matching problem is SOLVED on `{±1}` and at one point outside it,
  so it is not a statement with no instances. The review also caught that
  §4's map is defined by choice and therefore cannot be computed with;
  `spinQuotToSL2Quot_spec` is its choice-free characterisation.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import SpinQuotient

namespace SL2Quotient

open SpinVectorRep SpinToOrthogonal MinkowskiSignature LorentzGroup
open SpinToLorentzMat SpinOrthochronous SpinFibre SpinQuotient
open CliffordAlgebra CliffordRealMinkowski

noncomputable section

/-! ## 1. The SL₂ map, as a `Function.Surjective`

`LorentzSurjectivity.SOplus13_surjective` quantifies over a matrix and a
determinant proof separately and produces an equation between `Units`.
Nothing in Mathlib's quotient API can consume that. Repackaging it costs
two lines and is the only reason §3 is possible at all.
-/

theorem sl2_surjective : Function.Surjective lorentzSOplusHom := by
  intro M
  obtain ⟨A, hA, heq⟩ := LorentzSurjectivity.SOplus13_surjective M.1 M.2
  exact ⟨⟨A, hA⟩, Subtype.ext heq⟩

/-! ## 2. `{±1}` inside SL₂(ℂ), as a subgroup object

Deliberately the same shape as `SpinQuotient.pmOne`, down to the proof of
the inverse case: from `A = −1` one gets `A⁻¹ = −1` out of `A · A⁻¹ = 1`
and nothing else. Writing it the same way is what makes §4's composite
look like the identity it is rather than like a coincidence.
-/

/-- The two-element subgroup `{1, −1}` of SL₂(ℂ). -/
def sl2PmOne : Subgroup SL2C where
  carrier := {A | (A : Matrix (Fin 2) (Fin 2) ℂ) = 1
      ∨ (A : Matrix (Fin 2) (Fin 2) ℂ) = -1}
  one_mem' := Or.inl Matrix.SpecialLinearGroup.coe_one
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb) <;>
      simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_mul, ha, hb]
    · exact Or.inl (one_mul _)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl (by rw [neg_mul_neg, one_mul])
  inv_mem' := by
    rintro a ha
    have hinv : (a : Matrix (Fin 2) (Fin 2) ℂ)
        * ((a⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    rcases ha with ha | ha
    · rw [ha, one_mul] at hinv
      exact Or.inl hinv
    · rw [ha, neg_one_mul] at hinv
      refine Or.inr ?_
      calc ((a⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)
          = -(-((a⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)) := (neg_neg _).symm
        _ = -1 := by rw [hinv]

theorem mem_sl2PmOne (A : SL2C) :
    A ∈ sl2PmOne ↔ ((A : Matrix (Fin 2) (Fin 2) ℂ) = 1
      ∨ (A : Matrix (Fin 2) (Fin 2) ℂ) = -1) := Iff.rfl

/-- **The kernel of `lorentzSOplusHom`, as an equality of subgroups.**
    `mem_ker_lorentzSOplusHom` gave this pointwise; a quotient needs the
    subgroup object. Exactly the step `SpinQuotient` §1 took. -/
theorem ker_lorentzSOplusHom_eq_sl2PmOne :
    MonoidHom.ker lorentzSOplusHom = sl2PmOne := by
  ext A
  exact LorentzSurjectivity.mem_ker_lorentzSOplusHom A

instance : (sl2PmOne).Normal := by
  rw [← ker_lorentzSOplusHom_eq_sl2PmOne]
  exact MonoidHom.normal_ker lorentzSOplusHom

/-- `SL₂(ℂ) ⧸ {±1}`. -/
abbrev SL2Quot := SL2C ⧸ sl2PmOne

/-! ## 3. The double cover as ONE object

`double_cover` is five conjuncts. A reader assembles "SL₂(ℂ)/±1 ≅
SO⁺(1,3)" from them by hand, and a THEOREM cannot: no downstream file can
apply a conjunction as an isomorphism. Here it is as a `MulEquiv`.
-/

/-- **SL₂(ℂ) ⧸ {±1} ≅ SO⁺(1,3).** -/
def sl2QuotEquiv : SL2Quot ≃* SOplus13 :=
  (QuotientGroup.quotientMulEquivOfEq ker_lorentzSOplusHom_eq_sl2PmOne).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective lorentzSOplusHom sl2_surjective)

@[simp] theorem sl2QuotEquiv_mk (A : SL2C) :
    sl2QuotEquiv (QuotientGroup.mk A) = lorentzSOplusHom A := rfl

theorem sl2QuotEquiv_symm_apply (M : SOplus13) :
    sl2QuotEquiv (sl2QuotEquiv.symm M) = M := sl2QuotEquiv.apply_symm_apply M

/-! ## 4. The first map between the two chains

Both chains now land in a group quotient by `{±1}`, and one of the two
quotients is isomorphic to SO⁺(1,3). So the spin quotient maps into the
SL₂ quotient — injectively, because both legs are injective.

This is the theorem `SpinQuotient` §4 said did not exist.
-/

/-- **`Spin(1,3) ⧸ {±1} → SL₂(ℂ) ⧸ {±1}`.** -/
def spinQuotToSL2Quot : SpinQuot →* SL2Quot :=
  (sl2QuotEquiv.symm : SOplus13 ≃* SL2Quot).toMonoidHom.comp spinQuotEmbed

@[simp] theorem spinQuotToSL2Quot_mk (g : spinGroup Q₁₃) :
    spinQuotToSL2Quot (QuotientGroup.mk g)
      = sl2QuotEquiv.symm (spinToSOplus g) := rfl

/-- **And it is injective.** -/
theorem spinQuotToSL2Quot_injective : Function.Injective spinQuotToSL2Quot := by
  intro x y h
  exact spinQuotEmbed_injective (sl2QuotEquiv.symm.injective h)

/-! ## 5. The remaining gap, in better coordinates

W7 step (d)'s missing half is surjectivity. Stated on SO⁺(1,3) it is a
statement about an abstractly specified subgroup of GL₄(ℝ): one must show
every proper orthochronous Lorentz matrix is hit. Transported across
`sl2QuotEquiv` it becomes a statement about matching two EXPLICIT
families — for each SL₂ matrix `A`, find a spinor whose image is `Λ(A)`.

Nothing below closes the gap. What it does is change what a future proof
has to produce: a construction `A ↦ g`, not a classification of SO⁺(1,3).
-/

/-- **The easy direction, in general.** Every spinor's Lorentz
    transformation is induced by an SL₂(ℂ) matrix. `SpinMeetsSL2` proved
    this for `R₁₂'` and `B'` and its header said "two elements are not a
    group"; with §1's repackaging the general statement is one line, and
    the restriction to two elements is retired. -/
theorem spin_realised_by_sl2 (g : spinGroup Q₁₃) :
    ∃ A : SL2C, lorentzSOplusHom A = spinToSOplus g :=
  sl2_surjective (spinToSOplus g)

/-- §4's map is built through `quotientKerEquivOfSurjective`, which picks
    a right inverse by choice, so it cannot be computed with. This is its
    choice-free characterisation and the form a downstream user wants:
    the class of `g` goes to the class of ANY `A` inducing the same
    Lorentz transformation. -/
theorem spinQuotToSL2Quot_spec (g : spinGroup Q₁₃) :
    ∃ A : SL2C, spinQuotToSL2Quot (QuotientGroup.mk g) = QuotientGroup.mk A
      ∧ lorentzSOplusHom A = spinToSOplus g := by
  obtain ⟨A, hA⟩ := sl2_surjective (spinToSOplus g)
  refine ⟨A, ?_, hA⟩
  rw [spinQuotToSL2Quot_mk, ← hA, ← sl2QuotEquiv_mk, sl2QuotEquiv.symm_apply_apply]

theorem surjective_iff :
    Function.Surjective spinQuotToSL2Quot ↔ SurjectivityStatement := by
  constructor
  · intro h M
    obtain ⟨x, hx⟩ := h (sl2QuotEquiv.symm M)
    exact ⟨x, sl2QuotEquiv.symm.injective hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h (sl2QuotEquiv y)
    refine ⟨x, ?_⟩
    have : sl2QuotEquiv.symm (spinQuotEmbed x) = sl2QuotEquiv.symm (sl2QuotEquiv y) := by
      rw [hx]
    rwa [sl2QuotEquiv.symm_apply_apply] at this

theorem bijective_iff :
    Function.Bijective spinQuotToSL2Quot ↔ SurjectivityStatement :=
  ⟨fun h => surjective_iff.1 h.2,
    fun h => ⟨spinQuotToSL2Quot_injective, surjective_iff.2 h⟩⟩

/-- **The gap as a matching problem.** `SurjectivityStatement` holds iff
    every SL₂(ℂ) matrix's Lorentz transformation is realised by a spinor.
    Both sides of that are explicitly given maps; neither mentions
    SO⁺(1,3)'s defining conditions. -/
theorem surjectivity_iff_matches_sl2 :
    SurjectivityStatement
      ↔ ∀ A : SL2C, ∃ g : spinGroup Q₁₃, spinToSOplus g = lorentzSOplusHom A := by
  constructor
  · intro h A
    obtain ⟨x, hx⟩ := h (lorentzSOplusHom A)
    induction x using QuotientGroup.induction_on with
    | H g => exact ⟨g, hx⟩
  · intro h M
    obtain ⟨A, hA⟩ := sl2_surjective M
    obtain ⟨g, hg⟩ := h A
    exact ⟨QuotientGroup.mk g, by rw [spinQuotEmbed_mk, hg, hA]⟩

/-! ## 6. Review round 31 — that any of this is about anything

Four ways §§2–5 could be vacuous, each stated as its negation and proved.

* If `−1 = 1` in SL₂(ℂ) then `sl2PmOne` is trivial, `sl2QuotEquiv` says
  SL₂(ℂ) ≅ SO⁺(1,3), and the word "cover" is wrong.
* If `sl2PmOne` were everything the quotient would be trivial and §4's
  injection would be an injection of the trivial group.
* If `SL2Quot` were abelian the whole construction would be about a group
  it is not about — and the proof below routes through `spinQuotToSL2Quot`
  itself, so it is also the first *use* of §4 rather than another
  statement of it.
* If `sl2QuotEquiv` did not compute the Lorentz matrix it would be some
  other isomorphism. It computes it, on the one element of SO⁺(1,3) the
  estate has ever evaluated by hand.
-/

/-- `−1` as an element of SL₂(ℂ). -/
def negOneSL2 : SL2C := ⟨-1, by rw [Matrix.det_neg]; simp⟩

@[simp] theorem negOneSL2_coe :
    ((negOneSL2 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := rfl

theorem negOneSL2_ne_one : negOneSL2 ≠ (1 : SL2C) := by
  intro h
  have hv : ((negOneSL2 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)
      = ((1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) := congrArg Subtype.val h
  rw [Matrix.SpecialLinearGroup.coe_one] at hv
  have h00 := Matrix.ext_iff.mpr hv 0 0
  change (-1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = _ at h00
  rw [Matrix.neg_apply, Matrix.one_apply_eq] at h00
  norm_num at h00

theorem sl2PmOne_two_members :
    (1 : SL2C) ∈ sl2PmOne ∧ negOneSL2 ∈ sl2PmOne ∧ negOneSL2 ≠ (1 : SL2C) :=
  ⟨Or.inl Matrix.SpecialLinearGroup.coe_one, Or.inr rfl, negOneSL2_ne_one⟩

theorem sl2PmOne_ne_bot : sl2PmOne ≠ (⊥ : Subgroup SL2C) := by
  intro h
  have hmem : negOneSL2 ∈ sl2PmOne := Or.inr rfl
  rw [h, Subgroup.mem_bot] at hmem
  exact negOneSL2_ne_one hmem

/-- A matrix whose `(0,0)` entry is neither `1` nor `−1` is not `±1`. -/
theorem not_mem_sl2PmOne_of_entry {A : SL2C}
    (h1 : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ≠ 1)
    (h2 : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ≠ -1) : A ∉ sl2PmOne := by
  rintro (h | h)
  · exact h1 (by rw [h, Matrix.one_apply_eq])
  · exact h2 (by rw [h, Matrix.neg_apply, Matrix.one_apply_eq])

/-- The rotation used throughout `LorentzSurjectivity`'s worked example,
    as an element of SL₂(ℂ). -/
def su2Ywitness : SL2C :=
  ⟨LorentzSurjectivity.su2Y (3 / 5) (4 / 5),
    LorentzSurjectivity.det_su2Y _ _ (by norm_num)⟩

theorem su2Ywitness_not_mem : su2Ywitness ∉ sl2PmOne := by
  refine not_mem_sl2PmOne_of_entry ?_ ?_ <;>
    · change ((3 / 5 : ℝ) : ℂ) ≠ _
      norm_num

theorem sl2PmOne_ne_top : sl2PmOne ≠ (⊤ : Subgroup SL2C) := fun h =>
  su2Ywitness_not_mem (h ▸ Subgroup.mem_top su2Ywitness)

/-- **The SL₂ quotient is nonabelian** — transported across §4's map from
    the spin side, which is the first time anything in the estate has
    carried a fact from one chain to the other. -/
theorem sl2Quot_nonabelian : ∃ x y : SL2Quot, x * y ≠ y * x := by
  obtain ⟨a, b, hab⟩ := spinQuot_nonabelian
  refine ⟨spinQuotToSL2Quot a, spinQuotToSL2Quot b, ?_⟩
  intro h
  rw [← map_mul, ← map_mul] at h
  exact hab (spinQuotToSL2Quot_injective h)

/-- The quotient genuinely quotients: `SL₂(ℂ) → SL₂(ℂ) ⧸ {±1}` is not
    injective, so `sl2QuotEquiv` is not an isomorphism `SL₂(ℂ) ≅
    SO⁺(1,3)` in disguise. -/
theorem mk_not_injective :
    ¬ Function.Injective (QuotientGroup.mk : SL2C → SL2Quot) := by
  intro hinj
  refine negOneSL2_ne_one (hinj ?_)
  rw [QuotientGroup.mk_one]
  exact (QuotientGroup.eq_one_iff negOneSL2).2 (Or.inr rfl)

/-- **`sl2QuotEquiv` computes the Lorentz matrix**: on the class of
    U_y(3/5,4/5) it returns rotY(−7/25, 24/25), which is the value
    `LorentzSurjectivity` computed by hand for the doubled angle. -/
theorem sl2QuotEquiv_su2Ywitness :
    (((sl2QuotEquiv (QuotientGroup.mk su2Ywitness) : SOplus13)
        : Matrix.GeneralLinearGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ)
      = LorentzSurjectivity.rotY (-(7 / 25)) (24 / 25) := by
  rw [sl2QuotEquiv_mk, lorentzSOplusHom_apply]
  change lorentzMat (LorentzSurjectivity.su2Y (3 / 5) (4 / 5)) = _
  rw [LorentzSurjectivity.lorentzMat_su2Y _ _ (by norm_num)]
  norm_num

theorem sl2Quot_mk_su2Ywitness_ne_one :
    (QuotientGroup.mk su2Ywitness : SL2Quot) ≠ 1 := by
  intro h
  exact su2Ywitness_not_mem ((QuotientGroup.eq_one_iff su2Ywitness).1 h)

/-! ## 7. The matching problem is not vacuous

§5 says the gap is "for every `A`, find a spinor `g` with `ρ(g) = Λ(A)`".
A statement of that form is worth nothing if it is unsolvable at every
nontrivial point — the reader should be shown at least one instance
where the match is exhibited by NAME, not by an existential.

It is. `spinToO13 R₁₂' = diag(1,−1,−1,1)` (`SpinToLorentzMat`) and
`Λ(U_z(0,1)) = rotZ(−1,0)`, which is the same matrix. So the π-rotation
in the (1,2)-plane is reached by both chains, and the two witnesses are
written down rather than chosen.
-/

/-- `U_z(0,1) = diag(−i, i)`, the SL₂(ℂ) π-rotation about the z axis. -/
def su2Zwitness : SL2C :=
  ⟨LorentzSurjectivity.su2Z 0 1, LorentzSurjectivity.det_su2Z _ _ (by norm_num)⟩

theorem lorentzMat_su2Zwitness :
    lorentzMat ((su2Zwitness : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.diagonal ![1, -1, -1, 1] := by
  change lorentzMat (LorentzSurjectivity.su2Z 0 1) = _
  rw [LorentzSurjectivity.lorentzMat_su2Z _ _ (by norm_num)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [LorentzSurjectivity.rotZ, Matrix.diagonal]

/-- **The two chains agree, at a named pair.** The spin group's
    π-rotation and `U_z(0,1) ∈ SL₂(ℂ)` induce the SAME element of
    SO⁺(1,3). `SpinMeetsSL2` had this only as an existential
    (`R₁₂'_in_SL2_image`); here the SL₂ witness is exhibited. -/
theorem chains_agree_at_R₁₂' :
    spinToSOplus R₁₂' = lorentzSOplusHom su2Zwitness := by
  refine Subtype.ext (Units.ext ?_)
  have hL : ((spinToSOplus R₁₂' : SOplus13)
      : Matrix.GeneralLinearGroup (Fin 4) ℝ).val
      = Matrix.diagonal ![1, -1, -1, 1] := spinToO13_R₁₂'_matrix
  rw [hL, lorentzSOplusHom_apply, lorentzMat_su2Zwitness]

/-- Hence the matching problem of §5 has a solution at a NONTRIVIAL `A`:
    `su2Zwitness` is not in `{±1}`, and yet a spinor matches it. -/
theorem matching_at_su2Zwitness :
    su2Zwitness ∉ sl2PmOne
      ∧ ∃ g : spinGroup Q₁₃, spinToSOplus g = lorentzSOplusHom su2Zwitness := by
  refine ⟨?_, R₁₂', chains_agree_at_R₁₂'⟩
  refine not_mem_sl2PmOne_of_entry ?_ ?_ <;>
    · change ((0 : ℝ) : ℂ) - ((1 : ℝ) : ℂ) * Complex.I ≠ _
      simp [Complex.ext_iff]

/-- And it is solved on all of `{±1}`, trivially but not vacuously: those
    are exactly the `A` with `Λ(A) = 1`, matched by the identity spinor.
    So §5's quantifier is already discharged on a subgroup and at one
    point outside it; what is missing is the rest. -/
theorem matches_on_kernel (A : SL2C) (hA : A ∈ sl2PmOne) :
    ∃ g : spinGroup Q₁₃, spinToSOplus g = lorentzSOplusHom A := by
  have hker : A ∈ MonoidHom.ker lorentzSOplusHom := by
    rw [ker_lorentzSOplusHom_eq_sl2PmOne]
    exact hA
  exact ⟨1, by rw [map_one]; exact (MonoidHom.mem_ker.1 hker).symm⟩

end

end SL2Quotient
