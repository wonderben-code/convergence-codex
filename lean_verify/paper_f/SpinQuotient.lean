/-
  SpinQuotient.lean — `spinGroup Q₁₃ ⧸ {±1}` embeds in SO⁺(1,3), as a
  theorem rather than as a reading.

  WHY. `SpinFibre` proved the kernel of `spinToSOplus` is exactly `{±1}`
  and the fibres have exactly two points, and its header then said: "the
  honest reading is `spinGroup Q₁₃ ⧸ {±1}` embeds in SO⁺(1,3)". **That is
  prose asserting mathematics**, which is the class of thing this project
  keeps catching in itself — nearly every entry in ERRATA is a docstring
  claiming what the theorem below it does not. It is also two steps short:
  the kernel was established POINTWISE, not as an equality of subgroup
  objects, and `SpinFibre`'s own header flagged that gap when it was
  written.

  WHAT THIS FILE PROVES:
  1. **`pmOne`** — `{g : (g : Cl) = 1 ∨ (g : Cl) = −1}` as an honest
     subgroup of `spinGroup Q₁₃`, closure proved rather than asserted.
     The inverse case is the only one with content: from `g = −1`,
     `g⁻¹ = −1` follows from `g · g⁻¹ = 1`.
  2. **`ker_spinToSOplus_eq_pmOne`** — the kernel as an EQUALITY OF
     SUBGROUPS, which is the gap `SpinFibre` recorded.
  3. **`spinQuotEmbed`** and **`spinQuotEmbed_injective`** — the quotient
     `spinGroup Q₁₃ ⧸ {±1}` maps injectively into SO⁺(1,3). The prose
     claim is now a theorem.
  4. **`spinQuotEmbed_ne_one`** — and the quotient is not trivial, so the
     embedding embeds something.

  WHAT IS STILL NOT TRUE. **An injection is not a bijection.** Whether
  `spinQuotEmbed` is ONTO is exactly W7 step (d)'s remaining part, and it
  is not proved. So this file says the quotient is a subgroup of
  SO⁺(1,3) up to isomorphism, and does NOT say it is SO⁺(1,3). The
  difference between those two sentences is the whole of what is left.

  **SUPERSEDED 8 AUG 2026** — the sentence above was true when written
  and is now false: `SpinSurjective.spin_surjective` proves the spin map
  onto SO⁺(1,3), and `SpinSurjective.spinDoubleCover` bundles W7 step (d)
  as `Spin(1,3) ⧸ {±1} ≃* SO⁺(1,3)`. Left standing per the house rule;
  what remains open is the TOPOLOGICAL reading (ASSUMPTIONS 41 and 42),
  not the algebraic one.
  `spinQuotEmbed` IS onto — `SpinSurjective.surjectivityStatement` — so
  §4's `SurjectivityStatement` is a discharged hypothesis rather than a
  gap, and it is kept as a `def` because downstream statements are
  phrased against it.

  WHAT ROUND 30 ADDED, and the first item underpins every "double cover"
  sentence in the estate: **`neg_one_ne_one_cl`** — `−1 ≠ 1` in
  Cl(1,3;ℝ). If that failed, `pmOne` would be trivial, the quotient would
  be the whole group, and every theorem here would be about nothing. It
  was assumed everywhere and proved nowhere. With `pmOne_two_members`,
  `pmOne_ne_top`, `pmOne_ne_bot`, and `surjectivityStatement_implies`,
  which is how one reviews a `def` that states a gap: it cannot be tested
  by proving it, so instead check that it entails what §4 says it does.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import SpinFibre

namespace SpinQuotient

open SpinVectorRep SpinToOrthogonal MinkowskiSignature LorentzGroup
open SpinToLorentzMat SpinOrthochronous SpinFibre
open CliffordAlgebra CliffordRealMinkowski

noncomputable section

/-! ## 1. `{±1}` as a subgroup -/

/-- The two-element subgroup `{1, −1}` of the spin group. -/
def pmOne : Subgroup (spinGroup Q₁₃) where
  carrier := {g | (g : Cl) = 1 ∨ (g : Cl) = -1}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb) <;>
      simp only [Set.mem_setOf_eq,
        show ∀ x y : spinGroup Q₁₃, ((x * y : spinGroup Q₁₃) : Cl) = (x : Cl) * (y : Cl)
          from fun _ _ => rfl, ha, hb]
    · exact Or.inl (one_mul _)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl (by rw [neg_mul_neg, one_mul])
  inv_mem' := by
    rintro a (ha | ha)
    · left
      have h := congrArg Subtype.val (mul_inv_cancel a)
      rw [show ((a * a⁻¹ : spinGroup Q₁₃) : Cl)
        = (a : Cl) * ((a⁻¹ : spinGroup Q₁₃) : Cl) from rfl, ha, one_mul] at h
      exact h
    · right
      have h := congrArg Subtype.val (mul_inv_cancel a)
      rw [show ((a * a⁻¹ : spinGroup Q₁₃) : Cl)
        = (a : Cl) * ((a⁻¹ : spinGroup Q₁₃) : Cl) from rfl, ha, neg_one_mul] at h
      exact neg_eq_iff_eq_neg.mp h

@[simp] theorem mem_pmOne (g : spinGroup Q₁₃) :
    g ∈ pmOne ↔ ((g : Cl) = 1 ∨ (g : Cl) = -1) := Iff.rfl

/-- **The kernel, as an equality of subgroups.** `SpinFibre` proved this
    pointwise and its header recorded that the subgroup-object version
    was missing; this is it. -/
theorem ker_spinToSOplus_eq_pmOne : MonoidHom.ker spinToSOplus = pmOne := by
  ext g
  rw [mem_pmOne]
  exact mem_ker_spinToSOplus g

instance : (pmOne).Normal := by
  rw [← ker_spinToSOplus_eq_pmOne]
  exact MonoidHom.normal_ker spinToSOplus

/-! ## 2. The quotient embeds -/

/-- The quotient of the spin group by `{±1}`. -/
abbrev SpinQuot := spinGroup Q₁₃ ⧸ pmOne

/-- **`spinGroup Q₁₃ ⧸ {±1}` maps into SO⁺(1,3).** -/
def spinQuotEmbed : SpinQuot →* SOplus13 :=
  QuotientGroup.lift pmOne spinToSOplus fun g hg =>
    (ker_spinToSOplus_eq_pmOne ▸ hg : g ∈ MonoidHom.ker spinToSOplus)

@[simp] theorem spinQuotEmbed_mk (g : spinGroup Q₁₃) :
    spinQuotEmbed (QuotientGroup.mk g) = spinToSOplus g := rfl

/-- **And the map is INJECTIVE.** The prose claim of `SpinFibre`'s header
    is now a theorem. -/
theorem spinQuotEmbed_injective : Function.Injective spinQuotEmbed := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [eq_bot_iff]
  rintro x hx
  induction x using QuotientGroup.induction_on with
  | H g =>
    have hg : spinToSOplus g = 1 := hx
    have : g ∈ pmOne := (mem_pmOne g).2 ((mem_ker_spinToSOplus g).1 hg)
    simpa using (QuotientGroup.eq_one_iff (N := pmOne) g).2 this

/-! ## 3. It embeds something

An injection into a group says nothing if its source is trivial. It is
not: the image is nonabelian, so the quotient has at least two elements
that do not commute.
-/

theorem spinQuotEmbed_ne_one :
    spinQuotEmbed (QuotientGroup.mk R₁₂') ≠ 1 := by
  intro h
  refine spinToO13_R₁₂'_ne_one (Subtype.ext ?_)
  have hv : spinToSOplus R₁₂' = 1 := h
  exact congrArg (fun M : SOplus13 => (M : Matrix.GeneralLinearGroup (Fin 4) ℝ)) hv

theorem spinQuot_nonabelian :
    ∃ x y : SpinQuot, x * y ≠ y * x := by
  refine ⟨QuotientGroup.mk B', QuotientGroup.mk R₁₂', ?_⟩
  intro h
  refine spinToO13_noncomm (Subtype.ext ?_)
  have h1 : spinToSOplus (B' * R₁₂') = spinToSOplus (R₁₂' * B') := by
    have hq := congrArg spinQuotEmbed h
    rwa [map_mul, map_mul, spinQuotEmbed_mk, spinQuotEmbed_mk, ← map_mul,
      ← map_mul] at hq
  exact congrArg
    (fun M : SOplus13 => (M : Matrix.GeneralLinearGroup (Fin 4) ℝ)) h1

/-! ## 4. What an injection is not

`spinQuotEmbed` being injective makes the quotient isomorphic to a
SUBGROUP of SO⁺(1,3). Whether that subgroup is everything is W7 step
(d)'s remaining part and is not proved. The statement below is what the
file would need in order to say "double cover", written out so that its
absence is visible rather than implied.
-/

/-- The missing statement, named but NOT proved anywhere in the estate:
    surjectivity. It is stated here as a definition of the gap, not as a
    theorem — nothing in this file or any other establishes it.

    **SUPERSEDED 8 AUG 2026**: `SpinSurjective.surjectivityStatement`
    proves it. The `def` is kept because several downstream statements
    are phrased against it, and the docstring is kept because a record
    of what the project believed at each point is part of what the
    record is for. -/
def SurjectivityStatement : Prop := Function.Surjective spinQuotEmbed

/-- What IS available: the SL₂(ℂ) chain reaches all of SO⁺(1,3). That is
    a different map, and no theorem relates the two. -/
theorem sl2_reaches_all (M : Matrix.GeneralLinearGroup (Fin 4) ℝ)
    (hM : M ∈ SOplus13) :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1), lorentzUnit A hA = M :=
  LorentzSurjectivity.SOplus13_surjective M hM

/-! ## 5. Why the quotient is a quotient by something

Review round 30's fold, and the first item underpins every "double
cover" sentence anywhere in the estate. **If `−1 = 1` in Cl(1,3;ℝ) then
`pmOne` is trivial, the quotient is the whole group, and every theorem
in this file is about nothing.** That was assumed everywhere and proved
nowhere.
-/

/-- **`−1 ≠ 1` in Cl(1,3;ℝ).** The algebra map from ℝ is injective and
    `−1 ≠ 1` there. Everything about `{±1}` being a TWO-element subgroup
    rests on this. -/
theorem neg_one_ne_one_cl : (-1 : Cl) ≠ (1 : Cl) := by
  intro h
  have hr : (-1 : ℝ) = 1 := by
    apply FaithfulSMul.algebraMap_injective ℝ Cl
    simpa using h
  norm_num at hr

/-- So `pmOne` genuinely has two members. -/
theorem pmOne_two_members :
    (1 : spinGroup Q₁₃) ∈ pmOne ∧ negSpin (1 : spinGroup Q₁₃) ∈ pmOne
      ∧ negSpin (1 : spinGroup Q₁₃) ≠ (1 : spinGroup Q₁₃) := by
  refine ⟨Or.inl rfl, Or.inr ?_, negSpin_ne 1⟩
  change -((1 : spinGroup Q₁₃) : Cl) = -1
  norm_num

/-- It is a PROPER subgroup — the π-rotation is outside it. -/
theorem R₁₂'_not_mem_pmOne : R₁₂' ∉ pmOne := by
  rintro (h | h)
  · exact SpinFibre.R₁₂_ne_pm_one.1 h
  · exact SpinFibre.R₁₂_ne_pm_one.2 h

theorem pmOne_ne_top : pmOne ≠ (⊤ : Subgroup (spinGroup Q₁₃)) := fun h =>
  R₁₂'_not_mem_pmOne (h ▸ Subgroup.mem_top R₁₂')

theorem pmOne_ne_bot : pmOne ≠ (⊥ : Subgroup (spinGroup Q₁₃)) := by
  intro h
  have hmem : negSpin (1 : spinGroup Q₁₃) ∈ pmOne := pmOne_two_members.2.1
  rw [h, Subgroup.mem_bot] at hmem
  exact negSpin_ne 1 hmem

/-- **Quotienting by less would not work.** The underlying map is not
    injective, so the trivial subgroup does not serve. -/
theorem spinToSOplus_not_injective : ¬ Function.Injective spinToSOplus := by
  intro hinj
  refine negSpin_ne R₁₂' (hinj (Subtype.ext ?_))
  exact congrArg (fun M : O13 => (M : Matrix.GeneralLinearGroup (Fin 4) ℝ))
    (spinToO13_negSpin R₁₂')

/-- **How to review a `def` that states a gap.** `SurjectivityStatement`
    cannot be tested by proving it — that is the point of it. What can be
    tested is that it says what §4 claims: if it held, the underlying map
    would be onto as well. It does. -/
theorem surjectivityStatement_implies (h : SurjectivityStatement) :
    Function.Surjective spinToSOplus := by
  intro M
  obtain ⟨x, hx⟩ := h M
  induction x using QuotientGroup.induction_on with
  | H g => exact ⟨g, hx⟩

end

end SpinQuotient
