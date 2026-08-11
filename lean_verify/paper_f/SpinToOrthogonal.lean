/-
  SpinToOrthogonal.lean — the bundling half of the stair WALLS.md W7
  maps as step (c): the vector representation as a group homomorphism.

  WHY THIS IS A SEPARATE FILE, AND WHY IT IS LARGER THAN "PACKAGING".

  `SpinVectorRep.lean` proves that each spin element acts on ℝ⁴ as an
  isometry of Q₁₃, that 1 acts as the identity, and that the action is
  multiplicative. W7 asks for one thing more: that this be bundled as a
  monoid homomorphism `spinGroup Q₁₃ →* Q₁₃.IsometryEquiv Q₁₃`. The
  previous session recorded that step as needing no new construction,
  on the grounds that "Mathlib bundles `QuadraticMap.IsometryEquiv`, so
  step (c) has a target — the orthogonal group of Q₁₃ in Mathlib's
  language". **That was wrong, and it is ERRATUM 41.**

  Mathlib has the TYPE `Q.IsometryEquiv Q`. It does not have the GROUP.
  `Mathlib/LinearAlgebra/QuadraticForm/IsometryEquiv.lean` declares
  exactly three instances on it — `EquivLike`, `LinearEquivClass` and
  `CoeOut` — and nowhere in Mathlib is there a `Mul`, `One`, `Inv`,
  `Monoid` or `Group` instance for the self-isometries of a quadratic
  form. `refl`, `symm` and `trans` exist as bare definitions. So there
  is no orthogonal group to be a homomorphism INTO, and a `MonoidHom`
  to that type does not typecheck until something is built.

  §1 builds it, for an arbitrary quadratic map over an arbitrary
  commutative ring, not just for Q₁₃. That is the honest scope: the
  missing object is general, so the fix is general.

  WHAT THIS FILE PROVES:
  1. `Monoid` and `Group` instances on `Q.IsometryEquiv Q` for any
     quadratic map `Q`, with `one_apply` and `mul_apply` fixing the
     composition order (`(f * g) x = f (g x)`, so that homomorphisms
     into it compose the way function application does).
  2. `spinToEndo_congr` — the transport that lets a `spinToEndo` at one
     unit be compared with a `spinToEndo` at an equal unit. Needed
     because `spinToEndo` is indexed by a membership proof whose TYPE
     mentions the unit, so `toUnits (g * h) = toUnits g * toUnits h`
     does not by itself rewrite under it.
  3. **`spinIsom`** — each element of `spinGroup Q₁₃` as an honest
     element of the orthogonal group: a linear EQUIVALENCE (the inverse
     is the action of the inverse element) that preserves Q₁₃.
  4. **`spinRep : spinGroup Q₁₃ →* Q₁₃.IsometryEquiv Q₁₃`** — the
     bundled homomorphism. This is W7's step (c), complete.
  5. `spinRep_R₁₂'_ne_one` and `spinRep_neg_one` — the homomorphism is
     not the trivial one, and −1 is in its kernel. Both inherited from
     `SpinVectorRep` §5–6 rather than reproved, but restated at the
     bundled level, because a homomorphism whose non-triviality is only
     known about its unbundled shadow is not much of a homomorphism.
  6. **`spinRep_not_injective`** — not "one element of the kernel was
     computed" but the failure of injectivity as a theorem, which is
     what a double cover actually requires. With `spinRep_R₁₂'_sq` and
     `R₁₂'_sq_ne_one` putting the factor of two where it belongs:
     `R₁₂'` has order 4, its image has order 2.

  NOT proven here, unchanged from `SpinVectorRep`: that the image is
  SO⁺(1,3), that `spinRep` is onto it, or that its kernel is no larger
  than ±1. That is step (d), it is research-level, and this file gets
  no closer to it than the last one did.

  A note on the instances in §1: they are declared on a Mathlib type
  from outside Mathlib. Nothing else in the estate uses
  `QuadraticMap.IsometryEquiv`, so there is no clash today; if Mathlib
  ever adds its own group structure this section should be deleted
  rather than reconciled.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import SpinVectorRep

open CliffordAlgebra CliffordRealMinkowski SpinVectorRep

noncomputable section

/-! ## 1. The orthogonal group of a quadratic map

Mathlib has `refl`, `symm` and `trans` for isometric equivalences but
no algebraic structure on the self-isometries. The multiplication is
`trans` with its arguments reversed, so that `(f * g) x = f (g x)`. -/

namespace QuadraticMap.IsometryEquiv

section Monoid

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] {Q : QuadraticMap R M N}

instance : One (Q.IsometryEquiv Q) := ⟨IsometryEquiv.refl Q⟩

instance : Mul (Q.IsometryEquiv Q) := ⟨fun f g => g.trans f⟩

@[simp] theorem one_apply (x : M) : (1 : Q.IsometryEquiv Q) x = x := rfl

@[simp] theorem mul_apply (f g : Q.IsometryEquiv Q) (x : M) : (f * g) x = f (g x) := rfl

instance : Monoid (Q.IsometryEquiv Q) where
  mul_assoc _ _ _ := DFunLike.ext _ _ fun _ => rfl
  one_mul _ := DFunLike.ext _ _ fun _ => rfl
  mul_one _ := DFunLike.ext _ _ fun _ => rfl

end Monoid

section Group

/- **The same context as the monoid above, and it used to be stronger.** This section asked for
`[CommRing R] [AddCommGroup M] [AddCommGroup N]` while the section directly above it — the same
structure, one axiom less — asked only for `[CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]`.
Nothing here consumes the difference: the inverse is `IsometryEquiv.symm`, and `inv_mul_cancel` is
`LinearEquiv.left_inv`, neither of which needs negation. Weakened after `ERRATUM 116`, where the
same defect appeared in `IsingTransferSym` and was traced to copying a typeclass context from
elsewhere rather than reading off what the proofs use. -/
variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] {Q : QuadraticMap R M N}

instance : Inv (Q.IsometryEquiv Q) := ⟨IsometryEquiv.symm⟩

@[simp] theorem inv_apply (f : Q.IsometryEquiv Q) (x : M) :
    f⁻¹ x = f.toLinearEquiv.symm x := rfl

instance : Group (Q.IsometryEquiv Q) where
  inv_mul_cancel f := DFunLike.ext _ _ fun x => f.toLinearEquiv.left_inv x

/- **AND THE WEAKENING BITES, CHECKED RATHER THAN ANNOUNCED.** `ℕ` is a `CommSemiring` and not a
ring, and an `AddCommMonoid` is a `ℕ`-module automatically, so this line asks for the isometry group
of a quadratic map with **nothing to subtract anywhere in sight** — which the old `[CommRing R]
[AddCommGroup M]` refused outright. It is an `example` on purpose: it is a witness, not an instance,
and should not enter the instance graph. `check_ledger.py` does not count it as a declaration. -/
example {M N : Type} [AddCommMonoid M] [AddCommMonoid N] (Q : QuadraticMap ℕ M N) :
    Group (Q.IsometryEquiv Q) := inferInstance

end Group

end QuadraticMap.IsometryEquiv

namespace SpinToOrthogonal

/-! ## 2. Comparing the action at equal units

`spinToEndo` takes a membership proof whose type mentions the unit, so
an equation between units does not rewrite under it on its own. -/

theorem spinToEndo_congr {x y : Clˣ} (hx : (x : Cl) ∈ spinGroup Q₁₃)
    (hy : (y : Cl) ∈ spinGroup Q₁₃) (h : x = y) (v : V) :
    spinToEndo hx v = spinToEndo hy v := by
  subst h
  rfl

/-- The underlying unit of a spin-group element is a spin element. -/
theorem toUnits_mem (g : spinGroup Q₁₃) :
    ((spinGroup.toUnits g : Clˣ) : Cl) ∈ spinGroup Q₁₃ := g.2

/-- The action of `g`, as a linear map. -/
def endo (g : spinGroup Q₁₃) : V →ₗ[ℝ] V := spinToEndo (toUnits_mem g)

theorem endo_mul (g h : spinGroup Q₁₃) (v : V) :
    endo (g * h) v = endo g (endo h v) := by
  rw [endo, endo, endo, ← spinToEndo_mul (toUnits_mem g) (toUnits_mem h) v]
  exact spinToEndo_congr _ _ (map_mul spinGroup.toUnits g h) v

theorem endo_one (v : V) : endo (1 : spinGroup Q₁₃) v = v := by
  rw [endo, spinToEndo_congr (toUnits_mem 1) spinGroup_one_mem (map_one spinGroup.toUnits) v,
    spinToEndo_one]
  rfl

theorem endo_inv_left (g : spinGroup Q₁₃) (v : V) : endo g⁻¹ (endo g v) = v := by
  rw [← endo_mul, inv_mul_cancel, endo_one]

theorem endo_inv_right (g : spinGroup Q₁₃) (v : V) : endo g (endo g⁻¹ v) = v := by
  rw [← endo_mul, mul_inv_cancel, endo_one]

/-! ## 3. The bundled homomorphism -/

/-- The action of `g` as a linear equivalence: the inverse is the
    action of `g⁻¹`, which is exactly what the unbundled file could not
    say. -/
def linEquiv (g : spinGroup Q₁₃) : V ≃ₗ[ℝ] V :=
  LinearEquiv.ofLinear (endo g) (endo g⁻¹)
    (LinearMap.ext fun v => endo_inv_right g v)
    (LinearMap.ext fun v => endo_inv_left g v)

@[simp] theorem linEquiv_apply (g : spinGroup Q₁₃) (v : V) : linEquiv g v = endo g v := rfl

/-- **Each spin element as an element of the orthogonal group of Q₁₃.** -/
def spinIsom (g : spinGroup Q₁₃) : Q₁₃.IsometryEquiv Q₁₃ :=
  { linEquiv g with
    map_app' := fun v => spinToEndo_preserves (toUnits_mem g) v }

@[simp] theorem spinIsom_apply (g : spinGroup Q₁₃) (v : V) : spinIsom g v = endo g v := rfl

/-- **W7 step (c), complete: the vector representation as a group
    homomorphism.** -/
def spinRep : spinGroup Q₁₃ →* Q₁₃.IsometryEquiv Q₁₃ where
  toFun := spinIsom
  map_one' := DFunLike.ext _ _ fun v => endo_one v
  map_mul' g h := DFunLike.ext _ _ fun v => endo_mul g h v

@[simp] theorem spinRep_apply (g : spinGroup Q₁₃) (v : V) : spinRep g v = endo g v := rfl

/-! ## 4. The homomorphism is not the trivial one

Inherited from `SpinVectorRep` §5–6 rather than reproved, but restated
here: a bundled homomorphism whose non-triviality is only known of its
unbundled shadow has not really been checked. -/

/-- `R₁₂` as an element of the spin group. -/
def R₁₂' : spinGroup Q₁₃ := ⟨(R₁₂ : Cl), R₁₂_mem⟩

theorem endo_R₁₂' (v : V) : endo R₁₂' v = rotXY v := by
  rw [endo, spinToEndo_congr (toUnits_mem R₁₂') R₁₂_mem (Units.ext rfl) v]
  exact spinToEndo_R₁₂ v

/-- **`spinRep` is not the trivial homomorphism.** -/
theorem spinRep_R₁₂'_ne_one : spinRep R₁₂' ≠ 1 := by
  intro h
  have h1 : spinRep R₁₂' e₁ = (1 : Q₁₃.IsometryEquiv Q₁₃) e₁ := by rw [h]
  rw [spinRep_apply, endo_R₁₂', QuadraticMap.IsometryEquiv.one_apply] at h1
  have h2 : (rotXY e₁).1.2 = (e₁ : V).1.2 := by rw [h1]
  norm_num [rotXY, e₁] at h2

/-- −1 is in the kernel. Together with the previous theorem: the map is
    non-trivial and not injective, which is what a double cover looks
    like from this side. Not proved, here or anywhere: that the kernel
    is no LARGER than ±1. -/
theorem spinRep_neg_one : spinRep ⟨((-1 : Clˣ) : Cl), neg_one_mem⟩ = 1 := by
  refine DFunLike.ext _ _ fun v => ?_
  rw [spinRep_apply, endo,
    spinToEndo_congr (toUnits_mem ⟨((-1 : Clˣ) : Cl), neg_one_mem⟩) neg_one_mem
      (Units.ext rfl) v,
    spinToEndo_neg_one]
  rfl

/-! ## 5. The double cover, stated at the bundled level

Review round 17 attacked the inverse — the piece a `LinearEquiv` carries
as data and that nothing downstream recomputes — and it held. What the
round produced that the file did not yet say is below: the failure of
injectivity as a theorem rather than as a single computed instance, and
the order mismatch that makes the covering visible. -/

/-- The inverse of the π-rotation is the π-rotation: `rotXY` is an
    involution, so the inverse element acts the same way. Recorded
    because a wrong inverse in `linEquiv` would be invisible at every
    use site. -/
theorem spinIsom_R₁₂'_inv (v : V) : (spinIsom R₁₂')⁻¹ v = rotXY v := by
  have h := endo_inv_left R₁₂' (rotXY v)
  rw [endo_R₁₂'] at h
  have hinv : rotXY (rotXY v) = v := by simp [rotXY]
  rw [hinv] at h
  change endo R₁₂'⁻¹ v = rotXY v
  rw [← h]

/-- −1 and 1 are different elements of the spin group. -/
theorem neg_one_ne_one : (⟨((-1 : Clˣ) : Cl), neg_one_mem⟩ : spinGroup Q₁₃) ≠ 1 := by
  intro h
  have h3 : ((-1 : Clˣ) : Cl) = ((1 : spinGroup Q₁₃) : Cl) := congrArg Subtype.val h
  have hr : (-1 : ℝ) = 1 := by
    apply FaithfulSMul.algebraMap_injective ℝ Cl
    simpa using h3
  norm_num at hr

/-- **`spinRep` is not injective.** Not "we computed one element of the
    kernel" — the map genuinely fails to be injective, which is the
    statement a double cover requires. What is NOT proved, here or
    anywhere in the estate, is the other side: that the kernel is no
    larger than ±1. -/
theorem spinRep_not_injective : ¬ Function.Injective spinRep := by
  intro hinj
  exact neg_one_ne_one (hinj (by rw [spinRep_neg_one, map_one]))

/-- The image of `R₁₂'` squares to the identity: order 2 downstairs. -/
theorem spinRep_R₁₂'_sq : spinRep R₁₂' * spinRep R₁₂' = 1 := by
  rw [← map_mul]
  refine DFunLike.ext _ _ fun v => ?_
  rw [spinRep_apply, endo_mul, endo_R₁₂', endo_R₁₂',
    QuadraticMap.IsometryEquiv.one_apply]
  simp [rotXY]

/-- But `R₁₂'` itself does not: order 4 upstairs. **This is the factor
    of two, stated where it belongs — between a group element and its
    image.** -/
theorem R₁₂'_sq_ne_one : R₁₂' * R₁₂' ≠ 1 := by
  intro h
  have hv : ((R₁₂' * R₁₂' : spinGroup Q₁₃) : Cl) = 1 := by rw [h]; rfl
  rw [show ((R₁₂' * R₁₂' : spinGroup Q₁₃) : Cl) = (R₁₂ : Cl) * (R₁₂ : Cl) from rfl,
    R₁₂_sq] at hv
  have hr : (-1 : ℝ) = 1 := by
    apply FaithfulSMul.algebraMap_injective ℝ Cl
    simpa using hv
  norm_num at hr

end SpinToOrthogonal
