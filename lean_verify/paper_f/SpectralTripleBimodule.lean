/-
  SpectralTripleBimodule: the pair `(A, A°)` as ONE algebra, and which axiom does the cutting

  SPINE LINK L6 — WALL W9, RUNG 2. `WALLS` §W9.1 names this unit in its own words:
  *"Abstracting `piOp` over a variable algebra is the next unit; deriving a constraint on
  the factor list from it is the rung."* It is the spine's highest-Caesar step, ranked 1 of
  12 and labelled **hard, unblocks 6**.

  WHAT WAS THERE. Rung 1 was climbed on 2026-09-14: `StarRepSemisimple` proves that a
  finite-dimensional ⋆-algebra with a FAITHFUL ⋆-representation on an inner-product space is
  semisimple. `WALLS` §W9.1 then says exactly what blocks rung 2: *"what is missing to state
  rung 2 is the second algebra: CCM's order-one condition is about `A` and the opposite
  algebra `A°` acting on the same `H` with commuting images, and the estate has the SHAPE of
  that — `KOSixSpectralTriple`'s `piOp` and `commutant_condition` — for `A = Mₙ(ℂ)` only."*

  THE MATHLIB IMPORT THAT MAKES THE RUNG STATEABLE, and it was one search away.
  `Algebra.TensorProduct.lift` takes `f : A →ₐ[S] C`, `g : B →ₐ[R] C` and a proof of
  `∀ x y, Commute (f x) (g y)` to a single `A ⊗[R] B →ₐ[S] C`. **Its hypothesis IS the
  order-zero condition**, verbatim. So the pair `(A, A°)` acting on `H` with commuting images
  is not two maps to be reasoned about together — it is **one algebra map out of
  `A ⊗[𝕂] Aᵐᵒᵖ`**, and `bimodule` below is that map. That is the object rung 2 needs, and no
  new mathematics was required to build it.

  WHAT THIS FILE ESTABLISHES.
  * **`Triple`** — over a VARIABLE algebra: `π`, `πOp`, `D`, `J`, `γ`, both ⋆-conditions,
    order-zero, order-one, the KO-6 signs `(ε, ε′, ε″) = (1, 1, -1)`, **and `πOp_impl`** as
    fields. ~~the `structure FiniteRealSpectralTriple` §W9.1 asks for~~ — **that description
    was FALSE until 2026-09-15 and is now true again, `ERRATUM 573`.** The missing axiom was
    `πOp_impl`: in CCM the right action is not a datum but `b° = J π(b*) J⁻¹`, so order-zero
    and order-one relate THREE objects and not four. For nine units `πOp` was an independent
    field with nothing tying it to `J`, and `OppositeFromRealStructure` measured the gap and
    found it real rather than notional — `OrderOneNontrivial`'s witness satisfied every other
    field and **failed CCM's order-zero for the `J`-implemented action**, so it was deleted
    when the field was added and `RealSpectralWitness.realWitness` replaces it. The gap was
    invisible until `ERRATUM 571`'s repair, because a `ℂ`-linear `J` could not form
    `J π(b*) J` at all: **a missing axiom hid behind a wrong type.**
    **`J` is conjugate-linear, `H →ₗ⋆[𝕜] H`**;
    it was a `Module.End 𝕜 H` until `ERRATUM 571`. Parametrised over the ground field `𝕂` so
    that both CCM's real case (`𝕂 = ℝ`, `𝕜 = ℂ`) and the estate's own complex case
    (`𝕂 = 𝕜 = ℂ`, where `CascadeEnd`'s Azumaya chain lives) are instances of one object.
  * **`bimodule`** and `bimodule_tmul` — order-zero as a single algebra map.
  * **`bimodule_star`** — the ⋆-condition transported to the doubled algebra, by induction on
    the tensor product. The proof needs order-zero a second time, at `(star a, star b)`.
  * **`doubled_isSemisimple`** — rung 1 applied to the DOUBLED algebra: a faithful bimodule
    forces `IsSemisimpleRing (A ⊗[𝕂] Aᵐᵒᵖ)`. `StarRepSemisimple`'s theorem had only ever been
    applied to `A`.
  * **`finrank_mul_finrank_le`** — the dimension constraint: a faithful bimodule forces
    `(dim A)² ≤ dim (End H)`, so `dim A ≤ dim H` at `𝕂 = 𝕜` (`finrank_le_of_faithful`).
  * **`oneForm_commutes`** and `oneForms_and_pi_commute` — order-one's content: the one-forms
    `⁅D, π a⁆` lie in the commutant of `πOp`'s image, alongside `π`'s own image. That is what
    makes CCM's inner fluctuations well defined.
  * **`scalarWitness`** and `triple_inhabited` — the structure is INHABITED, so nothing below is
    vacuous: `A = 𝕂 = 𝕜 = ℂ` acting by scalars on `EuclideanSpace ℂ (Fin 2)`, with `γ = σ₃`
    through Mathlib's `Matrix.toEuclideanCLM`, and `J` the CONJUGATE-LINEAR coordinate swap
    `v ↦ (conj (v 1), conj (v 0))` from `ConjugatePermutation.conjPerm`. `J` and `γ`
    anticommute — the KO-6 sign `ε″ = -1`, which is what forces dimension at least two — and
    `swap_pauli3` is the one matrix identity that delivers it. **Exhibited because
    a structure nobody can instantiate is a vacuous object, and this campaign has already
    shipped one vacuous statement it had to retract** (`ERRATUM 557`).

  AND THE FINDING, WHICH IS A NEGATIVE ONE AND IS THE POINT OF THE UNIT.
  `orderOne_of_commute_D` proves that order-one holds **automatically** whenever `D` commutes
  with every `π a`. So order-one is VACUOUS on the commutant, and constrains only through a
  `D` that fails to commute. Together with the semisimplicity result that means:

  > **the order-zero condition, plus faithfulness, yields exactly rung 1 again and no more.**

  **Which half of that is machine-checked, stated exactly, because the two halves have very
  different standing.** MACHINE-CHECKED here: `doubled_isSemisimple` (order-zero plus
  faithfulness gives `IsSemisimpleRing (A ⊗[𝕂] Aᵐᵒᵖ)`) and `orderOne_of_commute_D`
  (order-one is free whenever `D` is in the commutant). CITED AND **NOT** PROVED HERE: that
  over a field of characteristic zero a finite-dimensional algebra is semisimple iff it is
  separable iff `A ⊗ Aᵒᵖ` is semisimple — the standard separability criterion, true of `ℝ`
  and `ℂ` because char-0 fields are perfect, and the reason `doubled_isSemisimple` and rung 1
  are the same constraint wearing different clothes. **The negative conclusion is therefore
  one machine-checked implication plus one cited equivalence, not a theorem**, and it is
  labelled that way here rather than in a footnote.

  What it buys even so is the location of the operative axiom: the cut in the factor list
  that rungs 3–5 need cannot come from order-zero, and must come from order-one together
  with `J` and `γ` — which is what §W9.1 suspected and did not establish. `oneForm_commutes`
  is the first theorem in this estate about what order-one says; `orderOne_of_commute_D` is
  the first about when it says nothing.

  AND THE FINDING SHARPENS ONCE MORE, which was not planned and is the better half.
  `orderOne_of_central_piOp` proves that order-one holds for **every** `D` whatever — not
  merely for a `D` in the commutant — as soon as `πOp`'s image is CENTRAL. Now put that
  beside order-zero, which already forces `πOp A°` into the commutant of `π A`: **if `π` is
  irreducible, that commutant is the scalars by Schur, `πOp` is central, and order-one says
  nothing at all, for any Dirac operator however far from central.** So order-one has content
  only where `π` is REDUCIBLE — which is why CCM's `H` is a large reducible space and not an
  irreducible one, and which turns *"what does order-one do to the pair"* from an open
  question into a question about the reducible case specifically. (The Schur half is standard
  and is cited, not proved here; `orderOne_of_central_piOp` is the implication from
  centrality and is machine-checked.) **And the witness below is an instance of exactly this
  trap**: its `π` is scalar, so no choice of `D` would have made its order-one say anything.

  WHAT IS **NOT** CLAIMED, and the wall does not fall.
  * **Rung 2 is not climbed.** The rung is *"which involutions `∏ Mₐᵢ(Dᵢ)` admits, and what
    the order-one condition does to the pair"*. This file builds the pair, proves what
    order-zero gives, and proves that it is not enough. The classification argument itself is
    not here and no factor list is cut.
  * **Rung 2's own next step is now stateable and is not taken here.** The finding says the
    content lives in the reducible case; the unit does not then go on to classify the
    reducible ones, and no decomposition of `H` into `π`-isotypic pieces is built.
  * ~~**`J` is a linear map, not an antilinear one.**~~ **THE FIELD HAS BEEN WIDENED and the
    defect is gone — `ERRATUM 571`.** `J` now has type `H →ₛₗ[starRingEnd 𝕜] H`, which Lean
    prints as `H →ₗ⋆[𝕜] H` and which is exactly a conjugate-linear map; the three KO-6 sign
    axioms are now conditions on the right kind of object, and `scalarWitness` below carries
    a genuine real structure. The withdrawn excuse read *"Mathlib's `LinearMap` cannot
    express that at this signature"*: Mathlib's `LinearMap` is SEMILINEAR by default, and
    `RingHomCompTriple (starRingEnd 𝕜) (starRingEnd 𝕜) (RingHom.id 𝕜)` is what makes
    `J.comp J = LinearMap.id` a statable identity. **What remains true, and is much
    narrower**, is that a `J` of this kind cannot be STORED in `Module.End 𝕜 H` — a fact
    about a type, not about the library.
  * **`J` still does no work in §2–§6, and widening it did not change that.** No theorem
    between `bimodule` and `orderOne_of_central_piOp` mentions `J`; the KO-6 signs constrain
    only the witnesses. Making the field honest is not the same as making it load-bearing,
    and this unit did the first, not the second.
  * **`KOSixSpectralTriple` is NOT an instance of `Triple`, and cannot be.** `KOSixAlgebraAction`
    machine-checked that its `piRep` is **not additive in the matrix**
    (`piRep_not_additive_in_matrix`), so it is not a `RingHom`, let alone an `AlgHom`. The
    genuine ⋆-representation built there, `particleRep`, discards the antiparticle blocks and
    so is not that triple either. **This structure is therefore not yet instantiated at the
    estate's own spectral triple**, which is L18's standing residue (`ERRATUM 565`,
    `UNLOCK_WATCHLIST` 261).
  * **No `K`-theory, no intersection form, no Poincaré duality** — rungs 3–5, which §W9.1
    calls *"a subject, not a project"*.
  * The cascade's `M₄(ℂ)` as the algebra (`ASSUMPTIONS_LEDGER` 19), and which real structure
    the cascade carries (18, 48, a DECISIONS NEEDED item), are untouched.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import StarRepSemisimple
import CascadeEnd
import ConjugatePermutation

namespace SpectralTripleBimodule

open scoped TensorProduct
open MulOpposite

noncomputable section

/-! ## 1. The structure `WALLS` §W9.1 asks for, over a variable algebra -/

/-- A finite spectral triple over a VARIABLE `𝕂`-algebra `A`, with both algebra actions,
the two order conditions and the KO-6 signs `(ε, ε′, ε″) = (1, 1, -1)` as fields.

`𝕂` is the ground field of the algebra and `𝕜` the field of the Hilbert space: CCM's real
case is `𝕂 = ℝ`, `𝕜 = ℂ`, and the estate's own complex objects are `𝕂 = 𝕜 = ℂ`.

**`J` is carried as a CONJUGATE-LINEAR map**, `H →ₛₗ[starRingEnd 𝕜] H`, which is what a real
structure is. It was a `Module.End 𝕜 H` until `ERRATUM 571` — see the header. Nothing else
below uses it; the witnesses do. -/
structure Triple (𝕂 𝕜 A H : Type*) [Field 𝕂] [RCLike 𝕜] [Algebra 𝕂 𝕜]
    [Ring A] [StarRing A] [Algebra 𝕂 A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [Module 𝕂 H] [IsScalarTower 𝕂 𝕜 H] where
  /-- The algebra acting on `H`. -/
  π : A →ₐ[𝕂] Module.End 𝕜 H
  /-- The OPPOSITE algebra acting on the same `H` — CCM's `π°`, `KOSixSpectralTriple`'s `piOp`
  abstracted over `A`. -/
  πOp : Aᵐᵒᵖ →ₐ[𝕂] Module.End 𝕜 H
  /-- The Dirac operator. -/
  D : Module.End 𝕜 H
  /-- **The real structure, carried as a CONJUGATE-LINEAR map** — `H →ₛₗ[starRingEnd 𝕜] H`,
  which Lean prints as `H →ₗ⋆[𝕜] H`. This field was `Module.End 𝕜 H` until `ERRATUM 571`; see
  the header. -/
  J : H →ₛₗ[starRingEnd 𝕜] H
  /-- The grading. -/
  γ : Module.End 𝕜 H
  /-- `π` is a ⋆-representation, stated through the inner product as `StarRepSemisimple` does
  (which avoids needing a `StarRing (Module.End 𝕜 H)` instance). -/
  star_π : ∀ (a : A) (u v : H), inner 𝕜 (π a u) v = inner 𝕜 u (π (star a) v)
  /-- `πOp` is a ⋆-representation. -/
  star_πOp : ∀ (b : Aᵐᵒᵖ) (u v : H), inner 𝕜 (πOp b u) v = inner 𝕜 u (πOp (star b) v)
  /-- **The order-zero condition**: the two images commute. -/
  order_zero : ∀ (a : A) (b : Aᵐᵒᵖ), Commute (π a) (πOp b)
  /-- **The order-one condition**: the one-forms commute with the opposite action. -/
  order_one : ∀ (a : A) (b : Aᵐᵒᵖ), ⁅⁅D, π a⁆, πOp b⁆ = 0
  /-- KO-6 sign `ε = 1`. Two conjugate-linear maps compose to a `𝕜`-LINEAR one — that is
  `RingHomCompTriple (starRingEnd 𝕜) (starRingEnd 𝕜) (RingHom.id 𝕜)` — so `LinearMap.id` is
  the right-hand side and the identity is statable. -/
  J_sq : J.comp J = LinearMap.id
  /-- KO-6 sign `ε′ = 1`. Both sides are conjugate-linear, by `RingHomCompTriple.ids` and
  `RingHomCompTriple.right_ids`. -/
  J_comm_D : J.comp D = D.comp J
  /-- KO-6 sign `ε″ = -1`. -/
  J_anticomm_γ : J.comp γ = -(γ.comp J)
  /-- The grading is an involution. -/
  γ_sq : γ * γ = 1
  /-- **CCM'S RELATION, and the axiom this structure was missing until `ERRATUM 573`.**
  In Connes' definition the right action is not a datum: it is `b° = J π(b*) J⁻¹`, manufactured
  from the real structure. Without this field `πOp` is a free parameter and the structure is
  strictly weaker than a real spectral triple — `OppositeFromRealStructure` measured the gap
  and found it real, not notional. Stated pointwise because `J` is semilinear, so
  `J ∘ π(b*) ∘ J` is a composite of three maps with two different scalar twists and writing it
  as an equation of bundled maps would need the `RingHomCompTriple` instances spelled out at
  every use. -/
  πOp_impl : ∀ (b : Aᵐᵒᵖ) (v : H), πOp b v = J (π (star (MulOpposite.unop b)) (J v))

variable {𝕂 𝕜 A H : Type*} [Field 𝕂] [RCLike 𝕜] [Algebra 𝕂 𝕜]
  [Ring A] [StarRing A] [Algebra 𝕂 A]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [Module 𝕂 H] [IsScalarTower 𝕂 𝕜 H]

/-! ## 2. Order-zero IS the tensor-lift hypothesis: the pair is one algebra -/

/-- **The rung-2 object.** `Algebra.TensorProduct.lift`'s hypothesis is exactly `order_zero`,
so the pair `(A, A°)` acting on `H` with commuting images is a single algebra map out of
`A ⊗[𝕂] Aᵐᵒᵖ`. -/
def bimodule (T : Triple 𝕂 𝕜 A H) : A ⊗[𝕂] Aᵐᵒᵖ →ₐ[𝕂] Module.End 𝕜 H :=
  Algebra.TensorProduct.lift T.π T.πOp T.order_zero

@[simp]
theorem bimodule_tmul (T : Triple 𝕂 𝕜 A H) (a : A) (b : Aᵐᵒᵖ) :
    bimodule T (a ⊗ₜ[𝕂] b) = T.π a * T.πOp b :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem bimodule_left (T : Triple 𝕂 𝕜 A H) (a : A) :
    bimodule T (a ⊗ₜ[𝕂] 1) = T.π a := by
  rw [bimodule_tmul, map_one, mul_one]

theorem bimodule_right (T : Triple 𝕂 𝕜 A H) (b : Aᵐᵒᵖ) :
    bimodule T ((1 : A) ⊗ₜ[𝕂] b) = T.πOp b := by
  rw [bimodule_tmul, map_one, one_mul]

/-! ## 3. The ⋆-condition on the doubled algebra -/

section Star

variable [StarRing 𝕂] [StarModule 𝕂 A]

/-- The ⋆-condition transported to `A ⊗[𝕂] Aᵐᵒᵖ`, by induction on the tensor product. **The
proof uses order-zero a second time**, at `(star a, star b)`: pushing `π (star a)` past
`πOp (star b)` is what makes the two adjoints compose in the right order. -/
theorem bimodule_star (T : Triple 𝕂 𝕜 A H) (x : A ⊗[𝕂] Aᵐᵒᵖ) (u v : H) :
    inner 𝕜 (bimodule T x u) v = inner 𝕜 u (bimodule T (star x) v) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      rw [TensorProduct.star_tmul, bimodule_tmul, bimodule_tmul]
      have h : T.π (star a) * T.πOp (star b) = T.πOp (star b) * T.π (star a) :=
        T.order_zero (star a) (star b)
      rw [h]
      simp only [Module.End.mul_apply]
      rw [T.star_π, T.star_πOp]
  | add x y hx hy =>
      rw [star_add, map_add, map_add]
      simp only [LinearMap.add_apply, inner_add_left, inner_add_right, hx, hy]

end Star

/-! ## 4. Rung 1, applied to the DOUBLED algebra -/

section Semisimple

variable [StarRing 𝕂] [StarModule 𝕂 A] [Module.Finite 𝕂 A]

/-- **Rung 1 on the pair.** A faithful bimodule forces the doubled algebra
`A ⊗[𝕂] Aᵐᵒᵖ` to be semisimple. `StarRepSemisimple`'s theorem had only ever been applied to
`A` itself; this is the first time it is applied to the object the order-zero condition
produces. -/
theorem doubled_isSemisimple (T : Triple 𝕂 𝕜 A H)
    (hinj : Function.Injective (bimodule T)) :
    IsSemisimpleRing (A ⊗[𝕂] Aᵐᵒᵖ) :=
  haveI : IsArtinianRing (A ⊗[𝕂] Aᵐᵒᵖ) := IsArtinianRing.of_finite 𝕂 _
  StarRepSemisimple.isSemisimpleRing_of_faithful_star_rep
    (bimodule T).toRingHom hinj (bimodule_star T)

omit [StarRing 𝕂] [StarModule 𝕂 A] in
/-- Rung 1 itself, in the structure's vocabulary: a faithful `π` forces `A` semisimple. -/
theorem isSemisimple_of_faithful_pi (T : Triple 𝕂 𝕜 A H)
    (hinj : Function.Injective T.π) :
    IsSemisimpleRing A :=
  haveI : IsArtinianRing A := IsArtinianRing.of_finite 𝕂 A
  StarRepSemisimple.isSemisimpleRing_of_faithful_star_rep
    (T.π).toRingHom hinj T.star_π

end Semisimple

/-! ## 5. The dimension constraint order-zero DOES give -/

section Dimension

variable [Module.Finite 𝕂 A] [FiniteDimensional 𝕜 H] [Module.Finite 𝕂 𝕜]

omit [StarRing A] [Module.Finite 𝕂 A] in
theorem finrank_op : Module.finrank 𝕂 Aᵐᵒᵖ = Module.finrank 𝕂 A :=
  (opLinearEquiv 𝕂 (M := A)).symm.finrank_eq

omit [Module.Finite 𝕂 A] in
/-- **The constraint.** A faithful bimodule forces `(dim A)² ≤ dim (End H)`. This is what the
order-zero condition buys, stated as a number rather than as a structure. -/
theorem finrank_mul_finrank_le (T : Triple 𝕂 𝕜 A H)
    (hinj : Function.Injective (bimodule T)) :
    Module.finrank 𝕂 A * Module.finrank 𝕂 A
      ≤ Module.finrank 𝕂 (Module.End 𝕜 H) := by
  haveI : Module.Finite 𝕂 (Module.End 𝕜 H) := Module.Finite.trans 𝕜 (Module.End 𝕜 H)
  have hfin : Module.finrank 𝕂 (A ⊗[𝕂] Aᵐᵒᵖ) = Module.finrank 𝕂 A * Module.finrank 𝕂 A := by
    rw [Module.finrank_tensorProduct, finrank_op]
  calc Module.finrank 𝕂 A * Module.finrank 𝕂 A
      = Module.finrank 𝕂 (A ⊗[𝕂] Aᵐᵒᵖ) := hfin.symm
    _ ≤ Module.finrank 𝕂 (Module.End 𝕜 H) :=
        LinearMap.finrank_le_finrank_of_injective (f := (bimodule T).toLinearMap) hinj

end Dimension

/-! ## 6. What order-one says, and when it says nothing -/

/-- **Order-one's content**: every one-form `⁅D, π a⁆` commutes with the whole image of
`πOp`. Together with `order_zero` this puts `π A` and `⁅D, π A⁆` in the SAME commutant, which
is what makes CCM's inner fluctuations `D + ∑ π(a) ⁅D, π(b)⁆` well defined. -/
theorem oneForm_commutes (T : Triple 𝕂 𝕜 A H) (a : A) (b : Aᵐᵒᵖ) :
    Commute ⁅T.D, T.π a⁆ (T.πOp b) :=
  commute_iff_lie_eq.mpr (T.order_one a b)

/-- `π`'s image and the one-forms lie in the same commutant. -/
theorem oneForms_and_pi_commute (T : Triple 𝕂 𝕜 A H) (a : A) (b : Aᵐᵒᵖ) :
    Commute (T.π a) (T.πOp b) ∧ Commute ⁅T.D, T.π a⁆ (T.πOp b) :=
  ⟨T.order_zero a b, oneForm_commutes T a b⟩

omit [StarRing A] in
/-- **THE FINDING, and it is negative.** If `D` commutes with every `π a` then the order-one
condition holds for free, whatever `πOp` is. So order-one is VACUOUS on the commutant of
`π`'s image, and can only constrain through a `D` that fails to commute — which is why the
cut in the factor list that rungs 3–5 need cannot come from order-zero, and must come from
order-one together with `J` and `γ`. -/
theorem orderOne_of_commute_D
    (π : A →ₐ[𝕂] Module.End 𝕜 H) (πOp : Aᵐᵒᵖ →ₐ[𝕂] Module.End 𝕜 H)
    (D : Module.End 𝕜 H) (hD : ∀ a : A, Commute D (π a)) :
    ∀ (a : A) (b : Aᵐᵒᵖ), ⁅⁅D, π a⁆, πOp b⁆ = 0 := by
  intro a b
  have h : ⁅D, π a⁆ = 0 := commute_iff_lie_eq.mp (hD a)
  rw [h]
  simp [Ring.lie_def]

/-- And the same for the ⋆-condition side: a `D` in the commutant makes every one-form zero,
so the one-form module is trivial. Stated separately because it is the statement a reader of
`oneForm_commutes` needs in order to see that the theorem has content only off the
commutant. -/
theorem oneForms_trivial_of_commute_D (T : Triple 𝕂 𝕜 A H)
    (hD : ∀ a : A, Commute T.D (T.π a)) (a : A) :
    ⁅T.D, T.π a⁆ = 0 :=
  commute_iff_lie_eq.mp (hD a)

omit [StarRing A] in
/-- **The sharper version, and it is the one that matters.** If `πOp`'s image is CENTRAL in
`Module.End 𝕜 H` then order-one holds for every `D` whatever, not only for a `D` in the
commutant. Combined with order-zero this is a strong statement about when the axiom is
empty: order-zero already puts `πOp A°` inside the commutant of `π A`, so **if `π` is
irreducible then that commutant is the scalars by Schur, `πOp` is central, and order-one
says nothing at all** — for any `D`, however far from central. Order-one therefore has
content only where `π` is REDUCIBLE, which is why CCM's `H` is a large reducible space and
not an irreducible one. (The Schur half of that sentence is standard and is not proved here;
what is proved is the implication from centrality.) -/
theorem orderOne_of_central_piOp
    (π : A →ₐ[𝕂] Module.End 𝕜 H) (πOp : Aᵐᵒᵖ →ₐ[𝕂] Module.End 𝕜 H)
    (D : Module.End 𝕜 H) (hc : ∀ (b : Aᵐᵒᵖ) (x : Module.End 𝕜 H), Commute (πOp b) x) :
    ∀ (a : A) (b : Aᵐᵒᵖ), ⁅⁅D, π a⁆, πOp b⁆ = 0 :=
  fun a b => commute_iff_lie_eq.mp ((hc b ⁅D, π a⁆).symm)

/-! ## 7. The structure is INHABITED, and the witness demonstrates the finding -/

/-- `σ₃`, the grading of the witness. Named `pauli3` rather than `sigma3` because
`MinkowskiHerm2` already declares a `sigma3` — and declares it `private`, so it cannot be
imported and reused. The distinct name is the honest fix; an accept line recording the
collision would have been the cheap one. -/
def pauli3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- `σ₁`, the real structure of the witness. -/
def pauli1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Matrices as endomorphisms of `EuclideanSpace ℂ (Fin 2)`, through Mathlib's
`Matrix.toEuclideanCLM` (a `StarAlgEquiv`) and `ContinuousLinearMap.toLinearMapRingHom` (a
`RingHom`). Being a composite of those two, `mEnd` preserves `1`, `*` and `-`, which is
exactly what the KO-6 sign identities need. -/
def mEnd (M : Matrix (Fin 2) (Fin 2) ℂ) : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) :=
  ContinuousLinearMap.toLinearMapRingHom (Matrix.toEuclideanCLM (𝕜 := ℂ) M)

theorem pauli3_sq : pauli3 * pauli3 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli3, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauli1_sq : pauli1 * pauli1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli1, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauli1_anticomm : pauli1 * pauli3 = -(pauli3 * pauli1) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauli1, pauli3, Matrix.mul_apply, Fin.sum_univ_two]

/-- The matrix identity `scalarWitness`'s KO-6 sign `ε″ = -1` reduces to: conjugating `σ₃`'s
entries and swapping its indices returns `-σ₃`. Real and anti-invariant, which is exactly
`ConjugatePermutation.conjPerm_anticommute_of_neg`'s hypothesis. -/
theorem swap_pauli3 :
    (pauli3.submatrix (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)).map
        (starRingEnd ℂ) = -pauli3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli3, Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- **A witness, so the structure is not vacuous.** `A = 𝕂 = 𝕜 = ℂ` acting by scalars on
`EuclideanSpace ℂ (Fin 2)`, with `γ = σ₃`, `J` the CONJUGATE-LINEAR coordinate swap
`v ↦ (conj (v 1), conj (v 0))` (which anticommutes with `γ`, as the KO-6 sign `ε″ = -1`
demands, and which forces dimension at least two) and `D = 0`. **`J` was `σ₁` acting linearly
until `ERRATUM 571`; the witness now carries a genuine real structure.**

**And the witness demonstrates the finding rather than evading it.** Its `D` is `0`, so it
satisfies order-one for exactly the trivial reason `orderOne_of_commute_D` names; and its `π`
is scalar, so `orderOne_of_central_piOp` applies too and NO choice of `D` would have made
order-one say anything here. **An inhabited structure whose only easy witnesses make the
operative axiom vacuous is precisely the state of rung 2**, and that is the honest summary of
this unit. -/
def scalarWitness : Triple ℂ ℂ ℂ (EuclideanSpace ℂ (Fin 2)) where
  π := Algebra.ofId ℂ _
  πOp := (Algebra.ofId ℂ _).comp (AlgEquiv.toOpposite ℂ ℂ).symm.toAlgHom
  D := 0
  J := ConjugatePermutation.conjPerm (Equiv.swap 0 1)
  γ := mEnd pauli3
  star_π a u v := by
    simp only [Algebra.ofId_apply]
    rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      inner_smul_left, inner_smul_right]
    simp
  star_πOp b u v := by
    simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.ofId_apply]
    rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      inner_smul_left, inner_smul_right]
    simp
  order_zero a b := Algebra.commute_algebraMap_left _ _ |>.trans (by rfl)
  order_one a b := by simp [Ring.lie_def]
  J_sq := ConjugatePermutation.conjPerm_comp_self _ (Equiv.swap_apply_self 0 1)
  J_comm_D := by ext v i; simp
  J_anticomm_γ := by
    refine LinearMap.ext fun v => ?_
    simpa [mEnd, ContinuousLinearMap.toLinearMapRingHom] using
      ConjugatePermutation.conjPerm_anticommute_of_neg (Equiv.swap (0 : Fin 2) 1) pauli3
        swap_pauli3 v
  γ_sq := by unfold mEnd; rw [← map_mul, ← map_mul, pauli3_sq, map_one, map_one]
  πOp_impl b v := by
    simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.ofId_apply,
      Module.algebraMap_end_apply, ConjugatePermutation.conjPerm_conj_smul,
      ConjugatePermutation.conjPerm_involutive (Equiv.swap (0 : Fin 2) 1)
        (Equiv.swap_apply_self 0 1)]
    simp

theorem triple_inhabited : Nonempty (Triple ℂ ℂ ℂ (EuclideanSpace ℂ (Fin 2))) := ⟨scalarWitness⟩

end

end SpectralTripleBimodule
