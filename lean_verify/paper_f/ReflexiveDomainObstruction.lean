import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fintype.Card

/-!
# Why `D ≃ (D → D)` is impossible, and what changes when the arrow is continuous

`WALLS.md` W8 (the non-trivial reflexive domain, `D∞`) is the estate's other wall with **no
staircase climbed at all**. Its failing step reads:

> *"a Scott-style `D∞` construction (continuous lattices, inverse limits of function spaces).
> Mathlib has domain-theoretic fragments (ω-CPOs) but not the `D ≃ (D → D)` construction."*

This file does not build `D∞`. What it does is **prove the obstruction that makes `D∞` necessary**,
which nothing in this estate or in Mathlib states, and then locate exactly where that obstruction
stops applying — which is the whole content of Scott's move.

> **`subsingleton_of_setReflexive`** — if `D ≃ (D → D)` as bare types then `D` has at most one
> element. Cantor, via a surjection onto `Set D` built out of the equivalence.
>
> **`isSetReflexive_iff`** — and that is sharp in both directions: `D ≃ (D → D)` holds **exactly
> when** `D` is a nonempty subsingleton. So the naive equation is not merely unproved in this
> estate, it is **false** for every `D` anyone would want.
>
> **`not_surjective_coe_continuousHom`** — the continuous self-maps of `Prop` are a **proper**
> subcollection of all its self-maps, `Not` being the witness. That is not a remark: it is the
> precise reason the theorem above says nothing about `D ≃ (D →𝒄 D)`.
>
> **`not_isDomainReflexive_of_finite`** — and no **finite** `D` with more than one element solves
> the continuous equation either, because the constant maps already inject `D` into `D →𝒄 D` and
> miss the identity. Any solution is infinite, which is what `D∞` is, and `dInfExists_infinite`
> states that as a constraint on the target rather than as a fact about finite types.

## The estate's existing `ReflexiveDomain` is a complete lattice and nothing more

`ReflexiveDomainFP.lean` declares `class ReflexiveDomain (D) extends CompleteLattice D` with **no
further field**, so it is definitionally `CompleteLattice` and every theorem in that file is
Knaster–Tarski. Those theorems are true and the file's own docstring says the class is a model
rather than the thing. **Nothing anywhere in the estate carries `D ≃ (D → D)` in any form**, which
is why the statement had to be written down here before it could be refuted.

## What this file does NOT do

**It does not build `D∞` and does not shorten that construction by one line.** `DInfExists` below
names the target and is not proved. This file supplies the two facts that bracket it: the naive
equation is impossible, and the continuous equation is impossible for finite `D`. Between those
sits an inverse limit of ω-CPOs along embedding–projection pairs, and neither Mathlib nor this
estate has one.

**Probed 2026-08-11, by shape.** Mathlib has `OmegaCompletePartialOrder` (80 declarations in
`Order/OmegaCompletePartialOrder.lean`), the continuous-hom bundling `ContinuousHom` with notation
`→𝒄`, and crucially `instance : OmegaCompletePartialOrder (α →𝒄 β)` — so the function-space
functor's action on objects is **already there**. `Order/DirectedInverseSystem.lean` has
`DirectedSystem` and `DirectLimit`, but that is a **direct** limit built as a quotient of a sigma
type, not an inverse limit, and it is not about ω-CPOs. `InverseLimit` matches exactly one file in
all of Mathlib and it is `FieldTheory/CardinalEmb.lean`. `DomainTheory` and `ReflexiveDomain`:
zero files each.
-/

namespace ReflexiveDomainObstruction

open OmegaCompletePartialOrder

/-! ## 1. The two equations, told apart -/

/-- **The naive reflexive equation**: `D` is isomorphic to *all* of its self-maps. -/
def IsSetReflexive (D : Type u) : Prop := Nonempty (D ≃ (D → D))

/-- **Scott's equation**: `D` is isomorphic to its **continuous** self-maps. This is the one
domain theory solves, and the one `WALLS` W8 is about. -/
def IsDomainReflexive (D : Type u) [OmegaCompletePartialOrder D] : Prop :=
  Nonempty (D ≃ (D →𝒄 D))

/-! ## 2. The naive equation has only the trivial solution -/

/-- **CANTOR KILLS THE NAIVE EQUATION.** From `e : D ≃ (D → D)` and two distinct points `a ≠ b`,
the map `d ↦ {x | e d x = a}` is a surjection `D → Set D`: given `S`, the function sending `S` to
`a` and its complement to `b` is some `e d`, and that `d` names `S`. `Function.cantor_surjective`
forbids it. -/
theorem subsingleton_of_setReflexive {D : Type u} (e : D ≃ (D → D)) : Subsingleton D := by
  classical
  by_contra hns
  obtain ⟨a, b, hab⟩ := (not_subsingleton_iff_nontrivial.mp hns).exists_pair_ne
  refine Function.cantor_surjective (fun d => {x : D | e d x = a}) ?_
  intro S
  refine ⟨e.symm (fun x => if x ∈ S then a else b), ?_⟩
  have he : e (e.symm (fun x => if x ∈ S then a else b)) = fun x => if x ∈ S then a else b :=
    e.apply_symm_apply _
  ext x
  simp only [Set.mem_setOf_eq, he]
  by_cases hx : x ∈ S <;> simp [hx, Ne.symm hab]

/-- **AND THAT IS SHARP.** `D ≃ (D → D)` holds **exactly when** `D` is a nonempty subsingleton —
the empty type fails because `∅ → ∅` has one element and `∅` has none. So the naive reflexive
equation is not an open problem with no known solution; it is a **false statement** about every
type with two distinct elements, and a trivially true one about the rest. -/
theorem isSetReflexive_iff (D : Type u) :
    IsSetReflexive D ↔ (Nonempty D ∧ Subsingleton D) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨⟨e.symm id⟩, subsingleton_of_setReflexive e⟩
  · rintro ⟨⟨x⟩, hs⟩
    exact ⟨⟨fun _ _ => x, fun _ => x, fun _ => Subsingleton.elim _ _,
      fun _ => funext fun _ => Subsingleton.elim _ _⟩⟩

/-- The one solution there is. -/
theorem isSetReflexive_punit : IsSetReflexive PUnit :=
  (isSetReflexive_iff PUnit).mpr ⟨⟨PUnit.unit⟩, inferInstance⟩

/-- The empty type is **not** a solution, which is why `isSetReflexive_iff` needs its `Nonempty`
conjunct and why "subsingleton" alone would be the wrong statement. -/
theorem not_isSetReflexive_empty : ¬ IsSetReflexive PEmpty := by
  intro h
  exact ((isSetReflexive_iff PEmpty).mp h).1.elim PEmpty.elim

/-! ## 3. Where the obstruction stops applying, exhibited rather than asserted

The proof in §2 builds `fun x => if x ∈ S then a else b` and feeds it through `e.symm`. For that
step to survive with `→𝒄` in place of `→`, every such characteristic function would have to be
continuous. They are not, and the smallest ω-CPO shows it. -/

/-- **NEGATION IS NOT MONOTONE**, so it is not a continuous self-map of `Prop`. -/
theorem not_monotone_not : ¬ Monotone (fun p : Prop => ¬p) := by
  intro h
  exact (h (show False ≤ True from fun x => x.elim) (fun x => x)) trivial

/-- **SO THE CONTINUOUS SELF-MAPS ARE A PROPER SUBCOLLECTION**, already on `Prop`. Some self-map
is missing from `Prop →𝒄 Prop`; `not_monotone_of_separates` below says it is *the one §2 needs*. -/
theorem not_surjective_coe_continuousHom :
    ¬ Function.Surjective (fun f : Prop →𝒄 Prop => (f : Prop → Prop)) := by
  intro hsurj
  obtain ⟨f, hf⟩ := hsurj (fun p : Prop => ¬p)
  exact not_monotone_not (hf ▸ f.monotone)

/-- **AND IT IS §2's OWN WITNESS THAT IS MISSING, in every ω-CPO and not just in `Prop`.** The
proof in §2 needs a function taking the value `a` on `S` and `b` off it, for an arbitrary `S`. Any
such function is non-monotone as soon as `S` fails to be an upper set — as soon as some `x ≤ y`
has `x ∈ S` and `y ∉ S` — provided `a ≰ b`. So the diagonal breaks **at the step that constructs
its witness**, which is sharper than "some function is discontinuous": no rearrangement of the
argument recovers it, because the sets it must name are exactly the ones it cannot.

Stated without `if`, so no decidability of membership is assumed — the hypotheses say what the
function does rather than how it is written. -/
theorem not_monotone_of_separates {D : Type u} [Preorder D] {f : D → D} {S : Set D} {a b : D}
    (hin : ∀ z ∈ S, f z = a) (hout : ∀ z ∉ S, f z = b)
    {x y : D} (hxy : x ≤ y) (hx : x ∈ S) (hy : y ∉ S) (hab : ¬ a ≤ b) : ¬ Monotone f := by
  intro hm
  exact hab (hin x hx ▸ hout y hy ▸ hm hxy)

/-! ## 4. And no finite domain solves the continuous equation either -/

/-- The constant maps inject `D` into its continuous self-maps. -/
theorem const_injective (D : Type u) [OmegaCompletePartialOrder D] :
    Function.Injective (ContinuousHom.const : D → (D →𝒄 D)) := by
  intro x y h
  have : (ContinuousHom.const x : D →𝒄 D) y = (ContinuousHom.const y : D →𝒄 D) y := by rw [h]
  simpa using this

/-- **THE IDENTITY IS NOT CONSTANT** once `D` has two distinct points. -/
theorem id_notMem_range_const {D : Type u} [OmegaCompletePartialOrder D] (h : ¬ Subsingleton D) :
    (ContinuousHom.id : D →𝒄 D) ∉ Set.range (ContinuousHom.const : D → (D →𝒄 D)) := by
  rintro ⟨c, hc⟩
  obtain ⟨a, b, hab⟩ := (not_subsingleton_iff_nontrivial.mp h).exists_pair_ne
  have ha : a = c := congrArg (fun g : D →𝒄 D => g a) hc.symm
  have hb : b = c := congrArg (fun g : D →𝒄 D => g b) hc.symm
  exact hab (ha.trans hb.symm)

/-- **HENCE NO NON-TRIVIAL FINITE REFLEXIVE DOMAIN.** If `D` were finite, the equivalence would
force the injection `const` to be surjective, and it is not — it misses the identity. So any `D`
solving Scott's equation is either a subsingleton or infinite. `D∞` is infinite, and this says it
has to be, rather than that it happens to be. -/
theorem not_isDomainReflexive_of_finite (D : Type u) [OmegaCompletePartialOrder D] [Finite D]
    (h : ¬ Subsingleton D) : ¬ IsDomainReflexive D := by
  rintro ⟨e⟩
  have hsurj : Function.Surjective (ContinuousHom.const : D → (D →𝒄 D)) :=
    (Finite.injective_iff_surjective_of_equiv e).mp (const_injective D)
  obtain ⟨c, hc⟩ := hsurj ContinuousHom.id
  exact id_notMem_range_const h ⟨c, hc⟩

/-! ## 5. The target, named and not proved

`PROOF_STRATEGY` §3's condition for leaving a chain is that the remaining leg be written down
precisely. This is it. -/

/-- **WHAT W8 ACTUALLY WANTS**: a non-trivial ω-CPO isomorphic to its own continuous self-maps.

**This is a theorem of the literature (Scott, 1970), not a conjecture of this project**, and that
distinction is deliberate: `ERRATUM 108` refuted a gap object this estate had written down and
never tried to falsify. This one is the standard `D∞`, an inverse limit along embedding–projection
pairs starting from any non-trivial ω-CPO.

**The small cases were checked before this was written down**, which is the habit that erratum
produced. `¬ Subsingleton D` is not decoration: `PUnit` satisfies the equation trivially, and
`isSetReflexive_punit` records it. Finite `D` is ruled out **in Lean**, by
`not_isDomainReflexive_of_finite` above.

*One further case was checked by hand and is NOT formalised here, and is labelled so rather than
left looking like the rest.* An infinite type carrying the **discrete** order would also be an
ω-CPO — a monotone `ℕ →o D` into a discrete order is constant, so every chain has a sup and every
function is both monotone and continuous — and there `D →𝒄 D` is all of `D → D`, so §2 applies and
the case dies. That paragraph is arithmetic done outside Lean; formalising it would mean building
the discrete-order ω-CPO instance and the equivalence `(D →𝒄 D) ≃ (D → D)`, which is a unit of work
and not this one. What it means for the target is that a witness must be infinite *and* genuinely
ordered, which is exactly what `D∞` is and why it takes a construction.

**Not attempted here.** What it needs is the inverse limit of the tower
`D₀ ← D₁ ← D₂ ← ⋯` with `Dₙ₊₁ = Dₙ →𝒄 Dₙ`, the embedding–projection pairs relating consecutive
levels, and the proof that the limit is a fixed point of the function-space functor. Mathlib has
the objects and the arrows and the fact that `α →𝒄 β` is again an ω-CPO; it has no inverse limit of
ω-CPOs at all. -/
def DInfExists : Prop :=
  ∃ (D : Type) (_ : OmegaCompletePartialOrder D), ¬ Subsingleton D ∧ Nonempty (D ≃ (D →𝒄 D))

/-- **AND THE REDUCTION, so the `def` above is not decorative:** anything satisfying it is
infinite. This is `not_isDomainReflexive_of_finite` read as a constraint on the target rather than
as a fact about finite types. -/
theorem dInfExists_infinite (h : DInfExists) :
    ∃ (D : Type) (_ : OmegaCompletePartialOrder D), ¬ Subsingleton D ∧ Infinite D := by
  obtain ⟨D, inst, hns, ⟨e⟩⟩ := h
  refine ⟨D, inst, hns, ?_⟩
  rw [← not_finite_iff_infinite]
  intro hfin
  exact not_isDomainReflexive_of_finite D hns ⟨e⟩

end ReflexiveDomainObstruction
