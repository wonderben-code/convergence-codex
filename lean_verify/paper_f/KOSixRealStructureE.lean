/-
  KOSixRealStructureE: the real structure IS expressible, and the claim that it was not was
  mine, repeated in three file headers

  SPINE LINK L18. Since `SpectralTripleBimodule` was built, three headers of mine have carried
  a version of the same sentence:

  > *"`J` is a linear map, not an antilinear one. A real structure is conjugate-linear, and
  > Mathlib's `LinearMap` cannot express that at this signature."*
  > *"`J` is antilinear and `Module.End ℂ (HfE n)` cannot hold it."*
  > *"conjugating `J` by `blockEquiv` gives an antilinear map on `HfE n` — which
  > `Module.End ℂ (HfE n)` cannot hold, exactly as the header says. Naming the obstruction is
  > not removing it."*

  **The obstruction was not real.** Mathlib's `LinearMap` is *semilinear by default*: the
  notation `M →ₛₗ[σ] N` carries a ring homomorphism `σ` twisting the scalars, and at
  `σ = starRingEnd ℂ` that is exactly a conjugate-linear map. `RingHomInvPair` and
  `RingHomCompTriple` instances for `starRingEnd ℂ` are already in place, so two of them
  compose back to an honest `ℂ`-linear map. **`Module.End ℂ H` cannot hold `J`, which is true
  and was never the question; the type that holds `J` is `H →ₛₗ[starRingEnd ℂ] H`.** Filed as
  `ERRATUM 571` and corrected in all three headers.

  **WHY I BELIEVED IT, because the shape is reusable.** Every earlier unit reached for `J` as
  a FIELD of a structure whose other fields were `Module.End 𝕜 H`, and asked whether that type
  could hold it. It cannot. But *"this field's type cannot hold the object"* is not
  *"the library cannot express the object"* — and I wrote the second while checking only the
  first. **A type that is wrong for one slot is not evidence about the library**, and three
  headers repeated the inference without ever grepping for `→ₛₗ` or `semilinear`.

  WHAT IS PROVED.
  * **`blockSwap`** — the index involution exchanging particle and antiparticle blocks, `0↔2`
    and `1↔3`, with `blockSwap_involutive`. Named `blockSwap` rather than `swap`, which
    `PrismReflection` already has.
  * **`Jmap : HfE n →ₛₗ[starRingEnd ℂ] HfE n`** — the real structure, conjugate-linear, as a
    genuine bundled map: `(J v) (i, b) = conj (v (i, blockSwap b))`.
  * **`Jmap_apply`**, **`Jmap_conj_smul`** — the conjugate-linearity, exhibited rather than
    only typed.
  * **`Jmap_involutive`** — `J (J v) = v`, the KO-6 sign `ε = 1`.
  * **`Jmap_comp_self`** — the same fact as an identity of `ℂ`-LINEAR maps, through
    `RingHomCompTriple`: composing two conjugate-linear maps lands in `Module.End ℂ (HfE n)`,
    which is the mechanism the three headers missed.

  WHAT IS **NOT** CLAIMED.
  * **No `πOp`, no order condition, and no `Triple`.** This unit supplies `J` and its
    involutivity; it does not build the opposite action, does not prove order-zero, and does
    not assemble a `Triple`. The instance diamond from `KOSixInnerProduct` is untouched.
  * **The KO-6 signs relating `J` to `D` and `γ` are not proved**, because `D` and `γ` are not
    built on `HfE n` at all. `Jmap_involutive` is `ε = 1` alone.
  * **`Jmap` is not claimed to be `KOSixSpectralTriple.J` transported.** That file's `J` lives
    on `Hf n` and `blockEquiv` is `ℂ`-linear, so the transport is not an identity of bundled
    maps and is not asserted here; the two are the same formula on corresponding indices, and
    that is a statement this unit does not prove.
  * **No claim that the real case is now unblocked.** `ERRATUM 570` showed the repair of
    `piRep` is conjugate-linear in the ALGEBRA variable, which is a different conjugation from
    `J`'s in the VECTOR variable. Confusing the two would be the `ERRATUM 565` error again;
    they are kept apart here and neither is derived from the other.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import KOSixInnerProduct

namespace KOSixRealStructureE

open ComplexConjugate KOSixInnerProduct

noncomputable section

variable {n : ℕ}

/-! ## 1. The block involution -/

/-- The index involution exchanging particle and antiparticle blocks: `0↔2`, `1↔3`. Written
as `+ 2` in `Fin 4`, where addition is mod 4, so it needs no bound proofs — a case split with
`⟨b.val + 2, by omega⟩` does not typecheck, because the branch hypothesis is not in scope for
the proof term. -/
def blockSwap : Fin 4 → Fin 4 := fun b => b + 2

@[simp]
theorem blockSwap_involutive (b : Fin 4) : blockSwap (blockSwap b) = b := by
  fin_cases b <;> rfl

/-! ## 2. The real structure, as a conjugate-linear map -/

/-- **The real structure.** Conjugate-linear, and expressible as a bundled map because
Mathlib's `LinearMap` is semilinear by default: `→ₛₗ[starRingEnd ℂ]` twists the scalars by
complex conjugation. This is the type the three headers said did not exist. -/
def Jmap : HfE n →ₛₗ[starRingEnd ℂ] HfE n where
  toFun v := (WithLp.toLp 2 fun p => conj (v (p.1, blockSwap p.2)))
  map_add' u v := by ext p; simp
  map_smul' c v := by ext p; simp

@[simp]
theorem Jmap_apply (v : HfE n) (i : Fin n) (b : Fin 4) :
    Jmap v (i, b) = conj (v (i, blockSwap b)) := rfl

/-- Conjugate-linearity, exhibited rather than only typed. -/
theorem Jmap_conj_smul (c : ℂ) (v : HfE n) : Jmap (c • v) = conj c • Jmap (v : HfE n) :=
  Jmap.map_smul' c v

/-- **The KO-6 sign `ε = 1`**: `J² = 1`. -/
@[simp]
theorem Jmap_involutive (v : HfE n) : Jmap (Jmap v) = v := by
  ext p
  obtain ⟨i, b⟩ := p
  simp

/-- **The mechanism the three headers missed**, as a theorem: two conjugate-linear maps
compose to a `ℂ`-LINEAR one, through `RingHomCompTriple (starRingEnd ℂ) (starRingEnd ℂ) (id)`,
so `J ∘ J` is an honest element of `Module.End ℂ (HfE n)` — and it is the identity. -/
theorem Jmap_comp_self : (Jmap : HfE n →ₛₗ[starRingEnd ℂ] HfE n).comp Jmap = LinearMap.id := by
  ext v
  simp

end

end KOSixRealStructureE
