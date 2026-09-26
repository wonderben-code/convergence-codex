/-
  OrderOneUnderCCM: what the new axiom DOES — §W9.2's vacuity theorem, sharpened, with the
  Schur citation removed

  SPINE LINK L6 — WALL W9, RUNG 2. `UNLOCK_WATCHLIST` 265's item (3), taken.

  THE QUESTION. Three units ago `Triple` was found to be missing CCM's relation
  `πOp b = J π(b*) J`; one unit ago the field `πOp_impl` was added. Adding an axiom is only
  worth the churn if something follows from it, and §W9.2's own two vacuity theorems were
  proved for the WEAKER structure. **Do they survive the tightening, and does either get
  sharper?** Entry 265 called this *"the first thing to check"*.

  THE ANSWER, and it is the sharper kind.
  * **`orderOne_of_commute_D` survives untouched** — it never mentioned `πOp` at all, so no
    argument of it can have used the freedom the axiom removed. Nothing to check, and saying
    so is part of the answer.
  * **`orderOne_of_central_piOp` gets STRICTLY SHARPER, and loses a citation.** §W9.2's
    negative half read: *"if `π` is irreducible, that commutant is the scalars by Schur, `πOp`
    is central, and order-one says nothing at all"* — with **Schur's lemma cited and not
    proved**, and the conclusion conditional on irreducibility. Under CCM's relation neither
    is needed:

    > **`central_piOp_iff_central_pi` — `πOp`'s image is central if and only if `π`'s is.**

    Because `πOp` is no longer a free parameter: it is `π` conjugated by `J`, and conjugation
    by `J` is a **ring automorphism** of `Module.End 𝕜 H` (`conjEnd_mul`, `conjEnd_one`,
    `conjEnd_involutive`), so it preserves the centre. `star` and `unop` are bijections, which
    closes the quantifier. **No irreducibility hypothesis and no Schur.**
  * **`pi_scalar_of_central_piOp`** then converts "central" into "scalar" through Mathlib's
    `Module.End.mem_center_iff`, valid because `H` is a free `𝕜`-module: if `πOp`'s image is
    central then every `π a` is `α • id` for a scalar `α`.
  * **`orderOne_not_vacuous_of_pi_not_scalar`** is the rung-2 statement the unit exists for.
    **For any `Triple` whose `π` is not scalar, `orderOne_of_central_piOp` does not apply** —
    unconditionally, with no hypothesis on `H` beyond freeness and no appeal to irreducibility.
    The escape route §W9.2 had to argue around by citing Schur is **closed by the axiom**.
  * **`realWitness_orderOne_live`** applies both halves to the estate's own CCM triple: its `π`
    is not scalar and its `D` is outside the commutant, so **neither** vacuity theorem applies
    and order-one is a live condition there. §W9.3 established that for the weaker structure;
    this establishes it for a genuine real spectral triple.

  WHAT CHANGED IN THE PICTURE, said plainly. §W9.2 concluded that order-one has content *"only
  where `π` is REDUCIBLE"*, which was a statement about a structure in which `πOp` could be
  chosen. In a CCM triple `πOp` cannot be chosen, and the boundary moves: order-one is vacuous
  by centrality **exactly when `π` is scalar**, which is a far smaller class than "irreducible".
  So there is strictly more room for order-one to have content than §W9.2 thought, and the
  reason is the axiom rather than a new argument.

  WHAT IS **NOT** CLAIMED.
  * **Rung 2 is not climbed.** No involution is classified and no factor list is cut. This
    unit removes an escape route and a citation; it does not derive a constraint.
  * **`orderOne_of_central_piOp` is not withdrawn.** It is true and unchanged; what changed is
    how hard its hypothesis is to satisfy.
  * **No claim that order-one always has content when `π` is non-scalar.** The theorem says the
    CENTRALITY route to vacuity is closed; `orderOne_of_commute_D` is a second route and stays
    open, and a `D` in the commutant still makes order-one free. Both have to fail, which is
    what `realWitness_orderOne_live` checks for one witness.
  * **Schur's lemma is not proved here; it is no longer NEEDED here.** §W9.2's citation stands
    as a citation in that section; the theorem below does not use it.
  * **No `K`-theory, no cascade, no KO-dimension**, and `D` is still not shown to anticommute
    with `γ` in any witness.
    ⚠ 26 September 2026 (unit 229, `ERRATUM 698`): shown 38 minutes after this file, in
    unit 29's amendment (`bb8d637`): `RealSpectralWitness.Dccm_anticomm_gammaCcm`, the witness's
    `D` anticommutes with its `γ`; `WALLS` §W9.7 (1) records it. Kept as written (`ERRATUM 94`).

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import RealSpectralWitness

namespace OrderOneUnderCCM

open Matrix MulOpposite SpectralTripleBimodule OrderOneNontrivial
open RealSpectralWitness OppositeFromRealStructure

noncomputable section

/-! ## 1. Conjugation by `J` is a ring automorphism of `Module.End 𝕜 H` -/

variable {𝕂 𝕜 A H : Type*} [Field 𝕂] [RCLike 𝕜] [Algebra 𝕂 𝕜]
  [Ring A] [StarRing A] [Algebra 𝕂 A]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [Module 𝕂 H] [IsScalarTower 𝕂 𝕜 H]

/-- `x ↦ J ∘ x ∘ J`. **`𝕜`-linear in the vector**, because `J` is conjugate-linear twice; the
map itself is conjugate-linear in the SCALAR, which is why it is not an algebra map — and
nothing below needs it to be, only a ring automorphism. -/
def conjEnd (T : Triple 𝕂 𝕜 A H) (x : Module.End 𝕜 H) : Module.End 𝕜 H :=
  T.J.comp (x.comp T.J)

@[simp] theorem conjEnd_apply (T : Triple 𝕂 𝕜 A H) (x : Module.End 𝕜 H) (v : H) :
    conjEnd T x v = T.J (x (T.J v)) := rfl

/-- **`conjEnd` is an involution**, off `J² = 1`. -/
theorem conjEnd_involutive (T : Triple 𝕂 𝕜 A H) (x : Module.End 𝕜 H) :
    conjEnd T (conjEnd T x) = x := by
  refine LinearMap.ext fun v => ?_
  simp only [conjEnd_apply]
  rw [OppositeFromRealStructure.J_apply_J, OppositeFromRealStructure.J_apply_J]

/-- **`conjEnd` is multiplicative**, because the inner `J²` cancels. -/
theorem conjEnd_mul (T : Triple 𝕂 𝕜 A H) (x y : Module.End 𝕜 H) :
    conjEnd T (x * y) = conjEnd T x * conjEnd T y := by
  refine LinearMap.ext fun v => ?_
  simp only [conjEnd_apply, Module.End.mul_apply, conjEnd_apply]
  rw [OppositeFromRealStructure.J_apply_J]

@[simp] theorem conjEnd_one (T : Triple 𝕂 𝕜 A H) : conjEnd T 1 = 1 := by
  refine LinearMap.ext fun v => ?_
  simp only [conjEnd_apply, Module.End.one_apply]
  exact OppositeFromRealStructure.J_apply_J T v

theorem conjEnd_injective (T : Triple 𝕂 𝕜 A H) : Function.Injective (conjEnd T) := by
  intro x y h
  rw [← conjEnd_involutive T x, ← conjEnd_involutive T y, h]

/-- **Conjugation by `J` carries the centre into the centre.** A ring automorphism cannot move
the centre, and `conjEnd` is one — that is the whole mechanism of this unit. -/
theorem conjEnd_center_of_center (T : Triple 𝕂 𝕜 A H) {x : Module.End 𝕜 H}
    (h : x ∈ Set.center (Module.End 𝕜 H)) :
    conjEnd T x ∈ Set.center (Module.End 𝕜 H) := by
  refine Semigroup.mem_center_iff.mpr fun y => ?_
  refine conjEnd_injective T ?_
  rw [conjEnd_mul, conjEnd_mul, conjEnd_involutive]
  exact Semigroup.mem_center_iff.mp h (conjEnd T y)

/-- Both ways, off involutivity. -/
theorem conjEnd_mem_center_iff (T : Triple 𝕂 𝕜 A H) (x : Module.End 𝕜 H) :
    conjEnd T x ∈ Set.center (Module.End 𝕜 H) ↔ x ∈ Set.center (Module.End 𝕜 H) :=
  ⟨fun h => by
      have h' := conjEnd_center_of_center T h
      rwa [conjEnd_involutive] at h',
   conjEnd_center_of_center T⟩

/-! ## 2. `πOp` is `π` conjugated, so their centralities are the same question -/

/-- CCM's relation, as an identity of bundled maps rather than a pointwise one. -/
theorem piOp_eq_conjEnd (T : Triple 𝕂 𝕜 A H) (b : Aᵐᵒᵖ) :
    T.πOp b = conjEnd T (T.π (star (unop b))) :=
  LinearMap.ext fun v => T.πOp_impl b v

/-- **THE THEOREM THE UNIT EXISTS FOR.** `πOp`'s image is central **iff** `π`'s image is
central. No irreducibility hypothesis, no Schur's lemma: `πOp` is not a free parameter under
CCM's relation, it is `π` conjugated by `J`, and `conjEnd` is a ring automorphism. -/
theorem central_piOp_iff_central_pi (T : Triple 𝕂 𝕜 A H) :
    (∀ b : Aᵐᵒᵖ, T.πOp b ∈ Set.center (Module.End 𝕜 H))
      ↔ (∀ a : A, T.π a ∈ Set.center (Module.End 𝕜 H)) := by
  constructor
  · intro h a
    have := h (op (star a))
    rw [piOp_eq_conjEnd, unop_op, star_star] at this
    exact (conjEnd_mem_center_iff T (T.π a)).mp this
  · intro h b
    rw [piOp_eq_conjEnd]
    exact (conjEnd_mem_center_iff T _).mpr (h _)

/-! ## 3. Central means scalar, and what that does to rung 2 -/

variable [Module.Free 𝕜 H]

/-- **Central becomes SCALAR**, through Mathlib's `Module.End.mem_center_iff`, which needs `H`
free over `𝕜` — true for the finite-dimensional spaces every witness uses. -/
theorem pi_scalar_of_central_piOp (T : Triple 𝕂 𝕜 A H)
    (h : ∀ b : Aᵐᵒᵖ, T.πOp b ∈ Set.center (Module.End 𝕜 H)) (a : A) :
    ∃ α : 𝕜, ∀ v : H, T.π a v = α • v := by
  obtain ⟨α, _, hα⟩ := Module.End.mem_center_iff.mp
    ((central_piOp_iff_central_pi T).mp h a)
  exact ⟨α, fun v => by rw [hα]; rfl⟩

/-- **THE RUNG-2 STATEMENT.** For any `Triple` whose `π` is not a scalar action,
`SpectralTripleBimodule.orderOne_of_central_piOp` **does not apply** — its hypothesis fails.
Unconditionally: no irreducibility, no Schur, no condition on `H` beyond freeness. **The
escape route §W9.2 had to argue around is closed by the axiom `πOp_impl`.** -/
theorem orderOne_not_vacuous_of_pi_not_scalar (T : Triple 𝕂 𝕜 A H)
    (hns : ¬ ∀ (a : A), ∃ α : 𝕜, ∀ v : H, T.π a v = α • v) :
    ¬ (∀ b : Aᵐᵒᵖ, T.πOp b ∈ Set.center (Module.End 𝕜 H)) := by
  intro h
  exact hns fun a => pi_scalar_of_central_piOp T h a

end

/-! ## 4. The estate's own CCM triple escapes both vacuity routes -/

/-- `realWitness`'s `π` is **not** a scalar action: `π σ₃` acts as `σ₃ ⊗ 1`, which is not a
multiple of the identity — read off two entries of the Kronecker product. -/
theorem realWitness_pi_not_scalar :
    ¬ ∀ (a : Matrix (Fin 2) (Fin 2) ℂ), ∃ α : ℂ, ∀ v : Hw, realWitness.π a v = α • v := by
  intro h
  obtain ⟨α, hα⟩ := h pauli3
  have h0 : (1 : ℂ) = α := by
    simpa [realWitness, piW_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kroneckerMap, Matrix.one_apply, pauli3] using
      congrArg (fun z : Hw => z (0, 0)) (hα (WithLp.toLp 2 fun _ => (1 : ℂ)))
  have h1 : (-1 : ℂ) = α := by
    simpa [realWitness, piW_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kroneckerMap, Matrix.one_apply, pauli3] using
      congrArg (fun z : Hw => z (1, 0)) (hα (WithLp.toLp 2 fun _ => (1 : ℂ)))
  rw [← h0] at h1
  exact absurd h1 (by norm_num)

/-- **NEITHER vacuity theorem applies to the estate's CCM triple.** `π` is not scalar, so the
centrality route is closed by `orderOne_not_vacuous_of_pi_not_scalar`; and `D` is outside the
commutant of `π A`, so the commutant route is closed too. §W9.3 established this for the
WEAKER structure; here it is established for a genuine real spectral triple, and the first
half needs neither Schur nor irreducibility. -/
theorem realWitness_orderOne_live :
    ¬ (∀ b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ,
        realWitness.πOp b ∈ Set.center (Module.End ℂ Hw))
      ∧ ¬ (∀ a : Matrix (Fin 2) (Fin 2) ℂ, Commute realWitness.D (realWitness.π a)) :=
  ⟨orderOne_not_vacuous_of_pi_not_scalar realWitness realWitness_pi_not_scalar,
    Dccm_not_commute_piW⟩

end OrderOneUnderCCM
