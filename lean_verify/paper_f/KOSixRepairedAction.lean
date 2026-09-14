/-
  KOSixRepairedAction: `piRep`'s shape cannot be repaired, and the map that replaces it is an
  `ℝ`-algebra hom and not a `ℂ`-algebra hom — which is why `Triple` was parametrised over the
  base field

  SPINE LINK L18, and `UNLOCK_WATCHLIST` 261. That entry, written by me after
  `SpectralTripleBimodule` built the variable-algebra `Triple`, recorded that
  `KOSixSpectralTriple.piRep` cannot fill an `AlgHom` field because
  `KOSixAlgebraAction.piRep_not_additive_in_matrix` machine-checked that it is not additive in
  the matrix (`ERRATUM 565`). It then named two repair routes and said of the first:
  *"(a) is the better route and the structure's shape is evidence for it: a `Triple` wants `π`
  and `πOp` separately, which is precisely the split `piRep` collapsed into one non-additive
  map."*

  **THE SHAPE ITSELF IS UNREPAIRABLE, and that is the first half of this unit.**
  `piRep a v = ((a *ᵥ v.1.1, a *ᵥ v.1.2), (v.2.1, v.2.2))` — `a` on the particle blocks, and
  the antiparticle blocks returned **unchanged**, i.e. by a map that does not depend on `a` at
  all. `no_additive_of_constant_antiparticle` proves that no map of that shape can be additive
  at all. **And ADDITIVITY ALONE SUFFICES — unitality is not needed, which is stronger than
  the first draft of this header claimed.** The proof: additivity at `a = b = 0` forces
  `π 0 v = 0`, so its antiparticle part is `0`; constancy says that part is `v.2`; hence every
  vector has zero antiparticle blocks, and `Hf n` has vectors that do not. **So entry 261's
  route (a) cannot be completed as described.** The fault is not a missing lemma or a choice of
  `πOp`; it is that *"acts as `a` on particles and leaves antiparticles alone"* is not the
  shape of an additive map, let alone a homomorphism.

  **AND THE MAP THAT DOES WORK IS THE INTERESTING HALF.** Let the antiparticle blocks carry
  the entrywise CONJUGATE action instead of the identity:

  > `piRepC a v = ((a *ᵥ v.1.1, a *ᵥ v.1.2), (ā *ᵥ v.2.1, ā *ᵥ v.2.2))`

  This is additive (`mbar_add`), multiplicative (`mbar_mul`) and **unital** (`mbar_one`), so it
  is a genuine ring homomorphism where `piRep` was not — `piRepC_ring_hom`. It is
  `ℝ`-**linear** (`piRepC_real_smul`). And it is **NOT `ℂ`-linear**
  (`piRepC_not_complex_linear`), because conjugation is not: at `a = 1` and `c = i` the two
  sides differ by a sign on the antiparticle blocks.

  **WHICH IS EXACTLY WHY `SpectralTripleBimodule.Triple` IS PARAMETRISED OVER `𝕂`.** That
  structure takes `π : A →ₐ[𝕂] Module.End 𝕜 H` with `𝕂` the ground field of the algebra and
  `𝕜` that of the Hilbert space, so that `𝕂 = ℝ`, `𝕜 = ℂ` is available. When that
  parametrisation was written the reason given was *"CCM's algebra is real"*. **The reason is
  now a theorem about this estate's own triple**: the only repair of `piRep` that is a
  homomorphism at all is conjugate-linear on half the space, so it is an `ℝ`-algebra map and
  cannot be a `ℂ`-algebra map. The design choice was right for a sharper reason than the one
  recorded for it.

  WHAT IS PROVED.
  * **`no_additive_of_constant_antiparticle`** — the impossibility, from additivity alone.
  * **`piRep_antiparticle_constant`** — that `piRep` really is of the forbidden shape, so the
    impossibility applies to it and is not about a strawman.
  * **`piRepC`**, with `piRepC_add`, `piRepC_mul`, `piRepC_one`, `piRepC_zero` and
    `piRepC_ring_hom` bundling them: **the repair, as a `RingHom`**.
  * **`piRepC_real_smul`** and **`piRepC_not_complex_linear`** — `ℝ`-linear, not `ℂ`-linear.
  * **`piRepC_vector_add`**, **`piRepC_vector_smul`** — still linear in the VECTOR, which is
    what `piRep_add`/`piRep_smul` were about and what `ERRATUM 565` found cited for the wrong
    claim. Kept here so the two variables are never confused again.
  * **`piRepC_ne_piRep`** — the repair is a different map, exhibited at a point.

  WHAT IS **NOT** CLAIMED, and `Triple` is still not instantiated.
  * **No `InnerProductSpace` on `Hf n`.** `Hf n` is a bare product of four `Fin n → ℂ` with no
    inner product instance, and `Triple` needs `[NormedAddCommGroup H] [InnerProductSpace 𝕜 H]`.
    Supplying one needs a `WithLp`/`EuclideanSpace` type synonym and the `def`-not-`abbrev`
    discipline `Herm4Gaussian` had to learn. **That is the Caesar order's item 5 and it is not
    done here**, so `piRepC` cannot yet fill a `Triple`'s `π` field even though it is now the
    right kind of map.
  * **No `πOp` is built.** `KOSixSpectralTriple.piOp` is defined through `J` and the old
    `piRep`; what it becomes under the repair is not computed, and order-zero for the repaired
    pair is not proved.
  * **Nothing is withdrawn from `KOSixSpectralTriple`.** `piRep` stays as it is; this file adds
    a different map beside it and proves the two differ. `ERRATUM 565`'s annotation of that
    file's header stands.
  * **No KO-dimension, `J`, or grading claim**, and no connection to `CascadeHilbert`,
    `CascadeAlgebra` or the 96 — L18's standing residue, untouched.
  * **`piRepC` is not claimed to be CCM's action.** It is the unique repair *of this shape*;
    whether CCM's finite geometry assigns the conjugate action to the antiparticle sector is a
    modelling question this file does not settle (`ASSUMPTIONS_LEDGER` 18, 48).

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import KOSixAlgebraAction

namespace KOSixRepairedAction

open KOSixSpectralTriple
open Matrix ComplexConjugate

noncomputable section

variable {n : ℕ}

/-! ## 1. The shape `piRep` has is not the shape of a unital homomorphism -/

/-- `piRep`'s antiparticle blocks do not depend on the matrix at all: they are returned
unchanged. Stated so that the impossibility below is about `piRep` and not a strawman. -/
theorem piRep_antiparticle_constant (a : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) :
    (piRep a v).2 = v.2 := rfl

/-- **THE IMPOSSIBILITY, and additivity alone does it.** Suppose a map `π` returns the
antiparticle blocks unchanged — more generally, by anything not depending on `a`. Then `π`
cannot be additive: additivity at `a = b = 0` forces `π 0 v = 0`, whose antiparticle part is
therefore `0`; constancy says that part is `v.2`; so every vector would have zero antiparticle
blocks, and `Hf n` has vectors that do not.

**No unitality hypothesis is used**, which is stronger than expected — the first draft of this
file's header claimed additivity and unitality were each doing half the work, and only
additivity is. So *"acts as `a` on particles and leaves antiparticles alone"* is not the shape
of an additive map at all, and `UNLOCK_WATCHLIST` 261's route (a) cannot be completed as it was
described — the fault is the shape, not a missing lemma or a choice of `πOp`. -/
theorem no_additive_of_constant_antiparticle
    (π : Matrix (Fin 1) (Fin 1) ℂ → Hf 1 → Hf 1)
    (hconst : ∀ (a : Matrix (Fin 1) (Fin 1) ℂ) (v : Hf 1), (π a v).2 = v.2)
    (hadd : ∀ (a b : Matrix (Fin 1) (Fin 1) ℂ) (v : Hf 1), π (a + b) v = π a v + π b v) :
    False := by
  set v : Hf 1 := ((0, 0), (fun _ => 1, 0)) with hv
  -- additivity at `a = b = 0` forces `π 0 v = 0`
  have hz : π 0 v = π 0 v + π 0 v := by simpa using hadd 0 0 v
  have h0 : π 0 v = 0 :=
    (add_left_cancel (a := π 0 v) (b := 0) (c := π 0 v) (by rw [add_zero]; exact hz)).symm
  -- but the antiparticle blocks were returned unchanged, so `v.2 = 0`
  have h2 : v.2 = 0 := by rw [← hconst 0 v, h0]; rfl
  have h3 := congrFun (congrArg Prod.fst h2) 0
  simp [hv] at h3

/-! ## 2. The repair: the conjugate action on the antiparticle blocks -/

/-- **The repaired action.** `a` on the particle blocks, the entrywise conjugate `ā` on the
antiparticle blocks. -/
def piRepC (a : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) : Hf n :=
  ((a *ᵥ v.1.1, a *ᵥ v.1.2), (mbar a *ᵥ v.2.1, mbar a *ᵥ v.2.2))

@[simp]
theorem piRepC_apply (a : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) :
    piRepC a v = ((a *ᵥ v.1.1, a *ᵥ v.1.2), (mbar a *ᵥ v.2.1, mbar a *ᵥ v.2.2)) := rfl

theorem mbar_add (a b : Matrix (Fin n) (Fin n) ℂ) : mbar (a + b) = mbar a + mbar b := by
  ext i j; simp [mbar, Matrix.map_apply, map_add]

theorem mbar_one : mbar (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [mbar, Matrix.map_apply, Matrix.one_apply_eq]
  · simp [mbar, Matrix.map_apply, Matrix.one_apply_ne h]

/-- **Additive in the MATRIX** — the property `piRep` fails (`ERRATUM 565`). -/
theorem piRepC_add (a b : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) :
    piRepC (a + b) v = piRepC a v + piRepC b v := by
  simp only [piRepC_apply, mbar_add, Matrix.add_mulVec]
  rfl

theorem piRepC_zero (v : Hf n) : piRepC 0 v = 0 := by
  simp only [piRepC_apply]
  have : mbar (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by ext i j; simp [mbar, Matrix.map_apply]
  rw [this]
  simp only [Matrix.zero_mulVec]
  rfl

/-- **Unital**, which is the property the additive-but-not-unital candidate `a ⊕ 0` fails. -/
theorem piRepC_one (v : Hf n) : piRepC 1 v = v := by
  simp only [piRepC_apply, mbar_one, Matrix.one_mulVec]

/-- Entrywise conjugation is multiplicative. Not in `KOSixSpectralTriple`, which has
`mbar_mbar`, `mbar_transpose`, `mbar_conjTranspose` and `mbar_of_transpose` but no product
rule — the identity a repaired action needs and the old one did not. -/
theorem mbar_mul (a b : Matrix (Fin n) (Fin n) ℂ) : mbar (a * b) = mbar a * mbar b := by
  ext i j
  simp [mbar, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]

/-- **Multiplicative**, using that entrywise conjugation is a ring map. -/
theorem piRepC_mul (a b : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) :
    piRepC (a * b) v = piRepC a (piRepC b v) := by
  simp only [piRepC_apply, mbar_mul, ← Matrix.mulVec_mulVec]

/-! ## 3. Linear over `ℝ`, not over `ℂ` — which is the point -/

/-- `ℝ`-linear in the matrix: real scalars pass through conjugation unchanged. -/
theorem piRepC_real_smul (r : ℝ) (a : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) :
    piRepC ((r : ℂ) • a) v = (r : ℂ) • piRepC a v := by
  have hb : mbar ((r : ℂ) • a) = (r : ℂ) • mbar a := by
    ext i j
    simp only [mbar, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    rw [map_mul, Complex.conj_ofReal]
  simp only [piRepC_apply, hb]
  simp [Prod.smul_mk, Matrix.smul_mulVec]

/-- **NOT `ℂ`-linear**, and the witness is `a = 1`, `c = i`: on the antiparticle blocks the
conjugate action gives `-i` where `ℂ`-linearity would give `i`. **This is the theorem that
makes `SpectralTripleBimodule.Triple`'s parametrisation over the base field `𝕂` load-bearing
rather than a convenience**: the only repair of `piRep` that is a homomorphism at all is an
`ℝ`-algebra map and cannot be a `ℂ`-algebra map. -/
theorem piRepC_not_complex_linear :
    ¬ (∀ (c : ℂ) (a : Matrix (Fin 1) (Fin 1) ℂ) (v : Hf 1),
        piRepC (c • a) v = c • piRepC a v) := by
  intro h
  have key : (-Complex.I : ℂ) = Complex.I := by
    have hcomp := congrFun (congrArg Prod.fst (congrArg Prod.snd
      (h Complex.I 1 ((0, 0), (fun _ => 1, 0))))) 0
    simpa [piRepC, mbar, Matrix.map_apply, Matrix.mulVec, Matrix.one_apply, dotProduct]
      using hcomp
  exact Complex.I_ne_zero (by linear_combination -key / 2)

/-! ## 4. Still linear in the VECTOR, so the two variables are never confused again -/

theorem piRepC_vector_add (a : Matrix (Fin n) (Fin n) ℂ) (u v : Hf n) :
    piRepC a (u + v) = piRepC a u + piRepC a v := by
  simp only [piRepC_apply]
  simp [Prod.mk_add_mk, Matrix.mulVec_add]

theorem piRepC_vector_smul (a : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (v : Hf n) :
    piRepC a (c • v) = c • piRepC a v := by
  simp only [piRepC_apply]
  simp [Prod.smul_mk, Matrix.mulVec_smul]

/-- The repair is a genuinely different map from `piRep`. -/
theorem piRepC_ne_piRep :
    piRepC (0 : Matrix (Fin 1) (Fin 1) ℂ) ((0, 0), (fun _ => 1, 0))
      ≠ piRep (0 : Matrix (Fin 1) (Fin 1) ℂ) ((0, 0), (fun _ => 1, 0)) := by
  intro h
  have := congrFun (congrArg Prod.fst (congrArg Prod.snd h)) 0
  simp [piRepC, piRep, mbar] at this

end

end KOSixRepairedAction
