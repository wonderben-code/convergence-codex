import RealDivisionAnticomm

/-!
# The form as a function, and the dictionary between orthogonal and anticommuting

`RealDivisionAnticomm` proved leg (c) step 2's algebraic heart and named what was still missing:
*the dictionary between "orthogonal" for the form and "anticommuting"*, and then a basis argument.
**This is the dictionary**, and getting it needs the form to be a function rather than a family of
existential statements — which is why the earlier files, which had no consumer for it, were right
not to build one and this one is right to.

> **`pureSq`** — the real a pure element squares to, as a function on the bundled pure part. It is
> `Classical.choose` on `IsPure` and is well defined for a reason rather than by fiat:
> `RealDivisionPureForm.sq_scalar_unique` says the scalar is unique, so any other extraction agrees
> with this one (`pureSq_eq`).
>
> **`pureForm`** — by polarisation, `(pureSq (u+v) − pureSq u − pureSq v)/2`.
>
> **`anticomm_eq`** — and it does what a form should: `u*v + v*u = (2 · pureForm u v) • 1`.
>
> **`orthogonal_iff_anticomm`** — **the dictionary.** `pureForm u v = 0` exactly when `u` and `v`
> anticommute. With `RealDivisionAnticomm`'s theorems this turns *"a fourth direction orthogonal to
> `i`, `j`, `ij`"* into *"a fourth direction anticommuting with all three"*, which is zero.
>
> **`pureForm_self`**, **`pureForm_comm`**, **`pureSq_neg_of_ne_zero`** — the form is symmetric, its
> diagonal is the square, and that square is strictly negative off `0`. With the sign convention
> `⟪u,v⟫ = −pureForm u v` it is positive definite.

## What is still missing from step 2, and it is now one thing

**The basis argument.** `dim V ≥ 4` would give a nonzero element orthogonal to `i`, `j` and `i *
j`; the dictionary makes it anticommute with all three;
`RealDivisionAnticomm.eq_zero_of_anticomm_three` makes it `0`. **What is not here is the linear
algebra that produces such an element** — bilinearity of `pureForm`, an orthogonal basis, and
the dimension count. Bilinearity is short and is deliberately not folded in here: it belongs
beside the basis argument that consumes it, and this file's subject is the dictionary. **Not
attempted, not costed** (`ERRATUM 194`, `ERRATUM 246`).

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RealDivisionFormFun

open RealDivisionPure RealDivisionPureAdd RealDivisionPureForm RealDivisionPureSpace

/-! **The rigidity lemma needs no finiteness**, so it is stated before the section that assumes it
— `ERRATUM 405`'s split, applied at the moment the file was written rather than after the linter
asked. (It asked anyway, on the first draft: sixth instance, and the addendum to that erratum is
about exactly this.) -/
section Rigidity

variable {D : Type*} [DivisionRing D] [Algebra ℝ D]

/-- **The rigidity every proof below leans on**: distinct reals give distinct scalars.
`RealDivisionPureForm.sq_scalar_unique` is this fact wrapped around a square, and the first draft
of this file tried to use it at `w = 1`, which asserts `1 = c • 1` and is not what any of these
proofs have. Stated on its own, where it belongs. -/
theorem smul_one_inj {c c' : ℝ} (h : c • (1 : D) = c' • (1 : D)) : c = c' := by
  have hmap : (algebraMap ℝ D) c = (algebraMap ℝ D) c' := by
    rwa [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at h
  exact (algebraMap ℝ D).injective hmap

end Rigidity

variable {D : Type*} [DivisionRing D] [Algebra ℝ D] [Module.Finite ℝ D]

/-- The real that a pure element squares to. -/
noncomputable def pureSq (u : pureSubmodule D) : ℝ :=
  Classical.choose (mem_pureSubmodule.mp u.2)

theorem pureSq_spec (u : pureSubmodule D) :
    (u : D) * (u : D) = (pureSq u) • (1 : D) :=
  (Classical.choose_spec (mem_pureSubmodule.mp u.2)).2

theorem pureSq_nonpos (u : pureSubmodule D) : pureSq u ≤ 0 :=
  (Classical.choose_spec (mem_pureSubmodule.mp u.2)).1

/-- **Well defined for a reason.** Any real the element squares to IS `pureSq`, so nothing depends
on the choice `Classical.choose` made. -/
theorem pureSq_eq {u : pureSubmodule D} {c : ℝ} (h : (u : D) * (u : D) = c • (1 : D)) :
    c = pureSq u :=
  sq_scalar_unique h (pureSq_spec u)

/-- A nonzero pure element has a strictly negative square. -/
theorem pureSq_neg_of_ne_zero {u : pureSubmodule D} (hu : u ≠ 0) : pureSq u < 0 :=
  sq_neg_of_ne_zero (mem_pureSubmodule.mp u.2) (fun h => hu (Subtype.ext h)) (pureSq_spec u)

/-- The form, by polarisation. -/
noncomputable def pureForm (u v : pureSubmodule D) : ℝ :=
  (pureSq (u + v) - pureSq u - pureSq v) / 2

/-- **It does what a form should**: the anticommutator is twice it. -/
theorem anticomm_eq (u v : pureSubmodule D) :
    (u : D) * (v : D) + (v : D) * (u : D) = (2 * pureForm u v) • (1 : D) := by
  have hsum : ((u + v : pureSubmodule D) : D) = (u : D) + (v : D) := rfl
  have hexp : ((u : D) + (v : D)) * ((u : D) + (v : D))
      = (u : D) * (u : D) + ((u : D) * (v : D) + (v : D) * (u : D)) + (v : D) * (v : D) :=
    sq_add _ _
  have hkey : (pureSq (u + v)) • (1 : D)
      = (pureSq u) • (1 : D) + ((u : D) * (v : D) + (v : D) * (u : D))
        + (pureSq v) • (1 : D) := by
    rw [← pureSq_spec u, ← pureSq_spec v, ← hexp, ← hsum, pureSq_spec (u + v)]
  rw [pureForm]
  have hhalf : (2 * ((pureSq (u + v) - pureSq u - pureSq v) / 2))
      = pureSq (u + v) - pureSq u - pureSq v := by ring
  rw [hhalf]
  have hsplit : (pureSq (u + v) - pureSq u - pureSq v) • (1 : D)
      = pureSq (u + v) • (1 : D) - pureSq u • (1 : D) - pureSq v • (1 : D) := by module
  rw [hsplit, hkey]
  abel

/-- The diagonal is the square. -/
theorem pureForm_self (u : pureSubmodule D) : pureForm u u = pureSq u := by
  have h := anticomm_eq u u
  have hsq : (u : D) * (u : D) + (u : D) * (u : D) = (2 * pureSq u) • (1 : D) := by
    rw [pureSq_spec u]; module
  have := smul_one_inj (D := D) (h.symm.trans hsq)
  linarith

/-- Symmetry. -/
theorem pureForm_comm (u v : pureSubmodule D) : pureForm u v = pureForm v u := by
  have h := anticomm_eq u v
  have h' := anticomm_eq v u
  have hcomm : (u : D) * (v : D) + (v : D) * (u : D) = (v : D) * (u : D) + (u : D) * (v : D) :=
    add_comm _ _
  have := smul_one_inj (D := D) (h.symm.trans (hcomm.trans h'))
  linarith

/-- **THE DICTIONARY.** Orthogonal is anticommuting. -/
theorem orthogonal_iff_anticomm (u v : pureSubmodule D) :
    pureForm u v = 0 ↔ (u : D) * (v : D) + (v : D) * (u : D) = 0 := by
  constructor
  · intro h
    rw [anticomm_eq u v, h, mul_zero, zero_smul]
  · intro h
    have hz : (2 * pureForm u v) • (1 : D) = (0 : ℝ) • (1 : D) := by
      rw [← anticomm_eq u v, h, zero_smul]
    have := smul_one_inj (D := D) hz
    linarith

end RealDivisionFormFun
