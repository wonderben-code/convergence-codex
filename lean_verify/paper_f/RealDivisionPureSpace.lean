import RealDivisionPureForm

/-!
# The pure part as a subspace, its complement, and normalised pure elements

`RealDivisionPureAdd` and `RealDivisionPureForm` proved the closure and definiteness statements and
both declined to bundle anything, on the ground that a `Submodule` nothing consumes is a definition
rather than a theorem. **Leg (c) consumes it** — it is a statement about `dim V` — so the bundling
is built here, where it is used, rather than where it was first available.

> **`pureSubmodule`** — the pure part as a `Submodule ℝ D`, from `isPure_zero`, `isPure_add` and
> `isPure_smul`.
>
> **`isCompl_span_one`** — `ℝ ∙ 1` and the pure part are **complements**. This is leg (a) restated
> in bundled form: `exists_scalar_add_pure` gives codisjointness and `isPure_scalar_iff` gives
> disjointness.
>
> **`finrank_eq_succ`** — hence `dim_ℝ D = 1 + dim_ℝ V`. **This is the equation leg (c) is about**:
> `dim V ∈ {0, 1, 3}` is exactly `dim D ∈ {1, 2, 4}`.
>
> **`exists_smul_sq_neg_one`** — every nonzero pure element can be scaled to square to `−1`. That
> is the normalisation every step of leg (c) opens with, and it is where `sq_neg_of_ne_zero`'s
> strictness is spent: a square of `0` could not be scaled anywhere.

## What leg (c) still needs, and none of it is here

1. **One orthogonalisation step**: given `i` normalised, a nonzero pure `v` gives a pure element
   orthogonal to `i`, by subtracting the component along `i`.
2. **`dim V ≤ 3`**: if `i`, `j` are orthogonal and normalised then `k := ij` is normalised
   (`RealDivisionPureForm.sq_mul_of_anticomm`), and any `l` orthogonal to all three both commutes
   and anticommutes with `k`, forcing `kl = 0` and so `l = 0`.
3. **The identifications** `dim V = 0, 1, 3 ⟹ D ≅ ℝ, ℂ, ℍ`, which are algebra isomorphisms and not
   dimension counts.

**None is attempted and no cost is claimed for any of them** (`ERRATUM 194`, `ERRATUM 246`). Step 2
is the one that decides the theorem; steps 1 and 3 are bookkeeping by comparison, and saying so is a
judgement about shape, not an estimate.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RealDivisionPureSpace

open RealDivisionPure RealDivisionPureAdd RealDivisionPureForm

variable (D : Type*) [DivisionRing D] [Algebra ℝ D] [Module.Finite ℝ D]

/-- The pure part, bundled. Built here rather than in the file that proved the closure properties,
because that file had no consumer for it and this one does. -/
def pureSubmodule : Submodule ℝ D where
  carrier := {d | IsPure d}
  add_mem' := isPure_add
  zero_mem' := isPure_zero
  smul_mem' := fun t _ h => isPure_smul h t

variable {D}

@[simp] theorem mem_pureSubmodule {d : D} : d ∈ pureSubmodule D ↔ IsPure d := Iff.rfl

/-- **Leg (a) in bundled form**: the scalars and the pure part are complements. -/
theorem isCompl_span_one : IsCompl (ℝ ∙ (1 : D)) (pureSubmodule D) := by
  rw [isCompl_iff]
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [(isPure_scalar_iff r).mp hx', zero_smul]
  · rw [codisjoint_iff, eq_top_iff]
    intro d _
    obtain ⟨r, v, hv, hd⟩ := exists_scalar_add_pure d
    exact hd ▸ Submodule.mem_sup.mpr
      ⟨r • (1 : D), Submodule.mem_span_singleton.mpr ⟨r, rfl⟩, v, hv, rfl⟩

/-- **The equation leg (c) is about.** `dim V ∈ {0, 1, 3}` is `dim D ∈ {1, 2, 4}`. -/
theorem finrank_eq_succ :
    1 + Module.finrank ℝ (pureSubmodule D) = Module.finrank ℝ D := by
  have h1 : Module.finrank ℝ (ℝ ∙ (1 : D)) = 1 := finrank_span_singleton one_ne_zero
  have := Submodule.finrank_add_eq_of_isCompl (isCompl_span_one (D := D))
  rwa [h1] at this

/-! **Normalisation needs no finiteness**, and is stated outside the section that assumes it: it
takes `IsPure u` as a hypothesis rather than deriving it, so nothing here calls `exists_quadratic`.
The linter reported the section variable unused and this is the true generality rather than an
`omit` (`ERRATUM 274`, `ERRATUM 278`) — the same correction this chain has now made in four
consecutive files, which is worth noticing about how I write section headers. -/
section NoFiniteness

variable {D : Type*} [DivisionRing D] [Algebra ℝ D]

/-- **Normalisation.** Every nonzero pure element scales to one squaring to `−1`; this is where
`sq_neg_of_ne_zero`'s strictness is spent. -/
theorem exists_smul_sq_neg_one {u : D} (hu : IsPure u) (hne : u ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ (t • u) * (t • u) = (-1 : ℝ) • (1 : D) := by
  obtain ⟨c, hc, h⟩ := hu
  have hcneg : c < 0 := sq_neg_of_ne_zero ⟨c, hc, h⟩ hne h
  have hpos : (0 : ℝ) < -c := by linarith
  have hs : Real.sqrt (-c) * Real.sqrt (-c) = -c := Real.mul_self_sqrt (le_of_lt hpos)
  have hspos : 0 < Real.sqrt (-c) := Real.sqrt_pos.mpr hpos
  refine ⟨1 / Real.sqrt (-c), by positivity, ?_⟩
  rw [smul_mul_assoc, mul_smul_comm, h, smul_smul, smul_smul]
  congr 1
  field_simp
  linarith [hs]

end NoFiniteness

end RealDivisionPureSpace
