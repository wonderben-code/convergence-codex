import QuaternionCenter
import CliffordRealMinkowski

/-!
# The centre of `Cl(1,3;ℝ)` is `ℝ` — ALREADY PROVED IN THIS ESTATE, see the retraction below

**RETRACTION, `ERRATUM 118`, added on the day this file was written.** `SpinKernel.lean` proved
`clifford_central` on **8 August**, by transport along `cliffordRealMinkowskiEquiv` — the same
route,
the same isomorphism. `WALLS` §W7 records that closure **four paragraphs below the route paragraphs
this file quotes**, and the section was not read to its end. **This file closes nothing that was
open.**

What it legitimately adds: `mem_center_congr`, the transport stated as a **general reusable lemma**
about any `AlgEquiv` rather than inlined into one proof, and `instIsCentral`, which `SpinKernel`
does not provide. Everything else here is a second proof of a theorem the estate already had.

`WALLS.md` §W7's step (d) has three parts, and step (iii) of them is:

> *"The centre of `Cl(1,3;ℝ)` is `ℝ`. This is the real work. Route: transport along the estate's
> `cliffordRealMinkowskiEquiv` to `M₂(ℍ)` and compute the centre there."*

**`SpinKernel` did exactly this on 8 August** and `WALLS` says so four paragraphs after the quote
above. The 11 August sequence — `QuaternionCenter` proving the route's destination and claiming the
step (`ERRATUM 117` second addendum), then this file supplying the transport — re-derived a closed
result twice over. Both errors are the same one: **reading part of a document and concluding about
the whole.**

> **`mem_center_congr`** — centre membership passes along **any** `AlgEquiv`, in either direction.
> Stated generally because it is a general fact and nothing about it is Clifford-specific.
>
> **`algebraMap_eq_scalar`** — the one bridge the composition needs: the algebra map into a matrix
> algebra is `Matrix.scalar` of the algebra map into the entries.
>
> **`center_eq_range`** — the centre of `Cl(1,3;ℝ)` is exactly the scalars. **Already proved as
> `SpinKernel.clifford_central`; this is a second proof.**
>
> **`mem_center_iff`** — the same as a membership criterion, which is the form step (ii) consumes.

## What this does NOT do

**It does not close W7.** Step (d) needs (i), (ii) and (iii); §W7 records (i) and (ii) as small and
verified-available (`ι_spinToEndo`, `ι_injective`, `CliffordAlgebra.induction`,
`CliffordAlgebra.adjoin_range_ι`), but **small is not done, and neither is built here.** Step (d)
itself is one of the three parts of the double-cover statement, and the other two remain
research-level.

**It says nothing about the kernel.** "The centre is `ℝ`" is the ingredient; "the kernel is no
larger than `±1`" is the conclusion §W7 wants, and getting there needs (i), (ii) and then the
unitarity argument (iv). None of that is here.
-/

namespace CliffordCenter

open CliffordRealMinkowski

universe u v

/-! ## 1. Centres transport along algebra equivalences -/

variable {R : Type u} [CommSemiring R]

/-- **CENTRE MEMBERSHIP PASSES ALONG AN `AlgEquiv`.** Surjectivity gives the forward direction —
every element of the target is `e a` for some `a` — and injectivity gives the reverse. Nothing here
is specific to Clifford algebras or to `ℝ`, so it is stated for an arbitrary equivalence of
`R`-algebras.

Mathlib has `Subsemiring.centerCongr`, which packages the same fact as an equivalence of the two
centres as *subobjects*. This is the membership form, which is what a composition with
`QuaternionCenter.mem_matrixCenter_iff` actually consumes. -/
theorem mem_center_congr {A : Type u} {B : Type v} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) {x : A} :
    x ∈ Set.center A ↔ e x ∈ Set.center B := by
  simp only [Semigroup.mem_center_iff]
  constructor
  · intro h b
    obtain ⟨a, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, h a]
  · intro h a
    exact e.injective (by rw [map_mul, map_mul, h (e a)])

/-! ## 2. The bridge: `algebraMap` into a matrix algebra is `Matrix.scalar` -/

/-- The algebra map into `Mₙ(α)` is `Matrix.scalar` applied to the algebra map into `α`. Needed
because `QuaternionCenter.mem_matrixCenter_iff` speaks of `Matrix.scalar` while `AlgEquiv.commutes`
speaks of `algebraMap`, and the composition has to put them on the same side. -/
theorem algebraMap_eq_scalar {n : Type*} [Fintype n] [DecidableEq n]
    {α : Type*} [Semiring α] [Algebra R α] (r : R) :
    algebraMap R (Matrix n n α) r = Matrix.scalar n (algebraMap R α r) := by
  rw [Matrix.algebraMap_eq_diagonal]
  rfl

/-! ## 3. The centre of `Cl(1,3;ℝ)` -/

/-- **THE CENTRE OF `Cl(1,3;ℝ)` IS THE SCALARS.** By transport along
`cliffordRealMinkowskiEquiv`, using the centre of `M₂(ℍ[ℝ])`.

**`SpinKernel.clifford_central` states this and proves it the same way, since 8 August.** This is a
second proof and is kept only because `mem_center_congr` above factors the transport out as a
general lemma. The one thing here that is not a duplicate is that the matrix half comes from
**Mathlib** (`Matrix.subsemigroupCenter_eq_scalar_map`, any `Semiring`) rather than being
hand-built, which is `ERRATUM 118`'s surviving finding. -/
theorem mem_center_iff {x : CliffordAlgebra Q₁₃} :
    x ∈ Set.center (CliffordAlgebra Q₁₃)
      ↔ ∃ r : ℝ, x = algebraMap ℝ (CliffordAlgebra Q₁₃) r := by
  rw [mem_center_congr cliffordRealMinkowskiEquiv, QuaternionCenter.mem_matrixCenter_iff]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, cliffordRealMinkowskiEquiv.injective ?_⟩
    rw [AlgEquiv.commutes, hr, algebraMap_eq_scalar]
  · rintro ⟨r, rfl⟩
    exact ⟨r, by rw [AlgEquiv.commutes, algebraMap_eq_scalar]⟩

/-- The same, as an equality of sets. -/
theorem center_eq_range :
    Set.center (CliffordAlgebra Q₁₃) = Set.range (algebraMap ℝ (CliffordAlgebra Q₁₃)) := by
  ext x
  rw [mem_center_iff]
  exact ⟨fun ⟨r, hr⟩ => ⟨r, hr.symm⟩, fun ⟨r, hr⟩ => ⟨r, hr.symm⟩⟩

/-- **AND THE `Algebra.IsCentral` INSTANCE**, matching the one `QuaternionCenter` supplies for
`ℍ[ℝ]`. `Cl(1,3;ℝ)` is a central simple algebra over `ℝ`; this is the central half, and **no claim
is made about simplicity**. -/
instance instIsCentral : Algebra.IsCentral ℝ (CliffordAlgebra Q₁₃) where
  out x hx := by
    obtain ⟨r, hr⟩ := mem_center_iff.1 (by simpa using hx)
    exact ⟨r, hr.symm⟩

/-! ## 4. Nothing here is closed by this file

**`WALLS` §W7 step (d) was closed on 8 August by `SpinKernel.lean`** — `kernel_iff`, a spin element
acts trivially exactly when it is `±1`, with (i), (ii), (iii) and (iv) all built there. This file
re-proved (iii). **W7 itself is not closed**: step (d) is one of three parts of the double-cover
statement and the other two remain research-level, which was true before this file and is true
after it. -/

end CliffordCenter
