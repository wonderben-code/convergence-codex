import QuaternionCenter
import CliffordRealMinkowski

/-!
# The centre of `Cl(1,3;ℝ)` is `ℝ` — `WALLS` §W7 step (iii)

`WALLS.md` §W7's step (d) has three parts, and step (iii) of them is:

> *"The centre of `Cl(1,3;ℝ)` is `ℝ`. This is the real work. Route: transport along the estate's
> `cliffordRealMinkowskiEquiv` to `M₂(ℍ)` and compute the centre there."*

**`QuaternionCenter` computed the centre there. It did not transport, and it said it had closed the
step.** That overclaim is `ERRATUM 117`'s second addendum — a step read down as far as its *route*,
the route's destination proved, and the step's name written on it. This file is the transport, and
with it the step really does close.

> **`mem_center_congr`** — centre membership passes along **any** `AlgEquiv`, in either direction.
> Stated generally because it is a general fact and nothing about it is Clifford-specific.
>
> **`algebraMap_eq_scalar`** — the one bridge the composition needs: the algebra map into a matrix
> algebra is `Matrix.scalar` of the algebra map into the entries.
>
> **`center_eq_range`** — **the centre of `Cl(1,3;ℝ)` is exactly the scalars.** §W7 step (iii).
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

/-- **THE CENTRE OF `Cl(1,3;ℝ)` IS THE SCALARS.** `WALLS` §W7 step (iii), by the route §W7 itself
proposed: transport along `cliffordRealMinkowskiEquiv` and use the centre of `M₂(ℍ[ℝ])`.

Both halves of the computation were in hand before this file — the matrix half from Mathlib
(`Matrix.subsemigroupCenter_eq_scalar_map`, over any `Semiring`, so the non-commutative entries are
fine) and the quaternion half from `QuaternionCenter`. **What was missing was exactly this
crossing.** -/
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

/-! ## 4. The step is closed, and the wall is not

`WALLS` §W7 step (d)(iii) asked for exactly `center_eq_range`, and it is proved. **Step (d) is not
closed**: (i) *trivial action ⇒ commutes with every vector* and (ii) *commutes with every vector ⇒
central* are both still to build, and §W7 records them as small rather than as done — a distinction
this estate has now got wrong once today and should not repeat. **W7 is not closed**: step (d) is
one of several, and the other parts of the double-cover statement remain research-level. -/

end CliffordCenter
