import Mathlib.Algebra.Quaternion
import Mathlib.Tactic

/-!
# The centre of `ℍ[ℝ]` is `ℝ`

`WALLS.md` §W7 step (iii) needs the centre of `M₂(ℍ[ℝ])`, and records that **two** ingredients are
missing from Mathlib and must be built here:

> *"**Verified ABSENT from Mathlib, both of them:** there is no ring-centre theorem for a matrix
> algebra (`Matrix.mem_center_iff` does not exist …), and there is nothing about the centre of the
> quaternions (`Quaternion.mem_center_iff` does not exist, and `Algebra.IsCentral ℝ ℍ[ℝ]` is not
> an instance — the class exists, the instance does not). Both must be built."*

**Half of that is false, and the half that is true is this file.** Re-probed 2026-08-11 against
the pinned environment's *statements* rather than against guessed names (`check_ledger.py
--shape`, built this day after `ERRATUM 116`):

* **The matrix half EXISTS.** `Matrix.center_eq_range` states
  `Set.center (Matrix n n R) = Set.range (Matrix.scalar n)` over any `CommSemiring`, with
  `Matrix.subsemigroupCenter_eq_scalar_map` beside it. The earlier probe tried
  `Matrix.mem_center_iff`, `Matrix.center_eq` and `Matrix.mem_center_iff'` — **it missed by one
  suffix** — and recorded an absence that held a wall's residue shut. See `ERRATUM 117`.
* **The quaternion half is genuinely absent.** 148 statements in the environment mention
  `Quaternion` and **not one mentions a centre**; `Algebra.IsCentral` exists as a class with 24
  statements and has no instance for `ℍ[ℝ]`. That claim survived the shape probe, so this file
  proves it.

> **`mem_center_iff`** — `q` is central in `ℍ[ℝ]` **iff** it is real.
>
> **`center_eq_range`** — deliberately named to match Mathlib's matrix theorem, because the two are
> now the two halves of the same argument and a reader should see that.
>
> **`instIsCentral`** — and the `Algebra.IsCentral ℝ ℍ[ℝ]` instance the wall's note says does not
> exist. It exists now.
>
> **`mem_matrixCenter_iff`, `matrixCenter_eq_range`** — and therefore **the centre of `Mₙ(ℍ[ℝ])` is
> the real scalar matrices**, which is `WALLS` §W7 step (iii) itself. See the section below on why
> this header first claimed the opposite.

## The argument, and why two witnesses suffice

Centrality is a condition against *every* quaternion, but it is pinned down by **two**: commuting
with `i` forces the `j` and `k` components to vanish, and commuting with `j` forces the `i`
component to vanish. Nothing needs to be said about `k`, and the file proves that rather than
checking a third case for reassurance.

## §3 closes step (iii), and this section used to say it did not

**Superseded in place, and the superseded text is quoted because it was wrong for an instructive
reason.** The first draft of this header read:

> *"**It does not close W7 step (iii)** … Mathlib's `Matrix.center_eq_range` is stated for a
> `CommSemiring` of entries — **`ℍ[ℝ]` is not commutative** — so the two halves do not simply
> compose. **The remaining step is the centre of a matrix algebra over a NON-commutative base**,
> which is a different theorem from the one Mathlib has, and it is not proved here."*

Every clause about `center_eq_range` is true. The inference — *therefore Mathlib cannot do the
non-commutative case* — is **false**. **`Matrix.subsemigroupCenter_eq_scalar_map` is stated over
`[Semiring α]`**, no commutativity anywhere, and gives the centre of the matrix semigroup as the
image under `Matrix.scalar` of the centre of the base. It was **one line below `center_eq_range` in
the same `--shape` output**; the first reading took the first hit and stopped.

So §3 proves **`mem_matrixCenter_iff`** and **`matrixCenter_eq_range`**: the centre of `Mₙ(ℍ[ℝ])`
is exactly the real scalar matrices, for **every** index type rather than only `Fin 2`.

**AND THE FIRST VERSION OF THIS PARAGRAPH THEN SAID "That is `WALLS` §W7 step (iii)", WHICH IS AN
OVERCLAIM.** Step (iii) is *"the centre of `Cl(1,3;ℝ)` is ℝ"*; transporting along
`cliffordRealMinkowskiEquiv` to `M₂(ℍ)` is its **route**. This file proves the route's
**destination**. The transport is **not done here**, so step (iii) is **not closed** — what is
closed is that both ingredients the wall called missing are now in hand, one from Mathlib and one
from §2. Mathlib's `Subsemiring.centerCongr` transports a centre along a ring equivalence and is
the obvious next rung.

**That is three instances in one day of the same error** — a name probe that missed a lemma, a
shape search read to its first hit, and now a step's *route* read as the step. All three are the
same move: taking a part for the whole. Recorded rather than smoothed over, in `ERRATUM 117`.

## What this still does NOT do

**It does not close W7.** Step (iii) is one of four. **No claim is made about `Cl(1,3;ℝ)`** —
transporting along `cliffordRealMinkowskiEquiv` is step (ii), steps (i) and (iv) are separate, and
all three are untouched here. What this file settles is the centre computation those steps consume.
-/

open scoped Quaternion

namespace QuaternionCenter

/-- The quaternion `i`. -/
def qi : ℍ[ℝ] := ⟨0, 1, 0, 0⟩

/-- The quaternion `j`. -/
def qj : ℍ[ℝ] := ⟨0, 0, 1, 0⟩

/-! ## 1. Two witnesses are enough -/

/-- **Commuting with `i` kills the `j` and `k` components.** -/
theorem imJ_imK_eq_zero_of_comm_qi {q : ℍ[ℝ]} (h : q * qi = qi * q) :
    q.imJ = 0 ∧ q.imK = 0 := by
  rw [Quaternion.ext_iff] at h
  obtain ⟨-, -, hJ, hK⟩ := h
  simp only [qi, Quaternion.imJ_mul, Quaternion.imK_mul] at hJ hK
  constructor <;> linarith

/-- **Commuting with `j` kills the `i` component** — and it is read off the `k` component of the
equation, not the `i` one. `(q·j).imK = q.imI` while `(j·q).imK = −q.imI`, whereas the `i`
components of the two sides say something about `q.imK` and repeat what `i` already gave. The
first draft of this file took the `i` component because the conclusion is about `imI`, and
`linarith` refused it with `q.imK` on the board. -/
theorem imI_eq_zero_of_comm_qj {q : ℍ[ℝ]} (h : q * qj = qj * q) : q.imI = 0 := by
  rw [Quaternion.ext_iff] at h
  obtain ⟨-, -, -, hK⟩ := h
  simp only [qj, Quaternion.imK_mul] at hK
  linarith

/-! ## 2. The centre -/

/-- **A QUATERNION IS CENTRAL IFF IT IS REAL.** The forward direction uses exactly two test
elements, `i` and `j`; the backward direction is `Algebra.commutes`.

`Semigroup.mem_center_iff` is what makes both directions one line each — centrality in a semigroup
is plain commutation, with none of `IsMulCentral`'s associativity fields to discharge. -/
theorem mem_center_iff {q : ℍ[ℝ]} :
    q ∈ Set.center ℍ[ℝ] ↔ ∃ r : ℝ, q = algebraMap ℝ ℍ[ℝ] r := by
  constructor
  · intro hq
    obtain ⟨hJ, hK⟩ :=
      imJ_imK_eq_zero_of_comm_qi (Semigroup.mem_center_iff.1 hq qi).symm
    have hI := imI_eq_zero_of_comm_qj (Semigroup.mem_center_iff.1 hq qj).symm
    refine ⟨q.re, ?_⟩
    rw [Quaternion.ext_iff]
    simp [hI, hJ, hK]
  · rintro ⟨r, rfl⟩
    exact Semigroup.mem_center_iff.2 fun g => (Algebra.commutes r g).symm

/-- **THE CENTRE OF `ℍ[ℝ]`, as a set.** Named to match `Matrix.center_eq_range`, which is the other
half of `WALLS` §W7 step (iii) and which — contrary to that section's note — Mathlib already has. -/
theorem center_eq_range : Set.center ℍ[ℝ] = Set.range (algebraMap ℝ ℍ[ℝ]) := by
  ext q
  rw [mem_center_iff]
  exact ⟨fun ⟨r, hr⟩ => ⟨r, hr.symm⟩, fun ⟨r, hr⟩ => ⟨r, hr.symm⟩⟩

/-- **AND THE INSTANCE `WALLS` §W7 SAYS DOES NOT EXIST.** `Algebra.IsCentral ℝ ℍ[ℝ]`: the class was
already in Mathlib with 24 statements about it, and no instance for the quaternions. -/
instance instIsCentral : Algebra.IsCentral ℝ ℍ[ℝ] where
  out q hq := by
    obtain ⟨r, hr⟩ := mem_center_iff.1 (by simpa using hq)
    exact ⟨r, hr.symm⟩

/-! ## 3. The centre of a matrix algebra over `ℍ[ℝ]`

**And the step this file's header called "the only thing left" is not left either.** The header
said Mathlib's `Matrix.center_eq_range` needs a `CommSemiring` of entries, so it cannot speak about
`M₂(ℍ[ℝ])` — which is true of *that* lemma. It is not true of Mathlib:
**`Matrix.subsemigroupCenter_eq_scalar_map` is stated over `[Semiring α]`**, with no commutativity
at all, and says the centre of the matrix semigroup is the image under `Matrix.scalar` of the
centre of the base. Composed with §2, that is `WALLS` §W7 step (iii).

**This was found by asking the KEY GENERATOR question immediately** (`PROOF_STRATEGY` §6 rule 3:
if the unit just finished was a B, retry B→C before touching the queue) — the lemma was sitting in
the same `--shape` output that produced §2's finding, one line below it, and the first reading took
`center_eq_range` and stopped. -/

/-- **THE CENTRE OF `Mₙ(ℍ[ℝ])` IS THE REAL SCALARS.** `WALLS` §W7 step (iii), for every index type
rather than only `Fin 2`. Mathlib supplies the matrix half over a **non-commutative** base and §2
supplies the quaternion half. -/
theorem mem_matrixCenter_iff {n : Type*} [DecidableEq n] [Fintype n]
    {A : Matrix n n ℍ[ℝ]} :
    A ∈ Set.center (Matrix n n ℍ[ℝ]) ↔ ∃ r : ℝ, A = Matrix.scalar n (algebraMap ℝ ℍ[ℝ] r) := by
  constructor
  · intro hA
    have h1 : A ∈ Subsemigroup.center (Matrix n n ℍ[ℝ]) :=
      Subsemigroup.mem_center_iff.2 (Semigroup.mem_center_iff.1 hA)
    rw [Matrix.subsemigroupCenter_eq_scalar_map] at h1
    obtain ⟨c, hc, rfl⟩ := h1
    obtain ⟨r, hr⟩ :=
      mem_center_iff.1 (Semigroup.mem_center_iff.2 (Subsemigroup.mem_center_iff.1 hc))
    -- `Subsemigroup.map` carries `Matrix.scalar n` through two coercions; they are
    -- definitionally the plain application, so `rfl` closes the gap `rw` leaves.
    exact ⟨r, by rw [hr]; rfl⟩
  · rintro ⟨r, rfl⟩
    refine Semigroup.mem_center_iff.2 fun B => ?_
    have : (Matrix.scalar n) (algebraMap ℝ ℍ[ℝ] r) ∈ Subsemigroup.center (Matrix n n ℍ[ℝ]) := by
      rw [Matrix.subsemigroupCenter_eq_scalar_map]
      exact ⟨algebraMap ℝ ℍ[ℝ] r,
        Subsemigroup.mem_center_iff.2 (Semigroup.mem_center_iff.1 (mem_center_iff.2 ⟨r, rfl⟩)),
        rfl⟩
    exact (Subsemigroup.mem_center_iff.1 this B)

/-- The same statement as an equality of sets. -/
theorem matrixCenter_eq_range {n : Type*} [DecidableEq n] [Fintype n] :
    Set.center (Matrix n n ℍ[ℝ])
      = Set.range (fun r : ℝ => Matrix.scalar n (algebraMap ℝ ℍ[ℝ] r)) := by
  ext A
  rw [mem_matrixCenter_iff]
  exact ⟨fun ⟨r, hr⟩ => ⟨r, hr.symm⟩, fun ⟨r, hr⟩ => ⟨r, hr.symm⟩⟩

/-! ## 4. The two witnesses are not redundant

A reader may reasonably ask whether one test element would have done. It would not, and the file
answers that with counterexamples rather than with an assertion.

**These are stated existentially on purpose.** A first draft wrote them as
`qi * qi = qi * qi ∧ ¬∃ r, qi = algebraMap ℝ _ r`, and the first conjunct of that is `rfl` — a
tautology sitting where a reader would read a proved commutation. The claim being made is that
*some* non-real quaternion commutes with the test element, and that is what these now say. -/

/-- **`i` ALONE IS NOT ENOUGH**: something commutes with `i` and is not real, namely `i`. -/
theorem exists_comm_qi_not_real :
    ∃ q : ℍ[ℝ], q * qi = qi * q ∧ ¬ ∃ r : ℝ, q = algebraMap ℝ ℍ[ℝ] r := by
  refine ⟨qi, rfl, ?_⟩
  rintro ⟨r, hr⟩
  have := congrArg QuaternionAlgebra.imI hr
  simp [qi] at this

/-- **`j` ALONE IS NOT ENOUGH**, for the same reason. -/
theorem exists_comm_qj_not_real :
    ∃ q : ℍ[ℝ], q * qj = qj * q ∧ ¬ ∃ r : ℝ, q = algebraMap ℝ ℍ[ℝ] r := by
  refine ⟨qj, rfl, ?_⟩
  rintro ⟨r, hr⟩
  have := congrArg QuaternionAlgebra.imJ hr
  simp [qj] at this

end QuaternionCenter
