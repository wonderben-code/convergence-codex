import PerronPrimitive
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-!
# The Perron chain, stated on Mathlib's own predicate

`IsingTransfer2D` and `IsingTransferSym` both say *"Perron–Frobenius is absent from Mathlib"*, on
a probe for `PerronFrobenius` / `perronFrobenius`: **zero files**. The claim is TRUE and the probe
is the wrong one, which `ERRATUM 234`'s addendum is about — it searches for the theorem's
**eponym**, and Mathlib does not name it after Perron or Frobenius at all.

**What Mathlib has is the VOCABULARY: `Matrix.IsPrimitive` and `Matrix.IsIrreducible`.** Seventeen
declarations between them, and every one is a definition or an accessor — `nonneg`,
`exists_pos_pow`, `exists_pos`, `transpose`, `connected`, `isIrreducible`. **There is no
conclusion**: nothing about a dominant eigenvalue, its simplicity, or a gap. So the estate's claim
survives its own bad probe, and what the bad probe hid is that the two sides fit together.

**`PerronPrimitive.abs_lt_max_of_ne_of_primitive` takes `hnn : ∀ i j, 0 ≤ A i j` together with
`0 < k` and `∀ i j, 0 < (A ^ k) i j`. That triple IS `Matrix.IsPrimitive`**, field for field:
`IsPrimitive.nonneg` and `IsPrimitive.exists_pos_pow`. The estate hand-wrote a predicate the
library names.

## What is proved

* **`isPrimitive_of_pos`** — a strictly positive matrix is `Matrix.IsPrimitive`, at `k = 1`;
* **`abs_lt_max_of_ne_of_isPrimitive`** and **`max_pos_of_isPrimitive`** — the estate's two
  conclusions, restated with `Matrix.IsPrimitive` as the hypothesis instead of the triple;
* **`transferSym_isPrimitive`** — the two-dimensional Ising strip's symmetrised transfer matrix
  satisfies Mathlib's predicate;
* **`transferSym_gap_isPrimitive`** — and therefore the gap, stated end to end in Mathlib's
  vocabulary.

## What this is and is not

**It is a restatement, not a new theorem, and the mathematics is `PerronPrimitive`'s.** Every proof
below destructures `Matrix.IsPrimitive` and calls that file. What it buys is that the estate's
Perron results now have the shape a Mathlib contribution would need — a conclusion about
`Matrix.IsPrimitive`, which Mathlib defines and says nothing further about.

**It does not prove Perron–Frobenius.** The results carry `Matrix.IsHermitian` throughout, and the
classical theorem does not: symmetry is what gives this estate a real spectrum and a variational
argument, and the general case is untouched. **`Matrix.IsIrreducible` is not used at all** — the
weaker hypothesis under which the classical theorem still holds, and which nothing here reaches.

**And it does not move `WALLS` §W4.** Everything is at one fixed width; item 3 wants the width
limit.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace PerronMathlibPredicate

open Matrix IsingTransfer2D IsingTransferSym PerronPrimitive PerronGap

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **A STRICTLY POSITIVE MATRIX IS `Matrix.IsPrimitive`**, with `k = 1`. -/
theorem isPrimitive_of_pos {A : Matrix n n ℝ} (hpos : ∀ i j, 0 < A i j) : A.IsPrimitive :=
  ⟨fun i j => (hpos i j).le, ⟨1, one_pos, by simpa using hpos⟩⟩

/-- **THE GAP, ON MATHLIB'S HYPOTHESIS.** `PerronPrimitive.abs_lt_max_of_ne_of_primitive` with its
three loose hypotheses replaced by the one predicate they spell out. -/
theorem abs_lt_max_of_ne_of_isPrimitive [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (hP : A.IsPrimitive) {p : n} (hp : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues p) {j : n}
    (hne : hA.eigenvalues j ≠ hA.eigenvalues p) :
    |hA.eigenvalues j| < hA.eigenvalues p := by
  obtain ⟨k, hk, hkpos⟩ := hP.exists_pos_pow
  exact abs_lt_max_of_ne_of_primitive hA hP.nonneg hk hkpos hp hne

/-- **AND THE TOP EIGENVALUE IS POSITIVE**, likewise. -/
theorem max_pos_of_isPrimitive [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (hP : A.IsPrimitive) {p : n} (hp : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues p) :
    0 < hA.eigenvalues p := by
  obtain ⟨k, hk, hkpos⟩ := hP.exists_pos_pow
  exact max_pos_of_primitive hA hP.nonneg hk hkpos hp

/-- **THE STRIP'S TRANSFER MATRIX SATISFIES MATHLIB'S PREDICATE.** -/
theorem transferSym_isPrimitive (β : ℝ) (m : ℕ) : (transferSym β m).IsPrimitive :=
  isPrimitive_of_pos fun i j => transferSym_pos β i j

/-- **THE GAP AT THE WALL'S OWN MATRIX, END TO END IN MATHLIB'S VOCABULARY.**

**Deliberately the same statement as `PerronGap.transferSym_eigenvalues_gap` and
`PerronPrimitive.transferSym_gap_primitive`, and not a new result** — the third time this project
states one number's separation, which is the cost of a restatement and is stated rather than
hidden. Nothing downstream should cite this in preference to `PerronGap`'s version; what it is for
is that a reader coming from `Matrix.IsPrimitive` finds the chain from where they are. -/
theorem transferSym_gap_isPrimitive (β : ℝ) (m : ℕ) :
    ∃ p : Col m, 0 < (transferSym_isHermitian β m).eigenvalues p ∧
      (∀ j, (transferSym_isHermitian β m).eigenvalues j
        ≤ (transferSym_isHermitian β m).eigenvalues p) ∧
      ∀ j, (transferSym_isHermitian β m).eigenvalues j
            ≠ (transferSym_isHermitian β m).eigenvalues p →
        |(transferSym_isHermitian β m).eigenvalues j|
          < (transferSym_isHermitian β m).eigenvalues p := by
  obtain ⟨p, hp⟩ := exists_max_eigenvalue (transferSym_isHermitian β m)
  exact ⟨p, max_pos_of_isPrimitive _ (transferSym_isPrimitive β m) hp, hp,
    fun j hj => abs_lt_max_of_ne_of_isPrimitive _ (transferSym_isPrimitive β m) hp hj⟩

end PerronMathlibPredicate
