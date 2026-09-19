import FieldBlockContinuum

/-!
# The box, completely: finite exactly when a side or a dimension is trivial

`RE-SWEEP #68` closed a watchlist clause by proving the box dichotomy at `2 ≤ d` and side
`≥ 2`, and **named its own residue in the same breath**: nothing covered `d = 0` or side length
one, because those theorems fix the side at `k + 1 ≥ 2`. This file removes both restrictions, so
the statement is about `boxGraph d n` for **every** `d` and **every** `n`.

## What is proved

**`finite_symmetryMatrices_box_iff`** — at every non-zero mass,
`(symmetryMatrices (boxGraph d n) mass).Finite` **if and only if** `d ≤ 1 ∨ n ≤ 1`. The four
trivial corners are trivial for three different reasons and the proof keeps them apart:
`d = 0` makes `Site d n` a one-point type (the empty tuple); `n = 0` makes it empty as soon as
`d ≥ 1`; `n = 1` makes it a one-point type again; and `d = 1` is the LINE, which is finite for a
real reason — `FieldSimpleCriterion.eigenvalues_injective_line`, the propagator's spectrum being
simple there.

**`mk_symmetryMatrices_box_eq_continuum_iff`** — and therefore `# = 𝔠` **if and only if**
`2 ≤ d ∧ 2 ≤ n`. Nothing lies between: the two cases are complementary and exhaustive.

**`finite_symmetryMatrices_of_subsingleton`** — the general step the trivial corners use: on a
one-point or empty vertex type the symmetries are finite, at every graph and every non-zero mass,
because a function out of a subsingleton is injective and
`FieldSymmetryFinite.finite_symmetryMatrices_of_injective` does the rest. **No box appears in it.**

## What is NOT here

**NO COUNT IN THE TRIVIAL CORNERS.** `finite` is proved; the exact number is not, except on the
line, where `FieldBlockContinuum.nat_card_symmetryMatrices_line` already gives `2 ^ (k + 1)`.
`FieldSymmetryCount.card_symmetryMatrices_of_injective` would give `2 ^ |Site d n|` in each corner
and **this file does not instantiate it**, because the corners are the cases where the count is
least interesting. **Four instantiations not made on 2026-09-19, and no cost is claimed for any of
them** (`ERRATUM 246`); what stops them is that `Fintype.card (Site d n)` wants evaluating in each
corner separately, which is arithmetic this file has no use for.

**NOTHING ABOUT THE TORUS'S TRIVIAL CORNERS.** `FieldBlockContinuum.mk_symmetryMatrices_torus`
takes `1 ≤ d` and side `N + 3`, and the torus at `d = 0` or side below three is not this estate's
object (`FieldTorusRotation` says so). **Not attempted, and it is a scope statement rather than a
difficulty one.**

**NO WALL MOVES.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldBoxDichotomy

open Matrix GraphLaplacian FieldRotationCount BoxGraph Cardinal

/-! ## 1. A subsingleton vertex type has finitely many symmetries, at every graph -/

/-- **ON A ONE-POINT OR EMPTY VERTEX TYPE THE SYMMETRIES ARE FINITE**, at every graph and every
non-zero mass: a function out of a subsingleton is injective, and
`FieldSymmetryFinite.finite_iff_injective` is the criterion. -/
theorem finite_symmetryMatrices_of_subsingleton {V : Type} [Fintype V] [DecidableEq V]
    [Subsingleton V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} (hm : m ≠ 0) :
    (symmetryMatrices G m).Finite :=
  FieldSymmetryFinite.finite_symmetryMatrices_of_injective hm
    (fun _ _ _ => Subsingleton.elim _ _)

/-! ## 2. The trivial corners of the box -/

theorem subsingleton_site_of_d_eq_zero (n : ℕ) : Subsingleton (Site 0 n) :=
  ⟨fun _ _ => funext fun i => absurd i.2 (by omega)⟩

theorem subsingleton_site_of_n_le_one {d n : ℕ} (hn : n ≤ 1) : Subsingleton (Site d n) := by
  haveI : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
  exact ⟨fun a b => funext fun _ => Subsingleton.elim _ _⟩

/-! ## 3. The dichotomy -/

/-- **THE BOX IS FINITE EXACTLY WHEN A DIMENSION OR A SIDE IS TRIVIAL.** -/
theorem finite_symmetryMatrices_box_iff {d n : ℕ} {mass : ℝ} (hmass : mass ≠ 0) :
    (symmetryMatrices (boxGraph d n) mass).Finite ↔ d ≤ 1 ∨ n ≤ 1 := by
  constructor
  · intro hfin
    by_contra hcon
    rw [not_or, not_le, not_le] at hcon
    obtain ⟨hd, hn⟩ := hcon
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hmk := FieldBlockContinuum.mk_symmetryMatrices_box (d := d) (n := k) hd (by omega) hmass
    haveI := hfin.to_subtype
    have hlt : #(symmetryMatrices (boxGraph d (k + 1)) mass) < ℵ₀ :=
      Cardinal.lt_aleph0_of_finite _
    rw [hmk] at hlt
    exact absurd hlt (not_lt.2 aleph0_le_continuum)
  · rintro (hd | hn)
    · interval_cases d
      · haveI := subsingleton_site_of_d_eq_zero n
        exact finite_symmetryMatrices_of_subsingleton hmass
      · rcases Nat.eq_zero_or_pos n with rfl | hpos
        · haveI := subsingleton_site_of_n_le_one (d := 1) (n := 0) (by omega)
          exact finite_symmetryMatrices_of_subsingleton hmass
        · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          exact FieldBlockContinuum.finite_symmetryMatrices_line hmass
    · haveI := subsingleton_site_of_n_le_one (d := d) hn
      exact finite_symmetryMatrices_of_subsingleton hmass

/-- **AND THE CONTINUUM CASE IS THE COMPLEMENT**, so the two are exhaustive and exclusive. -/
theorem mk_symmetryMatrices_box_eq_continuum_iff {d n : ℕ} {mass : ℝ} (hmass : mass ≠ 0) :
    #(symmetryMatrices (boxGraph d n) mass) = 𝔠 ↔ 2 ≤ d ∧ 2 ≤ n := by
  constructor
  · intro hmk
    by_contra hcon
    rw [not_and_or, not_le, not_le] at hcon
    have hfin : (symmetryMatrices (boxGraph d n) mass).Finite := by
      refine (finite_symmetryMatrices_box_iff hmass).2 ?_
      rcases hcon with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    haveI := hfin.to_subtype
    have hlt : #(symmetryMatrices (boxGraph d n) mass) < ℵ₀ := Cardinal.lt_aleph0_of_finite _
    rw [hmk] at hlt
    exact absurd hlt (not_lt.2 aleph0_le_continuum)
  · rintro ⟨hd, hn⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact FieldBlockContinuum.mk_symmetryMatrices_box hd (by omega) hmass

end FieldBoxDichotomy
