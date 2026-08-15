import LovelockWeylFree

/-!
# Sectional entries determine an algebraic curvature tensor

`WALLS` §W5.0 §5e now ends at one statement: whether the `O(n)`-orbit of the explicit Weyl witness
**spans** the Weyl summand. **This file builds the rung that a classical route to that statement
would stand on**, and builds only that rung — read §3 for what is still missing before it reaches
anything.

## What is proved

* `mult` — the multilinear extension of a four-index array, `Z(x,y,z,w) = ∑ xₐ y_b z_c w_d Z_abcd`,
  as a sum over the quadruple index. `mult_add_one` … `mult_add_four` are its additivity in each
  slot, and `mult_basis` evaluates it on standard basis vectors, returning the entry;
* `mult_reverse` — reversing all four slots changes nothing, because `Z_abcd = Z_dcba` follows from
  the pair symmetry and the two antisymmetries. One reindexing, by `Fintype.sum_bijective` on the
  reversal involution;
* `sec Z x y = Z(x,y,y,x)` — the sectional entry, in the estate's index convention where `ricci`
  contracts slots 1 and 4 and `constCurv i j j i = 1`;
* **`eq_zero_of_sec`** — **an algebraic curvature tensor whose sectional entries all vanish is
  zero.** Three polarisations and the Bianchi identity:
  1. expanding `sec Z (x+z) y = 0` and using `mult_reverse` gives `Z(x,y,y,z) = 0`;
  2. expanding that in the middle pair gives `Z(x,y,z,w) = −Z(x,z,y,w)` — **antisymmetry in slots
     2 and 3**, which an algebraic curvature tensor does not have for free;
  3. on standard basis vectors that is an identity between entries, and with `antisymm_left` it
     makes the first three slots alternating, so the three terms of `bianchi` are equal and
     `3·Z_abcd = 0`.

## What is NOT here, and the gap is two named things

**This is a hypothesis about ALL pairs `x, y`.** What an orthogonality condition against the orbit
of the witness would supply is the same vanishing **only for orthonormal pairs** — one pair of rows
of an orthogonal matrix at a time. Getting from there to here is elementary (scale, and use the
antisymmetry when the pair is dependent) but it is **not proved here**, and the Lean form of it
needs *extend an orthonormal pair to an orthogonal matrix*, which is a Mathlib bridge this estate
has not built.

**And the other half is not here either:** that `ip Z (act Q W) = 0` for every orthogonal `Q` is
equivalent to the sectional entries of every frame-change of `Z` vanishing. That is a computation
about `ip Y (knSquare (twoProj i j))`, and it is not in this file.

**So nothing about `KillsWeyl` follows from this file, and the watchlist item does not move.** What
this file is, is the *algebraic core* of a classical route stated and proved on its own, so that if
the two bridges above are built the route has no gap left in the middle. Recording the route
without the core would be the failure `ERRATUM 175` was written about; recording the core as if it
were the route would be worse.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockSectional

open AlgebraicCurvature Finset

variable {n : ℕ}

/-- **THE MULTILINEAR EXTENSION** of a four-index array, over the quadruple index. -/
def mult (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (x y z w : Fin n → ℝ) : ℝ :=
  ∑ p : Fin n × Fin n × Fin n × Fin n,
    x p.1 * y p.2.1 * z p.2.2.1 * w p.2.2.2 * Z p.1 p.2.1 p.2.2.1 p.2.2.2

theorem mult_add_one (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (x x' y z w : Fin n → ℝ) :
    mult Z (fun t => x t + x' t) y z w = mult Z x y z w + mult Z x' y z w := by
  simp only [mult, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem mult_add_two (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (x y y' z w : Fin n → ℝ) :
    mult Z x (fun t => y t + y' t) z w = mult Z x y z w + mult Z x y' z w := by
  simp only [mult, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem mult_add_three (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (x y z z' w : Fin n → ℝ) :
    mult Z x y (fun t => z t + z' t) w = mult Z x y z w + mult Z x y z' w := by
  simp only [mult, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem mult_add_four (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (x y z w w' : Fin n → ℝ) :
    mult Z x y z (fun t => w t + w' t) = mult Z x y z w + mult Z x y z w' := by
  simp only [mult, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- Evaluating on standard basis vectors returns the entry. -/
theorem mult_basis (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    mult Z (fun t => delta a t) (fun t => delta b t) (fun t => delta c t) (fun t => delta d t)
      = Z a b c d := by
  classical
  simp only [mult]
  rw [Finset.sum_eq_single (a, b, c, d)]
  · simp [delta_self]
  · intro p _ hp
    have : delta a p.1 * delta b p.2.1 * delta c p.2.2.1 * delta d p.2.2.2 = 0 := by
      by_cases h1 : a = p.1
      · by_cases h2 : b = p.2.1
        · by_cases h3 : c = p.2.2.1
          · by_cases h4 : d = p.2.2.2
            · exact absurd (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))).symm hp
            · simp [delta, h4]
          · simp [delta, h3]
        · simp [delta, h2]
      · simp [delta, h1]
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ (a, b, c, d)) h

/-- **REVERSING ALL FOUR SLOTS CHANGES NOTHING.** `Z_abcd = Z_dcba` is the pair symmetry followed
by both antisymmetries, and the reindexing is the reversal involution. -/
theorem mult_reverse {Z : Fin n → Fin n → Fin n → Fin n → ℝ} (hZ : IsAlgCurv Z)
    (x y z w : Fin n → ℝ) : mult Z x y z w = mult Z w z y x := by
  have hrev : ∀ a b c d : Fin n, Z d c b a = Z a b c d := by
    intro a b c d
    rw [hZ.pair_symm d c b a, hZ.antisymm_left b a d c, hZ.antisymm_right a b c d]
  have hbij : Function.Bijective
      (fun p : Fin n × Fin n × Fin n × Fin n => (p.2.2.2, p.2.2.1, p.2.1, p.1)) := by
    constructor
    · intro p q h
      simp only [Prod.mk.injEq] at h
      simp only [Prod.ext_iff]
      tauto
    · intro q
      exact ⟨(q.2.2.2, q.2.2.1, q.2.1, q.1), rfl⟩
  simp only [mult]
  refine Fintype.sum_bijective _ hbij _ _ (fun p => ?_)
  simp only [hrev]
  ring

/-- **THE SECTIONAL ENTRY**, in the estate's index convention: `ricci` contracts slots 1 and 4,
and `constCurv i j j i = 1`. -/
def sec (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (x y : Fin n → ℝ) : ℝ := mult Z x y y x

/-- **VANISHING SECTIONAL ENTRIES FORCE THE TENSOR TO VANISH.** Two polarisations produce
antisymmetry in slots 2 and 3 — which an algebraic curvature tensor does not have for free — and
that makes the first three slots alternating, so `bianchi`’s three terms are equal and each is
zero.

**The hypothesis is about ALL pairs.** Read the header: an orthogonality condition against the
witness orbit would give it only for orthonormal pairs, and that bridge is not built here. -/
theorem eq_zero_of_sec {Z : Fin n → Fin n → Fin n → Fin n → ℝ} (hZ : IsAlgCurv Z)
    (hs : ∀ x y, sec Z x y = 0) (a b c d : Fin n) : Z a b c d = 0 := by
  have step1 : ∀ x y z : Fin n → ℝ, mult Z x y y z = 0 := by
    intro x y z
    have hexp := hs (fun t => x t + z t) y
    simp only [sec] at hexp
    rw [mult_add_one, mult_add_four, mult_add_four] at hexp
    have h0x : mult Z x y y x = 0 := hs x y
    have h0z : mult Z z y y z = 0 := hs z y
    have hsym : mult Z z y y x = mult Z x y y z := mult_reverse hZ z y y x
    linarith
  have step2 : ∀ x y z w : Fin n → ℝ, mult Z x y z w = -mult Z x z y w := by
    intro x y z w
    have hexp := step1 x (fun t => y t + z t) w
    rw [mult_add_two, mult_add_three, mult_add_three] at hexp
    have h1 : mult Z x y y w = 0 := step1 x y w
    have h2 : mult Z x z z w = 0 := step1 x z w
    linarith
  have step2i : ∀ p q r s : Fin n, Z p q r s = -Z p r q s := by
    intro p q r s
    have := step2 (fun t => delta p t) (fun t => delta q t) (fun t => delta r t)
      (fun t => delta s t)
    rw [mult_basis, mult_basis] at this
    exact this
  have hcyc : ∀ p q r s : Fin n, Z q r p s = Z p q r s := by
    intro p q r s
    have h1 : Z q r p s = -Z r q p s := hZ.antisymm_left q r p s
    have h2 : Z r q p s = -Z r p q s := step2i r q p s
    have h3 : Z r p q s = -Z p r q s := hZ.antisymm_left r p q s
    have h4 : Z p r q s = -Z p q r s := step2i p r q s
    linarith
  have e1 : Z b c a d = Z a b c d := hcyc a b c d
  have e2 : Z c a b d = Z a b c d := by
    have := hcyc b c a d
    rw [e1] at this
    exact this
  have hbi := hZ.bianchi a b c d
  rw [e1, e2] at hbi
  linarith

end LovelockSectional
