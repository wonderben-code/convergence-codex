import LovelockSectional

/-!
# The frame change is evaluation on rows, and the witness pairing reads off one entry

`WALLS` §W5.0 §5g names two bridges the sectional route still needs. **This file builds the
computational half of the second one and nothing else.**

## What is proved

* **`act_eq_mult`** — `act Q R a b c d` **is** `R` evaluated multilinearly on rows `a, b, c, d` of
  `Q`. `rfl`: `act` and `LovelockSectional.mult` are the same sum, which is worth stating rather
  than leaving as a coincidence of definitions;
* **`sec_rows`** — hence `sec Z (row i) (row j) = act Q Z i j j i`. Also `rfl`. **This is the
  identification that makes the sectional hypothesis a statement about frame changes**;
* `sum_delta_quad` — a four-fold delta contraction reads off one entry;
* **`ip_knSquare_twoProj`** — `⟨Y, knSquare (twoProj i j)⟩ = 4·Y i j j i` for every algebraic
  curvature tensor `Y`. Eight delta terms, four of which cancel in pairs; the remaining four are
  equal after `pair_symm` and `antisymm_right`. **So pairing against the witness's underlying square
  reads off exactly one sectional entry.**

## What is still missing on this bridge, and on the other

**On this bridge:** the statement above is about `knSquare (twoProj i j)`, not about
`weylPart (knSquare (twoProj i j))`. Replacing one by the other needs `⟨Y, ricciPart X⟩ = 0` and
`⟨Y, scalPart X⟩ = 0` for Ricci-flat `Y` — which `LovelockOrthogonality.ip_eq_zero_of_ricci_eq_zero`
supplies at the level of `h ⊙ δ` — plus linearity of `ip` in its second argument. **That assembly is
not in this file.**

**On the other bridge, nothing has changed:** getting from orthonormal pairs to all pairs still
needs *extend an orthonormal pair to an orthogonal matrix*, and this estate still has no such bridge
to Mathlib.

**So `KillsWeyl` at `n ≥ 4` is untouched and the watchlist item does not move.** §5g is a candidate
route with named gaps; this file shortens one of them and leaves it open.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockSectionalWitness

open AlgebraicCurvature LovelockProjections LovelockOrthogonality LovelockEquivariance
  WeylNonzeroGeneral LovelockSectional Finset

variable {n : ℕ} {Q : Fin n → Fin n → ℝ}

/-- **A FRAME CHANGE IS MULTILINEAR EVALUATION ON THE ROWS OF `Q`.** `rfl` — `act` and `mult` are
the same sum over the quadruple index. -/
theorem act_eq_mult (R : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    act Q R a b c d
      = mult R (fun t => Q a t) (fun t => Q b t) (fun t => Q c t) (fun t => Q d t) := rfl

/-- **AND SO THE SECTIONAL ENTRY OF A PAIR OF ROWS IS AN ENTRY OF THE MOVED TENSOR.** Also `rfl`.
This is what turns `LovelockSectional`’s hypothesis into a statement about frame changes. -/
theorem sec_rows (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (i j : Fin n) :
    sec Z (fun t => Q i t) (fun t => Q j t) = act Q Z i j j i := rfl

/-- A four-fold delta contraction reads off one entry. -/
theorem sum_delta_quad (Y : Fin n → Fin n → Fin n → Fin n → ℝ) (p q r s : Fin n) :
    ∑ a, ∑ b, ∑ c, ∑ d, (delta a p * delta b q * delta c r * delta d s) * Y a b c d
      = Y p q r s := by
  have h1 : ∀ a b c : Fin n,
      ∑ d, (delta a p * delta b q * delta c r * delta d s) * Y a b c d
        = (delta a p * delta b q * delta c r) * Y a b c s := by
    intro a b c
    rw [← sum_delta_left s fun d => (delta a p * delta b q * delta c r) * Y a b c d]
    exact Finset.sum_congr rfl fun d _ => by ring
  have h2 : ∀ a b : Fin n, ∑ c, (delta a p * delta b q * delta c r) * Y a b c s
      = (delta a p * delta b q) * Y a b r s := by
    intro a b
    rw [← sum_delta_left r fun c => (delta a p * delta b q) * Y a b c s]
    exact Finset.sum_congr rfl fun c _ => by ring
  have h3 : ∀ a : Fin n, ∑ b, (delta a p * delta b q) * Y a b r s
      = (delta a p) * Y a q r s := by
    intro a
    rw [← sum_delta_left q fun b => (delta a p) * Y a b r s]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => h1 a b c,
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => h2 a b,
    Finset.sum_congr rfl fun a _ => h3 a,
    ← sum_delta_left p fun a => Y a q r s]

/-- **PAIRING AGAINST THE WITNESS SQUARE READS OFF ONE SECTIONAL ENTRY.** Eight delta terms; the
first and fifth cancel, so do the fourth and eighth, and the remaining four are equal after
`pair_symm` and `antisymm_right`. Read the header for what still stands between this and the Weyl
part of the same square. -/
theorem ip_knSquare_twoProj {Y : Fin n → Fin n → Fin n → Fin n → ℝ} (hY : IsAlgCurv Y)
    (i j : Fin n) : ip Y (knSquare (twoProj i j)) = 4 * Y i j j i := by
  have hterm : ∀ a b c d : Fin n, Y a b c d * knSquare (twoProj i j) a b c d
      = (delta a i * delta b i * delta c i * delta d i) * Y a b c d
        + (delta a i * delta b j * delta c j * delta d i) * Y a b c d
        + (delta a j * delta b i * delta c i * delta d j) * Y a b c d
        + (delta a j * delta b j * delta c j * delta d j) * Y a b c d
        - (delta a i * delta b i * delta c i * delta d i) * Y a b c d
        - (delta a i * delta b j * delta c i * delta d j) * Y a b c d
        - (delta a j * delta b i * delta c j * delta d i) * Y a b c d
        - (delta a j * delta b j * delta c j * delta d j) * Y a b c d := by
    intro a b c d; simp only [knSquare, twoProj]; ring
  simp only [ip]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => hterm a b c d]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_delta_quad]
  have e1 : Y j i i j = Y i j j i := hY.pair_symm j i i j
  have e2 : Y i j i j = -Y i j j i := by
    have h := hY.antisymm_right i j j i
    linarith
  have e3 : Y j i j i = -Y i j j i := by
    have h := hY.antisymm_right j i i j
    rw [e1] at h
    linarith
  rw [e1, e2, e3]
  ring

end LovelockSectionalWitness
