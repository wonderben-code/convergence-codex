import LovelockInvariantSplitting

/-!
# The complement is not irreducible — the prose claim, made a theorem

`LovelockInvariantSplitting` closed with a sentence that was an assertion rather than a result:

> `Curv^⊥` is visibly not irreducible (it carries at least the totally antisymmetric part and the
> Bianchi residue as separate invariant pieces, neither of which is computed here).

**Standing orders say findings are folded back by proving more, never by softening prose**, so this
file proves it. What it proves is slightly different from what that sentence said, and the
difference is an improvement: **total antisymmetry is more than the argument needs.** Invariance
under the three-cycle on the last three slots is enough, and that is a weaker hypothesis on a larger
family.

## What is proved

* **`ip_eq_zero_of_cyc_invariant`** — an array unchanged by cycling its last three slots is
  `ip`-orthogonal to **every** algebraic curvature tensor. Three lines: such an array satisfies
  `cyc X = 3X`, `LovelockCurvProjection.ip_cyc_left` moves `cyc` across the pairing **with no
  hypothesis**, and `cyc_eq_zero_of_isAlgCurv` kills the other side;
* **`ip_eq_zero_of_fst_symm`** — and so is an array symmetric in its first pair, by
  `LovelockPairProjection.ip_sw12` against the curvature tensor's antisymmetry there. Two lines;
* `cycArr`, `symArr` and their four small facts — explicit non-zero witnesses, with `symArr`
  **not** cyclically invariant at any `n ≥ 2`;
* **`act_cyc_invariant`** — **the cyclically invariant family is `act`-stable**, by one reindexing
  of the quadruple product index;
* **`perp_not_irreducible`** — the four facts assembled: `Curv^⊥` contains a non-zero member of an
  `act`-stable family, and also a member **outside** that family. **That is a proper non-zero
  invariant subfamily, which is what "not irreducible" means**, stated without a subspace type
  because the estate has none.

## What this does and does not settle

**It settles that the fourth summand of `LovelockInvariantSplitting`'s four-way decomposition is
not irreducible**, so that decomposition is definitely not the one Schur consumes. That was said
there and is now proved.

**It says nothing about the other three summands.** In particular **the Weyl summand's
irreducibility over `ℝ` — the open question — is untouched**, and nothing here bears on it: the
argument used is that `Curv^⊥` is easy to break up, not that any summand is hard to.

**`KillsWeyl` at `n ≥ 4` is untouched and the watchlist item does not move.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.


## ⚠ "BECAUSE THE ESTATE HAS NONE" IS FALSE. Annotated 1 September 2026

Kept as written (`ERRATUM 94`, `ERRATUM 391`). `perp_not_irreducible` is stated *"without a subspace
type because the estate has none"*. **`LovelockCompleteReducibility` (2026-08-22) works with
`act`-stable submodules of four-index arrays and `LovelockWeylSubmodule` supplies one**, so the
estate has had the carrier since 22 August.

**Nothing here is restated in submodule form and this note does not claim it should be.** The
predicate form is what the four assembled facts produce and it says exactly what it says; whether
the fourth summand's reducibility is worth restating against a `Submodule` is not attempted and not
costed (`ERRATUM 194`, `ERRATUM 246`).
-/

namespace LovelockPerpPieces

open AlgebraicCurvature LovelockProjections LovelockOrthogonality LovelockPairProjection
  LovelockCurvProjection Finset

variable {n : ℕ}

/-! ## 1. Two families orthogonal to every curvature tensor -/

/-- **A CYCLICALLY INVARIANT ARRAY IS ORTHOGONAL TO EVERY CURVATURE TENSOR.** -/
theorem ip_eq_zero_of_cyc_invariant {X : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hX : ∀ a b c d, X a c d b = X a b c d) {R : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hR : IsAlgCurv R) : ip X R = 0 := by
  have hcyc : cyc X = fun a b c d => 3 * X a b c d := by
    funext a b c d
    simp only [cyc]
    have h1 := hX a b c d
    have h2 := hX a c d b
    rw [hX a b c d] at h2
    linarith
  have hz : cyc R = fun _ _ _ _ => (0 : ℝ) :=
    funext fun a => funext fun b => funext fun c => funext fun d =>
      cyc_eq_zero_of_isAlgCurv hR a b c d
  have key : ip (cyc X) R = ip X (cyc R) := ip_cyc_left X R
  rw [hcyc, hz] at key
  have hl : ip (fun a b c d => 3 * X a b c d) R = 3 * ip X R := by
    simp only [ip, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  have hr : ip X (fun _ _ _ _ => (0 : ℝ)) = 0 := by
    simp only [ip, mul_zero, Finset.sum_const_zero]
  rw [hl, hr] at key
  linarith

/-- **AND SO IS AN ARRAY SYMMETRIC IN ITS FIRST PAIR.** -/
theorem ip_eq_zero_of_fst_symm {Y : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hY : ∀ a b c d, Y b a c d = Y a b c d) {R : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hR : IsAlgCurv R) : ip Y R = 0 := by
  have hswap : ip (fun a b c d => Y b a c d) R = ip Y (fun a b c d => R b a c d) := ip_sw12 Y R
  have hl : (fun a b c d => Y b a c d) = Y := funext fun a => funext fun b => funext fun c =>
    funext fun d => hY a b c d
  have hr : (fun a b c d => R b a c d) = fun a b c d => -R a b c d :=
    funext fun a => funext fun b => funext fun c => funext fun d => by
      have := hR.antisymm_left a b c d; linarith
  rw [hl, hr] at hswap
  have hneg : ip Y (fun a b c d => -R a b c d) = -ip Y R := by
    simp only [ip, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  rw [hneg] at hswap
  linarith

/-! ## 2. Explicit witnesses -/

/-- The cyclically invariant witness. -/
def cycArr (a b c d : Fin n) : ℝ :=
  delta a b * delta c d + delta a c * delta d b + delta a d * delta b c

/-- The first-pair-symmetric witness. -/
def symArr (a b c d : Fin n) : ℝ := delta a b * delta c d

theorem cyc_invariant_cycArr (a b c d : Fin n) : cycArr a c d b = cycArr a b c d := by
  simp only [cycArr]; ring

theorem fst_symm_symArr (a b c d : Fin n) : symArr b a c d = symArr a b c d := by
  simp only [symArr]; rw [delta_symm b a]

theorem cycArr_ne_zero (hn : 0 < n) : (cycArr : Fin n → Fin n → Fin n → Fin n → ℝ)
    ≠ fun _ _ _ _ => (0 : ℝ) := by
  intro h
  have := congrFun (congrFun (congrFun (congrFun h ⟨0, hn⟩) ⟨0, hn⟩) ⟨0, hn⟩) ⟨0, hn⟩
  simp only [cycArr, delta_self] at this
  norm_num at this

theorem symArr_not_cyc_invariant (hn : 2 ≤ n) :
    ¬ ∀ a b c d : Fin n, symArr a c d b = symArr a b c d := by
  intro h
  have h0 : (0 : ℕ) < n := by omega
  have hne : (⟨0, h0⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    intro e; exact absurd (congrArg Fin.val e) (by norm_num)
  have := h ⟨0, h0⟩ ⟨0, h0⟩ ⟨1, by omega⟩ ⟨1, by omega⟩
  simp only [symArr, delta_self] at this
  rw [delta, delta, if_neg hne, if_neg (Ne.symm hne)] at this
  norm_num at this

/-- **THE CYCLICALLY INVARIANT FAMILY IS `act`-STABLE.** -/
theorem act_cyc_invariant (Q : Fin n → Fin n → ℝ) {X : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hX : ∀ a b c d, X a c d b = X a b c d) (a b c d : Fin n) :
    act Q X a c d b = act Q X a b c d := by
  simp only [act]
  refine Fintype.sum_bijective (fun p => (p.1, p.2.2.2, p.2.1, p.2.2.1))
    ⟨fun p q h => ?_, fun q => ⟨(q.1, q.2.2.1, q.2.2.2, q.2.1), rfl⟩⟩ _ _ (fun p => ?_)
  · obtain ⟨p1, p2, p3, p4⟩ := p
    obtain ⟨q1, q2, q3, q4⟩ := q
    simp only [Prod.mk.injEq] at h
    obtain ⟨e1, e2, e3, e4⟩ := h
    subst e1; subst e2; subst e3; subst e4; rfl
  · rw [hX p.1 p.2.2.2 p.2.1 p.2.2.1]
    ring

/-! ## 3. And therefore -/

/-- **THE COMPLEMENT IS NOT IRREDUCIBLE**, stated without a subspace type. -/
theorem perp_not_irreducible (hn : 2 ≤ n) :
    ∃ X Y : Fin n → Fin n → Fin n → Fin n → ℝ,
      (∀ R, IsAlgCurv R → ip X R = 0) ∧ (∀ R, IsAlgCurv R → ip Y R = 0)
      ∧ (∀ a b c d, X a c d b = X a b c d)
      ∧ X ≠ (fun _ _ _ _ => (0 : ℝ))
      ∧ ¬ (∀ a b c d, Y a c d b = Y a b c d) :=
  ⟨cycArr, symArr, fun _ hR => ip_eq_zero_of_cyc_invariant cyc_invariant_cycArr hR,
    fun _ hR => ip_eq_zero_of_fst_symm fst_symm_symArr hR,
    cyc_invariant_cycArr, cycArr_ne_zero (by omega), symArr_not_cyc_invariant hn⟩

end LovelockPerpPieces
