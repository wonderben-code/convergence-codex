import RealDivisionPureBasis
import Mathlib.Algebra.Quaternion

/-!
# The trichotomy: the pure part has dimension `0`, `1` or `3`, so `dim D` is `1`, `2` or `4`

`RealDivisionPureBasis` proved `dim V ≤ 3` and said in its header, **as a route and not a fact**,
what excluding `dim V = 2` would take: pair a vanishing combination `α i + β j + γ k = 0` against
each of `i`, `j`, `k` in turn. **This file runs that route.** It was the shortest thing named as
open on this chain and it is the last piece of leg (c) step 2.

> **§1. What `pureForm` does to zero.** `pureForm_zero_left`, from `pureForm_smul_left` at `t = 0`.
> One line, and it is what the pairing argument needs at the other end of the equation.
>
> **§2. Independence.** `linearIndependent_triple` — a normalised orthogonal pair and its product
> are linearly independent. `Fintype.linearIndependent_iff` turns the statement into *a vanishing
> combination has vanishing coefficients*, and each coefficient falls out of pairing the
> combination against its own direction: the diagonal contributes `-1` times it and the two
> off-diagonal terms are `0`, by §1 and by `RealDivisionPureBasis` §3.
>
> **§3. The exclusion and the trichotomy.** `finrank_pure_ne_two` — if the dimension were `2` then
> a nonzero element exists, a single direction cannot span (`span_lt_top_of_card_lt_finrank`, since
> `1 < 2`), `RealDivisionPureBasis.exists_orthogonal_normalised` produces the partner, and §2 makes
> three independent vectors, so the dimension is at least `3`. **That partner lemma was written
> inline inside `finrank_pure_le_three`, and this file's first draft copied it here rather than
> moving it** — the duplicate was caught reviewing this header and the lemma now lives upstream
> where both callers see it (`ERRATUM 408`). Then `finrank_pure_eq` and
> `finrank_eq_one_two_or_four` are `omega` over that, the bound from `RealDivisionPureBasis`, and
> `RealDivisionPureSpace.finrank_eq_succ`.
>
> **§4. Sharpness.** `finrank_attained` exhibits `ℝ`, `ℂ` and `Quaternion ℝ` at `1`, `2` and `4`,
> so no case of the trichotomy is empty; `quaternion_in_trichotomy` runs §3's own theorem at the
> quaternions, which tests that the three standing instances are found there.

**WHAT THIS IS.** `dim ℝ D ∈ {1, 2, 4}` for every finite-dimensional real division algebra. Read
with `RealDivisionPureBasis`, leg (c) step 2 is finished: the watchlist item's `dim V ∈ {0, 1, 3}`
is a theorem.

**WHAT THIS IS NOT** (`ERRATUM 60`). **It still does not say `D` is `ℝ`, `ℂ` or `ℍ`.** Frobenius's
theorem is the classification, not the dimension count, and the three algebra isomorphisms — leg (c)
step 3 — are untouched here, not attempted, and not costed (`ERRATUM 194`, `ERRATUM 246`). A
`4`-dimensional real division algebra is not yet known to be `ℍ` by anything in this estate; that
is a statement about the multiplication, and every theorem in this file is about dimension.
**No published tag moves and nothing in the earlier files is restated.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RealDivisionPureDim

open RealDivisionPure RealDivisionPureAdd RealDivisionPureForm RealDivisionPureSpace
open RealDivisionFormFun RealDivisionPureBasis

variable {D : Type*} [DivisionRing D] [Algebra ℝ D] [Module.Finite ℝ D]

/-! ### §1. The form at zero -/

/-- `pureForm` vanishes on zero — `pureForm_smul_left` at `t = 0`. -/
theorem pureForm_zero_left (w : pureSubmodule D) : pureForm 0 w = 0 := by
  have h := pureForm_smul_left (0 : ℝ) w w
  simpa using h

/-! ### §2. A normalised orthogonal pair and its product are independent -/

/-- **Independence.** Each coefficient falls out of pairing the vanishing combination against its
own direction: the diagonal contributes `-1` times it, the two off-diagonal terms vanish. -/
theorem linearIndependent_triple {i j k : pureSubmodule D} (hi : pureSq i = -1)
    (hj : pureSq j = -1) (hij : pureForm i j = 0) (hk : (k : D) = (i : D) * (j : D)) :
    LinearIndependent ℝ ![i, j, k] := by
  have hji : pureForm j i = 0 := by rw [pureForm_comm]; exact hij
  have hk1 : pureSq k = -1 := prod_pureSq hi hj hij hk
  have hki : pureForm k i = 0 := prod_orthogonal_left hij hk
  have hkj : pureForm k j = 0 := prod_orthogonal_right hij hk
  have hik : pureForm i k = 0 := by rw [pureForm_comm]; exact hki
  have hjk : pureForm j k = 0 := by rw [pureForm_comm]; exact hkj
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum : g 0 • i + g 1 • j + g 2 • k = 0 := by
    rw [Fin.sum_univ_three] at hg
    simpa using hg
  have hpair : ∀ w : pureSubmodule D,
      g 0 * pureForm i w + g 1 * pureForm j w + g 2 * pureForm k w = 0 := by
    intro w
    have h := congrArg (fun x => pureForm x w) hsum
    simp only [pureForm_add_left, pureForm_smul_left, pureForm_zero_left] at h
    exact h
  have h0 : g 0 = 0 := by
    have h := hpair i
    rw [pureForm_self, hi, hji, hki] at h
    linarith
  have h1 : g 1 = 0 := by
    have h := hpair j
    rw [pureForm_self, hj, hij, hkj] at h
    linarith
  have h2 : g 2 = 0 := by
    have h := hpair k
    rw [pureForm_self, hk1, hik, hjk] at h
    linarith
  intro n
  fin_cases n <;> assumption

/-! ### §3. Dimension two is impossible, and the trichotomy -/

/-- **The exclusion.** A two-dimensional pure part would carry a normalised element, a direction
outside its span, and therefore three independent vectors. -/
theorem finrank_pure_ne_two : Module.finrank ℝ (pureSubmodule D) ≠ 2 := by
  intro h2
  haveI : Nontrivial (pureSubmodule D) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [h2]; norm_num)
  obtain ⟨u, hu⟩ := exists_ne (0 : pureSubmodule D)
  obtain ⟨t, _, hti⟩ := exists_smul_sq_neg_one (mem_pureSubmodule.mp u.2)
    (fun hc => hu (Submodule.coe_eq_zero.mp hc))
  have hi : pureSq (t • u) = -1 := (pureSq_eq (D := D) (u := t • u) hti).symm
  have hlt : Submodule.span ℝ ({t • u} : Set (pureSubmodule D)) < ⊤ := by
    refine span_lt_top_of_card_lt_finrank ?_
    simp [h2]
  obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt hlt
  obtain ⟨j, hj, hij⟩ := exists_orthogonal_normalised hi hv
  obtain ⟨k, hk⟩ := exists_prod hij
  have hind := linearIndependent_triple hi hj hij hk
  have hcard := hind.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  omega

/-- **The trichotomy for the pure part** — the watchlist item's `dim V ∈ {0, 1, 3}`. -/
theorem finrank_pure_eq : Module.finrank ℝ (pureSubmodule D) = 0 ∨
    Module.finrank ℝ (pureSubmodule D) = 1 ∨ Module.finrank ℝ (pureSubmodule D) = 3 := by
  have hle := finrank_pure_le_three (D := D)
  have hne := finrank_pure_ne_two (D := D)
  omega

/-- **The trichotomy for `D`.** Every finite-dimensional real division algebra has dimension `1`,
`2` or `4`. Which algebra it is at each dimension is not decided here; see the header. -/
theorem finrank_eq_one_two_or_four :
    Module.finrank ℝ D = 1 ∨ Module.finrank ℝ D = 2 ∨ Module.finrank ℝ D = 4 := by
  have hsucc := finrank_eq_succ (D := D)
  have h := finrank_pure_eq (D := D)
  omega

/-! ### §4. All three dimensions are attained, and the hypotheses hold at the hardest case -/

/-- **The trichotomy is sharp: none of its three cases is empty.** A theorem permitting dimensions
that nothing realises would be weaker than it looks, so the three witnesses are exhibited from
Mathlib's own dimension lemmas. -/
theorem finrank_attained : Module.finrank ℝ ℝ = 1 ∧ Module.finrank ℝ ℂ = 2 ∧
    Module.finrank ℝ (Quaternion ℝ) = 4 :=
  ⟨Module.finrank_self ℝ, Complex.finrank_real_complex, Quaternion.finrank_eq_four⟩

/-- **And the standing hypotheses are satisfiable at the hardest of the three.** This is §4's own
theorem instantiated at the quaternions, so it is a check that `DivisionRing`, `Algebra ℝ` and
`Module.Finite ℝ` are all found there — not a restatement of `finrank_attained`, which never
mentions the trichotomy. -/
theorem quaternion_in_trichotomy : Module.finrank ℝ (Quaternion ℝ) = 1 ∨
    Module.finrank ℝ (Quaternion ℝ) = 2 ∨ Module.finrank ℝ (Quaternion ℝ) = 4 :=
  finrank_eq_one_two_or_four

end RealDivisionPureDim
