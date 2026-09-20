/-
  HyperchargeInPatiSalam: the hypercharge is not a fourth factor — it is an element of the
  three, and that corrects the register entry that asked for a fourth

  SPINE LINK L17. `UNLOCK_WATCHLIST` 260, written by me after `PatiSalamOrthogonal` proved
  that the trace form of the chiral 16 is the orthogonal direct sum of the `sl₄`, `sl₂_L` and
  `sl₂_R` forms, asked for *"a `psRepU1 : ℂ →ₗ⁅ℂ⁆ Matrix PSIndex PSIndex ℂ` whose image is
  `WeinbergIndex.Y` up to normalisation, its mixed trace products against `su4Rep`, `su2LRep`,
  `su2RRep`, and then the four-factor version of `psRep_trace_orthogonal_sum`."*

  **THERE IS NO FOURTH FACTOR.** Reading `WeinbergIndex`'s own definitions settles it:

  > `yval = t3Rval + blval / 2`, with `t3Rval = Sum.elim 0 (t₃ ∘ snd)` and
  > `blval = Sum.elim (b₄ ∘ fst) (-(b₄ ∘ fst))`

  and those two are **exactly** the diagonals of `su2RRep T₃` and `su4Rep B₄`. So

  > **`Y = su2RRep T₃ + ½ · su4Rep B₄ = psRep (½ B₄, 0, T₃)`**

  — `Y_eq_psRep` below. The hypercharge already lies in the image of the Pati–Salam algebra,
  which is the whole content of the embedding `SMInPatiSalam.smToPS` and the reason
  `su(4) × su(2)_L × su(2)_R` has rank 5 while the Standard Model has rank 4. **Entry 260
  asked for an object that cannot exist, and it did so because it read the `u(1)` off the
  Standard-Model side of the embedding instead of off the Pati–Salam side.** Filed as
  `ERRATUM 569` and corrected in the entry.
  ⚠ 20 September 2026 (hardening unit 190): *the whole content of the embedding `smToPS`* was
  too much: `Y = (½ B₄, 0, T₃)` is NOT in the range of `smToPS`
  (`PatiSalamLieModule.hypercharge_not_mem_range_smToPS`); it is in the range of the
  hypercharge-normalised `smToPSY` (`smToPSY_u1_eq_hypercharge`). `ERRATUM 679`.

  WHAT THAT BUYS, AND IT IS NOT THE NUMBERS. `WeinbergIndex` already proves
  `trace_Y_sq = 10/3`, `trace_T3L_sq = 2`, `trace_T3L_Y = 0` and
  `coupling_ratio_three_fifths = 3/5`, each by a direct computation over the sixteen indices
  in `ℚ`. This file does **not** improve those numbers. What it adds is that the same numbers
  fall out of the INVARIANT FORM:

  * `trace_T3L_sq_via_form` — `4 · Tr(T₃²) = 2`;
  * `trace_Y_sq_via_form` — `4 · Tr((½B₄)²) + 4 · Tr(T₃²) = 10/3`;
  * `trace_T3L_Y_via_form` — `0`, because the two elements sit in complementary factors;

  all three off `PatiSalamOrthogonal.psRep_trace_orthogonal_sum`, whose hypotheses `Tr X = 0`
  are supplied by `trace_B4` and `trace_T3` — **and those are the physical tracelessness of
  `B−L` and of `T₃`, so the hypothesis of the form theorem is exactly the statement that these
  generators are in `sl`, not `gl`.** Two independent derivations of the same three numbers,
  which `two_routes_agree` states as one theorem. That is cross-validation of a direct
  computation, not duplication of it.

  AND IT LOCATES `ASSUMPTIONS_LEDGER` 57 MORE PRECISELY THAN BEFORE. The coupling matching is
  the assumption that `g'²/g² = Tr(T₃L²)/Tr(Y²)` at unification. Before this file that could
  be described as *"one invariant form must normalise a generator the estate has no algebra
  for"*. It cannot be described that way any more: `Y` is an element of the algebra the form
  is already defined on, so the matching is a statement about **the normalisation of one
  particular element of the existing product** — and `Y`'s coefficients `(½, 0, 1)` in
  `(B₄, ·, T₃)` are a CHOICE, not forced by anything here. **That is a sharper form of the
  same open question, and it remains open.**

  WHAT IS **NOT** CLAIMED.
  * **The coupling matching itself** — `ASSUMPTIONS_LEDGER` 57, a `DECISIONS NEEDED` entry,
    untouched. Nothing here derives `sin²θ_W`; the ratio `3/5` is a trace ratio and the
    physics input is that it equals a ratio of couplings.
  * **`Y`'s normalisation is not derived.** That `Y = T₃R + (B−L)/2` rather than any other
    combination is the standard convention and is an input; what is proved is that *given*
    that convention, `Y` is in the image and the form computes its norm.
  * **No `u(1)` Lie algebra is built, and none is needed.** Entry 260 wanted one; the right
    object turned out to be an element, not a factor. `SMInPatiSalam.SM`'s bare `ℂ` slot is
    untouched and no `psRepU1` exists anywhere — by query, still.
  * **No `so(10)`.** Inside it the normalisation would be forced; it is still absent from the
    estate, as `PatiSalamOnSixteen` and `PatiSalamTraceForm` both record.
  * **The chiral content** is L12's postulate (`ASSUMPTIONS_LEDGER` 5, 34), and the charge
    assignments are conventions.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import PatiSalamOrthogonal

namespace HyperchargeInPatiSalam

open Matrix WeinbergIndex SU4OnSixteen PatiSalamOnSixteen PatiSalamOrthogonal

noncomputable section

/-! ## 1. The two generators, over `ℂ` -/

/-- `B−L` on the Pati–Salam 4, as a complex matrix: `(1/3, 1/3, 1/3, -1)`. -/
def B4 : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal fun a => ((b4 a : ℚ) : ℂ)

/-- `T₃` on the doublet, as a complex matrix: `(1/2, -1/2)`. -/
def T3 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal fun i => ((t3 i : ℚ) : ℂ)

/-- **`B−L` is traceless**, which is what lets the orthogonal-sum theorem apply to it: the
hypothesis `Tr X = 0` there is exactly the statement that `X` lies in `sl₄` and not `gl₄`. -/
theorem trace_B4 : B4.trace = 0 := by
  rw [B4, Matrix.trace_diagonal, Fin.sum_univ_four]
  norm_num [b4]

/-- And so is `T₃`. -/
theorem trace_T3 : T3.trace = 0 := by
  rw [T3, Matrix.trace_diagonal, Fin.sum_univ_two]
  norm_num [t3]

theorem trace_B4_sq : (B4 * B4).trace = 4 / 3 := by
  rw [B4, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Fin.sum_univ_four]
  norm_num [b4]

theorem trace_T3_sq : (T3 * T3).trace = 1 / 2 := by
  rw [T3, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Fin.sum_univ_two]
  norm_num [t3]

/-! ## 2. The hypercharge, and the fact there is no fourth factor -/

/-- `WeinbergIndex.Y` over `ℂ`. -/
def Yc : Matrix PSIndex PSIndex ℂ := Matrix.diagonal fun s => ((yval s : ℚ) : ℂ)

/-- `WeinbergIndex.T3L` over `ℂ`. -/
def T3Lc : Matrix PSIndex PSIndex ℂ := Matrix.diagonal fun s => ((t3Lval s : ℚ) : ℂ)

/-- **THE THEOREM, and it says entry 260 asked for an object that cannot exist.** The
hypercharge is already an element of the Pati–Salam algebra's image on the 16 — the `T₃R`
part in `sl₂_R` and the `(B−L)/2` part in `sl₄` — so there is no fourth factor to build a
four-factor orthogonal sum out of. This is the content of the embedding
`SMInPatiSalam.smToPS`, and the reason the Pati–Salam algebra has rank 5 while the Standard
Model has rank 4.
⚠ 20 September 2026 (unit 190): read *`smToPSY`* — `smToPS`'s `u(1)` line misses `Y`
(`PatiSalamLieModule.hypercharge_not_mem_range_smToPS`, `ERRATUM 679`). -/
theorem Y_eq_psRep : Yc = psRep (((1 : ℂ) / 2) • B4, 0, T3) := by
  ext s t
  cases s with
  | inl p => cases t with
    | inl q =>
        simp [Yc, psRep, su4Rep, su2LRep, su2RRep, B4, T3, yval, t3Rval, blval,
          Matrix.diagonal_apply, kroneckerMap_apply, Prod.ext_iff, and_comm]
        split_ifs <;> simp_all [Matrix.one_apply]
        all_goals ring
    | inr q => simp [Yc, psRep, su4Rep, su2LRep, su2RRep]
  | inr p => cases t with
    | inl q => simp [Yc, psRep, su4Rep, su2LRep, su2RRep]
    | inr q =>
        simp [Yc, psRep, su4Rep, su2LRep, su2RRep, B4, T3, yval, t3Rval, blval,
          Matrix.diagonal_apply, kroneckerMap_apply, Prod.ext_iff, and_comm]
        split_ifs <;> simp_all [Matrix.one_apply]
        all_goals ring

/-- `T₃L` sits in the `sl₂_L` factor alone. -/
theorem T3L_eq_psRep : T3Lc = psRep (0, T3, 0) := by
  ext s t
  cases s with
  | inl p => cases t with
    | inl q =>
        simp [T3Lc, psRep, su4Rep, su2LRep, su2RRep, T3, t3Lval,
          Matrix.diagonal_apply, kroneckerMap_apply, Prod.ext_iff, and_comm]
        split_ifs <;> simp_all [Matrix.one_apply]
    | inr q => simp [T3Lc, psRep, su4Rep, su2LRep, su2RRep]
  | inr p => cases t with
    | inl q => simp [T3Lc, psRep, su4Rep, su2LRep, su2RRep]
    | inr q => simp [T3Lc, psRep, su4Rep, su2LRep, su2RRep, t3Lval, Matrix.diagonal_apply]

/-! ## 3. The three numbers, derived from the invariant form -/

/-- `½ B₄` is traceless, which is the hypothesis `psRep_trace_orthogonal_sum` needs. -/
theorem trace_half_B4 : (((1 : ℂ) / 2) • B4).trace = 0 := by
  rw [Matrix.trace_smul, trace_B4, smul_zero]

/-- **`Tr₁₆(T₃L²) = 2`, off the orthogonal-sum theorem** rather than off a computation over the
sixteen indices. `WeinbergIndex.trace_T3L_sq` proves the same number directly in `ℚ`; this is
a second and independent derivation. -/
theorem trace_T3L_sq_via_form : (T3Lc * T3Lc).trace = 2 := by
  rw [T3L_eq_psRep, psRep_trace_orthogonal_sum 0 0 T3 T3 0 0 (Matrix.trace_zero _ _)
    (Matrix.trace_zero _ _), trace_T3_sq]
  simp
  norm_num

/-- **`Tr₁₆(Y²) = 10/3`, off the orthogonal-sum theorem.** The two contributions are
`4 · Tr((½B₄)²) = 4/3` from `sl₄` and `4 · Tr(T₃²) = 2` from `sl₂_R`, and they add rather than
interfere **because the form is an orthogonal direct sum** — which is exactly what
`PatiSalamOrthogonal` proved and what makes this derivation possible at all. -/
theorem trace_Y_sq_via_form : (Yc * Yc).trace = 10 / 3 := by
  rw [Y_eq_psRep, psRep_trace_orthogonal_sum _ _ 0 0 T3 T3 trace_half_B4 trace_half_B4]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, trace_B4_sq,
    trace_T3_sq]
  simp only [Matrix.mul_zero, Matrix.trace_zero, smul_eq_mul]
  ring

/-- **`Tr₁₆(T₃L · Y) = 0`, and the reason is structural**: `T₃L` lives in `sl₂_L` while `Y`
lives in `sl₄ ⊕ sl₂_R`, and the form has no cross terms between distinct factors once the
`sl₄` entries are traceless. `WeinbergIndex.trace_T3L_Y` proves it by computation. -/
theorem trace_T3L_Y_via_form : (T3Lc * Yc).trace = 0 := by
  rw [T3L_eq_psRep, Y_eq_psRep,
    psRep_trace_orthogonal_sum 0 _ T3 0 0 T3 (Matrix.trace_zero _ _) trace_half_B4]
  simp

/-- **The ratio, from the form.** `WeinbergIndex.coupling_ratio_three_fifths` has the same
number in `ℚ`; this is the same statement with the trace form doing the work. -/
theorem weinberg_ratio_via_form : (T3Lc * T3Lc).trace / (Yc * Yc).trace = 3 / 5 := by
  rw [trace_T3L_sq_via_form, trace_Y_sq_via_form]
  norm_num

/-! ## 4. The two routes agree -/

/-- Casting a rational matrix product's trace into `ℂ` commutes with taking the trace. -/
theorem trace_cast (M N : Matrix PSIndex PSIndex ℚ) :
    ((M.map (fun q => ((q : ℚ) : ℂ))) * (N.map (fun q => ((q : ℚ) : ℂ)))).trace
      = (((M * N).trace : ℚ) : ℂ) := by
  have hM : M.map (fun q => ((q : ℚ) : ℂ)) = M.map (Rat.castHom ℂ) := rfl
  have hN : N.map (fun q => ((q : ℚ) : ℂ)) = N.map (Rat.castHom ℂ) := rfl
  rw [hM, hN, ← Matrix.map_mul, Matrix.trace]
  simp [Matrix.trace, Matrix.diag, Matrix.map_apply, Rat.castHom]

theorem Yc_eq_map : Yc = WeinbergIndex.Y.map (fun q => ((q : ℚ) : ℂ)) := by
  ext s t
  by_cases h : s = t
  · subst h; simp [Yc, WeinbergIndex.Y, Matrix.map_apply]
  · simp [Yc, WeinbergIndex.Y, Matrix.map_apply, Matrix.diagonal_apply_ne _ h]

theorem T3Lc_eq_map : T3Lc = WeinbergIndex.T3L.map (fun q => ((q : ℚ) : ℂ)) := by
  ext s t
  by_cases h : s = t
  · subst h; simp [T3Lc, WeinbergIndex.T3L, Matrix.map_apply]
  · simp [T3Lc, WeinbergIndex.T3L, Matrix.map_apply, Matrix.diagonal_apply_ne _ h]

/-- **THE CROSS-VALIDATION.** The three numbers this file derives from the invariant form are
the `ℂ`-images of the three `WeinbergIndex` proves by direct computation over the sixteen
indices. Two independent routes to the same quantities — which is worth having as a theorem
rather than as a coincidence of numerals, because `ERRATUM 557` was a bridge theorem in this
same area that was **vacuous** and stood for a day. -/
theorem two_routes_agree :
    (T3Lc * T3Lc).trace = (((WeinbergIndex.T3L * WeinbergIndex.T3L).trace : ℚ) : ℂ)
      ∧ (Yc * Yc).trace = (((WeinbergIndex.Y * WeinbergIndex.Y).trace : ℚ) : ℂ)
      ∧ (T3Lc * Yc).trace = (((WeinbergIndex.T3L * WeinbergIndex.Y).trace : ℚ) : ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [T3Lc_eq_map, trace_cast]
  · rw [Yc_eq_map, trace_cast]
  · rw [T3Lc_eq_map, Yc_eq_map, trace_cast]

end

end HyperchargeInPatiSalam
