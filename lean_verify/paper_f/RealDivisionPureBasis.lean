import RealDivisionFormFun

/-!
# The basis argument: three pure directions span, so a real division algebra has dimension ≤ 4

`RealDivisionFormFun` built the dictionary — *orthogonal* for `pureForm` is *anticommuting* — and
closed by naming what leg (c) still needed as **one thing**: bilinearity of the form, an orthogonal
basis, and the dimension count. **This file is that one thing.** It ends with a statement about `D`
itself rather than about the pure part.

> **§1. Bilinearity.** `pureForm_add_left` and `pureForm_smul_left` share one shape: `anticomm_eq`
> turns a value of the form into a scalar, the corresponding identity in `D` is noncommutative ring
> arithmetic, and `smul_one_inj` reads the scalar back. `pureForm_add_right` and
> `pureForm_smul_right` are those two with `pureForm_comm` on either side, and have no content of
> their own. **The form is bilinear and symmetric — as four theorems and `pureForm_comm`, NOT as a
> `LinearMap.BilinForm`**: §4 consumes the theorems and nothing in this estate consumes a bundled
> form, which is the same refusal the two files before this one made about `Submodule`.
>
> **§2. Orthogonalisation.** `pureForm_orthogonalise` — against a `u` with `pureSq u = -1`, the
> element `v + pureForm v u • u` is orthogonal to `u`. One rewrite and a `ring`, once §1 exists.
> **The sign is not a slip**: the form is NEGATIVE definite, so Gram–Schmidt adds here where over
> an inner product space it would subtract.
>
> **§3. The product of an orthogonal pair.** `exists_prod` (`ij` is pure), `prod_pureSq`
> (`(ij)² = -1`), `prod_orthogonal_left` and `prod_orthogonal_right` (`ij` is orthogonal to both).
> Each is an earlier file's theorem read through the dictionary:
> `RealDivisionPureForm.isPure_mul_of_anticomm`, `RealDivisionPureForm.sq_mul_of_anticomm`, and
> `RealDivisionAnticomm.anticomm_mul_left` / `_right`.
>
> **§4. The span.** `span_eq_top_of_orthogonal_pair` — for a normalised orthogonal pair `i`, `j`
> and any `k` with `(k : D) = i * j`, the three span the whole pure part. The proof is the reason
> the form had to become a function: for any `l`, the element `l + ⟨l,i⟩i + ⟨l,j⟩j + ⟨l,k⟩k` is
> orthogonal to all three by §1 and §3, hence anticommutes with all three by the dictionary, hence
> is **zero** by `RealDivisionAnticomm.eq_zero_of_anticomm_three`. **No Gram–Schmidt induction, no
> `InnerProductSpace` instance and no `QuadraticForm`**: the orthogonal complement of the triple is
> written down in closed form and shown to vanish.
>
> **§5. The dimension.** `finrank_pure_le_three` builds the pair when one exists and disposes of the
> two degenerate cases directly, so it carries **no hypothesis beyond the standing three**; then
> `finrank_le_four` is `RealDivisionPureSpace.finrank_eq_succ` applied to it.
>
> **§6. Two checks against `ℂ`**, because a theorem quantified over an empty class of algebras
> compiles exactly as this one does. `isPure_I` tests the definition — `Complex.I` squares to `-1`,
> so it is pure — and `finrank_complex_le_four` exhibits an algebra satisfying all three standing
> hypotheses, where `Complex.finrank_real_complex` puts the answer at `2`.

**WHAT THIS IS.** `Module.finrank ℝ D ≤ 4` for every finite-dimensional real division algebra. The
watchlist item's `dim V ∈ {0, 1, 3}` is `dim D ∈ {1, 2, 4}`, and this is the upper bound half of it.
**IT DISCHARGES TWO OF THE THREE THINGS `RealDivisionPureSpace`'s HEADER NAMED** as leg (c)'s
remaining work — *one orthogonalisation step* (§2) and *`dim V ≤ 3`* (§4-§5). That file is left as
written; supersession is recorded forward, here, and not by editing what was true when it was
written (`ERRATUM 393`).

**WHAT THIS IS NOT** (`ERRATUM 60`). It does not say `D` is `ℝ`, `ℂ` or `ℍ`: three algebra
isomorphisms are the third thing that header named, they are not attempted here, and their cost is
not claimed (`ERRATUM 194`, `ERRATUM 246`). **It also does not exclude `dim D = 3`**, so
`dim D ∈ {1, 2, 4}` must not be read off this file. **A ROUTE FOR THAT, AND IT IS A ROUTE AND NOT A
FACT** (`ERRATUM 204`): pairing a vanishing combination `α i + β j + γ k = 0` against each of `i`,
`j`, `k` should make `α`, `β`, `γ` vanish in turn by §1 and §3, so a normalised orthogonal pair
would force `dim V ≥ 3` and, with §5, `= 3`. **Not attempted, not costed** (`ERRATUM 194`,
`ERRATUM 246`). It is left to the file that needs it, because `≤` is what a dimension count proves
and `=` is a separate statement. **No published tag moves and nothing in the earlier files is
restated.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RealDivisionPureBasis

open RealDivisionPure RealDivisionPureAdd RealDivisionPureForm RealDivisionPureSpace
open RealDivisionFormFun

variable {D : Type*} [DivisionRing D] [Algebra ℝ D] [Module.Finite ℝ D]

/-! ### §1. The form is bilinear -/

/-- Additivity in the first slot. -/
theorem pureForm_add_left (u v w : pureSubmodule D) :
    pureForm (u + v) w = pureForm u w + pureForm v w := by
  have hsum : ((u + v : pureSubmodule D) : D) = (u : D) + (v : D) := rfl
  have hexp : (2 * pureForm (u + v) w) • (1 : D)
      = (2 * pureForm u w + 2 * pureForm v w) • (1 : D) := by
    rw [← anticomm_eq (u + v) w, hsum]
    have hring : ((u : D) + (v : D)) * (w : D) + (w : D) * ((u : D) + (v : D))
        = ((u : D) * (w : D) + (w : D) * (u : D))
          + ((v : D) * (w : D) + (w : D) * (v : D)) := by noncomm_ring
    rw [hring, anticomm_eq u w, anticomm_eq v w]
    module
  have := smul_one_inj (D := D) hexp
  linarith

/-- Homogeneity in the first slot. -/
theorem pureForm_smul_left (t : ℝ) (u v : pureSubmodule D) :
    pureForm (t • u) v = t * pureForm u v := by
  have hsmul : ((t • u : pureSubmodule D) : D) = t • (u : D) := rfl
  have hexp : (2 * pureForm (t • u) v) • (1 : D) = (t * (2 * pureForm u v)) • (1 : D) := by
    rw [← anticomm_eq (t • u) v, hsmul]
    have hring : (t • (u : D)) * (v : D) + (v : D) * (t • (u : D))
        = t • ((u : D) * (v : D) + (v : D) * (u : D)) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_add]
    rw [hring, anticomm_eq u v, smul_smul]
  have := smul_one_inj (D := D) hexp
  linarith

/-- Additivity in the second slot, by symmetry. -/
theorem pureForm_add_right (u v w : pureSubmodule D) :
    pureForm u (v + w) = pureForm u v + pureForm u w := by
  rw [pureForm_comm, pureForm_add_left, pureForm_comm v u, pureForm_comm w u]

/-- Homogeneity in the second slot, by symmetry. -/
theorem pureForm_smul_right (t : ℝ) (u v : pureSubmodule D) :
    pureForm u (t • v) = t * pureForm u v := by
  rw [pureForm_comm, pureForm_smul_left, pureForm_comm v u]

/-! ### §2. Zero, non-vanishing, and one Gram–Schmidt step -/

/-- The zero element squares to zero — the partner `pureSq_neg_of_ne_zero` needs. -/
theorem pureSq_zero : pureSq (0 : pureSubmodule D) = 0 := by
  have h : ((0 : pureSubmodule D) : D) * ((0 : pureSubmodule D) : D) = (0 : ℝ) • (1 : D) := by
    simp
  exact (pureSq_eq h).symm

/-- A strictly negative square forces a nonzero element, in the bundled part … -/
theorem ne_zero_of_pureSq_neg {u : pureSubmodule D} (h : pureSq u < 0) : u ≠ 0 := by
  intro h0
  rw [h0, pureSq_zero] at h
  exact lt_irrefl 0 h

/-- … and in `D`, which is the form `mul_ne_zero` wants. -/
theorem coe_ne_zero_of_pureSq_neg {u : pureSubmodule D} (h : pureSq u < 0) : (u : D) ≠ 0 :=
  fun hc => ne_zero_of_pureSq_neg h (Submodule.coe_eq_zero.mp hc)

/-- **One Gram–Schmidt step.** Against a normalised `u`, this element is orthogonal to `u`.
The `+` is not a slip: `pureForm u u = -1`, so the projection removed is a *negative* multiple. -/
theorem pureForm_orthogonalise {u : pureSubmodule D} (hu : pureSq u = -1) (v : pureSubmodule D) :
    pureForm (v + pureForm v u • u) u = 0 := by
  rw [pureForm_add_left, pureForm_smul_left, pureForm_self, hu]
  ring

/-! ### §3. The product of a normalised orthogonal pair -/

/-- The product of two orthogonal pure elements is pure — the bundled form of
`RealDivisionPureForm.isPure_mul_of_anticomm`. -/
theorem exists_prod {i j : pureSubmodule D} (h : pureForm i j = 0) :
    ∃ k : pureSubmodule D, (k : D) = (i : D) * (j : D) :=
  ⟨⟨(i : D) * (j : D),
    isPure_mul_of_anticomm (mem_pureSubmodule.mp i.2) (mem_pureSubmodule.mp j.2)
      ((orthogonal_iff_anticomm i j).mp h)⟩, rfl⟩

/-- `(ij)² = -1` when `i² = j² = -1` and the two are orthogonal. -/
theorem prod_pureSq {i j k : pureSubmodule D} (hi : pureSq i = -1) (hj : pureSq j = -1)
    (hij : pureForm i j = 0) (hk : (k : D) = (i : D) * (j : D)) : pureSq k = -1 := by
  have hanti : (i : D) * (j : D) + (j : D) * (i : D) = 0 := (orthogonal_iff_anticomm i j).mp hij
  have hi' : (i : D) * (i : D) = (-1 : ℝ) • (1 : D) := by rw [pureSq_spec i, hi]
  have hj' : (j : D) * (j : D) = (-1 : ℝ) • (1 : D) := by rw [pureSq_spec j, hj]
  have hsq : (k : D) * (k : D) = (-1 : ℝ) • (1 : D) := by
    rw [hk]
    have h := sq_mul_of_anticomm hanti hi' hj'
    have hone : (-((-1 : ℝ) * (-1 : ℝ))) = (-1 : ℝ) := by ring
    rwa [hone] at h
  exact (pureSq_eq hsq).symm

/-- `ij` is orthogonal to `i` — `RealDivisionAnticomm.anticomm_mul_left` through the dictionary. -/
theorem prod_orthogonal_left {i j k : pureSubmodule D} (hij : pureForm i j = 0)
    (hk : (k : D) = (i : D) * (j : D)) : pureForm k i = 0 := by
  have hanti : (i : D) * (j : D) + (j : D) * (i : D) = 0 := (orthogonal_iff_anticomm i j).mp hij
  refine (orthogonal_iff_anticomm k i).mpr ?_
  rw [hk]
  exact RealDivisionAnticomm.anticomm_mul_left hanti

/-- `ij` is orthogonal to `j`. -/
theorem prod_orthogonal_right {i j k : pureSubmodule D} (hij : pureForm i j = 0)
    (hk : (k : D) = (i : D) * (j : D)) : pureForm k j = 0 := by
  have hanti : (i : D) * (j : D) + (j : D) * (i : D) = 0 := (orthogonal_iff_anticomm i j).mp hij
  refine (orthogonal_iff_anticomm k j).mpr ?_
  rw [hk]
  exact RealDivisionAnticomm.anticomm_mul_right hanti

/-! ### §4. Three directions span the pure part -/

/-- **THE BASIS ARGUMENT.** For a normalised orthogonal pair `i`, `j` and any `k` equal to `i * j`,
the three span the whole pure part. The orthogonal complement of the triple is written down in
closed form and shown to be zero; there is no induction and no inner-product structure. -/
theorem span_eq_top_of_orthogonal_pair {i j k : pureSubmodule D} (hi : pureSq i = -1)
    (hj : pureSq j = -1) (hij : pureForm i j = 0) (hk : (k : D) = (i : D) * (j : D)) :
    Submodule.span ℝ (Set.range ![i, j, k]) = ⊤ := by
  have hji : pureForm j i = 0 := by rw [pureForm_comm]; exact hij
  have hk1 : pureSq k = -1 := prod_pureSq hi hj hij hk
  have hki : pureForm k i = 0 := prod_orthogonal_left hij hk
  have hkj : pureForm k j = 0 := prod_orthogonal_right hij hk
  have hik : pureForm i k = 0 := by rw [pureForm_comm]; exact hki
  have hjk : pureForm j k = 0 := by rw [pureForm_comm]; exact hkj
  have hine : (i : D) ≠ 0 := coe_ne_zero_of_pureSq_neg (by rw [hi]; norm_num)
  have hjne : (j : D) ≠ 0 := coe_ne_zero_of_pureSq_neg (by rw [hj]; norm_num)
  refine eq_top_iff.mpr fun l _ => ?_
  have hexp : ∀ w : pureSubmodule D,
      pureForm (l + pureForm l i • i + pureForm l j • j + pureForm l k • k) w
        = pureForm l w + pureForm l i * pureForm i w + pureForm l j * pureForm j w
          + pureForm l k * pureForm k w := by
    intro w
    rw [pureForm_add_left, pureForm_add_left, pureForm_add_left,
      pureForm_smul_left, pureForm_smul_left, pureForm_smul_left]
  have h'i : pureForm (l + pureForm l i • i + pureForm l j • j + pureForm l k • k) i = 0 := by
    rw [hexp i, pureForm_self, hi, hji, hki]; ring
  have h'j : pureForm (l + pureForm l i • i + pureForm l j • j + pureForm l k • k) j = 0 := by
    rw [hexp j, pureForm_self, hj, hij, hkj]; ring
  have h'k : pureForm (l + pureForm l i • i + pureForm l j • j + pureForm l k • k) k = 0 := by
    rw [hexp k, pureForm_self, hk1, hik, hjk]; ring
  have hzero : ((l + pureForm l i • i + pureForm l j • j + pureForm l k • k : pureSubmodule D)
      : D) = 0 := by
    refine RealDivisionAnticomm.eq_zero_of_anticomm_three (mul_ne_zero hine hjne)
      ((orthogonal_iff_anticomm _ i).mp h'i) ((orthogonal_iff_anticomm _ j).mp h'j) ?_
    have h := (orthogonal_iff_anticomm _ k).mp h'k
    rwa [hk] at h
  have hl'0 : l + pureForm l i • i + pureForm l j • j + pureForm l k • k = 0 :=
    Submodule.coe_eq_zero.mp hzero
  have hmi : i ∈ Set.range ![i, j, k] := ⟨0, by simp⟩
  have hmj : j ∈ Set.range ![i, j, k] := ⟨1, by simp⟩
  have hmk : k ∈ Set.range ![i, j, k] := ⟨2, by simp⟩
  have hsub : pureForm l i • i + pureForm l j • j + pureForm l k • k
      ∈ Submodule.span ℝ (Set.range ![i, j, k]) :=
    Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span hmi))
      (Submodule.smul_mem _ _ (Submodule.subset_span hmj)))
      (Submodule.smul_mem _ _ (Submodule.subset_span hmk))
  have hleq : l = (l + pureForm l i • i + pureForm l j • j + pureForm l k • k)
      - (pureForm l i • i + pureForm l j • j + pureForm l k • k) := by abel
  rw [hleq, hl'0]
  exact Submodule.sub_mem _ (Submodule.zero_mem _) hsub

/-! ### §5. The dimension count -/

/-- **The pure part has dimension at most three**, with no hypothesis beyond the standing three:
the normalised orthogonal pair is built where it exists, and the two degenerate cases — everything
is zero, or one direction already spans — are disposed of directly. -/
theorem finrank_pure_le_three : Module.finrank ℝ (pureSubmodule D) ≤ 3 := by
  by_cases h1 : ∃ u : pureSubmodule D, u ≠ 0
  case neg =>
    haveI : Subsingleton (pureSubmodule D) := ⟨fun x y => by
      rw [not_not.mp (fun h => h1 ⟨x, h⟩), not_not.mp (fun h => h1 ⟨y, h⟩)]⟩
    rw [Module.finrank_zero_of_subsingleton]
    norm_num
  obtain ⟨u, hu⟩ := h1
  obtain ⟨t, _, hti⟩ := exists_smul_sq_neg_one (mem_pureSubmodule.mp u.2)
    (fun hc => hu (Submodule.coe_eq_zero.mp hc))
  have hi : pureSq (t • u) = -1 := (pureSq_eq (D := D) (u := t • u) hti).symm
  by_cases h2 : ∃ v : pureSubmodule D,
      v ∉ Submodule.span ℝ ({t • u} : Set (pureSubmodule D))
  case neg =>
    have hall : ∀ v : pureSubmodule D, v ∈ Submodule.span ℝ ({t • u} : Set (pureSubmodule D)) :=
      fun v => not_not.mp (fun h => h2 ⟨v, h⟩)
    have hrange : Set.range ![t • u] = ({t • u} : Set (pureSubmodule D)) := by simp
    have hspan : Submodule.span ℝ (Set.range ![t • u]) = ⊤ := by
      rw [hrange]
      exact eq_top_iff.mpr fun v _ => hall v
    have hb := finrank_le_of_span_eq_top hspan
    simp only [Fintype.card_fin] at hb
    omega
  obtain ⟨v, hv⟩ := h2
  have hwi : pureForm (v + pureForm v (t • u) • (t • u)) (t • u) = 0 :=
    pureForm_orthogonalise hi v
  have hwne : v + pureForm v (t • u) • (t • u) ≠ 0 := by
    intro h0
    refine hv ?_
    have hveq : v = (v + pureForm v (t • u) • (t • u)) - pureForm v (t • u) • (t • u) := by abel
    rw [hveq, h0]
    exact Submodule.sub_mem _ (Submodule.zero_mem _)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  obtain ⟨s, _, hsj⟩ := exists_smul_sq_neg_one
    (mem_pureSubmodule.mp (v + pureForm v (t • u) • (t • u)).2)
    (fun hc => hwne (Submodule.coe_eq_zero.mp hc))
  have hj : pureSq (s • (v + pureForm v (t • u) • (t • u))) = -1 :=
    (pureSq_eq (D := D) (u := s • (v + pureForm v (t • u) • (t • u))) hsj).symm
  have hij : pureForm (t • u) (s • (v + pureForm v (t • u) • (t • u))) = 0 := by
    rw [pureForm_comm, pureForm_smul_left, hwi, mul_zero]
  obtain ⟨k, hk⟩ := exists_prod hij
  have hb := finrank_le_of_span_eq_top (span_eq_top_of_orthogonal_pair hi hj hij hk)
  simp only [Fintype.card_fin] at hb
  exact hb

/-- **The dimension count, in `D`.** Every finite-dimensional real division algebra has dimension
at most four. `3` is not excluded here; see the header. -/
theorem finrank_le_four : Module.finrank ℝ D ≤ 4 := by
  have h := finrank_eq_succ (D := D)
  have h3 := finrank_pure_le_three (D := D)
  omega

/-! ### §6. The hypotheses are satisfiable — two checks against `ℂ` -/

/-- **`i` really is pure**, at the one algebra where everybody can check the answer. This tests the
DEFINITION rather than the theorem: `IsPure` asks for a non-positive real that the element squares
to, and for `Complex.I` that real is `-1`. -/
theorem isPure_I : IsPure (Complex.I) := ⟨-1, by norm_num, by rw [Complex.I_mul_I]; simp⟩

/-- **§5 is not quantified over an empty class.** `ℂ` satisfies all three standing hypotheses and
the bound holds there — with room to spare, since `Complex.finrank_real_complex` says the dimension
is `2`. A theorem about finite-dimensional real division algebras that happened to have no
instances would compile exactly as this one does, so the instances are exhibited. -/
theorem finrank_complex_le_four : Module.finrank ℝ ℂ ≤ 4 := finrank_le_four

end RealDivisionPureBasis
