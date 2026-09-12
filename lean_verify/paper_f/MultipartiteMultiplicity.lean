import MultipartiteEigenspace

/-!
# The equipartite family's three multiplicities, and nothing left over

**THE PREVIOUS UNIT FENCED THE TWO THIS FILE COUNTS.** `MultipartiteEigenspace` counted the third
eigenspace — the vanishing-part-sum vectors, of dimension `rt − r` — and said in its own words that
the other two are not counted, that *the second of the two is where the work is: it needs an
isomorphism between the part-constant vectors and `ℝ^r`, and this file builds none*. **This file
builds it**, counts both, and adds the three dimensions to `rt`.

**WHAT THE ISOMORPHISM IS, AND IT IS ONE MATHLIB MAP.** A vector on the parts becomes a
part-constant vector on the vertices by precomposition with `Prod.fst` — Mathlib's
`LinearMap.funLeft`, injective because `Prod.fst` is surjective once the parts are non-empty. Under
it the zero-sum vectors of `ℝ^r` become exactly the middle eigenspace, so the dimension `r − 1`
transports, and the zero-sum dimension is `CompleteSpectrumTwoPoints.finrank_ker_sumForm` at
`V := Fin r` — a lemma written two units ago for the complete graph and used here **unchanged**,
which is the whole reason it was stated for an arbitrary `Fintype`.

**WHERE THE HYPOTHESES BITE, MEASURED RATHER THAN ASSUMED.** The middle characterisation needs
`r ≥ 1` and `t ≥ 1` — summing the row equation over all vertices gives `rt·∑x = 0`, which is what
forces the total sum to vanish. The **top** characterisation needs `r ≥ 2`: summing over one part
gives `t·∑x = rt·partSum`, so the part sums are all equal, and the row equation then makes the
vector constant **provided `(r − 1)t ≠ 0`**. At `r = 1` the graph is edgeless and both statements
fail, as the previous unit's header already records for its own characterisation.

## What is proved

**`lift`, `lift_apply`, `injective_lift`, `partSum_lift`, `sum_lift`** — the part-constant lift
and its three basic identities: it is injective, it multiplies part sums by `t`, and it
multiplies the total sum by `t`.

**`signlessLap_multi_mulVec_eq_mid_iff`** — `Q x = (r−2)t·x` **iff** `x` is the lift of a zero-sum
vector on the parts. Both directions: the forward one recovers the vector as `partSum x i / t`.

**`eigenspace_signlessLap_multi_mid_eq`**, **`finrank_eigenspace_signlessLap_multi_mid`** — so
that eigenspace **is** the image of the zero-sum subspace under the lift, and its dimension is
**`r − 1`**.

**`signlessLap_multi_mulVec_eq_top_iff`**, **`eigenspace_signlessLap_multi_top_eq`**,
**`finrank_eigenspace_signlessLap_multi_top`** — `Q x = 2(r−1)t·x` **iff** `x` is constant, so that
eigenspace is the span of the constant vector, of dimension **one**.

**`finrank_eigenspaces_multi_add`** — **AND THE THREE DIMENSIONS ADD TO `rt`**: `1 + (r − 1) +
(rt − r)`. So there is no room for a fourth eigenvalue, which `MultipartiteSpectrum` proved by a
split and this file now proves again by dimension — the same double coverage
`CompleteSpectrumTwoPoints` gives for the complete graph.

## What is NOT here

* **NOTHING FOR THE ORDINARY LAPLACIAN'S TOP AND MIDDLE EIGENSPACES.** Its `(r−1)t` eigenspace is
  the same subspace as the signless one's (`MultipartiteEigenspace`), and its `0` and `rt`
  eigenspaces are the constants and the lifted zero-sum vectors by the same arguments with two
  signs changed — **and those two statements are not written here**. Not attempted, and no cost is
  offered (`ERRATUM 246`).
* **NO CHARACTERISTIC POLYNOMIAL**, as in the three units before this one: that step needs
  diagonalisability and these arguments avoid it.
⚠ **THE REASON IN THE PARAGRAPH ABOVE IS FALSE AND THE PARAGRAPH IS KEPT AS WRITTEN**
(`ERRATUM 94`, `ERRATUM 508`, 2026-09-12). It does not matter what this file's argument avoids:
`Matrix.IsHermitian.charpoly_eq` supplies the diagonalisation for **every** Hermitian matrix, and
this estate had been citing it since 2026-08-26 (`HermitianSpectralMapping`, `RayleighPow`). What
was genuinely missing was the **grouping** — the product over the index type is free, and the
explicit factorisation with multiplicities as exponents needed the dimension-to-fibre bridge, now
`HermitianCharpoly.charpoly_eq_prod_pow_finrank`. **The absence itself was correctly declared**:
this file writes no characteristic polynomial.

⚠ **AND THE ABSENCE IS CLOSED AS OF 2026-09-12 (entry 162)** (`ERRATUM 94`).
`MultipartiteSignlessCharpoly.charpoly_signlessLap_multi` writes it out for `r ≥ 2` and `t ≥ 2`:
`(X − 2(r−1)t)·(X − (r−2)t)^{r−1}·(X − (r−1)t)^{rt−r}`, the exponents being **this file's own three
dimension counts**. The only step that file adds is the eigenvalue **set** — that the image of the
enumeration is exactly those three values — for which it needs
`MultipartiteSpectrum.eigenvalue_signlessLap_multi` in one direction and these three counts being
non-zero in the other. `rootMultiplicity_signlessLap_multi_top`, `_mid` and `_part` say the
exponents are root multiplicities.
* **NOTHING AT `r = 1`**, where the graph is edgeless and two of the three characterisations are
  false — the header says which and why.
* **NOTHING UNBALANCED.** Parts of different sizes change the degree per part and the row identity
  with it.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and `OS1`
  in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `r` and `t` natural numbers; `1 ≤ r` and
`1 ≤ t` on the middle characterisation and its two consequences, `2 ≤ r` with `1 ≤ t` on the top
three, and `2 ≤ r` with `2 ≤ t` on the sum — the last only because it quotes
`MultipartiteEigenspace`'s dimension, which takes them. `lift` is `noncomputable` for the same
reason `partForm` is.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace MultipartiteMultiplicity

open Matrix Finset SimpleGraph LaplacianSignless MultipartiteSpectrum MultipartiteEigenspace
open CompleteSpectrumTwoPoints

variable {r t : ℕ}

/-! ## 1. The part-constant vectors, as the image of one linear map -/

/-- A vector on the parts, read as a vector on the vertices: the part-constant lift. -/
noncomputable def lift (r t : ℕ) : (Fin r → ℝ) →ₗ[ℝ] (Fin r × Fin t → ℝ) :=
  LinearMap.funLeft ℝ ℝ Prod.fst

theorem lift_apply (y : Fin r → ℝ) (v : Fin r × Fin t) : lift r t y v = y v.1 := rfl

theorem injective_lift (ht : 1 ≤ t) : Function.Injective (lift r t) := by
  refine LinearMap.funLeft_injective_of_surjective ℝ ℝ _ ?_
  intro i
  exact ⟨(i, ⟨0, by omega⟩), rfl⟩

theorem partSum_lift (y : Fin r → ℝ) (i : Fin r) : partSum (lift r t y) i = (t : ℝ) * y i := by
  simp [partSum, lift_apply, Finset.sum_const, Finset.card_univ]

theorem sum_lift (y : Fin r → ℝ) : ∑ v, lift r t y v = (t : ℝ) * ∑ i, y i := by
  rw [← sum_partSum]
  simp only [partSum_lift]
  rw [← Finset.mul_sum]

/-! ## 2. The middle eigenspace is the lift of the zero-sum vectors -/

theorem signlessLap_multi_mulVec_eq_mid_iff (hr : 1 ≤ r) (ht : 1 ≤ t)
    {x : Fin r × Fin t → ℝ} :
    signlessLap (completeEquipartiteGraph r t) *ᵥ x = (((r : ℝ) - 2) * t) • x
      ↔ ∃ y : Fin r → ℝ, (∑ i, y i) = 0 ∧ x = lift r t y := by
  have htne : (t : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  have hrne : (r : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  constructor
  · intro h
    have hrow : ∀ v : Fin r × Fin t,
        (((r : ℝ) - 1) * t) * x v + (∑ u, x u) - partSum x v.1 = (((r : ℝ) - 2) * t) * x v := by
      intro v
      have hv := congrFun h v
      rw [signlessLap_multi_mulVec] at hv
      simpa using hv
    have hpart : ∀ v : Fin r × Fin t, partSum x v.1 = (t : ℝ) * x v + ∑ u, x u := by
      intro v
      have := hrow v
      linarith [this]
    have hS : ∑ u, x u = 0 := by
      have h1 : ∑ v : Fin r × Fin t, partSum x v.1
          = ∑ v : Fin r × Fin t, ((t : ℝ) * x v + ∑ u, x u) :=
        Finset.sum_congr rfl fun v _ => hpart v
      rw [sum_partSum_comp, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
        nsmul_eq_mul] at h1
      have hfac : ((r : ℝ) * t) * ∑ u, x u = 0 := by push_cast at h1; linarith
      exact (mul_eq_zero.mp hfac).resolve_left (mul_ne_zero hrne htne)
    refine ⟨fun i => partSum x i / (t : ℝ), ?_, ?_⟩
    · rw [← Finset.sum_div, sum_partSum, hS, zero_div]
    · funext v
      rw [lift_apply, hpart v, hS, add_zero]
      field_simp
  · rintro ⟨y, hy, rfl⟩
    refine signlessLap_multi_mulVec_of_part_const ?_ ?_
    · intro v
      rw [partSum_lift, lift_apply]
    · rw [sum_lift, hy, mul_zero]

/-! ## 3. So the middle eigenspace has dimension `r − 1` -/

theorem eigenspace_signlessLap_multi_mid_eq (hr : 1 ≤ r) (ht : 1 ≤ t) :
    LinearMap.ker (Matrix.toLin' (signlessLap (completeEquipartiteGraph r t))
        - (((r : ℝ) - 2) * t) • LinearMap.id)
      = Submodule.map (lift r t) (LinearMap.ker (sumForm (Fin r))) := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero, Matrix.toLin'_apply, Submodule.mem_map]
  rw [signlessLap_multi_mulVec_eq_mid_iff hr ht]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, by simpa [LinearMap.mem_ker, sumForm_apply] using hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, ?_, rfl⟩
    simpa [sumForm_apply] using (LinearMap.mem_ker.mp hy)

theorem finrank_eigenspace_signlessLap_multi_mid (hr : 1 ≤ r) (ht : 1 ≤ t) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (completeEquipartiteGraph r t))
      - (((r : ℝ) - 2) * t) • LinearMap.id)) = r - 1 := by
  rw [eigenspace_signlessLap_multi_mid_eq hr ht,
    ← (Submodule.equivMapOfInjective (lift r t) (injective_lift ht)
      (LinearMap.ker (sumForm (Fin r)))).finrank_eq]
  simpa using finrank_ker_sumForm (V := Fin r) (by simpa using hr)

/-! ## 4. And the top eigenspace is the constants -/

theorem signlessLap_multi_mulVec_eq_top_iff (hr : 2 ≤ r) (ht : 1 ≤ t)
    {x : Fin r × Fin t → ℝ} :
    signlessLap (completeEquipartiteGraph r t) *ᵥ x = (2 * ((r : ℝ) - 1) * t) • x
      ↔ ∃ c : ℝ, x = fun _ ↦ c := by
  have htne : (t : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  have hrne : ((r : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hr0 : (r : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  constructor
  · intro h
    have hrow : ∀ v : Fin r × Fin t,
        (((r : ℝ) - 1) * t) * x v + (∑ u, x u) - partSum x v.1
          = (2 * ((r : ℝ) - 1) * t) * x v := by
      intro v
      have hv := congrFun h v
      rw [signlessLap_multi_mulVec] at hv
      simpa using hv
    have hpart : ∀ i : Fin r, (t : ℝ) * (∑ u, x u) = ((r : ℝ) * t) * partSum x i := by
      intro i
      have h1 : ∑ j : Fin t, ((((r : ℝ) - 1) * t) * x (i, j) + (∑ u, x u) - partSum x i)
          = ∑ j : Fin t, (2 * ((r : ℝ) - 1) * t) * x (i, j) :=
        Finset.sum_congr rfl fun j _ => hrow (i, j)
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
      simp only [partSum] at h1 ⊢
      ring_nf at h1 ⊢
      linarith [h1]
    refine ⟨(∑ u, x u) / ((r : ℝ) * t), funext fun v => ?_⟩
    have h2 := hrow v
    have h3 := hpart v.1
    have hx : (((r : ℝ) - 1) * t) * x v = (∑ u, x u) - partSum x v.1 := by linarith
    have hp : partSum x v.1 = (t : ℝ) * (∑ u, x u) / ((r : ℝ) * t) := by
      field_simp at h3 ⊢
      linarith [h3]
    rw [hp] at hx
    field_simp at hx ⊢
    linarith [hx]
  · rintro ⟨c, rfl⟩
    exact signlessLap_multi_mulVec_const c

theorem eigenspace_signlessLap_multi_top_eq (hr : 2 ≤ r) (ht : 1 ≤ t) :
    LinearMap.ker (Matrix.toLin' (signlessLap (completeEquipartiteGraph r t))
        - (2 * ((r : ℝ) - 1) * t) • LinearMap.id)
      = Submodule.span ℝ {(fun _ ↦ (1 : ℝ) : Fin r × Fin t → ℝ)} := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero, Matrix.toLin'_apply, Submodule.mem_span_singleton]
  rw [signlessLap_multi_mulVec_eq_top_iff hr ht]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by funext v; simp⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by funext v; simp⟩

theorem finrank_eigenspace_signlessLap_multi_top (hr : 2 ≤ r) (ht : 1 ≤ t) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (completeEquipartiteGraph r t))
      - (2 * ((r : ℝ) - 1) * t) • LinearMap.id)) = 1 := by
  rw [eigenspace_signlessLap_multi_top_eq hr ht]
  refine finrank_span_singleton ?_
  intro h0
  have := congrFun h0 (⟨0, by omega⟩, ⟨0, by omega⟩)
  simp at this

/-! ## 5. And the three dimensions add to the number of vertices -/

/-- **NOTHING IS LEFT OVER**: `1 + (r − 1) + (rt − r) = rt`. -/
theorem finrank_eigenspaces_multi_add (hr : 2 ≤ r) (ht : 2 ≤ t) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (completeEquipartiteGraph r t))
          - (2 * ((r : ℝ) - 1) * t) • LinearMap.id))
        + Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
          (signlessLap (completeEquipartiteGraph r t))
          - (((r : ℝ) - 2) * t) • LinearMap.id))
        + Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
          (signlessLap (completeEquipartiteGraph r t))
          - (((r : ℝ) - 1) * t) • LinearMap.id))
      = r * t := by
  rw [finrank_eigenspace_signlessLap_multi_top hr (by omega),
    finrank_eigenspace_signlessLap_multi_mid (by omega) (by omega),
    eigenspace_signlessLap_multi_eq (by omega), finrank_ker_partForm (by omega)]
  have h1 : r ≤ r * t := Nat.le_mul_of_pos_right r (by omega)
  omega

end MultipartiteMultiplicity
