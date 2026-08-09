/-
  HermitePiPoincare.lean — **the Gaussian Poincaré inequality in n
  dimensions, beyond polynomials**.

  `Var(f) ≤ Σᵢ ∫ gᵢ² dγⁿ` for every `f ∈ L²(γⁿ)` with a gradient partner `g`
  in the sense of `HermitePiStein.SteinPairPi` — Gaussian integration by
  parts against the multi-index Hermite system, one coordinate at a time.
  The constant is `1` and §5 proves it sharp.

  WHAT THIS IS AND IS NOT, STATED CAREFULLY BECAUSE TWO NEARBY CLAIMS ARE
  FALSE. The estate has had `poincare_MV` — the same inequality for
  POLYNOMIAL test functions — since early August. This statement is about a
  class **defined by a pairing condition rather than by being a
  polynomial**, which is a genuine difference in kind: membership is a
  property an arbitrary `L²(γⁿ)` function can have.

  **What is not proved IN THIS FILE, and what an earlier draft of this header
  wrongly claimed was:** that the class is strictly LARGER than the
  polynomials. Every member §5 exhibits is a Hermite product, and Hermite
  products are polynomials. The claim was retracted here and the gap named on
  the watchlist.

  **RESOLVED THE SAME DAY, in `AbsSteinWitnessPi`.** `|xᵢ|` is a member of
  `SteinPairPi n` with gradient `sgn(xᵢ)·eᵢ`
  (`absCoord_steinPairPi`), and it is not a.e. equal to ANY differentiable
  function, hence to no polynomial (`absCoord_not_ae_differentiable`). So the
  class IS strictly larger than the polynomials and this inequality IS
  genuinely beyond `poincare_MV` — but that is a theorem in another file, and
  this header states it as a pointer rather than as something proved below.

  **It is also NOT the textbook Sobolev space.** Connecting `SteinPairPi` to
  `TextbookSobolevPi`'s `Cc^∞`-tested class is the n-dimensional
  `W6Converse`, a cutoff argument with no twin in the estate, and until it
  lands the n-dimensional "polynomial test functions only" fence has not
  fallen. That distinction is the whole reason the two are separate files.

  **What IS proved beyond the inequality:** the constant `1` is SHARP in
  every dimension (`poincare_sharp` — for the coordinate function both sides
  are `1`), and the Hermite products are all members with their gradients
  (`Hpi_mem`), which is what stops the theorem from being about constants
  only.

  THE PROOF IS THE 1-d ONE WITH A REINDEXING IN THE MIDDLE. Parseval turns
  `Var(f)` into `Σ_{m ≠ 0} (∏ⱼmⱼ!)·c_m(f)²`. Parseval and
  `HermitePiStein.coeffPi_recursion` turn `Σᵢ ∫ gᵢ²` into
  `Σ_k |k|·(∏ⱼkⱼ!)·c_k(f)²`, where `|k| = Σᵢ kᵢ` — and THAT step is the one
  piece with no 1-dimensional analogue, because in one dimension the
  reindexing `n ↦ n+1` is `Nat.succ` and Mathlib has shift lemmas for it.
  Here it is `m ↦ m + eᵢ` on multi-indices, and the bijection onto
  `{k : kᵢ ≥ 1}` has to be built by hand. The inequality is then
  `1 ≤ |k|` for `k ≠ 0`, term by term.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import HermitePiStein

namespace HermitePiPoincare

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness GaussianProductMeasure HermitePi
open HermitePiBessel HermitePiBasis HermitePiRiesz HermitePiStein

noncomputable section

/-! ## 1. The zero multi-index -/

theorem facPi_zero (n : ℕ) : facPi n (0 : Fin n → ℕ) = 1 := by
  simp [facPi]

theorem Hpi_zero (n : ℕ) (x : Fin n → ℝ) : Hpi n (0 : Fin n → ℕ) x = 1 := by
  simp [Hpi]

theorem coeffPi_zero (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    coeffPi n (0 : Fin n → ℕ) f = ∫ x, f x ∂gaussPi n := by
  rw [coeffPi, facPi_zero, div_one]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [Hpi_zero, mul_one]

/-! ## 2. Variance as a sum over the NONZERO multi-indices -/

theorem variance_eq_tsum (n : ℕ) {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 (gaussPi n)) :
    (∫ x, f x * f x ∂gaussPi n) - (∫ x, f x ∂gaussPi n) ^ 2
      = ∑' k : Fin n → ℕ,
          (if k = 0 then 0 else facPi n k * coeffPi n k f ^ 2) := by
  classical
  have hsum : Summable fun k : Fin n → ℕ => facPi n k * coeffPi n k f ^ 2 := by
    have h := summable_coeffPi_sq n (hf.toLp f)
    refine h.congr fun k => ?_
    rw [coeffPi_congr_ae n hf.coeFn_toLp k]
  have hpar := integral_mul_eq_tsum_coeffPi n hf hf
  have hsq : ∀ k : Fin n → ℕ,
      facPi n k * (coeffPi n k f * coeffPi n k f) = facPi n k * coeffPi n k f ^ 2 := by
    intro k; ring
  rw [tsum_congr hsq] at hpar
  rw [hpar, hsum.tsum_eq_add_tsum_ite (0 : Fin n → ℕ), facPi_zero, coeffPi_zero, one_mul]
  ring

/-! ## 3. The reindexing `m ↦ m + eᵢ`

This is the step with no one-dimensional analogue: there the shift is
`Nat.succ` and Mathlib has `summable_nat_add_iff` and friends. Here the map
is `succAt · i` on multi-indices, and what is needed is that it is injective
with range exactly `{k : kᵢ ≥ 1}` — which is where the weight `kᵢ` in §4
comes from, since it kills precisely the multi-indices outside that range.
-/

theorem succAt_injective (n : ℕ) (i : Fin n) :
    Function.Injective fun m : Fin n → ℕ => succAt m i := by
  intro m m' h
  funext j
  have hcf := congrFun h j
  dsimp only at hcf
  by_cases hj : j = i
  · subst hj
    rw [succAt_self, succAt_self] at hcf
    omega
  · rwa [succAt_of_ne m hj, succAt_of_ne m' hj] at hcf

/-- Every multi-index with `kᵢ ≥ 1` is in the range: lower the `i`-th entry. -/
theorem mem_range_succAt (n : ℕ) (i : Fin n) {k : Fin n → ℕ} (hk : k i ≠ 0) :
    k ∈ Set.range fun m : Fin n → ℕ => succAt m i := by
  refine ⟨Function.update k i (k i - 1), ?_⟩
  funext j
  dsimp only
  by_cases hj : j = i
  · subst hj
    rw [succAt_self, Function.update_self]
    omega
  · rw [succAt_of_ne _ hj, Function.update_of_ne hj]

/-- **THE REINDEXED PARSEVAL SUM.** For each coordinate,
    `Σ_m (∏ⱼmⱼ!)·c_m(gᵢ)² = Σ_k kᵢ·(∏ⱼkⱼ!)·c_k(f)²`. -/
theorem tsum_coeff_gi (n : ℕ) {f : (Fin n → ℝ) → ℝ}
    {g : Fin n → ((Fin n → ℝ) → ℝ)} (h : SteinPairPi n f g) (i : Fin n) :
    (∑' m : Fin n → ℕ, facPi n m * coeffPi n m (g i) ^ 2)
      = ∑' k : Fin n → ℕ, (k i : ℝ) * (facPi n k * coeffPi n k f ^ 2) := by
  set F : (Fin n → ℕ) → ℝ :=
    fun k => (k i : ℝ) * (facPi n k * coeffPi n k f ^ 2) with hFdef
  have hterm : ∀ m : Fin n → ℕ,
      facPi n m * coeffPi n m (g i) ^ 2 = F (succAt m i) := by
    intro m
    rw [hFdef]
    simp only
    rw [succAt_self, coeffPi_recursion n h i m, facPi_succAt]
    push_cast
    ring
  have hsupp : Function.support F ⊆ Set.range fun m : Fin n → ℕ => succAt m i := by
    intro k hk
    refine mem_range_succAt n i ?_
    intro h0
    apply hk
    rw [hFdef]
    simp [h0]
  rw [tsum_congr hterm, (succAt_injective n i).tsum_eq hsupp]

/-- **EXTRACTED from `poincare_steinPi`, where this was a `have`.** If `f`
    has a Stein partner then for each coordinate the `kᵢ`-weighted
    coefficient series of `f` CONVERGES. The inequality below consumes it,
    and so does every refutation of membership: a coefficient sequence whose
    weighted series diverges has no partner at all. -/
theorem summable_weighted_coeffPi (n : ℕ) {f : (Fin n → ℝ) → ℝ}
    {g : Fin n → ((Fin n → ℝ) → ℝ)} (h : SteinPairPi n f g) (i : Fin n) :
    Summable fun k : Fin n → ℕ => (k i : ℝ) * (facPi n k * coeffPi n k f ^ 2) := by
  classical
  have hg := h.2.1
  have hs : Summable fun m : Fin n → ℕ => facPi n m * coeffPi n m (g i) ^ 2 := by
    have hh := summable_coeffPi_sq n ((hg i).toLp (g i))
    refine hh.congr fun m => ?_
    rw [coeffPi_congr_ae n (hg i).coeFn_toLp m]
  have hterm : ∀ m : Fin n → ℕ,
      facPi n m * coeffPi n m (g i) ^ 2
        = (fun k : Fin n → ℕ => (k i : ℝ) * (facPi n k * coeffPi n k f ^ 2))
            (succAt m i) := by
    intro m
    simp only
    rw [succAt_self, coeffPi_recursion n h i m, facPi_succAt]
    push_cast
    ring
  have hsupp : Function.support
      (fun k : Fin n → ℕ => (k i : ℝ) * (facPi n k * coeffPi n k f ^ 2))
        ⊆ Set.range fun m : Fin n → ℕ => succAt m i := by
    intro k hk
    refine mem_range_succAt n i ?_
    intro h0
    apply hk
    simp [h0]
  have hzero : ∀ k ∉ Set.range fun m : Fin n → ℕ => succAt m i,
      (fun k : Fin n → ℕ => (k i : ℝ) * (facPi n k * coeffPi n k f ^ 2)) k = 0 := by
    intro k hk
    by_contra hne
    exact hk (hsupp hne)
  exact ((succAt_injective n i).summable_iff hzero).mp (hs.congr hterm)

/-! ## 4. THE INEQUALITY -/

/-- **GAUSSIAN POINCARÉ IN n DIMENSIONS, BEYOND POLYNOMIALS.**
    For `f ∈ L²(γⁿ)` paired against the multi-index Hermite system with
    gradient `g`, `Var(f) ≤ Σᵢ ∫ gᵢ² dγⁿ`, with constant `1`. -/
theorem poincare_steinPi (n : ℕ) {f : (Fin n → ℝ) → ℝ}
    {g : Fin n → ((Fin n → ℝ) → ℝ)} (h : SteinPairPi n f g) :
    (∫ x, f x * f x ∂gaussPi n) - (∫ x, f x ∂gaussPi n) ^ 2
      ≤ ∑ i : Fin n, ∫ x, g i x * g i x ∂gaussPi n := by
  classical
  have hf := h.1
  have hg := h.2.1
  -- each coordinate's Parseval, reindexed
  have hgi : ∀ i : Fin n, (∫ x, g i x * g i x ∂gaussPi n)
      = ∑' k : Fin n → ℕ, (k i : ℝ) * (facPi n k * coeffPi n k f ^ 2) := by
    intro i
    have hpar := integral_mul_eq_tsum_coeffPi n (hg i) (hg i)
    have hsq : ∀ m : Fin n → ℕ,
        facPi n m * (coeffPi n m (g i) * coeffPi n m (g i))
          = facPi n m * coeffPi n m (g i) ^ 2 := by
      intro m; ring
    rw [tsum_congr hsq] at hpar
    rw [hpar, tsum_coeff_gi n h i]
  simp_rw [hgi]
  -- summability, coordinate by coordinate and in total
  have hsumF : ∀ i : Fin n,
      Summable fun k : Fin n → ℕ => (k i : ℝ) * (facPi n k * coeffPi n k f ^ 2) :=
    fun i => summable_weighted_coeffPi n h i
  rw [← Summable.tsum_finsetSum fun i _ => hsumF i]
  -- and the term-by-term comparison
  rw [variance_eq_tsum n hf]
  refine Summable.tsum_le_tsum (fun k => ?_) ?_ (summable_sum fun i _ => hsumF i)
  · have hbase : (0:ℝ) ≤ facPi n k * coeffPi n k f ^ 2 :=
      mul_nonneg (le_of_lt (facPi_pos n k)) (sq_nonneg _)
    have hall : ∀ i : Fin n, (0:ℝ) ≤ (k i : ℝ) * (facPi n k * coeffPi n k f ^ 2) :=
      fun i => mul_nonneg (Nat.cast_nonneg _) hbase
    by_cases hk : k = 0
    · rw [if_pos hk]
      exact Finset.sum_nonneg fun i _ => hall i
    · rw [if_neg hk]
      have hone : ∃ i : Fin n, k i ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hk (funext fun i => hc i)
      obtain ⟨i0, hi0⟩ := hone
      calc facPi n k * coeffPi n k f ^ 2
          = 1 * (facPi n k * coeffPi n k f ^ 2) := by ring
        _ ≤ (k i0 : ℝ) * (facPi n k * coeffPi n k f ^ 2) := by
            refine mul_le_mul_of_nonneg_right ?_ hbase
            have : 1 ≤ k i0 := Nat.one_le_iff_ne_zero.mpr hi0
            exact_mod_cast this
        _ ≤ ∑ i : Fin n, (k i : ℝ) * (facPi n k * coeffPi n k f ^ 2) := by
            exact Finset.single_le_sum (f := fun i : Fin n =>
              (k i : ℝ) * (facPi n k * coeffPi n k f ^ 2))
              (fun i _ => hall i) (Finset.mem_univ i0)
  · refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
      (summable_coeffPi_sq n (hf.toLp f) |>.congr fun k => by
        rw [coeffPi_congr_ae n hf.coeFn_toLp k])
    · split_ifs with hk
      · exact le_rfl
      · exact mul_nonneg (le_of_lt (facPi_pos n k)) (sq_nonneg _)
    · split_ifs with hk
      · exact mul_nonneg (le_of_lt (facPi_pos n k)) (sq_nonneg _)
      · exact le_rfl

/-! ## 5. The class is not just the constants, and the constant `1` is sharp

Without §5 the theorem would be an implication with only trivial instances:
`HermitePiStein.one_mem` puts the constants in the class, and there both
sides are `0`. So §5 exhibits the Hermite products themselves as members,
with their gradients — and at the multi-index `eᵢ`, where the member IS the
coordinate function `x ↦ xᵢ`, the inequality is an EQUALITY. That is
sharpness of the constant in every dimension.

Nothing here needs a derivative: the pairing condition is checked against
`Hpi_orthogonality` alone, because `Hpi_succ` has already turned the
left-hand side into a pairing of two Hermite products.
-/

/-- Lower the `i`-th entry of a multi-index by one. -/
def predAt {n : ℕ} (k : Fin n → ℕ) (i : Fin n) : Fin n → ℕ :=
  Function.update k i (k i - 1)

theorem predAt_self {n : ℕ} (k : Fin n → ℕ) (i : Fin n) : predAt k i i = k i - 1 := by
  simp [predAt]

theorem predAt_of_ne {n : ℕ} (k : Fin n → ℕ) {i j : Fin n} (h : j ≠ i) :
    predAt k i j = k j := by
  simp [predAt, Function.update_of_ne h]

theorem succAt_predAt {n : ℕ} {k : Fin n → ℕ} {i : Fin n} (h : k i ≠ 0) :
    succAt (predAt k i) i = k := by
  funext j
  by_cases hj : j = i
  · subst hj; rw [succAt_self, predAt_self]; omega
  · rw [succAt_of_ne _ hj, predAt_of_ne _ hj]

theorem predAt_succAt {n : ℕ} (m : Fin n → ℕ) (i : Fin n) :
    predAt (succAt m i) i = m := by
  funext j
  by_cases hj : j = i
  · subst hj; rw [predAt_self, succAt_self]; omega
  · rw [predAt_of_ne _ hj, succAt_of_ne _ hj]

theorem facPi_predAt {n : ℕ} {k : Fin n → ℕ} {i : Fin n} (h : k i ≠ 0) :
    facPi n k = (k i : ℝ) * facPi n (predAt k i) := by
  conv_lhs => rw [← succAt_predAt h]
  rw [facPi_succAt, predAt_self]
  congr 1
  have : 1 ≤ k i := Nat.one_le_iff_ne_zero.mpr h
  push_cast [Nat.cast_sub this]
  ring

/-- **THE HERMITE PRODUCTS ARE MEMBERS**, with gradient
    `gᵢ = kᵢ·Hpi (k − eᵢ)`. At `kᵢ = 0` the factor `kᵢ` kills the term, which
    is exactly right. -/
theorem Hpi_mem (n : ℕ) (k : Fin n → ℕ) :
    SteinPairPi n (Hpi n k) (fun i x => (k i : ℝ) * Hpi n (predAt k i) x) := by
  classical
  refine ⟨Hpi_memLp n k, fun i => (Hpi_memLp n (predAt k i)).const_mul _, fun i m => ?_⟩
  have hL : ∫ x, Hpi n k x
      * (x i * Hpi n m x - fderiv ℝ (Hpi n m) x (Pi.single i (1:ℝ))) ∂gaussPi n
      = if k = succAt m i then facPi n k else 0 := by
    rw [show (fun x : Fin n → ℝ => Hpi n k x
        * (x i * Hpi n m x - fderiv ℝ (Hpi n m) x (Pi.single i (1:ℝ))))
        = fun x => Hpi n k x * Hpi n (succAt m i) x from
      funext fun x => by rw [Hpi_succ]]
    rw [Hpi_orthogonal, facPi]
  have hR : ∫ x, ((k i : ℝ) * Hpi n (predAt k i) x) * Hpi n m x ∂gaussPi n
      = (k i : ℝ) * (if predAt k i = m then facPi n (predAt k i) else 0) := by
    rw [show (fun x : Fin n → ℝ => ((k i : ℝ) * Hpi n (predAt k i) x) * Hpi n m x)
        = fun x => (k i : ℝ) * (Hpi n (predAt k i) x * Hpi n m x) from
      funext fun x => by ring, integral_const_mul, Hpi_orthogonal, facPi]
  rw [hL, hR]
  by_cases hki : k i = 0
  · -- the gradient component vanishes, and so does the pairing
    have hne : k ≠ succAt m i := by
      intro hcon
      have := congrFun hcon i
      rw [succAt_self] at this
      omega
    rw [if_neg hne, hki]
    simp
  · by_cases hcase : k = succAt m i
    · have hm : predAt k i = m := by rw [hcase, predAt_succAt]
      rw [if_pos hcase, if_pos hm]
      exact facPi_predAt hki
    · have hm : predAt k i ≠ m := by
        intro hcon
        exact hcase (by rw [← hcon, succAt_predAt hki])
      rw [if_neg hcase, if_neg hm, mul_zero]

theorem facPi_single (n : ℕ) (i : Fin n) : facPi n (Pi.single i 1) = 1 := by
  classical
  rw [facPi, Finset.prod_eq_single i]
  · rw [Pi.single_eq_same]; simp
  · intro j _ hj; rw [Pi.single_eq_of_ne hj]; simp
  · intro h; exact absurd (Finset.mem_univ i) h

theorem single_ne_zero (n : ℕ) (i : Fin n) : (Pi.single i 1 : Fin n → ℕ) ≠ 0 := by
  intro h
  have := congrFun h i
  rw [Pi.single_eq_same] at this
  exact one_ne_zero this

theorem predAt_single (n : ℕ) (i : Fin n) :
    predAt (Pi.single i 1 : Fin n → ℕ) i = 0 := by
  funext j
  by_cases hj : j = i
  · subst hj; rw [predAt_self, Pi.single_eq_same]; rfl
  · rw [predAt_of_ne _ hj, Pi.single_eq_of_ne hj]; rfl

/-- The variance of the coordinate function is `1`. -/
theorem coord_var (n : ℕ) (i : Fin n) :
    (∫ x, Hpi n (Pi.single i 1) x * Hpi n (Pi.single i 1) x ∂gaussPi n)
      - (∫ x, Hpi n (Pi.single i 1) x ∂gaussPi n) ^ 2 = 1 := by
  have h1 : ∫ x, Hpi n (Pi.single i 1) x * Hpi n (Pi.single i 1) x ∂gaussPi n = 1 := by
    rw [Hpi_orthogonal, if_pos rfl, ← facPi, facPi_single]
  have h2 : ∫ x, Hpi n (Pi.single i 1) x ∂gaussPi n = 0 := by
    have hcast : (fun x : Fin n → ℝ => Hpi n (Pi.single i 1) x)
        = fun x => Hpi n (Pi.single i 1) x * Hpi n (0 : Fin n → ℕ) x :=
      funext fun x => by rw [Hpi_zero, mul_one]
    rw [hcast, Hpi_orthogonal, if_neg (single_ne_zero n i)]
  rw [h1, h2]
  norm_num

/-- And the squared gradient integrates to `1` as well. -/
theorem coord_grad_sq (n : ℕ) (i : Fin n) :
    (∑ j : Fin n, ∫ x, (((Pi.single i 1 : Fin n → ℕ) j : ℝ)
          * Hpi n (predAt (Pi.single i 1) j) x)
        * (((Pi.single i 1 : Fin n → ℕ) j : ℝ)
          * Hpi n (predAt (Pi.single i 1) j) x) ∂gaussPi n) = 1 := by
  classical
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, predAt_single]
    have hone : (fun x : Fin n → ℝ => ((1:ℕ) : ℝ) * Hpi n (0 : Fin n → ℕ) x
        * (((1:ℕ) : ℝ) * Hpi n (0 : Fin n → ℕ) x)) = fun _ => (1:ℝ) :=
      funext fun x => by rw [Hpi_zero]; norm_num
    rw [hone, integral_const, probReal_univ, smul_eq_mul, mul_one]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **THE CONSTANT IS SHARP IN EVERY DIMENSION.** For the coordinate
    function, the two sides of `poincare_steinPi` are both `1`. -/
theorem poincare_sharp (n : ℕ) (i : Fin n) :
    (∫ x, Hpi n (Pi.single i 1) x * Hpi n (Pi.single i 1) x ∂gaussPi n)
        - (∫ x, Hpi n (Pi.single i 1) x ∂gaussPi n) ^ 2
      = ∑ j : Fin n, ∫ x, (((Pi.single i 1 : Fin n → ℕ) j : ℝ)
            * Hpi n (predAt (Pi.single i 1) j) x)
          * (((Pi.single i 1 : Fin n → ℕ) j : ℝ)
            * Hpi n (predAt (Pi.single i 1) j) x) ∂gaussPi n := by
  rw [coord_var, coord_grad_sq]

/-- At the multi-index `eᵢ` the member is the coordinate function `x ↦ xᵢ`. -/
theorem Hpi_single_eq_coord (n : ℕ) (i : Fin n) (x : Fin n → ℝ) :
    Hpi n (Pi.single i 1) x = x i := by
  classical
  rw [Hpi, Finset.prod_eq_single i]
  · rw [Pi.single_eq_same, ← X_mul_H_zero, H_zero]
    simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, H_zero]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **THE CONSTANT IS SHARP IN EVERY DIMENSION.** The coordinate function
    `x ↦ xᵢ` is in the class with gradient `eᵢ`, and for it the inequality is
    an equality: `Var = 1 = Σⱼ ∫ gⱼ²`. -/
theorem coord_mem (n : ℕ) (i : Fin n) :
    SteinPairPi n (Hpi n (Pi.single i 1))
      (fun j x => ((Pi.single i 1 : Fin n → ℕ) j : ℝ)
        * Hpi n (predAt (Pi.single i 1) j) x) :=
  Hpi_mem n (Pi.single i 1)

end

end HermitePiPoincare
