/-
  GraphOS2Exponential.lean — OS2 for the exponential algebra of the lattice
  Gaussian field.

  WHY, AND THE ANSWER TO A QUESTION SEEDED ONE UNIT AGO. `GraphOS2` reached
  measure-level OS2 for LINEAR observables and stopped there, recording that
  the exponential algebra — OS2 as physics states it — needed the route
  `SchurExponential` → `OS2ExpKernel` → `OS2Exponential`, and that **whether
  that route applies here was unknown**: it worked on a reflected kernel of
  the form `∏ₖ exp(−Δₖ|zᵢₖ − θzⱼₖ|)`, a PRODUCT over coordinates, and the
  lattice Green function is the inverse of a matrix and is not a product over
  anything. The watchlist item seeded for it says the first deliverable of any
  attempt should be an answer to that question, negative if negative.

  **THE ANSWER IS YES, AND THE PRODUCT STRUCTURE WAS NEVER WHAT THE ROUTE
  NEEDED.** What `SchurExponential` consumes is a POSITIVE SEMIDEFINITE
  matrix; the OU programme built one out of a coordinate product because that
  was the only way it had to get one. Reflection positivity IS that matrix,
  handed over directly — `crossGram_posSemidef` below derives it from
  bilinearity in four lines. **So the lattice case is shorter than the case it
  was modelled on**, and the pessimism in the seeded item was misplaced. It is
  recorded here rather than deleted.

  WHAT THIS FILE PROVES:
  1. **`crossForm`** — the cross-covariance of two coefficient families across
     the reflection, `∑∑ c p · d q · G(θp, q)`; symmetric under `IsRefl`
     (`crossForm_symm`) and bilinear.
  2. **`crossGram_posSemidef`** — **the Gram matrix `[crossForm (t i) (t j)]`
     is positive semidefinite** whenever every `t i` is supported on a half
     where reflection positivity holds. This is the whole bridge: a statement
     quantified over ONE coefficient family becomes a statement about a MATRIX
     of them, by bilinearity, and nothing else is needed.
  3. **`Q_expand`, `charFun_freqVec`** — the characteristic function of the
     field at the frequency difference of two exponential observables is
     `exp(−q(tᵢ)/2 − q(tⱼ)/2 + crossForm tᵢ tⱼ)`, a positive real. The
     `qform`s match because the Green function is reflection-invariant
     (`qform_mir`), which is where `IsRefl` is spent a second time.
  4. **`os2_exponential`** — **OS2 FOR EXPONENTIAL OBSERVABLES OF THE GAUSSIAN
     FIELD OF ANY GRAPH.** A finite complex-linear combination of exponentials
     of the field, paired against the conjugate of its reflection, has
     non-negative integral.
  5. **§5, the instances**: the `d`-dimensional box of even side,
     **four dimensions**, and **`os2_exponential_lattice`** against
     `LatticeField.latticeField` on either side of the first-coordinate cut.

  WHAT THIS DOES NOT DO.
  * **Still one finite box of even side, still one coordinate cut.** Inherited
    verbatim; nothing here touches them.
  * **No infinite-volume limit and no continuum limit.** W2 stands untouched,
    and it is where the physics is.
  * **This is OS2 and only OS2.** OS0/OS1/OS3/OS4 — temperedness, Euclidean
    invariance, symmetry, ergodicity — are not formalised for this field, and
    OS reconstruction needs all of them plus a limit.
  * **The field is FREE.** Nothing here bears on interacting lattice systems,
    and in particular nothing here bears on the Peierls/Ruelle/Wilson
    citations `_proof_004_logos` carries.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import GraphOS2
import OS2ExpKernel

namespace GraphOS2Exponential

open MeasureTheory ProbabilityTheory Matrix Finset GraphLaplacian
open scoped ComplexOrder RealInnerProductSpace

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The two quadratic forms

`qform` is the field's own energy at a coefficient family; `crossForm` is the
covariance between a family and the reflection of another. `OS2Exponential`
calls these `qform` and `bform` and builds both out of `prodCov`; here they
are built out of `green`, which is the only difference that matters.
-/

/-- The self-form: `∑∑ c p · c q · G(p,q)`. -/
def qform (m : ℝ) (c : V → ℝ) : ℝ := ∑ p, ∑ q, c p * c q * green G m p q

/-- **The cross form**: the covariance of `c` with the reflection of `d`. -/
def crossForm (m : ℝ) (θ : V ≃ V) (c d : V → ℝ) : ℝ :=
  ∑ p, ∑ q, c p * d q * green G m (θ p) q

variable {G}

/-- The propagator between a site's mirror and another site is unchanged by
    swapping the two — invariance plus symmetry, and the reason `crossForm` is
    a symmetric form. -/
theorem green_refl_swap (m : ℝ) {θ : V ≃ V} (h : GraphReflection.IsRefl G θ) (p q : V) :
    green G m (θ p) q = green G m (θ q) p := by
  have h1 : green G m (θ p) (θ (θ q)) = green G m p (θ q) :=
    GraphReflection.green_aut h m p (θ q)
  rw [h.invol q] at h1
  rw [h1, GraphReflection.green_symm (G := G) m p (θ q)]

theorem crossForm_symm (m : ℝ) {θ : V ≃ V} (h : GraphReflection.IsRefl G θ) (c d : V → ℝ) :
    crossForm G m θ c d = crossForm G m θ d c :=
  calc crossForm G m θ c d
      = ∑ p, ∑ q, d q * c p * green G m (θ q) p :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
          rw [green_refl_swap m h p q]; ring
    _ = ∑ q, ∑ p, d q * c p * green G m (θ q) p := Finset.sum_comm
    _ = crossForm G m θ d c := rfl

/-! ## 2. Bilinearity, and the Gram matrix

**This is the bridge, and it is the whole reason the exponential layer is
cheap here.** `GraphReflection.ReflectionPositive` quantifies over ONE
coefficient family. `SchurExponential` wants a positive semidefinite MATRIX.
Bilinearity converts the first into the second with no analysis at all.
-/

theorem crossForm_sum_left (m : ℝ) (θ : V ≃ V) {M : ℕ} (a : Fin M → ℝ)
    (t : Fin M → V → ℝ) (d : V → ℝ) :
    ∑ i, a i * crossForm G m θ (t i) d
      = crossForm G m θ (fun p => ∑ i, a i * t i p) d := by
  simp only [crossForm, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => by ring

theorem crossForm_sum_right (m : ℝ) (θ : V ≃ V) {M : ℕ} (a : Fin M → ℝ)
    (t : Fin M → V → ℝ) (c : V → ℝ) :
    ∑ j, a j * crossForm G m θ c (t j)
      = crossForm G m θ c (fun q => ∑ j, a j * t j q) := by
  simp only [crossForm, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun j _ => by ring

/-- The quadratic form of the Gram matrix is the cross form of the combined
    family. -/
theorem crossGram_quad (m : ℝ) (θ : V ≃ V) {M : ℕ} (a : Fin M → ℝ) (t : Fin M → V → ℝ) :
    ∑ i, ∑ j, a i * a j * crossForm G m θ (t i) (t j)
      = crossForm G m θ (fun p => ∑ i, a i * t i p) (fun q => ∑ j, a j * t j q) := by
  have hrow : ∀ i, ∑ j, a i * a j * crossForm G m θ (t i) (t j)
      = a i * crossForm G m θ (t i) (fun q => ∑ j, a j * t j q) := by
    intro i
    rw [← crossForm_sum_right m θ a t (t i), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hrow]
  exact crossForm_sum_left m θ a t _

/-- **THE GRAM MATRIX OF THE CROSS FORM IS POSITIVE SEMIDEFINITE.** -/
theorem crossGram_posSemidef (m : ℝ) {θ : V ≃ V} (h : GraphReflection.IsRefl G θ)
    {H : Finset V} (hrp : GraphReflection.ReflectionPositive G m θ H)
    {M : ℕ} (t : Fin M → V → ℝ) (ht : ∀ i p, p ∉ H → t i p = 0) :
    (Matrix.of fun i j => crossForm G m θ (t i) (t j)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    exact crossForm_symm m h (t j) (t i)
  · intro a
    have hq : star a ⬝ᵥ (Matrix.of fun i j => crossForm G m θ (t i) (t j)) *ᵥ a
        = ∑ i, ∑ j, a i * a j * crossForm G m θ (t i) (t j) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, star_trivial]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hq, crossGram_quad]
    refine hrp _ fun p hp => ?_
    exact Finset.sum_eq_zero fun i _ => by rw [ht i p hp, mul_zero]

/-! ## 3. The frequency vector and the expansion of its quadratic form -/

variable (G)

/-- The frequency difference of the reflected observable at `c` and the plain
    observable at `d`. -/
def vfun (θ : V ≃ V) (c d : V → ℝ) : V → ℝ := fun p => c (θ.symm p) - d p

def freqVec (θ : V ≃ V) (c d : V → ℝ) : EuclideanSpace ℝ V := WithLp.toLp 2 (vfun θ c d)

variable {G}

omit [DecidableEq V] in
theorem inner_freqVec (θ : V ≃ V) (c d : V → ℝ) (ω : EuclideanSpace ℝ V) :
    ⟪ω, freqVec (V := V) θ c d⟫ = (∑ p, c p * ω (θ p)) - ∑ p, d p * ω p := by
  have hbase : ⟪ω, freqVec (V := V) θ c d⟫ = ∑ p, (c (θ.symm p) - d p) * ω p := by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun _ _ => rfl
  have h1 : ∑ p, (c (θ.symm p) - d p) * ω p
      = (∑ p, c (θ.symm p) * ω p) - ∑ p, d p * ω p := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hbase, h1]
  congr 1
  refine (Equiv.sum_comp θ (fun p => c (θ.symm p) * ω p)).symm.trans ?_
  exact Finset.sum_congr rfl fun p _ => by rw [Equiv.symm_apply_apply]

/-- The self-form is reflection-invariant. -/
theorem qform_mir (m : ℝ) {θ : V ≃ V} (h : GraphReflection.IsRefl G θ) (c : V → ℝ) :
    qform G m (fun p => c (θ.symm p)) = qform G m c := by
  have hrow : ∀ p : V, ∑ q, c (θ.symm p) * c (θ.symm q) * green G m p q
      = ∑ q, c (θ.symm p) * c q * green G m p (θ q) := by
    intro p
    refine (Equiv.sum_comp θ
      (fun q => c (θ.symm p) * c (θ.symm q) * green G m p q)).symm.trans ?_
    exact Finset.sum_congr rfl fun q _ => by rw [Equiv.symm_apply_apply]
  simp only [qform]
  rw [show (∑ p, ∑ q, c (θ.symm p) * c (θ.symm q) * green G m p q)
      = ∑ p, ∑ q, c (θ.symm p) * c q * green G m p (θ q) from
    Finset.sum_congr rfl fun p _ => hrow p]
  refine (Equiv.sum_comp θ
    (fun p => ∑ q, c (θ.symm p) * c q * green G m p (θ q))).symm.trans ?_
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Equiv.symm_apply_apply, GraphReflection.green_aut h m p q]

/-- The cross term of the expansion is `crossForm`. -/
theorem cross_term (m : ℝ) (θ : V ≃ V) (c d : V → ℝ) :
    ∑ p, ∑ q, c (θ.symm p) * d q * green G m p q = crossForm G m θ c d := by
  refine (Equiv.sum_comp θ
    (fun p => ∑ q, c (θ.symm p) * d q * green G m p q)).symm.trans ?_
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
    rw [Equiv.symm_apply_apply]

/-- **THE QUADRATIC FORM OF THE DIFFERENCE VECTOR EXPANDS**, exactly as
    `OS2Exponential.Q_expand` does for the doubled OU field, and for the same
    two reasons: the two self-blocks agree (`qform_mir`, i.e. reflection
    invariance) and the cross block is the reflected covariance. -/
theorem Q_expand (m : ℝ) {θ : V ≃ V} (h : GraphReflection.IsRefl G θ) (c d : V → ℝ) :
    (freqVec (V := V) θ c d : EuclideanSpace ℝ V) ⬝ᵥ (green G m) *ᵥ
        (freqVec (V := V) θ c d : EuclideanSpace ℝ V)
      = qform G m c + qform G m d - 2 * crossForm G m θ c d := by
  have hexp : (freqVec (V := V) θ c d : EuclideanSpace ℝ V) ⬝ᵥ (green G m) *ᵥ
      (freqVec (V := V) θ c d : EuclideanSpace ℝ V)
      = ∑ p, ∑ q, vfun θ c d p * green G m p q * vfun θ c d q := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by simp [freqVec]; ring
  rw [hexp]
  have hsplit : ∀ p q : V, vfun θ c d p * green G m p q * vfun θ c d q
      = c (θ.symm p) * c (θ.symm q) * green G m p q
        + d p * d q * green G m p q
        - (c (θ.symm p) * d q * green G m p q + d p * c (θ.symm q) * green G m p q) := by
    intro p q
    simp only [vfun]
    ring
  simp_rw [hsplit]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hA : (∑ p, ∑ q, c (θ.symm p) * c (θ.symm q) * green G m p q) = qform G m c :=
    qform_mir m h c
  have hB : (∑ p, ∑ q, d p * d q * green G m p q) = qform G m d := rfl
  have hC : (∑ p, ∑ q, c (θ.symm p) * d q * green G m p q) = crossForm G m θ c d :=
    cross_term m θ c d
  have hD : (∑ p, ∑ q, d p * c (θ.symm q) * green G m p q) = crossForm G m θ c d := by
    rw [← hC]
    refine Finset.sum_comm.trans ?_
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
      rw [GraphReflection.green_symm (G := G) m q p]; ring
  rw [hA, hB, hC, hD]
  ring

/-! ## 4. The characteristic function, and the theorem -/

theorem charFun_freqVec (m : ℝ) (hm : m ≠ 0) {θ : V ≃ V} (h : GraphReflection.IsRefl G θ)
    (c d : V → ℝ) :
    charFun (gaussianField G m) (freqVec (V := V) θ c d)
      = Complex.ofReal (Real.exp
          (-(qform G m c) / 2 + -(qform G m d) / 2 + crossForm G m θ c d)) := by
  rw [gaussianField, charFun_multivariateGaussian (green_posDef G hm).posSemidef]
  rw [inner_zero_right, Q_expand m h c d]
  rw [show ((qform G m c + qform G m d - 2 * crossForm G m θ c d : ℝ) : ℂ) / 2
      = ((qform G m c / 2 + qform G m d / 2 - crossForm G m θ c d : ℝ) : ℂ) by
    push_cast; ring]
  rw [Complex.ofReal_zero, zero_mul, zero_sub, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  congr 1
  ring_nf

theorem integrable_charTerm (m : ℝ) (v : EuclideanSpace ℝ V) :
    Integrable (fun ω : EuclideanSpace ℝ V => Complex.exp ((⟪ω, v⟫ : ℝ) * Complex.I))
      (gaussianField G m) := by
  have hmeas : AEStronglyMeasurable
      (fun ω : EuclideanSpace ℝ V => Complex.exp ((⟪ω, v⟫ : ℝ) * Complex.I))
      (gaussianField G m) := by fun_prop
  refine (integrable_const (1 : ℝ)).mono' hmeas ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Complex.norm_exp_ofReal_mul_I]

/-- **OS2 FOR EXPONENTIAL OBSERVABLES OF THE GAUSSIAN FIELD OF ANY GRAPH.**
    A finite complex-linear combination of exponentials of the reflected
    field, paired against the conjugate of the same combination of the plain
    field, has non-negative integral.

    This is the OS2 axiom in the shape physics states it — on the exponential
    algebra rather than on linear observables — for one covariance on one
    finite graph. -/
theorem os2_exponential (m : ℝ) (hm : m ≠ 0) {θ : V ≃ V} (h : GraphReflection.IsRefl G θ)
    {H : Finset V} (hrp : GraphReflection.ReflectionPositive G m θ H)
    {M : ℕ} (t : Fin M → V → ℝ) (ht : ∀ i p, p ∉ H → t i p = 0) (c : Fin M → ℂ) :
    0 ≤ ∫ ω, (∑ i, c i * Complex.exp ((∑ p, t i p * ω (θ p) : ℝ) * Complex.I))
        * (starRingEnd ℂ) (∑ j, c j * Complex.exp ((∑ p, t j p * ω p : ℝ) * Complex.I))
        ∂(gaussianField G m) := by
  have hpt : ∀ ω : EuclideanSpace ℝ V,
      (∑ i, c i * Complex.exp ((∑ p, t i p * ω (θ p) : ℝ) * Complex.I))
        * (starRingEnd ℂ) (∑ j, c j * Complex.exp ((∑ p, t j p * ω p : ℝ) * Complex.I))
      = ∑ i, ∑ j, (c i * (starRingEnd ℂ) (c j))
          * Complex.exp ((⟪ω, freqVec (V := V) θ (t i) (t j)⟫ : ℝ) * Complex.I) := by
    intro ω
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    rw [show (starRingEnd ℂ) (Complex.exp ((∑ p, t j p * ω p : ℝ) * Complex.I))
        = Complex.exp (-((∑ p, t j p * ω p : ℝ) * Complex.I)) by
      rw [← Complex.exp_conj]
      congr 1
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring]
    rw [inner_freqVec]
    have hE : Complex.exp ((∑ p, t i p * ω (θ p) : ℝ) * Complex.I)
        * Complex.exp (-((∑ p, t j p * ω p : ℝ) * Complex.I))
        = Complex.exp
            ((∑ p, t i p * ω (θ p) - ∑ p, t j p * ω p : ℝ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc c i * Complex.exp ((∑ p, t i p * ω (θ p) : ℝ) * Complex.I)
          * ((starRingEnd ℂ) (c j) * Complex.exp (-((∑ p, t j p * ω p : ℝ) * Complex.I)))
        = c i * (starRingEnd ℂ) (c j)
            * (Complex.exp ((∑ p, t i p * ω (θ p) : ℝ) * Complex.I)
              * Complex.exp (-((∑ p, t j p * ω p : ℝ) * Complex.I))) := by ring
      _ = _ := by rw [hE]
  simp_rw [hpt]
  have hint : ∀ i j : Fin M,
      Integrable (fun ω : EuclideanSpace ℝ V => (c i * (starRingEnd ℂ) (c j))
        * Complex.exp ((⟪ω, freqVec (V := V) θ (t i) (t j)⟫ : ℝ) * Complex.I))
        (gaussianField G m) :=
    fun i j => (integrable_charTerm m (freqVec (V := V) θ (t i) (t j))).const_mul _
  rw [integral_finset_sum _ (fun i _ =>
    integrable_finset_sum _ (fun j _ => hint i j))]
  have hterm : ∀ i j : Fin M,
      ∫ ω, (c i * (starRingEnd ℂ) (c j))
        * Complex.exp ((⟪ω, freqVec (V := V) θ (t i) (t j)⟫ : ℝ) * Complex.I)
        ∂(gaussianField G m)
      = (c i * (starRingEnd ℂ) (c j)) * Complex.ofReal (Real.exp
          (-(qform G m (t i)) / 2 + -(qform G m (t j)) / 2
            + crossForm G m θ (t i) (t j))) := by
    intro i j
    rw [show (fun ω : EuclideanSpace ℝ V => (c i * (starRingEnd ℂ) (c j))
        * Complex.exp ((⟪ω, freqVec (V := V) θ (t i) (t j)⟫ : ℝ) * Complex.I))
        = fun ω : EuclideanSpace ℝ V => (c i * (starRingEnd ℂ) (c j)) •
          Complex.exp ((⟪ω, freqVec (V := V) θ (t i) (t j)⟫ : ℝ) * Complex.I) from rfl,
    MeasureTheory.integral_smul, smul_eq_mul]
    congr 1
    rw [← charFun_freqVec m hm h (t i) (t j), charFun_apply]
  simp_rw [integral_finset_sum _ (fun j _ => hint _ j), hterm]
  have hd : ∀ i j : Fin M,
      -(qform G m (t i)) / 2 + -(qform G m (t j)) / 2 + crossForm G m θ (t i) (t j)
      = (fun i => -(qform G m (t i)) / 2) i + (fun i => -(qform G m (t i)) / 2) j
        + (Matrix.of fun i j => crossForm G m θ (t i) (t j)) i j := fun i j => rfl
  simp_rw [hd]
  exact OS2ExpKernel.gaussKernel_complex_nonneg _ (crossGram_posSemidef m h hrp t ht) c

/-! ## 5. The boxes -/

section Boxes

open BoxGraph GraphHalfSpace IsingFiniteVolume LatticeReflectionPositive

variable {d n : ℕ} {m : ℝ}

/-- Exponential-observable OS2 on the `d`-dimensional box of even side. -/
theorem os2_exponential_box (i : Fin d) (hn : Even n) (hm : m ≠ 0)
    {M : ℕ} (t : Fin M → BoxGraph.Site d n → ℝ)
    (ht : ∀ k p, p ∉ lowerHalf i n → t k p = 0) (c : Fin M → ℂ) :
    0 ≤ ∫ ω, (∑ k, c k * Complex.exp
          ((∑ p, t k p * ω (GraphReflection.revSite (n := n) i p) : ℝ) * Complex.I))
        * (starRingEnd ℂ) (∑ l, c l * Complex.exp ((∑ p, t l p * ω p : ℝ) * Complex.I))
        ∂(gaussianField (boxGraph d n) m) :=
  os2_exponential m hm
    { invol := GraphReflection.revSite_involutive i
      adj := fun p q => by
        simpa using GraphReflection.adj_revSite (n := n) i p q }
    (GraphReflectionPositive.reflectionPositive_box i hn hm) t ht c

/-- **AND IN FOUR DIMENSIONS.** -/
theorem os2_exponential_box_four (i : Fin 4) (hn : Even n) (hm : m ≠ 0)
    {M : ℕ} (t : Fin M → BoxGraph.Site 4 n → ℝ)
    (ht : ∀ k p, p ∉ lowerHalf i n → t k p = 0) (c : Fin M → ℂ) :
    0 ≤ ∫ ω, (∑ k, c k * Complex.exp
          ((∑ p, t k p * ω (GraphReflection.revSite (n := n) i p) : ℝ) * Complex.I))
        * (starRingEnd ℂ) (∑ l, c l * Complex.exp ((∑ p, t l p * ω p : ℝ) * Complex.I))
        ∂(gaussianField (boxGraph 4 n) m) :=
  os2_exponential_box i hn hm t ht c

/-- **THE ESTATE'S OWN FIELD, ON THE EXPONENTIAL ALGEBRA.** -/
theorem os2_exponential_lattice (hn : Even n) (hm : m ≠ 0)
    {half : Finset (IsingFiniteVolume.Site n)}
    (hlow : half ⊆ lowerHalfPair n ∨ half ⊆ (lowerHalfPair n)ᶜ)
    {M : ℕ} (t : Fin M → IsingFiniteVolume.Site n → ℝ)
    (ht : ∀ k p, p ∉ half → t k p = 0) (c : Fin M → ℂ) :
    0 ≤ ∫ ω, (∑ k, c k * Complex.exp
          ((∑ p, t k p * ω (LatticeReflection.refl n p) : ℝ) * Complex.I))
        * (starRingEnd ℂ) (∑ l, c l * Complex.exp ((∑ p, t l p * ω p : ℝ) * Complex.I))
        ∂(LatticeField.latticeField n m) := by
  rw [GraphLaplacian.latticeField_box]
  refine os2_exponential m hm (GraphReflection.isRefl_latticeGraph n) ?_ t ht c
  rw [GraphReflection.reflectionPositive_box n m half]
  rcases hlow with h | h
  · exact reflectionPositive_lattice hn hm h
  · exact reflectionPositive_lattice_compl hn hm h

end Boxes

/-! ## 6. Review round 86 — the ways this could be hollow

**"The seeded item said this might not work. Did the item just lose?"** Yes,
and the way it lost is the finding. It asked whether the entrywise-exponential
argument has purchase on a NON-FACTORISING kernel, on the grounds that the OU
route's kernel was a coordinate product. **The premise was a mis-reading of
what the route consumes.** `SchurExponential.posSemidef_entrywise_exp` takes a
positive semidefinite matrix and returns one; the product structure in the OU
case was how THAT file got its PSD matrix, not what the exponential step
needed. Here reflection positivity supplies it directly. **A named risk that
turns out to be a misdescription of one's own machinery is worth recording
more than one that materialises**, and the watchlist entry is annotated rather
than deleted.

**"Then is `crossGram_posSemidef` really doing work?"** It is the only new
mathematics in the file and it is four lines of bilinearity, which is an
honest description of both facts. `ReflectionPositive` says one quadratic form
is non-negative; positive semidefiniteness of the Gram matrix says a whole
family of them is. The step between is that `crossForm` is bilinear, so a
combination of the `t i` is itself a coefficient family supported on the half
— **and `ht` is exactly what makes that combination admissible.** Drop `ht`
and the theorem is false.

**"`IsRefl` appears twice. Is one of them decorative?"** No, and they are
different uses. `crossForm_symm` needs it to make the Gram matrix HERMITIAN,
without which `PosSemidef` is not even the right predicate. `qform_mir` needs
it so the two self-blocks of the expansion agree — that is the step which, in
the OU file, was `prodCov_doubled_inr_inr`, and it is the reason the exponent
splits as `d i + d j + B i j` in the shape
`OS2ExpKernel.gaussKernel_complex_nonneg` consumes. **If the reflection were
merely a bijection and not an automorphism, the expansion would carry a third
kind of term and the Schur step would not apply.**

**"How much of this is `OS2Exponential` copied?"** The characteristic-function
assembly — §4's `hpt`, `hint`, `hterm` — follows that file closely and the
header says so. What is NOT copied is §1–§3: `crossForm` over `green` instead
of `prodCov`, the Gram argument, and an expansion that works on ONE field with
a reflection acting on its index type rather than on a DOUBLED field with two
blocks. The doubling was the OU programme's way of expressing a reflection it
could not otherwise write; here the reflection is an `Equiv` and the field is
not doubled, which is why `Q_expand` has four terms rather than four blocks.

**"So is OS reconstruction close?"** No, and the gap is not this axiom. This
is OS2 for one covariance on one finite box of even side, cut in one
coordinate. **OS0, OS1, OS3 and OS4 are not formalised for this field at
all**, and reconstruction additionally needs the infinite-volume and continuum
limits, which are W2 and untouched. What has been shown today is that the
lattice free field satisfies one axiom in the full algebraic form — a rung,
and the ladder above it is longer than the one below.
-/

end

end GraphOS2Exponential
