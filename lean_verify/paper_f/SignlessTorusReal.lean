import SignlessTorusComplete

/-!
# `Q`'s spectrum on the periodic lattice, over `ℝ` — the complexification removed

`SignlessTorusComplete` determined the spectrum of `Q = D + A` on `torusGraph d (N+3)` and closed
with a fence naming its own restrictive setting:

> *"this is `Q` **over `ℂ`**; the real symmetric matrix has the same eigenvalues, but that transfer
> is not made and no file claims it."*

`PROOF_STRATEGY` §7 rule 3 — *"take a result already proven under restrictive hypotheses and remove
one"* — applied to that sentence. **`signlessLap G` is a real matrix**, and every statement about
its spectrum so far has been about its complexification.

> **`real_eigenvalue_iff_cx`** — the transfer, stated for **an arbitrary real square matrix and an
> arbitrary real scalar**, because it is not about this graph and will be wanted again: `μ` is an
> eigenvalue of `A` over `ℝ` **iff** it is an eigenvalue of `cx A` over `ℂ`. The forward direction
> is the coercion; the reverse takes real and imaginary parts, and the work is that at least one of
> them is non-zero.
>
> **`eigenvalue_real_iff`** — hence, on the periodic lattice in every dimension: a **real** `μ` is
> an eigenvalue of the **real** matrix `Q` exactly when `μ = 2d + 2 Σᵢ cos(2π kᵢ / n)` at some
> frequency.
>
> **`spectrum_real_eq_range_nuQR`** — the same as an equality of sets of reals.

**WHAT THIS DOES AND DOES NOT ADD.** It does not compute a new number: the values are the ones
entry 24 computed. What it removes is the complexification from the *statement*, so a caller
holding a real matrix and wanting its eigenvalues no longer has to pass through `ℂ` — and the
transfer that lets them is now a theorem about arbitrary real matrices rather than a remark.

**STILL FENCED.** **Multiplicities are not computed**, over `ℝ` any more than over `ℂ`. The
eigenvectors here are the real and imaginary parts of characters and **no claim is made that they
are independent**, so this determines the spectrum as a *set* and not as a list. The **box** is
still not reached: a boundary and a non-constant degree, so no character family at all.
-/

namespace SignlessTorusReal

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection CycleLaplacianSpectrum
open LaplacianSignless TorusLaplacianSpectrum SignlessTorusSpectrum SignlessTorusComplete

/-! ## 1. Real and complex eigenvalues of a real matrix -/

section Transfer

variable {V : Type*} [Fintype V]

/-- Applying a complexified real matrix and then taking real parts is applying the real matrix to
the real parts. -/
theorem cx_mulVec_re (A : Matrix V V ℝ) (z : V → ℂ) (v : V) :
    ((MatrixLoewner.cx A *ᵥ z) v).re = (A *ᵥ (fun u => (z u).re)) v := by
  simp [MatrixLoewner.cx, Matrix.mulVec, dotProduct, Complex.re_sum, Complex.mul_re]

/-- And likewise for imaginary parts. -/
theorem cx_mulVec_im (A : Matrix V V ℝ) (z : V → ℂ) (v : V) :
    ((MatrixLoewner.cx A *ᵥ z) v).im = (A *ᵥ (fun u => (z u).im)) v := by
  simp [MatrixLoewner.cx, Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im]

/-- **THE TRANSFER, AND IT IS ABOUT AN ARBITRARY REAL MATRIX.** A real number is an eigenvalue of a
real matrix exactly when it is an eigenvalue of its complexification. Stated here rather than
inside the application because nothing in it mentions a graph. -/
theorem real_eigenvalue_iff_cx (A : Matrix V V ℝ) (μ : ℝ) :
    (∃ x : V → ℝ, x ≠ 0 ∧ A *ᵥ x = μ • x)
      ↔ (∃ z : V → ℂ, z ≠ 0 ∧ MatrixLoewner.cx A *ᵥ z = (μ : ℂ) • z) := by
  have key : ∀ (x : V → ℝ) (w : V),
      (MatrixLoewner.cx A *ᵥ (fun u => (x u : ℂ))) w = (((A *ᵥ x) w : ℝ) : ℂ) := by
    intro x w
    simp [MatrixLoewner.cx, Matrix.mulVec, dotProduct]
  constructor
  · rintro ⟨x, hx0, hx⟩
    refine ⟨fun u => (x u : ℂ), ?_, ?_⟩
    · intro h
      apply hx0
      funext u
      have hu : ((x u : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by
        simpa using congrFun h u
      exact_mod_cast hu
    · funext v
      rw [key x v, congrFun hx v]
      simp
  · rintro ⟨z, hz0, hz⟩
    obtain ⟨u, hu⟩ : ∃ u, z u ≠ 0 := by
      by_contra h
      exact hz0 (funext fun w => not_not.1 (fun hw => h ⟨w, hw⟩))
    have hre : A *ᵥ (fun w => (z w).re) = μ • (fun w => (z w).re) := by
      funext v
      rw [← cx_mulVec_re A z v, hz]
      simp
    have him : A *ᵥ (fun w => (z w).im) = μ • (fun w => (z w).im) := by
      funext v
      rw [← cx_mulVec_im A z v, hz]
      simp
    by_cases hr : (fun w => (z w).re) = (0 : V → ℝ)
    · refine ⟨fun w => (z w).im, ?_, him⟩
      intro hi
      apply hu
      apply Complex.ext
      · exact congrFun hr u
      · exact congrFun hi u
    · exact ⟨fun w => (z w).re, hr, hre⟩

end Transfer

/-! ## 2. The real eigenvalue at a frequency -/

variable {d : ℕ}

/-- The eigenvalue as a **real** number: the degree `2d` plus one cosine per axis. This is
`SignlessTorusSpectrum.nuQ_eq_real`'s right-hand side given a name. -/
noncomputable def nuQR (N : ℕ) (k : Site d (N + 3)) : ℝ :=
  2 * d + ∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3))

theorem nuQ_eq_ofReal_nuQR (N : ℕ) (k : Site d (N + 3)) :
    nuQ N k = ((nuQR N k : ℝ) : ℂ) :=
  nuQ_eq_real N k

/-! ## 3. The real spectrum -/

/-- **THE REAL MATRIX `Q`, THE REAL SCALARS.** A real `μ` is an eigenvalue of
`signlessLap (torusGraph d (N+3))` **iff** `μ = 2d + 2 Σᵢ cos(2π kᵢ / n)` at some frequency `k`.
No complexification appears in the statement. -/
theorem eigenvalue_real_iff (N : ℕ) (μ : ℝ) :
    (∃ x : Site d (N + 3) → ℝ, x ≠ 0 ∧
        signlessLap (torusGraph d (N + 3)) *ᵥ x = μ • x)
      ↔ ∃ k : Site d (N + 3), nuQR N k = μ := by
  rw [real_eigenvalue_iff_cx, SignlessTorusComplete.eigenvalue_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [nuQ_eq_ofReal_nuQR] at hk; exact_mod_cast hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [nuQ_eq_ofReal_nuQR, hk]⟩

/-- **THE REAL SPECTRUM AS A SET.** -/
theorem spectrum_real_eq_range_nuQR (N : ℕ) :
    {μ : ℝ | ∃ x : Site d (N + 3) → ℝ, x ≠ 0 ∧
        signlessLap (torusGraph d (N + 3)) *ᵥ x = μ • x}
      = Set.range (nuQR (d := d) N) := by
  ext μ
  exact eigenvalue_real_iff N μ

end SignlessTorusReal
