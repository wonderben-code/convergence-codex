/-
  SpectralAction.lean — Tr f(D/Λ), written down.

  WHY. `PROOF_STRATEGY.md` §1 names exactly one object as the clearest
  open Caesar target in this project:

      "A definition that does not exist yet. If nothing downstream can
       even be STATED, defining the object is the Caesar move. Writing
       down a spectral-action measure in Lean is the clearest example
       currently open — every Bakry-Émery-family tag is blocked behind
       that object existing at all."

  And `UNLOCK_WATCHLIST`'s Bakry-Émery item records the trigger:
  **"REVISIT WHEN: a spectral action is written down as a function of an
  actual Dirac operator, even in a restricted finite model."** The estate
  now owns an actual Dirac operator — `KOSixSpectralTriple.D`, self-adjoint,
  anticommuting with the grading, part of a finite real spectral triple
  whose commutant and order-one axioms are proved. So the trigger can
  fire, and this file fires it.

  THE RESTRICTED MODEL, stated before anything else so it is not
  discovered later. **The cutoff function `f` is a POLYNOMIAL.** For a
  general Schwartz cutoff, `f(D/Λ)` needs functional calculus; for a
  polynomial it needs nothing at all, because `aeval` is already an
  algebra map and `D` acts on a finite-dimensional space. That is the
  "restricted finite model" the trigger asked for, and it is restricted
  in exactly one way, named here.

  WHAT THIS FILE PROVES:
  1. `Dlin`, `gammaLin` — the Dirac operator and the grading as bundled
     `LinearMap`s, so that `trace`, `pow` and `aeval` apply to them at
     all. `KOSixSpectralTriple` had them as raw functions with linearity
     lemmas beside them.
  2. **`spectralAction f Λ M := Tr (f (D/Λ))`** — the object. Nothing in
     the estate computed `Tr f(D/Λ)`, and `spectralAction_eq_sum` gives
     it as the moment expansion `∑ₖ fₖ Λ^(−k) Tr(Dᵏ)`.
  3. **`trace_Dlin_pow_odd`** — every ODD moment vanishes. From
     `{D, γ} = 0` and `γ² = 1`: conjugating `Dᵏ` by `γ` multiplies it by
     `(−1)ᵏ` and leaves the trace alone, so `Tr(Dᵏ) = (−1)ᵏ Tr(Dᵏ)`.
  4. **`spectralAction_neg_lambda`** — hence the spectral action is
     unchanged under `Λ ↦ −Λ`: **it is a function of `Λ²`.** That is the
     structural fact the estate's `gap = 2/Λ²` sentence needs and which
     was, until now, asserted nowhere. And
     **`spectralAction_congr_of_even`** — the action cannot see the odd
     part of the cutoff function at all.
  5. **`trace_Dlin_sq`** — the first nonconstant moment, computed:
     `Tr(D²) = 4 · Tr(M Mᴴ)`. The Frobenius norm of the Yukawa matrix,
     four times over — once per block of the four-block space. This is
     the term the physics literature calls the Yukawa/Higgs mass term,
     and here it is an equality between two things the estate defines.

  WHAT THIS DOES NOT DO, and it is the entire point of saying it here.
  **This is not a measure, and no Bakry-Émery tag moves.** The watchlist
  item asks whether the spectral action produces a Gaussian FLUCTUATION
  MEASURE of variance Λ²/2. A trace is a number, not a measure; nothing
  below constructs a measure, integrates against one, or derives a
  variance. What has changed is that the question is now expressible:
  `spectralAction` exists, its `Λ`-dependence is proved to be through
  `Λ²`, and its first nonconstant term is computed. §7 states the
  remaining leg precisely and sends the modelling choice to the author.

  ADDED AFTER THE FIRST DRAFT (§6): the odd-moment vanishing is a shadow
  of a three-line structural fact — **`γ` maps the `λ`-eigenvectors of
  `D` bijectively to the `(−λ)`-eigenvectors, so the spectrum is
  symmetric about zero**. That secures the general-cutoff case
  mathematically and narrows DECISION 6 to plumbing.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import KOSixSpectralTriple
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Eigenspace.Basic

namespace SpectralAction

open Matrix ComplexConjugate KOSixSpectralTriple

noncomputable section

variable {n : ℕ}

/-! ## 1. The operators, bundled

`KOSixSpectralTriple` defines `D` and `gamma` as functions with
linearity lemmas beside them. `trace`, `^` and `aeval` all need
`LinearMap`s, so the first thing this file does is bundle them; nothing
here is new mathematics.
-/

/-- The Dirac operator as a bundled linear map. -/
def Dlin (M : Matrix (Fin n) (Fin n) ℂ) : Hf n →ₗ[ℂ] Hf n where
  toFun := D M
  map_add' := D_add M
  map_smul' := D_smul M

/-- The chirality grading as a bundled linear map. -/
def gammaLin : Hf n →ₗ[ℂ] Hf n where
  toFun := gamma
  map_add' := gamma_add
  map_smul' := gamma_smul

@[simp] theorem Dlin_apply (M : Matrix (Fin n) (Fin n) ℂ) (v : Hf n) :
    Dlin M v = D M v := rfl

@[simp] theorem gammaLin_apply (v : Hf n) : (gammaLin : Hf n →ₗ[ℂ] Hf n) v = gamma v := rfl

theorem gammaLin_sq : (gammaLin : Hf n →ₗ[ℂ] Hf n) * gammaLin = 1 := by
  refine LinearMap.ext fun v => ?_
  change gamma (gamma v) = v
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := v
  simp [gamma]

/-- `{D, γ} = 0`, in the algebra of endomorphisms. Stated with the sign
    as a SCALAR rather than as `Neg.neg`, because every use below is a
    `smul` manipulation and mixing the two forms is what makes this kind
    of induction fight the rewriter. -/
theorem gammaLin_Dlin (M : Matrix (Fin n) (Fin n) ℂ) :
    (gammaLin : Hf n →ₗ[ℂ] Hf n) * Dlin M = ((-1 : ℂ)) • (Dlin M * gammaLin) := by
  refine LinearMap.ext fun v => ?_
  change gamma (D M v) = ((-1 : ℂ)) • (D M (gamma v))
  rw [neg_one_smul, D_anticomm_gamma M v, neg_neg]

/-! ## 2. The moments

Two facts about `Tr(Dᵏ)`: the odd ones vanish, and the first even one
is the Yukawa term.
-/

/-- Conjugating `Dᵏ` by the grading multiplies it by `(−1)ᵏ`. -/
theorem gammaLin_conj_pow (M : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    (gammaLin : Hf n →ₗ[ℂ] Hf n) * ((Dlin M) ^ k * gammaLin)
      = ((-1 : ℂ) ^ k) • (Dlin M) ^ k := by
  induction k with
  | zero => simp [gammaLin_sq]
  | succ k ih =>
    calc (gammaLin : Hf n →ₗ[ℂ] Hf n) * ((Dlin M) ^ (k + 1) * gammaLin)
        = (gammaLin * Dlin M) * ((Dlin M) ^ k * gammaLin) := by
          rw [pow_succ']; noncomm_ring
      _ = ((-1 : ℂ) • (Dlin M * gammaLin)) * ((Dlin M) ^ k * gammaLin) := by
          rw [gammaLin_Dlin]
      _ = (-1 : ℂ) • (Dlin M * (gammaLin * ((Dlin M) ^ k * gammaLin))) := by
          rw [smul_mul_assoc, mul_assoc]
      _ = (-1 : ℂ) • (Dlin M * (((-1 : ℂ) ^ k) • (Dlin M) ^ k)) := by rw [ih]
      _ = ((-1 : ℂ) ^ (k + 1)) • (Dlin M) ^ (k + 1) := by
          rw [mul_smul_comm, smul_smul, ← pow_succ' (Dlin M) k]
          congr 1
          ring

/-- **Every odd moment of the Dirac operator vanishes.** The grading
    does it: `Tr(Dᵏ) = Tr(γ Dᵏ γ) = (−1)ᵏ Tr(Dᵏ)`. -/
theorem trace_Dlin_pow_odd (M : Matrix (Fin n) (Fin n) ℂ) {k : ℕ} (hk : Odd k) :
    LinearMap.trace ℂ (Hf n) ((Dlin M) ^ k) = 0 := by
  have h1 : ((Dlin M) ^ k) = ((Dlin M) ^ k * gammaLin) * gammaLin := by
    rw [mul_assoc, gammaLin_sq, mul_one]
  have hstep : LinearMap.trace ℂ (Hf n) ((Dlin M) ^ k)
      = ((-1 : ℂ) ^ k) * LinearMap.trace ℂ (Hf n) ((Dlin M) ^ k) := by
    calc LinearMap.trace ℂ (Hf n) ((Dlin M) ^ k)
        = LinearMap.trace ℂ (Hf n) (((Dlin M) ^ k * gammaLin) * gammaLin) := by rw [← h1]
      _ = LinearMap.trace ℂ (Hf n) (gammaLin * ((Dlin M) ^ k * gammaLin)) :=
          LinearMap.trace_mul_comm ℂ _ _
      _ = ((-1 : ℂ) ^ k) * LinearMap.trace ℂ (Hf n) ((Dlin M) ^ k) := by
          rw [gammaLin_conj_pow, map_smul, smul_eq_mul]
  rw [hk.neg_one_pow] at hstep
  linear_combination hstep / 2

/-- The trace of a matrix acting on `Fin n → ℂ` is the matrix trace.

    **This is Mathlib's `Matrix.trace_toLin'_eq`**, and the only reason
    it is restated is that Mathlib phrases it for `Matrix.toLin'` while
    everything here produces `Matrix.mulVecLin`. The two are DEFEQ but
    not syntactically equal, so the `@[simp]` lemma does not fire and
    `exact?` does not find it — while `exact Matrix.trace_toLin'_eq A`
    closes it outright.

    Recorded because an earlier draft of this file carried the docstring
    "Mathlib has no lemma in this shape", on the strength of `exact?`
    failing. **`exact?` failing is not a probe.** ERRATUM 42's rule —
    grep the library for the SHAPE of the statement — found it in one
    search, before the false claim was committed. -/
theorem trace_mulVecLin (A : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.trace ℂ _ (Matrix.mulVecLin A) = A.trace :=
  Matrix.trace_toLin'_eq A

/-- `D` is off-diagonal in chirality, so `D²` is block diagonal — and
    each block is one of the four products `MMᴴ`, `MᴴM`, `M̄Mᵀ`, `MᵀM̄`. -/
theorem Dlin_sq (M : Matrix (Fin n) (Fin n) ℂ) :
    (Dlin M) ^ 2
      = LinearMap.prodMap
          (LinearMap.prodMap (Matrix.mulVecLin (M * Mᴴ)) (Matrix.mulVecLin (Mᴴ * M)))
          (LinearMap.prodMap (Matrix.mulVecLin (mbar M * Mᵀ))
            (Matrix.mulVecLin (Mᵀ * mbar M))) := by
  refine LinearMap.ext fun v => ?_
  rw [pow_two]
  change D M (D M v) = _
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := v
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · exact Matrix.mulVec_mulVec a M Mᴴ
  · exact Matrix.mulVec_mulVec b Mᴴ M
  · exact Matrix.mulVec_mulVec c (mbar M) Mᵀ
  · exact Matrix.mulVec_mulVec d Mᵀ (mbar M)

/-- **The first nonconstant moment: `Tr(D²) = 4 · Tr(M Mᴴ)`.** All four
    blocks contribute the same number — the particle blocks by
    `trace_mul_comm`, the antiparticle blocks because `M̄Mᵀ = (MMᴴ)ᵀ`. -/
theorem trace_Dlin_sq (M : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.trace ℂ (Hf n) ((Dlin M) ^ 2) = 4 * (M * Mᴴ).trace := by
  rw [Dlin_sq, LinearMap.trace_prodMap', LinearMap.trace_prodMap',
    LinearMap.trace_prodMap', trace_mulVecLin, trace_mulVecLin,
    trace_mulVecLin, trace_mulVecLin]
  have h1 : (Mᴴ * M).trace = (M * Mᴴ).trace := Matrix.trace_mul_comm _ _
  have h2 : (mbar M * Mᵀ).trace = (M * Mᴴ).trace := by
    rw [show mbar M * Mᵀ = (M * Mᴴ)ᵀ by
      rw [Matrix.transpose_mul, ← mbar_transpose, Matrix.transpose_transpose]]
    exact Matrix.trace_transpose _
  have h3 : (Mᵀ * mbar M).trace = (M * Mᴴ).trace := by
    rw [Matrix.trace_mul_comm, h2]
  rw [h1, h2, h3]
  ring

theorem finrank_Hf : Module.finrank ℂ (Hf n) = 4 * n := by
  simp [Hf, Module.finrank_prod]
  ring

/-- The zeroth moment is the dimension of the space: four blocks of
    size `n`. -/
theorem trace_Dlin_pow_zero (M : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.trace ℂ (Hf n) ((Dlin M) ^ 0) = (4 * n : ℕ) := by
  rw [pow_zero]
  change LinearMap.trace ℂ (Hf n) LinearMap.id = _
  rw [LinearMap.trace_id, finrank_Hf]

/-! ## 3. The spectral action

`Tr f(D/Λ)` for a POLYNOMIAL cutoff `f`. That restriction is what makes
the definition need no functional calculus: `aeval` is an algebra map
into the endomorphism ring, and the space is finite-dimensional so the
trace exists.
-/

/-- **The spectral action, `Tr f(D/Λ)`.** -/
def spectralAction (f : Polynomial ℂ) (Λ : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  LinearMap.trace ℂ (Hf n) (Polynomial.aeval (Λ⁻¹ • Dlin M) f)

/-- **The moment expansion.** `Tr f(D/Λ) = ∑ₖ fₖ Λ^(−k) Tr(Dᵏ)`. Stated
    over any range past the degree, so two polynomials can be compared
    on a common range. -/
theorem spectralAction_eq_sum (f : Polynomial ℂ) (Λ : ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) {N : ℕ} (hN : f.natDegree < N) :
    spectralAction f Λ M
      = ∑ k ∈ Finset.range N,
          f.coeff k * Λ⁻¹ ^ k * LinearMap.trace ℂ (Hf n) ((Dlin M) ^ k) := by
  rw [spectralAction, Polynomial.aeval_eq_sum_range' hN, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_pow, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_assoc]

/-! ## 4. It is a function of `Λ²`

The odd moments vanish, so only even powers of `Λ⁻¹` survive. Two
consequences, and the first is the one the estate's `gap = 2/Λ²`
sentence has always needed and never had.
-/

/-- **The spectral action is unchanged by `Λ ↦ −Λ`** — it depends on the
    cutoff only through `Λ²`. -/
theorem spectralAction_neg_lambda (f : Polynomial ℂ) (Λ : ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    spectralAction f (-Λ) M = spectralAction f Λ M := by
  rw [spectralAction_eq_sum f (-Λ) M (Nat.lt_succ_self _),
    spectralAction_eq_sum f Λ M (Nat.lt_succ_self _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases Nat.even_or_odd k with hk | hk
  · rw [show ((-Λ)⁻¹ : ℂ) = -(Λ⁻¹) by rw [inv_neg], hk.neg_pow]
  · rw [trace_Dlin_pow_odd M hk, mul_zero, mul_zero]

/-- **And it cannot see the odd part of the cutoff function.** Two
    polynomials agreeing in every even coefficient give the same
    action. -/
theorem spectralAction_congr_of_even (f g : Polynomial ℂ) (Λ : ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) (h : ∀ k, Even k → f.coeff k = g.coeff k) :
    spectralAction f Λ M = spectralAction g Λ M := by
  set N := max f.natDegree g.natDegree + 1 with hNdef
  have hf : f.natDegree < N := Nat.lt_succ_of_le (le_max_left _ _)
  have hg : g.natDegree < N := Nat.lt_succ_of_le (le_max_right _ _)
  rw [spectralAction_eq_sum f Λ M hf, spectralAction_eq_sum g Λ M hg]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases Nat.even_or_odd k with hk | hk
  · rw [h k hk]
  · rw [trace_Dlin_pow_odd M hk, mul_zero, mul_zero]

/-- A cutoff with no even part gives zero. -/
theorem spectralAction_of_no_even_part (f : Polynomial ℂ) (Λ : ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) (h : ∀ k, Even k → f.coeff k = 0) :
    spectralAction f Λ M = 0 := by
  rw [spectralAction_eq_sum f Λ M (Nat.lt_succ_self _)]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases Nat.even_or_odd k with hk | hk
  · rw [h k hk, zero_mul, zero_mul]
  · rw [trace_Dlin_pow_odd M hk, mul_zero]

/-! ## 5. The action at the quadratic cutoff

The leading nonconstant term, computed. `Tr((D/Λ)²) = 4 Tr(MMᴴ)/Λ²` —
the Yukawa/Higgs term of the physics literature, as an equality between
two objects this estate defines.
-/

theorem spectralAction_X_sq (Λ : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    spectralAction (Polynomial.X ^ 2) Λ M = Λ⁻¹ ^ 2 * (4 * (M * Mᴴ).trace) := by
  have hdeg : (Polynomial.X ^ 2 : Polynomial ℂ).natDegree < 3 := by
    rw [Polynomial.natDegree_X_pow]; norm_num
  rw [spectralAction_eq_sum _ Λ M hdeg, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one]
  rw [trace_Dlin_sq]
  simp [Polynomial.coeff_X_pow]

/-- And the constant cutoff sees only the dimension. -/
theorem spectralAction_one (Λ : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    spectralAction 1 Λ M = (4 * n : ℕ) := by
  have hdeg : (1 : Polynomial ℂ).natDegree < 1 := by
    rw [Polynomial.natDegree_one]; norm_num
  rw [spectralAction_eq_sum _ Λ M hdeg, Finset.sum_range_one,
    trace_Dlin_pow_zero]
  simp

/-! ## 6. Why the odd moments vanish: the spectrum is symmetric

§2 proves `Tr(Dᵏ) = 0` for odd `k` by a trace identity. That is the
form §4 consumes, but it is a shadow of something more basic, and the
more basic fact is three lines: **`γ` carries the `λ`-eigenvectors of
`D` to the `(−λ)`-eigenvectors bijectively, so the spectrum of `D` is
symmetric about zero.**

This matters beyond tidiness. §4's "the action is a function of `Λ²`"
is currently proved through the moment expansion and therefore holds
only for POLYNOMIAL cutoffs. The spectral symmetry is what would carry
the same conclusion for an arbitrary cutoff, because `Tr f(D/Λ)` is
then `∑ f(λᵢ/Λ)` over a set of eigenvalues closed under negation. So
this section secures the MATHEMATICAL content of the general case; what
DECISION 6 is left asking is whether the project wants the
functional-calculus plumbing, which is a scope question and not a
mathematical one.
-/

theorem gammaLin_gammaLin (v : Hf n) :
    (gammaLin : Hf n →ₗ[ℂ] Hf n) (gammaLin v) = v := by
  change gamma (gamma v) = v
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := v
  simp [gamma]

theorem gammaLin_injective : Function.Injective (gammaLin : Hf n →ₗ[ℂ] Hf n) :=
  Function.LeftInverse.injective gammaLin_gammaLin

/-- **`γ` sends `λ`-eigenvectors to `(−λ)`-eigenvectors.** -/
theorem eigenvector_neg (M : Matrix (Fin n) (Fin n) ℂ) (l : ℂ) (v : Hf n)
    (hv : Dlin M v = l • v) : Dlin M (gammaLin v) = (-l) • gammaLin v := by
  change D M (gamma v) = (-l) • gamma v
  rw [D_anticomm_gamma M v, show D M v = l • v from hv, gamma_smul, neg_smul]

/-- **The spectrum of the Dirac operator is symmetric about zero.** -/
theorem hasEigenvalue_neg (M : Matrix (Fin n) (Fin n) ℂ) (l : ℂ)
    (h : Module.End.HasEigenvalue (Dlin M) l) :
    Module.End.HasEigenvalue (Dlin M) (-l) := by
  obtain ⟨v, hv, hv0⟩ := h.exists_hasEigenvector
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := gammaLin v) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    refine eigenvector_neg M l v ?_
    rw [← Module.End.mem_eigenspace_iff]
    exact hv
  · intro hz
    exact hv0 (gammaLin_injective (by rw [hz, map_zero]))

/-- Stated as the biconditional it is, since `γ` is an involution. -/
theorem hasEigenvalue_neg_iff (M : Matrix (Fin n) (Fin n) ℂ) (l : ℂ) :
    Module.End.HasEigenvalue (Dlin M) l ↔ Module.End.HasEigenvalue (Dlin M) (-l) :=
  ⟨hasEigenvalue_neg M l, fun h => by simpa using hasEigenvalue_neg M (-l) h⟩

/-! ## 7. Review round 35 — that the object is not empty

Three ways this file could be a definition about nothing.

* If `D` were zero the moments would all vanish and §5 would be
  `0 = 0`. It is not, and the witness is explicit.
* If the odd-vanishing were vacuous — if there were no odd moments to
  vanish — §4 would be decoration. It is not: `Tr(D)` is an odd moment
  and `D ≠ 0`.
* If the action were constant in `Λ`, "a function of `Λ²`" would be an
  empty statement. It is not.
-/

/-- The Dirac operator is not the zero map, so the moments are moments
    of something. -/
theorem Dlin_one_ne_zero : Dlin (1 : Matrix (Fin 1) (Fin 1) ℂ) ≠ 0 := by
  intro h
  have hv := congrArg (fun T : Hf 1 →ₗ[ℂ] Hf 1 => (T ((1, 0), (0, 0))).1.2 0) h
  simp only [Dlin_apply, D, LinearMap.zero_apply, Matrix.conjTranspose_one,
    Matrix.one_mulVec, Pi.one_apply, Prod.fst_zero, Prod.snd_zero,
    Pi.zero_apply] at hv
  norm_num at hv

/-- **§5 is not `0 = 0`:** at `M = 1` the quadratic term is `4/Λ²`. -/
theorem spectralAction_X_sq_nonzero (Λ : ℂ) (hΛ : Λ ≠ 0) :
    spectralAction (Polynomial.X ^ 2) Λ (1 : Matrix (Fin 1) (Fin 1) ℂ) ≠ 0 := by
  rw [spectralAction_X_sq]
  simp [hΛ]

/-- **The `Λ`-dependence is real:** the quadratic action takes different
    values at `Λ = 1` and `Λ = 2`, so "a function of `Λ²`" is not a
    statement about a constant. -/
theorem spectralAction_lambda_dependent :
    spectralAction (Polynomial.X ^ 2) 1 (1 : Matrix (Fin 1) (Fin 1) ℂ)
      ≠ spectralAction (Polynomial.X ^ 2) 2 (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  rw [spectralAction_X_sq, spectralAction_X_sq]
  simp
  norm_num

/-- **The odd-vanishing is not vacuous:** the first moment is an odd
    moment, and it is zero while the operator is not. -/
theorem trace_Dlin_zero_but_Dlin_ne :
    LinearMap.trace ℂ (Hf 1) ((Dlin (1 : Matrix (Fin 1) (Fin 1) ℂ)) ^ 1) = 0
      ∧ Dlin (1 : Matrix (Fin 1) (Fin 1) ℂ) ≠ 0 :=
  ⟨trace_Dlin_pow_odd _ odd_one, Dlin_one_ne_zero⟩

/-! ## 8. What is still missing, and whose decision it is

**No Bakry-Émery tag moves.** The watchlist item this file fires the
trigger for asks whether the spectral action produces a Gaussian
FLUCTUATION MEASURE of variance `Λ²/2`. A trace is a number. Nothing
above constructs a measure, integrates against one, or derives a
variance, and no amount of further computation of `Tr(Dᵏ)` will produce
one — the missing step is a modelling step, not a calculation.

What HAS changed, precisely:

* `Tr f(D/Λ)` exists as a Lean object for the estate's own Dirac
  operator, where before nothing computed it at all.
* Its `Λ`-dependence is PROVED to be through `Λ²` alone
  (`spectralAction_neg_lambda`), which is the shape any `gap = 2/Λ²`
  claim must have and which was previously asserted nowhere.
* Its leading nonconstant term is `4 Tr(MMᴴ)/Λ²`.

**DECISIONS NEEDED (author).** Two, and they are modelling choices that
do not belong to a formalisation:

1. *What is the fluctuation measure?* To get from `Tr f(D/Λ)` to a
   probability measure one must say which variable fluctuates and with
   what weight — the standard choice being `exp(−Tr f(D/Λ))` in the
   inner fluctuations of `D`. The estate has no such definition and
   choosing one is a physics commitment.
2. *Is the polynomial cutoff acceptable?* The literature uses a smooth
   even cutoff and reads off heat-kernel coefficients. This file's
   restriction to polynomials is honest and stated. **§6 narrows this
   decision:** the mathematical content of the general case — that the
   spectrum is symmetric about zero, hence that only the even part of
   any cutoff can contribute — is now proved and does not depend on the
   cutoff being polynomial. What is left is functional-calculus
   plumbing, which is a scope question rather than a mathematical one.

Until (1) is answered the Bakry-Émery tags stay where they are, and the
watchlist item stays open with its remaining leg now one sentence long
instead of two.
-/

end

end SpectralAction
