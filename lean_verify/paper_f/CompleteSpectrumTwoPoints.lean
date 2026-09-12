import CompleteSignlessSpectrum

/-!
# The complete graph's spectrum is exactly two points, and the eigenspaces are named

**THE PREVIOUS UNIT FENCED THIS FILE'S CONTENT IN ITS OWN WORDS**: *the eigenvalue `n − 2` is
exhibited on the zero-sum subspace and **no dimension count is made**: that the subspace is
`(n − 1)`-dimensional, and that the two eigenvalues therefore exhaust the spectrum, is standard and
not proved here.* It is proved here, and **without a spectral theorem** — which is what makes it
worth a file rather than a citation.

**THE WHOLE ARGUMENT, BECAUSE IT IS SHORT AND NOBODY SHOULD LOOK FOR MORE.** On `K_n` the signless
Laplacian acts by `(Q x) v = (n − 2)·x v + ∑x`. Suppose `Q x = μ·x` with `x ≠ 0`, and sum that
equation over the vertices: the left side is `(n − 2)∑x + n∑x` and the right is `μ∑x`, so either
`∑x = 0` — and then the equation at any vertex where `x` does not vanish gives `μ = n − 2` — or
`μ = 2n − 2`. **No orthogonality, no diagonalisation, no `IsHermitian`**: two cases and a
cancellation. The same two lines give the ordinary Laplacian's `{0, n}`.

**AND THE TWO EIGENSPACES ARE NAMED RATHER THAN COUNTED.** `Q`'s `(n − 2)`-eigenspace **is** the
kernel of the sum functional, and its `(2n − 2)`-eigenspace **is** the span of the constant vector —
both as equalities of submodules, from which the dimensions `n − 1` and `1` follow. Their sum is
`n`, so there is no room for a third eigenvalue: the exhaustion is available twice over, once by the
case split and once by dimension.

**WHAT HAD TO BE PROVED RATHER THAN SUBSTITUTED** (`ERRATUM 500`'s rule): the case split and the two
submodule equalities are new; `CompleteSignlessSpectrum` supplied the row identities, and Mathlib
supplied `LinearMap.finrank_range_add_finrank_ker`, `Module.finrank_fintype_fun_eq_card` and
`finrank_span_singleton`. The sum functional is written out here as `sumForm` because the estate had
no name for it — `∑ i, LinearMap.proj i`, whose kernel is the zero-sum hyperplane.

## What is proved

**`signlessLap_top_mulVec_eq_smul_iff`** — `Q x = (n − 2)·x` **iff** `∑x = 0`, with no hypothesis at
all; **`lapMatrix_top_mulVec_eq_smul_iff`** — and `L x = n·x` iff `∑x = 0`.

**`signlessLap_top_mulVec_eq_two_smul_iff`** — `Q x = (2n − 2)·x` **iff** `x` is constant, above one
vertex.

**`eigenvalue_signlessLap_top`** — **EVERY EIGENVALUE OF `Q` ON `K_n` IS `2n − 2` OR `n − 2`**, and
the statement takes **no cardinality hypothesis**: at one vertex the two coincide at `0` and at
none there is no eigenvector. **`eigenvalue_lapMatrix_top`** — and every eigenvalue of `L` is `0`
or `n`. **That is the completeness `SignlessCycleSpectrum` and `SignlessTorusSpectrum` both fence**
and neither has: on the cycle and the torus the characters are exhibited and nothing says they
exhaust.

**`sumForm`, `sumForm_apply`, `finrank_ker_sumForm`** — the sum functional, its value, and the
`(n − 1)`-dimensionality of its kernel, through surjectivity (`c` is the image of the constant
`c / n`).

**`eigenspace_signlessLap_top_eq_ker_sumForm`**, **`eigenspace_lapMatrix_top_eq_ker_sumForm`** —
both lower eigenspaces **are** that kernel, as submodule equalities in the `ker (toLin' M − μ •
id)` form this estate uses elsewhere.

**`eigenspace_signlessLap_top_eq_span`**, **`finrank_eigenspace_signlessLap_top_span`** — and `Q`'s
top eigenspace is the **span of the constant vector**, of dimension one.

**`finrank_eigenspaces_signlessLap_top_add`** — **SO THE TWO DIMENSIONS ADD TO `n`**: the spectrum
is `{2n − 2, (n − 2)^(n−1)}` with nothing left over.

## What is NOT here

* **NO `IsHermitian.eigenvalues` STATEMENT.** The spectrum is given as *which scalars have
  eigenvectors* and as *what the eigenspaces are*; it is **not** transported to Mathlib's sorted
  enumeration, which is an indexing question this estate has gone around before
  (`FieldLaplacianSimple`). Not attempted, no cost claimed (`ERRATUM 246`).
* **NO CHARACTERISTIC POLYNOMIAL.** `(X − (2n − 2))(X − (n − 2))^(n−1)` follows from the dimension
  count for a symmetric matrix and is **not** written: that step needs diagonalisability, which is
  exactly what the argument above avoids.
⚠ **THE REASON IN THE PARAGRAPH ABOVE IS FALSE AND THE PARAGRAPH IS KEPT AS WRITTEN**
(`ERRATUM 94`, `ERRATUM 508`, 2026-09-12). It does not matter what this file's argument avoids:
`Matrix.IsHermitian.charpoly_eq` supplies the diagonalisation for **every** Hermitian matrix, and
this estate had been citing it since 2026-08-26 (`HermitianSpectralMapping`, `RayleighPow`). What
was genuinely missing was the **grouping** — the product over the index type is free, and the
explicit factorisation with multiplicities as exponents needed the dimension-to-fibre bridge, now
`HermitianCharpoly.charpoly_eq_prod_pow_finrank`. **The absence itself was correctly declared**:
this file writes no characteristic polynomial.
* **NOTHING FOR THE CYCLE OR THE TORUS.** Their completeness fences stand: the case split here is
  special to `K_n`, where the off-diagonal part is the all-ones matrix and has rank one. Nothing
  here generalises to a graph whose adjacency matrix is not `J − I`.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and `OS1`
  in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `V` a `Fintype` with `DecidableEq`, and
`1 ≤ Fintype.card V` on the five statements that mention the constant vector or a dimension —
`sumForm_apply` and `finrank_ker_sumForm` take no `DecidableEq`, and **the two exhaustion theorems
take no cardinality hypothesis whatever**.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CompleteSpectrumTwoPoints

open Matrix Finset SimpleGraph LaplacianSignless CompleteSignlessSpectrum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The eigenvector equations, as characterisations -/

theorem signlessLap_top_mulVec_eq_smul_iff {x : V → ℝ} :
    signlessLap (⊤ : SimpleGraph V) *ᵥ x = ((Fintype.card V : ℝ) - 2) • x ↔ ∑ u, x u = 0 := by
  constructor
  · intro h
    classical
    rcases isEmpty_or_nonempty V with hV | hV
    · simp [Finset.univ_eq_empty]
    obtain ⟨v⟩ := hV
    have hv := congrFun h v
    rw [signlessLap_top_mulVec] at hv
    simpa using hv
  · exact fun h => signlessLap_top_mulVec_of_sum_eq_zero h

theorem lapMatrix_top_mulVec_eq_smul_iff {x : V → ℝ} :
    (⊤ : SimpleGraph V).lapMatrix ℝ *ᵥ x = (Fintype.card V : ℝ) • x ↔ ∑ u, x u = 0 := by
  constructor
  · intro h
    classical
    rcases isEmpty_or_nonempty V with hV | hV
    · simp [Finset.univ_eq_empty]
    obtain ⟨v⟩ := hV
    have hv := congrFun h v
    rw [lapMatrix_top_mulVec] at hv
    simp only [Pi.smul_apply, smul_eq_mul] at hv
    linarith
  · exact fun h => lapMatrix_top_mulVec_of_sum_eq_zero h

theorem signlessLap_top_mulVec_eq_two_smul_iff {x : V → ℝ} (h1 : 1 ≤ Fintype.card V) :
    signlessLap (⊤ : SimpleGraph V) *ᵥ x = (2 * (Fintype.card V : ℝ) - 2) • x
      ↔ ∃ c : ℝ, x = fun _ ↦ c := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast h1
    linarith
  constructor
  · intro h
    refine ⟨(∑ u, x u) / (Fintype.card V : ℝ), funext fun v ↦ ?_⟩
    have hv := congrFun h v
    rw [signlessLap_top_mulVec] at hv
    simp only [Pi.smul_apply, smul_eq_mul] at hv
    field_simp
    linarith
  · rintro ⟨c, rfl⟩
    funext v
    rw [signlessLap_top_mulVec]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Pi.smul_apply, smul_eq_mul]
    ring

/-! ## 2. Every eigenvalue is one of the two -/

theorem eigenvalue_signlessLap_top {μ : ℝ} {x : V → ℝ}
    (hx0 : x ≠ 0) (hx : signlessLap (⊤ : SimpleGraph V) *ᵥ x = μ • x) :
    μ = 2 * (Fintype.card V : ℝ) - 2 ∨ μ = (Fintype.card V : ℝ) - 2 := by
  classical
  set S := ∑ u, x u with hS
  have hrow : ∀ v, ((Fintype.card V : ℝ) - 2) * x v + S = μ * x v := by
    intro v
    have hv := congrFun hx v
    rw [signlessLap_top_mulVec] at hv
    simpa [hS] using hv
  by_cases hSz : S = 0
  · right
    obtain ⟨v, hv⟩ : ∃ v, x v ≠ 0 := by
      by_contra hall
      exact hx0 (funext fun v => by simpa using not_not.mp (not_exists.mp hall v))
    have hvx := hrow v
    rw [hSz, add_zero] at hvx
    exact (mul_right_cancel₀ hv hvx).symm
  · left
    have hsum : ((Fintype.card V : ℝ) - 2) * S + (Fintype.card V : ℝ) * S = μ * S := by
      have := Finset.sum_congr rfl fun v (_ : v ∈ Finset.univ) => hrow v
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, ← Finset.mul_sum] at this
      simpa [hS] using this
    have hfin : (2 * (Fintype.card V : ℝ) - 2) * S = μ * S := by linarith
    exact (mul_right_cancel₀ hSz hfin).symm

theorem eigenvalue_lapMatrix_top {μ : ℝ} {x : V → ℝ}
    (hx0 : x ≠ 0) (hx : (⊤ : SimpleGraph V).lapMatrix ℝ *ᵥ x = μ • x) :
    μ = 0 ∨ μ = (Fintype.card V : ℝ) := by
  classical
  set S := ∑ u, x u with hS
  have hrow : ∀ v, (Fintype.card V : ℝ) * x v - S = μ * x v := by
    intro v
    have hv := congrFun hx v
    rw [lapMatrix_top_mulVec] at hv
    simpa [hS] using hv
  by_cases hSz : S = 0
  · right
    obtain ⟨v, hv⟩ : ∃ v, x v ≠ 0 := by
      by_contra hall
      exact hx0 (funext fun v => by simpa using not_not.mp (not_exists.mp hall v))
    have hvx := hrow v
    rw [hSz, sub_zero] at hvx
    exact (mul_right_cancel₀ hv hvx).symm
  · left
    have hsum : (Fintype.card V : ℝ) * S - (Fintype.card V : ℝ) * S = μ * S := by
      have h1 := Finset.sum_congr rfl fun v (_ : v ∈ Finset.univ) => hrow v
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, ← Finset.mul_sum] at h1
      simpa [hS] using h1
    have hfin : (0 : ℝ) * S = μ * S := by linarith
    exact (mul_right_cancel₀ hSz hfin).symm

/-! ## 3. Both eigenspaces are named subspaces, so the multiplicities are counted -/

/-- The zero-sum hyperplane, as the kernel of the sum functional. -/
noncomputable def sumForm (V : Type*) [Fintype V] : (V → ℝ) →ₗ[ℝ] ℝ := ∑ i : V, LinearMap.proj i

omit [DecidableEq V] in
theorem sumForm_apply (x : V → ℝ) : sumForm V x = ∑ u, x u := by
  simp [sumForm]

theorem eigenspace_signlessLap_top_eq_ker_sumForm :
    LinearMap.ker (Matrix.toLin' (signlessLap (⊤ : SimpleGraph V))
        - ((Fintype.card V : ℝ) - 2) • LinearMap.id) = LinearMap.ker (sumForm V) := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero, Matrix.toLin'_apply, sumForm_apply]
  exact signlessLap_top_mulVec_eq_smul_iff

omit [DecidableEq V] in
theorem finrank_ker_sumForm (h1 : 1 ≤ Fintype.card V) :
    Module.finrank ℝ (LinearMap.ker (sumForm V)) = Fintype.card V - 1 := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast h1
    linarith
  have hsurj : Function.Surjective (sumForm V) := by
    intro c
    refine ⟨fun _ ↦ c / (Fintype.card V : ℝ), ?_⟩
    rw [sumForm_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hrange : Module.finrank ℝ (LinearMap.range (sumForm V)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have htotal := LinearMap.finrank_range_add_finrank_ker (sumForm V)
  rw [hrange, Module.finrank_fintype_fun_eq_card] at htotal
  omega

theorem eigenspace_lapMatrix_top_eq_ker_sumForm :
    LinearMap.ker (Matrix.toLin' ((⊤ : SimpleGraph V).lapMatrix ℝ)
        - (Fintype.card V : ℝ) • LinearMap.id) = LinearMap.ker (sumForm V) := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero, Matrix.toLin'_apply, sumForm_apply]
  exact lapMatrix_top_mulVec_eq_smul_iff

theorem eigenspace_signlessLap_top_eq_span (h1 : 1 ≤ Fintype.card V) :
    LinearMap.ker (Matrix.toLin' (signlessLap (⊤ : SimpleGraph V))
        - (2 * (Fintype.card V : ℝ) - 2) • LinearMap.id)
      = Submodule.span ℝ {(fun _ ↦ (1 : ℝ) : V → ℝ)} := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero, Matrix.toLin'_apply, Submodule.mem_span_singleton]
  rw [signlessLap_top_mulVec_eq_two_smul_iff h1]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by funext v; simp⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by funext v; simp⟩

theorem finrank_eigenspace_signlessLap_top_span (h1 : 1 ≤ Fintype.card V) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (⊤ : SimpleGraph V))
        - (2 * (Fintype.card V : ℝ) - 2) • LinearMap.id)) = 1 := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := ‹Nonempty V›
  rw [eigenspace_signlessLap_top_eq_span h1]
  refine finrank_span_singleton ?_
  intro h0
  have := congrFun h0 v
  simp at this

/-- **AND THE TWO EIGENSPACES FILL THE SPACE**, so there is no room for a third eigenvalue: the
dimensions are `1` and `card V − 1`. -/
theorem finrank_eigenspaces_signlessLap_top_add (h1 : 1 ≤ Fintype.card V) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (⊤ : SimpleGraph V))
          - (2 * (Fintype.card V : ℝ) - 2) • LinearMap.id))
        + Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (⊤ : SimpleGraph V))
          - ((Fintype.card V : ℝ) - 2) • LinearMap.id))
      = Fintype.card V := by
  rw [finrank_eigenspace_signlessLap_top_span h1, eigenspace_signlessLap_top_eq_ker_sumForm,
    finrank_ker_sumForm h1]
  omega

end CompleteSpectrumTwoPoints
