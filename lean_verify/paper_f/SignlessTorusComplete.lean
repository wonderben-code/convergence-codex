import SignlessTorusSpectrum
import TorusGreenFormula

/-!
# Completeness: the characters are a basis, and those eigenvalues are *all* of them

`SignlessTorusSpectrum` computed eigenvalues of `Q = D + A` on the periodic lattice in every
dimension, and fenced itself in the honest place: **every statement there is "this vector is an
eigenvector with this eigenvalue", and none is "these are all of them".** That fence is closed
here.

**AND THE UNIT EXISTS BECAUSE THE PREVIOUS ONE MISREAD THE METHOD.** Entry 24's `KEY GENERATOR`
named this leg and **declined it**, on the reading that *"a B is retried once and then the queue
resumes"*. `PROOF_STRATEGY` §3 says the opposite in terms — *"a partial C is a legitimate B — and
therefore a reason to keep going, not to stop"*, and *"the moment B lands, immediately re-attempt
B → C … you will never again have as much of it loaded in working memory as you do right now"*.
A spectrum without completeness is exactly a partial C. `ERRATUM 350`.

> **`chiDBasis`** — the `n^d` product characters are a **basis** of `Site d n → ℂ`. The spanning
> half is `TorusGreenFormula.single_eq_sum_chiD`, which was proved for the Green's function and is
> reused rather than reproved; linear independence comes free from the cardinality, since a
> spanning family of `finrank` many vectors is a basis.
>
> **`eigenvalue_iff`** — `μ` is an eigenvalue of `Q` on `torusGraph d (N+3)` **iff** `μ = νQ k` for
> some frequency `k`. The forward direction is the new content: expand an eigenvector in the basis,
> and every coefficient is killed by a factor `νQ k − μ` that is assumed non-zero.
>
> **`spectrum_eq_range_nuQ`** — the same statement as an equality of sets, which is what *the
> spectrum* means.

**WHAT IS STILL NOT HERE.** Multiplicities are not computed: two frequencies can share an
eigenvalue and nothing below counts how often. The **box** is not reached and is not close — a
boundary and a non-constant degree, so no character family at all. And this is `Q` over `ℂ`; the
real symmetric matrix has the same eigenvalues, but the transfer is not made and no file claims it.
-/

namespace SignlessTorusComplete

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection CycleLaplacianSpectrum
open LaplacianSignless TorusLaplacianSpectrum TorusGreenFormula SignlessTorusSpectrum

variable {d : ℕ}

/-! ## 1. The characters are a basis -/

/-- The product characters span, because the standard basis vectors are in their span — which is
`TorusGreenFormula.single_eq_sum_chiD`, proved there to invert the Green's function and reused
here rather than reproved. -/
theorem top_le_span_chiD {n : ℕ} (hn : n ≠ 0) :
    ⊤ ≤ Submodule.span ℂ (Set.range (chiD (d := d) n)) := by
  classical
  rw [← (Pi.basisFun ℂ (Site d n)).span_eq, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  rw [Pi.basisFun_apply, single_eq_sum_chiD hn y]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

/-- **THE CHARACTERS ARE A BASIS.** `n^d` vectors spanning a space of dimension `n^d`; linear
independence then follows from the cardinality alone, by
`basisOfTopLeSpanOfCardEqFinrank`, and needs no argument of its own. -/
noncomputable def chiDBasis {n : ℕ} (hn : n ≠ 0) :
    Module.Basis (Site d n) ℂ (Site d n → ℂ) :=
  basisOfTopLeSpanOfCardEqFinrank _ (top_le_span_chiD hn)
    (by rw [Module.finrank_fintype_fun_eq_card])

@[simp] theorem chiDBasis_apply {n : ℕ} (hn : n ≠ 0) (k : Site d n) :
    chiDBasis (d := d) hn k = chiD n k := by
  rw [chiDBasis, coe_basisOfTopLeSpanOfCardEqFinrank]

/-! ## 2. Those eigenvalues are all of them -/

/-- **`μ` IS AN EIGENVALUE OF `Q` IFF IT IS `νQ` AT SOME FREQUENCY.** The reverse direction is
`SignlessTorusSpectrum.cx_signlessLap_mulVec_chiD` with `chiD_ne_zero`. The forward direction is
the content: expand the eigenvector in the character basis, apply `Q`, and compare coefficients —
each is multiplied by `νQ k − μ`, which is non-zero by assumption, so every coefficient vanishes
and the eigenvector is `0`. -/
theorem eigenvalue_iff (N : ℕ) (μ : ℂ) :
    (∃ x : Site d (N + 3) → ℂ, x ≠ 0 ∧
        MatrixLoewner.cx (signlessLap (torusGraph d (N + 3))) *ᵥ x = μ • x)
      ↔ ∃ k : Site d (N + 3), nuQ N k = μ := by
  classical
  have hn : (N + 3 : ℕ) ≠ 0 := by omega
  constructor
  · rintro ⟨x, hx0, hx⟩
    by_contra hex
    have hnone : ∀ k : Site d (N + 3), nuQ N k ≠ μ := fun k hk => hex ⟨k, hk⟩
    apply hx0
    set b := chiDBasis (d := d) hn with hb
    have hQ : ∀ y : Site d (N + 3) → ℂ,
        MatrixLoewner.cx (signlessLap (torusGraph d (N + 3))) *ᵥ y
          = Matrix.toLin' (MatrixLoewner.cx (signlessLap (torusGraph d (N + 3)))) y :=
      fun y => (Matrix.toLin'_apply _ y).symm
    have hrepr : ∑ j, b.repr x j • b j = x := b.sum_repr x
    have h1 : Matrix.toLin' (MatrixLoewner.cx (signlessLap (torusGraph d (N + 3)))) x
        = ∑ j, (nuQ N j * b.repr x j) • b j := by
      conv_lhs => rw [← hrepr]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, hb, chiDBasis_apply, ← hQ, cx_signlessLap_mulVec_chiD, smul_smul, mul_comm]
    have h2 : μ • x = ∑ j, (μ * b.repr x j) • b j := by
      conv_lhs => rw [← hrepr]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_smul _ _ _
    have hsum : ∑ j, ((nuQ N j - μ) * b.repr x j) • b j = 0 := by
      have hsplit : ∑ j, ((nuQ N j - μ) * b.repr x j) • b j
          = (∑ j, (nuQ N j * b.repr x j) • b j) - ∑ j, (μ * b.repr x j) • b j := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← sub_smul, sub_mul]
      rw [hsplit, ← h1, ← h2, ← hQ, hx, sub_self]
    have hzero : ∀ k, (nuQ N k - μ) * b.repr x k = 0 :=
      Fintype.linearIndependent_iff.1 b.linearIndependent _ hsum
    have hcoeff : ∀ k, b.repr x k = 0 := by
      intro k
      rcases mul_eq_zero.1 (hzero k) with h | h
      · exact absurd (sub_eq_zero.1 h) (hnone k)
      · exact h
    have hr : b.repr x = 0 := by ext k; exact hcoeff k
    have := congrArg b.repr.symm hr
    simpa using this
  · rintro ⟨k, rfl⟩
    exact ⟨chiD (N + 3) k, fun h => chiD_ne_zero (N + 3) k k (congrFun h k),
      cx_signlessLap_mulVec_chiD N k⟩

/-- **THE SPECTRUM, AS A SET.** The same statement as `eigenvalue_iff` in the form the word
*spectrum* means: the set of eigenvalues of `Q` on the `d`-dimensional periodic lattice **is**
the range of `νQ`. **This theorem exists because the header cited it and the first draft of the
file did not contain it** — `ERRATUM 343`'s defect exactly, and its repair is to prove the
citation rather than cut the sentence. `--cites-lean` could not have caught it: that mode skips
every backticked name without a dot, which is the shape a file uses to cite its own theorems. -/
theorem spectrum_eq_range_nuQ (N : ℕ) :
    {μ : ℂ | ∃ x : Site d (N + 3) → ℂ, x ≠ 0 ∧
        MatrixLoewner.cx (signlessLap (torusGraph d (N + 3))) *ᵥ x = μ • x}
      = Set.range (nuQ (d := d) N) := by
  ext μ
  exact eigenvalue_iff N μ

end SignlessTorusComplete
