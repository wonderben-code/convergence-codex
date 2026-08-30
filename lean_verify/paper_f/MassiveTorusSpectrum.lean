import SignlessTorusReal

/-!
# The massive Laplacian's spectrum on the periodic lattice, over `ℝ`, and its least point

`TorusLaplacianSpectrum` computed **eigenvalues** of `massive (torusGraph d n) m` in every
dimension and stopped where every spectrum file in this estate had stopped:

> every statement there is *this vector is an eigenvector with this eigenvalue*, and none is
> *these are all of them*.

`SignlessTorusComplete` closed that fence for the **signless** Laplacian `Q = D + A`, and in doing
so extracted `eigenvalue_iff_of_basis` — *a matrix diagonalised by a basis has exactly the
eigenvalues on that basis* — which mentions no graph, no `Q`, and no character. `SignlessTorusReal`
then extracted `real_eigenvalue_iff_cx`, which removes the complexification from any real matrix's
spectrum. **This file spends both levers on the operator they were built next to but not for**: the
massive Laplacian, whose eigenvectors are the *same* basis `chiDBasis` and whose eigenvector
equation `TorusLaplacianSpectrum.cx_massive_mulVec_chiD` has been on the shelf since 27 August.

> **`massive_eigenvalue_iff`** — `μ` is an eigenvalue of `massive (torusGraph d (N+3)) m` over `ℂ`
> **iff** `μ = ν N m k` at some frequency `k`. Four lines, because the general lemma does the work.
>
> **`nuR`, `massive_eigenvalue_real_iff`, `spectrum_real_eq_range_nuR`** — the same over `ℝ`, for
> the real matrix and real scalars, with no complexification in the statement:
> `μ = 2d + m² − 2 Σᵢ cos(2π kᵢ / n)`.
>
> **`sq_le_nuR`** and **`nuR_at_zero`** — every eigenvalue is at least `m²`, because each cosine is
> at most `1`; and the constant character attains `m²` exactly. Hence
>
> **`isLeast_spectrum_real`** — the **least** eigenvalue of the massive Laplacian on the
> `d`-dimensional periodic lattice **is `m²`**, in every dimension and at every side length `≥ 3`.
> This is the statement completeness was needed for: a lower bound on a *set* of eigenvalues is not
> available from an eigenvector, however many you exhibit.

## What was new here and what was carried

**The mathematics of the diagonalisation is not new in this unit** — the basis is
`SignlessTorusComplete.chiDBasis` and the eigenvector equation is `cx_massive_mulVec_chiD`, both
already proved. What is new is that the **completeness** statement is now made for `massive`, and
the least point of its spectrum is identified. `CycleLaplacianSpectrum.eigenvalue_pos` proved
`0 < 2 + m² − 2cos(2πk/N)` at `d = 1` for `m ≠ 0`, and `eigenvalue_at_zero` proved the value at
`k = 0` **is** `m²`; neither is a statement about the spectrum as a set, because at that point no
file knew the list was complete.

## What is NOT here

**Multiplicities are not computed.** Two frequencies can share an eigenvalue and nothing below
counts how often, over `ℝ` or over `ℂ`. `spectrum_real_eq_range_nuR` is an equality of **sets**.

**No Loewner statement is derived.** `nuR_le_two_degree` bounds every eigenvalue by `4d + m²`,
which is `2Δ + m²` at this graph's degree `Δ = 2d` — the same number `LaplacianDegreeBound` bounds
the *matrix* by — but **passing from an eigenvalue bound to `massive ≼ c·1` is a separate step and
is not taken here**; `CycleSpectralBound.massive_le_smul_one_of_eigenvalues_le` is what that step
looks like, and it is `d = 1` only. Nothing in this file is used to reprove the degree bound and
nothing here supersedes it.

**No greatest point.** `nuR_le_two_degree` is an upper bound, not an attained one: whether some
frequency reaches `4d + m²` needs `cos = −1` at every axis at once, which is the parity question
`CycleSpectralBound.cos_ne_neg_one_of_odd` answers at `d = 1` and **no file answers here**. So
`IsLeast` has no `IsGreatest` beside it, deliberately.

**The box is still not reached** — a boundary and a non-constant degree, so no character family at
all — and the side length is still `N + 3`, because `torusGraph`'s degree formula needs `3 ≤ n`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace MassiveTorusSpectrum

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection
open TorusLaplacianSpectrum SignlessTorusComplete SignlessTorusReal

variable {d : ℕ}

/-! ## 1. Completeness over `ℂ` -/

/-- **`μ` IS AN EIGENVALUE OF THE MASSIVE LAPLACIAN IFF IT IS `ν` AT SOME FREQUENCY.** The
characters are a basis (`chiDBasis`) and they diagonalise `massive`
(`cx_massive_mulVec_chiD`), so `eigenvalue_iff_of_basis` applies with nothing left to do. -/
theorem massive_eigenvalue_iff (N : ℕ) (m : ℝ) (μ : ℂ) :
    (∃ x : Site d (N + 3) → ℂ, x ≠ 0 ∧
        MatrixLoewner.cx (massive (torusGraph d (N + 3)) m) *ᵥ x = μ • x)
      ↔ ∃ k : Site d (N + 3), nu N m k = μ := by
  classical
  have hn : (N + 3 : ℕ) ≠ 0 := by omega
  refine eigenvalue_iff_of_basis _ (chiDBasis (d := d) hn) (nu N m) (fun k => ?_) μ
  rw [chiDBasis_apply]
  exact cx_massive_mulVec_chiD N m k

/-- **THE COMPLEX SPECTRUM AS A SET.** -/
theorem spectrum_eq_range_nu (N : ℕ) (m : ℝ) :
    {μ : ℂ | ∃ x : Site d (N + 3) → ℂ, x ≠ 0 ∧
        MatrixLoewner.cx (massive (torusGraph d (N + 3)) m) *ᵥ x = μ • x}
      = Set.range (nu (d := d) N m) := by
  ext μ
  exact massive_eigenvalue_iff N m μ

/-! ## 2. The same over `ℝ` -/

/-- The eigenvalue as a **real** number: `2d + m²` less one cosine per axis. This is
`TorusLaplacianSpectrum.nu_eq_real`'s right-hand side given a name. -/
noncomputable def nuR (N : ℕ) (m : ℝ) (k : Site d (N + 3)) : ℝ :=
  2 * d + m ^ 2 - ∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3))

theorem nu_eq_ofReal_nuR (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    nu N m k = ((nuR N m k : ℝ) : ℂ) :=
  nu_eq_real N m k

/-- **THE REAL MATRIX, THE REAL SCALARS.** A real `μ` is an eigenvalue of
`massive (torusGraph d (N+3)) m` **iff** `μ = 2d + m² − 2 Σᵢ cos(2π kᵢ / n)` at some frequency.
No complexification appears in the statement. -/
theorem massive_eigenvalue_real_iff (N : ℕ) (m : ℝ) (μ : ℝ) :
    (∃ x : Site d (N + 3) → ℝ, x ≠ 0 ∧
        massive (torusGraph d (N + 3)) m *ᵥ x = μ • x)
      ↔ ∃ k : Site d (N + 3), nuR N m k = μ := by
  rw [real_eigenvalue_iff_cx, massive_eigenvalue_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [nu_eq_ofReal_nuR] at hk; exact_mod_cast hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [nu_eq_ofReal_nuR, hk]⟩

/-- **THE REAL SPECTRUM AS A SET.** -/
theorem spectrum_real_eq_range_nuR (N : ℕ) (m : ℝ) :
    {μ : ℝ | ∃ x : Site d (N + 3) → ℝ, x ≠ 0 ∧
        massive (torusGraph d (N + 3)) m *ᵥ x = μ • x}
      = Set.range (nuR (d := d) N m) := by
  ext μ
  exact massive_eigenvalue_real_iff N m μ

/-! ## 3. Where the spectrum sits, and its least point -/

/-- **EVERY EIGENVALUE IS AT LEAST `m²`**, because each of the `d` cosines is at most `1`. -/
theorem sq_le_nuR (N : ℕ) (m : ℝ) (k : Site d (N + 3)) : m ^ 2 ≤ nuR N m k := by
  have hle : ∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3))
      ≤ ∑ _i : Fin d, (2 : ℝ) :=
    Finset.sum_le_sum fun i _ => by
      have := Real.cos_le_one (2 * Real.pi * (k i).val / ((N : ℝ) + 3))
      linarith
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  rw [nuR]
  linarith

/-- **AND AT MOST `4d + m²`**, because each cosine is at least `−1`. At this graph's degree
`Δ = 2d` that number is `2Δ + m²`, which is what `LaplacianDegreeBound` bounds the **matrix** by;
the passage from this bound to that one is a separate step and is not taken here. -/
theorem nuR_le_two_degree (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    nuR N m k ≤ 4 * d + m ^ 2 := by
  have hge : ∑ _i : Fin d, (-2 : ℝ)
      ≤ ∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3)) :=
    Finset.sum_le_sum fun i _ => by
      have := Real.neg_one_le_cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3))
      linarith
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hge
  rw [nuR]
  linarith

/-- **THE CONSTANT CHARACTER ATTAINS `m²`.** At the zero frequency every angle is `0`, every
cosine is `1`, and the `2d` from the degree cancels exactly. -/
@[simp] theorem nuR_at_zero (N : ℕ) (m : ℝ) : nuR (d := d) N m 0 = m ^ 2 := by
  rw [nuR]
  simp
  ring

/-- **THE LEAST EIGENVALUE OF THE MASSIVE LAPLACIAN ON THE PERIODIC LATTICE IS `m²`**, in every
dimension and at every side length at least three. This is the statement completeness was needed
for: exhibiting eigenvectors, however many, never bounds a spectrum from below — the bound
quantifies over *all* eigenvalues, and that quantifier is `massive_eigenvalue_real_iff`'s forward
direction. -/
theorem isLeast_spectrum_real (N : ℕ) (m : ℝ) :
    IsLeast {μ : ℝ | ∃ x : Site d (N + 3) → ℝ, x ≠ 0 ∧
        massive (torusGraph d (N + 3)) m *ᵥ x = μ • x} (m ^ 2) := by
  constructor
  · exact (massive_eigenvalue_real_iff N m (m ^ 2)).2 ⟨0, nuR_at_zero N m⟩
  · rintro μ hμ
    obtain ⟨k, hk⟩ := (massive_eigenvalue_real_iff N m μ).1 hμ
    exact hk ▸ sq_le_nuR N m k

end MassiveTorusSpectrum
