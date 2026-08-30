import MassiveTorusSpectrum
import CycleSpectralBound

/-!
# The top of the spectrum, and when it is reached: even side length, in every dimension

`MassiveTorusSpectrum` identified the **least** eigenvalue of `massive (torusGraph d (N+3)) m` as
`m²` and fenced itself in the obvious place:

> **No `IsGreatest` beside the `IsLeast`**, and deliberately: attaining `4d + m²` needs `cos = −1`
> on every axis at once, which is the parity question `CycleSpectralBound.cos_ne_neg_one_of_odd`
> settles at `d = 1` and no file settles in general.

That fence is one unit old and it is closed here. **The answer is a clean dichotomy**, and both
halves come from the frequency `k` with every coordinate at `n/2`, which exists exactly when the
side length is even.

> **`halfFreq`, `nuR_at_half`, `isGreatest_spectrum_real_of_even`** — at even side length the
> all-halfway frequency puts every cosine at `−1`, so `νR = 4d + m²`, and with
> `MassiveTorusSpectrum.nuR_le_two_degree` that value is the **greatest** eigenvalue.
>
> **`nuR_lt_of_odd`, `top_not_mem_spectrum_of_odd`** — at odd side length **no** frequency reaches
> it, in every dimension with at least one axis. The cosine never equals `−1`
> (`CycleSpectralBound.cos_ne_neg_one_of_odd`, a parity argument), so every term is *strictly*
> above `−2` and a non-empty sum of strict inequalities is strict.
>
> **`mem_spectrum_top_iff_even`** — hence the dichotomy as a biconditional: `4d + m²` is an
> eigenvalue **iff** the side length is even.
>
> **`isGreatest_signless_real`, `isLeast_signless_real_of_even`** — and `Q = D + A`'s spectrum is
> pinned at both ends by the same two frequencies, nearly free: the constant character gives
> `4d` at every side length, and the halfway character gives `0` at even ones. The second is
> `SignlessTorusSpectrum.nuQ_eq_zero_of_even` upgraded from *this value occurs* to *this value is
> the minimum*, which is what completeness buys.

## The estate already knew the odd case in a different shape, and the shapes are not connected

`LaplacianSharpEquality.torus_exists_quadForm_eq_iff_colorable` says a **vector** attains the
quadratic-form bound `xᵀLx = 2·(2d)·(x⬝ᵥx)` on the periodic lattice **iff** the graph is
two-colourable, and `torus_not_colorable_two_of_odd` says it is not, at odd side length, in every
dimension. **So the odd case's *quadratic-form* half has been known since that file was written**,
by chromatic number rather than by any spectrum.

**THE TWO ARE NOT THE SAME STATEMENT AND THIS FILE DOES NOT JOIN THEM.** That file says repeatedly
that it is about *a supplied vector, not an eigenvalue list*, and that identifying
`∃ x ≠ 0 with xᵀLx = 2Δ(x⬝ᵥx)` with *`2Δ` is the largest eigenvalue of `L`* is **not made** there.
Nothing here makes it either: what is proved below is about `massive`'s eigenvalues as a set, by a
parity argument on cosines, and it neither uses nor implies the colouring statement. **The bridge
— for this family, where both sides are now known, the quadratic-form bound is attained exactly
when the top eigenvalue is — is the obvious next unit and is not taken here.**

## What is NOT here

**Multiplicities are still not computed**, at either end.

**At odd side length no closed form for the actual maximum is given.** `nuR_lt_of_odd` says every
eigenvalue is strictly below `4d + m²`; the greatest one exists (a finite non-empty set of reals)
and **is not identified**. That is `CycleSpectralBound`'s own fence at `d = 1` — *"no closed form
for it is given, and none is needed for the refutation"* — and it is unchanged.

**No Loewner statement**, here as in the previous unit: an eigenvalue bound is not `massive ≼ c·1`
and the passage between them is not taken.

**The box is not reached.** A boundary and a non-constant degree, so no character family at all.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusSpectrumExtremes

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection LaplacianSignless
open CycleLaplacianSpectrum SignlessCycleSpectrum CycleSpectralBound
open TorusLaplacianSpectrum SignlessTorusSpectrum SignlessTorusComplete SignlessTorusReal
open MassiveTorusSpectrum

variable {d : ℕ}

/-! ## 1. The all-halfway frequency, as an object rather than a hypothesis -/

/-- **THE FREQUENCY WITH EVERY COORDINATE AT `n/2`**, which exists exactly when the side length is
even. `SignlessTorusSpectrum.nuQ_eq_zero_of_even` takes such a `k` as a hypothesis and never builds
one; both halves of this file need it built. -/
def halfFreq {M N : ℕ} (hN : N + 3 = 2 * M) : Site d (N + 3) := fun _ => ⟨M, by omega⟩

@[simp] theorem halfFreq_val {M N : ℕ} (hN : N + 3 = 2 * M) (i : Fin d) :
    ((halfFreq (d := d) hN) i).val = M := rfl

/-- The side length as a real number, in the form the angle lemmas want. -/
theorem cast_side {M N : ℕ} (hN : N + 3 = 2 * M) : ((N : ℝ) + 3) = 2 * M := by
  have h : ((N + 3 : ℕ) : ℝ) = ((2 * M : ℕ) : ℝ) := by rw [hN]
  push_cast at h
  linarith

/-- At the halfway frequency every angle is `π`, so every cosine is `−1`. -/
theorem cos_halfFreq {M N : ℕ} (hN : N + 3 = 2 * M) (i : Fin d) :
    Real.cos (2 * Real.pi * ((halfFreq (d := d) hN) i).val / ((N : ℝ) + 3)) = -1 := by
  have hM : 0 < M := by omega
  rw [halfFreq_val, cast_side hN, angle_at_half M hM, Real.cos_pi]

/-! ## 2. The top of the massive spectrum at even side length -/

/-- **THE HALFWAY FREQUENCY REACHES `4d + m²`.** -/
theorem nuR_at_half {M N : ℕ} (hN : N + 3 = 2 * M) (m : ℝ) :
    nuR N m (halfFreq (d := d) hN) = 4 * d + m ^ 2 := by
  have hterm : ∀ i : Fin d,
      2 * Real.cos (2 * Real.pi * ((halfFreq (d := d) hN) i).val / ((N : ℝ) + 3)) = -2 := by
    intro i
    rw [cos_halfFreq hN i]
    ring
  rw [nuR, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **SO AT EVEN SIDE LENGTH `4d + m²` IS THE GREATEST EIGENVALUE**, in every dimension. The bound
is `MassiveTorusSpectrum.nuR_le_two_degree` and the attainment is the line above; completeness is
what turns *an upper bound plus a witness* into *the greatest element of the spectrum*. -/
theorem isGreatest_spectrum_real_of_even {M N : ℕ} (hN : N + 3 = 2 * M) (m : ℝ) :
    IsGreatest {μ : ℝ | ∃ x : Site d (N + 3) → ℝ, x ≠ 0 ∧
        massive (torusGraph d (N + 3)) m *ᵥ x = μ • x} (4 * d + m ^ 2) := by
  constructor
  · exact (massive_eigenvalue_real_iff N m _).2 ⟨halfFreq hN, nuR_at_half hN m⟩
  · rintro μ hμ
    obtain ⟨k, hk⟩ := (massive_eigenvalue_real_iff N m μ).1 hμ
    exact hk ▸ nuR_le_two_degree N m k

/-! ## 3. And at odd side length nothing reaches it -/

/-- **EVERY EIGENVALUE IS STRICTLY BELOW `4d + m²` AT ODD SIDE LENGTH**, in every dimension with at
least one axis. Each cosine is at least `−1` and never equal to it, so each term of the sum is
strictly above `−2`; the hypothesis `0 < d` is what makes the sum non-empty, and it is needed —
at `d = 0` the sum is empty and the bound is an equality. -/
theorem nuR_lt_of_odd (N : ℕ) (hodd : Odd (N + 3)) (hd : 0 < d) (m : ℝ) (k : Site d (N + 3)) :
    nuR N m k < 4 * d + m ^ 2 := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hcast : ((N + 3 : ℕ) : ℝ) = (N : ℝ) + 3 := by push_cast; ring
  have hlt : ∑ _i : Fin d, (-2 : ℝ)
      < ∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3)) := by
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => ?_
    have hge := Real.neg_one_le_cos (2 * Real.pi * ((k i).val : ℝ) / ((N : ℝ) + 3))
    have hne : Real.cos (2 * Real.pi * ((k i).val : ℝ) / ((N : ℝ) + 3)) ≠ -1 := by
      have h := cos_ne_neg_one_of_odd (N := N + 3) (k := (k i).val) hodd
      rwa [hcast] at h
    have : (-1 : ℝ) < Real.cos (2 * Real.pi * ((k i).val : ℝ) / ((N : ℝ) + 3)) :=
      lt_of_le_of_ne hge (Ne.symm hne)
    linarith
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
  rw [nuR]
  linarith

/-- **SO AT ODD SIDE LENGTH `4d + m²` IS NOT AN EIGENVALUE AT ALL** — not merely unattained as a
supremum, absent from the spectrum. -/
theorem top_not_mem_spectrum_of_odd (N : ℕ) (hodd : Odd (N + 3)) (hd : 0 < d) (m : ℝ) :
    (4 * d + m ^ 2) ∉ {μ : ℝ | ∃ x : Site d (N + 3) → ℝ, x ≠ 0 ∧
        massive (torusGraph d (N + 3)) m *ᵥ x = μ • x} := by
  intro hmem
  obtain ⟨k, hk⟩ := (massive_eigenvalue_real_iff N m _).1 hmem
  exact absurd hk (ne_of_lt (nuR_lt_of_odd N hodd hd m k))

/-- **THE DICHOTOMY.** `4d + m²` is an eigenvalue of the massive Laplacian on the `d`-dimensional
periodic lattice **iff** the side length is even. -/
theorem mem_spectrum_top_iff_even (N : ℕ) (hd : 0 < d) (m : ℝ) :
    (4 * d + m ^ 2) ∈ {μ : ℝ | ∃ x : Site d (N + 3) → ℝ, x ≠ 0 ∧
        massive (torusGraph d (N + 3)) m *ᵥ x = μ • x} ↔ Even (N + 3) := by
  constructor
  · intro hmem
    rcases Nat.even_or_odd (N + 3) with he | ho
    · exact he
    · exact absurd hmem (top_not_mem_spectrum_of_odd N ho hd m)
  · rintro ⟨M, hM⟩
    have hN : N + 3 = 2 * M := by omega
    exact (isGreatest_spectrum_real_of_even hN m).1

/-! ## 4. Both ends of `Q`'s spectrum, from the same two frequencies -/

/-- At the zero frequency every angle is `0` and `νQ` is `4d`. -/
@[simp] theorem nuQR_at_zero (N : ℕ) : nuQR (d := d) N 0 = 4 * d := by
  rw [nuQR]
  simp
  ring

/-- `νQ` is at most `4d`, each cosine being at most `1`. -/
theorem nuQR_le (N : ℕ) (k : Site d (N + 3)) : nuQR N k ≤ 4 * d := by
  have hle : ∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3))
      ≤ ∑ _i : Fin d, (2 : ℝ) :=
    Finset.sum_le_sum fun i _ => by
      have := Real.cos_le_one (2 * Real.pi * (k i).val / ((N : ℝ) + 3))
      linarith
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  rw [nuQR]
  linarith

/-- **THE GREATEST EIGENVALUE OF `Q = D + A` ON THE PERIODIC LATTICE IS `4d`**, at every side length
and in every dimension — the constant character, which is an eigenvector of `Q` at twice the degree
and of `L` at zero. -/
theorem isGreatest_signless_real (N : ℕ) :
    IsGreatest {μ : ℝ | ∃ x : Site d (N + 3) → ℝ, x ≠ 0 ∧
        signlessLap (torusGraph d (N + 3)) *ᵥ x = μ • x} (4 * d) := by
  constructor
  · exact (eigenvalue_real_iff N _).2 ⟨0, nuQR_at_zero N⟩
  · rintro μ hμ
    obtain ⟨k, hk⟩ := (eigenvalue_real_iff N μ).1 hμ
    exact hk ▸ nuQR_le N k

/-- At even side length the halfway frequency sends `νQ` to zero. This is
`SignlessTorusSpectrum.nuQ_eq_zero_of_even` with the frequency supplied rather than assumed. -/
theorem nuQR_at_half {M N : ℕ} (hN : N + 3 = 2 * M) :
    nuQR (d := d) N (halfFreq hN) = 0 := by
  rw [nuQR]
  exact nuQ_eq_zero_of_even hN _ fun _ => rfl

/-- **AND AT EVEN SIDE LENGTH `0` IS THE LEAST EIGENVALUE OF `Q`**, in every dimension. The bound is
`SignlessTorusSpectrum.nuQ_real_nonneg` and the attainment is the line above. **This is the upgrade
completeness buys**: that file exhibited a frequency where `νQ` vanishes, which says `0` occurs;
that `0` is the *minimum* of the spectrum is a statement about every eigenvalue. -/
theorem isLeast_signless_real_of_even {M N : ℕ} (hN : N + 3 = 2 * M) :
    IsLeast {μ : ℝ | ∃ x : Site d (N + 3) → ℝ, x ≠ 0 ∧
        signlessLap (torusGraph d (N + 3)) *ᵥ x = μ • x} 0 := by
  constructor
  · exact (eigenvalue_real_iff N _).2 ⟨halfFreq hN, nuQR_at_half hN⟩
  · rintro μ hμ
    obtain ⟨k, hk⟩ := (eigenvalue_real_iff N μ).1 hμ
    rw [← hk, nuQR]
    exact nuQ_real_nonneg N k

end TorusSpectrumExtremes
