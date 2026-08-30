import TorusLaplacianSpectrum
import SignlessCycleSpectrum

/-!
# The spectrum of `Q = D + A` on the periodic lattice, in every dimension

`SignlessCycleSpectrum` removed the standing fence — *no eigenvalue of `D + A` is computed anywhere
in this estate* — at one family, the cycle, and closed by naming the next rung: the **torus in every
dimension**, where `TorusLaplacianSpectrum` has already done for `L` exactly what
`CycleLaplacianSpectrum` did for the ring. **This is that rung**, and the prediction was right about
the shape: the product characters are eigenvectors of `Q` too, with one cosine per axis.

> **`cx_signlessLap_mulVec_chiD`** — `Q χ_k = νQ · χ_k` on `torusGraph d (N+3)`, in every
> dimension.
>
> **`nuQ_eq_real`** — `νQ = 2d + 2 Σᵢ cos(2π kᵢ / n)`, real: the `d = 1` answer with a sum in
> place of its single term.
>
> **`nuQ_add_nu`** — and `νQ + ν = 4d + m²` at every frequency, which is
> `LaplacianSignless.signlessLap_add_lapMatrix`'s `Q + L = 2D` on a `2d`-regular graph, read one
> eigenvector at a time. **The check the cycle file made at `d = 1`, in every dimension.**
>
> **`nuQ_eq_zero_of_even`** — at an even side length and the all-halfway frequency the eigenvalue
> is **exactly `0`**. Which `LaplacianSignlessDefinite.torus_even_not_signlessLap_posDef` already
> says, by a colouring argument with no trigonometry in it. **Two routes meeting at a computed
> number, in every dimension.**

**WHAT THIS COSTS AND WHY IT IS SMALL, said rather than dressed up.** `Q` and `L` differ in one
sign, and `TorusLaplacianSpectrum` already carries every hard step — `neighborFinset_eq_image`
(the neighbours are the `2d` steps, which the degree theorem does not give), `stepT_injective`,
and the factorisation of the product character along a step. This file re-uses all of them and
changes a `−` to a `+`. **The fence stood because nobody had written the plus sign.**

**FENCED, and the fence is what it was on the cycle.** **Completeness is not claimed**: that the
`n^d` product characters exhaust the spectrum needs them to span, which
`TorusGreenFormula.sum_chiD_mul_inv` has and which is **not invoked here**. Every statement below
is *this vector is an eigenvector with this eigenvalue*, and none is *these are all of them*. The
**box** is not reached and is not close — it has a boundary and a non-constant degree, so no
character family at all — and no eigenvalue of `Q` is known at any graph that is not a cycle or a
torus.
-/

namespace SignlessTorusSpectrum

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection CycleLaplacianSpectrum
open LaplacianSignless SignlessCycleSpectrum TorusLaplacianSpectrum

variable {d : ℕ}

/-! ## 1. The eigenvalue -/

/-- The signless eigenvalue at frequency `k`: the degree `2d`, **plus** one term per axis, where
`TorusLaplacianSpectrum.nu` has the degree plus the mass **minus** the same sum. -/
noncomputable def nuQ (N : ℕ) (k : Site d (N + 3)) : ℂ :=
  (2 * d : ℂ) + ∑ i : Fin d, (zeta (N + 3) ^ (k i).val + (zeta (N + 3) ^ (k i).val)⁻¹)

/-! ## 2. The eigenvector equation -/

/-- **THE PRODUCT CHARACTERS ARE EIGENVECTORS OF `D + A` ON THE PERIODIC LATTICE, IN EVERY
DIMENSION.** The proof is `TorusLaplacianSpectrum.cx_massive_mulVec_chiD`'s, with the neighbour sum
entering with the other sign and no mass term. -/
theorem cx_signlessLap_mulVec_chiD (N : ℕ) (k : Site d (N + 3)) :
    MatrixLoewner.cx (signlessLap (torusGraph d (N + 3))) *ᵥ chiD (N + 3) k
      = nuQ N k • chiD (N + 3) k := by
  classical
  have hn : 3 ≤ N + 3 := by omega
  funext p
  rw [cx_signlessLap_mulVec, neighborFinset_eq_image hn p,
    Finset.sum_image fun t _ t' _ h => TorusEmbeddingAllDims.stepT_injective hn p h]
  have hdeg : ((torusGraph d (N + 3)).degree p : ℂ) = 2 * d := by
    rw [TorusEmbeddingAllDims.torusGraph_degree_eq hn p]
    push_cast; ring
  have hsum : (∑ t : Fin d × Bool, chiD (N + 3) k (TorusDecay.stepT p t.1 t.2))
      = (∑ i : Fin d, (zeta (N + 3) ^ (k i).val + (zeta (N + 3) ^ (k i).val)⁻¹))
          * chiD (N + 3) k p := by
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool, chiD_stepT_true, chiD_stepT_false]
    ring
  rw [hdeg, hsum, Pi.smul_apply, smul_eq_mul, nuQ]
  ring

/-! ## 3. The eigenvalue is real, and it is the classical one -/

/-- **THE EIGENVALUE IS REAL**, and is `2d + 2 Σᵢ cos(2π kᵢ / n)` — one cosine per axis, the sign
being the only difference from `TorusLaplacianSpectrum.nu_eq_real`. -/
theorem nuQ_eq_real (N : ℕ) (k : Site d (N + 3)) :
    nuQ N k
      = ((2 * d
          + ∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3)) : ℝ) : ℂ) := by
  rw [nuQ, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => zeta_pow_add_inv N (k i)]
  push_cast
  ring

/-- **AND IT IS NON-NEGATIVE**, each cosine being at least `−1`, so the sum is at least `−2d`.
Deliberately not strict: §5 exhibits where it is zero. -/
theorem nuQ_real_nonneg (N : ℕ) (k : Site d (N + 3)) :
    0 ≤ 2 * d + ∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3)) := by
  have h : (∑ _i : Fin d, (-2 : ℝ))
      ≤ ∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have := Real.neg_one_le_cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3))
    linarith
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  linarith

/-! ## 4. `Q + L = 2D`, one eigenvector at a time, in every dimension -/

/-- **THE TWO EIGENVALUES SUM TO `4d + m²` AT EVERY FREQUENCY.** `signlessLap_add_lapMatrix` says
`Q + L = 2D` as matrices and the torus is `2d`-regular, so on a shared eigenvector the two
eigenvalues must sum to `2·(2d)` plus the mass the massive operator carries. They do, and the
character terms cancel identically — **the cycle file's check, in every dimension.** -/
theorem nuQ_add_nu (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    nuQ N k + nu N m k = (4 * d : ℂ) + (m : ℂ) ^ 2 := by
  rw [nuQ, nu]
  ring

/-! ## 5. The even torus, where the eigenvalue is exactly zero -/

/-- **AT AN EVEN SIDE LENGTH AND THE ALL-HALFWAY FREQUENCY THE EIGENVALUE IS `0`**, in every
dimension: each axis contributes `2cos(π) = −2` and there are `d` of them, against the degree `2d`.
The eigenvector is `chiD`, which is nowhere zero (`TorusLaplacianSpectrum.chiD_ne_zero`), so this
is a genuine zero of the spectrum and not a vacuous identity.
`LaplacianSignlessDefinite.torus_even_not_signlessLap_posDef` says `Q` is not positive definite
there by two-colouring the torus — **no trigonometry anywhere in that argument**, and the two now
agree at a number. -/
theorem nuQ_eq_zero_of_even {M N : ℕ} (hN : N + 3 = 2 * M) (k : Site d (N + 3))
    (hk : ∀ i, (k i).val = M) :
    2 * d + ∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3))
      = 0 := by
  have hM : 0 < M := by omega
  have hcast : ((N : ℝ) + 3) = 2 * M := by
    have h : ((N + 3 : ℕ) : ℝ) = ((2 * M : ℕ) : ℝ) := by rw [hN]
    push_cast at h
    linarith
  have hterm : ∀ i : Fin d,
      2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3)) = -2 := by
    intro i
    rw [hk i, hcast, angle_at_half M hM, Real.cos_pi]
    ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end SignlessTorusSpectrum
