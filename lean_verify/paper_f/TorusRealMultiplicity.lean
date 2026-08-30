import RealComplexKernel

/-!
# The multiplicities, over `ℝ`, where the matrices actually live

`TorusMultiplicity` computed every eigenspace dimension on the periodic lattice and fenced itself
in the place the whole chain had been fenced:

> **These are eigenspace dimensions over `ℂ`.** The real matrix has the same eigenvalues by
> `real_eigenvalue_iff_cx`, but **no claim is made here that real eigenspaces have the same
> dimension** — that is a transfer of `finrank`, not of membership.

`RealComplexKernel.finrank_eigenspace_cx` is that transfer, and this file spends it. **Every
multiplicity statement in the chain now holds for the real matrix, with no complexification in the
statement**, and the counting formula is stated against `νR` and `νQR` — the *real* eigenvalue
functions — rather than against their complex originals.

> **`finrank_eigenspace_massive_real`** — for a **real** `μ`, the dimension of the real eigenspace
> of `massive (torusGraph d (N+3)) m` at `μ` is the number of frequencies `k` with `νR k = μ`.
> **`finrank_eigenspace_signless_real`** — the same for `Q = D + A` and `νQR`.
>
> **`ground_state_simple_real`** — so the ground state of the free lattice field is unique **over
> `ℝ`**: the real eigenspace at `m²` is one dimensional, in every dimension and at every side
> length at least three.
>
> **`top_eigenvalue_simple_real`, `signless_zero_simple_real`** — and both extremes at even side
> length are simple over `ℝ` too.

**WHAT IS NEW HERE IS THE FIELD AND NOTHING ELSE.** No new eigenvalue is computed, no new
frequency is counted, and every arithmetical fact below was proved in the two previous units. What
changes is that a caller holding the real matrix — which is the matrix the estate's Loewner order,
its Green's function and its Gaussian field are all built on — no longer has to pass through `ℂ` to
learn how big an eigenspace is.

## What is NOT here

**Still no multiplicity at any interior eigenvalue.** The counting question is answered here at the
two extremes and **nowhere else**, exactly as it was over `ℂ`; the real statement inherits the
complex one's silence.

**No eigenvector is exhibited over `ℝ`.** The dimensions transfer; the *bases* do not, and nothing
below names a real eigenvector. The constant vector is the obvious one at `m²` and **it is not
identified as spanning that eigenspace here**.

**Nothing about non-real eigenvalues.** `finrank_eigenspace_cx` is a statement about a real `μ`,
and a real matrix's complex eigenspaces at non-real points have no real counterpart at all. Those
do not arise for these two operators, both being symmetric — but **that symmetry is not used below
and no such statement is made**.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusRealMultiplicity

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection LaplacianSignless
open TorusLaplacianSpectrum SignlessTorusSpectrum SignlessTorusComplete SignlessTorusReal
open MassiveTorusSpectrum TorusMultiplicity TorusTopSimple RealComplexKernel

variable {d : ℕ}

/-! ## 1. The counting formula over `ℝ` -/

/-- **THE REAL EIGENSPACE OF THE MASSIVE LAPLACIAN AT A REAL `μ`** has dimension equal to the
number of frequencies at which `νR` takes the value `μ`. The complex count is
`TorusMultiplicity.finrank_eigenspace_massive`; the transfer is
`RealComplexKernel.finrank_eigenspace_cx`; and the index set is re-expressed against `νR` so that
no complex number appears in the statement. -/
theorem finrank_eigenspace_massive_real (N : ℕ) (m μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (massive (torusGraph d (N + 3)) m) - μ • LinearMap.id))
      = Nat.card {k : Site d (N + 3) // nuR N m k = μ} := by
  rw [← finrank_eigenspace_cx, finrank_eigenspace_massive N m ((μ : ℝ) : ℂ)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun k => ?_)
  rw [nu_eq_ofReal_nuR, Complex.ofReal_inj]

/-- **AND THE SAME FOR `Q = D + A`**, against `νQR`. -/
theorem finrank_eigenspace_signless_real (N : ℕ) (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap (torusGraph d (N + 3))) - μ • LinearMap.id))
      = Nat.card {k : Site d (N + 3) // nuQR N k = μ} := by
  rw [← finrank_eigenspace_cx, finrank_eigenspace_signless N ((μ : ℝ) : ℂ)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun k => ?_)
  rw [nuQ_eq_ofReal_nuQR, Complex.ofReal_inj]

/-! ## 2. Both extremes, over `ℝ` -/

/-- **THE GROUND STATE IS UNIQUE OVER `ℝ`.** The real eigenspace of the massive Laplacian at its
least eigenvalue `m²` is one dimensional, in every dimension and at every side length at least
three. -/
theorem ground_state_simple_real (N : ℕ) (m : ℝ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (massive (torusGraph d (N + 3)) m) - (m ^ 2) • LinearMap.id)) = 1 := by
  rw [← finrank_eigenspace_cx]
  exact ground_state_simple N m

/-- **AND THE TOP IS SIMPLE OVER `ℝ` AT EVEN SIDE LENGTH.** -/
theorem top_eigenvalue_simple_real {M N : ℕ} (hN : N + 3 = 2 * M) (m : ℝ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (massive (torusGraph d (N + 3)) m)
          - (4 * d + m ^ 2) • LinearMap.id)) = 1 := by
  rw [← finrank_eigenspace_cx]
  exact top_eigenvalue_simple hN m

/-- **AND `Q`'s ZERO.** The real kernel of `D + A` on the even periodic lattice is one dimensional,
which `LaplacianSignlessKernel.card_bipartiteComponent_eq_finrank_ker` also gives by counting
two-colourable components — the two now being connected by a theorem rather than agreeing by
coincidence (`RealComplexKernel`). -/
theorem signless_zero_simple_real {M N : ℕ} (hN : N + 3 = 2 * M) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap (torusGraph d (N + 3))) - (0 : ℝ) • LinearMap.id)) = 1 := by
  rw [← finrank_eigenspace_cx]
  have h := signless_zero_simple (d := d) hN
  simpa using h

end TorusRealMultiplicity
