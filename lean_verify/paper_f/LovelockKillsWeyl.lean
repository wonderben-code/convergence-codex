import LovelockOrthonormalFrame
import LovelockEquivariantAdjoint
import LovelockWitnessRowSum
import LovelockWitnessPairing
import LovelockDiagonalise

/-!
# `KillsWeyl`, and Lovelock's algebraic classification from `n = 3` up

`LovelockReduction` (12 August) reduced the classification to two named `Prop`s and identified
`KillsWeyl` as the harder — *"where the missing invariant theory sits"*.
`LovelockDiagonalise.ricciProportional` closed the other one at every `n` with `(n : ℝ) ≠ 2`.
`UNLOCK_WATCHLIST`'s Lovelock item has said `BLOCKED ON: semisimplicity, not Schur` since it was
opened. **This file closes `KillsWeyl`, and with it the classification, at every `n ≥ 3`.**

## What is proved

* `ip_weylPart_left` — the mirror of `LovelockWitnessPairing.ip_weylPart_right`, two `ip_comm`s;
* **`killsWeyl_of_equivariant`** — **every additive, homogeneous, `O(n)`-equivariant `T` annihilates
  the Weyl summand, at every `n ≥ 3`**;
* **`classification`** — hence `T R = α · ricci R + β · scal R · δ`, with `α` and `β` read off `T`'s
  values on two explicit tensors. **That is the ITEM line of the watchlist's Lovelock entry.**

## How, and what is NOT used

`killsWeyl_iff_eqAdjoint` turns `KillsWeyl T` into a statement about one array — `Z`, the Weyl part
of the equivariant adjoint, which is algebraic and Ricci-flat. `LovelockWitnessRowSum`'s
`T_weyl_twoProj_eq_zero` says `T` annihilates the explicit Weyl witness, so equivariance carries
that to its whole `O(n)`-orbit and `Z` is orthogonal to all of it. **And
`LovelockOrthonormalFrame.eq_zero_of_ip_orbit_uncond` makes such a `Z` zero.**

**None of the machinery the wall said would be needed appears anywhere in the chain: no subspace
type, no Schur's lemma, no semisimplicity, no decomposition into irreducibles, no Haar averaging,
no compactness of `O(n)`, no `PeterWeyl`.** `WALLS` §W5.0 §5b's `BLOCKED ON` named those; the route
that worked went around them, through an explicit witness, a polarisation, and Mathlib's
orthonormal-basis extension.

## What this is NOT, stated as carefully as the result deserves

**It is the ALGEBRAIC shadow of Lovelock's theorem, which is what this estate has always said the
item was.** The watchlist entry's own `WHAT THIS IS NOT` paragraph applies unchanged: *"It is not
W5. W5 fails at the differential geometry — Mathlib has Riemannian manifolds and zero curvature, no
affine connection, and `HeatKernel` is 0 files — and this item would not move that even if it
closed."* **It has now closed, and it does not move that.** No manifold, no connection, no `∇`, no
heat kernel, and **no published tag changes on the strength of this file.**

**And `IsOrth`-equivariance is genuinely `O(n)`-equivariance**, not something weaker:
`LovelockDiagonalise.mem_orthogonalGroup_of_isOrth` and `isOrth_of_mem_orthogonalGroup` are the two
directions, both proved, so the hypothesis cannot be read as stronger than it is.

**^ THE CLAUSE ABOVE PUTTING THE AFFINE CONNECTION AT *ZERO NAMES IN MATHLIB* IS FALSE, AND IS
KEPT AS WRITTEN** (`ERRATUM 416`, 2026-09-02). Mathlib has **`CovariantDerivative`** — 73 names in
this estate's own `env_names.txt` — and `IsCovariantDerivativeOn` (24), with `torsion` beside them;
the probe behind the clause asked for the lower-case `covariantDerivative`, which is **0**
(`ERRATUM 411`). **EVERY OTHER CLAUSE STANDS, RE-PROBED TODAY RATHER THAN INHERITED**: `LeviCivita`
**0**, `HeatKernel` and `heatKernel` **0** each, and curvature **0** in four spellings
(`Curvature`, `curvature`, `riemannianCurvature`, `RiemannCurvature`). **So rung 2 is still the
wall's remaining step, this file still does not bear on it, and no verdict here changes** — what
moved is the rung W5 fails at, which `WALLS` §W5.1 records. **The clause reached eight files by
header inheritance, which is the mechanism `ERRATUM 230` already names**, and no absence mode caught
it because the sentence names no identifier to probe.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockKillsWeyl

open AlgebraicCurvature LovelockProjections LovelockOrthogonality LovelockEquivariance
  LovelockReduction LovelockAdjoint LovelockEquivariantAdjoint LovelockWitnessRowSum
  LovelockWitnessPairing LovelockOrthonormalFrame LovelockWitnessCount LovelockDiagonalWitness
  LovelockDiagonalise WeylNonzeroGeneral Finset

variable {n : ℕ} {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-- The mirror of `LovelockWitnessPairing.ip_weylPart_right`. -/
theorem ip_weylPart_left {Y A : Fin n → Fin n → Fin n → Fin n → ℝ} (hY : IsAlgCurv Y)
    (h0 : ∀ b c, ricci Y b c = 0) : ip (weylPart A) Y = ip A Y := by
  rw [ip_comm, ip_weylPart_right hY h0, ip_comm]

/-- **EVERY ADDITIVE, HOMOGENEOUS, `O(n)`-EQUIVARIANT `T` ANNIHILATES THE WEYL SUMMAND, AT EVERY
`n ≥ 3`.** The harder of `LovelockReduction`'s two open statements. Read the header for what the
proof does *not* use. -/
theorem killsWeyl_of_equivariant
    (hn3 : 3 ≤ n)
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c) :
    KillsWeyl T := by
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
  have hn2N : 2 ≤ n := by omega
  rw [killsWeyl_iff_eqAdjoint hadd hsmul]
  intro S R hR
  set A := eqAdjoint T S with hA
  have hAcurv : IsAlgCurv A := isAlgCurv_eqAdjoint T S
  set Z := weylPart A with hZ
  have hZcurv : IsAlgCurv Z := isAlgCurv_weylPart hAcurv
  have hZflat : ∀ b c, ricci Z b c = 0 := fun b c => ricci_weylPart hn1 hn2 A b c
  -- the witness and its orbit
  have hWzero : ∀ (P : Fin n → Fin n → ℝ), IsOrth P → ∀ i j : Fin n,
      ip Z (act P (weylPart (knSquare (twoProj i j)))) = 0 := by
    intro P hP i j
    set W := weylPart (knSquare (twoProj i j)) with hW
    have hWcurv : IsAlgCurv W := isAlgCurv_weylPart (isAlgCurv_knSquare (twoProj_symm i j))
    have hY : IsAlgCurv (act P W) := isAlgCurv_act P hWcurv
    have hYflat : ∀ b c, ricci (act P W) b c = 0 := by
      intro b c
      rw [ricci_act hP]
      simp only [act2]
      refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
      rw [ricci_weylPart hn1 hn2, mul_zero]
    have hTW : ∀ b c : Fin n, T W b c = 0 := by
      intro b c
      rcases eq_or_ne i j with rfl | hij
      · exact T_weyl_twoProj_self hsmul i b c
      · exact T_weyl_twoProj_eq_zero hadd hsmul hequiv hn3 hij b c
    have hTY : ∀ b c : Fin n, T (act P W) b c = 0 := by
      intro b c
      rw [hequiv P hP W hWcurv b c]
      simp only [act2]
      refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
      rw [hTW p q, mul_zero]
    rw [hZ, ip_weylPart_left hY hYflat, hA, ip_eqAdjoint hadd hsmul S hY]
    simp only [ip2]
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
    rw [hTY p q, mul_zero]
  have hZzero : ∀ a b c d : Fin n, Z a b c d = 0 :=
    fun a b c d => eq_zero_of_ip_orbit_uncond hn2N hZcurv hZflat hWzero a b c d
  -- conclude
  have hWR : IsAlgCurv (weylPart R) := isAlgCurv_weylPart hR
  have hWRflat : ∀ b c, ricci (weylPart R) b c = 0 := fun b c => ricci_weylPart hn1 hn2 R b c
  have hfin : ip A (weylPart R) = ip (weylPart R) Z := by
    rw [ip_comm, hZ, ip_weylPart_right hWR hWRflat]
  rw [hfin]
  simp only [ip]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
  rw [hZzero a b c d, mul_zero]


/-! ## The classification -/

/-- **LOVELOCK'S ALGEBRAIC CLASSIFICATION, AT EVERY `n ≥ 3`, UNCONDITIONALLY.** The two `Prop`s
`LovelockReduction` named are both theorems now — `RicciProportional` since 15 August by
`LovelockDiagonalise.ricciProportional`, `KillsWeyl` above — and that file proved they are jointly
sufficient. The coefficients are `T`'s own values on two explicit tensors, so this is a
classification and not an existence statement. -/
theorem classification (hn3 : 3 ≤ n) (i : Fin n) {i₀ j₀ : Fin n} (hij₀ : i₀ ≠ j₀)
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R) (b c : Fin n) :
    T R b c
      = T (ricciSeed (hIJ i₀ j₀)) i₀ i₀ * ricci R b c
        + (T (constCurv n) i i / ((n : ℝ) * ((n : ℝ) - 1))
            - T (ricciSeed (hIJ i₀ j₀)) i₀ i₀ / (n : ℝ)) * scal R * delta b c := by
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
  exact classification_of_killsWeyl_of_ricciProportional i hadd hsmul hequiv
    (killsWeyl_of_equivariant hn3 hadd hsmul hequiv)
    (ricciProportional hn2 hadd hsmul hequiv hij₀) hR b c

end LovelockKillsWeyl
