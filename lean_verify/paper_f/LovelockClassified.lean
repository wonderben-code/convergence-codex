import LovelockOneProp
import LovelockKillsWeyl

/-!
# Lovelock's classification with no `KillsWeyl` hypothesis

`LovelockReduction` split the algebraic content of Lovelock's theorem into two statements,
`KillsWeyl` and `RicciProportional`, and proved them jointly sufficient. `LovelockDiagonalise`
proved the second. `LovelockOneProp` then showed the first suffices **alone** — its header is
titled *"One `Prop` left, and it is not merely sufficient — it is the problem"* — and stopped
there, on 15 August.

**`LovelockKillsWeyl.killsWeyl_of_equivariant` proved that `Prop` the next day**, for every
additive, homogeneous, `O(n)`-equivariant `T` at every `n ≥ 3`. Four files carry a `⚠ SUPERSEDED`
note saying so. **`LovelockOneProp` is the one the sweep missed** — the file whose title is about
the very `Prop` in question — and `ERRATUM 351` records that.

**⚠ THE PARAGRAPH THAT STOOD HERE WAS FALSE AND IS CORRECTED BELOW** (`ERRATUM 353`, kept per
`ERRATUM 94`). It read: *"So the two halves have sat one import apart for a fortnight and nothing
joined them. This file is the join."* **They were joined on 16 August, in `LovelockKillsWeyl`
itself**: `LovelockKillsWeyl.classification` discharges `KillsWeyl` by
`killsWeyl_of_equivariant` in its own proof, on the same day both landed. I did not find it because
I grepped for the statement in ONE PHRASING — `Classified T` — and that file writes the equation
out longhand and contains the word `Classified` **zero times**. That is `ERRATUM 346`'s defect,
cited in the very entry that carried the false claim.

**WHAT THIS FILE ACTUALLY ADDS, WHICH IS REAL AND IS SMALL.** `LovelockKillsWeyl.classification`
still carries **four hypotheses that `3 ≤ n` already implies**: `(n : ℝ) − 2 ≠ 0`, an index
`i : Fin n`, and two distinct indices `i₀ ≠ j₀`. It also states the conclusion **pointwise, with the
constants written out**, rather than as the packaged predicate.

> **`classified_of_equivariant`** — for every `T` that is additive, homogeneous and
> `O(n)`-equivariant, at every `n ≥ 3`: **`∃ α β, Classified T α β`**. **The only hypotheses are
> `3 ≤ n` and the three equivariance conditions** — the index hypotheses are discharged here rather
> than passed on, and the conclusion is `LovelockOneProp`'s `Classified` predicate.

**THAT IS THE WHOLE OF THE CONTRIBUTION AND IT IS STATED AT ITS SIZE.** It is a hypothesis
reduction and a repackaging, not a first composition. The mathematics was in place on 16 August.

**WHAT THIS IS NOT.** It is not Lovelock's theorem in differential geometry: `T` here is a map on
algebraic curvature tensors at a point, there is no manifold, no metric connection and no
divergence-freeness anywhere in the estate. **The equivariance hypothesis is not removable and is
not decoration** — it is the whole content, and a `T` that is merely additive and homogeneous is
not classified by anything here. `AlgebraicCurvature`'s header says the same and is the authority.
-/

namespace LovelockClassified

open AlgebraicCurvature LovelockProjections LovelockEquivariance
open LovelockReduction LovelockOneProp LovelockKillsWeyl

variable {n : ℕ} {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-- **LOVELOCK'S ALGEBRAIC CLASSIFICATION, WITH NO `KillsWeyl` HYPOTHESIS.** Every additive,
homogeneous, `O(n)`-equivariant `T` is `α · ricci + β · scal · δ` on algebraic curvature tensors,
at every `n ≥ 3`. The `KillsWeyl` hypothesis `LovelockOneProp.classified_of_killsWeyl` carries is
supplied by `LovelockKillsWeyl.killsWeyl_of_equivariant` from the hypotheses already present. -/
theorem classified_of_equivariant (hn3 : 3 ≤ n)
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c) :
    ∃ α β : ℝ, Classified T α β := by
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  refine ⟨_, _, LovelockOneProp.classified_of_killsWeyl hn2 ⟨0, h0⟩ hadd hsmul hequiv
    (i₀ := ⟨0, h0⟩) (j₀ := ⟨1, h1⟩) ?_ (killsWeyl_of_equivariant hn3 hadd hsmul hequiv)⟩
  simp [Fin.ext_iff]

/-- **AND THE EQUIVALENCE COLLAPSES.** `LovelockOneProp.killsWeyl_iff` says `KillsWeyl T` holds
exactly when the classification does; with the left side now a theorem under equivariance, both
sides are. Stated so the two files are checked against each other rather than left to agree. -/
theorem killsWeyl_and_classified (hn3 : 3 ≤ n)
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hequiv : ∀ Q, IsOrth Q → ∀ R, IsAlgCurv R → ∀ b c, T (act Q R) b c = act2 Q (T R) b c) :
    KillsWeyl T ∧ ∃ α β : ℝ, Classified T α β :=
  ⟨killsWeyl_of_equivariant hn3 hadd hsmul hequiv,
    classified_of_equivariant hn3 hadd hsmul hequiv⟩

end LovelockClassified
