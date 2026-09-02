import LovelockCompleteReducibility
import LovelockDiagonalise
import LovelockInstances

/-!
# The Weyl summand as a submodule, and the linearity nobody had written down

`LovelockCompleteReducibility` proved that every `act`-stable **submodule** of four-index arrays
has an `act`-stable complement, and instantiated it at `algCurv`. It then said what stopped the
instantiation that would matter:

> The natural next instance is the **Weyl summand as a submodule**, whose stability is
> `LovelockActInverse.weylSet_act` — but that is a statement about a *set*, and turning it into a
> `Submodule` needs `weylPart` to be additive and homogeneous. **Neither lemma exists in this
> estate.**

That was checked by grep, not assumed, and it was right. This file writes them.

## What is proved

* **`tracefreeRicci_add`, `tracefreeRicci_smul`** — from `ricci_add`/`ricci_smul` and
  `scal_add`/`scal_smul`, which the estate already had **in four different files**;
* **`kn_add_left`, `kn_smul_left`** — `kn` is linear in its first argument, one `ring` each;
* **`ricciPart_add`, `ricciPart_smul`, `scalPart_add`, `scalPart_smul`**, and hence
  **`weylPart_add`, `weylPart_smul`** — the two the previous file named;
* **`weylSub`** — the Weyl summand as a `Submodule ℝ (EuclideanSpace ℝ (ArrIdx n))`, the image of
  the algebraic curvature tensors under `weylPart`;
* **`stable_weylSub`** and **`exists_stable_complement_weylSub`** — it is `act`-stable, by
  `act_weylPart` and `isAlgCurv_act`, and therefore has an `act`-stable complement.

## Where these lemmas belong, said rather than left to be noticed

**`weylPart_add` and `weylPart_smul` belong with `weylPart`, in `LovelockProjections`.** They are
here because that file is imported by most of the estate and this is the only consumer; **if a
second consumer appears they should move.** The four they are built from are already scattered —
`ricci_add` in `LovelockDiagonalise`, `scal_add` in `LovelockInstances`, `ricci_smul` and
`scal_smul` in `AlgebraicCurvature` — which is the same drift one step earlier, and is recorded
here rather than repaired, because moving four lemmas that thirty files import is a bigger change
than this unit is.

## What this does NOT do, and it is the same sentence as the last two files

**A stable complement for the Weyl summand is not `KillsWeyl` and is not a step toward it.**
Schur's lemma needs the Weyl summand **irreducible**, and complete reducibility is precisely the
statement that says nothing about which subspaces are minimal. `WALLS` §W5.0 §5d says so and that
sentence is not superseded. **The watchlist item does not move.**


**⚠ CORRECTED 2026-08-22 — THE SENTENCE ABOVE IS TRUE AND ITS FRAMING IS NOT, and it is kept per
`ERRATUM 94`.** `KillsWeyl` is **proved**, at every `n ≥ 3`, by
`LovelockKillsWeyl.killsWeyl_of_equivariant` (`171d474`, 15 August), and the watchlist's Lovelock
item is CLOSED. *"The watchlist item does not move"* is therefore true only in the sense that a
closed item cannot move — **and it invites the reading that `KillsWeyl` is open, which is false.**
What this file does not bear on is the wall's actual remaining step, which is rung 2 of `WALLS`
§W5.1's staircase: an **affine connection and Levi-Civita**, zero names in Mathlib. `ERRATUM 230`
records that this framing was inherited from the headers being extended and repeated across a
day's units without being checked.

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

namespace LovelockWeylSubmodule

open AlgebraicCurvature LovelockProjections LovelockOrthogonality LovelockInnerSpace
  LovelockEquivariance LovelockActInverse LovelockCompleteReducibility
  LovelockCurvProjectionOrthogonal LovelockDiagonalise LovelockInstances

variable {n : ℕ}

/-! ## 1. Linearity, from the four lemmas the estate already had -/

theorem tracefreeRicci_add (R S : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) :
    tracefreeRicci (fun a b c d => R a b c d + S a b c d) b c
      = tracefreeRicci R b c + tracefreeRicci S b c := by
  simp only [tracefreeRicci, scal_add, congrFun (congrFun (ricci_add R S) b) c]
  ring

theorem tracefreeRicci_smul (lam : ℝ) (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) :
    tracefreeRicci (fun a b c d => lam * R a b c d) b c = lam * tracefreeRicci R b c := by
  simp only [tracefreeRicci, scal_smul, ricci_smul]
  ring

theorem kn_add_left (h h' k : Fin n → Fin n → ℝ) (a b c d : Fin n) :
    kn (fun x y => h x y + h' x y) k a b c d = kn h k a b c d + kn h' k a b c d := by
  simp only [kn]; ring

theorem kn_smul_left (lam : ℝ) (h k : Fin n → Fin n → ℝ) (a b c d : Fin n) :
    kn (fun x y => lam * h x y) k a b c d = lam * kn h k a b c d := by
  simp only [kn]; ring

theorem ricciPart_add (R S : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    ricciPart (fun a b c d => R a b c d + S a b c d) a b c d
      = ricciPart R a b c d + ricciPart S a b c d := by
  have h : (fun x y => tracefreeRicci (fun a b c d => R a b c d + S a b c d) x y)
      = fun x y => tracefreeRicci R x y + tracefreeRicci S x y := by
    funext x y; exact tracefreeRicci_add R S x y
  simp only [ricciPart, h, kn_add_left]
  ring

theorem ricciPart_smul (lam : ℝ) (R : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    ricciPart (fun a b c d => lam * R a b c d) a b c d = lam * ricciPart R a b c d := by
  have h : (fun x y => tracefreeRicci (fun a b c d => lam * R a b c d) x y)
      = fun x y => lam * tracefreeRicci R x y := by
    funext x y; exact tracefreeRicci_smul lam R x y
  simp only [ricciPart, h, kn_smul_left]
  ring

theorem scalPart_add (R S : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    scalPart (fun a b c d => R a b c d + S a b c d) a b c d
      = scalPart R a b c d + scalPart S a b c d := by
  simp only [scalPart, scal_add]
  ring

theorem scalPart_smul (lam : ℝ) (R : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    scalPart (fun a b c d => lam * R a b c d) a b c d = lam * scalPart R a b c d := by
  simp only [scalPart, scal_smul]
  ring

/-- **THE WEYL PROJECTION IS ADDITIVE** — one of the two `LovelockCompleteReducibility` named. -/
theorem weylPart_add (R S : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    weylPart (fun a b c d => R a b c d + S a b c d) a b c d
      = weylPart R a b c d + weylPart S a b c d := by
  simp only [weylPart, ricciPart_add, scalPart_add]
  ring

/-- **AND HOMOGENEOUS.** -/
theorem weylPart_smul (lam : ℝ) (R : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    weylPart (fun a b c d => lam * R a b c d) a b c d = lam * weylPart R a b c d := by
  simp only [weylPart, ricciPart_smul, scalPart_smul]
  ring

/-! ## 2. The submodule -/

/-- **THE WEYL SUMMAND AS A SUBMODULE**: the Weyl parts of algebraic curvature tensors. -/
def weylSub (n : ℕ) : Submodule ℝ (EuclideanSpace ℝ (ArrIdx n)) where
  carrier := {x | ∃ X, IsAlgCurv X ∧ (arrEquiv n).symm x = weylPart X}
  zero_mem' := ⟨fun _ _ _ _ => 0, isAlgCurv_zero, by
    funext a b c d
    simp only [weylPart, ricciPart, scalPart, tracefreeRicci, ricci, scal, kn, knSquare]
    simp⟩
  add_mem' := by
    rintro x y ⟨X, hX, hx⟩ ⟨Y, hY, hy⟩
    refine ⟨fun a b c d => X a b c d + Y a b c d, isAlgCurv_add hX hY, ?_⟩
    funext a b c d
    have hX' := congrFun (congrFun (congrFun (congrFun hx a) b) c) d
    have hY' := congrFun (congrFun (congrFun (congrFun hy a) b) c) d
    simp only [weylPart_add]
    exact congrArg₂ (· + ·) hX' hY'
  smul_mem' := by
    rintro lam x ⟨X, hX, hx⟩
    refine ⟨fun a b c d => lam * X a b c d, isAlgCurv_smul lam hX, ?_⟩
    funext a b c d
    have := congrFun (congrFun (congrFun (congrFun hx a) b) c) d
    simp only [weylPart_smul]
    exact congrArg (lam * ·) this

/-- **IT IS `act`-STABLE**, by `act_weylPart` and `isAlgCurv_act`. -/
theorem stable_weylSub : Stable (weylSub n) := by
  rintro Q hQ x ⟨X, hX, hx⟩
  refine ⟨act Q X, isAlgCurv_act Q hX, ?_⟩
  funext a b c d
  have hxe : (arrEquiv n).symm (actE Q x) = act Q ((arrEquiv n).symm x) := rfl
  rw [hxe, hx, act_weylPart hQ X a b c d]

/-- **AND THEREFORE HAS AN `act`-STABLE COMPLEMENT.** Not `KillsWeyl`: Schur needs the Weyl
summand **irreducible**, and this says only that stable subspaces split off. -/
theorem exists_stable_complement_weylSub :
    ∃ K' : Submodule ℝ (EuclideanSpace ℝ (ArrIdx n)), Stable K' ∧ IsCompl (weylSub n) K' :=
  exists_stable_complement _ stable_weylSub

end LovelockWeylSubmodule
