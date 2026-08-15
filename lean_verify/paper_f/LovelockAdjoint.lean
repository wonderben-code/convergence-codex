import LovelockDiagonalSum
import LovelockOrthogonality
import LovelockReduction

/-!
# The adjoint of `T`, and `KillsWeyl` restated as a statement about it

`WALLS` §W5.0 §5d numbers a candidate elementary route to `KillsWeyl` and calls the adjoint of `T`
its rung 2. **This file is that rung**, and the first thing to say is what the adjoint does *not*
need.

## No inner-product-space structure is required, and an earlier draft said otherwise

A draft of §5d's account named the missing piece as *"finite-dimensional inner-product-space
structure on `Curv`, which the estate deliberately lacks — `Curv` is a `Prop`-subset of functions,
not a submodule"*. **That is not the obstruction.** `LovelockReduction`'s hypotheses on `T`, read
exactly, put `hadd` and `hsmul` on **all** four-index arrays with no `IsAlgCurv` — only `hequiv`
carries it. So `T` is an honest linear map on `ℝ^{n⁴}`, whose adjoint is a formula in the standard
basis: no Riesz representation, no bundled inner product space, no submodule, no completeness.

## What is proved

* `ip2` — the full contraction of two 2-tensors. `LovelockOrthogonality` writes exactly this sum by
  hand inside `ip_kn` and never names it; naming it is what makes the adjoint statable. `ip2_unit`
  (testing against a single-entry tensor reads off one entry), `ip2_smul` and `ip2_sum`;
* `unitArray` and **`unitArray_expand`** — the standard basis of four-index arrays, and the fact
  that every array is its own expansion in it;
* **`T_expand`** — `T R p q = ∑_{abcd} R_{abcd} · T(unitArray a b c d) p q`. **`T` is determined by
  its values on the basis**, which is linearity over a `Finset.sum` and nothing more.
  `LovelockDiagonalSum.T_sum` does the induction; it is applied four times and **not rebuilt**;
* **`adjoint`** — `(T* S)_{abcd} := ⟨S, T (unitArray a b c d)⟩`, and **`ip_adjoint`**:
  `⟨T* S, R⟩ = ⟨S, T R⟩` **for every `R`**, algebraic curvature tensor or not;
* **`killsWeyl_iff_adjoint`** — `KillsWeyl T` holds **if and only if** `T* S` is `ip`-orthogonal to
  the Weyl part of every algebraic curvature tensor, for every 2-tensor `S`.

## What this is not

**`killsWeyl_iff_adjoint` is a restatement and not progress.** It is an equivalence: both sides are
exactly as open as each other, and nothing here decides either. What it buys is that the route's
later rungs get to work on `T* S`, which is a four-index array the reflection lemmas of
`LovelockReflectionFour` can be pointed at, instead of on `T`, which they cannot.

**And §5d's two gaps are untouched.** (i) The adjoint's equivariance still needs `T (act Q R) =
act2 Q (T R)` at arrays that are not algebraic curvature tensors, and `hequiv` does not supply it —
`unitArray a b c d` is not an algebraic curvature tensor for any `a b c d`. (ii) Nothing here says
`adjoint T S` is an algebraic curvature tensor, so the `ip`-orthogonality machinery of
`LovelockOrthogonality`, which is stated on `IsAlgCurv`, does not apply to it. **The watchlist item
does not move.**

**The name is `adjoint` and not `adj`** because `BoxGraph.adj` and `IsingFiniteVolume.adj` already
exist — graph adjacency, unrelated — and the estate's duplicated-name list is a decision already
waiting on the author rather than something to lengthen.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockAdjoint

open AlgebraicCurvature LovelockProjections LovelockOrthogonality LovelockReduction
  LovelockDiagonalSum Finset

variable {n : ℕ}
variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-- The full contraction of two 2-tensors. -/
def ip2 (S U : Fin n → Fin n → ℝ) : ℝ := ∑ b, ∑ c, S b c * U b c

/-- Testing against a single-entry 2-tensor reads off one entry. -/
theorem ip2_unit (U : Fin n → Fin n → ℝ) (b c : Fin n) :
    ip2 (fun x y => delta b x * delta c y) U = U b c := by
  simp only [ip2]
  rw [Finset.sum_eq_single b]
  · rw [Finset.sum_eq_single c]
    · simp [delta_self]
    · intro y _ hy; simp [delta, Ne.symm hy]
    · intro h; exact absurd (Finset.mem_univ c) h
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [delta, Ne.symm hx]
  · intro h; exact absurd (Finset.mem_univ b) h

/-- The standard unitArray array. -/
def unitArray (a b c d : Fin n) : Fin n → Fin n → Fin n → Fin n → ℝ :=
  fun x y z w => delta a x * delta b y * delta c z * delta d w

theorem unitArray_expand (R : Fin n → Fin n → Fin n → Fin n → ℝ) (x y z w : Fin n) :
    R x y z w = ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * unitArray a b c d x y z w := by
  simp only [unitArray]
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single y]
    · rw [Finset.sum_eq_single z]
      · rw [Finset.sum_eq_single w]
        · simp [delta_self]
        · intro v _ hv; simp [delta, hv]
        · intro h; exact absurd (Finset.mem_univ w) h
      · intro v _ hv
        refine (Finset.sum_eq_zero fun u _ => ?_)
        simp [delta, hv]
      · intro h; exact absurd (Finset.mem_univ z) h
    · intro v _ hv
      refine (Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun t _ => ?_)
      simp [delta, hv]
    · intro h; exact absurd (Finset.mem_univ y) h
  · intro v _ hv
    refine (Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun t _ =>
      Finset.sum_eq_zero fun r _ => ?_)
    simp [delta, hv]
  · intro h; exact absurd (Finset.mem_univ x) h

theorem T_smul_unitArray
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (lam : ℝ) (a b c d p q : Fin n) :
    T (fun x y z w => lam * unitArray a b c d x y z w) p q = lam * T (unitArray a b c d) p q :=
  congrFun (congrFun (hsmul lam (unitArray a b c d)) p) q

theorem T_expand
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ) (p q : Fin n) :
    T R p q = ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * T (unitArray a b c d) p q := by
  have hd : ∀ a b c : Fin n,
      T (fun x y z w => ∑ d, R a b c d * unitArray a b c d x y z w) p q
        = ∑ d, R a b c d * T (unitArray a b c d) p q := by
    intro a b c
    rw [T_sum hadd hsmul univ (fun d => fun x y z w => R a b c d * unitArray a b c d x y z w) p q]
    exact Finset.sum_congr rfl fun d _ => T_smul_unitArray hsmul _ a b c d p q
  have hc : ∀ a b : Fin n,
      T (fun x y z w => ∑ c, ∑ d, R a b c d * unitArray a b c d x y z w) p q
        = ∑ c, ∑ d, R a b c d * T (unitArray a b c d) p q := by
    intro a b
    rw [T_sum hadd hsmul univ
      (fun c => fun x y z w => ∑ d, R a b c d * unitArray a b c d x y z w) p q]
    exact Finset.sum_congr rfl fun c _ => hd a b c
  have hb : ∀ a : Fin n,
      T (fun x y z w => ∑ b, ∑ c, ∑ d, R a b c d * unitArray a b c d x y z w) p q
        = ∑ b, ∑ c, ∑ d, R a b c d * T (unitArray a b c d) p q := by
    intro a
    rw [T_sum hadd hsmul univ
      (fun b => fun x y z w => ∑ c, ∑ d, R a b c d * unitArray a b c d x y z w) p q]
    exact Finset.sum_congr rfl fun b _ => hc a b
  have ha : T (fun x y z w => ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * unitArray a b c d x y z w) p q
      = ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * T (unitArray a b c d) p q := by
    rw [T_sum hadd hsmul univ
      (fun a => fun x y z w => ∑ b, ∑ c, ∑ d, R a b c d * unitArray a b c d x y z w) p q]
    exact Finset.sum_congr rfl fun a _ => hb a
  have hR : (fun x y z w => ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * unitArray a b c d x y z w) = R := by
    funext x y z w; exact (unitArray_expand R x y z w).symm
  rw [hR] at ha
  exact ha

theorem ip2_smul (S U : Fin n → Fin n → ℝ) (lam : ℝ) :
    ip2 S (fun p q => lam * U p q) = lam * ip2 S U := by
  simp only [ip2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

theorem ip2_sum (S : Fin n → Fin n → ℝ) (F : Fin n → Fin n → Fin n → ℝ) :
    ip2 S (fun p q => ∑ i, F i p q) = ∑ i, ip2 S (F i) := by
  simp only [ip2, Finset.mul_sum]
  have h1 : ∀ p : Fin n, ∑ q, ∑ i, S p q * F i p q = ∑ i, ∑ q, S p q * F i p q :=
    fun p => Finset.sum_comm
  rw [Finset.sum_congr rfl fun p _ => h1 p, Finset.sum_comm]

/-- **THE ADJOINT.** -/
def adjoint (T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ)
    (S : Fin n → Fin n → ℝ) (a b c d : Fin n) : ℝ := ip2 S (T (unitArray a b c d))

theorem ip_adjoint
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (S : Fin n → Fin n → ℝ) (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip (adjoint T S) R = ip2 S (T R) := by
  have hd : ∀ a b c : Fin n,
      ip2 S (fun p q => ∑ d, R a b c d * T (unitArray a b c d) p q)
        = ∑ d, R a b c d * adjoint T S a b c d := by
    intro a b c
    rw [ip2_sum]
    exact Finset.sum_congr rfl fun d _ => ip2_smul S (T (unitArray a b c d)) (R a b c d)
  have hc : ∀ a b : Fin n,
      ip2 S (fun p q => ∑ c, ∑ d, R a b c d * T (unitArray a b c d) p q)
        = ∑ c, ∑ d, R a b c d * adjoint T S a b c d := by
    intro a b
    rw [ip2_sum]
    exact Finset.sum_congr rfl fun c _ => hd a b c
  have hb : ∀ a : Fin n,
      ip2 S (fun p q => ∑ b, ∑ c, ∑ d, R a b c d * T (unitArray a b c d) p q)
        = ∑ b, ∑ c, ∑ d, R a b c d * adjoint T S a b c d := by
    intro a
    rw [ip2_sum]
    exact Finset.sum_congr rfl fun b _ => hc a b
  have hTfun : T R
      = fun p q => ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * T (unitArray a b c d) p q :=
    funext fun p => funext fun q => T_expand hadd hsmul R p q
  have hRHS : ip2 S (T R) = ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * adjoint T S a b c d := by
    rw [hTfun, ip2_sum]
    exact Finset.sum_congr rfl fun a _ => hb a
  have hLHS : ip (adjoint T S) R = ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * adjoint T S a b c d := by
    simp only [ip]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  rw [hLHS, hRHS]

theorem killsWeyl_iff_adjoint
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c) :
    KillsWeyl T ↔ ∀ (S : Fin n → Fin n → ℝ) R, IsAlgCurv R → ip (adjoint T S) (weylPart R) = 0 := by
  constructor
  · intro hW S R hR
    rw [ip_adjoint hadd hsmul]
    simp only [ip2]
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
    rw [hW R hR p q, mul_zero]
  · intro h R hR b c
    have hb := h (fun x y => delta b x * delta c y) R hR
    rw [ip_adjoint hadd hsmul, ip2_unit] at hb
    exact hb

end LovelockAdjoint
