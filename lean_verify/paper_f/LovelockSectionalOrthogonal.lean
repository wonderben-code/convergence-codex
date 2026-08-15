import LovelockWitnessPairing

/-!
# Orthogonal pairs are enough — one restrictive hypothesis off the sectional theorem

`LovelockSectional.eq_zero_of_sec` assumes the sectional entries vanish on **every** pair of
vectors. `LovelockWitnessPairing.eq_zero_of_ip_orbit` then carries the whole route on a hypothesis
`hext` bridging from what orbit-orthogonality actually supplies. **This file removes as much of that
hypothesis as is elementary, and says exactly what is left.**

## What is proved

* `dotp` — the ordinary dot product on `Fin n → ℝ`;
* `mult_smul_one`, `mult_smul_four` — homogeneity of the multilinear extension in the outer slots;
* **`mult_swap12`, `mult_swap34`** — swapping either antisymmetric pair of slots flips the sign.
  Each is one reindexing by `Fintype.sum_bijective`, in the pattern `mult_reverse` established;
  `mult_self_left` and `mult_self_right` follow;
* `sec_zero_right`, `dotp_self_eq_zero` — the degenerate cases, and positive definiteness;
* **`sec_eq_zero_of_orthogonal`** — **vanishing on ORTHOGONAL pairs forces vanishing on all pairs.**
  Split `x = x⊥ + c·y` with `c = ⟨x,y⟩/⟨y,y⟩`. Three of the four terms die on the spot — two have
  `y` in both of the first slots, one has `y` in both of the last — so `sec Z x y = sec Z x⊥ y`,
  and `x⊥ ⟂ y` by construction;
* **`eq_zero_of_sec_orthogonal`** — hence `eq_zero_of_sec` **with a strictly weaker hypothesis**.

## What is left of `hext`, stated exactly

`eq_zero_of_ip_orbit`'s hypothesis was *"sectional vanishing on all pairs of rows of orthogonal
matrices implies it on all pairs"*. **Two of its three parts are now theorems.** What remains is one
statement and it is purely about matrices:

> **every orthonormal pair of vectors in `Fin n → ℝ` is a pair of rows of some orthogonal matrix**

plus the scaling that turns an orthogonal pair into an orthonormal one, which needs `Real.sqrt` and
positive definiteness. **That is a Mathlib-facing statement** — `OrthonormalBasis` and
`Orthonormal.exists_orthonormalBasis_extension` are where it would come from — **and this estate has
never bridged `Fin n → ℝ` to `EuclideanSpace ℝ (Fin n)`.** It is not attempted here and it is not
asserted to be hard; it is named so the next attempt starts from a statement rather than a
paragraph.

**`KillsWeyl` at `n ≥ 4` does not follow from this file** — nothing here mentions an equivariant
`T` — **and the watchlist item does not move.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockSectionalOrthogonal

open AlgebraicCurvature LovelockSectional Finset

variable {n : ℕ}

/-- The ordinary dot product on `Fin n → ℝ`. -/
def dotp (x y : Fin n → ℝ) : ℝ := ∑ t, x t * y t

theorem mult_smul_one (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (lam : ℝ) (x y z w : Fin n → ℝ) :
    mult Z (fun t => lam * x t) y z w = lam * mult Z x y z w := by
  simp only [mult, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem mult_smul_four (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (lam : ℝ) (x y z w : Fin n → ℝ) :
    mult Z x y z (fun t => lam * w t) = lam * mult Z x y z w := by
  simp only [mult, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- **SWAPPING THE FIRST PAIR FLIPS THE SIGN.** One reindexing, in `mult_reverse`'s pattern. -/
theorem mult_swap12 {Z : Fin n → Fin n → Fin n → Fin n → ℝ} (hZ : IsAlgCurv Z)
    (x y z w : Fin n → ℝ) : mult Z x y z w = -mult Z y x z w := by
  have hbij : Function.Bijective
      (fun p : Fin n × Fin n × Fin n × Fin n => (p.2.1, p.1, p.2.2.1, p.2.2.2)) := by
    constructor
    · intro p q h
      simp only [Prod.mk.injEq] at h
      simp only [Prod.ext_iff]
      tauto
    · intro q; exact ⟨(q.2.1, q.1, q.2.2.1, q.2.2.2), rfl⟩
  simp only [mult, ← Finset.sum_neg_distrib]
  refine Fintype.sum_bijective _ hbij _ _ (fun p => ?_)
  simp only [hZ.antisymm_left p.2.1 p.1 p.2.2.1 p.2.2.2]
  ring

/-- **AND SO DOES SWAPPING THE LAST PAIR.** -/
theorem mult_swap34 {Z : Fin n → Fin n → Fin n → Fin n → ℝ} (hZ : IsAlgCurv Z)
    (x y z w : Fin n → ℝ) : mult Z x y z w = -mult Z x y w z := by
  have hbij : Function.Bijective
      (fun p : Fin n × Fin n × Fin n × Fin n => (p.1, p.2.1, p.2.2.2, p.2.2.1)) := by
    constructor
    · intro p q h
      simp only [Prod.mk.injEq] at h
      simp only [Prod.ext_iff]
      tauto
    · intro q; exact ⟨(q.1, q.2.1, q.2.2.2, q.2.2.1), rfl⟩
  simp only [mult, ← Finset.sum_neg_distrib]
  refine Fintype.sum_bijective _ hbij _ _ (fun p => ?_)
  simp only [hZ.antisymm_right p.1 p.2.1 p.2.2.2 p.2.2.1]
  ring

/-- Hence a repeated vector in the first pair kills the form. -/
theorem mult_self_left {Z : Fin n → Fin n → Fin n → Fin n → ℝ} (hZ : IsAlgCurv Z)
    (x z w : Fin n → ℝ) : mult Z x x z w = 0 := by
  have := mult_swap12 hZ x x z w
  linarith

/-- And in the last pair. -/
theorem mult_self_right {Z : Fin n → Fin n → Fin n → Fin n → ℝ} (hZ : IsAlgCurv Z)
    (x y z : Fin n → ℝ) : mult Z x y z z = 0 := by
  have := mult_swap34 hZ x y z z
  linarith

theorem sec_zero_right (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    sec Z x (fun _ => (0 : ℝ)) = 0 := by
  simp only [sec, mult]
  exact Finset.sum_eq_zero fun p _ => by ring

/-- Positive definiteness, in the form this file needs. -/
theorem dotp_self_eq_zero {y : Fin n → ℝ} (h : dotp y y = 0) (t : Fin n) : y t = 0 := by
  have hnn : ∀ s ∈ (univ : Finset (Fin n)), 0 ≤ y s * y s := fun s _ => mul_self_nonneg _
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h t (Finset.mem_univ t)
  exact mul_self_eq_zero.mp this

/-- **VANISHING ON ORTHOGONAL PAIRS IS ENOUGH.** -/
theorem sec_eq_zero_of_orthogonal {Z : Fin n → Fin n → Fin n → Fin n → ℝ} (hZ : IsAlgCurv Z)
    (h : ∀ x y : Fin n → ℝ, dotp x y = 0 → sec Z x y = 0) (x y : Fin n → ℝ) :
    sec Z x y = 0 := by
  by_cases hy : dotp y y = 0
  · have hfun : y = fun _ => (0 : ℝ) := funext fun t => dotp_self_eq_zero hy t
    rw [hfun, sec_zero_right]
  · set c := dotp x y / dotp y y with hc
    set xp := fun t => x t - c * y t with hxp
    have hsplit : x = fun t => xp t + c * y t := by
      funext t; simp only [hxp]; ring
    have hstep : sec Z x y = sec Z xp y := by
      simp only [sec]
      rw [hsplit, mult_add_one, mult_add_four, mult_add_four, mult_smul_one, mult_smul_four,
        mult_smul_four]
      simp only [mult_self_left hZ, mult_self_right hZ]
      ring
    have hperp : dotp xp y = 0 := by
      have hexp : dotp xp y = dotp x y - c * dotp y y := by
        simp only [dotp, hxp, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun t _ => by ring
      rw [hexp, hc]
      field_simp
      ring
    rw [hstep]
    exact h xp y hperp

/-- **`eq_zero_of_sec` WITH A STRICTLY WEAKER HYPOTHESIS.** Orthogonal pairs suffice. -/
theorem eq_zero_of_sec_orthogonal {Z : Fin n → Fin n → Fin n → Fin n → ℝ} (hZ : IsAlgCurv Z)
    (h : ∀ x y : Fin n → ℝ, dotp x y = 0 → sec Z x y = 0) (a b c d : Fin n) : Z a b c d = 0 :=
  eq_zero_of_sec hZ (sec_eq_zero_of_orthogonal hZ h) a b c d

end LovelockSectionalOrthogonal
