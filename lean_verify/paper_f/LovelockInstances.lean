import LovelockCoefficients

/-!
# The classification, run against the two maps it classifies

`LovelockKillsWeyl.classification` is this estate's headline result and it was proved yesterday.
**The strongest available check on it is to feed it the two maps it says span everything and see
whether the formula reproduces them.** It does, and this file is that check.

## Why this is a check and not decoration

The classification's right-hand side is `α·ricci R + β·scal R·δ` with `α` and `β` **computed from
`T`'s own values** at two explicit tensors. If the `KillsWeyl` proof, the reduction, or the
coefficient bookkeeping carried a sign or a factor error, running the formula on `ricci` itself
would produce something other than `ricci R`. **`AlgebraicCurvature` §15 set this standard for the
`n = 2` theorem (`lovelock_two_ricci`) and `LovelockDiagonalise` §4 repeated it at `n = 3`; this is
the same standard applied at every `n ≥ 3`.**

## What is proved

* `ricci_hadd`, `ricci_hsmul`, `ricci_hequiv` — `ricci` satisfies the three hypotheses, from
  `LovelockDiagonalise.ricci_add`, `AlgebraicCurvature.ricci_smul` and `ricci_act`;
* **`classification_at_ricci`** — the classification instantiated at `T = ricci`;
* **`ricci_alpha`, `ricci_beta`** — its coefficients come out **`α = 1` and `β = 0`**, so the
  formula returns `ricci R` exactly. **Both slots are checked**: `β = 0` requires the `constCurv`
  term and the `α/n` correction to cancel, which they do;
* `scalMap`, `scal_add`, `scalMap_hadd`, `scalMap_hsmul`, `scalMap_hequiv` — the other basis map
  `R ↦ scal R · δ` and its three hypotheses. `scal_add` was absent from the estate;
* **`scalMap_alpha`, `scalMap_beta`** — and there the coefficients come out **`α = 0`, `β = 1`**,
  again returning the map itself.

**So the two maps the classification names are both in its own image with the right coefficients**,
and the family it classifies is non-empty — the `§3` standard this estate applies to every
classification theorem.

## What this does not do

**It does not re-prove the classification** and it is not independent of it: both theorems here are
instances. What it rules out is a mis-stated conclusion — a wrong coefficient, a wrong sign, a
missing factor — which is the failure mode a correct-looking proof of a *reduction* cannot catch.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockInstances

open AlgebraicCurvature LovelockProjections LovelockReduction LovelockDiagonalWitness
  LovelockDiagonalise LovelockKillsWeyl LovelockCoefficients Finset

variable {n : ℕ}

/-- `ricci` satisfies the classification's three hypotheses. -/
theorem ricci_hadd (R S : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ricci (fun a b c d => R a b c d + S a b c d) = fun b c => ricci R b c + ricci S b c :=
  ricci_add R S

theorem ricci_hsmul (lam : ℝ) (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ricci (fun a b c d => lam * R a b c d) = fun b c => lam * ricci R b c :=
  funext fun b => funext fun c => ricci_smul lam R b c

theorem ricci_hequiv (Q : Fin n → Fin n → ℝ) (hQ : IsOrth Q)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ) (_ : IsAlgCurv R) (b c : Fin n) :
    ricci (act Q R) b c = act2 Q (ricci R) b c := ricci_act hQ R b c

/-- **THE CLASSIFICATION, RUN ON `ricci` ITSELF.** -/
theorem classification_at_ricci (hn3 : 3 ≤ n) (i : Fin n) {i₀ j₀ : Fin n} (hij₀ : i₀ ≠ j₀)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R) (b c : Fin n) :
    ricci R b c
      = ricci (ricciSeed (hIJ i₀ j₀)) i₀ i₀ * ricci R b c
        + (ricci (constCurv n) i i / ((n : ℝ) * ((n : ℝ) - 1))
            - ricci (ricciSeed (hIJ i₀ j₀)) i₀ i₀ / (n : ℝ)) * scal R * delta b c :=
  classification (T := ricci) hn3 i hij₀ ricci_hadd ricci_hsmul
    (fun Q hQ S hS b' c' => ricci_hequiv Q hQ S hS b' c') hR b c

/-- **AND ITS COEFFICIENTS COME OUT `α = 1`** … -/
theorem ricci_alpha (hn3 : 3 ≤ n) {i₀ j₀ : Fin n} (hij₀ : i₀ ≠ j₀) :
    ricci (ricciSeed (hIJ i₀ j₀)) i₀ i₀ = 1 := by
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
  have htr : ∑ a, hIJ i₀ j₀ a a = 0 := hIJ_trace hij₀
  have h := ricci_ricciSeed (hIJ i₀ j₀) i₀ i₀
  rw [htr, delta_self] at h
  rw [h, hIJ_at_i]
  field_simp
  ring

/-- … **and `β = 0`**, so the formula returns `ricci R` exactly. -/
theorem ricci_beta (hn3 : 3 ≤ n) (i : Fin n) :
    ricci (constCurv n) i i / ((n : ℝ) * ((n : ℝ) - 1))
      - ricci (ricciSeed (hIJ (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)) ⟨0, by omega⟩ ⟨0, by omega⟩
        / (n : ℝ) = 0 := by
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hij : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    intro hc
    exact absurd (congrArg Fin.val hc) (by norm_num)
  rw [ricci_alpha hn3 hij, ricci_constCurv, delta_self, mul_one]
  field_simp
  ring

/-! ## The other basis map -/

/-- `scalMap R = scal R · δ`. -/
def scalMap (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) : ℝ := scal R * delta b c

theorem scal_add (R S : Fin n → Fin n → Fin n → Fin n → ℝ) :
    scal (fun a b c d => R a b c d + S a b c d) = scal R + scal S := by
  simp only [scal, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => congrFun (congrFun (ricci_add R S) b) b

theorem scalMap_hadd (R S : Fin n → Fin n → Fin n → Fin n → ℝ) :
    scalMap (fun a b c d => R a b c d + S a b c d)
      = fun b c => scalMap R b c + scalMap S b c := by
  funext b c; simp only [scalMap, scal_add]; ring

theorem scalMap_hsmul (lam : ℝ) (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    scalMap (fun a b c d => lam * R a b c d) = fun b c => lam * scalMap R b c := by
  funext b c; simp only [scalMap, scal_smul]; ring

theorem scalMap_hequiv (Q : Fin n → Fin n → ℝ) (hQ : IsOrth Q)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ) (_ : IsAlgCurv R) (b c : Fin n) :
    scalMap (act Q R) b c = act2 Q (scalMap R) b c := by
  have h : act2 Q (scalMap R) b c = scal R * act2 Q delta b c := by
    simp only [scalMap, act2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [h, act2_delta hQ, scalMap, scal_act hQ]

/-- **AND ON `scalMap`, THE COEFFICIENTS COME OUT `α = 0`, `β = 1`.** -/
theorem scalMap_alpha {i₀ j₀ : Fin n} (hij₀ : i₀ ≠ j₀) :
    scalMap (ricciSeed (hIJ i₀ j₀)) i₀ i₀ = 0 := by
  simp only [scalMap]
  rw [scal_ricciSeed_of_traceless (hIJ_trace hij₀), zero_mul]

theorem scalMap_beta (hn3 : 3 ≤ n) (i : Fin n) {i₀ j₀ : Fin n} (hij₀ : i₀ ≠ j₀) :
    scalMap (constCurv n) i i / ((n : ℝ) * ((n : ℝ) - 1))
      - scalMap (ricciSeed (hIJ i₀ j₀)) i₀ i₀ / (n : ℝ) = 1 := by
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  rw [scalMap_alpha hij₀]
  simp only [scalMap]
  rw [scal_constCurv, delta_self, mul_one]
  field_simp
  ring

end LovelockInstances
