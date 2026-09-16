/-
  WheelSpectrum: the wheel — the cone chain's first COMPUTED rim, and the price unit 79 named,
  paid

  WHY THIS FILE EXISTS. `UNLOCK_WATCHLIST` **L34992** has asked for the wheel since 2026-09-11,
  and unit 79 — which generalised the wheel to the cone over any `d`-regular graph — **priced the
  instance wrongly, was corrected before its own commit by `estateclaim_scan`, and left the
  corrected price in writing**: the instance owes *three* things, not none.

      1. `Q = 2I + A` on a cycle, which is trivial because a cycle is 2-regular.
      2. **A REAL eigenvector where the estate holds a complex character.**
         `CycleLaplacianSpectrum.chi` is `ℂ`-valued and every cycle theorem in this estate is
         stated over `ℂ`; `ConeSignlessSpectrum.cone_signless_rim_eigen` is over `ℝ`.
      3. **`∑ chi = 0` — the character sum the general file was designed to avoid.**

  All three are paid here, and the third is paid with a geometric series rather than with
  trigonometry: `zeta` is a primitive root by `Complex.isPrimitiveRoot_exp`, so `zeta ^ k ≠ 1`
  for `0 < k < N` and `geom_sum_eq` does the rest. **That name is in the ROOT namespace, not
  `Finset`, and this header said `Finset.geom_sum_eq` until `--cites-lean` flagged it — after
  the proof below had it right all along.** Third citation in this batch written from memory
  with the wrong qualifier, which makes it a population rather than a slip.

  **WHAT THIS MAKES TRUE FOR THE FIRST TIME IN THIS CHAIN.** Units 79, 80, 82, 83 and 86 all
  carry the same fence: every statement is relative to `finrank (rimEig G _)`, *which this chain
  has computed for no `G`*. **Here is a `G`.** With the rim's modes in hand the wheel's spectrum
  is described as follows, all of it proved:

  * the top is `hubRootPlus (n + 3) 2` — **an explicit real number**, greatest, and **simple**
    (unit 86, instantiated);
  * `3 + 2cos(2πk/(n+3))` is an eigenvalue for every `k ≠ 0`;
  * and by unit 80's dichotomy **every** eigenvalue is a hub root or of that rim form.

  WHAT IS PROVED.

  * **`cycle_reg`** — the cycle is 2-regular, from Mathlib's `cycleGraph_degree_three_le`; the
    hypothesis every cone theorem takes.
  * **`zeta_add_inv`** — `zeta ^ k + (zeta ^ k)⁻¹ = ↑(2 cos(2πk/N))`, off the estate's
    `SignlessCycleSpectrum.signless_eigenvalue_eq_real` by subtracting the `2`. **This is the
    step that makes the coefficient REAL**, and everything else in the file depends on it.
  * **`adj_mulVec_chi`** — the ADJACENCY matrix on the character, derived from the estate's
    signless theorem by peeling the degree diagonal rather than re-running the three-line
    neighbour computation (`ERRATUM 348`).
  * **`rchi`, `rchi_zero`, `rchi_ne_zero`** — the real eigenvector, `Re(chi)`, nonzero because
    its `0` coordinate is `1`.
  * **`adj_mulVec_rchi`** — and it IS an eigenvector over `ℝ`, at `2cos(2πk/N)`: take real parts,
    which works only because the coefficient is real.
  * **`sum_chi_eq_zero`, `sum_rchi_eq_zero`** — the character sum, for `k ≠ 0`.
  * **`rchi_mem_rimEig`** — so `Re(chi)` lands in the rim's zero-sum eigenspace, which is what
    the cone theorems consume.
  * **`wheel_rim_eigenvalue`** — `3 + 2cos(2πk/(n+3))` is an eigenvalue of the wheel's signless
    Laplacian, with a nonzero eigenvector exhibited.
  * **`one_le_finrank_wheel_rim`** — and its eigenspace is at least a line.
  * **`isGreatest_wheelSpectrum`, `finrank_wheel_top`** — the wheel's top, explicit and simple.
  * **`wheel_le_five_of_ne_top`** — and everything below the top is at most `5`, which is unit
    86's ceiling at `d = 2`.

  WHAT IS **NOT** CLAIMED.

  * **THE RIM'S MULTIPLICITIES ARE NOT COMPUTED, only bounded below by one.** `Re(chi k)` and
    `Im(chi k)` are both eigenvectors at the same value and are independent for
    `k ∉ {0, N/2}` — **and proving that independence is exactly the step this chain has avoided
    in every unit.** So the rim side gives eigenVALUES with a nonzero eigenspace, not a
    multiplicity table. The fence has moved from *no `G`* to *this `G`, one direction*.
  * **THE RIM VALUES ARE NOT PROVED TO EXHAUST THE RIM.** Unit 80's dichotomy says every
    eigenvalue is a hub root or `3 + μ` with `μ` a zero-sum adjacency eigenvalue; that the
    `2cos(2πk/N)` are ALL such `μ` would need a dimension count, which is the same missing
    independence.
  * **NOTHING IS SAID ABOUT WHICH EIGENVALUE IS SECOND.** `5` bounds them all; nothing shows it
    attained, and the cosines are not compared with each other.
  * **NOTHING ABOUT THE CASCADE, THE SPINE OR ANY WALL.**

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import ConeTopEigen
import SignlessCycleSpectrum
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace WheelSpectrum

open SimpleGraph LaplacianSignless Matrix
open CycleLaplacianSpectrum SignlessCycleSpectrum
open ConeSignlessSpectrum ConeSignlessExhaustion ConeMultiplicity ConeMultiplicityExact
open ConeTopEigen

/-! ## The cycle as a rim -/

section Rim

variable (n : ℕ) (k : Fin (n + 3))

/-- The cycle is 2-regular — the hypothesis every theorem of the cone chain takes. -/
theorem cycle_reg : ∀ i : Fin (n + 3), (cycleGraph (n + 3)).degree i = 2 :=
  fun _ => cycleGraph_degree_three_le

/-- **THE COEFFICIENT IS REAL**, and this is the step the whole file rests on: off the estate's
`signless_eigenvalue_eq_real` by subtracting the degree. -/
theorem zeta_add_inv :
    zeta (n + 3) ^ (k : ℕ) + (zeta (n + 3) ^ (k : ℕ))⁻¹
      = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / (n + 3)) : ℝ) : ℂ) := by
  have h := signless_eigenvalue_eq_real n k
  have h2 : ((2 + 2 * Real.cos (2 * Real.pi * (k : ℕ) / (n + 3)) : ℝ) : ℂ)
      = 2 + ((2 * Real.cos (2 * Real.pi * (k : ℕ) / (n + 3)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h2] at h
  linear_combination h

/-- **THE ADJACENCY MATRIX ON THE CHARACTER**, obtained by peeling the degree diagonal off the
estate's signless theorem rather than re-running its neighbour computation (`ERRATUM 348`). -/
theorem adj_mulVec_chi :
    (cycleGraph (n + 3)).adjMatrix ℂ *ᵥ chi (n + 3) k
      = (zeta (n + 3) ^ (k : ℕ) + (zeta (n + 3) ^ (k : ℕ))⁻¹) • chi (n + 3) k := by
  funext j
  have h := congrFun (cx_signlessLap_mulVec_chi n k) j
  rw [cx_signlessLap_mulVec, cycleGraph_degree_three_le] at h
  rw [adjMatrix_mulVec_apply]
  simp only [Pi.smul_apply, smul_eq_mul] at h ⊢
  push_cast at h
  linear_combination h

end Rim

/-! ## The real eigenvector -/

section Real

variable (n : ℕ) (k : Fin (n + 3))

/-- The real part of the character. -/
noncomputable def rchi : Fin (n + 3) → ℝ := fun j => (chi (n + 3) k j).re

theorem rchi_zero : rchi n k 0 = 1 := by
  simp [rchi, chi, zeta]

theorem rchi_ne_zero : rchi n k ≠ 0 := by
  intro hc
  have := congrFun hc 0
  rw [rchi_zero] at this
  exact one_ne_zero this

/-- **AND IT IS AN EIGENVECTOR OVER `ℝ`**, at `2cos(2πk/N)`. Taking real parts works only
because `zeta_add_inv` made the coefficient real. -/
theorem adj_mulVec_rchi :
    (cycleGraph (n + 3)).adjMatrix ℝ *ᵥ rchi n k
      = (2 * Real.cos (2 * Real.pi * (k : ℕ) / (n + 3))) • rchi n k := by
  funext j
  have h := congrFun (adj_mulVec_chi n k) j
  rw [adjMatrix_mulVec_apply, zeta_add_inv] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [adjMatrix_mulVec_apply]
  simp only [rchi, Pi.smul_apply, smul_eq_mul]
  rw [← Complex.re_sum, h, Complex.re_ofReal_mul]

/-- **THE CHARACTER SUM**, for a nontrivial character: a geometric series, not trigonometry. -/
theorem sum_chi_eq_zero (hk : k ≠ 0) : ∑ j, chi (n + 3) k j = 0 := by
  have hprim : IsPrimitiveRoot (zeta (n + 3)) (n + 3) := by
    rw [CycleLaplacianSpectrum.zeta.eq_1]
    exact Complex.isPrimitiveRoot_exp _ (by omega)
  have hk0 : (k : ℕ) ≠ 0 := by
    intro h
    exact hk (Fin.ext h)
  have hne : zeta (n + 3) ^ (k : ℕ) ≠ 1 := hprim.pow_ne_one_of_pos_of_lt hk0 k.isLt
  have hpow : (zeta (n + 3) ^ (k : ℕ)) ^ (n + 3) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, zeta_pow_card (by omega), one_pow]
  have hrw : ∀ j : Fin (n + 3),
      chi (n + 3) k j = (zeta (n + 3) ^ (k : ℕ)) ^ (j : ℕ) := by
    intro j
    rw [chi, ← pow_mul, mul_comm]
  rw [Finset.sum_congr rfl fun j _ => hrw j, Fin.sum_univ_eq_sum_range,
    geom_sum_eq hne, hpow, sub_self, zero_div]

theorem sum_rchi_eq_zero (hk : k ≠ 0) : ∑ j, rchi n k j = 0 := by
  simp only [rchi]
  rw [← Complex.re_sum, sum_chi_eq_zero n k hk, Complex.zero_re]

/-- **SO `Re(chi)` LANDS IN THE RIM'S ZERO-SUM EIGENSPACE**, which is the object every cone
theorem consumes. -/
theorem rchi_mem_rimEig (hk : k ≠ 0) :
    rchi n k ∈ rimEig (cycleGraph (n + 3))
      (2 * Real.cos (2 * Real.pi * (k : ℕ) / (n + 3))) :=
  (mem_rimEig _).2 ⟨adj_mulVec_rchi n k, sum_rchi_eq_zero n k hk⟩

end Real

/-! ## The wheel

**THE WHEEL IS NOT GIVEN A DEFINITION OF ITS OWN, and that is a decision rather than laziness.**
`def wheelGraph n := coneGraph (cycleGraph (n + 3))` was written first and deleted: a new
definition does not inherit `coneGraph`'s `DecidableRel` instance, so every statement below had
to carry one by hand and every rewrite between the two spellings hit a *motive is not type
correct* on the instance argument. Writing `coneGraph (cycleGraph (n + 3))` throughout costs one
line of reading and no fights. -/

section Wheel

variable (n : ℕ) (k : Fin (n + 3))

/-- **A RIM EIGENVALUE OF THE WHEEL**, exhibited with a nonzero eigenvector: for every
`k ≠ 0`, `3 + 2cos(2πk/(n+3))` is an eigenvalue of the wheel's signless Laplacian. -/
theorem wheel_rim_eigenvalue (hk : k ≠ 0) :
    ∃ x : Option (Fin (n + 3)) → ℝ, x ≠ 0 ∧
      signlessLap (coneGraph (cycleGraph (n + 3))) *ᵥ x
        = (3 + 2 * Real.cos (2 * Real.pi * (k : ℕ) / (n + 3))) • x := by
  refine ⟨liftRim (rchi n k), ?_, ?_⟩
  · exact liftRim_ne_zero (rchi_ne_zero n k)
  · have h := cone_signless_rim_eigen (cycleGraph (n + 3)) (cycle_reg n) (rchi n k)
      (sum_rchi_eq_zero n k hk) (adj_mulVec_rchi n k)
    rw [h]
    congr 1
    push_cast
    ring

/-- and its eigenspace is at least a line. -/
theorem one_le_finrank_wheel_rim (hk : k ≠ 0) :
    1 ≤ Module.finrank ℝ (coneEig (cycleGraph (n + 3))
      (3 + 2 * Real.cos (2 * Real.pi * (k : ℕ) / (n + 3)))) := by
  refine Submodule.one_le_finrank_iff.2 ?_
  rw [Submodule.ne_bot_iff]
  obtain ⟨x, hx0, hxe⟩ := wheel_rim_eigenvalue n k hk
  exact ⟨x, (mem_coneEig _).2 hxe, hx0⟩

/-- **THE WHEEL'S TOP EIGENVALUE**, explicit and greatest — unit 86 at `d = 2`. -/
theorem isGreatest_wheelSpectrum :
    IsGreatest {lam : ℝ | ∃ x : Option (Fin (n + 3)) → ℝ, x ≠ 0 ∧
        signlessLap (coneGraph (cycleGraph (n + 3))) *ᵥ x = lam • x} (hubRootPlus (n + 3) 2) := by
  have h := isGreatest_coneSpectrum (cycleGraph (n + 3)) (cycle_reg n)
  simp only [Fintype.card_fin] at h
  exact h

/-- **AND IT IS SIMPLE.** -/
theorem finrank_wheel_top :
    Module.finrank ℝ (coneEig (cycleGraph (n + 3)) (hubRootPlus (n + 3) 2)) = 1 := by
  have h := finrank_coneEig_hubRootPlus (cycleGraph (n + 3)) (cycle_reg n)
  have hc : Fintype.card (Fin (n + 3)) = n + 3 := Fintype.card_fin _
  rw [hc] at h
  exact h

/-- **EVERYTHING BELOW THE TOP IS AT MOST `5`** — unit 86's ceiling at `d = 2`. -/
theorem wheel_le_five_of_ne_top {lam : ℝ} {x : Option (Fin (n + 3)) → ℝ} (hx : x ≠ 0)
    (hQ : signlessLap (coneGraph (cycleGraph (n + 3))) *ᵥ x = lam • x)
    (hne : lam ≠ hubRootPlus (n + 3) 2) :
    lam ≤ 5 := by
  have hne' : lam ≠ hubRootPlus (Fintype.card (Fin (n + 3))) 2 := by
    simp only [Fintype.card_fin]; exact hne
  have h := le_two_mul_add_one_of_ne_hubRootPlus (cycleGraph (n + 3)) (cycle_reg n) hx hQ hne'
  norm_num at h
  exact h

end Wheel

end WheelSpectrum
