import LovelockDiagonalise
import LovelockWitnessTransport

/-!
# The traceless-Ricci summand is irreducible — and this one actually needs the group

`LovelockScalarLine` filled the second entry of `WALLS` §W5.0 §5f's four-summand map, and its whole
header was an argument for why that entry was cheap: the scalar summand is a **line**, a line has no
proper non-zero subspace whether or not a group is watching, and `scalarLine_irreducible` carries no
`act`-stability hypothesis because it needs none.

**This file fills the third entry, and the contrast is the point.** Here the proof uses
`act2`-stability **twice**, in two different ways; delete either use and the argument dies. And the
contrast is a theorem in the file rather than an impression: `act2_nontrivial_on_hIJ` exhibits a
frame change that moves an element of this summand, where `LovelockScalarLine.act_onScalarLine`
proves nothing moves at all.

## What is proved

* `trace_act2` — the trace of a **2-tensor** is unchanged by an orthogonal frame change. Absent from
  the estate before: `AlgebraicCurvature` has `act2_delta` (the metric specifically),
  and `ricci_act` and `scal_act` (traces of a four-index array), and nothing that says `act2`
  preserves the trace of a general 2-tensor;
* `exists_ne_diag` — a non-zero traceless diagonal tensor has **two different diagonal entries**.
  Tracelessness plus "all entries equal" forces `n · c = 0`;
* `diag_sub_swap` — a diagonal tensor minus its `(i j)`-transpose is `(d_ii − d_jj) · hIJ i j`.
  Four cases, all `ring`;
* **`tracelessSym_irreducible`** — the theorem. A family `V` of 2-tensors closed under sums, scalar
  multiples, pointwise equality and **every orthogonal frame change**, holding of one non-zero
  symmetric traceless tensor, holds of **every** symmetric traceless tensor;
* `exists_ne_zero_tracelessSym` — at `n ≥ 2` such a seed exists (`hIJ i j`), so the theorem is not
  about the empty family;
* **`act2_nontrivial_on_hIJ`** — and the frame change does **not** fix this summand pointwise:
  transposing `i` and `j` negates `hIJ i j`. Compare `LovelockScalarLine.act_onScalarLine`, where
  nothing moves at all;
* `ricciSeed_add` and **`ricciSummand_irreducible`** — the same statement transported through
  `LovelockDiagonalWitness.ricciSeed`, which is the traceless-Ricci summand's parametrisation. The
  transport is four closure checks and no new mathematics, because `act_ricciSeed` and
  `ricciSeed_smul` were already there.

## Where the group is used, named precisely

**Twice, and neither use is removable.**

1. **Diagonalisation.** `LovelockDiagonalise.diagonalisable` — Mathlib's real-symmetric spectral
   theorem, bridged through `isOrth_of_mem_orthogonalGroup` — turns the seed into a diagonal tensor
   in some orthogonal frame, and `act2`-stability is what keeps it inside `V`. Without it the seed
   is an arbitrary symmetric tensor and there is nothing to compare entries of.
2. **Permutations.** `pairMove` carries any ordered pair of distinct indices to any other, and
   `act2`-stability again is what carries `hIJ i j` to `hIJ p q`. Without it one witness is all
   there is, and the expansion has nothing to expand into.

Then `LovelockDiagonalSum.hIJ_expand` — which already existed, and which the fourth review question
found before it was re-proved — assembles every diagonal traceless tensor from the witnesses, and
`act2_transp_act2` carries the conclusion back out of the adapted frame.

## What this does not do

**It says nothing about the Weyl summand.** The argument's engine is the spectral theorem for real
symmetric **matrices**, applied to a 2-tensor. The Weyl summand is not a space of 2-tensors and has
no such normal form in Mathlib or here — that is the same wall `WALLS` §W5.0 §5c's step 3 hit, and
§5d's antisymmetric half, and it is not weakened by anything in this file.

**So the map now reads: `Curv^⊥` reducible, scalar irreducible, traceless-Ricci irreducible, Weyl
unknown.** Three of four, with the fourth being the whole question. **`KillsWeyl` at `n ≥ 4` is
untouched and the watchlist item does not move.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockRicciIrreducible

open AlgebraicCurvature LovelockProjections LovelockEquivariance LovelockFrameInverse
  LovelockDiagonalWitness LovelockDiagonalSum LovelockDiagonalise LovelockWitnessTransport Finset

variable {n : ℕ} {Q : Fin n → Fin n → ℝ}

/-! ## 1. Three small facts, none of which was in the estate -/

/-- **THE TRACE OF A 2-TENSOR SURVIVES A FRAME CHANGE.** `IsOrth.cols` collapses the double sum. -/
theorem trace_act2 (hQ : IsOrth Q) (S : Fin n → Fin n → ℝ) :
    ∑ b, act2 Q S b b = ∑ b, S b b := by
  have step : ∀ b : Fin n, act2 Q S b b = ∑ b', ∑ c', Q b b' * Q b c' * S b' c' := fun _ => rfl
  rw [Finset.sum_congr rfl fun b _ => step b]
  rw [Finset.sum_comm]
  have inner : ∀ b' : Fin n, ∑ b : Fin n, ∑ c', Q b b' * Q b c' * S b' c'
      = ∑ c', delta b' c' * S b' c' := by
    intro b'
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [← Finset.sum_mul, hQ.cols b' c']
  rw [Finset.sum_congr rfl fun b' _ => inner b']
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [Finset.sum_eq_single b']
  · rw [delta_self, one_mul]
  · intro c' _ hc'; simp [delta, Ne.symm hc']
  · intro h; exact absurd (Finset.mem_univ b') h

/-- **A NON-ZERO TRACELESS DIAGONAL TENSOR HAS TWO DIFFERENT DIAGONAL ENTRIES.** If they were all
equal the trace would be `n` times that value, hence zero, hence the tensor. -/
theorem exists_ne_diag {d : Fin n → Fin n → ℝ}
    (hdiag : ∀ b c, b ≠ c → d b c = 0) (htr : ∑ a, d a a = 0)
    {x y : Fin n} (hxy : d x y ≠ 0) :
    ∃ i j : Fin n, i ≠ j ∧ d i i ≠ d j j := by
  have hxeq : x = y := by
    by_contra h
    exact hxy (hdiag x y h)
  subst hxeq
  by_contra hcon
  have hall : ∀ j : Fin n, d j j = d x x := by
    intro j
    by_cases h : x = j
    · rw [h]
    · by_contra hne
      exact hcon ⟨x, j, h, fun he => hne he.symm⟩
  have hsum : ∑ a : Fin n, d a a = (n : ℝ) * d x x := by
    rw [Finset.sum_congr rfl fun a _ => hall a, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [htr] at hsum
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr x.pos.ne'
  rcases mul_eq_zero.mp hsum.symm with h | h
  · exact hn0 h
  · exact hxy h

/-- **AND THE DIFFERENCE OF A DIAGONAL TENSOR AND ITS `(i j)`-TRANSPOSE IS A MULTIPLE OF THE
WITNESS.** This is what turns "two entries differ" into "the witness is in the family". -/
theorem diag_sub_swap {d : Fin n → Fin n → ℝ} (hdiag : ∀ b c, b ≠ c → d b c = 0)
    (i j : Fin n) (hij : i ≠ j) (x y : Fin n) :
    d x y - d (Equiv.swap i j x) (Equiv.swap i j y)
      = (d i i - d j j) * hIJ i j x y := by
  rcases eq_or_ne x y with rfl | hxy
  · by_cases hxi : x = i
    · subst hxi
      rw [Equiv.swap_apply_left, hIJ_at_i]
      ring
    · by_cases hxj : x = j
      · subst hxj
        rw [Equiv.swap_apply_right, hIJ_at_j hij]
        ring
      · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj, hIJ_at_other hxi hxj]
        ring
  · rw [hdiag x y hxy, hdiag _ _ (fun h => hxy ((Equiv.swap i j).injective h)),
      hIJ_offDiag i j hxy]
    ring

/-! ## 2. The theorem -/

variable {V : (Fin n → Fin n → ℝ) → Prop}

/-- **THE TRACELESS SYMMETRIC 2-TENSORS HAVE NO PROPER NON-ZERO INVARIANT SUBFAMILY.** `V` is
closed under sums, scalar multiples, pointwise equality and every orthogonal frame change, and holds
of one non-zero symmetric traceless tensor; then it holds of every symmetric traceless tensor.

**Unlike `LovelockScalarLine.scalarLine_irreducible`, this genuinely consumes `hact`** — once to
diagonalise the seed and once to move the witness around. Read the header for where. -/
theorem tracelessSym_irreducible
    (hD : Diagonalisable n)
    (hadd : ∀ A B, V A → V B → V (fun x y => A x y + B x y))
    (hsmul : ∀ (lam : ℝ) A, V A → V (fun x y => lam * A x y))
    (hcongr : ∀ A B : Fin n → Fin n → ℝ, (∀ x y, A x y = B x y) → V A → V B)
    (hact : ∀ P, IsOrth P → ∀ A, V A → V (act2 P A))
    {h₀ : Fin n → Fin n → ℝ} (hV : V h₀)
    (hsym₀ : ∀ x y, h₀ x y = h₀ y x) (htr₀ : ∑ a, h₀ a a = 0)
    (hne₀ : ∃ x y, h₀ x y ≠ 0)
    {h : Fin n → Fin n → ℝ} (hsym : ∀ x y, h x y = h y x) (htr : ∑ a, h a a = 0) :
    V h := by
  classical
  obtain ⟨x₀, y₀, hx₀⟩ := hne₀
  have hzero : V (fun _ _ => (0 : ℝ)) :=
    hcongr _ _ (fun x y => zero_mul _) (hsmul 0 h₀ hV)
  have hsub : ∀ A B, V A → V B → V (fun x y => A x y - B x y) := by
    intro A B hA hB
    exact hcongr _ _ (fun x y => by ring) (hadd A _ hA (hsmul (-1) B hB))
  -- 1. diagonalise the seed; the frame change keeps it inside `V`
  obtain ⟨Q, hQ, hdQ⟩ := hD h₀ hsym₀
  have hVd : V (act2 Q h₀) := hact Q hQ h₀ hV
  have hdtr : ∑ a, act2 Q h₀ a a = 0 := by rw [trace_act2 hQ, htr₀]
  have hdne : ∃ x y, act2 Q h₀ x y ≠ 0 := by
    by_contra hcon
    have hall : ∀ x y, act2 Q h₀ x y = act2 Q (fun _ _ => (0 : ℝ)) x y := by
      intro x y
      have h1 : act2 Q h₀ x y = 0 := by
        by_contra hc
        exact hcon ⟨x, y, hc⟩
      rw [h1]
      simp only [act2]
      exact (Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => by ring).symm
    exact hx₀ (eq_of_act2_eq hQ hall x₀ y₀)
  obtain ⟨x₁, y₁, hx₁⟩ := hdne
  obtain ⟨i, j, hij, hdij⟩ := exists_ne_diag hdQ hdtr hx₁
  -- 2. one witness, from the transposition
  have hVswap : V (act2 (permMat (Equiv.swap i j)) (act2 Q h₀)) :=
    hact _ (isOrth_permMat _) _ hVd
  have hVdiff : V (fun x y => (act2 Q h₀ i i - act2 Q h₀ j j) * hIJ i j x y) := by
    refine hcongr _ _ (fun x y => ?_) (hsub _ _ hVd hVswap)
    rw [act2_permMat]
    exact diag_sub_swap hdQ i j hij x y
  have hcoef : act2 Q h₀ i i - act2 Q h₀ j j ≠ 0 := sub_ne_zero.mpr hdij
  have hVij : V (hIJ i j) := by
    refine hcongr _ _ (fun x y => ?_) (hsmul (act2 Q h₀ i i - act2 Q h₀ j j)⁻¹ _ hVdiff)
    field_simp
  -- 3. every witness, from `pairMove`
  have hVpq : ∀ p q : Fin n, p ≠ q → V (hIJ p q) := by
    intro p q hpq
    have hspec := hact (permMat (pairMove p q i j)) (isOrth_permMat _) _ hVij
    refine hcongr _ _ (fun x y => ?_) hspec
    rw [act2_permMat, hIJ_perm]
    have h1 : (pairMove p q i j).symm i = p := by
      rw [Equiv.symm_apply_eq]
      exact (pairMove_fst p q i j hpq hij).symm
    have h2 : (pairMove p q i j).symm j = q := by
      rw [Equiv.symm_apply_eq]
      exact (pairMove_snd p q i j).symm
    rw [h1, h2]
  -- 4. every diagonal traceless tensor, by the expansion
  have hVdiag : ∀ d : Fin n → Fin n → ℝ, (∀ x y, x ≠ y → d x y = 0) → (∑ a, d a a = 0) → V d := by
    intro d hdd hdt
    have hexp : ∀ x y, d x y = ∑ i ∈ Finset.univ.erase x₀, d i i * hIJ i x₀ x y :=
      fun x y => hIJ_expand hdd hdt x₀ x y
    have hsum : V (∑ i ∈ Finset.univ.erase x₀, fun x y => d i i * hIJ i x₀ x y) := by
      refine Finset.sum_induction _ V (fun A B hA hB => hadd A B hA hB) hzero ?_
      intro i hi
      exact hsmul (d i i) _ (hVpq i x₀ (Finset.ne_of_mem_erase hi))
    refine hcongr _ _ (fun x y => ?_) hsum
    rw [Finset.sum_apply, Finset.sum_apply]
    exact (hexp x y).symm
  -- 5. and back out of the adapted frame
  obtain ⟨Q', hQ', hdQ'⟩ := hD h hsym
  have hd'tr : ∑ a, act2 Q' h a a = 0 := by rw [trace_act2 hQ', htr]
  have hVd' : V (act2 Q' h) := hVdiag _ hdQ' hd'tr
  refine hcongr _ _ (fun x y => ?_) (hact (transp Q') (isOrth_transp hQ') _ hVd')
  exact act2_transp_act2 hQ' h x y

/-! ## 3. Non-vacuity, and the contrast with the scalar line -/

/-- The family is non-empty at `n ≥ 2`: `hIJ i j` is symmetric, traceless and non-zero. -/
theorem exists_ne_zero_tracelessSym (hn : 2 ≤ n) :
    ∃ h : Fin n → Fin n → ℝ,
      (∀ x y, h x y = h y x) ∧ (∑ a, h a a = 0) ∧ ∃ x y, h x y ≠ 0 := by
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  have hne : (⟨0, h0⟩ : Fin n) ≠ ⟨1, h1⟩ := by
    intro hc
    exact absurd (congrArg Fin.val hc) (by norm_num)
  refine ⟨hIJ ⟨0, h0⟩ ⟨1, h1⟩, hIJ_symm _ _, hIJ_trace hne, ⟨⟨0, h0⟩, ⟨0, h0⟩, ?_⟩⟩
  rw [hIJ_at_i]
  norm_num

/-- **AND THE FRAME CHANGE DOES NOT FIX THIS SUMMAND POINTWISE.** Transposing `i` and `j` negates
`hIJ i j`, so the action here is genuinely non-trivial — the opposite of
`LovelockScalarLine.act_onScalarLine`, where every element is fixed and irreducibility follows for
free. -/
theorem act2_nontrivial_on_hIJ {i j : Fin n} (hij : i ≠ j) (x y : Fin n) :
    act2 (permMat (Equiv.swap i j)) (hIJ i j) x y = -(hIJ i j x y) := by
  rw [act2_permMat, hIJ_perm]
  have h1 : (Equiv.swap i j).symm i = j := by
    rw [Equiv.symm_swap, Equiv.swap_apply_left]
  have h2 : (Equiv.swap i j).symm j = i := by
    rw [Equiv.symm_swap, Equiv.swap_apply_right]
  rw [h1, h2, hIJ_swap hij]

/-! ## 4. Transported to the summand -/

theorem ricciSeed_add (g₁ g₂ : Fin n → Fin n → ℝ) (a b c d : Fin n) :
    ricciSeed (fun x y => g₁ x y + g₂ x y) a b c d
      = ricciSeed g₁ a b c d + ricciSeed g₂ a b c d := by
  simp only [ricciSeed, kn]; ring

/-- **THE TRACELESS-RICCI SUMMAND IS IRREDUCIBLE**, in the same idiom. Four closure checks and no
new mathematics: `act_ricciSeed` and `ricciSeed_smul` already carried the seed across the frame
change and across scalars. -/
theorem ricciSummand_irreducible
    (hD : Diagonalisable n)
    {W : (Fin n → Fin n → Fin n → Fin n → ℝ) → Prop}
    (Wadd : ∀ A B, W A → W B → W (fun a b c d => A a b c d + B a b c d))
    (Wsmul : ∀ (lam : ℝ) A, W A → W (fun a b c d => lam * A a b c d))
    (Wcongr : ∀ A B : Fin n → Fin n → Fin n → Fin n → ℝ,
      (∀ a b c d, A a b c d = B a b c d) → W A → W B)
    (Wact : ∀ P, IsOrth P → ∀ A, W A → W (act P A))
    {h₀ : Fin n → Fin n → ℝ} (hW : W (ricciSeed h₀))
    (hsym₀ : ∀ x y, h₀ x y = h₀ y x) (htr₀ : ∑ a, h₀ a a = 0)
    (hne₀ : ∃ x y, h₀ x y ≠ 0)
    {h : Fin n → Fin n → ℝ} (hsym : ∀ x y, h x y = h y x) (htr : ∑ a, h a a = 0) :
    W (ricciSeed h) := by
  refine tracelessSym_irreducible (V := fun g => W (ricciSeed g)) hD ?_ ?_ ?_ ?_ hW hsym₀ htr₀
    hne₀ hsym htr
  · intro A B hA hB
    exact Wcongr _ _ (fun a b c d => (ricciSeed_add A B a b c d).symm) (Wadd _ _ hA hB)
  · intro lam A hA
    exact Wcongr _ _ (fun a b c d => (ricciSeed_smul lam A a b c d).symm) (Wsmul lam _ hA)
  · intro A B hAB hA
    refine Wcongr _ _ (fun a b c d => ?_) hA
    have hfun : A = B := funext fun x => funext fun y => hAB x y
    rw [hfun]
  · intro P hP A hA
    exact Wcongr _ _ (fun a b c d => congrFun (congrFun (congrFun (congrFun
      (act_ricciSeed hP A) a) b) c) d) (Wact P hP _ hA)

end LovelockRicciIrreducible
