import TorusAttainmentBridge

/-!
# Multiplicities — and the ground state of the lattice field is unique

**THIS FILE EXISTS BECAUSE A CLAIMED BLOCKER WAS NEVER PROBED.** Three consecutive entries of this
campaign named multiplicities as the smallest thing still blocking the spectrum chain, and each said
the same thing about why: that they *"need the characters' orthogonality as a statement about the
basis rather than about a Green's function"*. **That is false, and one probe settles it.** A
diagonalising basis determines every eigenspace's dimension with no inner product anywhere: the
eigenspace at `μ` is spanned by the basis vectors whose eigenvalue is `μ`, that subfamily is
independent because a subfamily of a basis is, and `finrank_span_eq_card` finishes it. **No
orthogonality, no Parseval, no Green's function.** `ERRATUM 358`.

> **`eigenspace_eq_span_of_basis`** — for an arbitrary matrix diagonalised by an arbitrary basis,
> `ker (A − μ)` **is** the span of `{b k : ν k = μ}`. The coefficient computation is the same one
> `SignlessTorusComplete.eigenvalue_iff_of_basis` does; what is new is keeping the surviving
> coefficients rather than deriving a contradiction from them.
>
> **`finrank_eigenspace_of_basis`** — hence its dimension is the number of frequencies carrying
> that eigenvalue, at that same generality.
>
> **`finrank_eigenspace_massive`, `finrank_eigenspace_signless`** — on the periodic lattice in
> every dimension, for both operators the chain has spectra for.
>
> **`nuR_eq_sq_iff`** — `νR = m²` happens **only** at the zero frequency: the `d` cosines are each
> at most `1` and their doubled sum has to reach `2d`, so every one of them is exactly `1`, and a
> cosine equal to `1` on `[0, 2π)` forces the angle to vanish.
>
> **`ground_state_simple`** — therefore the least eigenvalue `m²` of the massive Laplacian on the
> `d`-dimensional periodic lattice has **multiplicity one**. The ground state of the free lattice
> field is unique up to scale, in every dimension and at every side length at least three.

## What is NOT here

**Nothing below computes a multiplicity at any eigenvalue other than the bottom.**
`finrank_eigenspace_massive` reduces every multiplicity to a **counting** question — how many
frequencies share a value of `νR` — and **that counting is not done here**, at the top or anywhere
in between. Whether the top eigenvalue is simple at even side length is a different count (`k` with
every coordinate at `n/2`, unique, so the answer is plainly yes) and **is not proved below**;
whether interior eigenvalues are degenerate is a genuine question about cosine sums and nothing
here touches it.

**These are eigenspace dimensions over `ℂ`.** The real matrix has the same eigenvalues by
`SignlessTorusReal.real_eigenvalue_iff_cx`, but **no claim is made here that real eigenspaces have
the same dimension** — that is a transfer of `finrank`, not of membership, and it is not made.

**No characteristic polynomial appears below and no algebraic multiplicity is stated here.**
`finrank (ker (A − μ))` is the **geometric** multiplicity. For a diagonalisable matrix the two
agree; that agreement is standard, is not stated below, and is not used.

**The box is not reached here.** A boundary and a non-constant degree, so no character family at
all.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusMultiplicity

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection LaplacianSignless
open TorusLaplacianSpectrum SignlessTorusSpectrum SignlessTorusComplete SignlessTorusReal
open MassiveTorusSpectrum

variable {d : ℕ}

/-! ## 1. The eigenspace of a matrix diagonalised by a basis -/

/-- **THE EIGENSPACE AT `μ` IS THE SPAN OF THE BASIS VECTORS WHOSE EIGENVALUE IS `μ`.** No inner
product appears: the two inclusions are the eigenvector equation one way, and the coefficient
computation of `SignlessTorusComplete.eigenvalue_iff_of_basis` the other, keeping the surviving
coefficients instead of contradicting them. -/
theorem eigenspace_eq_span_of_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (b : Module.Basis ι ℂ (ι → ℂ)) (ν : ι → ℂ)
    (hb : ∀ k, A *ᵥ b k = ν k • b k) (μ : ℂ) :
    LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)
      = Submodule.span ℂ (Set.range fun k : {k // ν k = μ} => b k.1) := by
  classical
  have hA : ∀ y : ι → ℂ, A *ᵥ y = Matrix.toLin' A y :=
    fun y => (Matrix.toLin'_apply _ y).symm
  have hmem : ∀ y : ι → ℂ,
      y ∈ LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id) ↔ A *ᵥ y = μ • y := by
    intro y
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h
      rw [← hA y] at h
      exact sub_eq_zero.1 h
    · intro h
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [← hA y, h, sub_self]
  apply le_antisymm
  · intro x hx
    rw [hmem x] at hx
    have hrepr : ∑ j, b.repr x j • b j = x := b.sum_repr x
    have h1 : Matrix.toLin' A x = ∑ j, (ν j * b.repr x j) • b j := by
      conv_lhs => rw [← hrepr]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← hA, hb, smul_smul, mul_comm]
    have h2 : μ • x = ∑ j, (μ * b.repr x j) • b j := by
      conv_lhs => rw [← hrepr]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_smul _ _ _
    have hsum : ∑ j, ((ν j - μ) * b.repr x j) • b j = 0 := by
      have hsplit : ∑ j, ((ν j - μ) * b.repr x j) • b j
          = (∑ j, (ν j * b.repr x j) • b j) - ∑ j, (μ * b.repr x j) • b j := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← sub_smul, sub_mul]
      rw [hsplit, ← h1, ← h2, ← hA, hx, sub_self]
    have hzero : ∀ k, (ν k - μ) * b.repr x k = 0 :=
      Fintype.linearIndependent_iff.1 b.linearIndependent _ hsum
    have hvanish : ∀ k, ν k ≠ μ → b.repr x k = 0 := by
      intro k hk
      rcases mul_eq_zero.1 (hzero k) with h | h
      · exact absurd (sub_eq_zero.1 h) hk
      · exact h
    have hres : x = ∑ j ∈ Finset.univ.filter (fun j => ν j = μ), b.repr x j • b j := by
      conv_lhs => rw [← hrepr]
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro j _ hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [hvanish j hj, zero_smul]
    rw [hres]
    refine Submodule.sum_mem _ fun j hj => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, hmem, hb, k.2]

/-- **SO THE MULTIPLICITY IS A COUNT OF FREQUENCIES.** The subfamily is independent because a
subfamily of a basis is (`LinearIndependent.comp` along `Subtype.val`), and
`finrank_span_eq_card` turns the span into the count. -/
theorem finrank_eigenspace_of_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (b : Module.Basis ι ℂ (ι → ℂ)) (ν : ι → ℂ)
    (hb : ∀ k, A *ᵥ b k = ν k • b k) (μ : ℂ) :
    Module.finrank ℂ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id))
      = Nat.card {k // ν k = μ} := by
  classical
  rw [eigenspace_eq_span_of_basis A b ν hb μ, Nat.card_eq_fintype_card]
  exact finrank_span_eq_card (b.linearIndependent.comp _ Subtype.val_injective)

/-! ## 2. Both operators on the periodic lattice -/

/-- **THE MULTIPLICITY OF `μ` FOR THE MASSIVE LAPLACIAN** is the number of frequencies at which
`ν` takes the value `μ`, in every dimension. -/
theorem finrank_eigenspace_massive (N : ℕ) (m : ℝ) (μ : ℂ) :
    Module.finrank ℂ (LinearMap.ker
        (Matrix.toLin' (MatrixLoewner.cx (massive (torusGraph d (N + 3)) m))
          - μ • LinearMap.id))
      = Nat.card {k : Site d (N + 3) // nu N m k = μ} := by
  classical
  have hn : (N + 3 : ℕ) ≠ 0 := by omega
  refine finrank_eigenspace_of_basis _ (chiDBasis (d := d) hn) (nu N m) (fun k => ?_) μ
  rw [chiDBasis_apply]
  exact cx_massive_mulVec_chiD N m k

/-- **AND FOR `Q = D + A`**, by the same basis. -/
theorem finrank_eigenspace_signless (N : ℕ) (μ : ℂ) :
    Module.finrank ℂ (LinearMap.ker
        (Matrix.toLin' (MatrixLoewner.cx (signlessLap (torusGraph d (N + 3))))
          - μ • LinearMap.id))
      = Nat.card {k : Site d (N + 3) // nuQ N k = μ} := by
  classical
  have hn : (N + 3 : ℕ) ≠ 0 := by omega
  refine finrank_eigenspace_of_basis _ (chiDBasis (d := d) hn) (nuQ N) (fun k => ?_) μ
  rw [chiDBasis_apply]
  exact cx_signlessLap_mulVec_chiD N k

/-! ## 3. The bottom is simple -/

/-- **`νR` REACHES `m²` ONLY AT THE ZERO FREQUENCY.** Each of the `d` cosines is at most `1` and
their doubled sum must reach `2d`, so every one is exactly `1`; and on `(−2π, 2π)` a cosine equal to
`1` forces its angle to vanish, which pins the coordinate at `0`. -/
theorem nuR_eq_sq_iff (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    nuR N m k = m ^ 2 ↔ k = 0 := by
  constructor
  · intro h
    have hpos : (0 : ℝ) < (N : ℝ) + 3 := by positivity
    have hsum : ∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3))
        = ∑ _i : Fin d, (2 : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [nuR] at h
      linarith
    have heach := (Finset.sum_eq_sum_iff_of_le (fun i _ => by
      have := Real.cos_le_one (2 * Real.pi * ((k i).val : ℝ) / ((N : ℝ) + 3))
      linarith)).1 hsum
    funext i
    have hcos : Real.cos (2 * Real.pi * ((k i).val : ℝ) / ((N : ℝ) + 3)) = 1 := by
      have := heach i (Finset.mem_univ i)
      linarith
    have hlt : ((k i).val : ℝ) < (N : ℝ) + 3 := by
      have h1 : ((k i).val : ℝ) < ((N + 3 : ℕ) : ℝ) := by exact_mod_cast (k i).isLt
      push_cast at h1
      linarith
    have hnn : (0 : ℝ) ≤ ((k i).val : ℝ) := Nat.cast_nonneg _
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hub : 2 * Real.pi * ((k i).val : ℝ) / ((N : ℝ) + 3) < 2 * Real.pi := by
      rw [div_lt_iff₀ hpos]
      nlinarith
    have hlb : -(2 * Real.pi) < 2 * Real.pi * ((k i).val : ℝ) / ((N : ℝ) + 3) := by
      have : (0 : ℝ) ≤ 2 * Real.pi * ((k i).val : ℝ) / ((N : ℝ) + 3) := by positivity
      linarith
    have hzero := (Real.cos_eq_one_iff_of_lt_of_lt hlb hub).1 hcos
    have hk0 : ((k i).val : ℝ) = 0 := by
      rcases div_eq_zero_iff.1 hzero with h' | h'
      · rcases mul_eq_zero.1 h' with h'' | h''
        · exact absurd h'' (by positivity)
        · exact h''
      · exact absurd h' (by positivity)
    have : (k i).val = 0 := by exact_mod_cast hk0
    exact Fin.ext this
  · rintro rfl
    exact nuR_at_zero N m

/-- **THE GROUND STATE IS UNIQUE.** The least eigenvalue `m²` of the massive Laplacian on the
`d`-dimensional periodic lattice has multiplicity **one**, in every dimension and at every side
length at least three — the constant character, and nothing else. -/
theorem ground_state_simple (N : ℕ) (m : ℝ) :
    Module.finrank ℂ (LinearMap.ker
        (Matrix.toLin' (MatrixLoewner.cx (massive (torusGraph d (N + 3)) m))
          - ((m ^ 2 : ℝ) : ℂ) • LinearMap.id)) = 1 := by
  classical
  rw [finrank_eigenspace_massive N m ((m ^ 2 : ℝ) : ℂ)]
  have hiff : ∀ k : Site d (N + 3), nu N m k = ((m ^ 2 : ℝ) : ℂ) ↔ k = 0 := by
    intro k
    rw [nu_eq_ofReal_nuR, Complex.ofReal_inj]
    exact nuR_eq_sq_iff N m k
  have huniq : ∀ x : {k : Site d (N + 3) // nu N m k = ((m ^ 2 : ℝ) : ℂ)},
      x = ⟨0, (hiff 0).2 rfl⟩ := fun x => Subtype.ext ((hiff x.1).1 x.2)
  haveI : Unique {k : Site d (N + 3) // nu N m k = ((m ^ 2 : ℝ) : ℂ)} :=
    ⟨⟨⟨0, (hiff 0).2 rfl⟩⟩, huniq⟩
  exact Nat.card_unique

end TorusMultiplicity
