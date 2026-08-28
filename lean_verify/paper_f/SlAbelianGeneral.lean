import SlFourAbelian

/-!
# The `4 > 3` of `SlFourAbelian` is `pq > p + q − 1`, and the margin is unbounded

`SlFourAbelian` checked the clause `SMEmbeddingHonest` uses to dismiss the rank argument — *"rank
alone is NOT an obstruction inside `sl₄(ℂ)`, which contains 4-dimensional abelian subalgebras (an
off-diagonal `2 × 2` block)"* — and found it true: an abelian subalgebra of dimension `4` against a
Cartan of dimension `3`.

**`PROOF_STRATEGY` §7 rule 3 says to take a result proved under restrictive hypotheses and remove
one. The restriction here is the dimension**, and it comes off completely.

## What is proved

Working over `Fin p ⊕ Fin q` rather than `Fin 4`, so the block structure is `Matrix.fromBlocks`
rather than index arithmetic:

> **`finrank_nilBlockRange = p * q`** — the strictly-upper `p × q` block `[[0, B], [0, 0]]` is a
> `pq`-dimensional subspace of `sl_{p+q}(ℂ)`, and **every product of two of its elements is zero**
> (`nilBlock_mul`), so it is abelian and `nilBlockRange_bracket_mem` closes it under the commutator.
>
> **`finrank_cartanRange = p + q - 1`** — the diagonal traceless matrices, the Cartan, by
> rank–nullity on the sum functional.
>
> **`abelian_exceeds_cartan_general`** — for `p, q ≥ 2`, `p + q - 1 < p * q`. **So in `sl_n(ℂ)` for
> every `n ≥ 4` there is an abelian subalgebra strictly larger than a Cartan**, and at `p = q = n/2`
> the ratio grows without bound: `n²/4` against `n − 1`.

`SlFourAbelian`'s `4 > 3` is `p = q = 2`, and `abelian_exceeds_cartan_four` records that rather than
reproving it (`ERRATUM 313`).

## What this does NOT prove

**It still does not say the embedding exists**, and it still removes only a *proposed* obstruction.
`SMEmbeddingHonest`'s refutation of its own maps is untouched, `ColourCommutant` closed one clause
of the other argument, and the nonexistence theorem is open.

**It still says nothing about the compact form.** That `su(n)` has no abelian subspace above
dimension `n − 1` is the true statement that makes the rank argument work where it works; it needs
maximal-torus theory, **is not proved here and is not begun here**, and `TracelessSkewDimension` is
not imported. **Only one side of the contrast is a theorem — and now the asymmetry is quantified:
the complex side fails by `(p−1)(q−1)`, which is as large as you like.**

**"Subalgebra" is the weak sense this estate has**: a subspace closed under `X, Y ↦ XY − YX`. No
`LieSubalgebra` instance is built and no Lie theory is invoked.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SlAbelianGeneral

open Matrix

/-! ## 1. Traceless matrices over an arbitrary finite index type -/

/-- The traceless matrices, indexed by any finite type. `CascadeFoundation.TracelessMatrix n` is
this at `ι = Fin n`, definitionally — `tracelessSub_fin` records that rather than restating it. -/
noncomputable def tracelessSub (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Submodule ℂ (Matrix ι ι ℂ) :=
  LinearMap.ker (Matrix.traceLinearMap ι ℂ ℂ)

theorem tracelessSub_fin (n : ℕ) : tracelessSub (Fin n) = TracelessMatrix n := rfl

variable {p q : ℕ}

/-! ## 2. The strictly-upper block -/

/-- `B ↦ [[0, B], [0, 0]]`. -/
def nilBlock (B : Matrix (Fin p) (Fin q) ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.fromBlocks 0 B 0 0

/-- **EVERY PRODUCT IS ZERO**, which is why the subspace is abelian: the right factor's nonzero
block starts where the left factor's ends. -/
theorem nilBlock_mul (B B' : Matrix (Fin p) (Fin q) ℂ) : nilBlock B * nilBlock B' = 0 := by
  simp [nilBlock, Matrix.fromBlocks_multiply]

theorem nilBlock_trace (B : Matrix (Fin p) (Fin q) ℂ) : Matrix.trace (nilBlock B) = 0 := by
  simp [nilBlock, Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

theorem nilBlock_mem (B : Matrix (Fin p) (Fin q) ℂ) :
    nilBlock B ∈ tracelessSub (Fin p ⊕ Fin q) :=
  LinearMap.mem_ker.mpr (nilBlock_trace B)

noncomputable def nilBlockMap :
    Matrix (Fin p) (Fin q) ℂ →ₗ[ℂ] tracelessSub (Fin p ⊕ Fin q) where
  toFun B := ⟨nilBlock B, nilBlock_mem B⟩
  map_add' B B' := by
    apply Subtype.ext
    simp [nilBlock, Matrix.fromBlocks_add]
  map_smul' c B := by
    apply Subtype.ext
    simp [nilBlock, Matrix.fromBlocks_smul]

theorem nilBlockMap_injective : Function.Injective (nilBlockMap (p := p) (q := q)) := by
  intro B B' h
  have hval : nilBlock B = nilBlock B' := congrArg Subtype.val h
  ext i j
  have := congrFun (congrFun hval (Sum.inl i)) (Sum.inr j)
  simpa [nilBlock] using this

noncomputable def nilBlockRange : Submodule ℂ (tracelessSub (Fin p ⊕ Fin q)) :=
  LinearMap.range (nilBlockMap (p := p) (q := q))

theorem finrank_nilBlockRange :
    Module.finrank ℂ (nilBlockRange (p := p) (q := q)) = p * q := by
  rw [nilBlockRange, LinearMap.finrank_range_of_inj nilBlockMap_injective, Module.finrank_matrix]
  simp

/-- **AND IT IS A SUBALGEBRA**, in the weak sense: closed under the commutator, because every
product of two of its elements is zero. -/
theorem nilBlockRange_bracket_mem {X Y : tracelessSub (Fin p ⊕ Fin q)}
    (hX : X ∈ nilBlockRange) (hY : Y ∈ nilBlockRange) :
    (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * (Y : Matrix _ _ ℂ)
      - (Y : Matrix _ _ ℂ) * (X : Matrix _ _ ℂ) = 0 := by
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨B', rfl⟩ := hY
  have h1 : ((nilBlockMap B : tracelessSub (Fin p ⊕ Fin q)) : Matrix _ _ ℂ) = nilBlock B := rfl
  have h2 : ((nilBlockMap B' : tracelessSub (Fin p ⊕ Fin q)) : Matrix _ _ ℂ) = nilBlock B' := rfl
  rw [h1, h2, nilBlock_mul, nilBlock_mul, sub_zero]

/-! ## 3. The Cartan, at any index type -/

/-- The sum of a vector's entries, as a functional. -/
noncomputable def sumFun (ι : Type*) [Fintype ι] : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun v := ∑ i, v i
  map_add' u v := by simp [Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum]

theorem sumFun_surjective (ι : Type*) [Fintype ι] [Nonempty ι] :
    Function.Surjective (sumFun ι) := by
  classical
  intro c
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨Pi.single i₀ c, ?_⟩
  simp [sumFun]

/-- **THE CARTAN**: the diagonal traceless matrices, as the image of the vectors summing to zero. -/
noncomputable def cartanMap (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (LinearMap.ker (sumFun ι)) →ₗ[ℂ] tracelessSub ι where
  toFun v := ⟨Matrix.diagonal (v : ι → ℂ), by
    refine LinearMap.mem_ker.mpr ?_
    have hv : ∑ i, (v : ι → ℂ) i = 0 := LinearMap.mem_ker.mp v.property
    simpa [Matrix.traceLinearMap, Matrix.trace, Matrix.diag] using hv⟩
  map_add' u v := by apply Subtype.ext; simp [Matrix.diagonal_add]
  map_smul' c v := by apply Subtype.ext; simp [Matrix.diagonal_smul]

theorem cartanMap_injective (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Function.Injective (cartanMap ι) := by
  intro u v h
  have hval : Matrix.diagonal (u : ι → ℂ) = Matrix.diagonal (v : ι → ℂ) := congrArg Subtype.val h
  exact Subtype.ext (Matrix.diagonal_injective hval)

noncomputable def cartanRange (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Submodule ℂ (tracelessSub ι) :=
  LinearMap.range (cartanMap ι)

theorem finrank_ker_sumFun (ι : Type*) [Fintype ι] [Nonempty ι] :
    Module.finrank ℂ (LinearMap.ker (sumFun ι)) = Fintype.card ι - 1 := by
  classical
  have h := LinearMap.finrank_range_add_finrank_ker (sumFun ι)
  rw [LinearMap.range_eq_top.mpr (sumFun_surjective ι), finrank_top,
    Module.finrank_pi_fintype ℂ] at h
  simp only [Module.finrank_self, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  omega

/-- **`card ι − 1` DIMENSIONS**, which is the rank of `sl(ι)`. -/
theorem finrank_cartanRange (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Module.finrank ℂ (cartanRange ι) = Fintype.card ι - 1 := by
  rw [cartanRange, LinearMap.finrank_range_of_inj (cartanMap_injective ι), finrank_ker_sumFun]

/-! ## 4. Rank is not the obstruction, and the margin is `(p−1)(q−1)` -/

/-- **AN ABELIAN SUBALGEBRA STRICTLY LARGER THAN A CARTAN, AT EVERY `p, q ≥ 2`.**
`p + q - 1 < p * q`, so in `sl_n(ℂ)` for every `n = p + q ≥ 4` the inequality *"abelian dimension ≤
rank"* is **false** — and at `p = q` the two sides are `n²/4` against `n − 1`, so the failure is not
marginal.

**This says nothing about the compact form**, where the inequality does hold; that needs
maximal-torus theory and is not begun here. -/
theorem abelian_exceeds_cartan_general (hp : 2 ≤ p) (hq : 2 ≤ q) :
    Module.finrank ℂ (cartanRange (Fin p ⊕ Fin q))
      < Module.finrank ℂ (nilBlockRange (p := p) (q := q)) := by
  have hne : Nonempty (Fin p ⊕ Fin q) := ⟨Sum.inl ⟨0, by omega⟩⟩
  rw [finrank_cartanRange, finrank_nilBlockRange]
  have hcard : Fintype.card (Fin p ⊕ Fin q) = p + q := by simp
  rw [hcard]
  have := Nat.add_le_mul hp hq
  omega

/-- `SlFourAbelian`'s `4 > 3` is this at `p = q = 2`. Recorded rather than reproved
(`ERRATUM 313`); the two files build the same subspace over different index types and neither is a
duplicate of the other, the general one being about `sl_{p+q}` and the earlier about `sl₄`. -/
theorem abelian_exceeds_cartan_four :
    Module.finrank ℂ (cartanRange (Fin 2 ⊕ Fin 2))
      < Module.finrank ℂ (nilBlockRange (p := 2) (q := 2)) :=
  abelian_exceeds_cartan_general le_rfl le_rfl

end SlAbelianGeneral
