import LieAlgebraEmbedding
import TracelessSkewDimension
import SMEmbeddingHonest

/-!
# The nine broken generators, decomposed — six of them, as a subspace rather than a subtraction

`TracelessSkewDimension.finrank_prod_diff` records that `dim(su(4)⊕su(2)⊕su(2)) − dim(SM) = 9`,
and says of the physics reading — six leptoquarks plus three right-handed weak bosons — exactly
what it is:

> **That reading is not proved here**: this is `21 − 12`, and nothing in this file decomposes
> either space.

**Nothing anywhere decomposed either space.** The estate's two candidates are
`F4_1e.ps_to_sm_broken_generators`, which is `21 - 12 = 9 := by norm_num`, and
`LieAlgebraEmbedding.leptoquark_generators`, which is `15 - 12 = 3` by rewriting three dimension
lemmas. **Neither exhibits a subspace.** Checked before writing this file, on the rule
`ERRATUM 313` cost a unit to learn.

**⚠ THE SENTENCE IN BOLD ABOVE IS FALSE, AND IS KEPT SO THAT THE CORRECTION IS LEGIBLE
(`ERRATUM 94`, `ERRATUM 317`).** `SMEmbeddingHonest` decomposed `sl(4,ℂ)` on 2 August 2026 and this
file did not know it: `colour_bl_finrank` exhibits the image of colour ⊕ `B − L` as a genuine
**9**-dimensional subspace, and `leptoquark_coset` gives the complementary **6** as a quotient
dimension. What was checked before writing was the two declarations the fence itself *names*; the
prior work carries neither of those names and was not found by looking for them. **§5 below is the
fold-back, and it is a theorem rather than a retraction**: `ker_offDiagMap_eq_colour_bl` proves the
kernel described here by an entry condition **is** that image, and `leptoquarkCosetEquiv` upgrades
the earlier quotient *dimension* into a quotient *model* — the coset is the pair of off-diagonal
blocks. **What §§1–3 add that was not there** is the 6 as a subspace with an explicit section
rather than only as a quotient, and the block-diagonal description of the 9. **What §4 adds** has
no prior at all: `SMEmbeddingHonest` works over `ℂ`, and §4 is over `ℝ`.

**This file decomposes the `su(4)` factor.** `offDiagMap` sends a traceless `4 × 4` matrix to its
last column and last row, above and left of the corner:

```
⎡ A   b ⎤        M ↦ (b, c),   A : 3×3,  b, c : 3×1
⎣ c   d ⎦
```

It is linear and **surjective** — the matrix with those entries and nothing else is traceless,
because its whole diagonal is zero — so its range is all of `(Fin 3 → ℂ) × (Fin 3 → ℂ)`, of
dimension **6**. Rank–nullity against `CascadeFoundation.traceless_dim_4` then makes the kernel
**9**, and `mem_ker_offDiagMap_iff` says the kernel is exactly the block-diagonal traceless
matrices. So

> **`su4_splits_nine_six`** — `15 = 9 + 6`, with both summands exhibited, **derived from a map
> rather than asserted about numerals.**

## What this settles and what it does not

**Settled:** the `su(4)` factor of the Pati–Salam algebra splits as a 9-dimensional block-diagonal
part and a 6-dimensional off-diagonal part, and the 6 is a named subspace with a surjection onto
it. That is the half of `TracelessSkewDimension`'s reading that concerns `su(4)`.

**NOT settled, and both halves are named.** *(i)* **The interpretation is physics and is not
proved.** That these six directions are leptoquark gauge bosons mediating proton decay is a reading
of the decomposition, not a consequence of it; nothing here mentions a particle, a current or a
decay. *(ii)* **The other three of the nine are untouched.** They come from `su(2)_R ⊕ u(1)_{B−L}`
minus hypercharge, which is a different computation in a different factor, and this file says
nothing about it. **So `TracelessSkewDimension`'s fence is half closed, not closed**, and its
paragraph is annotated to say which half.

## 5, added the same night

**The nine was already a subspace, and §5 identifies it.** See the amended paragraph above: the
`ℂ` half of this file overlaps prior work it did not find, and the overlap is discharged by proving
the two descriptions equal rather than by softening either.

**No wall moves. No published tag moves**, and no claim here bears on the cascade's physical
content.
-/

namespace PatiSalamOffDiagonal

-- `LieAlgebraEmbedding` and `CascadeFoundation` declare at the root, so there is no
-- namespace to open; only `Matrix` is one.
open Matrix

/-! ## 1. The off-diagonal blocks, as a linear map -/

/-- The last column and the last row of a traceless `4 × 4` matrix, both read on the first three
indices. The corner entry `M 3 3` is deliberately not read: it is determined by the rest. -/
noncomputable def offDiagMap :
    TracelessMatrix 4 →ₗ[ℂ] ((Fin 3 → ℂ) × (Fin 3 → ℂ)) where
  toFun M := (fun i => (M : Matrix (Fin 4) (Fin 4) ℂ) (fin3_to_fin4 i) 3,
              fun j => (M : Matrix (Fin 4) (Fin 4) ℂ) 3 (fin3_to_fin4 j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem offDiagMap_fst (M : TracelessMatrix 4) (i : Fin 3) :
    (offDiagMap M).1 i = (M : Matrix (Fin 4) (Fin 4) ℂ) (fin3_to_fin4 i) 3 := rfl

@[simp] theorem offDiagMap_snd (M : TracelessMatrix 4) (j : Fin 3) :
    (offDiagMap M).2 j = (M : Matrix (Fin 4) (Fin 4) ℂ) 3 (fin3_to_fin4 j) := rfl

/-! ## 2. It is surjective, because a purely off-diagonal matrix is traceless -/

/-- The matrix carrying `b` down the last column and `c` along the last row, and nothing else. -/
def offDiagOf (b c : Fin 3 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j =>
    if _ : j = 3 then (if hi : i.val < 3 then b ⟨i.val, hi⟩ else 0)
    else if i = 3 then (if hjv : j.val < 3 then c ⟨j.val, hjv⟩ else 0)
    else 0

/-- **ITS DIAGONAL IS ZERO**, which is the whole reason the map below is surjective: the
off-diagonal directions cost nothing against the trace condition. -/
theorem offDiagOf_diag (b c : Fin 3 → ℂ) (i : Fin 4) : offDiagOf b c i i = 0 := by
  simp only [offDiagOf, Matrix.of_apply]
  by_cases hi : i = 3
  · subst hi; norm_num
  · rw [dif_neg hi, if_neg hi]

theorem offDiagOf_mem (b c : Fin 3 → ℂ) : offDiagOf b c ∈ TracelessMatrix 4 := by
  refine LinearMap.mem_ker.mpr ?_
  simp only [traceMap, Matrix.traceLinearMap_apply, Matrix.trace, Matrix.diag]
  exact Finset.sum_eq_zero fun i _ => offDiagOf_diag b c i

theorem offDiagMap_surjective : Function.Surjective offDiagMap := by
  rintro ⟨b, c⟩
  refine ⟨⟨offDiagOf b c, offDiagOf_mem b c⟩, ?_⟩
  have h1 : ∀ i : Fin 3, offDiagOf b c (fin3_to_fin4 i) 3 = b i := by
    intro i
    simp [offDiagOf, fin3_to_fin4, i.isLt]
  have h2 : ∀ j : Fin 3, offDiagOf b c 3 (fin3_to_fin4 j) = c j := by
    intro j
    have hj : (fin3_to_fin4 j : Fin 4) ≠ 3 := by
      intro hc
      have := congrArg Fin.val hc
      simp only [fin3_to_fin4] at this
      omega
    -- `dif_neg` first: unfolding `fin3_to_fin4` before it rewrites `hj` out of shape
    simp only [offDiagOf, Matrix.of_apply]
    rw [dif_neg hj]
    simp [fin3_to_fin4, j.isLt]
  exact Prod.ext (funext h1) (funext h2)

/-! ## 3. Six and nine, from rank–nullity -/

/-- **THE SIX.** The off-diagonal directions form a space of dimension `6` — two copies of
`Fin 3 → ℂ`, one for the last column and one for the last row. -/
theorem finrank_range_offDiagMap :
    Module.finrank ℂ (LinearMap.range offDiagMap) = 6 := by
  rw [LinearMap.range_eq_top.mpr offDiagMap_surjective]
  rw [finrank_top]
  simp [Module.finrank_prod]

/-- **AND THE NINE.** Rank–nullity against `CascadeFoundation.traceless_dim_4`. -/
theorem finrank_ker_offDiagMap :
    Module.finrank ℂ (LinearMap.ker offDiagMap) = 9 := by
  have h := LinearMap.finrank_range_add_finrank_ker offDiagMap
  rw [finrank_range_offDiagMap, traceless_dim_4] at h
  omega

/-- **THE KERNEL IS THE BLOCK-DIAGONAL PART**, said as a condition on entries so that the
decomposition is legible rather than merely counted. -/
theorem mem_ker_offDiagMap_iff (M : TracelessMatrix 4) :
    M ∈ LinearMap.ker offDiagMap ↔
      (∀ i : Fin 3, (M : Matrix (Fin 4) (Fin 4) ℂ) (fin3_to_fin4 i) 3 = 0)
        ∧ ∀ j : Fin 3, (M : Matrix (Fin 4) (Fin 4) ℂ) 3 (fin3_to_fin4 j) = 0 := by
  constructor
  · intro h
    have h' : offDiagMap M = 0 := LinearMap.mem_ker.mp h
    exact ⟨fun i => congrFun (congrArg Prod.fst h') i,
           fun j => congrFun (congrArg Prod.snd h') j⟩
  · rintro ⟨h1, h2⟩
    exact LinearMap.mem_ker.mpr (Prod.ext (funext h1) (funext h2))

/-- **`15 = 9 + 6`, WITH BOTH SUMMANDS EXHIBITED.** `F4_1e.ps_to_sm_broken_generators` is
`21 - 12 = 9` on numerals and `LieAlgebraEmbedding.leptoquark_generators` is `15 - 12 = 3` by three
dimension rewrites; **neither names a subspace.** This is the same arithmetic derived from a map
whose kernel and range are both described.

**It is the `su(4)` half of `TracelessSkewDimension`'s reading and not the whole of it**: the other
three broken generators live in `su(2)_R ⊕ u(1)_{B−L}` and are untouched here. And the *reading* —
that these six are leptoquark gauge bosons — is physics, not a consequence of this theorem. -/
theorem su4_splits_nine_six :
    Module.finrank ℂ (TracelessMatrix 4)
      = Module.finrank ℂ (LinearMap.ker offDiagMap)
        + Module.finrank ℂ (LinearMap.range offDiagMap) := by
  rw [finrank_ker_offDiagMap, finrank_range_offDiagMap, traceless_dim_4]


/-! ## 4. The same decomposition in `su(4)`, which is the object the fence is actually about

**§§1–3 decompose `sl(4,ℂ)` and `TracelessSkewDimension` counts `su(4)`, and those are different
spaces.** `CascadeFoundation.TracelessMatrix 4` is the traceless COMPLEX matrices, a `ℂ`-submodule
of `finrank ℂ = 15`; `TracelessSkewDimension.traceless 4` is the traceless SKEW-HERMITIAN matrices,
an `ℝ`-submodule of `finrank ℝ = 15`. The dimensions coincide and the objects do not — one is a
real form of the other — and a first version of this file annotated the fence as though §§1–3
settled it. **They do not. This section does** (`ERRATUM 316`).

**And the real count is the interesting one.** A skew-Hermitian matrix's last ROW is determined by
its last column, `M 3 i = −conj (M i 3)`, so the off-diagonal part is three COMPLEX entries — six
real dimensions — rather than six independent ones. **That is where the six comes from in the
physics, and §§1–3 got it by a different route that happens to give the same number.**
-/

open TracelessSkewDimension in
/-- The last column of a traceless skew-Hermitian `4 × 4` matrix, on the first three indices. The
last row is not read because skew-Hermiticity determines it. -/
noncomputable def offDiagMapR : traceless 4 →ₗ[ℝ] (Fin 3 → ℂ) where
  toFun M := fun i =>
    ((M : skewAdjoint (Matrix (Fin 4) (Fin 4) ℂ)) : Matrix (Fin 4) (Fin 4) ℂ) (fin3_to_fin4 i) 3
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `b` down the last column, `−conj b` along the last row, nothing else. -/
noncomputable def skewOffDiagOf (b : Fin 3 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j =>
    if _ : j = 3 then (if hi : i.val < 3 then b ⟨i.val, hi⟩ else 0)
    else if i = 3 then (if hj : j.val < 3 then -(starRingEnd ℂ) (b ⟨j.val, hj⟩) else 0)
    else 0

theorem skewOffDiagOf_skew (b : Fin 3 → ℂ) :
    skewOffDiagOf b ∈ skewAdjoint (Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [skewAdjoint.mem_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewOffDiagOf]

theorem skewOffDiagOf_diag (b : Fin 3 → ℂ) (i : Fin 4) : skewOffDiagOf b i i = 0 := by
  simp only [skewOffDiagOf, Matrix.of_apply]
  by_cases hi : i = 3
  · subst hi; norm_num
  · rw [dif_neg hi, if_neg hi]

open TracelessSkewDimension in
theorem skewOffDiagOf_mem (b : Fin 3 → ℂ) :
    (⟨skewOffDiagOf b, skewOffDiagOf_skew b⟩ : skewAdjoint (Matrix (Fin 4) (Fin 4) ℂ))
      ∈ traceless 4 :=
  -- membership IS `(trace _).im = 0` definitionally, so the term is supplied rather than the
  -- goal restated: the style linter reserves `show` for readability
  have h : (Matrix.trace (skewOffDiagOf b)).im = 0 := by
    rw [Matrix.trace]
    simp only [Matrix.diag, Complex.im_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [skewOffDiagOf_diag b i]; simp
  h

theorem offDiagMapR_surjective : Function.Surjective offDiagMapR := by
  intro b
  refine ⟨⟨⟨skewOffDiagOf b, skewOffDiagOf_skew b⟩, skewOffDiagOf_mem b⟩, ?_⟩
  funext i
  exact (by simp [skewOffDiagOf, fin3_to_fin4, i.isLt] :
    skewOffDiagOf b (fin3_to_fin4 i) 3 = b i)

/-- **THE SIX, AS A REAL DIMENSION.** Three complex entries, two real dimensions each. -/
theorem finrank_range_offDiagMapR :
    Module.finrank ℝ (LinearMap.range offDiagMapR) = 6 := by
  rw [LinearMap.range_eq_top.mpr offDiagMapR_surjective, finrank_top,
    Module.finrank_pi_fintype ℝ]
  simp [Complex.finrank_real_complex]

open TracelessSkewDimension in
/-- **AND THE NINE**, by rank–nullity against `TracelessSkewDimension.finrank_traceless_four`. -/
theorem finrank_ker_offDiagMapR :
    Module.finrank ℝ (LinearMap.ker offDiagMapR) = 9 := by
  have h := LinearMap.finrank_range_add_finrank_ker offDiagMapR
  rw [finrank_range_offDiagMapR, finrank_traceless_four] at h
  omega

open TracelessSkewDimension in
/-- **`15 = 9 + 6` IN `su(4)` ITSELF**, the space
`TracelessSkewDimension.finrank_prod_diff` counts. This is the statement that bears on that
file's fence; §3's is the same shape in `sl(4,ℂ)` and does not. -/
theorem su4_real_splits_nine_six :
    Module.finrank ℝ (traceless 4)
      = Module.finrank ℝ (LinearMap.ker offDiagMapR)
        + Module.finrank ℝ (LinearMap.range offDiagMapR) := by
  rw [finrank_ker_offDiagMapR, finrank_range_offDiagMapR, finrank_traceless_four]

/-! ## 5. The nine was already a subspace, and this identifies it (`ERRATUM 317`) -/

/-- The top-left `3 × 3` block of a `4 × 4` matrix. -/
def topBlock (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  M.submatrix fin3_to_fin4 fin3_to_fin4

/-- **THE TRACE SPLITS OFF THE CORNER.** -/
theorem trace_topBlock (M : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix.trace (topBlock M) + M 3 3 = Matrix.trace M := by
  have e0 : fin3_to_fin4 0 = 0 := rfl
  have e1 : fin3_to_fin4 1 = 1 := rfl
  have e2 : fin3_to_fin4 2 = 2 := rfl
  simp only [topBlock, Matrix.trace, Matrix.diag, Matrix.submatrix_apply, Fin.sum_univ_three,
    Fin.sum_univ_four, e0, e1, e2]

/-- The colour summand's underlying matrix, unfolded once so that no later proof has to. -/
theorem su3EmbedRestricted_val (A : TracelessMatrix 3) :
    ((su3EmbedRestricted A : TracelessMatrix 4) : Matrix (Fin 4) (Fin 4) ℂ)
      = su3EmbedFn (A : Matrix (Fin 3) (Fin 3) ℂ) := rfl

/-- The `B − L` summand's underlying matrix, likewise. -/
theorem u1EmbedRestricted_val (c : ℂ) :
    ((u1EmbedRestricted c : TracelessMatrix 4) : Matrix (Fin 4) (Fin 4) ℂ) = u1EmbedFn c := rfl

/-- The value of the assembled map, unfolded once so that no later proof has to. -/
theorem coprod_val (A : TracelessMatrix 3) (c : ℂ) :
    ((su3EmbedRestricted.coprod u1EmbedRestricted) (A, c) : Matrix (Fin 4) (Fin 4) ℂ)
      = su3EmbedFn (A : Matrix (Fin 3) (Fin 3) ℂ) + u1EmbedFn c := rfl

/-- **THE COLOUR ⊕ `B − L` IMAGE LANDS IN THE KERNEL.** Neither summand has an entry in the last
column or the last row off the corner: the `su(3)` block is confined to indices `< 3`, and the
`B − L` matrix is diagonal. -/
theorem colour_bl_le_ker_offDiagMap :
    LinearMap.range (su3EmbedRestricted.coprod u1EmbedRestricted) ≤ LinearMap.ker offDiagMap := by
  rintro _ ⟨⟨A, c⟩, rfl⟩
  refine (mem_ker_offDiagMap_iff _).mpr ⟨fun i => ?_, fun j => ?_⟩
  · have hi : ¬ ((i : ℕ) = 3) := by omega
    simp [su3EmbedRestricted_val, u1EmbedRestricted_val, su3EmbedFn, u1EmbedFn, fin3_to_fin4,
      Fin.ext_iff, hi]
  · have hj : ¬ ((3 : ℕ) = (j : ℕ)) := by omega
    simp [su3EmbedRestricted_val, u1EmbedRestricted_val, su3EmbedFn, u1EmbedFn, fin3_to_fin4,
      Fin.ext_iff, hj]

/-- **AND THE KERNEL LANDS IN IT**, which is the direction with content. Given a traceless `M`
whose last column and last row vanish off the corner, put `c := -(M 3 3)/3` — forced, because
`u1EmbedFn c` is the only summand with a corner entry — and `A := topBlock M - c • 1`. That `A` is
traceless is not an extra hypothesis: `tr (topBlock M) = -(M 3 3) = 3c` by `trace_topBlock` and
`M`'s own tracelessness, and `tr (c • 1) = 3c` too. **The trace condition on the `4 × 4` matrix is
exactly what makes the `3 × 3` correction traceless**, which is the same accounting that made
`offDiagMap` surjective, read in the other direction. -/
theorem ker_offDiagMap_le_colour_bl :
    LinearMap.ker offDiagMap ≤ LinearMap.range (su3EmbedRestricted.coprod u1EmbedRestricted) := by
  intro M hM
  obtain ⟨h1, h2⟩ := (mem_ker_offDiagMap_iff M).mp hM
  have htr : Matrix.trace (M : Matrix (Fin 4) (Fin 4) ℂ) = 0 := by
    have hA := M.property
    simp only [TracelessMatrix, LinearMap.mem_ker, traceMap, Matrix.traceLinearMap_apply] at hA
    exact hA
  set N : Matrix (Fin 4) (Fin 4) ℂ := (M : Matrix (Fin 4) (Fin 4) ℂ) with hN
  set c : ℂ := -(N 3 3) / 3 with hc
  have hblock : Matrix.trace (topBlock N) = 3 * c := by
    have h := trace_topBlock N
    rw [htr] at h
    rw [hc]
    linear_combination h
  have hAmem : topBlock N - c • (1 : Matrix (Fin 3) (Fin 3) ℂ) ∈ TracelessMatrix 3 := by
    refine LinearMap.mem_ker.mpr ?_
    simp only [traceMap, Matrix.traceLinearMap_apply, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_one, Fintype.card_fin, hblock, smul_eq_mul]
    push_cast
    ring
  refine ⟨(⟨topBlock N - c • (1 : Matrix (Fin 3) (Fin 3) ℂ), hAmem⟩, c), ?_⟩
  apply Subtype.ext
  rw [coprod_val, ← hN]
  have a0 : N 0 3 = 0 := h1 0
  have a1 : N 1 3 = 0 := h1 1
  have a2 : N 2 3 = 0 := h1 2
  have b0 : N 3 0 = 0 := h2 0
  have b1 : N 3 1 = 0 := h2 1
  have b2 : N 3 2 = 0 := h2 2
  have hcorner : -(3 * c) = N 3 3 := by rw [hc]; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su3EmbedFn, u1EmbedFn, topBlock, fin3_to_fin4, a0, a1, a2, b0, b1, b2, hcorner]

/-- **THE TWO NINES ARE THE SAME NINE.** `SMEmbeddingHonest.colour_bl_finrank` (2 August 2026)
already exhibited a genuine `9`-dimensional subspace of `sl(4,ℂ)` — the image of colour ⊕ `B − L` —
and `SMEmbeddingHonest.leptoquark_coset` already gave the complementary `6` as a quotient
dimension. **§§1–3 above did not know that**, and said so in prose that was wrong; `ERRATUM 317`
records it. This theorem is the fold-back: the kernel characterised here by an entry condition
**is** that image, so the two descriptions are of one subspace and not of two that happen to agree
on a numeral. -/
theorem ker_offDiagMap_eq_colour_bl :
    LinearMap.ker offDiagMap = LinearMap.range (su3EmbedRestricted.coprod u1EmbedRestricted) :=
  le_antisymm ker_offDiagMap_le_colour_bl colour_bl_le_ker_offDiagMap

/-- **AND THE COSET IS THE PAIR OF OFF-DIAGONAL BLOCKS**, explicitly.
`SMEmbeddingHonest.leptoquark_coset` says the quotient `sl(4,ℂ) / (colour ⊕ B − L)` has dimension
`6`; this says *what* that quotient is — `offDiagMap` descends to it and the descent is an
isomorphism onto `(Fin 3 → ℂ) × (Fin 3 → ℂ)`. **A dimension becomes a model**, which is the one
thing a dimension count cannot give you.

**Only over `ℂ`.** The estate has no real colour ⊕ `B − L` embedding, so §4's real decomposition has
no counterpart here and none is claimed. -/
noncomputable def leptoquarkCosetEquiv :
    (TracelessMatrix 4 ⧸ LinearMap.range (su3EmbedRestricted.coprod u1EmbedRestricted))
      ≃ₗ[ℂ] ((Fin 3 → ℂ) × (Fin 3 → ℂ)) :=
  (Submodule.quotEquivOfEq _ _ ker_offDiagMap_eq_colour_bl.symm).trans
    (offDiagMap.quotKerEquivOfSurjective offDiagMap_surjective)

end PatiSalamOffDiagonal
