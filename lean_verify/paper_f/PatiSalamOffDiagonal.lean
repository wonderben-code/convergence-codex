import LieAlgebraEmbedding
import TracelessSkewDimension

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

end PatiSalamOffDiagonal
