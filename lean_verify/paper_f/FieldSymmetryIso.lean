import FieldLinearClassified

/-!
# The symmetry group, named: isomorphic to the orthogonal group of `ℝ^V`

`FieldLinearClassified` classified the linear symmetries as a **bijection of sets**, and its own
fence said what was missing twice over: *`conjSq_bijOn` is a bijection of sets; that it carries
matrix multiplication to matrix multiplication is true and **not proved**, so the word `group` is
not used of the bijection* — and *the classification is of **matrices**; that every continuous
linear map is one is standard and **not invoked**.* **Both are done here**, and the
`UNLOCK_WATCHLIST` item that carried them was right that each is one line, and right that the
bundling around them was the part nobody had looked at.

## What is proved

**`star_eq_transpose`, `mem_unitary_iff`** — over `ℝ` the star is the transpose, so membership of
`Matrix.unitaryGroup V ℝ` is `Aᵀ * A = 1`. **The orthogonal group is used as Mathlib's unitary
group with that characterisation proved**, rather than through `Matrix.orthogonalGroup`, which is
an `abbrev` for the same object under `attribute [local instance] starRingOfComm` — Mathlib's own
`TODO` beside it asks whether its lemmas work without that instance, so this file does not take it.

**`linSym`** — the matrices with `L C Lᵀ = C`, as a `Submonoid`: `1` is one, and a product is one
because `(ab) C (ab)ᵀ = a (b C bᵀ) aᵀ`.

**`conjSq_mul`, `invConj_conjSq`** — conjugation is multiplicative, and the inverse conjugation
undoes it.

**`conjSqEquiv`** — **a `MulEquiv` from `Matrix.unitaryGroup V ℝ` to `linSym G m`.** The linear
symmetry group of the Gaussian field **is** the orthogonal group of `ℝ^V`, conjugated by the
propagator's square root.

**`gaussianField_map_of_mem_linSym`, `mem_linSym_of_gaussianField_map`,
`mem_linSym_iff_gaussianField_map`** — a matrix lies in `linSym` **iff** its map preserves the
measure, **so the group named above is the symmetry group** and not merely a group of matrices that
happens to carry an isomorphism. Both inclusions are stated: without the second, `linSym` would only
be **contained** in the symmetries, which is the defect `ERRATUM 456` records and `ERRATUM 461`
records this file committing in its first draft, two hours after 456 wrote the check against it.

**`exists_matrix`, `gaussianField_map_iff_exists_orthogonal`** — **and the statement is about maps,
not only matrices**: a continuous linear map preserves the Gaussian field **iff** it is induced by a
conjugated orthogonal matrix. `Matrix.toEuclideanLin` is a `LinearEquiv`, which is what supplies the
matrix.

## What is NOT here

**`linSym` IS BUNDLED AS A `Submonoid`, NOT AS A `Subgroup`.** The `MulEquiv` above is with
`Matrix.unitaryGroup V ℝ`, which **is** a group, so `linSym` is a group in substance; **no
`Subgroup` instance is constructed** and none is claimed. Not attempted, no cost claimed
(`ERRATUM 246`).

**NO CARDINALITY.** The isomorphism moves every counting question onto `Matrix.unitaryGroup V ℝ`,
which is Mathlib's object. **Nothing here counts anything**, and in particular `FieldLineCount`'s
`2^(k+1)` remains a count of the **isometric** symmetries only.

**NOTHING ABOUT NON-LINEAR MAPS.** The full automorphism group of the measure is still untouched.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. A symmetry
group named exactly, in finite volume, is a shadow named exactly.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `m ≠ 0` is taken by `conjSq_mul`,
`invConj_conjSq`, `conjSqEquiv`, `conjSqEquiv_apply`, `gaussianField_map_of_mem_linSym`,
`mem_linSym_of_gaussianField_map`, `mem_linSym_iff_gaussianField_map` and
`gaussianField_map_iff_exists_orthogonal` — **eight of the thirteen**. It is **not** taken by
`star_eq_transpose`, `mem_unitary_iff`, `linSym`, `mem_linSym` or `exists_matrix`. **Three** of
the thirteen `omit` the graph's `DecidableRel` instance because they mention no graph —
`star_eq_transpose`, `mem_unitary_iff` and `exists_matrix` — and `star_eq_transpose` omits
`Fintype V` and `DecidableEq V` as well.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldSymmetryIso

open Matrix GraphLaplacian FieldSqrtConjugation FieldLinearClassified

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Over `ℝ` the unitary group is the orthogonal group -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem star_eq_transpose (A : Matrix V V ℝ) : star A = Aᵀ := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

omit [DecidableRel G.Adj] in
theorem mem_unitary_iff {A : Matrix V V ℝ} :
    A ∈ Matrix.unitaryGroup V ℝ ↔ Aᵀ * A = 1 := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_transpose]

/-! ## 2. The linear symmetries as a submonoid -/

/-- The matrices preserving the propagator's form, as a `Submonoid`. -/
def linSym (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) : Submonoid (Matrix V V ℝ) where
  carrier := {L : Matrix V V ℝ | L * green G m * Lᵀ = green G m}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    calc a * b * green G m * (a * b)ᵀ
        = a * (b * green G m * bᵀ) * aᵀ := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = green G m := by rw [hb]; exact ha

@[simp] theorem mem_linSym {L : Matrix V V ℝ} :
    L ∈ linSym G m ↔ L * green G m * Lᵀ = green G m := Iff.rfl

/-! ## 3. Conjugation is multiplicative -/

theorem conjSq_mul (hm : m ≠ 0) (O₁ O₂ : Matrix V V ℝ) :
    conjSq G m O₁ * conjSq G m O₂ = conjSq G m (O₁ * O₂) := by
  rw [conjSq, conjSq, conjSq]
  calc sqGreen G m * O₁ * (sqGreen G m)⁻¹ * (sqGreen G m * O₂ * (sqGreen G m)⁻¹)
      = sqGreen G m * O₁ * ((sqGreen G m)⁻¹ * sqGreen G m) * O₂ * (sqGreen G m)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = sqGreen G m * (O₁ * O₂) * (sqGreen G m)⁻¹ := by
        rw [inv_mul_sqGreen hm]
        simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem invConj_conjSq (hm : m ≠ 0) (O : Matrix V V ℝ) : invConj G m (conjSq G m O) = O := by
  rw [invConj, conjSq]
  calc (sqGreen G m)⁻¹ * (sqGreen G m * O * (sqGreen G m)⁻¹) * sqGreen G m
      = ((sqGreen G m)⁻¹ * sqGreen G m) * O * ((sqGreen G m)⁻¹ * sqGreen G m) := by
        simp only [Matrix.mul_assoc]
    _ = O := by rw [inv_mul_sqGreen hm, Matrix.one_mul, Matrix.mul_one]

/-! ## 4. The isomorphism -/

/-- **THE LINEAR SYMMETRY GROUP OF THE GAUSSIAN FIELD IS ISOMORPHIC TO THE ORTHOGONAL GROUP OF
`ℝ^V`**, by conjugation with the propagator's square root. -/
noncomputable def conjSqEquiv (hm : m ≠ 0) : Matrix.unitaryGroup V ℝ ≃* linSym G m where
  toFun O := ⟨conjSq G m O.1, conjSq_mul_green_mul_transpose hm (mem_unitary_iff.mp O.2)⟩
  invFun L := ⟨invConj G m L.1, mem_unitary_iff.mpr (invConj_orthogonal hm L.2)⟩
  left_inv O := Subtype.ext (invConj_conjSq hm O.1)
  right_inv L := Subtype.ext (conjSq_invConj hm L.1)
  map_mul' O₁ O₂ := Subtype.ext (conjSq_mul hm O₁.1 O₂.1).symm

@[simp] theorem conjSqEquiv_apply (hm : m ≠ 0) (O : Matrix.unitaryGroup V ℝ) :
    ((conjSqEquiv (G := G) hm) O : Matrix V V ℝ) = conjSq G m O.1 := rfl

/-- **AND EVERY MEMBER IS A SYMMETRY OF THE MEASURE.** -/
theorem gaussianField_map_of_mem_linSym (hm : m ≠ 0) {L : Matrix V V ℝ} (hL : L ∈ linSym G m) :
    MeasureTheory.Measure.map (mvCLM L) (gaussianField G m) = gaussianField G m :=
  (gaussianField_map_iff_conjSq hm L).mpr (exists_orthogonal_of_symmetry hm hL)

/-- **AND NOTHING ELSE IS.** -/
theorem mem_linSym_of_gaussianField_map (hm : m ≠ 0) {L : Matrix V V ℝ}
    (hL : MeasureTheory.Measure.map (mvCLM L) (gaussianField G m) = gaussianField G m) :
    L ∈ linSym G m :=
  mem_linSym.mpr (mul_green_mul_transpose_of_map hm hL)

/-- **SO `linSym` IS THE SYMMETRY GROUP** and not merely a group of matrices carrying an
isomorphism: a matrix lies in it **iff** its map preserves the Gaussian field. -/
theorem mem_linSym_iff_gaussianField_map (hm : m ≠ 0) {L : Matrix V V ℝ} :
    L ∈ linSym G m ↔
      MeasureTheory.Measure.map (mvCLM L) (gaussianField G m) = gaussianField G m :=
  ⟨gaussianField_map_of_mem_linSym hm, mem_linSym_of_gaussianField_map hm⟩

/-! ## 5. And every continuous linear map is a matrix -/

omit [DecidableRel G.Adj] in
theorem exists_matrix (T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) :
    ∃ L : Matrix V V ℝ, mvCLM L = T := by
  refine ⟨Matrix.toEuclideanLin.symm T.toLinearMap, ?_⟩
  ext x
  simp [mvCLM]

/-- **SO THE CLASSIFICATION IS ABOUT MAPS AND NOT ONLY ABOUT MATRICES**: a continuous linear map
preserves the Gaussian field **iff** it is induced by a conjugated orthogonal matrix. -/
theorem gaussianField_map_iff_exists_orthogonal (hm : m ≠ 0)
    (T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) :
    MeasureTheory.Measure.map T (gaussianField G m) = gaussianField G m ↔
      ∃ O : Matrix V V ℝ, Oᵀ * O = 1 ∧ mvCLM (conjSq G m O) = T := by
  obtain ⟨L, rfl⟩ := exists_matrix T
  constructor
  · intro hT
    obtain ⟨O, hO, hOL⟩ := (gaussianField_map_iff_conjSq hm L).mp hT
    exact ⟨O, hO, by rw [hOL]⟩
  · rintro ⟨O, hO, hOL⟩
    rw [← hOL]
    exact (gaussianField_map_iff_conjSq hm _).mpr ⟨O, hO, rfl⟩

end FieldSymmetryIso
