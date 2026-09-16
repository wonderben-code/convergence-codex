/-
  StarStructureTwistFibre: the twist is pinned to a nonzero REAL scalar, and two ⋆-structures
  on M₂(ℂ) are separated

  SPINE LINK L11 — `UNLOCK_WATCHLIST` line 39104, item (1)'s residue: *the signature of `P`*.

  WHERE THIS PICKS UP. `StarStructureHermitian.exists_hermitian_twist` proved that every
  ⋆-structure on `Mₙ(ℂ)` is `X ↦ (P X P⁻¹)ᴴ` with `P` invertible and HERMITIAN, and its own
  header then said, of the sentence *"what remains is a non-degenerate Hermitian form up
  to scalars, that is, a signature"*:

  > **That last sentence is a description of the remaining object and not a theorem about it**
  > — the signature is not computed and no two ⋆-structures are shown equivalent or
  > inequivalent.

  **This file makes the first clause a theorem and closes one reading of the second.** It does
  not compute the signature; §"WHAT IS NOT CLAIMED" says exactly what is still owed and prices
  it.

  WHAT IS PROVED.
  * **`twistMap` and `hermitianStar`** — the presentation as a FUNCTION OF THE TWIST. The
    estate had a pointwise formula for a given `s` (`exists_hermitian_twist`) and one
    instantiated structure (`conjTransposeStar`, the untwisted case). **It had no map from
    twists to ⋆-structures, so "up to scalars" could not even be stated as a fibre.**
    `hermitianStar P hP` supplies it, and `inv_hermitian` is where Hermitian-ness of the twist
    is spent: it is needed for `map_involutive` and for nothing else in the structure.
  * **`twistMap_smulTwist`** — **the map cannot see the scalar at all.** Rescaling a twist by
    ANY nonzero complex scalar presents the same map; the two occurrences of the scalar cancel.
    No Hermitian hypothesis is used.
  * **`smulTwist_hermitian_iff`** — **and Hermitian-ness is exactly what narrows that
    ambiguity.** `c • P` is Hermitian iff `c` is real. So the entire purchase of the normal
    form is the passage from `ℂˣ` to `ℝˣ`, stated here as an iff rather than gestured at.
  * **`twist_unique`** — the converse, and the headline: **two Hermitian twists presenting the
    same map differ by a nonzero REAL scalar.** `conjTranspose` is injective, so the two
    conjugations agree; `Q⁻¹ P` then commutes with everything, so
    `StarStructureMatrix.matrix_center_scalar` makes it `c • 1` and `P = c • Q`; and
    conjugate-transposing that against `Pᴴ = P`, `Qᴴ = Q` forces `conj c = c`. **Both Hermitian
    hypotheses are spent on the realness of `c` and buy nothing else.**
  * **`twistMap_eq_iff` and `hermitianStar_eq_iff`** — **the fibre, computed**, in both
    readings: equal maps, and equal ⋆-structures. With `hermitianStar_surjective` (which is
    `exists_hermitian_twist` repackaged as an equality of structures through
    `starStructure_eq_of_map`) this says the ⋆-structures on `Mₙ(ℂ)` are in bijection with the
    Hermitian units modulo `ℝˣ`.
  * **`realScalarRel_equivalence`** — *"modulo `ℝˣ`"* is a quotient of a genuine equivalence
    relation. **Without this the previous bullet would be a reading of the statements rather
    than a fact about them**, so it is proved rather than assumed.
  * **`hermitianStar_neg`** — **what no invariant of the ⋆-structure can see.** `P` and `-P`
    present the same ⋆-structure. So a complete invariant is a function of the `ℝˣ`-orbit, and
    in particular cannot separate a Hermitian form from its negative: **whatever the invariant
    turns out to be, it can be a signature only up to exchanging its two parts.**
  * **`conjTransposeStar_ne_diagTwist`** — **two ⋆-structures on `M₂(ℂ)` that are literally
    different maps.** `X ↦ Xᴴ` is `hermitianStar 1` (`hermitianStar_one`, which ties the new
    map to the estate's existing object), `X ↦ D Xᴴ D` is `hermitianStar diagTwist` for
    `D = diag(1,-1)`, and `diag(1,-1)` is not a real multiple of `1` — read off two diagonal
    entries. **Before this, the estate exhibited exactly one object of type `StarStructure`** —
    `conjTransposeStar`, the untwisted case — **and, measured 2026-09-16 over the whole index,
    carried no statement anywhere that two ⋆-structures differ.** Said exactly, because the
    loose version is false and the gate caught it: **five more ⋆-structures are exhibited on
    OTHER carriers** in the ring-level `StarStr`/`StarStrC` sense —
    `StarStructurePi.conjPermStar` on `∏ ℂ`, and `prodConjTranspose`, `prodSwapTranspose` with
    their two `C` twins on a product of two matrix algebras — so *one anywhere* was wrong while
    *one of this type* is right. The disequality is what had no instance, and the fibre supplies
    it in one line, which is the point of computing a fibre.

  WHAT IS **NOT** CLAIMED.
  * **The signature is still not computed.** No invariant is constructed here. The file says
    precisely which twists collide; it does not say which Hermitian forms there are up to `ℝˣ`.
  * **`conjTransposeStar_ne_diagTwist` separates the two structures as MAPS, not up to
    EQUIVALENCE**, and the difference is not cosmetic. ⋆-structures are classified in the
    literature up to conjugation by an algebra automorphism — `t = α⁻¹ ∘ s ∘ α` — and the
    `ℝˣ`-classes computed here are a strictly finer partition than the conjugation classes.
    Classically these two ⋆-structures are inequivalent because their signatures `(2,0)` and
    `(1,1)` differ; **that is not what is proved here.**
  * **What the missing step needs, measured rather than guessed.** The pinned Mathlib has both
    halves of Sylvester's law of inertia — `Mathlib/LinearAlgebra/QuadraticForm/Signature.lean`
    with `QuadraticMap.Equivalent.sigPos_eq` and `sigNeg_eq` for invariance under equivalence
    and `sigPos_of_equiv_weightedSumSquares` for the computation, existence being
    `equivalent_one_zero_neg_one_weighted_sum_squared` in `QuadraticForm/Real.lean` — **and
    this estate already uses that API**, in the Clifford development (`CliffordHypTower`,
    `CliffordHyperbolicStep`; 105 estate statements name `sigPos` or `sigNeg`). **What is
    absent is the bridge, and it is bespoke work rather than a lemma.** A complex Hermitian
    form is sesquilinear, not `ℂ`-bilinear, so it is not `QuadraticMap.restrictScalars` of
    anything; the passage is `x ↦ re ⟪x, P x⟫` on the underlying real space, with the Hermitian
    signature `(p, q)` appearing as `(2p, 2q)`. **The estate has 0 declarations whose
    statement names both a quadratic form and `IsHermitian` or `conjTranspose`** — grepped —
    and Mathlib's `QuadraticForm` directory names `IsHermitian` nowhere.
  * **Nothing over `ℝ` or `ℍ`.** `twist_unique` is a statement about `ℂ` and uses that the
    Hermitian condition is `conj`-linear over it.
  * **Nothing about the cascade is cut.** `a·b·c = 16` keeps every alternative
    (`ASSUMPTIONS_LEDGER` 5, 10, 11, 30, 35). The fibre sharpens L11's residue from *a Hermitian
    form up to scalars* to *up to real scalars*; **a sharper residue is still a residue and
    prefers no factorisation.**

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import StarStructureHermitian

namespace StarStructureTwistFibre

open Matrix StarStructureMatrix StarStructureHermitian

noncomputable section

variable {n : ℕ}

/-! ## 1. The presentation map -/

/-- The map a twist `P` presents: `X ↦ (P X P⁻¹)ᴴ`. -/
def twistMap (P : (Matrix (Fin n) (Fin n) ℂ)ˣ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ((P : Matrix (Fin n) (Fin n) ℂ) * X
    * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))ᴴ

@[simp] theorem twistMap_apply (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    twistMap P X = ((P : Matrix (Fin n) (Fin n) ℂ) * X
      * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))ᴴ := rfl

theorem twistMap_congr {P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ}
    (h : (P : Matrix (Fin n) (Fin n) ℂ) = (Q : Matrix (Fin n) (Fin n) ℂ)) :
    twistMap P = twistMap Q := by
  have : P = Q := Units.ext h
  rw [this]

/-! ## 2. Rescaling a twist -/

/-- A twist rescaled by a nonzero complex scalar. -/
def smulTwist (c : ℂ) (hc : c ≠ 0) (P : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    (Matrix (Fin n) (Fin n) ℂ)ˣ where
  val := c • (P : Matrix (Fin n) (Fin n) ℂ)
  inv := c⁻¹ • ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
  val_inv := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
    simp
  inv_val := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
    simp

@[simp] theorem smulTwist_val (c : ℂ) (hc : c ≠ 0) (P : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    ((smulTwist c hc P : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = c • (P : Matrix (Fin n) (Fin n) ℂ) := rfl

@[simp] theorem smulTwist_inv_val (c : ℂ) (hc : c ≠ 0) (P : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    (((smulTwist c hc P)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = c⁻¹ • ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := rfl

/-- **The map cannot see the scalar.** Rescaling a twist by ANY nonzero complex scalar
presents the same map. -/
theorem twistMap_smulTwist (c : ℂ) (hc : c ≠ 0) (P : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    twistMap (smulTwist c hc P) = twistMap P := by
  funext X
  simp only [twistMap_apply, smulTwist_val, smulTwist_inv_val]
  congr 1
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hc,
    one_smul]

/-! ## 3. A unit is not zero, and the inverse of a Hermitian twist is Hermitian -/

/-- A unit of `Mₙ(ℂ)` is not the zero matrix. The estate inlines this argument twice; it is
named here once. -/
theorem unit_ne_zero [NeZero n] (P : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    (P : Matrix (Fin n) (Fin n) ℂ) ≠ 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  intro h
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
    have hmi := P.mul_inv
    rw [h, Matrix.zero_mul] at hmi
    exact hmi.symm
  exact one_ne_zero h1

/-- The inverse of a Hermitian twist is Hermitian. -/
theorem inv_hermitian (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ)) :
    ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
      = ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
  have h1 : ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
      * (P : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    rw [← hP, ← Matrix.conjTranspose_mul]
    simp
  calc ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
      = ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
        * ((P : Matrix (Fin n) (Fin n) ℂ)
          * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by simp
    _ = (((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
          * (P : Matrix (Fin n) (Fin n) ℂ))
        * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
          rw [Matrix.mul_assoc]
    _ = ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
          rw [h1, Matrix.one_mul]

/-- **Rescaling keeps the twist Hermitian exactly when the scalar is real.** This is the whole
price of the normal form: the presentation map cannot see the scalar at all, and Hermitian-ness
cuts the ambiguity from `ℂˣ` down to `ℝˣ`. -/
theorem smulTwist_hermitian_iff [NeZero n] (c : ℂ) (hc : c ≠ 0)
    (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ)) :
    ((smulTwist c hc P : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
        = ((smulTwist c hc P : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      ↔ ∃ r : ℝ, c = (r : ℂ) := by
  simp only [smulTwist_val, Matrix.conjTranspose_smul, hP]
  constructor
  · intro h
    have h2 : (star c - c) • (P : Matrix (Fin n) (Fin n) ℂ) = 0 := by
      rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · have h4 : (starRingEnd ℂ) c = c := sub_eq_zero.1 h3
      exact ⟨c.re, (Complex.conj_eq_iff_re.1 h4).symm⟩
    · exact absurd h3 (unit_ne_zero P)
  · rintro ⟨r, rfl⟩
    rw [show star ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) from Complex.conj_ofReal r]

/-! ## 4. The fibre of the presentation map -/

/-- **The Hermitian twist is determined up to a nonzero REAL scalar.** Two Hermitian twists
presenting the same map differ by a real scalar. -/
theorem twist_unique [NeZero n] (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ))
    (h : twistMap P = twistMap Q) :
    ∃ r : ℝ, r ≠ 0 ∧ (P : Matrix (Fin n) (Fin n) ℂ) = (r : ℂ) • (Q : Matrix (Fin n) (Fin n) ℂ) := by
  classical
  have hconj : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      (P : Matrix (Fin n) (Fin n) ℂ) * X * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)
      = (Q : Matrix (Fin n) (Fin n) ℂ) * X * ((Q⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ) := fun X =>
    Matrix.conjTranspose_injective (by simpa using congrFun h X)
  set M : Matrix (Fin n) (Fin n) ℂ :=
    ((Q⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      * (P : Matrix (Fin n) (Fin n) ℂ) with hM
  have hcent : ∀ A : Matrix (Fin n) (Fin n) ℂ, M * A = A * M := by
    intro A
    have hA := hconj A
    have hQi : ((Q⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        * (Q : Matrix (Fin n) (Fin n) ℂ) = 1 := by simp
    calc M * A
        = ((Q⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
            * ((P : Matrix (Fin n) (Fin n) ℂ) * A) := by rw [hM]; noncomm_ring
      _ = ((Q⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
            * ((P : Matrix (Fin n) (Fin n) ℂ) * A
              * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
              * (P : Matrix (Fin n) (Fin n) ℂ)) := by
            congr 1
            rw [Matrix.mul_assoc, Matrix.mul_assoc]
            congr 1
            rw [← Matrix.mul_assoc]
            simp
      _ = ((Q⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
            * ((Q : Matrix (Fin n) (Fin n) ℂ) * A
              * ((Q⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
              * (P : Matrix (Fin n) (Fin n) ℂ)) := by rw [hA]
      _ = A * M := by
            rw [hM]
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQi, Matrix.one_mul]
            noncomm_ring
  obtain ⟨c, hc⟩ := StarStructureMatrix.matrix_center_scalar M hcent
  have hPQ : (P : Matrix (Fin n) (Fin n) ℂ) = c • (Q : Matrix (Fin n) (Fin n) ℂ) := by
    have hQM : (Q : Matrix (Fin n) (Fin n) ℂ) * M = (P : Matrix (Fin n) (Fin n) ℂ) := by
      rw [hM, ← Matrix.mul_assoc]; simp
    rw [← hQM, hc, Matrix.mul_smul, Matrix.mul_one]
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hPQ
    exact unit_ne_zero P hPQ
  have hstar : star c • (Q : Matrix (Fin n) (Fin n) ℂ)
      = c • (Q : Matrix (Fin n) (Fin n) ℂ) := by
    calc star c • (Q : Matrix (Fin n) (Fin n) ℂ)
        = star c • (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ := by rw [hQ]
      _ = (c • (Q : Matrix (Fin n) (Fin n) ℂ))ᴴ := by rw [Matrix.conjTranspose_smul]
      _ = (P : Matrix (Fin n) (Fin n) ℂ)ᴴ := by rw [hPQ]
      _ = (P : Matrix (Fin n) (Fin n) ℂ) := hP
      _ = c • (Q : Matrix (Fin n) (Fin n) ℂ) := hPQ
  have hcr : (starRingEnd ℂ) c = c := by
    have h2 : (star c - c) • (Q : Matrix (Fin n) (Fin n) ℂ) = 0 := by
      rw [sub_smul, hstar, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 (unit_ne_zero Q)
  have hre : ((c.re : ℝ) : ℂ) = c := Complex.conj_eq_iff_re.1 hcr
  refine ⟨c.re, ?_, ?_⟩
  · intro h0
    rw [h0] at hre
    exact hcne (by simpa using hre.symm)
  · rw [hre]; exact hPQ

/-- **The fibre, computed.** Two Hermitian twists present the same map exactly when they
differ by a nonzero real scalar. The forward direction is `twist_unique`; the converse is
`twistMap_smulTwist`, which needs no realness at all. -/
theorem twistMap_eq_iff [NeZero n] (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ)) :
    twistMap P = twistMap Q
      ↔ ∃ r : ℝ, r ≠ 0 ∧ (P : Matrix (Fin n) (Fin n) ℂ)
          = (r : ℂ) • (Q : Matrix (Fin n) (Fin n) ℂ) := by
  refine ⟨twist_unique P Q hP hQ, ?_⟩
  rintro ⟨r, hr, hPQ⟩
  have hrc : ((r : ℝ) : ℂ) ≠ 0 := by
    simpa using hr
  calc twistMap P = twistMap (smulTwist ((r : ℝ) : ℂ) hrc Q) :=
        twistMap_congr (by simpa using hPQ)
    _ = twistMap Q := twistMap_smulTwist _ _ _

/-! ## 5. The classification as a surjection with a computed fibre -/

/-- **Every Hermitian twist presents a ⋆-structure.** The estate had only the untwisted
`conjTransposeStar`; involutivity is where Hermitian-ness of the twist is spent. -/
def hermitianStar (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ)) :
    StarStructure n where
  map := twistMap P
  map_add := by
    intro X Y
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul := by
    intro c X
    simp
  map_mul := by
    intro X Y
    simp only [twistMap_apply]
    rw [← Matrix.conjTranspose_mul]
    congr 1
    have him : ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        * (P : Matrix (Fin n) (Fin n) ℂ) = 1 := by simp
    calc (P : Matrix (Fin n) (Fin n) ℂ) * (X * Y)
          * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        = (P : Matrix (Fin n) (Fin n) ℂ) * X
            * (((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
              * (P : Matrix (Fin n) (Fin n) ℂ)) * Y
            * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
          rw [him]; noncomm_ring
      _ = ((P : Matrix (Fin n) (Fin n) ℂ) * X
            * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
          * ((P : Matrix (Fin n) (Fin n) ℂ) * Y
            * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
          noncomm_ring
  map_involutive := by
    intro X
    have hinv := inv_hermitian P hP
    have him : ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        * (P : Matrix (Fin n) (Fin n) ℂ) = 1 := by simp
    simp only [twistMap_apply]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP, hinv,
      Matrix.conjTranspose_conjTranspose]
    calc ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
          * ((P : Matrix (Fin n) (Fin n) ℂ) * X
            * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
            * (P : Matrix (Fin n) (Fin n) ℂ))
        = (((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
            * (P : Matrix (Fin n) (Fin n) ℂ)) * X
          * (((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
            * (P : Matrix (Fin n) (Fin n) ℂ)) := by noncomm_ring
      _ = X := by rw [him, Matrix.one_mul, Matrix.mul_one]

@[simp] theorem hermitianStar_map (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ)) :
    (hermitianStar P hP).map = twistMap P := rfl

/-- A `StarStructure` is its map: the other fields are propositions. -/
theorem starStructure_eq_of_map {s t : StarStructure n} (h : s.map = t.map) : s = t := by
  obtain ⟨m, ha, hs, hm, hi⟩ := s
  obtain ⟨m', ha', hs', hm', hi'⟩ := t
  have hmm : m = m' := h
  subst hmm
  rfl

/-- **Surjectivity**: every ⋆-structure on `Mₙ(ℂ)` IS `hermitianStar P` for some Hermitian
unit `P`. This is `exists_hermitian_twist` repackaged so that the presentation is an equality
of ⋆-structures rather than a pointwise formula. -/
theorem hermitianStar_surjective [NeZero n] (s : StarStructure n) :
    ∃ (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
      (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ)),
      hermitianStar P hP = s := by
  obtain ⟨P, hherm, hmap⟩ := StarStructureHermitian.exists_hermitian_twist s
  exact ⟨P, hherm, starStructure_eq_of_map (funext fun X => (hmap X).symm)⟩

/-- **The fibre of the classification.** Two Hermitian twists present the same ⋆-STRUCTURE
exactly when they differ by a nonzero real scalar. With `hermitianStar_surjective` this says
the ⋆-structures on `Mₙ(ℂ)` are in bijection with the Hermitian units modulo `ℝˣ` — and that
is the precise sense in which the residue is "a Hermitian form up to scalars". -/
theorem hermitianStar_eq_iff [NeZero n] (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ)) :
    hermitianStar P hP = hermitianStar Q hQ
      ↔ ∃ r : ℝ, r ≠ 0 ∧ (P : Matrix (Fin n) (Fin n) ℂ)
          = (r : ℂ) • (Q : Matrix (Fin n) (Fin n) ℂ) := by
  rw [← twistMap_eq_iff P Q hP hQ]
  exact ⟨fun h => congrArg StarStructure.map h, fun h => starStructure_eq_of_map h⟩

/-- **What no invariant of the ⋆-structure can see.** `P` and `-P` present the SAME
⋆-structure. So a complete invariant of the ⋆-structure is a function of the `ℝˣ`-orbit of the
Hermitian form, and in particular it cannot separate a form from its negative. -/
theorem hermitianStar_neg [NeZero n] (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hnP : ((-P : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
      = ((-P : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) :
    hermitianStar (-P) hnP = hermitianStar P hP := by
  rw [hermitianStar_eq_iff]
  exact ⟨-1, by norm_num, by simp⟩

/-! ## 6. The relation is an equivalence, and two ⋆-structures are separated -/

/-- The relation the fibre computes: two twists differ by a nonzero real scalar. -/
def RealScalarRel (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Prop :=
  ∃ r : ℝ, r ≠ 0 ∧ (P : Matrix (Fin n) (Fin n) ℂ) = (r : ℂ) • (Q : Matrix (Fin n) (Fin n) ℂ)

theorem realScalarRel_iff (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    RealScalarRel P Q ↔ ∃ r : ℝ, r ≠ 0 ∧ (P : Matrix (Fin n) (Fin n) ℂ)
      = (r : ℂ) • (Q : Matrix (Fin n) (Fin n) ℂ) := Iff.rfl

/-- **"Modulo `ℝˣ`" is a quotient of a genuine equivalence relation.** Without this the phrase
in `hermitianStar_eq_iff` would be a reading of the statement rather than a fact about it. -/
theorem realScalarRel_equivalence : Equivalence (RealScalarRel (n := n)) where
  refl P := ⟨1, one_ne_zero, by simp⟩
  symm := by
    rintro P Q ⟨r, hr, h⟩
    refine ⟨r⁻¹, inv_ne_zero hr, ?_⟩
    have hrc : ((r : ℝ) : ℂ) ≠ 0 := by simpa using hr
    rw [h, smul_smul, Complex.ofReal_inv, inv_mul_cancel₀ hrc, one_smul]
  trans := by
    rintro P Q R ⟨r, hr, h⟩ ⟨s, hs, h'⟩
    refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
    rw [h, h', smul_smul, Complex.ofReal_mul]

/-- The negative of a Hermitian twist is Hermitian, so `hermitianStar_neg` has a hypothesis
that can be met. -/
theorem neg_hermitian (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ)) :
    ((-P : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ
      = ((-P : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
  simp [hP]

/-- The untwisted case is the estate's `conjTransposeStar`. -/
theorem hermitianStar_one (m : ℕ) :
    hermitianStar (1 : (Matrix (Fin m) (Fin m) ℂ)ˣ) (by simp) = conjTransposeStar m := by
  refine starStructure_eq_of_map (funext fun X => ?_)
  simp [hermitianStar, conjTransposeStar]

/-- The indefinite twist `diag(1, -1)` on `M₂(ℂ)`, as a unit. -/
def diagTwist : (Matrix (Fin 2) (Fin 2) ℂ)ˣ where
  val := Matrix.diagonal ![1, -1]
  inv := Matrix.diagonal ![1, -1]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp

theorem diagTwist_hermitian :
    ((diagTwist : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
      = ((diagTwist : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  change (Matrix.diagonal ![(1 : ℂ), -1])ᴴ = Matrix.diagonal ![(1 : ℂ), -1]
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  fin_cases i <;> simp

theorem one_not_realScalarRel_diagTwist :
    ¬ RealScalarRel (1 : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) diagTwist := by
  rintro ⟨r, hr, h⟩
  have h00 : (1 : ℂ) = (r : ℂ) := by
    simpa [diagTwist, Matrix.diagonal_apply_eq] using congrFun (congrFun h 0) 0
  have h11 : (1 : ℂ) = -(r : ℂ) := by
    simpa [diagTwist, Matrix.diagonal_apply_eq] using congrFun (congrFun h 1) 1
  have h2 : (2 : ℂ) = 0 := by linear_combination h00 + h11
  norm_num at h2

/-- **Two ⋆-structures on `M₂(ℂ)` that are literally different maps.** The estate could not
say this before: `StarStructureHermitian` reduced every ⋆-structure to a Hermitian twist but
proved nothing about which twists collide. The fibre does it in one line. -/
theorem conjTransposeStar_ne_diagTwist :
    conjTransposeStar 2 ≠ hermitianStar diagTwist diagTwist_hermitian := by
  intro h
  have h1 : hermitianStar (1 : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) (by simp)
      = hermitianStar diagTwist diagTwist_hermitian := by
    rw [hermitianStar_one, h]
  exact one_not_realScalarRel_diagTwist ((hermitianStar_eq_iff _ _ _ _).1 h1)

end

end StarStructureTwistFibre
