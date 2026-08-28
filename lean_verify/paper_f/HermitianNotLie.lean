import TracelessSkewLie

/-!
# The traceless Hermitian matrices are not a Lie algebra, and they have the same dimension as one

`F3_8a_QuantumGravityFoundations` carries, in a docstring and again in a comment inside the very
result it labels:

> *"Traceless Hermitian matrices = su(4) Lie algebra. dim = 4² − 1 = 15."*
> *"su(4) = traceless Hermitian: dim 15"*

**The identification is false as written.** The commutator of two Hermitian matrices is
**anti**-Hermitian: `(AB − BA)ᴴ = BᴴAᴴ − AᴴBᴴ = BA − AB = −(AB − BA)`. So the traceless Hermitian
matrices are not closed under the bracket at all, and are a Lie algebra under no reading of `⁅·,·⁆`.

**And the reason it survived is exactly `ERRATUM 316`'s.** The two spaces have the **same real
dimension**, `n² − 1`, because multiplication by `i` is a real-linear bijection between them. A
dimension check cannot tell them apart, and a dimension check is all the estate ever ran.

**The docstring is not simply a mistake, either, and the file says which part is right.** The
physics literature writes `su(n)` generators as Hermitian matrices with the bracket `i⁅·,·⁆`, and
under **that** operation the traceless Hermitian matrices *are* closed and *are* carried onto the
compact form by `i`. Both halves are proved below, so the sentence can be repaired to the true one
rather than deleted.

## What is proved

> **`tracelessHerm ι`** — the traceless Hermitian matrices as a `Submodule ℝ (Matrix ι ι ℂ)`.
>
> **`lie_mem_skewSub_of_mem_hermSub`** — their commutator is anti-Hermitian, and
> **`lie_eq_zero_of_lie_mem_hermSub`**: if that commutator is *also* Hermitian it is **zero**. So
> `hermSub` is closed under the bracket only where it is abelian.
>
> **`tracelessHerm_not_lie_closed`** — and it is not abelian: two explicit traceless Hermitian
> `2 × 2` matrices whose commutator is nonzero, hence outside the space. The claim is refuted, not
> merely unproved.
>
> **`finrank_tracelessHerm = (card ι)² − 1`** — the same number as
> `TracelessSkewLie.finrank_tracelessSkewMat`, transported along `mulI`, so
> **`finrank_eq_tracelessSkewMat`** states the coincidence that hid the error.
>
> **`physBracket A B := i • ⁅A, B⁆`** and **`physBracket_mem`** — under the physicists' bracket
> the space *is* closed, and **`mulI_physBracket`** shows `A ↦ i • A` carries it to the ordinary
> bracket on the compact form. That is the true sentence the docstring was reaching for.

## What is NOT claimed

**No Lie algebra structure is built on `tracelessHerm`.** `physBracket` is a function; the Jacobi
identity for it is **not verified here** and no `LieRing` is declared, so the phrase "is a Lie
algebra under `i⁅·,·⁆`" is **not** a theorem below — what is proved is closure, which is the half
the false sentence got wrong.

**`mulI` is not exhibited as a `LieEquiv`.** `mulI_physBracket` is the intertwining equation;
bundling it would need the structure the previous paragraph declines to build.

**Nothing in `F3_8a` is withdrawn as a theorem.** `gauge_observables_su4` and
`gravity_is_gauge_substructure` state arithmetic about `finrank ℂ (Matrix (Fin 4) (Fin 4) ℂ)` and
about numerals; **those statements are true and their proofs are untouched**. What is wrong there
is the prose that names the objects, and it is corrected in place under `ERRATUM 94`.

**Nothing about `SU(n)` as a group, no smooth structure, no maximal tori, no roots.** The name
`su` is not used for any declaration, following `F4_1e_SpectralTripleArithmetic`.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace HermitianNotLie

open Matrix TracelessSkewLie

variable {ι : Type*} [Fintype ι]

/-! ## 1. The Hermitian matrices as a real submodule -/

/-- The Hermitian matrices, as a `Submodule ℝ` of the matrix algebra. Mathlib's `selfAdjoint` is
an `AddSubgroup` carrying its module structure on the subtype; this is the same set in the shape
the comparison below needs. -/
def hermSub (ι : Type*) [Fintype ι] : Submodule ℝ (Matrix ι ι ℂ) where
  carrier := {A | Aᴴ = A}
  add_mem' {A B} hA hB := by
    simp only [Set.mem_setOf_eq] at hA hB ⊢
    rw [Matrix.conjTranspose_add, hA, hB]
  zero_mem' := by simp
  smul_mem' r A hA := by
    simp only [Set.mem_setOf_eq] at hA ⊢
    rw [Matrix.conjTranspose_smul, hA]
    congr 1

theorem mem_hermSub_iff (A : Matrix ι ι ℂ) : A ∈ hermSub ι ↔ Aᴴ = A := Iff.rfl

/-- **`tracelessHerm ι`** — the space `F3_8a`'s docstring calls `su(4)` at `ι = Fin 4`. -/
noncomputable def tracelessHerm (ι : Type*) [Fintype ι] : Submodule ℝ (Matrix ι ι ℂ) :=
  hermSub ι ⊓ traceZeroSub ι

theorem mem_tracelessHerm_iff (A : Matrix ι ι ℂ) :
    A ∈ tracelessHerm ι ↔ Aᴴ = A ∧ Matrix.trace A = 0 := Iff.rfl

/-! ## 2. It is not closed under the bracket -/

/-- **THE COMMUTATOR OF TWO HERMITIAN MATRICES IS ANTI-HERMITIAN.** -/
theorem lie_mem_skewSub_of_mem_hermSub {A B : Matrix ι ι ℂ} (hA : A ∈ hermSub ι)
    (hB : B ∈ hermSub ι) : ⁅A, B⁆ ∈ skewSub ι := by
  rw [mem_hermSub_iff] at hA hB
  rw [mem_skewSub_iff, Ring.lie_def, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hA, hB]
  abel

/-- **AND IF IT IS ALSO HERMITIAN IT IS ZERO.** So `hermSub` is closed under the bracket exactly
where it is abelian — which is the precise sense in which it is not a Lie algebra. -/
theorem lie_eq_zero_of_lie_mem_hermSub {A B : Matrix ι ι ℂ} (hA : A ∈ hermSub ι)
    (hB : B ∈ hermSub ι) (h : ⁅A, B⁆ ∈ hermSub ι) : ⁅A, B⁆ = 0 := by
  have hskew : (⁅A, B⁆ : Matrix ι ι ℂ)ᴴ = -⁅A, B⁆ :=
    lie_mem_skewSub_of_mem_hermSub hA hB
  have hherm : (⁅A, B⁆ : Matrix ι ι ℂ)ᴴ = ⁅A, B⁆ := h
  have hneg : (⁅A, B⁆ : Matrix ι ι ℂ) = -⁅A, B⁆ := hherm.symm.trans hskew
  have h2 : (2 : ℂ) • (⁅A, B⁆ : Matrix ι ι ℂ) = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hneg]
    abel
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem mem_hermSub_of_mem_tracelessHerm {A : Matrix ι ι ℂ} (h : A ∈ tracelessHerm ι) :
    A ∈ hermSub ι :=
  (mem_hermSub_iff A).mpr ((mem_tracelessHerm_iff A).mp h).1

/-! ## 3. And it is not abelian: an explicit witness -/

/-- `diag(1, −1)`. -/
def hWitness₁ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The first Pauli matrix. -/
def hWitness₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

theorem hWitness₁_mem : hWitness₁ ∈ tracelessHerm (Fin 2) :=
  (mem_tracelessHerm_iff _).mpr
    ⟨by ext i j; fin_cases i <;> fin_cases j <;> simp [hWitness₁, Matrix.conjTranspose_apply],
     by simp [hWitness₁, Matrix.trace_fin_two]⟩

theorem hWitness₂_mem : hWitness₂ ∈ tracelessHerm (Fin 2) :=
  (mem_tracelessHerm_iff _).mpr
    ⟨by ext i j; fin_cases i <;> fin_cases j <;> simp [hWitness₂, Matrix.conjTranspose_apply],
     by simp [hWitness₂, Matrix.trace_fin_two]⟩

theorem lie_hWitness_ne_zero : (⁅hWitness₁, hWitness₂⁆ : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
  intro h
  have hval := congrFun (congrFun h 0) 1
  simp [Ring.lie_def, hWitness₁, hWitness₂] at hval

/-- **THE CLAIM IS REFUTED, NOT MERELY UNPROVED.** Two traceless Hermitian matrices whose
commutator leaves the space. -/
theorem tracelessHerm_not_lie_closed :
    hWitness₁ ∈ tracelessHerm (Fin 2) ∧ hWitness₂ ∈ tracelessHerm (Fin 2)
      ∧ ⁅hWitness₁, hWitness₂⁆ ∉ tracelessHerm (Fin 2) := by
  refine ⟨hWitness₁_mem, hWitness₂_mem, ?_⟩
  intro hmem
  exact lie_hWitness_ne_zero
    (lie_eq_zero_of_lie_mem_hermSub (mem_hermSub_of_mem_tracelessHerm hWitness₁_mem)
      (mem_hermSub_of_mem_tracelessHerm hWitness₂_mem)
      (mem_hermSub_of_mem_tracelessHerm hmem))

/-! ## 4. Multiplication by `i`, and the dimension that hid the error -/

/-- `A ↦ i • A`, real-linearly. -/
noncomputable def mulI (ι : Type*) [Fintype ι] : Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℂ where
  toFun A := Complex.I • A
  map_add' _ _ := by simp [smul_add]
  map_smul' r A := by
    simp only [RingHom.id_apply, smul_comm]

theorem mulI_apply (A : Matrix ι ι ℂ) : mulI ι A = Complex.I • A := rfl

theorem mulI_injective : Function.Injective (mulI ι) := by
  intro A B h
  have h' : Complex.I • A = Complex.I • B := h
  have := congrArg (fun M => (Complex.I⁻¹ : ℂ) • M) h'
  simpa [smul_smul, Complex.inv_I] using this

/-- **`i` CARRIES THE HERMITIAN SPACE ONTO THE COMPACT FORM.** -/
theorem map_tracelessHerm :
    Submodule.map (mulI ι) (tracelessHerm ι) = tracelessSkewMat ι := by
  ext X
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨hherm, htr⟩ := (mem_tracelessHerm_iff A).mp hA
    refine (mem_tracelessSkewMat_iff _).mpr ⟨?_, ?_⟩
    · rw [mulI_apply, Matrix.conjTranspose_smul, hherm, RCLike.star_def, Complex.conj_I, neg_smul]
    · rw [mulI_apply, Matrix.trace_smul, htr, smul_zero]
  · intro hX
    obtain ⟨hskew, htr⟩ := (mem_tracelessSkewMat_iff X).mp hX
    refine ⟨(-Complex.I) • X, ?_, ?_⟩
    · refine (mem_tracelessHerm_iff _).mpr ⟨?_, ?_⟩
      · rw [Matrix.conjTranspose_smul, hskew, RCLike.star_def, map_neg, Complex.conj_I, neg_neg,
          smul_neg, neg_smul]
      · rw [Matrix.trace_smul, htr, smul_zero]
    · rw [mulI_apply, smul_smul]
      simp

/-- **THE SAME DIMENSION**, which is why no count in this estate could have caught the error. -/
theorem finrank_tracelessHerm [Nonempty ι] :
    Module.finrank ℝ (tracelessHerm ι) = Fintype.card ι ^ 2 - 1 := by
  rw [← finrank_tracelessSkewMat ι, ← map_tracelessHerm,
    (Submodule.equivMapOfInjective (mulI ι) mulI_injective (tracelessHerm ι)).finrank_eq]

theorem finrank_eq_tracelessSkewMat [Nonempty ι] :
    Module.finrank ℝ (tracelessHerm ι) = Module.finrank ℝ (tracelessSkewMat ι) := by
  rw [finrank_tracelessHerm, finrank_tracelessSkewMat]

/-! ## 5. The physicists' bracket, which is the true reading -/

/-- `i⁅A, B⁆` — the operation under which the physics literature's Hermitian generators close. -/
noncomputable def physBracket (A B : Matrix ι ι ℂ) : Matrix ι ι ℂ := Complex.I • ⁅A, B⁆

/-- **UNDER THAT OPERATION THE SPACE IS CLOSED.** -/
theorem physBracket_mem {A B : Matrix ι ι ℂ} (hA : A ∈ tracelessHerm ι)
    (hB : B ∈ tracelessHerm ι) : physBracket A B ∈ tracelessHerm ι := by
  have hskew : (⁅A, B⁆ : Matrix ι ι ℂ)ᴴ = -⁅A, B⁆ :=
    lie_mem_skewSub_of_mem_hermSub (mem_hermSub_of_mem_tracelessHerm hA)
      (mem_hermSub_of_mem_tracelessHerm hB)
  refine (mem_tracelessHerm_iff _).mpr ⟨?_, ?_⟩
  · rw [physBracket, Matrix.conjTranspose_smul, hskew, RCLike.star_def, Complex.conj_I,
      neg_smul_neg]
  · rw [physBracket, Matrix.trace_smul, Ring.lie_def, Matrix.trace_sub, Matrix.trace_mul_comm]
    simp

/-- **AND `i` INTERTWINES IT WITH THE ORDINARY BRACKET.** No hypotheses: this is an identity on
all matrices. -/
theorem mulI_physBracket (A B : Matrix ι ι ℂ) :
    mulI ι (physBracket A B) = ⁅mulI ι A, mulI ι B⁆ := by
  rw [mulI_apply, mulI_apply, mulI_apply, physBracket, Ring.lie_def, Ring.lie_def,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, smul_smul,
    smul_smul, ← smul_sub]

end HermitianNotLie
