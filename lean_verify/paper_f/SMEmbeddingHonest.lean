/-
  SMEmbeddingHonest: What Does — and Does Not — Embed in sl₄(ℂ)
  ==============================================================

  The estate's `LieAlgebraEmbedding` builds three individually genuine
  maps into sl₄(ℂ) — sl₃ (upper-left 3×3 block), sl₂ (lower-right 2×2
  block), u(1) (the diagonal diag(c,c,c,−3c)) — each injective,
  traceless-valued and bracket-preserving, and proves the ABSTRACT
  dimension arithmetic 8 + 3 + 1 = 12 < 15. All of those theorems are
  true and none is touched here. The file's closing docstring then reads
  the package as "the GENUINE proof that the Standard Model gauge
  algebra embeds in su(4) as a Lie subalgebra — not just a linear
  subspace". This file machine-checks that the reading is FALSE for
  these maps (ERRATA 36), and proves what is actually true instead.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `u1_eq_su3_add_su2` — THE OVERLAP: the u(1) image lies inside the
     span of the sl₃ and sl₂ images, entirely: diag(c,c,c,−3c) =
     su3(diag(c,c,−2c)) + su2(diag(3c,−3c)). The "third direction" is
     not a third direction.
  2. `assembly_not_injective` / `assembly_range_le_eleven` — the
     assembled linear map (A, B, c) ↦ su3(A) + su2(B) + u1(c) on
     sl₃ × sl₂ × u(1) has a NONZERO KERNEL (explicit element, from the
     overlap), so the three images span AT MOST an 11-dimensional
     subspace of sl₄ — strictly less than the 12 the abstract
     arithmetic suggests. Three injective maps do not make an injective
     assembly.
  3. `su3_su2_images_not_commuting` / `su2_u1_images_not_commuting` —
     the sl₃ and sl₂ images do NOT commute (the blocks share row and
     column 2), and the sl₂ image does not commute with the u(1) image
     either. In the direct sum su(3)⊕su(2)⊕u(1) distinct factors
     commute, and a Lie-algebra embedding preserves that; so the
     assembled map is not even a Lie homomorphism, let alone injective.
     "Embeds in su(4) as a Lie subalgebra" fails on both counts.
  4. WHAT IS TRUE — colour and B−L: `su3_u1_commute` (the sl₃ image
     commutes with the u(1) image), `su3_u1_injective` (the pair
     (A, c) ↦ su3(A) + u1(c) IS injective), `colour_bl_finrank` (its
     range is a genuine 9-dimensional subspace of the 15-dimensional
     sl₄), and `leptoquark_six`: the complement count is 15 − 9 = 6 —
     the six Pati–Salam leptoquark directions of the honest coset
     su(4)/(su(3)⊕u(1)_{B−L}), not the "3 extra generators" of the
     abstract 15 − 12 arithmetic.
  5. `sm_assembly_corrected` — the package: both refutations, both
     non-commutation witnesses, and the honest positive, in one
     statement.

  NOT proven here (prose, so nobody reads more than is proved):

  * The rank obstruction — su(3)⊕su(2)⊕u(1) has rank 4 and su(4) has
    rank 3, so NO faithful embedding exists by ANY maps, not just these
    (a 4-dim rep of sl₃⊕sl₂ faithful on both factors does not exist).
    That argument needs representation/Cartan theory the estate does
    not have; this file refutes exactly the assembly the docstring
    cited and no more.
  * Nothing about groups, fermion representations, or the Weinberg
    angle. The successor file computes the Weinberg trace forms on the
    honest Pati–Salam representation, where SU(2)_L is a separate
    factor exactly because of what is proven here, and hypercharge is
    Y = T₃R + (B−L)/2 with B−L the u(1) direction of THIS file.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import LieAlgebraEmbedding
import Mathlib.LinearAlgebra.Matrix.Notation

open Matrix Module

noncomputable section

namespace SMEmbeddingHonest

/-! ## 1. The overlap: the u(1) image sits inside sl₃-image + sl₂-image -/

/-- The traceless 3×3 half of the overlap decomposition: diag(c,c,−2c). -/
def overlap3 (c : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := !![c, 0, 0; 0, c, 0; 0, 0, -2 * c]

/-- The traceless 2×2 half of the overlap decomposition: diag(3c,−3c). -/
def overlap2 (c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![3 * c, 0; 0, -3 * c]

theorem overlap3_mem (c : ℂ) : overlap3 c ∈ TracelessMatrix 3 := by
  simp only [TracelessMatrix, LinearMap.mem_ker, traceMap, Matrix.traceLinearMap_apply]
  simp [overlap3, Matrix.trace_fin_three]
  ring

theorem overlap2_mem (c : ℂ) : overlap2 c ∈ TracelessMatrix 2 := by
  simp only [TracelessMatrix, LinearMap.mem_ker, traceMap, Matrix.traceLinearMap_apply]
  simp [overlap2, Matrix.trace_fin_two]

/-- **The overlap identity**: the u(1) generator is a sum of an sl₃-image
    element and an sl₂-image element. diag(c,c,c,−3c) =
    su3(diag(c,c,−2c)) + su2(diag(3c,−3c)), for every c. -/
theorem u1_eq_su3_add_su2 (c : ℂ) :
    u1EmbedFn c = su3EmbedFn (overlap3 c) + su2EmbedFn (overlap2 c) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [u1EmbedFn, su3EmbedFn, su2EmbedFn, overlap3, overlap2]
  all_goals ring

/-! ## 2. The assembled map has a kernel -/

/-- The assembled three-factor linear map (A, B, c) ↦ su3(A) + su2(B) + u1(c),
    exactly the object the estate docstring's "embeds in su(4)" reading
    quantifies over. -/
def assembly : ((TracelessMatrix 3 × TracelessMatrix 2) × ℂ) →ₗ[ℂ] TracelessMatrix 4 :=
  (su3EmbedRestricted.coprod su2EmbedRestricted).coprod u1EmbedRestricted

/-- The explicit kernel element: (diag(1,1,−2), diag(3,−3), −1). -/
def kernelElt : (TracelessMatrix 3 × TracelessMatrix 2) × ℂ :=
  ((⟨overlap3 1, overlap3_mem 1⟩, ⟨overlap2 1, overlap2_mem 1⟩), (-1 : ℂ))

theorem assembly_kernelElt : assembly kernelElt = 0 := by
  apply Subtype.ext
  change su3EmbedFn (overlap3 1) + su2EmbedFn (overlap2 1) + u1EmbedFn (-1)
    = (0 : Matrix (Fin 4) (Fin 4) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [su3EmbedFn, su2EmbedFn, u1EmbedFn, overlap3, overlap2]

/-- **The assembly is not injective**: three individually injective maps,
    one non-injective sum. The kernel element is nonzero (its u(1)
    component is −1). -/
theorem assembly_not_injective : ¬ Function.Injective assembly := by
  intro h
  have h0 : assembly kernelElt = assembly 0 := by rw [assembly_kernelElt, map_zero]
  have hc : (-1 : ℂ) = 0 := congrArg Prod.snd (h h0)
  norm_num at hc

/-- **The three images span at most 11 dimensions** — not the 12 of the
    abstract arithmetic: rank–nullity plus a nontrivial kernel. -/
theorem assembly_range_le_eleven :
    finrank ℂ (LinearMap.range assembly) ≤ 11 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker assembly
  have hdom : finrank ℂ ((TracelessMatrix 3 × TracelessMatrix 2) × ℂ) = 12 := by
    rw [Module.finrank_prod, Module.finrank_prod, traceless_dim_3, traceless_dim_2,
      Module.finrank_self]
  have hker_ne : LinearMap.ker assembly ≠ ⊥ := by
    intro hbot
    exact assembly_not_injective (LinearMap.ker_eq_bot.mp hbot)
  have hker : 0 < finrank ℂ (LinearMap.ker assembly) := by
    rw [finrank_pos_iff]
    exact Submodule.nontrivial_iff_ne_bot.mpr hker_ne
  rw [hdom] at hrn
  omega

/-! ## 3. The images do not pairwise commute -/

/-- Traceless witness in sl₃: the elementary matrix E₀₂. -/
def e02 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 0, 0, 0; 0, 0, 0]

/-- Traceless witness in sl₂: diag(1,−1). -/
def d2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Traceless witness in sl₂: the elementary matrix E₀₁. -/
def e01 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

theorem e02_mem : e02 ∈ TracelessMatrix 3 := by
  simp only [TracelessMatrix, LinearMap.mem_ker, traceMap, Matrix.traceLinearMap_apply]
  simp [e02, Matrix.trace_fin_three]

theorem d2_mem : d2 ∈ TracelessMatrix 2 := by
  simp only [TracelessMatrix, LinearMap.mem_ker, traceMap, Matrix.traceLinearMap_apply]
  simp [d2, Matrix.trace_fin_two]

theorem e01_mem : e01 ∈ TracelessMatrix 2 := by
  simp only [TracelessMatrix, LinearMap.mem_ker, traceMap, Matrix.traceLinearMap_apply]
  simp [e01, Matrix.trace_fin_two]

/-- **The sl₃ and sl₂ images do not commute**: the blocks share row and
    column 2. Witness: [su3(E₀₂), su2(diag(1,−1))] has (0,2)-entry 1.
    In su(3)⊕su(2) the factors commute; any Lie-algebra embedding must
    preserve that, so no embedding of the direct sum sends the factors
    to these two blocks. -/
theorem su3_su2_images_not_commuting :
    su3EmbedFn e02 * su2EmbedFn d2 ≠ su2EmbedFn d2 * su3EmbedFn e02 := by
  intro h
  have h02 := congr_fun (congr_fun h 0) 2
  norm_num [su3EmbedFn, su2EmbedFn, e02, d2, Matrix.mul_apply,
    Fin.sum_univ_four] at h02

/-- **The sl₂ image does not commute with the u(1) image**: "hypercharge"
    fails to commute with "weak isospin" in this embedding — in the
    Standard Model they commute by construction. Witness:
    [su2(E₀₁), u1(1)] has (2,3)-entry −4. -/
theorem su2_u1_images_not_commuting :
    su2EmbedFn e01 * u1EmbedFn 1 ≠ u1EmbedFn 1 * su2EmbedFn e01 := by
  intro h
  have h23 := congr_fun (congr_fun h 2) 3
  norm_num [su2EmbedFn, u1EmbedFn, e01, Matrix.mul_apply,
    Fin.sum_univ_four] at h23

/-! ## 4. What is true: colour and B−L -/

/-- **The sl₃ image commutes with the u(1) image**: on the colour block
    the u(1) generator is the scalar c, and scalars commute. This is the
    honest half — colour × B−L — and it is exactly the subalgebra
    Pati–Salam uses inside su(4). -/
theorem su3_u1_commute (A : Matrix (Fin 3) (Fin 3) ℂ) (c : ℂ) :
    su3EmbedFn A * u1EmbedFn c = u1EmbedFn c * su3EmbedFn A := by
  ext i j
  simp only [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [su3EmbedFn, u1EmbedFn, Fin.sum_univ_four] <;> ring

/-- **The colour ⊕ B−L pair assembles injectively**: (A, c) ↦ su3(A) + u1(c)
    has trivial kernel — the (3,3)-entry isolates c, and the sl₃ map is
    injective. Contrast `assembly_not_injective`. -/
theorem su3_u1_injective :
    Function.Injective (su3EmbedRestricted.coprod u1EmbedRestricted) := by
  intro p q h
  obtain ⟨A, a⟩ := p
  obtain ⟨A', a'⟩ := q
  have hval : su3EmbedFn A.val + u1EmbedFn a = su3EmbedFn A'.val + u1EmbedFn a' :=
    congrArg Subtype.val h
  have hs3 : ∀ B : Matrix (Fin 3) (Fin 3) ℂ, su3EmbedFn B 3 3 = 0 := fun B => by
    simp [su3EmbedFn]
  have hu1 : ∀ x : ℂ, u1EmbedFn x 3 3 = -(3 * x) := fun x => by
    simp [u1EmbedFn]
  have h33 := congr_fun (congr_fun hval 3) 3
  rw [Matrix.add_apply, Matrix.add_apply, hs3, hs3, hu1, hu1, zero_add,
    zero_add] at h33
  have hc : a = a' :=
    mul_left_cancel₀ (by norm_num : (3 : ℂ) ≠ 0) (neg_injective h33)
  subst hc
  have hA : A = A' := by
    apply Subtype.ext
    apply su3Embed_injective
    exact add_right_cancel hval
  rw [hA]

/-- **Colour ⊕ B−L is a genuine 9-dimensional subspace of sl₄**:
    8 + 1 = 9, now as the dimension of an actual range, not abstract
    arithmetic. -/
theorem colour_bl_finrank :
    finrank ℂ (LinearMap.range (su3EmbedRestricted.coprod u1EmbedRestricted)) = 9 := by
  rw [LinearMap.finrank_range_of_inj su3_u1_injective, Module.finrank_prod,
    traceless_dim_3, Module.finrank_self]

/-- **The honest leptoquark count is 6**: dim sl₄ − dim(colour ⊕ B−L) =
    15 − 9 = 6, the dimension of the Pati–Salam coset su(4)/(su(3)⊕u(1)).
    The estate's "3 extra generators" came from the broken 15 − 12
    arithmetic; the physical count of leptoquark directions in SU(4) is
    six. -/
theorem leptoquark_six :
    finrank ℂ (TracelessMatrix 4)
      - finrank ℂ (LinearMap.range (su3EmbedRestricted.coprod u1EmbedRestricted)) = 6 := by
  rw [colour_bl_finrank, traceless_dim_4]

/-! ## 5. The package -/

/-- **The corrected embedding statement.** The three-factor assembly is
    not injective and its factor images do not pairwise commute (two
    machine-checked witnesses), so su(3)⊕su(2)⊕u(1) does NOT embed in
    sl₄ via these maps — while colour ⊕ B−L genuinely does, commuting,
    injectively, spanning 9 of the 15 dimensions. -/
theorem sm_assembly_corrected :
    (¬ Function.Injective assembly)
      ∧ su3EmbedFn e02 * su2EmbedFn d2 ≠ su2EmbedFn d2 * su3EmbedFn e02
      ∧ su2EmbedFn e01 * u1EmbedFn 1 ≠ u1EmbedFn 1 * su2EmbedFn e01
      ∧ Function.Injective (su3EmbedRestricted.coprod u1EmbedRestricted)
      ∧ ∀ (A : Matrix (Fin 3) (Fin 3) ℂ) (c : ℂ),
          su3EmbedFn A * u1EmbedFn c = u1EmbedFn c * su3EmbedFn A :=
  ⟨assembly_not_injective, su3_su2_images_not_commuting,
    su2_u1_images_not_commuting, su3_u1_injective, su3_u1_commute⟩

end SMEmbeddingHonest
