/-
  PatiSalamLieModule: the whole Pati–Salam action on the chiral 16 as ONE Mathlib Lie module —
  over `gl₄ × gl₂ × gl₂`, over `sl₄ × sl₂ × sl₂` faithfully (the kernel on the full product is
  the line `ℂ · (1, −1, 1)`), and over the Standard-Model algebra through its embedding — where
  the estate's embedding turns out to miss the hypercharge, and the corrected one carries it

  Campaign 3 hardening unit 190 (20 September 2026). Spine links L16 (anomaly cancellation),
  L10 (gauge algebra embedding) and L17 (Weinberg angle).

  WHY. Three headers and one register row say one thing in four ways. `SPINE` L16's row: *"No
  group, no `LieModule` packaging."* `PatiSalamOnSixteen`: *"`LieModule` packaging of `psRep`
  (one definition away, unconsumed, as in `SU4OnSixteen`)."* `SU4OnSixteen`: *"It does not
  build a `LieModule`."* `PatiSalamTraceForm`, which DID build three — one per factor, as
  `local instance`s, on 14 September — explains why they are not one: *"the two
  `LieRingModule (Matrix (Fin 2) (Fin 2) ℂ) (PSIndex → ℂ)` instances are a genuine diamond"*,
  and names three type synonyms as the honest refactor. The diamond is real and the refactor
  is not needed: the product algebra `gl₄ × gl₂ × gl₂` is a different TYPE, and on it `psRep`
  is one Lie homomorphism with one global instance. That is the packaging. Then two consumers
  the packaging makes possible: Mathlib's `LieModule.traceForm` on the product, and — through
  `SMInPatiSalam`'s embedding — the 16 as a module over the Standard-Model algebra, which is
  where this unit's second finding lives, in (5).

  WHAT IS PROVED.
  (1) `psLieHom : glPS →ₗ⁅ℂ⁆ Matrix PSIndex PSIndex ℂ` with `toFun = psRep` (`psRep_add`,
      `psRep_smul` from the three factor `LieHom`s, `map_lie'` from `psRep_bracket`); `psEnd`
      through `PatiSalamTraceForm.matEnd`; **global instances `LieRingModule glPS (PSIndex → ℂ)`
      and `LieModule ℂ glPS (PSIndex → ℂ)`** (`LieRingModule.compLieHom`), and
      `⁅g, v⁆ = psRep g *ᵥ v` by `rfl` (`lie_eq_mulVec`).
  (2) `traceForm_eq_trace` and **`traceForm_orthogonal_sum`**: Mathlib's
      `LieModule.traceForm ℂ glPS (PSIndex → ℂ) (X, A, B) (Y, A', B') = 4·Tr(XY) + 4·Tr(AA')
      + 4·Tr(BB')` for traceless `X, Y` — `PatiSalamOrthogonal`'s orthogonal sum AS the value of
      one invariant form on one algebra (`traceForm_invariant`, `traceForm_symm`: Mathlib's
      theorems, applied).
  (3) **`psRep_eq_zero_iff`**: on the full product `psRep (X, A, B) = 0 ↔ ∃ c, X = c • 1 ∧
      A = −(c • 1) ∧ B = c • 1` — the kernel is the line `ℂ · (1, −1, 1)`, computed entrywise
      (`kron_one_add_one_kron_eq_zero`); with `Tr X = 0` it is zero
      (`psRep_eq_zero_of_traceless`).
  (4) `psIncl : PS →ₗ⁅ℂ⁆ glPS` (`LieHom.prodMap` of the three `LieSubalgebra.incl`s), the
      instances over `PS = sl₄ × sl₂ × sl₂`, and **`instIsFaithfulPS : LieModule.IsFaithful ℂ PS
      (PSIndex → ℂ)`** — the 16 is a faithful Pati–Salam module. `traceForm_PS` is the
      orthogonal sum with no tracelessness hypothesis left to state.
  (5) THE HYPERCHARGE. **`hypercharge_not_mem_range_smToPS`: no `x : SM` has
      `psIncl (smToPS x) = (½ B₄, 0, T₃)`.** The `u(1)` line of `SMInPatiSalam.smToPS` is
      `((3/2)(B−L), 0, T₃ᴿ)`, not `Y`'s `(½(B−L), 0, T₃ᴿ)`: the `T₃ᴿ` component forces `c = 1`,
      and then the `(3,3)` entry of the `sl₄` component is `−3/2` where `½ B₄`'s is `−1/2`.
      `ERRATUM 552` recorded the scalar as *"the DIRECTION is right, the SCALAR is not"*; a
      factor on ONE of two components moves the line, so the direction is not right, and the
      embedded algebra is a different 12-dimensional subalgebra of `PS` from the one the 16's
      charges select (`ERRATUM 679`). **`smToPSY`** — `colourBLY` with `u1EmbedFn (c/6) =
      (c/2) • (B−L)`, then `isoL` and `t3RHom` unchanged — is injective (`smToPSY_injective`)
      and has the hypercharge: **`smToPSY_u1_eq_hypercharge : psIncl (smToPSY (0, 0, 1)) =
      (½ B₄, 0, T₃)`**, so on the 16 `⁅(0, 0, 1), v⁆ = Yc *ᵥ v` (`lie_u1_eq_Y`, off
      `Y_eq_psRep`) and `⁅(0, T₃ᴿ, 0), v⁆ = T3Lc *ᵥ v` (`lie_t3L_eq_T3L`). Instances over `SM`
      through `smToPSY`, **faithful** (`instIsFaithfulSM`).
  (6) **THE WEINBERG RATIO AS A RATIO OF VALUES OF ONE INVARIANT FORM ON THE STANDARD-MODEL
      ALGEBRA**: `traceForm_SM_t3L = 2`, `traceForm_SM_u1 = 10/3`, `traceForm_SM_t3L_u1 = 0`,
      `weinberg_ratio_traceForm : … = 3/5`; `traceForm_SM_colour = 4 · Tr(AB)` (colour index 4,
      through `su3EmbedFn_mul` and `su3Embed_trace`); `traceForm_SM_invariant`. The numbers are
      `HyperchargeInPatiSalam`'s; what is new is that `T₃L` and `Y` are elements of ONE Lie
      algebra (`ℂ` is its `u(1)` factor) and the form is ONE `LieModule.traceForm`, which is
      what `PatiSalamTraceForm`'s abelian bullet said needed *"the `u(1)` factor as a Lie
      algebra"*.

  NOT PROVED, said exactly.
  • No decomposition of the 16 into irreducibles over `PS` or `SM`: no `LieSubmodule` is
    exhibited, `LieModule.IsIrreducible` is not claimed (over `PS` it is false — the two blocks
    of `PSIndex` are invariant), and quarks and leptons as `SM`-submodules are not written.
  • No group, no exponential of these representations, no `LieGroup`.
  • The ratio `2 : 10/3` is not `sin²θ_W`: the coupling matching is `ASSUMPTIONS_LEDGER` 57,
    under DECISIONS NEEDED, untouched.
  • `smToPS` is kept as it was: the theorem separating it from `smToPSY` is here, its header is
    annotated, and whether to retire it is the author's (DECISIONS NEEDED). No second module
    structure over `SM` is built from it — that would be the diamond.
  • Over `ℂ` throughout; no compact real form.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `traceForm_orthogonal_sum` takes
  `X.trace = 0` and `Y.trace = 0`; `psRep_eq_zero_of_traceless` takes `X.trace = 0`;
  `kron_one_add_one_kron_eq_zero` takes its equation. `psRep_eq_zero_iff`, `traceForm_PS`, the
  `SM` theorems and every instance are hypothesis-free — elements of the subtypes carry their
  own tracelessness (`sl4_trace`).

  QUERIED BEFORE WRITING. `grep -rn 'instance.*LieRingModule\|instance.*LieModule ℂ' paper_f`
  → 6 lines, all `local instance` in `PatiSalamTraceForm`, none global, none over a product;
  `IsFaithful` → 1 file (`PatiSalamTraceForm`, in prose: *"not claimed"*); `compLieHom` →
  1 file; `LieHom.prodMap` → 0 files; `smToPS` outside its own file → 3 prose lines in 2 files
  (`HyperchargeInPatiSalam` 21 and 119, `PatiSalamOrthogonal` 63) and no Lean consumer, so
  `smToPSY` breaks nothing; `SMInPatiSalam`'s *frame* sentences at its lines 29, 54 and 233.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`: the 55 names run against `paper_f`
  by word search — none taken after one rename: the bare `instLieRingModule` is Mathlib's
  `Module.End.instLieRingModule`, quoted in `PatiSalamTraceForm`'s prose, so the product
  instances carry the suffix `Gl`). `PatiSalamTraceForm`'s six local instances are per-factor
  on the matrix algebras; the three global ones here are on `glPS`, `PS` and `SM`, different
  types. `smToPSY` differs from `smToPS` in one scalar, `1/6` for `1/2`, and that is the point.
-/

import HyperchargeInPatiSalam
import PatiSalamTraceForm
import SMInPatiSalam

open Matrix LieAlgebra.SpecialLinear WeinbergIndex SU4OnSixteen PatiSalamOnSixteen
  PatiSalamOrthogonal PatiSalamTraceForm HyperchargeInPatiSalam SMInPatiSalam
  SMEmbeddingHonest SMLieHom
open scoped Kronecker

namespace PatiSalamLieModule

noncomputable section

/-- `gl₄ × gl₂ × gl₂`, the product Lie algebra `psRep` is defined on. -/
abbrev glPS := Matrix (Fin 4) (Fin 4) ℂ × Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ

/-! ## 1. `psRep` as one Lie algebra homomorphism -/

theorem psRep_add (g h : glPS) : psRep (g + h) = psRep g + psRep h := by
  obtain ⟨X, A, B⟩ := g
  obtain ⟨Y, A', B'⟩ := h
  have h1 : su4Rep (X + Y) = su4Rep X + su4Rep Y := map_add su4LieHom X Y
  have h2 : su2LRep (A + A') = su2LRep A + su2LRep A' := map_add su2LLieHom A A'
  have h3 : su2RRep (B + B') = su2RRep B + su2RRep B' := map_add su2RLieHom B B'
  change su4Rep (X + Y) + su2LRep (A + A') + su2RRep (B + B')
    = (su4Rep X + su2LRep A + su2RRep B) + (su4Rep Y + su2LRep A' + su2RRep B')
  rw [h1, h2, h3]
  abel

theorem psRep_smul (c : ℂ) (g : glPS) : psRep (c • g) = c • psRep g := by
  obtain ⟨X, A, B⟩ := g
  have h1 : su4Rep (c • X) = c • su4Rep X := map_smul su4LieHom c X
  have h2 : su2LRep (c • A) = c • su2LRep A := map_smul su2LLieHom c A
  have h3 : su2RRep (c • B) = c • su2RRep B := map_smul su2RLieHom c B
  change su4Rep (c • X) + su2LRep (c • A) + su2RRep (c • B)
    = c • (su4Rep X + su2LRep A + su2RRep B)
  rw [h1, h2, h3, smul_add, smul_add]

/-- **THE PATI–SALAM ACTION AS ONE LIE HOMOMORPHISM** from the product algebra. -/
def psLieHom : glPS →ₗ⁅ℂ⁆ Matrix PSIndex PSIndex ℂ where
  toFun := psRep
  map_add' := psRep_add
  map_smul' := psRep_smul
  map_lie' {g h} := by
    obtain ⟨X, A, B⟩ := g
    obtain ⟨Y, A', B'⟩ := h
    exact psRep_bracket X Y A A' B B'

theorem psLieHom_apply (g : glPS) : psLieHom g = psRep g := rfl

/-- The product algebra acting on the 16, through `PatiSalamTraceForm.matEnd`. -/
def psEnd : glPS →ₗ⁅ℂ⁆ Module.End ℂ (PSIndex → ℂ) := matEnd.comp psLieHom

theorem psEnd_apply (g : glPS) : psEnd g = Matrix.toLin' (psRep g) := rfl

/-- **THE 16 AS A LIE MODULE OVER `gl₄ × gl₂ × gl₂`.** -/
instance instLieRingModuleGl : LieRingModule glPS (PSIndex → ℂ) :=
  LieRingModule.compLieHom _ psEnd

instance instLieModuleGl : LieModule ℂ glPS (PSIndex → ℂ) :=
  LieModule.compLieHom _ psEnd

theorem lie_eq_mulVec (g : glPS) (v : PSIndex → ℂ) : ⁅g, v⁆ = (psRep g).mulVec v := rfl

theorem toEnd_eq_psEnd (g : glPS) :
    LieModule.toEnd ℂ glPS (PSIndex → ℂ) g = psEnd g :=
  LinearMap.ext fun v => LieRingModule.compLieHom_apply (PSIndex → ℂ) psEnd g v

/-! ## 2. The trace form of the product action -/

theorem traceForm_eq_trace (g h : glPS) :
    LieModule.traceForm ℂ glPS (PSIndex → ℂ) g h = (psRep g * psRep h).trace := by
  rw [LieModule.traceForm_apply_apply, toEnd_eq_psEnd, toEnd_eq_psEnd, psEnd_apply, psEnd_apply,
    ← Matrix.toLin'_mul, trace_toLin']

theorem traceForm_orthogonal_sum (X Y : Matrix (Fin 4) (Fin 4) ℂ)
    (A A' B B' : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.trace = 0) (hY : Y.trace = 0) :
    LieModule.traceForm ℂ glPS (PSIndex → ℂ) (X, A, B) (Y, A', B')
      = 4 * (X * Y).trace + 4 * (A * A').trace + 4 * (B * B').trace := by
  rw [traceForm_eq_trace, psRep_trace_orthogonal_sum X Y A A' B B' hX hY]

theorem traceForm_invariant (g : glPS) :
    ⁅g, LieModule.traceForm ℂ glPS (PSIndex → ℂ)⁆ = 0 :=
  LieModule.lie_traceForm_eq_zero ℂ glPS (PSIndex → ℂ) g

theorem traceForm_symm : LinearMap.IsSymm (LieModule.traceForm ℂ glPS (PSIndex → ℂ)) :=
  LieModule.traceForm_isSymm ℂ glPS (PSIndex → ℂ)

/-! ## 3. The kernel: the line `ℂ · (1, −1, 1)` on `gl`, zero on `sl` -/

theorem kron_one_add_one_kron_eq_zero
    (X : Matrix (Fin 4) (Fin 4) ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (h : X ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ A = 0) :
    X = X 0 0 • 1 ∧ A = -(X 0 0 • 1) := by
  have h00 : ∀ i : Fin 4, ∀ k : Fin 2, X i i + A k k = 0 := by
    intro i k
    have := congrFun (congrFun h (i, k)) (i, k)
    simpa [kroneckerMap_apply] using this
  have hX : ∀ i j : Fin 4, i ≠ j → X i j = 0 := by
    intro i j hij
    have := congrFun (congrFun h (i, 0)) (j, 0)
    simpa [kroneckerMap_apply, Matrix.one_apply, hij] using this
  have hA : ∀ k l : Fin 2, k ≠ l → A k l = 0 := by
    intro k l hkl
    have := congrFun (congrFun h (0, k)) (0, l)
    simpa [kroneckerMap_apply, Matrix.one_apply, hkl] using this
  refine ⟨?_, ?_⟩
  · ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      linear_combination h00 i 0 - h00 0 0
    · simp [hij, hX i j hij]
  · ext k l
    by_cases hkl : k = l
    · subst hkl
      simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      linear_combination h00 0 k
    · simp [hkl, hA k l hkl]

/-- **THE KERNEL OF `psRep` ON `gl₄ × gl₂ × gl₂` IS THE LINE `ℂ · (1, −1, 1)`.** -/
theorem psRep_eq_zero_iff (X : Matrix (Fin 4) (Fin 4) ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    psRep (X, A, B) = 0 ↔ ∃ c : ℂ, X = c • 1 ∧ A = -(c • 1) ∧ B = c • 1 := by
  constructor
  · intro h
    rw [psRep_eq, ← fromBlocks_zero, fromBlocks_inj] at h
    obtain ⟨h1, -, -, h2⟩ := h
    obtain ⟨hX, hA⟩ := kron_one_add_one_kron_eq_zero X A h1
    obtain ⟨-, hB⟩ := kron_one_add_one_kron_eq_zero (-Xᵀ) B h2
    refine ⟨X 0 0, hX, hA, ?_⟩
    rw [hB]
    have e0 : (-Xᵀ) 0 0 = -(X 0 0) := rfl
    rw [e0]
    ext i j
    simp
  · rintro ⟨c, rfl, rfl, rfl⟩
    rw [psRep_eq]
    have e1 : (c • (1 : Matrix (Fin 4) (Fin 4) ℂ)) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ (-(c • (1 : Matrix (Fin 2) (Fin 2) ℂ))) = 0 := by
      ext ⟨i, k⟩ ⟨j, l⟩
      simp [kroneckerMap_apply, Matrix.one_apply]
    have e2 : (-(c • (1 : Matrix (Fin 4) (Fin 4) ℂ))ᵀ) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ (c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
      ext ⟨i, k⟩ ⟨j, l⟩
      simp [kroneckerMap_apply, Matrix.one_apply]
      split_ifs <;> ring
    rw [e1, e2, fromBlocks_zero]

/-- On a traceless `sl₄` component the kernel is zero. -/
theorem psRep_eq_zero_of_traceless (X : Matrix (Fin 4) (Fin 4) ℂ)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.trace = 0) (h : psRep (X, A, B) = 0) :
    X = 0 ∧ A = 0 ∧ B = 0 := by
  obtain ⟨c, rfl, rfl, rfl⟩ := (psRep_eq_zero_iff X A B).mp h
  have hc : c = 0 := by
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin] at hX
    simpa using hX
  subst hc
  simp

/-! ## 4. The Pati–Salam algebra `sl₄ × sl₂ × sl₂` on the 16, faithfully -/

/-- The inclusion of the estate's Pati–Salam algebra into the product of matrix algebras. -/
def psIncl : PS →ₗ⁅ℂ⁆ glPS :=
  LieHom.prodMap (sl (Fin 4) ℂ).incl (LieHom.prodMap (sl (Fin 2) ℂ).incl (sl (Fin 2) ℂ).incl)

theorem psIncl_apply (p : PS) : psIncl p = (p.1.val, p.2.1.val, p.2.2.val) := rfl

def psEndPS : PS →ₗ⁅ℂ⁆ Module.End ℂ (PSIndex → ℂ) := psEnd.comp psIncl

theorem psEndPS_apply (p : PS) :
    psEndPS p = Matrix.toLin' (psRep (p.1.val, p.2.1.val, p.2.2.val)) := rfl

instance instLieRingModulePS : LieRingModule PS (PSIndex → ℂ) :=
  LieRingModule.compLieHom _ psEndPS

instance instLieModulePS : LieModule ℂ PS (PSIndex → ℂ) :=
  LieModule.compLieHom _ psEndPS

theorem toEnd_eq_psEndPS (p : PS) :
    LieModule.toEnd ℂ PS (PSIndex → ℂ) p = psEndPS p :=
  LinearMap.ext fun v => LieRingModule.compLieHom_apply (PSIndex → ℂ) psEndPS p v

theorem lie_PS_eq_mulVec (p : PS) (v : PSIndex → ℂ) :
    ⁅p, v⁆ = (psRep (p.1.val, p.2.1.val, p.2.2.val)).mulVec v := rfl

theorem sl4_trace (M : sl (Fin 4) ℂ) : (M : Matrix (Fin 4) (Fin 4) ℂ).trace = 0 := M.property

/-- **THE 16 IS A FAITHFUL MODULE OF THE PATI–SALAM ALGEBRA.** -/
instance instIsFaithfulPS : LieModule.IsFaithful ℂ PS (PSIndex → ℂ) where
  injective_toEnd := by
    intro p q h
    rw [toEnd_eq_psEndPS, toEnd_eq_psEndPS, psEndPS_apply, psEndPS_apply] at h
    have h' := Matrix.toLin'.injective h
    have h0 : psLieHom (psIncl p - psIncl q) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr h'
    rw [← map_sub] at h0
    change psRep ((p - q).1.val, (p - q).2.1.val, (p - q).2.2.val) = 0 at h0
    obtain ⟨hX, hA, hB⟩ := psRep_eq_zero_of_traceless _ _ _ (sl4_trace (p - q).1) h0
    apply sub_eq_zero.mp
    exact Prod.ext (Subtype.ext hX) (Prod.ext (Subtype.ext hA) (Subtype.ext hB))

theorem traceForm_PS (p q : PS) :
    LieModule.traceForm ℂ PS (PSIndex → ℂ) p q
      = 4 * (p.1.val * q.1.val).trace + 4 * (p.2.1.val * q.2.1.val).trace
        + 4 * (p.2.2.val * q.2.2.val).trace := by
  rw [LieModule.traceForm_apply_apply, toEnd_eq_psEndPS, toEnd_eq_psEndPS, psEndPS_apply,
    psEndPS_apply, ← Matrix.toLin'_mul, trace_toLin']
  exact psRep_trace_orthogonal_sum _ _ _ _ _ _ (sl4_trace p.1) (sl4_trace q.1)

theorem traceForm_PS_invariant (p : PS) :
    ⁅p, LieModule.traceForm ℂ PS (PSIndex → ℂ)⁆ = 0 :=
  LieModule.lie_traceForm_eq_zero ℂ PS (PSIndex → ℂ) p

/-! ## 5. The Standard-Model algebra on the 16, and where the hypercharge is -/

theorem t3R_val : (t3R : Matrix (Fin 2) (Fin 2) ℂ) = T3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [t3R, d2Sl, d2, T3, t3, Matrix.diagonal_apply]

/-- **HYPERCHARGE IS NOT IN THE RANGE OF `smToPS`.** -/
theorem hypercharge_not_mem_range_smToPS (x : SM) :
    psIncl (smToPS x) ≠ (((1 : ℂ) / 2) • B4, 0, T3) := by
  intro h
  rw [smToPS_apply, psIncl_apply] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, -, h3⟩ := h
  have hc : x.2.2 = 1 := by
    have e := congrFun (congrFun h3 0) 0
    norm_num [t3R, d2Sl, d2, T3, t3, Matrix.diagonal_apply] at e
    linear_combination e
  have e := congrFun (congrFun h1 3) 3
  change su3EmbedFn x.1.val 3 3 + u1EmbedFn ((1 / 2 : ℂ) * x.2.2) 3 3
    = (((1 : ℂ) / 2) • B4) 3 3 at e
  rw [hc] at e
  norm_num [su3EmbedFn, u1EmbedFn, B4, b4, Matrix.diagonal_apply] at e

/-- The `sl₄` component with the hypercharge scalar `c/6`, so that
`u1EmbedFn (c/6) = (c/2) • (B−L)`. -/
def colourBLY : SM →ₗ⁅ℂ⁆ sl (Fin 4) ℂ where
  toLinearMap :=
    su3EmbedRestricted ∘ₗ LinearMap.fst ℂ _ _
      + u1EmbedRestricted ∘ₗ ((1 / 6 : ℂ) • (LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _))
  map_lie' := by
    intro x y
    apply Subtype.ext
    have hc : (⁅x.2.2, y.2.2⁆ : ℂ) = 0 := by rw [Ring.lie_def]; ring
    change su3EmbedFn (⁅x.1, y.1⁆ : sl (Fin 3) ℂ).val
        + u1EmbedFn ((1 / 6 : ℂ) * ⁅x.2.2, y.2.2⁆)
      = ((⁅(⟨su3EmbedFn x.1.val + u1EmbedFn ((1 / 6 : ℂ) * x.2.2), _⟩ : sl (Fin 4) ℂ),
          (⟨su3EmbedFn y.1.val + u1EmbedFn ((1 / 6 : ℂ) * y.2.2), _⟩ : sl (Fin 4) ℂ)⁆)
            : sl (Fin 4) ℂ).val
    rw [sl_bracket, hc, mul_zero, sl_bracket]
    have h0 : u1EmbedFn 0 = 0 := map_zero u1EmbedLinear
    rw [h0, add_zero]
    exact (colour_bl_bracket x.1.val y.1.val ((1 / 6 : ℂ) * x.2.2) ((1 / 6 : ℂ) * y.2.2)).symm

/-- **THE HYPERCHARGE-NORMALISED EMBEDDING** of the Standard-Model algebra. -/
def smToPSY : SM →ₗ⁅ℂ⁆ PS := LieHom.prod colourBLY (LieHom.prod isoL t3RHom)

theorem smToPSY_apply (x : SM) : smToPSY x = (colourBLY x, x.2.1, x.2.2 • t3R) := rfl

theorem colourBLY_val (x : SM) :
    (colourBLY x : Matrix (Fin 4) (Fin 4) ℂ)
      = su3EmbedFn x.1.val + u1EmbedFn ((1 / 6 : ℂ) * x.2.2) := rfl

/-- **THE `u(1)` COORDINATE OF `smToPSY` IS THE HYPERCHARGE.** -/
theorem smToPSY_u1_eq_hypercharge :
    psIncl (smToPSY (0, 0, 1)) = (((1 : ℂ) / 2) • B4, 0, T3) := by
  rw [smToPSY_apply, psIncl_apply]
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · change su3EmbedFn (0 : sl (Fin 3) ℂ).val + u1EmbedFn ((1 / 6 : ℂ) * 1) = (1 / 2 : ℂ) • B4
    have h3 : su3EmbedFn 0 = 0 := map_zero su3EmbedLinear
    change su3EmbedFn 0 + u1EmbedFn ((1 / 6 : ℂ) * 1) = _
    rw [h3, zero_add]
    change _ = (1 / 2 : ℂ) • (Matrix.diagonal fun a => ((b4 a : ℚ) : ℂ))
    rw [bl_eq_u1Embed, ← u1EmbedFn_smul]
    congr 1
    norm_num
  · change ((1 : ℂ) • t3R : sl (Fin 2) ℂ).val = T3
    rw [one_smul]
    exact t3R_val

theorem smToPSY_iso : psIncl (smToPSY (0, t3R, 0)) = (0, T3, 0) := by
  rw [smToPSY_apply, psIncl_apply]
  refine Prod.ext ?_ (Prod.ext t3R_val ?_)
  · change su3EmbedFn (0 : sl (Fin 3) ℂ).val + u1EmbedFn ((1 / 6 : ℂ) * 0) = 0
    have h3 : su3EmbedFn 0 = 0 := map_zero su3EmbedLinear
    have h0 : u1EmbedFn 0 = 0 := map_zero u1EmbedLinear
    change su3EmbedFn 0 + u1EmbedFn ((1 / 6 : ℂ) * 0) = 0
    rw [h3, mul_zero, h0, add_zero]
  · change ((0 : ℂ) • t3R : sl (Fin 2) ℂ).val = 0
    rw [zero_smul]
    rfl

theorem smToPSY_colour (A : sl (Fin 3) ℂ) :
    psIncl (smToPSY (A, 0, 0)) = (su3EmbedFn A.val, 0, 0) := by
  rw [smToPSY_apply, psIncl_apply]
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · have h0 : u1EmbedFn 0 = 0 := map_zero u1EmbedLinear
    change su3EmbedFn A.val + u1EmbedFn ((1 / 6 : ℂ) * 0) = su3EmbedFn A.val
    rw [mul_zero, h0, add_zero]
  · change ((0 : ℂ) • t3R : sl (Fin 2) ℂ).val = 0
    rw [zero_smul]
    rfl

/-- **INJECTIVE**, by the same three steps as `smToPS_injective`. -/
theorem smToPSY_injective : Function.Injective smToPSY := by
  intro x y hxy
  rw [smToPSY_apply, smToPSY_apply] at hxy
  simp only [Prod.mk.injEq] at hxy
  obtain ⟨h1, h2, h3⟩ := hxy
  have hc : x.2.2 = y.2.2 := by
    have := sub_eq_zero.mpr h3
    rw [← sub_smul, smul_eq_zero] at this
    rcases this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h t3R_ne_zero
  have hA : x.1 = y.1 := by
    apply su3EmbedRestricted_injective
    apply Subtype.ext
    have h1' := congrArg Subtype.val h1
    rw [colourBLY_val, colourBLY_val, hc] at h1'
    exact add_right_cancel h1'
  exact Prod.ext hA (Prod.ext h2 hc)

/-- The Standard-Model algebra acting on the 16, through the hypercharge-normalised embedding. -/
def smEnd : SM →ₗ⁅ℂ⁆ Module.End ℂ (PSIndex → ℂ) := psEndPS.comp smToPSY

theorem smEnd_apply (x : SM) : smEnd x = Matrix.toLin' (psRep (psIncl (smToPSY x))) := rfl

instance instLieRingModuleSM : LieRingModule SM (PSIndex → ℂ) :=
  LieRingModule.compLieHom _ smEnd

instance instLieModuleSM : LieModule ℂ SM (PSIndex → ℂ) :=
  LieModule.compLieHom _ smEnd

theorem toEnd_eq_smEnd (x : SM) :
    LieModule.toEnd ℂ SM (PSIndex → ℂ) x = smEnd x :=
  LinearMap.ext fun v => LieRingModule.compLieHom_apply (PSIndex → ℂ) smEnd x v

/-- The hypercharge coordinate acts on the 16 as `WeinbergIndex`'s `Y`. -/
theorem lie_u1_eq_Y (v : PSIndex → ℂ) : ⁅((0, 0, 1) : SM), v⁆ = Yc.mulVec v := by
  change (psRep (psIncl (smToPSY (0, 0, 1)))).mulVec v = _
  rw [smToPSY_u1_eq_hypercharge, ← Y_eq_psRep]

/-- Weak isospin acts as `WeinbergIndex`'s `T₃L`. -/
theorem lie_t3L_eq_T3L (v : PSIndex → ℂ) : ⁅((0, t3R, 0) : SM), v⁆ = T3Lc.mulVec v := by
  change (psRep (psIncl (smToPSY (0, t3R, 0)))).mulVec v = _
  rw [smToPSY_iso, ← T3L_eq_psRep]

/-- **AND FAITHFUL OVER THE STANDARD-MODEL ALGEBRA**, from faithfulness over `PS` and the
injectivity of the embedding. -/
instance instIsFaithfulSM : LieModule.IsFaithful ℂ SM (PSIndex → ℂ) where
  injective_toEnd := by
    intro x y h
    rw [toEnd_eq_smEnd, toEnd_eq_smEnd] at h
    have hinj : Function.Injective (LieModule.toEnd ℂ PS (PSIndex → ℂ)) :=
      LieModule.IsFaithful.injective_toEnd
    have hps : smToPSY x = smToPSY y := by
      apply hinj
      rw [toEnd_eq_psEndPS, toEnd_eq_psEndPS]
      exact h
    exact smToPSY_injective hps

theorem traceForm_SM_eq_trace (x y : SM) :
    LieModule.traceForm ℂ SM (PSIndex → ℂ) x y
      = (psRep (psIncl (smToPSY x)) * psRep (psIncl (smToPSY y))).trace := by
  rw [LieModule.traceForm_apply_apply, toEnd_eq_smEnd, toEnd_eq_smEnd, smEnd_apply, smEnd_apply,
    ← Matrix.toLin'_mul, trace_toLin']

theorem traceForm_SM_colour (A B : sl (Fin 3) ℂ) :
    LieModule.traceForm ℂ SM (PSIndex → ℂ) (A, 0, 0) (B, 0, 0) = 4 * (A.val * B.val).trace := by
  rw [traceForm_SM_eq_trace, smToPSY_colour, smToPSY_colour]
  have hz : ∀ X : Matrix (Fin 4) (Fin 4) ℂ, psRep (X, 0, 0) = su4Rep X := by
    intro X
    have h1 : su2LRep 0 = 0 := map_zero su2LLieHom
    have h2 : su2RRep 0 = 0 := map_zero su2RLieHom
    change su4Rep X + su2LRep 0 + su2RRep 0 = su4Rep X
    rw [h1, h2, add_zero, add_zero]
  rw [hz, hz, trace_su4Rep_mul, su3EmbedFn_mul, su3Embed_trace]

theorem traceForm_SM_u1 :
    LieModule.traceForm ℂ SM (PSIndex → ℂ) (0, 0, 1) (0, 0, 1) = 10 / 3 := by
  rw [traceForm_SM_eq_trace, smToPSY_u1_eq_hypercharge, ← Y_eq_psRep, trace_Y_sq_via_form]

theorem traceForm_SM_t3L :
    LieModule.traceForm ℂ SM (PSIndex → ℂ) (0, t3R, 0) (0, t3R, 0) = 2 := by
  rw [traceForm_SM_eq_trace, smToPSY_iso, ← T3L_eq_psRep, trace_T3L_sq_via_form]

theorem traceForm_SM_t3L_u1 :
    LieModule.traceForm ℂ SM (PSIndex → ℂ) (0, t3R, 0) (0, 0, 1) = 0 := by
  rw [traceForm_SM_eq_trace, smToPSY_iso, smToPSY_u1_eq_hypercharge, ← T3L_eq_psRep,
    ← Y_eq_psRep, trace_T3L_Y_via_form]

/-- **THE WEINBERG RATIO AS A RATIO OF VALUES OF ONE INVARIANT FORM** on the Standard-Model
algebra. -/
theorem weinberg_ratio_traceForm :
    LieModule.traceForm ℂ SM (PSIndex → ℂ) (0, t3R, 0) (0, t3R, 0)
      / LieModule.traceForm ℂ SM (PSIndex → ℂ) (0, 0, 1) (0, 0, 1) = 3 / 5 := by
  rw [traceForm_SM_t3L, traceForm_SM_u1]
  norm_num

theorem traceForm_SM_invariant (x : SM) :
    ⁅x, LieModule.traceForm ℂ SM (PSIndex → ℂ)⁆ = 0 :=
  LieModule.lie_traceForm_eq_zero ℂ SM (PSIndex → ℂ) x

end

end PatiSalamLieModule
