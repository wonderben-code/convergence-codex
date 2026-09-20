/-
  ColourTriplet.lean — the colour triplet is THREE-dimensional and irreducible
  AS A SUBSPACE OF THE 4, and the estate's two colour embeddings are the same
  matrix.

  **SPINE link L13 (colour 4 → 3 ⊕ 1) — SPINE CAMPAIGN unit 8.**
  **Written in answer to a refutation of my own table.** The recompute's L13
  refuter corrected the audit's rating from GENUINE down to PARTIAL, and it was
  right. Its two material findings:

  > (a) THE TRIPLET'S DIMENSION IS NOWHERE STATED. `grep -n "finrank" ColourEquivariance.lean`
  > returns only `leptonSub_finrank` — there is no `quarkSub_finrank`, and no
  > `finrank ℂ (Col → ℂ) = 4` either, so nothing in the file says `quarkSub` is
  > three-dimensional … This asymmetry is the estate's own standard turned against
  > it: `leptonSub_finrank` exists precisely because adversarial review round 3
  > judged that *the singlet is a line* needed a finrank theorem rather than a
  > definition a reader can see. The same demand on the "3" is unmet.
  >
  > (b) IRREDUCIBILITY IS ABOUT A DIFFERENT MODULE. `quark_irreducible` is about
  > the raw action on `ℂ³`, not about `emb`-invariant submodules of
  > `quarkSub ⊆ (Col → ℂ)`; the file's own header says the identification
  > `ℂ³ ≅ quarkSub` "is NOT formalised here". Reading one as the other is exactly
  > the comparison `ERRATUM 316`'s discipline forbids.

  Both are now theorems, and the identification the header declined is built.

  ## What is proved

  1. **`quarkEquiv : quarkSub ≃ₗ[ℂ] (Fin 3 → ℂ)`** — the identification
     `ColourEquivariance`'s header §7 says is *"NOT formalised here"*: restrict a
     vector of the 4 that vanishes on the lepton index to its three colour
     coordinates. **`quarkEquiv_equivariant`** — it INTERTWINES the two actions:
     `quarkEquiv (emb X *ᵥ v) = X *ᵥ quarkEquiv v`. So `quarkSub` with `emb` and
     `ℂ³` with the raw action are the same representation, which is what reading
     one theorem as the other needed and did not have.
  2. **`quarkSub_finrank : finrank ℂ quarkSub = 3`** — the headline's own "3",
     which no file stated. **`col_finrank : finrank ℂ (Col → ℂ) = 4`** and
     **`quark_add_lepton_finrank`** — `3 + 1 = 4` as the dimensions of two
     complementary SUBSPACES of one space, not as an arithmetic identity between
     three unrelated spaces (which is what `RepDecomposition`'s
     `colour_lepton_dim_sum` is, as the refuter also found).
  3. **`quarkSub_irreducible`** — **irreducibility inside the 4**: every non-zero
     `emb`-invariant submodule `W ≤ quarkSub` is `quarkSub` itself. Transported
     from `quark_irreducible` through `quarkEquiv`, which is why the equivalence
     had to be equivariant.
  4. **`emb_reindex : (emb X).reindex finSumFinEquiv finSumFinEquiv = su3EmbedFn X`**
     — the estate's TWO colour embeddings are one matrix. `ColourEquivariance`
     works on `Col = Fin 3 ⊕ Fin 1`; `LieAlgebraEmbedding`, `SMLieHom`,
     `ColourCommutant` and `RepDecomposition` work on `Fin 4`. Nothing related
     them, so every equivariance statement here and every commutant statement
     there were about different objects. **`emb_bracket_su3Embed`** carries the
     bracket law across.

  ## What is NOT proved, said exactly

  - **The cascade identification.** `Col` and `Fin 4` are index types; that the
    cascade's `ℂ⁴` IS the `SU(4)` fundamental, and that indices `0,1,2` are quark
    colours while `3` is the lepton, are physical readings with no theorem
    (`ASSUMPTIONS_LEDGER` 30). The refuter's finding that
    `grep -rn "Submodule ℂ (Fin 4 → ℂ)"` returns NO hits in the estate stands:
    this file adds submodules of `Col → ℂ`, and `emb_reindex` relates the
    OPERATORS on the two index types, not the submodules. Transporting `quarkSub`
    along `finSumFinEquiv` into a submodule of `Fin 4 → ℂ` is one `Submodule.map`
    away and is named here, not done.
    ⚠ **DONE 2026-09-20 (unit 148), KEPT AS WRITTEN PER `ERRATUM 94`:**
    `ColourCascadeSubmodule.lean` transports both submodules — `quarkSub4`,
    `leptonSub4 : Submodule ℂ (Fin 4 → ℂ)` and `quarkSubCascade : Submodule ℂ
    CascadeHilbert` — with `finrank 3` / `1`, `su3EmbedFn`-invariance, the singlet
    annihilated, irreducibility inside the 4 and `IsCompl`; that grep now returns
    declarations. The cascade IDENTIFICATION (the next bullet's point) is
    unchanged by it.
  - **No group.** `su(3)` means `sl₃(ℂ)` throughout, as everywhere in this estate;
    no `SU(3)`, no exponential map. The irreducibility is under the traceless
    matrices, which is the Lie-algebra statement.
  - **The singlet's triviality is unchanged** (`lepton_trivial`, already there),
    and so is the `B−L` charge pair `+1`/`−3` (`charge_quark`, `charge_lepton`).
  - **Nothing about `3̄`.** That a faithful four-dimensional `sl₃`-representation
    must be `3 ⊕ 1` or `3̄ ⊕ 1` — the classification step `SMEmbeddingHonest` and
    `ColourCommutant` both name as absent — is not proved. This file says the
    estate's `emb` IS `3 ⊕ 1`; it does not say every faithful action is.

  ## Adversarial review, folded in

  **"`quarkSub_finrank` is a consequence of a linear equivalence, so it is
  bookkeeping."** It is, and that is the point: `leptonSub_finrank` is bookkeeping
  too and the estate demanded it anyway, because a dimension a reader can see is
  not a dimension the kernel has checked. The asymmetry between the two was the
  refutation.

  **"`emb_reindex` is `rfl` up to `decide`."** It is neither: `emb` is a
  `fromBlocks` on `Fin 3 ⊕ Fin 1` and `su3EmbedFn` is an `if i.val < 3 ∧ j.val < 3`
  on `Fin 4`, and the proof has to go through `finSumFinEquiv`'s `Fin.addCases`
  both ways. What is true is that it is short — which is the finding, since
  nothing in the estate had written it and two whole files were therefore about
  different matrices.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import ColourEquivariance
import LieAlgebraEmbedding

namespace ColourTriplet

open Matrix ColourEquivariance

/-! ## 1. The equivariant identification `quarkSub ≃ ℂ³` -/

/-- The colour triplet as a subspace of the 4 IS `ℂ³`: restrict to the three
colour coordinates. This is the identification `ColourEquivariance`'s header §7
records as not formalised. -/
def quarkEquiv : quarkSub ≃ₗ[ℂ] (Fin 3 → ℂ) where
  toFun v i := (v : Col → ℂ) (Sum.inl i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w := ⟨Sum.elim w 0, rfl⟩
  left_inv v := by
    ext z
    rcases z with i | j
    · rfl
    · have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      exact ((mem_quarkSub).mp v.2).symm
  right_inv w := rfl

@[simp] theorem quarkEquiv_apply (v : quarkSub) (i : Fin 3) :
    quarkEquiv v i = (v : Col → ℂ) (Sum.inl i) := rfl

@[simp] theorem quarkEquiv_symm_apply (w : Fin 3 → ℂ) :
    ((quarkEquiv.symm w : quarkSub) : Col → ℂ) = Sum.elim w 0 := rfl

/-- **THE IDENTIFICATION IS EQUIVARIANT.** `emb X` on `quarkSub` is `X` on `ℂ³`.
Without this, `quark_irreducible` (about `ℂ³`) and any statement about `quarkSub`
are statements about different representations. -/
theorem quarkEquiv_equivariant (X : Matrix (Fin 3) (Fin 3) ℂ) (v : quarkSub) :
    quarkEquiv ⟨emb X *ᵥ (v : Col → ℂ), quark_invariant X v.2⟩
      = X *ᵥ quarkEquiv v := by
  funext i
  simp only [quarkEquiv_apply]
  rw [emb, Matrix.mulVec, Matrix.mulVec]
  simp only [dotProduct]
  rw [Fintype.sum_sum_type]
  simp [Matrix.fromBlocks_apply₁₂]

/-! ## 2. The dimensions: the headline's own "3" -/

theorem col_finrank : Module.finrank ℂ (Col → ℂ) = 4 := by
  rw [Module.finrank_pi]
  simp

/-- **THE TRIPLET IS THREE-DIMENSIONAL.** The headline's `3`, which no file
stated: `ColourEquivariance` proved `leptonSub_finrank = 1` and left this. -/
theorem quarkSub_finrank : Module.finrank ℂ quarkSub = 3 := by
  have h := quarkEquiv.finrank_eq
  rw [h, Module.finrank_pi]
  simp

/-- `3 + 1 = 4` as the dimensions of two COMPLEMENTARY SUBSPACES of one space —
not an arithmetic identity between three unrelated spaces. -/
theorem quark_add_lepton_finrank :
    Module.finrank ℂ quarkSub + Module.finrank ℂ leptonSub
      = Module.finrank ℂ (Col → ℂ) := by
  rw [quarkSub_finrank, leptonSub_finrank, col_finrank]

/-! ## 3. Irreducibility inside the 4 -/

/-- **THE TRIPLET IS IRREDUCIBLE AS A SUBSPACE OF THE 4.** Every non-zero
submodule of `quarkSub` invariant under `emb X` for every traceless `X` is
`quarkSub` itself. Transported from `quark_irreducible` (which is about `ℂ³`)
through the equivariant `quarkEquiv`. -/
theorem quarkSub_irreducible (W : Submodule ℂ (Col → ℂ)) (hle : W ≤ quarkSub)
    (hne : W ≠ ⊥)
    (hinv : ∀ X : Matrix (Fin 3) (Fin 3) ℂ, X.trace = 0 →
      ∀ v ∈ W, emb X *ᵥ v ∈ W) :
    W = quarkSub := by
  -- push `W` into `ℂ³`
  set W' : Submodule ℂ (Fin 3 → ℂ) :=
    (W.comap quarkSub.subtype).map (quarkEquiv : quarkSub →ₗ[ℂ] (Fin 3 → ℂ))
    with hW'
  have hmem : ∀ w : Fin 3 → ℂ, w ∈ W' ↔ (Sum.elim w 0 : Col → ℂ) ∈ W := by
    intro w
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : (v : Col → ℂ) ∈ W := hv
      have hcast : (Sum.elim ((quarkEquiv : quarkSub →ₗ[ℂ] (Fin 3 → ℂ)) v) 0 : Col → ℂ)
          = (v : Col → ℂ) := by
        funext z
        rcases z with i | j
        · rfl
        · have hj : j = 0 := Subsingleton.elim j 0
          subst hj
          exact ((mem_quarkSub).mp v.2).symm
      rw [hcast]
      exact hv'
    · intro hw
      exact ⟨quarkEquiv.symm w, hw, quarkEquiv.apply_symm_apply w⟩
  -- `W'` is nonzero and invariant, so it is everything
  have hne' : W' ≠ ⊥ := by
    obtain ⟨v, hvW, hv0⟩ := (Submodule.ne_bot_iff W).mp hne
    refine (Submodule.ne_bot_iff W').mpr ⟨quarkEquiv ⟨v, hle hvW⟩, ?_, ?_⟩
    · exact ⟨⟨v, hle hvW⟩, hvW, rfl⟩
    · intro h
      apply hv0
      funext z
      rcases z with i | j
      · exact congrFun h i
      · have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        exact (mem_quarkSub).mp (hle hvW)
  have hinv' : ∀ X : Matrix (Fin 3) (Fin 3) ℂ, X.trace = 0 →
      ∀ w ∈ W', X *ᵥ w ∈ W' := by
    intro X hX w hw
    rw [hmem] at hw ⊢
    have hsub : (Sum.elim w 0 : Col → ℂ) ∈ quarkSub := rfl
    have hkey := hinv X hX _ hw
    have : (Sum.elim (X *ᵥ w) 0 : Col → ℂ) = emb X *ᵥ (Sum.elim w 0 : Col → ℂ) := by
      have hq := quarkEquiv_equivariant X ⟨Sum.elim w 0, hsub⟩
      funext z
      rcases z with i | j
      · have := congrFun hq i
        simpa using this.symm
      · have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        have hz : (emb X *ᵥ (Sum.elim w 0 : Col → ℂ)) (Sum.inr 0) = 0 :=
          quark_invariant X hsub
        simp [hz]
    rw [this]
    exact hkey
  have htop : W' = ⊤ := quark_irreducible W' hne' hinv'
  -- and so `W` is all of `quarkSub`
  refine le_antisymm hle fun v hv => ?_
  have hw : quarkEquiv ⟨v, hv⟩ ∈ W' := htop ▸ Submodule.mem_top
  rw [hmem] at hw
  have hvv : (Sum.elim (quarkEquiv ⟨v, hv⟩) 0 : Col → ℂ) = v := by
    funext z
    rcases z with i | j
    · rfl
    · have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      exact ((mem_quarkSub).mp hv).symm
  rwa [hvv] at hw

/-! ## 4. The estate's two colour embeddings are one matrix -/

/-- **THE BRIDGE.** `ColourEquivariance.emb` on `Fin 3 ⊕ Fin 1` and
`LieAlgebraEmbedding.su3EmbedFn` on `Fin 4` are the same matrix, reindexed.
Until this, every equivariance theorem here and every commutant theorem in
`ColourCommutant` were about different objects. -/
theorem emb_reindex (X : Matrix (Fin 3) (Fin 3) ℂ) :
    (emb X).reindex finSumFinEquiv finSumFinEquiv = su3EmbedFn X := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, su3EmbedFn,
    Matrix.of_apply]
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
    simp only [finSumFinEquiv, Equiv.coe_fn_symm_mk, Fin.addCases_left,
      Fin.addCases_right, emb, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  · rw [dif_pos ⟨a.isLt, b.isLt⟩]
    congr 1
  · have : ¬ ((Fin.castAdd 1 a).val < 3 ∧ (Fin.natAdd 3 b).val < 3) := by
      simp [Fin.natAdd]
    rw [dif_neg this]
    rfl
  · have : ¬ ((Fin.natAdd 3 a).val < 3 ∧ (Fin.castAdd 1 b).val < 3) := by
      simp [Fin.natAdd]
    rw [dif_neg this]
    rfl
  · have : ¬ ((Fin.natAdd 3 a).val < 3 ∧ (Fin.natAdd 3 b).val < 3) := by
      simp [Fin.natAdd]
    rw [dif_neg this]
    rfl

/-- The bracket law carried across the bridge. -/
theorem emb_bracket_su3Embed (X Y : Matrix (Fin 3) (Fin 3) ℂ) :
    su3EmbedFn (X * Y - Y * X) = su3EmbedFn X * su3EmbedFn Y
      - su3EmbedFn Y * su3EmbedFn X := by
  rw [← emb_reindex, ← emb_reindex, ← emb_reindex, emb_bracket]
  simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.submatrix_sub]

end ColourTriplet
