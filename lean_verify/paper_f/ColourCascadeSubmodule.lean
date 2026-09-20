/-
  ColourCascadeSubmodule.lean — the colour triplet as a SUBMODULE OF THE CASCADE'S OWN ℂ⁴.

  SPINE link L13 (colour 4 → 3 ⊕ 1), rated GENUINE — hardening unit 148, 2026-09-20.

  WHY. L13's row in `SPINE.md` says, in its *what is not machine-checked* column: *"the estate
  still has **no submodule of the cascade's own `ℂ⁴` at all** (queried) — `emb_reindex` relates
  operators, not submodules, and the transport is one `Submodule.map` away."* `ColourTriplet`'s
  own NOT list says the same: *"Transporting `quarkSub` along `finSumFinEquiv` into a submodule of
  `Fin 4 → ℂ` is one `Submodule.map` away and is named here, not done."* This file does it. Before
  this file `grep -rn "Submodule ℂ (Fin 4 → ℂ)" paper_f` returned that prose sentence and nothing
  else; the declarations below are what it returns now.

  WHAT IS PROVED.
  * `toFour : (Col → ℂ) ≃ₗ[ℂ] (Fin 4 → ℂ)` — `finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4` applied to
    function spaces (Mathlib's `LinearEquiv.funCongrLeft`), with both directions computed.
  * `quarkSub4`, `leptonSub4 : Submodule ℂ (Fin 4 → ℂ)` — the images of
    `ColourEquivariance.quarkSub` and `leptonSub`, with membership computed:
    `w ∈ quarkSub4 ↔ w 3 = 0` and `w ∈ leptonSub4 ↔ ∀ i : Fin 3, w (Fin.castAdd 1 i) = 0`.
  * `finrank_quarkSub4 : finrank ℂ quarkSub4 = 3`, `finrank_leptonSub4 = 1`, and their sum is the
    dimension of `Fin 4 → ℂ` (`finrank_quark_add_lepton4`).
  * `su3EmbedFn_mulVec_toFour : su3EmbedFn X *ᵥ toFour v = toFour (emb X *ᵥ v)` — the two colour
    actions of the estate correspond under the transport. This is `ColourTriplet.emb_reindex` read
    on VECTORS rather than on matrices, through `Matrix.submatrix_mulVec_equiv`.
  * `quarkSub4_invariant`, `leptonSub4_trivial` — inside `Fin 4 → ℂ`, the triplet is
    `su3EmbedFn`-invariant and the singlet is annihilated.
  * `quarkSub4_irreducible` — every non-zero `su3EmbedFn`-invariant submodule of `quarkSub4` is
    `quarkSub4`: `ColourTriplet.quarkSub_irreducible` pulled back along `toFour`.
  * `isCompl_quarkSub4_leptonSub4 : IsCompl quarkSub4 leptonSub4` — transported from
    `ColourEquivariance.isCompl_quark_lepton` through `Submodule.map_inf` / `map_sup`.
  * `quarkSubCascade`, `leptonSubCascade : Submodule ℂ CascadeHilbert` with their dimensions and
    complementarity — the same objects stated on `CascadeFoundation.CascadeHilbert`, the literal
    type the L13 row said carried no submodule.

  WHAT IS **NOT** PROVED, said exactly.
  * **The cascade identification.** `CascadeHilbert` is an `abbrev` for `Fin 4 → ℂ`, so
    `quarkSubCascade` is `quarkSub4` by `rfl`. The theorem is that the object exists on the
    cascade's TYPE with the dimensions and invariances the headline states; that the cascade's
    `ℂ⁴` IS the `SU(4)` fundamental, and that coordinate `3` is the lepton, are physical readings
    with no theorem (`ASSUMPTIONS_LEDGER` 30). Nothing here narrows that entry.
  * **Nothing about `3̄`.** That every faithful four-dimensional `sl₃`-representation is `3 ⊕ 1`
    or `3̄ ⊕ 1` is as absent as `ColourTriplet` records.
  * **No group.** `su(3)` means the traceless matrices throughout, as everywhere in this estate.
  * `emb_reindex` is consumed, not re-proved; nothing here is new about the matrices.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import ColourTriplet
import CascadeFoundation

namespace ColourCascadeSubmodule

open Matrix ColourEquivariance ColourTriplet

/-! ## 1. The transport `(Col → ℂ) ≃ₗ (Fin 4 → ℂ)` -/

/-- `finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4`, with its size arguments fixed by `Col`. An
`abbrev`, so that every statement below can be read through it as `finSumFinEquiv`. -/
abbrev colFourEquiv : Col ≃ Fin 4 := finSumFinEquiv

/-- `finSumFinEquiv` on function spaces. -/
noncomputable def toFour : (Col → ℂ) ≃ₗ[ℂ] (Fin 4 → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ colFourEquiv.symm

theorem toFour_apply (v : Col → ℂ) (i : Fin 4) : toFour v i = v (finSumFinEquiv.symm i) := rfl

theorem toFour_symm_apply (w : Fin 4 → ℂ) (c : Col) :
    toFour.symm w c = w (finSumFinEquiv c) := rfl

/-- `toFour v` is `v` reindexed: precomposing with `finSumFinEquiv` gives `v` back. -/
theorem toFour_comp (v : Col → ℂ) : (toFour v ∘ finSumFinEquiv) = v := by
  funext c
  simp [toFour_apply]

/-! ## 2. The triplet and the singlet inside `Fin 4 → ℂ` -/

/-- The colour triplet, as a submodule of `Fin 4 → ℂ`. -/
noncomputable def quarkSub4 : Submodule ℂ (Fin 4 → ℂ) :=
  quarkSub.map (toFour : (Col → ℂ) →ₗ[ℂ] (Fin 4 → ℂ))

/-- The lepton singlet, as a submodule of `Fin 4 → ℂ`. -/
noncomputable def leptonSub4 : Submodule ℂ (Fin 4 → ℂ) :=
  leptonSub.map (toFour : (Col → ℂ) →ₗ[ℂ] (Fin 4 → ℂ))

theorem finSumFinEquiv_inr_zero : (@finSumFinEquiv 3 1) (Sum.inr 0) = (3 : Fin 4) := by
  decide

theorem mem_quarkSub4 {w : Fin 4 → ℂ} : w ∈ quarkSub4 ↔ w 3 = 0 := by
  rw [quarkSub4, Submodule.mem_map_equiv, mem_quarkSub, toFour_symm_apply,
    finSumFinEquiv_inr_zero]

theorem mem_leptonSub4 {w : Fin 4 → ℂ} :
    w ∈ leptonSub4 ↔ ∀ i : Fin 3, w (Fin.castAdd 1 i) = 0 := by
  rw [leptonSub4, Submodule.mem_map_equiv, mem_leptonSub]
  simp only [toFour_symm_apply, finSumFinEquiv_apply_left]

theorem finrank_quarkSub4 : Module.finrank ℂ quarkSub4 = 3 := by
  rw [quarkSub4, LinearEquiv.finrank_map_eq, quarkSub_finrank]

theorem finrank_leptonSub4 : Module.finrank ℂ leptonSub4 = 1 := by
  rw [leptonSub4, LinearEquiv.finrank_map_eq, leptonSub_finrank]

theorem finrank_quark_add_lepton4 :
    Module.finrank ℂ quarkSub4 + Module.finrank ℂ leptonSub4 = Module.finrank ℂ (Fin 4 → ℂ) := by
  rw [finrank_quarkSub4, finrank_leptonSub4]
  simp

/-! ## 3. The two colour actions correspond under the transport -/

/-- `ColourTriplet.emb_reindex`, read on vectors: `su3EmbedFn X` acting on `Fin 4 → ℂ` is `emb X`
acting on `Col → ℂ`, conjugated by `toFour`. -/
theorem su3EmbedFn_mulVec_toFour (X : Matrix (Fin 3) (Fin 3) ℂ) (v : Col → ℂ) :
    su3EmbedFn X *ᵥ toFour v = toFour (emb X *ᵥ v) := by
  rw [← emb_reindex, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm,
    toFour_comp]
  funext i
  rw [toFour_apply]
  rfl

theorem quarkSub4_invariant (X : Matrix (Fin 3) (Fin 3) ℂ) {w : Fin 4 → ℂ}
    (hw : w ∈ quarkSub4) : su3EmbedFn X *ᵥ w ∈ quarkSub4 := by
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
  change su3EmbedFn X *ᵥ toFour v ∈ quarkSub4
  rw [su3EmbedFn_mulVec_toFour]
  exact Submodule.mem_map_of_mem (quark_invariant X hv)

theorem leptonSub4_trivial (X : Matrix (Fin 3) (Fin 3) ℂ) {w : Fin 4 → ℂ}
    (hw : w ∈ leptonSub4) : su3EmbedFn X *ᵥ w = 0 := by
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
  change su3EmbedFn X *ᵥ toFour v = 0
  rw [su3EmbedFn_mulVec_toFour, lepton_trivial X hv, map_zero]

/-! ## 4. Irreducibility inside `Fin 4 → ℂ` -/

/-- Every non-zero `su3EmbedFn`-invariant submodule of the triplet is the triplet. Pulled back
along `toFour` to `ColourTriplet.quarkSub_irreducible`. -/
theorem quarkSub4_irreducible (W : Submodule ℂ (Fin 4 → ℂ)) (hle : W ≤ quarkSub4) (hne : W ≠ ⊥)
    (hinv : ∀ X : Matrix (Fin 3) (Fin 3) ℂ, X.trace = 0 →
      ∀ w ∈ W, su3EmbedFn X *ᵥ w ∈ W) :
    W = quarkSub4 := by
  obtain ⟨W', hW'⟩ : ∃ W' : Submodule ℂ (Col → ℂ),
      W' = W.map (toFour.symm : (Fin 4 → ℂ) →ₗ[ℂ] (Col → ℂ)) := ⟨_, rfl⟩
  have h1 : W' ≤ quarkSub := by
    intro v hv
    rw [hW'] at hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    have := hle hw
    rw [quarkSub4, Submodule.mem_map_equiv] at this
    exact this
  have h2 : W' ≠ ⊥ := by
    intro h
    apply hne
    rw [Submodule.eq_bot_iff] at h ⊢
    intro w hw
    have := h (toFour.symm w) (by rw [hW']; exact Submodule.mem_map_of_mem hw)
    exact (LinearEquiv.map_eq_zero_iff _).mp this
  have h3 : ∀ X : Matrix (Fin 3) (Fin 3) ℂ, X.trace = 0 → ∀ v ∈ W', emb X *ᵥ v ∈ W' := by
    intro X hX v hv
    rw [hW'] at hv ⊢
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    refine Submodule.mem_map.mpr ⟨su3EmbedFn X *ᵥ w, hinv X hX w hw, ?_⟩
    have key := su3EmbedFn_mulVec_toFour X (toFour.symm w)
    rw [LinearEquiv.apply_symm_apply] at key
    change toFour.symm (su3EmbedFn X *ᵥ w) = emb X *ᵥ toFour.symm w
    rw [key, LinearEquiv.symm_apply_apply]
  have h4 : W' = quarkSub := quarkSub_irreducible W' h1 h2 h3
  have h5 : W = W'.map (toFour : (Col → ℂ) →ₗ[ℂ] (Fin 4 → ℂ)) := by
    ext w
    rw [hW', Submodule.mem_map_equiv, Submodule.mem_map_equiv, LinearEquiv.symm_symm,
      LinearEquiv.apply_symm_apply]
  rw [h5, h4]
  rfl

/-! ## 5. Complementarity -/

theorem isCompl_quarkSub4_leptonSub4 : IsCompl quarkSub4 leptonSub4 := by
  have h := isCompl_quark_lepton
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [quarkSub4, leptonSub4,
      ← Submodule.map_inf (toFour : (Col → ℂ) →ₗ[ℂ] (Fin 4 → ℂ)) toFour.injective, h1,
      Submodule.map_bot]
  · rw [quarkSub4, leptonSub4, ← Submodule.map_sup, h2, Submodule.map_top, LinearEquiv.range]

/-! ## 6. On the cascade's own type -/

/-- The colour triplet as a submodule of `CascadeHilbert` — the declaration the L13 row said did
not exist. `CascadeHilbert` is `Fin 4 → ℂ` by `abbrev`, so this is `quarkSub4`; the theorem is
about the TYPE and not about the physics (`ASSUMPTIONS_LEDGER` 30). -/
noncomputable def quarkSubCascade : Submodule ℂ CascadeHilbert := quarkSub4

/-- The lepton singlet as a submodule of `CascadeHilbert`. -/
noncomputable def leptonSubCascade : Submodule ℂ CascadeHilbert := leptonSub4

theorem finrank_quarkSubCascade : Module.finrank ℂ quarkSubCascade = 3 := finrank_quarkSub4

theorem finrank_leptonSubCascade : Module.finrank ℂ leptonSubCascade = 1 := finrank_leptonSub4

theorem isCompl_quarkSubCascade_leptonSubCascade :
    IsCompl quarkSubCascade leptonSubCascade := isCompl_quarkSub4_leptonSub4

theorem quarkSubCascade_irreducible (W : Submodule ℂ CascadeHilbert) (hle : W ≤ quarkSubCascade)
    (hne : W ≠ ⊥)
    (hinv : ∀ X : Matrix (Fin 3) (Fin 3) ℂ, X.trace = 0 →
      ∀ w ∈ W, su3EmbedFn X *ᵥ w ∈ W) :
    W = quarkSubCascade := quarkSub4_irreducible W hle hne hinv

end ColourCascadeSubmodule
