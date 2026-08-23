/-
  IsingSlabStrict.lean — the magnetisation of this estate's Ising slab in a POSITIVE field is
  STRICTLY POSITIVE.

  WHY. Three files in a row ended on the same sentence: `≥ 0` is not `> 0`. `IsingSlabGriffiths`
  got the slab magnetisation to non-negative and wrote the route to strictness down as a route.
  `IsingSlabFerro` identified the estate's own slab interaction as the parameter that theorem takes,
  which left strictness as the single remaining piece. `IsingGriffiths` then proved the strict
  inequality for an abstract finite Ising model — `griffiths_site_pos` — and said in as many words
  that the slab had not been told. **This file is the telling.**

  AND IT IS ONE SUBSTITUTION. The transport in `IsingSlabGriffiths.expectG_nonneg` — reindex the
  path of cross-sections as one configuration on space-time, rewrite `β · energyG` as interaction
  terms — is unchanged. Run it with `griffiths_site_pos` where `griffiths_site_nonneg` stood, and
  with `IsingSlabConfig.partitionG_pos` (which the estate has had all along) for the denominator.

  WHAT THE STRICT THEOREM ASKS FOR, AND WHERE THE SLAB HAS IT. `griffiths_site_pos` wants an
  interaction index whose set is the observed singleton and whose coupling is strictly positive.
  The slab has exactly one such family and it is the field: `sset M B (Sum.inr (Sum.inl (0, v₀)))`
  is `{(0, v₀)}` **definitionally** — the witness is `rfl` — and its coupling is `β · h`. So the
  hypothesis of the theorem below is precisely *the temperature is finite and the field is on*, and
  `0 < β · h` is the only thing that had to be new.

  WHAT IS PROVED.

  * **`expectG_pos`** — the abstract slab: for `0 < β`, `0 < h`, a ferromagnetic intra energy and a
    length of at least two slices, `0 < expectG β (intraOf c B + fieldE h) M (spin ∘ · v₀)`;
  * **`expectG_slab_pos`** — **this estate's own anisotropic three-dimensional slab**, through
    `IsingSlabFerro.slabIntraAniso_eq_intraOf`;
  * **`expectG_slab_pos_iso`** — the isotropic case, the slab the rest of the estate uses;
  * **`expectG_slab_eq_zero_of_no_field`** — and at `h = 0` the answer is `0`, so the field
    hypothesis is sharp.

  THE HYPOTHESES ARE THE ONES THE CHAIN ALREADY CARRIED, ONE OF THEM STRENGTHENED. `1 ≤ M`,
  `1 ≤ a`, `1 ≤ b` are unchanged and are there for the reason those files record: in `Fin (n+1)` the
  successor of the last index is itself, so a slab one slice long has no bond along its length and a
  cross-section one site wide has no bond across it. `0 ≤ β` and `0 ≤ h` become `0 < β` and
  `0 < h`, and both are needed. **At `h = 0` the conclusion is FALSE, and §4 proves it here rather
  than citing it** (`ERRATUM 247`): `expectG_slab_eq_zero_of_no_field` — the magnetisation of a slab
  in no field is exactly zero, at every `β`, every `M` and every cross-section, because the
  fieldless energy is flip-invariant. So `0 ≤ h` is not available. The couplings `Ja`, `Jb` stay
  `≥ 0`; nothing here needs them switched on.

  WHAT THIS DOES NOT SAY. It is a finite-volume statement at every finite `M`, `a`, `b`, with no
  bound uniform in them, so **it is not spontaneous magnetisation and it is not symmetry breaking**.
  The limit `h → 0⁺` after `M, a, b → ∞` is the thing `ExhibitsSymmetryBreaking` wants, and neither
  limit is taken here. What has closed is the watchlist item that asked for the magnetisation in a
  field to be positive at finite volume.

  ADDENDUM 2026-08-23, SAME DAY — **`1 ≤ a` AND `1 ≤ b` ARE GONE FROM `expectG_slab_pos` AND
  `expectG_slab_pos_iso`.** The paragraph above is kept (`ERRATUM 94`) and was right that the
  degenerate width is a real geometric fact and wrong to conclude the case had to be excluded: at
  `a = 0` the horizontal term is the CONSTANT `Ja`, and a constant is of Griffiths shape (the empty
  interaction set, whose product is `1`). `IsingSlabFerro.bondSet` now returns `∅` there and its
  identity holds for every `a` and `b`, so **this file's slab theorems hold at every cross-section,
  down to a single site.** `1 ≤ M` is unchanged and is still needed. `expectG_pos` never had the
  width hypotheses — it is stated for an arbitrary finite cross-section — so only the two slab
  corollaries move. See `ERRATUM 251` for the claim that the exclusion rested on, which was false.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingSlabFerro
import IsingFieldOdd

namespace IsingSlabStrict

open Finset Real
open IsingTransfer2D IsingSlabTransfer IsingSlabConfig IsingSlabField IsingSlabAniso
open IsingGriffiths IsingSlabGriffiths IsingSlabFerro

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {K : Type*} [Fintype K]

/-! ## 1. The witness: the field term at the observed site -/

omit [Fintype V] [Fintype K] in
/-- The field's interaction set at `(j, v)` **is** the singleton `{(j, v)}`, definitionally. This is
the `S i₀ = A` hypothesis of `IsingGriffiths.griffiths_site_pos`, and the slab satisfies it on the
nose rather than up to a rewrite. -/
theorem sset_field_singleton (M : ℕ) (B : K → Finset V) (j : Fin (M + 1)) (v : V) :
    sset M B (Sum.inr (Sum.inl (j, v))) = {(j, v)} := rfl

omit [Fintype V] [DecidableEq V] [Fintype K] in
/-- And its coupling is `β · h`, so it is strictly positive exactly when the temperature is finite
and the field is on. -/
theorem coup_field_pos {M : ℕ} {β h : ℝ} (hβ : 0 < β) (hh : 0 < h) {c : K → ℝ}
    (j : Fin (M + 1)) (v : V) : 0 < coup M β h c (Sum.inr (Sum.inl (j, v))) :=
  mul_pos hβ hh

/-! ## 2. The abstract slab -/

/-- **THE SLAB MAGNETISATION IN A STRICTLY POSITIVE FIELD IS STRICTLY POSITIVE**, for a
ferromagnetic intra energy, a strictly positive inverse temperature and a length of at least two
slices. The proof is `IsingSlabGriffiths.expectG_nonneg` with `griffiths_site_pos` in place of
`griffiths_site_nonneg` and `partitionG_pos` in place of the non-negativity of the denominator. -/
theorem expectG_pos {M : ℕ} (hM : 1 ≤ M) {β h : ℝ} (hβ : 0 < β) (hh : 0 < h)
    {c : K → ℝ} (hc : ∀ k, 0 ≤ c k) (B : K → Finset V) (v₀ : V) :
    0 < expectG β (fun σ => intraOf c B σ + fieldE h σ) M (fun σ => spin (σ v₀)) := by
  rw [expectG]
  refine div_pos ?_ (partitionG_pos _ _ _)
  have hg := griffiths_site_pos (V := Fin (M + 1) × V) (I := Idx M V K)
    (sset M B) (coup M β h c) (coup_nonneg hβ.le hh.le hc) ((0 : Fin (M + 1)), v₀)
    (Sum.inr (Sum.inl ((0 : Fin (M + 1)), v₀)))
    (sset_field_singleton M B _ _) (coup_field_pos hβ hh _ _)
  have htr := Fintype.sum_equiv (pathEquiv M V)
    (fun s : Fin (M + 1) → Cross V => spin (s 0 v₀)
      * exp (β * energyG (fun σ => intraOf c B σ + fieldE h σ) M s))
    (fun τ : (Fin (M + 1) × V) → Bool => spin (τ ((0 : Fin (M + 1)), v₀))
      * exp (∑ i : Idx M V K, coup M β h c i * ∏ w ∈ sset M B i, spin (τ w)))
    (fun s => by dsimp only [pathEquiv_apply]; rw [energy_eq hM β h c B s])
  rw [htr]
  exact hg

/-! ## 3. This estate's own slab -/

variable {a b : ℕ}

/-- **THE MAGNETISATION OF THIS ESTATE'S THREE-DIMENSIONAL ISING SLAB, IN A STRICTLY POSITIVE FIELD
AND WITH FERROMAGNETIC COUPLINGS, IS STRICTLY POSITIVE**, at every site, **every cross-section**,
and every length of at least two slices. (The width conditions were here when this was written and
were removed the same day — see the file header's second addendum and `ERRATUM 251`.) -/
theorem expectG_slab_pos {M : ℕ} (hM : 1 ≤ M)
    {β h Ja Jb : ℝ} (hβ : 0 < β) (hh : 0 < h) (hJa : 0 ≤ Ja) (hJb : 0 ≤ Jb)
    (v₀ : Fin (a + 1) × Fin (b + 1)) :
    0 < expectG β (fun σ => slabIntraAniso Ja Jb σ + fieldE h σ) M (fun σ => spin (σ v₀)) := by
  have hE : (fun σ : Cross (Fin (a + 1) × Fin (b + 1)) => slabIntraAniso Ja Jb σ + fieldE h σ)
      = fun σ => intraOf (bondCoup a b Ja Jb) (bondSet a b) σ + fieldE h σ := by
    funext σ
    rw [slabIntraAniso_eq_intraOf Ja Jb σ]
  rw [hE]
  exact expectG_pos hM hβ hh (bondCoup_nonneg hJa hJb) (bondSet a b) v₀

/-- The isotropic case, where the energy is the estate's own `slabIntra`. -/
theorem expectG_slab_pos_iso {M : ℕ} (hM : 1 ≤ M)
    {β h : ℝ} (hβ : 0 < β) (hh : 0 < h) (v₀ : Fin (a + 1) × Fin (b + 1)) :
    0 < expectG β (fun σ => slabIntra σ + fieldE h σ) M (fun σ => spin (σ v₀)) := by
  have hE : (fun σ : Cross (Fin (a + 1) × Fin (b + 1)) => slabIntra σ + fieldE h σ)
      = fun σ => slabIntraAniso 1 1 σ + fieldE h σ := by
    funext σ
    rw [slabIntraAniso_one_one]
  rw [hE]
  exact expectG_slab_pos hM hβ hh zero_le_one zero_le_one v₀

/-! ## 4. And `0 < h` is not removable -/

/-- **AT ZERO FIELD THE CONCLUSION IS FALSE, NOT MERELY UNPROVED — AND THAT IS A THEOREM HERE AND
NOT A CITATION.** The slab energy without a field is flip-invariant
(`IsingSlabAniso.slabIntraAniso_flipCross`), so `IsingFieldOdd.expectG_spin_eq_zero` gives
magnetisation exactly `0`, at every `β`, every `M`, every cross-section — no `1 ≤ a`, `1 ≤ b` or
`1 ≤ M` needed — and every site. So `0 < h` in `expectG_slab_pos` is not an artefact of the proof
and cannot be relaxed to `0 ≤ h` (`ERRATUM 247`: a sentence defending a hypothesis is a claim). -/
theorem expectG_slab_eq_zero_of_no_field (β : ℝ) (M : ℕ) (Ja Jb : ℝ)
    (v₀ : Fin (a + 1) × Fin (b + 1)) :
    expectG β (fun σ => slabIntraAniso Ja Jb σ + fieldE 0 σ) M (fun σ => spin (σ v₀)) = 0 := by
  refine IsingFieldOdd.expectG_spin_eq_zero (fun σ => ?_) β M v₀
  rw [slabIntraAniso_flipCross]
  simp [fieldE]

end

end IsingSlabStrict
