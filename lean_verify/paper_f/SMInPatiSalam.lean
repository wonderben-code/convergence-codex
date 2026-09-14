/-
  SMInPatiSalam.lean — the Standard-Model gauge algebra `sl₃ ⊕ sl₂ ⊕ u(1)` IS a
  Lie subalgebra of the Pati–Salam algebra `sl₄ ⊕ sl₂_L ⊕ sl₂_R`: one injective
  Lie homomorphism, built from the three maps the estate already has.

  WHY THIS FILE EXISTS — SPINE LINK L10, THE ONE FALSE `GENUINE`. The July
  spine rated L10 GENUINE on the headline *sl₃ ⊕ sl₂ ⊕ u(1) ↪ sl₄ injectively,
  bracket-preservingly*. `SMEmbeddingHonest` (2 August) machine-refuted that
  for the estate's own maps — the assembled map has a kernel, its 11-dimensional
  range is not bracket-closed, the `sl₃` and `sl₂` images do not commute — and
  `SMLieHom.no_lieHom_assembling` (28 August) sharpened it: **no `LieHom` from
  `sl₃ × sl₂ × ℂ` to `sl₄` has these two components.** The spine's 2 August
  addendum then said where the true target lives: *the target must now be the
  PS product, NOT `su(4)` alone*. Six weeks later nothing had been built there.
  Queried before writing: no file in `paper_f` mentions the product
  `sl (Fin 4) ℂ × sl (Fin 2) ℂ × sl (Fin 2) ℂ` at all. The 24-link recompute's
  L10 auditor named this statement as the link's next step.

  WHAT THIS FILE PROVES.

  1. **`colourBL`** — the `sl₄` component `(A, B, c) ↦ su3(A) + u1(c/2)`, a
     `LieHom`. A SUM of two Lie homomorphisms is a Lie homomorphism only when
     their images commute, and that is exactly what `SMEmbeddingHonest` left
     standing: `colour_bl_bracket`. So the refutation and this construction
     rest on the same theorem, read in opposite directions.
  2. `isoL` — weak isospin, the identity onto `sl₂_L`.
  3. **`t3RHom`** — `c ↦ c • T₃ᴿ` into `sl₂_R`, with `T₃ᴿ = ½·diag(1, −1)`; a
     `LieHom` because `u(1)` is abelian and `⁅T₃ᴿ, T₃ᴿ⁆ = 0`. This is the
     frame `WeinbergIndex` already uses: hypercharge `Y = T₃ᴿ + (B−L)/2` is
     split across `sl₂_R` and the `B−L` direction of `sl₄`.
  4. **`smToPS`** — the product, and **`smToPS_injective`**. `smToPS_su3`,
     `smToPS_su2`, `smToPS_u1` pin the three restrictions to the estate's
     `SMLieHom.su3Hom`, the identity, and `SMLieHom.u1Hom (c/2)` with `c • T₃ᴿ`.
  5. **`smRange`** — the range as a Mathlib `LieSubalgebra` of the Pati–Salam
     algebra, of dimension **12**, the dimension of the source: the
     Standard-Model algebra sits inside the Pati–Salam algebra as a
     12-dimensional Lie subalgebra, injectively, with colour and `B−L` in `sl₄`.
     `SMLieHom`'s header had said *"No `LieSubalgebra` is built for any image"*.

  WHAT THIS DOES NOT DO, STATED FOR THE RATING. **It does not rescue the July
  headline.** `sl₃ ⊕ sl₂ ⊕ u(1) ↪ sl₄` is refuted for the estate's maps and
  open in general (the nonexistence-by-any-maps theorem needs `sl₃`
  representation theory, not begun); this file embeds into the 21-dimensional
  Pati–Salam algebra, not the 15-dimensional `sl₄`, which is the statement the
  spine's own addendum says the link should have made. **No group** — no
  `SU(n)`, no exponential, nothing at the level of `SU(3)×SU(2)×U(1) → SU(4)×…`
  (gap N4 stands). **No compact real form** — everything is over `ℂ`, as the
  three source maps are. **The normalisations** `c/2` and `½·diag(1,−1)` are
  the physics frame and not forced: any nonzero scalars give an injective
  `LieHom`, and the file says so rather than presenting the frame as derived.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import SMLieHom
import Mathlib.Algebra.Lie.Prod

namespace SMInPatiSalam

open Matrix LieAlgebra.SpecialLinear SMEmbeddingHonest SMLieHom

noncomputable section

/-- The Standard-Model gauge algebra, as the estate presents it. -/
abbrev SM := sl (Fin 3) ℂ × sl (Fin 2) ℂ × ℂ

/-- The Pati–Salam algebra `sl₄ ⊕ sl₂_L ⊕ sl₂_R`. -/
abbrev PS := sl (Fin 4) ℂ × sl (Fin 2) ℂ × sl (Fin 2) ℂ

/-! ## 1. The `sl₄` component: colour plus `B−L`, and the commutation that makes it a `LieHom` -/

/-- **`(A, B, c) ↦ su3(A) + u1(c/2)`.** A sum of two Lie homomorphisms; a Lie
homomorphism because the colour and `B−L` images commute — `colour_bl_bracket`,
the theorem `SMEmbeddingHonest` proved while refuting the direct sum. -/
def colourBL : SM →ₗ⁅ℂ⁆ sl (Fin 4) ℂ where
  toLinearMap :=
    su3EmbedRestricted ∘ₗ LinearMap.fst ℂ _ _
      + u1EmbedRestricted ∘ₗ ((1 / 2 : ℂ) • (LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _))
  map_lie' := by
    intro x y
    apply Subtype.ext
    -- the source bracket on the `ℂ` coordinate is zero
    have hc : (⁅x.2.2, y.2.2⁆ : ℂ) = 0 := by rw [Ring.lie_def]; ring
    change su3EmbedFn (⁅x.1, y.1⁆ : sl (Fin 3) ℂ).val
        + u1EmbedFn ((1 / 2 : ℂ) * ⁅x.2.2, y.2.2⁆)
      = ((⁅(⟨su3EmbedFn x.1.val + u1EmbedFn ((1 / 2 : ℂ) * x.2.2), _⟩ : sl (Fin 4) ℂ),
          (⟨su3EmbedFn y.1.val + u1EmbedFn ((1 / 2 : ℂ) * y.2.2), _⟩ : sl (Fin 4) ℂ)⁆)
            : sl (Fin 4) ℂ).val
    rw [sl_bracket, hc, mul_zero, sl_bracket]
    have h0 : u1EmbedFn 0 = 0 := map_zero u1EmbedLinear
    rw [h0, add_zero]
    exact (colour_bl_bracket x.1.val y.1.val ((1 / 2 : ℂ) * x.2.2) ((1 / 2 : ℂ) * y.2.2)).symm

/-! ## 2. Weak isospin and the right-handed `T₃` -/

/-- Weak isospin: the `sl₂` coordinate, unchanged, into `sl₂_L`. -/
def isoL : SM →ₗ⁅ℂ⁆ sl (Fin 2) ℂ :=
  (LieHom.fst ℂ (sl (Fin 2) ℂ) ℂ).comp (LieHom.snd ℂ (sl (Fin 3) ℂ) (sl (Fin 2) ℂ × ℂ))

/-- `T₃ᴿ = ½·diag(1, −1)`, the estate's `d2Sl` halved. -/
def t3R : sl (Fin 2) ℂ := (1 / 2 : ℂ) • d2Sl

theorem d2Sl_ne_zero : d2Sl ≠ 0 := by
  intro h
  have := congrArg (fun M : sl (Fin 2) ℂ => M.val 0 0) h
  simp [d2Sl, d2] at this

theorem t3R_ne_zero : t3R ≠ 0 := by
  intro h
  have := smul_eq_zero.mp h
  rcases this with h | h
  · norm_num at h
  · exact d2Sl_ne_zero h

/-- **`c ↦ c • T₃ᴿ`** into `sl₂_R`: a `LieHom` because `u(1)` is abelian and
`⁅T₃ᴿ, T₃ᴿ⁆ = 0`. -/
def t3RHom : SM →ₗ⁅ℂ⁆ sl (Fin 2) ℂ where
  toLinearMap := (LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _).smulRight t3R
  map_lie' := by
    intro x y
    have hc : (⁅x.2.2, y.2.2⁆ : ℂ) = 0 := by rw [Ring.lie_def]; ring
    change ⁅x.2.2, y.2.2⁆ • t3R = ⁅x.2.2 • t3R, y.2.2 • t3R⁆
    rw [hc, zero_smul, smul_lie, lie_smul, lie_self, smul_zero, smul_zero]

/-! ## 3. The embedding -/

/-- **THE STANDARD-MODEL ALGEBRA INTO THE PATI–SALAM ALGEBRA.** -/
def smToPS : SM →ₗ⁅ℂ⁆ PS :=
  LieHom.prod colourBL (LieHom.prod isoL t3RHom)

theorem smToPS_apply (x : SM) :
    smToPS x = (colourBL x, x.2.1, x.2.2 • t3R) := rfl

/-- The colour restriction is the estate's `su3Hom`. -/
theorem smToPS_su3 (A : sl (Fin 3) ℂ) : smToPS (A, 0, 0) = (su3Hom A, 0, 0) := by
  refine Prod.ext ?_ (Prod.ext rfl (zero_smul ℂ t3R))
  apply Subtype.ext
  have h0 : u1EmbedFn 0 = 0 := map_zero u1EmbedLinear
  change su3EmbedFn A.val + u1EmbedFn ((1 / 2 : ℂ) * 0) = su3EmbedFn A.val
  rw [mul_zero, h0, add_zero]

/-- The weak-isospin restriction is the identity onto `sl₂_L`. -/
theorem smToPS_su2 (B : sl (Fin 2) ℂ) : smToPS (0, B, 0) = (0, B, 0) := by
  refine Prod.ext ?_ (Prod.ext rfl (zero_smul ℂ t3R))
  apply Subtype.ext
  have h0 : u1EmbedFn 0 = 0 := map_zero u1EmbedLinear
  have h3 : su3EmbedFn 0 = 0 := map_zero su3EmbedLinear
  change su3EmbedFn (0 : sl (Fin 3) ℂ).val + u1EmbedFn ((1 / 2 : ℂ) * 0) = 0
  rw [mul_zero, h0]
  change su3EmbedFn 0 + 0 = 0
  rw [h3, add_zero]

/-- The hypercharge direction: `B−L` at `c/2` in `sl₄`, and `c • T₃ᴿ` in `sl₂_R`. -/
theorem smToPS_u1 (c : ℂ) : smToPS (0, 0, c) = (u1Hom (c / 2), 0, c • t3R) := by
  refine Prod.ext ?_ (Prod.ext rfl rfl)
  apply Subtype.ext
  have h3 : su3EmbedFn 0 = 0 := map_zero su3EmbedLinear
  change su3EmbedFn (0 : sl (Fin 3) ℂ).val + u1EmbedFn ((1 / 2 : ℂ) * c) = u1EmbedFn (c / 2)
  change su3EmbedFn 0 + u1EmbedFn ((1 / 2 : ℂ) * c) = u1EmbedFn (c / 2)
  rw [h3, zero_add]
  congr 1
  ring

/-- **INJECTIVE.** The `sl₂_R` coordinate recovers `c`, the `sl₂_L` coordinate
recovers `B`, and then `su3Hom` is injective. -/
theorem smToPS_injective : Function.Injective smToPS := by
  intro x y hxy
  rw [smToPS_apply, smToPS_apply] at hxy
  simp only [Prod.mk.injEq] at hxy
  obtain ⟨h1, h2, h3⟩ := hxy
  -- the ℂ coordinate
  have hc : x.2.2 = y.2.2 := by
    have := sub_eq_zero.mpr h3
    rw [← sub_smul, smul_eq_zero] at this
    rcases this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h t3R_ne_zero
  -- the sl₃ coordinate, through su3EmbedRestricted's injectivity
  have hA : x.1 = y.1 := by
    apply su3EmbedRestricted_injective
    apply Subtype.ext
    have h1' := congrArg Subtype.val h1
    change su3EmbedFn x.1.val + u1EmbedFn ((1 / 2 : ℂ) * x.2.2)
      = su3EmbedFn y.1.val + u1EmbedFn ((1 / 2 : ℂ) * y.2.2) at h1'
    rw [hc] at h1'
    exact add_right_cancel h1'
  exact Prod.ext hA (Prod.ext h2 hc)

/-! ## 4. The range, as a Lie subalgebra of dimension 12 -/

/-- **THE STANDARD-MODEL ALGEBRA AS A `LieSubalgebra` OF THE PATI–SALAM ALGEBRA.** -/
def smRange : LieSubalgebra ℂ PS := smToPS.range

theorem finrank_SM : Module.finrank ℂ SM = 12 := by
  have h3 : Module.finrank ℂ (sl (Fin 3) ℂ) = 8 := traceless_dim_3
  have h2 : Module.finrank ℂ (sl (Fin 2) ℂ) = 3 := traceless_dim_2
  rw [Module.finrank_prod, Module.finrank_prod, h3, h2, Module.finrank_self]

/-- Twelve dimensions: `8 + 3 + 1`, carried across by injectivity. -/
theorem finrank_smRange : Module.finrank ℂ smRange = 12 := by
  have h : Module.finrank ℂ (LinearMap.range smToPS.toLinearMap) = 12 := by
    rw [LinearMap.finrank_range_of_inj smToPS_injective, finrank_SM]
  exact h

/-! ## 5. Review round 75 — the ways this could be hollow

**"It is the three known maps glued together."** It is the three known maps
glued together, and the point is the gluing: `SMLieHom.no_lieHom_assembling`
says two of them CANNOT be glued into `sl₄`, and §1 says two of them CAN be
glued into `sl₄` — a different two. What decides which pairs glue is whether
the images commute, and `colour_bl_bracket` is the theorem for the pair that
does. The `sl₂` factor, which refused to commute with colour inside `sl₄`, is
sent to its own factor of the product, where nothing is asked of it.

**"The 12 is dimension counting."** Yes — and it is the number the spine's
July text got wrong by one. `SMEmbeddingHonest.assembly_range_eq_eleven` is the
refuted assembly's span; this embedding's range is the full 12 because it is
injective, and injectivity is proved, not counted.

**"So L10 is GENUINE again."** No. The headline the July rating was attached to
is `↪ sl₄`, and that is refuted. What is proved is the statement the spine's
own addendum says the headline should have been. The recompute will rate
against the statement the author owns; this file re-rates nothing. **What
moved**: the defensible statement had no `LieHom` and no `LieSubalgebra`
behind it, and now has both.

**"The normalisation is a choice."** It is, and the header says so: `c/2` and
`½·diag(1, −1)` are `WeinbergIndex`'s frame, and any nonzero scalars would give
an injective `LieHom`. Nothing here derives the frame.
-/

end

end SMInPatiSalam
