/-
  ConeMultiplicity: the cone's eigenspace DIMENSIONS, pinned to within the one hub dimension —
  unit 80's own remaining fence

  WHY THIS FILE EXISTS. `PROOF_STRATEGY` §7 item 2: *finish every unfinished chain.* Unit 80
  proved that every eigenvalue of the cone's signless Laplacian is accounted for, and named what
  was left: **multiplicities are still not computed** — the dichotomy says which numbers can be
  eigenvalues and that nothing else can, not how many times each occurs. Unit 79 had said the
  missing ingredient was independence of `G`'s eigenvectors; unit 80 corrected that to *it is
  independence that a MULTIPLICITY count needs*. **This file shows that was also too pessimistic,
  and by the same mechanism as before**: the multiplicity follows from the projection commuting
  with `Q`, read at the level of eigenSPACES rather than eigenVECTORS, and independence is never
  used.

  WHAT IS PROVED.
  * **`coneEig`, `rimEig`, `mem_coneEig`, `mem_rimEig`** — the two eigenspaces as `Submodule`s,
    in this estate's own convention for an eigenspace (`(toLin' M - μ • id).ker`, as
    `BoxEigenspaceDimension` and `CompleteSpectrumTwoPoints` use it), with `rimEig` cut down by
    the zero-sum functional `sumL`.
  * **`rimPartL`, `liftRimL`** — unit 80's projection and unit 79's lift, as `LinearMap`s. They
    were plain functions, which is enough for a pointwise eigenvector statement and not enough
    for a dimension count; **that is the whole reason this file exists as a separate unit.**
  * **`rimPartL_mapsTo`, `liftRimL_mapsTo`** — the projection carries `coneEig lam` into
    `rimEig (lam - d - 1)` and the lift carries it back. The first consumes
    `ConeSignlessExhaustion.rimPart_eigen`, **which was EXTRACTED from unit 80's proof for this
    purpose rather than re-derived here** (`ERRATUM 348`, applied before a duplicate existed for
    the second time in this campaign).
  * **`restrict_surjective`** — the restricted projection is onto, because the lift is a section
    of it on zero-sum vectors.
  * **`finrank_coneEig` — THE EXACT FORMULA.** `finrank (rimEig (lam - d - 1)) + finrank (ker of
    the restricted projection) = finrank (coneEig lam)`, by rank–nullity on the restriction.
  * **`finrank_ker_le_one` — AND THE KERNEL IS AT MOST A LINE.** An eigenvector whose rim part
    vanishes has all its rim entries equal, and the rim equation then determines the hub entry
    from them, so the kernel injects into `ℝ` by reading one rim coordinate.
  * **`finrank_coneEig_bounds` — THE READER-FACING STATEMENT.** The cone's multiplicity at `lam`
    is the rim's zero-sum multiplicity at `lam - d - 1`, **or one more, and never anything else.**
    Unit 80's fence is closed to within that one dimension, which is exactly the hub plane's
    possible contribution.

  WHAT IS **NOT** CLAIMED.
  * **WHICH of the two values it is, is not decided here.** The kernel is one-dimensional exactly
    when `lam` is a root of the hub quadratic and zero-dimensional otherwise; the `≤ 1` bound is
    proved and the two-way determination is not. So this is a multiplicity formula with a
    one-dimensional ambiguity, not a multiplicity table — and the ambiguity is located, not
    diffuse: it is the hub plane and nothing else.
  * ~~**No eigenvalue is EVALUATED and no rim multiplicity is computed.** The formula takes the
    rim's zero-sum multiplicity as input, exactly as unit 79's and 80's statements take the
    rim's spectrum as input. **Nothing here computes a number.**~~
    **HALF FALSE FROM 2026-09-16 (unit 83).** `ConeMultiplicityExact` evaluates the two hub
    eigenvalues and decides the `≤ 1` this file left open, so *no eigenvalue is evaluated* is
    gone. **No rim multiplicity is computed is still exactly true** and is the larger half: two
    of the cone's `n + 1` eigenvalues are now explicit and the other `n - 1` remain inputs.
    Original kept per `ERRATUM 94`.
  * **Independence of `G`'s eigenvectors is never used**, which is the point: units 79 and 80
    both named it as the missing ingredient, and it is not needed for this either.
  * **Nothing about the cascade, the spine, or any wall.** `UNLOCK_WATCHLIST` L34948 clause (b)
    is narrowed once more; clause (c) is untouched.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import ConeSignlessExhaustion

namespace ConeMultiplicity

open SimpleGraph LaplacianSignless Matrix ConeSignlessSpectrum ConeSignlessExhaustion

/-! ## The two maps, and the zero-sum functional -/

section Maps

variable {V : Type*}

def liftRimL : (V → ℝ) →ₗ[ℝ] (Option V → ℝ) where
  toFun := liftRim
  map_add' u w := by funext a; cases a <;> simp [liftRim]
  map_smul' c w := by funext a; cases a <;> simp [liftRim]

@[simp] theorem liftRimL_apply (y : V → ℝ) : liftRimL (V := V) y = liftRim y := rfl

variable [Fintype V]

/-- The zero-sum functional on the rim. -/
noncomputable def sumL : (V → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i

@[simp] theorem sumL_apply (y : V → ℝ) : sumL (V := V) y = ∑ i, y i := by
  simp [sumL, LinearMap.sum_apply]

noncomputable def rimPartL : (Option V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun := rimPart
  map_add' u w := by
    funext i
    simp only [rimPart, Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c w := by
    funext i
    simp only [rimPart, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, RingHom.id_apply]
    ring

@[simp] theorem rimPartL_apply (w : Option V → ℝ) : rimPartL (V := V) w = rimPart w := rfl
end Maps

/-! ## The eigenspaces -/

section Eigenspaces

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def coneEig (lam : ℝ) : Submodule ℝ (Option V → ℝ) :=
  LinearMap.ker (Matrix.toLin' (signlessLap (coneGraph G)) - lam • LinearMap.id)

noncomputable def rimEig (mu : ℝ) : Submodule ℝ (V → ℝ) :=
  LinearMap.ker (Matrix.toLin' (G.adjMatrix ℝ) - mu • LinearMap.id) ⊓ LinearMap.ker (sumL (V := V))

theorem mem_coneEig {lam : ℝ} {x : Option V → ℝ} :
    x ∈ coneEig G lam ↔ signlessLap (coneGraph G) *ᵥ x = lam • x := by
  simp only [coneEig, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Matrix.toLin'_apply, sub_eq_zero]

theorem mem_rimEig {mu : ℝ} {y : V → ℝ} :
    y ∈ rimEig G mu ↔ (G.adjMatrix ℝ *ᵥ y = mu • y ∧ ∑ i, y i = 0) := by
  simp only [rimEig, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, Matrix.toLin'_apply, sub_eq_zero, sumL_apply]

/-- `rimPartL` carries the cone's eigenspace into the rim's zero-sum eigenspace. -/
theorem rimPartL_mapsTo (hV : 0 < Fintype.card V) {d : ℕ} (hreg : ∀ i, G.degree i = d)
    (hrow : ∀ y : V → ℝ, ∑ i, (G.adjMatrix ℝ *ᵥ y) i = (d : ℝ) * ∑ i, y i)
    (lam : ℝ) : ∀ x ∈ coneEig G lam, rimPartL (V := V) x ∈ rimEig G (lam - (d : ℝ) - 1) := by
  intro x hx
  rw [mem_coneEig] at hx
  rw [mem_rimEig]
  exact ⟨rimPart_eigen G hV hreg hrow hx, rimPart_sum hV x⟩

/-- and `liftRimL` carries it back. -/
theorem liftRimL_mapsTo {d : ℕ} (hreg : ∀ i, G.degree i = d) (lam : ℝ) :
    ∀ y ∈ rimEig G (lam - (d : ℝ) - 1), liftRimL (V := V) y ∈ coneEig G lam := by
  intro y hy
  rw [mem_rimEig] at hy
  rw [mem_coneEig, liftRimL_apply]
  have := cone_signless_rim_eigen G hreg y hy.2 hy.1
  rw [this]
  congr 1
  ring

/-- The restriction is SURJECTIVE, because `liftRimL` is a section of it on zero-sum vectors. -/
theorem restrict_surjective (hV : 0 < Fintype.card V) {d : ℕ} (hreg : ∀ i, G.degree i = d)
    (hrow : ∀ y : V → ℝ, ∑ i, (G.adjMatrix ℝ *ᵥ y) i = (d : ℝ) * ∑ i, y i) (lam : ℝ) :
    Function.Surjective
      ((rimPartL (V := V)).restrict (rimPartL_mapsTo G hV hreg hrow lam)) := by
  intro z
  refine ⟨⟨liftRimL (V := V) (z : V → ℝ), liftRimL_mapsTo G hreg lam _ z.2⟩, ?_⟩
  apply Subtype.ext
  have hz := (mem_rimEig G).1 z.2
  simp only [LinearMap.restrict_apply, rimPartL_apply, liftRimL_apply]
  funext i
  simp only [rimPart, liftRim_some]
  rw [hz.2]
  simp

/-- **THE MULTIPLICITY, EXACTLY.** The cone's eigenspace at `lam` has the dimension of the rim's
zero-sum eigenspace at `lam - d - 1`, plus whatever the hub plane contributes — and the hub term
is the kernel of the projection restricted to the eigenspace. -/
theorem finrank_coneEig (hV : 0 < Fintype.card V) {d : ℕ} (hreg : ∀ i, G.degree i = d)
    (hrow : ∀ y : V → ℝ, ∑ i, (G.adjMatrix ℝ *ᵥ y) i = (d : ℝ) * ∑ i, y i) (lam : ℝ) :
    Module.finrank ℝ (rimEig G (lam - (d : ℝ) - 1))
        + Module.finrank ℝ
            (LinearMap.ker ((rimPartL (V := V)).restrict (rimPartL_mapsTo G hV hreg hrow lam)))
      = Module.finrank ℝ (coneEig G lam) := by
  have h := LinearMap.finrank_range_add_finrank_ker
    ((rimPartL (V := V)).restrict (rimPartL_mapsTo G hV hreg hrow lam))
  rw [LinearMap.range_eq_top.2 (restrict_surjective G hV hreg hrow lam)] at h
  simpa using h

/-- Reading one rim coordinate, as a linear map off the kernel. Built explicitly rather than as
a composition of three maps: the composite's coercion would not unify with
`LinearMap.ker_eq_bot`, and an explicit `LinearMap.mk` sidesteps that entirely. -/
noncomputable def hubRead (hV : 0 < Fintype.card V) {d : ℕ} (hreg : ∀ i, G.degree i = d)
    (hrow : ∀ y : V → ℝ, ∑ i, (G.adjMatrix ℝ *ᵥ y) i = (d : ℝ) * ∑ i, y i) (lam : ℝ)
    [Nonempty V] :
    (LinearMap.ker ((rimPartL (V := V)).restrict (rimPartL_mapsTo G hV hreg hrow lam)))
      →ₗ[ℝ] ℝ where
  toFun z := ((z : (coneEig G lam)) : Option V → ℝ) (some (Classical.arbitrary V))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- An eigenvector whose rim part vanishes and whose read-off coordinate vanishes is zero: all
its rim entries are equal, hence all zero, and the rim equation then kills the hub entry. -/
theorem eq_zero_of_hubRead_eq_zero [Nonempty V] (hV : 0 < Fintype.card V) {d : ℕ}
    (hreg : ∀ i, G.degree i = d)
    (hrow : ∀ y : V → ℝ, ∑ i, (G.adjMatrix ℝ *ᵥ y) i = (d : ℝ) * ∑ i, y i) (lam : ℝ)
    (z : LinearMap.ker ((rimPartL (V := V)).restrict (rimPartL_mapsTo G hV hreg hrow lam)))
    (hz : hubRead G hV hreg hrow lam z = 0) : z = 0 := by
  have hrp : rimPart (V := V) ((z : (coneEig G lam)) : Option V → ℝ) = 0 := by
    have h0 := LinearMap.mem_ker.1 z.2
    have h1 : ((rimPartL (V := V)) ((z : (coneEig G lam)) : Option V → ℝ)) = 0 :=
      Subtype.ext_iff.1 h0
    simpa using h1
  have hall : ∀ i, ((z : (coneEig G lam)) : Option V → ℝ) (some i) = 0 := by
    intro i
    have h1 := congrFun hrp i
    have h2 := congrFun hrp (Classical.arbitrary V)
    simp only [rimPart, Pi.zero_apply, sub_eq_zero] at h1 h2
    rw [h1, ← h2]
    exact hz
  have heq := (mem_coneEig G).1 (z : (coneEig G lam)).2
  have hi := congrFun heq (some (Classical.arbitrary V))
  rw [cone_signless_mulVec_rim, hreg (Classical.arbitrary V)] at hi
  simp only [hall, mul_zero, zero_add, Finset.sum_const_zero, Pi.smul_apply,
    smul_eq_mul, mul_zero] at hi
  apply Subtype.ext
  apply Subtype.ext
  funext a
  cases a with
  | none => simpa using hi
  | some i => simpa using hall i

/-- **THE HUB TERM IS AT MOST ONE-DIMENSIONAL.** An eigenvector whose rim part vanishes has all
its rim entries equal, and the rim equation then determines the hub entry from them — so the
whole kernel injects into `ℝ` by reading one rim coordinate. -/
theorem finrank_ker_le_one [Nonempty V] (hV : 0 < Fintype.card V) {d : ℕ}
    (hreg : ∀ i, G.degree i = d)
    (hrow : ∀ y : V → ℝ, ∑ i, (G.adjMatrix ℝ *ᵥ y) i = (d : ℝ) * ∑ i, y i) (lam : ℝ) :
    Module.finrank ℝ
        (LinearMap.ker ((rimPartL (V := V)).restrict (rimPartL_mapsTo G hV hreg hrow lam)))
      ≤ 1 := by
  have hinj : Function.Injective (hubRead G hV hreg hrow lam) := by
    intro a b hab
    have hsub : hubRead G hV hreg hrow lam (a - b)
        = hubRead G hV hreg hrow lam a - hubRead G hV hreg hrow lam b := rfl
    have h := eq_zero_of_hubRead_eq_zero G hV hreg hrow lam (a - b) (by
      rw [hsub, hab, sub_self])
    exact sub_eq_zero.1 h
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

/-- **THE MULTIPLICITY, PINNED TO WITHIN THE ONE HUB DIMENSION.** The cone's eigenspace at `lam`
has at least the dimension of the rim's zero-sum eigenspace at `lam - d - 1`, and at most one
more. **This is what unit 80 recorded as still open**: *multiplicities are still not computed*. -/
theorem finrank_coneEig_bounds [Nonempty V] (hV : 0 < Fintype.card V) {d : ℕ}
    (hreg : ∀ i, G.degree i = d)
    (hrow : ∀ y : V → ℝ, ∑ i, (G.adjMatrix ℝ *ᵥ y) i = (d : ℝ) * ∑ i, y i) (lam : ℝ) :
    Module.finrank ℝ (rimEig G (lam - (d : ℝ) - 1)) ≤ Module.finrank ℝ (coneEig G lam)
      ∧ Module.finrank ℝ (coneEig G lam)
          ≤ Module.finrank ℝ (rimEig G (lam - (d : ℝ) - 1)) + 1 := by
  have he := finrank_coneEig G hV hreg hrow lam
  have hk := finrank_ker_le_one G hV hreg hrow lam
  omega

end Eigenspaces

end ConeMultiplicity
