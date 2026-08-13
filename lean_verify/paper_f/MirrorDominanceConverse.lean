import MirrorDominance

/-!
# The mirror criterion is necessary too, so it is the criterion

`MirrorDominance` proved `MirrorDominated` **sufficient** for reflection positivity on every
graph with a mirror reflection, at every mass, and left necessity as the leg — recorded in
`UNLOCK_WATCHLIST` and in `WALLS` W1.3 with its blocker named:

> Formalising it needs the solution of `D w = −2 Eᵀ u` exhibited, which the sufficiency
> direction does not, and the estate has no lemma producing it. **This is now a missing lemma
> rather than a missing idea.**

That lemma is §1. With it the converse is `ReflectionConverse`'s argument again, and the wall's
converse question is closed for **every** reflection, with or without fixed points:

* no fixed point — `ReflectionConverse.reflectionPositive_iff_hcross`;
* a fixed layer — `reflectionPositive_iff_mirrorDominated` below.

## The missing lemma, and why it is not a matrix inversion

The obstruction was described as inverting the mirror block `D`. It is not: what is needed is
only that the equation `D z = b` is **solvable**, and solvability is free. The map
`z ↦ (N z)|_Mir` carries vectors supported on the mirror to vectors supported on the mirror, and
it is **injective** — if `(N z)|_Mir = 0` for such a `z` then `⟪z, N z⟫` collapses to a sum over
the mirror of `z r · 0`, so the form vanishes and positive definiteness kills `z`. An injective
endomorphism of a finite-dimensional space is surjective. **§1 forms no submatrix, computes no
determinant and inverts nothing** — it is `massive_posDef` and `LinearMap.surjective_of_injective`.

Recorded because the leg was written down as *"the Schur solve"*, which sounds like linear
algebra one has to do, and the honest description is that it is linear algebra one does not.

(The Green function is of course still an inverse, by its definition, and §3 uses that as every
file on this wall does. The claim above is about §1 and is scoped to §1 — an earlier draft of
this header said *"no inverse appears anywhere in this file"*, which is false, and the adversarial
pass caught it before the unit was committed.)

## The rest is `ReflectionConverse`, with one hypothesis moved

`ReflectionConverse` proves necessity by feeding reflection positivity the vector `N η` cut down
to the half, for `η` even, and observing that on a fixed-point-free reflection cutting and
re-symmetrising are mutually inverse, so the symmetric energy is exact. With a fixed layer that
inversion fails in general — and §2 shows it fails only because `N η` may be nonzero on the
mirror. **Choose `η` so that it is not**, which is exactly what §1 supplies, and the same proof
runs. The mirror hypothesis is not removed; it is discharged by the choice of test vector.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace MirrorDominanceConverse

open Matrix GraphLaplacian GraphReflection GraphMirrorReflection MirrorDominance

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

/-! ## 1. The equation on the mirror is solvable, and solvability is all that is needed -/

/-- The vectors supported on the fixed layer. -/
def mirSpace (Mir : Finset V) : Submodule ℝ (V → ℝ) where
  carrier := {z | ∀ p, p ∉ Mir → z p = 0}
  add_mem' {a b} ha hb := fun p hp => by
    simp only [Pi.add_apply, ha p hp, hb p hp, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' c {z} hz := fun p hp => by
    simp only [Pi.smul_apply, hz p hp, smul_zero]

/-- The operator, restricted to the fixed layer at both ends. -/
noncomputable def mirOp (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (Mir : Finset V) :
    mirSpace Mir →ₗ[ℝ] mirSpace (V := V) Mir where
  toFun z := ⟨fun p => if p ∈ Mir then (massive G m *ᵥ (z : V → ℝ)) p else 0,
    fun _ hp => if_neg hp⟩
  map_add' z z' := by
    apply Subtype.ext; funext p
    by_cases hp : p ∈ Mir <;>
      simp [hp, Submodule.coe_add, Matrix.mulVec_add]
  map_smul' c z := by
    apply Subtype.ext; funext p
    by_cases hp : p ∈ Mir <;>
      simp [hp, Matrix.mulVec_smul]

/-- **INJECTIVE, BECAUSE THE FORM COLLAPSES.** For a vector supported on the mirror, every term
of `⟪z, N z⟫` has `z r` outside the mirror or `(N z) r` inside it, so the form is the mirror
sum and vanishes with the image. Positive definiteness does the rest. -/
theorem mirOp_injective (hm : m ≠ 0) : Function.Injective (mirOp (V := V) G m Mir) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have hzero : ∀ r ∈ Mir, (massive G m *ᵥ (z : V → ℝ)) r = 0 := by
    intro r hr
    have := congrFun (congrArg Subtype.val hz) r
    simpa [mirOp, hr] using this
  have hform : (z : V → ℝ) ⬝ᵥ (massive G m *ᵥ (z : V → ℝ)) = 0 := by
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hp : p ∈ Mir
    · rw [hzero p hp, mul_zero]
    · rw [z.2 p hp, zero_mul]
  by_contra hne
  have hv : (z : V → ℝ) ≠ 0 := fun hc => hne (Subtype.ext hc)
  have := (massive_posDef G hm).dotProduct_mulVec_pos hv
  simp only [star_trivial] at this
  linarith

/-- **THE SOLVE.** For any `b`, there is a vector supported on the mirror that the operator
carries onto `b` there. No inverse is formed. -/
theorem exists_mir_solution (hm : m ≠ 0) (b : V → ℝ) :
    ∃ z : V → ℝ, (∀ p, p ∉ Mir → z p = 0) ∧ ∀ r ∈ Mir, (massive G m *ᵥ z) r = b r := by
  have hsurj : Function.Surjective (mirOp (V := V) G m Mir) :=
    LinearMap.surjective_of_injective (mirOp_injective hm)
  obtain ⟨z, hz⟩ := hsurj ⟨fun p => if p ∈ Mir then b p else 0, fun _ hp => if_neg hp⟩
  refine ⟨(z : V → ℝ), z.2, fun r hr => ?_⟩
  have := congrFun (congrArg Subtype.val hz) r
  simpa [mirOp, hr] using this

/-! ## 2. Cutting inverts symmetrisation on an even vector that vanishes on the mirror

`ReflectionConverse.sym_cut` needs a fixed-point-free reflection. This is the same statement for
a mirror half, and it shows exactly what the mirror costs: one extra hypothesis on the vector,
not on the graph.
-/

omit [Fintype V] in
theorem sym_cut_of_mir_zero (hM : IsMirrorHalf θ H Mir) {y : V → ℝ} (hy : IsEvenFun θ y)
    (hy0 : ∀ r ∈ Mir, y r = 0) :
    GraphReflection.sym θ (ReflectionConverse.cut H y) = y := by
  funext p
  simp only [GraphReflection.sym, ReflectionConverse.cut]
  by_cases hp : p ∈ H
  · rw [if_pos hp, if_neg (hM.notMem_of_mem hp), add_zero]
  · by_cases hmir : p ∈ Mir
    · rw [if_neg hp, if_neg (by rw [(hM.fixed p).mp hmir]; exact hp), hy0 p hmir]; ring
    · rw [if_neg hp, if_pos (hM.mem_of_notMem hp hmir), zero_add, hy p]

/-! ## 3. Necessity

Given `u`, build the odd vector agreeing with it on the half, its even twin, and — by §1 — the
mirror correction that kills the even twin's image on the mirror. The corrected even vector's
image is even and zero on the mirror, so §2 applies to it, the symmetric energy is exact, and
the estimate runs exactly as in `ReflectionConverse`.
-/

theorem mirrorDominated_of_reflectionPositive (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hm : m ≠ 0) (hrp : GraphReflection.ReflectionPositive G m θ H) :
    MirrorDominated G m θ H Mir := by
  classical
  intro u
  set N := massive G m with hN
  have hNpd : N.PosDef := massive_posDef G hm
  have hdet : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp hNpd.isUnit
  -- the odd vector agreeing with `u` on the half, and its even twin
  set ξ : V → ℝ := GraphReflection.anti θ (ReflectionConverse.cut H u) with hξdef
  have hξodd : IsOddFun θ ξ := ReflectionConverse.anti_isOdd h _
  have hξH : ∀ p ∈ H, ξ p = u p := fun p hp => by
    rw [hξdef, GraphReflection.anti, ReflectionConverse.cut_eq_self hp,
      ReflectionConverse.cut_eq_zero (hM.notMem_of_mem hp), sub_zero]
  set e : V → ℝ := evenify H ξ with hedef
  have heeven : IsEvenFun θ e := evenify_isEven hM hξodd
  -- §1: the correction that kills the image on the mirror
  obtain ⟨z, hzsupp, hzsol⟩ :=
    exists_mir_solution (G := G) (m := m) (Mir := Mir) hm (fun r => -(N *ᵥ e) r)
  set η : V → ℝ := e + z with hηdef
  have hzeven : IsEvenFun θ z := by
    intro p
    by_cases hp : p ∈ Mir
    · rw [(hM.fixed p).mp hp]
    · have hθp : θ p ∉ Mir := by
        intro hc
        have hfx : θ (θ p) = θ p := (hM.fixed _).mp hc
        rw [h.invol p] at hfx
        exact hp ((hM.fixed p).mpr hfx.symm)
      rw [hzsupp p hp, hzsupp (θ p) hθp]
  have hηeven : IsEvenFun θ η := fun p => by
    simp only [hηdef, Pi.add_apply, heeven p, hzeven p]
  -- its image is even and vanishes on the mirror
  set y : V → ℝ := N *ᵥ η with hydef
  have hyeven : IsEvenFun θ y := ReflectionConverse.mulVec_isEven h m hηeven
  have hy0 : ∀ r ∈ Mir, y r = 0 := by
    intro r hr
    have h1 : (N *ᵥ z) r = -(N *ᵥ e) r := hzsol r hr
    simp only [hydef, hηdef, Matrix.mulVec_add, Pi.add_apply, h1]
    ring
  -- so §2 applies and the symmetric energy is exact
  set c : V → ℝ := ReflectionConverse.cut H y with hcdef
  have hcsupp : ∀ p, p ∉ H → c p = 0 := fun p hp => ReflectionConverse.cut_eq_zero hp
  have hsym : GraphReflection.sym θ c = y := sym_cut_of_mir_zero hM hyeven hy0
  have hgreen : GraphLaplacian.green G m *ᵥ y = η := by
    rw [hydef, show GraphLaplacian.green G m = N⁻¹ from rfl,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hEsym : GraphReflection.energy G m (GraphReflection.sym θ c) = η ⬝ᵥ y := by
    rw [hsym, energy_eq_dotProduct, hgreen, dotProduct_comm]
  -- the odd side keeps the estimate
  have hEanti : 2 * (ξ ⬝ᵥ GraphReflection.anti θ c) - ξ ⬝ᵥ (N *ᵥ ξ)
      ≤ GraphReflection.energy G m (GraphReflection.anti θ c) := by
    rw [energy_eq_dotProduct]
    exact dotProduct_inv_le hNpd (GraphReflection.anti θ c) ξ
  -- the two linear terms agree, the mirror correction pairing to zero against `c`
  have hzc : z ⬝ᵥ c = 0 := by
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hp : p ∈ Mir
    · rw [hcsupp p (fun hc' => hM.disj p hc' hp), mul_zero]
    · rw [hzsupp p hp, zero_mul]
  have hpair : ξ ⬝ᵥ GraphReflection.anti θ c = η ⬝ᵥ y := by
    rw [dotProduct_anti hξodd c, ← hsym, dotProduct_sym hηeven c]
    have : η ⬝ᵥ c = ξ ⬝ᵥ c := by
      rw [hηdef, add_dotProduct, hzc, add_zero, hedef,
        dotProduct_evenify_eq hM hξodd (fun p hp _ => hcsupp p hp)]
    rw [this]
  -- reflection positivity, expanded
  have hrfl : 0 ≤ GraphReflection.reflectedForm G m θ c := hrp c hcsupp
  have hre := GraphReflection.reflectedForm_eq (m := m) h c
  have hkey : η ⬝ᵥ y ≤ ξ ⬝ᵥ (N *ᵥ ξ) := by
    rw [hEsym] at hre
    linarith [hEanti, hpair, hre, hrfl]
  -- expand the left side: `quadDiff` plus the two mirror terms
  have hsymN : ∀ x y', N x y' = N y' x :=
    fun x y' => congrFun (congrFun (GraphLaplacian.massive_isSymm G m) y') x
  have hcrossMir : ∀ r ∈ Mir, (N *ᵥ e) r = 2 * ∑ q ∈ H, N r q * ξ q :=
    fun r hr => MirrorDominance.mulVec_evenify_on_mir h hM hξodd hr
  have hzNe : z ⬝ᵥ (N *ᵥ e) = ∑ r ∈ Mir, ∑ q ∈ H, 2 * (ξ q * z r * N q r) := by
    rw [dotProduct, ← Finset.sum_subset (Finset.subset_univ Mir)
      (fun r _ hr => by rw [hzsupp r hr, zero_mul])]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [hcrossMir r hr, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [hsymN r q]; ring
  have hzNz : z ⬝ᵥ (N *ᵥ z) = ∑ r ∈ Mir, ∑ s ∈ Mir, z r * z s * N r s := by
    rw [dotProduct, ← Finset.sum_subset (Finset.subset_univ Mir)
      (fun r _ hr => by rw [hzsupp r hr, zero_mul])]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [← Finset.sum_subset (Finset.subset_univ Mir)
      (fun s _ hs => by rw [hzsupp s hs]; ring)]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hexpand : η ⬝ᵥ y = e ⬝ᵥ (N *ᵥ e) + 2 * (z ⬝ᵥ (N *ᵥ e)) + z ⬝ᵥ (N *ᵥ z) := by
    have hsym2 : e ⬝ᵥ (N *ᵥ z) = z ⬝ᵥ (N *ᵥ e) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y' _ => by
        rw [hsymN y' x]; ring
    simp only [hydef, hηdef, Matrix.mulVec_add, add_dotProduct, dotProduct_add, hsym2]
    ring
  have hqd : e ⬝ᵥ (N *ᵥ e) - ξ ⬝ᵥ (N *ᵥ ξ) = 4 * crossForm G m θ H ξ := by
    rw [hedef]; exact quadDiff hM hξodd
  -- read off the witness: `w = -z/2`
  refine ⟨fun p => -(1 / 2) * z p, fun p hp => by simp only [hzsupp p hp]; ring, ?_⟩
  have hcrossu : crossForm G m θ H ξ = crossForm G m θ H u := by
    simp only [crossForm]
    exact Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => by
      rw [hξH p hp, hξH q hq]
  have hE : ∑ p ∈ H, ∑ r ∈ Mir, u p * (-(1 / 2) * z r) * N p r
      = -(1 / 2) * ∑ r ∈ Mir, ∑ q ∈ H, (ξ q * z r * N q r) := by
    rw [Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p hp => by rw [hξH p hp]; ring
  have hD : ∑ r ∈ Mir, ∑ s ∈ Mir, (-(1 / 2) * z r) * (-(1 / 2) * z s) * N r s
      = (1 / 4) * ∑ r ∈ Mir, ∑ s ∈ Mir, z r * z s * N r s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hsum2 : ∑ r ∈ Mir, ∑ q ∈ H, 2 * (ξ q * z r * N q r)
      = 2 * ∑ r ∈ Mir, ∑ q ∈ H, (ξ q * z r * N q r) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [Finset.mul_sum]
  rw [← hcrossu, hE, hD]
  rw [hsum2] at hzNe
  rw [hexpand, hzNe, hzNz] at hkey
  linarith [hqd, hkey]

/-! ## 4. And so it is the criterion, on every graph with a mirror reflection -/

/-- **THE WALL'S CONVERSE QUESTION, CLOSED FOR A MIRROR HALF TOO.** `hcross` was the answer for
a fixed-point-free reflection (`ReflectionConverse`); this is the answer in general, and it
degenerates to `hcross` exactly when the fixed layer is empty. -/
theorem reflectionPositive_iff_mirrorDominated (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive G m θ H ↔ MirrorDominated G m θ H Mir :=
  ⟨mirrorDominated_of_reflectionPositive hM h hm,
   MirrorDominance.reflectionPositive_of_mirrorDominated hM h hm⟩

/-- **AND IT RECOVERS `ReflectionConverse` WHEN THERE IS NO FIXED LAYER**, which is the check
that the general statement is the same statement. -/
theorem reflectionPositive_iff_hcross_of_isHalf (hH : GraphHalfSpace.IsHalf θ H)
    (h : IsRefl G θ) (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive G m θ H ↔ ∀ w : V → ℝ, crossForm G m θ H w ≤ 0 :=
  (reflectionPositive_iff_mirrorDominated (isMirrorHalf_of_isHalf hH) h hm).trans
    MirrorDominance.mirrorDominated_iff_hcross_of_empty_mir

/-- **THE WITNESS, NOW DECIDED IN BOTH DIRECTIONS.** `MirrorConverseFails` proved `mirGraph`
reflection positive at `m = 1/2` and not at `m = 11`; §4 says the criterion tracks that exactly,
so it must fail at `m = 11`. Stated because a criterion that only ever certifies positivity has
not been tested. -/
theorem not_mirrorDominated_mirGraph_eleven :
    ¬ MirrorDominated MirrorConverseFails.mirGraph 11 MirrorConverseFails.tau
        MirrorConverseFails.Hm MirrorConverseFails.Mirm := by
  intro hdom
  exact MirrorConverseFails.not_reflectionPositive_eleven
    (MirrorDominance.reflectionPositive_of_mirrorDominated MirrorConverseFails.isMirrorHalf_Hm
      MirrorConverseFails.isRefl_tau (by norm_num) hdom)

end MirrorDominanceConverse
