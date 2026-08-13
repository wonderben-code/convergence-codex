import LinkGraphOpen

/-!
# The wall's converse at a fixed mass

`CrossFormMatrix` §7 states the wall's remaining leg exactly:

> *"`hcross` is SUFFICIENT for reflection positivity … and `IndefiniteCoupling`
> `.hcross_necessary_for_positivity` shows it cannot be DELETED"* — but whether it is
> **necessary at a fixed mass** was left open, with two named consequences of a converse
> (`reflectionPositive_mass_independent_of_converse`, `not_converse_of_mass_dependent`).

Everything the estate has proved since then attacked that leg from the side. `GreenLargeMass`
§10 got the converse at **arbitrarily large** mass. `AdjSqForcesRegular` §7 got it at **every**
mass but only on the strongly regular graphs. `GreenDisconnected` got it on **disconnected**
graphs. `LinkGraphOpen` was written because those three exclusions left the question with no
concrete instance, and it named one — and then declined the finite computation that would
settle it, recording the decline in its own header: *"It is stated, not attempted."*

This file settles the leg itself, for every finite graph with a **fixed-point-free** reflection,
at **every** mass. The finite computation `LinkGraphOpen` declined is then a corollary and is
performed in §6.

## The argument

Nothing new is needed. Every ingredient has been sitting in `GraphMirrorReflection` since that
file was written to prove **sufficiency**; the converse is the same three lemmas read in the
other order.

Write `N` for the massive operator, `H` for the half. A vector `c` supported on `H` splits into
an even and an odd part, and `GraphReflection.reflectedForm_eq` says the reflected form is the
difference of their two energies, `⟪·, N⁻¹ ·⟫`. Now:

* **the odd side is estimated** by `dotProduct_inv_le` — completing the square, `⟪a, N⁻¹a⟫ ≥
  2⟪ξ,a⟫ − ⟪ξ,Nξ⟫` for every test vector `ξ`;
* **the even side is exact**, and this is the whole trick: choose `c` to be `N` applied to an
  even vector, cut down to the half. Because the reflection has **no fixed points**, cutting to
  the half and symmetrising are inverse to each other on even vectors (§2), so the symmetric
  part of `c` is *exactly* `N η` and its energy is *exactly* `⟪η, Nη⟫` — no estimate;
* **the difference of the two quadratic forms is the coupling**, by `quadDiff`.

Feeding the odd estimate the test vector `ξ` whose even twin is `η` makes the two linear terms
cancel identically (§4's pairing lemma), and what survives is `4·reflectedForm(c) ≤
−4·crossForm(w)`. A positive coupling therefore *produces* a refuting vector, at every mass.

`reflectionPositive_mirror` proves sufficiency by maximising `2⟪ξ,a⟫ − ⟪ξ,Nξ⟫` over `ξ` and
sign-flipping the maximiser. This file runs the same inequality backwards: it *chooses* the
test vector and *reads off* the loss. That is why no new analysis appears.

## Where the fixed-point-freeness is spent, and that it is FALSE without it

§2 is the only step that uses it, and it uses it twice over — a mirror layer would break both
directions of `sym_cut`. That is not an artefact of the write-up. With a fixed layer `Mir`, the
even sector of `N` couples `H` to `Mir`, the even energy acquires a Schur complement, and the
even side stops being exact. Sufficiency survives (`reflectionPositive_mirror` carries `Mir`
throughout, and the Schur correction only helps); necessity **fails**.

The hypothesis was not weakened to fit the proof: the proof was written first, and an
exhaustive rational search was then run to find out whether the hypothesis could be dropped.
It cannot. `MirrorConverseFails` exhibits a seven-vertex graph with `|H| = 2` and `|Mir| = 3`
that is reflection positive at `m = 1/2` and fails `hcross`. Seven vertices is the smallest
possible: every `σ`-invariant graph on four, five and six vertices was checked, at masses from
`10⁻³` to `50`, and every one of them obeys the equivalence.

That witness settles a second question the estate had left open. `CrossFormMatrix`
`.not_converse_of_mass_dependent` says a graph positive at one mass and not at another would
refute the converse; no such graph was known. This one is positive at `m² ≤ 1` and not at
`m² > 1`, so **reflection positivity is genuinely mass-dependent once the reflection has fixed
points** — and `reflectionPositive_mass_independent` below, which has no `Mir`, is sharp.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace ReflectionConverse

open Matrix GraphLaplacian GraphReflection GraphMirrorReflection

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H : Finset V}

/-! ## 1. Parity is preserved by the operator and by antisymmetrisation

Both facts are one line from `IsRefl`. `BoxOddNotStrict.mulVec_comp_refl` states the first for
an arbitrary graph while living in a file about the box; this is that fact with the evenness
already applied, which is the only form used here.
-/

/-- **THE MASSIVE OPERATOR PRESERVES EVENNESS.** The reflection is an automorphism, so it
commutes with the operator; an even vector therefore has an even image. -/
theorem mulVec_isEven (h : IsRefl G θ) (m : ℝ) {v : V → ℝ} (hv : IsEvenFun θ v) :
    IsEvenFun θ (massive G m *ᵥ v) := by
  intro p
  have hM : ∀ x y, massive G m (θ x) (θ y) = massive G m x y :=
    fun x y => congrFun (congrFun (h.massive m) x) y
  simp only [Matrix.mulVec, dotProduct]
  rw [← Fintype.sum_equiv θ (fun q => massive G m (θ p) (θ q) * v (θ q))
    (fun q => massive G m (θ p) q * v q) (fun _ => rfl)]
  exact Finset.sum_congr rfl fun q _ => by rw [hM p q, hv q]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **ANTISYMMETRISATION PRODUCES AN ODD VECTOR.** Involutivity, and nothing else. -/
theorem anti_isOdd (h : IsRefl G θ) (c : V → ℝ) : IsOddFun θ (GraphReflection.anti θ c) := by
  intro p
  simp only [GraphReflection.anti, h.invol p]
  ring

/-! ## 2. Cutting to the half inverts symmetrisation — and only without a mirror

`GraphReflection.sym` doubles up an arbitrary vector across the reflection. On an **even**
vector, restricting to the half and then symmetrising gets the vector back. Both directions of
the case split below use `IsHalf`: on the half because `θ p` is off it, off the half because
`θ p` is on it. A fixed point would satisfy neither, and this is where a mirror layer would
enter.
-/

/-- Restriction to the half, extended by zero. -/
def cut (H : Finset V) (y : V → ℝ) : V → ℝ := fun p => if p ∈ H then y p else 0

omit [Fintype V] in
theorem cut_eq_zero {y : V → ℝ} {p : V} (hp : p ∉ H) : cut H y p = 0 := if_neg hp

omit [Fintype V] in
theorem cut_eq_self {y : V → ℝ} {p : V} (hp : p ∈ H) : cut H y p = y p := if_pos hp

omit [Fintype V] in
/-- **THE INVERSION.** On an even vector, cutting to the half and symmetrising is the identity.
    This is the step, and the only step, that a fixed point would break. -/
theorem sym_cut (hH : GraphHalfSpace.IsHalf θ H) {y : V → ℝ} (hy : IsEvenFun θ y) :
    GraphReflection.sym θ (cut H y) = y := by
  funext p
  simp only [GraphReflection.sym, cut]
  by_cases hp : p ∈ H
  · rw [if_pos hp, if_neg (hH.notMem_of_mem hp), add_zero]
  · rw [if_neg hp, if_pos (hH.mem_of_notMem hp), zero_add, hy p]

/-! ## 3. The refuting vector

Given any `w`, the construction is forced by the two requirements of §4: the vector fed to
reflection positivity must be supported on the half, and its symmetric part must be `N` applied
to something even. `cut` and `sym_cut` are exactly the pair that makes both hold at once.
-/

/-- **THE REFUTING VECTOR.** Antisymmetrise `w` off the half, flip the sign back to get its even
twin, apply the operator, and cut to the half. `refuter` is supported on the half by
construction, and §4 shows its reflected form is at most `−crossForm w`. -/
noncomputable def refuter (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (θ : V ≃ V)
    (H : Finset V) (w : V → ℝ) : V → ℝ :=
  cut H (massive G m *ᵥ evenify H (GraphReflection.anti θ (cut H w)))

theorem refuter_supported (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (θ : V ≃ V)
    (H : Finset V) (w : V → ℝ) {p : V} (hp : p ∉ H) : refuter G m θ H w p = 0 :=
  cut_eq_zero hp

/-! ## 4. The estimate

One inequality — `dotProduct_inv_le` on the odd side — and three identities. The identities are
`sym_cut` (the even side is exact), `dotProduct_anti`/`dotProduct_sym`/`dotProduct_evenify_eq`
(the linear terms agree), and `quadDiff` (the quadratic terms differ by the coupling).
-/

/-- **A POSITIVE COUPLING COSTS EXACTLY WHAT IT IS WORTH.** The refuting vector's reflected form
is at most minus the coupling — an inequality in one direction only, because the odd side is
estimated, but with the *same constant* as `quadDiff`'s identity. -/
theorem reflectedForm_refuter_le (hH : GraphHalfSpace.IsHalf θ H) (h : IsRefl G θ)
    (hm : m ≠ 0) (w : V → ℝ) :
    4 * GraphReflection.reflectedForm G m θ (refuter G m θ H w)
      ≤ -(4 * crossForm G m θ H w) := by
  classical
  have hNpd : (massive G m).PosDef := massive_posDef G hm
  have hMH : IsMirrorHalf θ H (∅ : Finset V) := isMirrorHalf_of_isHalf hH
  -- the odd vector agreeing with `w` on the half, its even twin, and the operator's image
  set ξ : V → ℝ := GraphReflection.anti θ (cut H w) with hξdef
  have hξodd : IsOddFun θ ξ := anti_isOdd h _
  set η : V → ℝ := evenify H ξ with hηdef
  have hηeven : IsEvenFun θ η := evenify_isEven hMH hξodd
  set y : V → ℝ := massive G m *ᵥ η with hydef
  have hyeven : IsEvenFun θ y := mulVec_isEven h m hηeven
  set c : V → ℝ := cut H y with hcdef
  have hcsupp : ∀ p, p ∉ H → p ∉ (∅ : Finset V) → c p = 0 := fun p hp _ => cut_eq_zero hp
  have hsym : GraphReflection.sym θ c = y := sym_cut hH hyeven
  have hrefuter : refuter G m θ H w = c := rfl
  -- (a) the even side is exact
  have hgreen : GraphLaplacian.green G m *ᵥ y = η := by
    rw [hydef, show GraphLaplacian.green G m = (massive G m)⁻¹ from rfl,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
        ((Matrix.isUnit_iff_isUnit_det _).mp hNpd.isUnit), Matrix.one_mulVec]
  have hEsym : GraphReflection.energy G m (GraphReflection.sym θ c) = η ⬝ᵥ y := by
    rw [hsym, energy_eq_dotProduct, hgreen, dotProduct_comm]
  -- (b) the two linear terms agree
  have hpair : ξ ⬝ᵥ GraphReflection.anti θ c = η ⬝ᵥ y := by
    rw [dotProduct_anti hξodd c, ← hsym, dotProduct_sym hηeven c,
      dotProduct_evenify_eq hMH hξodd hcsupp]
  -- (c) the odd side is estimated
  have hEanti : 2 * (ξ ⬝ᵥ GraphReflection.anti θ c) - ξ ⬝ᵥ (massive G m *ᵥ ξ)
      ≤ GraphReflection.energy G m (GraphReflection.anti θ c) := by
    rw [energy_eq_dotProduct]
    exact dotProduct_inv_le hNpd (GraphReflection.anti θ c) ξ
  -- (d) the quadratic forms differ by the coupling
  have hQ : η ⬝ᵥ y - ξ ⬝ᵥ (massive G m *ᵥ ξ) = 4 * crossForm G m θ H ξ := by
    rw [hydef, hηdef]; exact quadDiff hMH hξodd
  -- (e) the coupling only reads the half, where `ξ` is `w`
  have hcross : crossForm G m θ H ξ = crossForm G m θ H w := by
    have hval : ∀ p ∈ H, ξ p = w p := fun p hp => by
      rw [hξdef, GraphReflection.anti, cut_eq_self hp, cut_eq_zero (hH.notMem_of_mem hp), sub_zero]
    simp only [crossForm]
    exact Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => by
      rw [hval p hp, hval q hq]
  rw [hrefuter, GraphReflection.reflectedForm_eq h c, hEsym]
  rw [hcross] at hQ
  linarith [hEanti, hpair, hQ]

/-! ## 5. The converse, and the three things it settles at once -/

/-- **THE WALL'S CONVERSE, AT A FIXED MASS, ON EVERY GRAPH.** No regularity, no connectivity, no
threshold, no `A²` identity — only that the reflection has no fixed points. -/
theorem hcross_of_reflectionPositive (hH : GraphHalfSpace.IsHalf θ H) (h : IsRefl G θ)
    (hm : m ≠ 0) (hrp : GraphReflection.ReflectionPositive G m θ H) (w : V → ℝ) :
    crossForm G m θ H w ≤ 0 := by
  by_contra hcon
  have hw : 0 < crossForm G m θ H w := not_le.mp hcon
  have hpos : 0 ≤ GraphReflection.reflectedForm G m θ (refuter G m θ H w) :=
    hrp _ (fun p hp => refuter_supported G m θ H w hp)
  linarith [reflectedForm_refuter_le hH h hm w]

/-- **AND SO IT IS AN EQUIVALENCE.** Sufficiency is `reflectionPositive_mirror`, which has
carried a mirror layer since it was written; necessity is §4. -/
theorem reflectionPositive_iff_hcross (hH : GraphHalfSpace.IsHalf θ H) (h : IsRefl G θ)
    (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive G m θ H ↔ ∀ w : V → ℝ, crossForm G m θ H w ≤ 0 :=
  ⟨fun hrp w => hcross_of_reflectionPositive hH h hm hrp w,
   fun hc _ hsupp =>
     reflectionPositive_mirror (isMirrorHalf_of_isHalf hH) h hm hc
       (fun p hp _ => hsupp p hp)⟩

/-- **REFLECTION POSITIVITY IS COMBINATORIAL.** `CrossBlockStructure.IsCrossBlock` mentions
neither the mass nor a single vector: every half-site with a cut neighbour is joined to the
mirror image of every other such site in its class. -/
theorem reflectionPositive_iff_isCrossBlock (hH : GraphHalfSpace.IsHalf θ H) (h : IsRefl G θ)
    (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive G m θ H
      ↔ CrossBlockStructure.IsCrossBlock G θ H :=
  (reflectionPositive_iff_hcross hH h hm).trans
    (CrossBlockStructure.hcross_iff_isCrossBlock (isMirrorHalf_of_isHalf hH) h m)

/-- **AND SO IT IS DECIDABLE**, at a fixed mass, on any graph with decidable adjacency. This is
what `GreenLargeMass.decidableLargeMassRP` could only say about the large-mass limit. -/
def decidableReflectionPositive (hH : GraphHalfSpace.IsHalf θ H) (h : IsRefl G θ) (hm : m ≠ 0) :
    Decidable (GraphReflection.ReflectionPositive G m θ H) :=
  decidable_of_iff _ (reflectionPositive_iff_isCrossBlock hH h hm).symm

/-- **THE FIRST NAMED CONSEQUENCE, DISCHARGED.** `CrossFormMatrix.reflectionPositive_mass_-`
`independent_of_converse` derived mass-independence *from* a converse it did not have. -/
theorem reflectionPositive_mass_independent (hH : GraphHalfSpace.IsHalf θ H) (h : IsRefl G θ)
    {m m' : ℝ} (hm : m ≠ 0) (hm' : m' ≠ 0) :
    GraphReflection.ReflectionPositive G m θ H ↔ GraphReflection.ReflectionPositive G m' θ H :=
  (reflectionPositive_iff_isCrossBlock hH h hm).trans
    (reflectionPositive_iff_isCrossBlock hH h hm').symm

/-- **THE SECOND, CONTRAPOSED.** `CrossFormMatrix.not_converse_of_mass_dependent` said a graph
that is reflection positive at one mass and not at another would refute the converse. §5 says
no such graph exists, so the estate may stop looking for one. -/
theorem no_mass_dependent_example (hH : GraphHalfSpace.IsHalf θ H) (h : IsRefl G θ)
    {m m' : ℝ} (hm : m ≠ 0) (hm' : m' ≠ 0) :
    ¬ (GraphReflection.ReflectionPositive G m θ H
        ∧ ¬ GraphReflection.ReflectionPositive G m' θ H) := by
  rintro ⟨h1, h2⟩
  exact h2 ((reflectionPositive_mass_independent hH h hm hm').mp h1)

/-- **THE THRESHOLD WAS ALWAYS AN ARTEFACT.** `GreenLargeMass` §10 proved that reflection
positivity at arbitrarily large mass is equivalent to `hcross`; §5 says the qualifier
`arbitrarily large` may be deleted whenever the reflection is fixed-point-free. -/
theorem reflectionPositive_of_arbitrarily_large (hH : GraphHalfSpace.IsHalf θ H)
    (h : IsRefl G θ) (hm : m ≠ 0)
    (hbig : ∀ M : ℝ, ∃ m' : ℝ, M < m' ∧ m' ≠ 0
      ∧ GraphReflection.ReflectionPositive G m' θ H) :
    GraphReflection.ReflectionPositive G m θ H := by
  obtain ⟨m', _, hm'0, hm'⟩ := hbig 0
  exact (reflectionPositive_mass_independent hH h hm'0 hm).mp hm'

/-! ## 6. The computation `LinkGraphOpen` declined

That file's header names exactly what it did not do — *"whether it is reflection positive at
small mass … is a finite computation on six vertices that nothing here performs"* — and its
last theorem lists the three exclusions that left the question open. §5 needs none of them: it
needs only that `σ : p ↦ p + 3` has no fixed point on `Fin 6`, and the coupling is already
known to be positive at `us`.
-/

/-- `Hs` is a fixed-point-free half for `sigma6`, which is all §5 asks of it. -/
theorem isHalf_Hs : GraphHalfSpace.IsHalf GreenLargeMass.sigma6 GreenLargeMass.Hs := by
  intro p
  fin_cases p <;> decide

/-- **`linkGraph` IS NOT REFLECTION POSITIVE AT ANY MASS.** `LinkGraphOpen` got `m² > 100` and
stopped; the threshold is gone, and with it the last concrete instance of the open question. -/
theorem linkGraph_not_reflectionPositive {m : ℝ} (hm : m ≠ 0) :
    ¬ GraphReflection.ReflectionPositive LinkGraphOpen.linkGraph m
        GreenLargeMass.sigma6 GreenLargeMass.Hs := by
  intro hrp
  have := hcross_of_reflectionPositive isHalf_Hs LinkGraphOpen.isRefl_sigma6_link hm hrp
    GreenLargeMass.us
  rw [LinkGraphOpen.crossForm_link_pos] at this
  norm_num at this

/-- **A CROSS-CHECK, NOT A NEW THEOREM.** `StepGraphSmallMass.stepGraph_not_reflectionPositive`
already has this, by computing all six columns of the Green function by hand and evaluating the
reflected form. §5 reaches the same conclusion from one positive coupling and no inverse at all.
Recorded because the two routes share no lemma below `crossForm`, so agreement is evidence. -/
theorem stepGraph_not_reflectionPositive_second_route {m : ℝ} (hm : m ≠ 0) :
    ¬ GraphReflection.ReflectionPositive GreenLargeMass.stepGraph m
        GreenLargeMass.sigma6 GreenLargeMass.Hs := by
  intro hrp
  have := hcross_of_reflectionPositive isHalf_Hs GreenLargeMass.isRefl_sigma6 hm hrp
    GreenLargeMass.us
  rw [GreenLargeMass.crossForm_step_pos] at this
  norm_num at this

end ReflectionConverse
