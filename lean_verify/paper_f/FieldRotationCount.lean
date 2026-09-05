import FieldBoxRotation

/-!
# How many rotations? A circle's worth, and the count closes a fence five files carry

**Four files of this chain** — `FieldRotationInstance`, `FieldEigenGramSchmidt`,
`FieldCycleRotation`, `FieldBoxRotation` — end their *What is NOT here* section with the same
sentence: **no count of the rotations, every `(c, s)` on the unit circle gives one and nothing here
compares them.** This compares them. The number is **four** because they were counted and not
recalled: `FieldRotation` itself does not carry the sentence, and the first draft of this line said
*"every file from `FieldRotation` onward"* (`ERRATUM 450`, whose rule is that a claim about how many
files say something is a count).

**The comparison is one line of the estate's own vocabulary.** `FieldRotation.rotMatrix_mulVec_left`
already says `rotMatrix u v n c s *ᵥ u = c • u + s • v`. Two rotations that are equal as matrices
therefore send `u` to the same vector, and `u` and `v` are orthogonal and non-zero, so `c` and `s`
are read straight off. **The angle is recoverable from the matrix**, which is exactly what
"comparing them" needed and is why the fence was cheap rather than deep — recorded plainly because
`ERRATUM 454` is about fences that looked deeper than they were.

## What is proved

**`symmetryMatrices`** — the orthogonal matrices commuting with the propagator, as a `Set`.
`FieldOrthIsometry.gaussianField_map_orthIsometry` makes every member a symmetry of the Gaussian
field, and **`gaussianField_map_of_mem`** says so, so a statement about the size of this set is a
statement about the size of the symmetry group and not about matrices.
⚠ **CORRECTED 2026-09-05, and the sentence is kept as written** (`ERRATUM 94`, `ERRATUM 456`):
that last clause holds **downwards only**. Every member is a symmetry, so a lower bound on this set
is a lower bound on the symmetry group — which is all this file uses it for, and its conclusion
stands. **The set is not known to be all of the symmetry group**: that an orthogonal map fixing the
measure must commute with `green` is proved nowhere in this estate.
⚠ **AND THAT LAST SENTENCE IS ITSELF SUPERSEDED, two units later** (`ERRATUM 94`):
`FieldInvarianceCommutes.mem_symmetryMatrices_iff_gaussianField_map` proves it, so among orthogonal
matrices this set **is** the symmetry group and the original clause is now true as written. Both
annotations stay: each was right when made.

**`rotMatrix_inj`** — distinct `(c, s)` give distinct rotations, at any orthogonal pair of equal
non-zero length.

**`rotMatrix_injective`** and **`circle_injects_symmetryMatrices`** — **the unit circle injects
into `symmetryMatrices`.** That is what the title's *"a circle's worth"* means and all it means: an
injection *into* the set, saying nothing about what else the set contains.

**`infinite_symmetryMatrices_of_orthogonal_eigenpair`** — hence **the set is infinite** wherever the
propagator has an orthogonal eigenpair of equal length at one eigenvalue: `t ↦ rotMatrix u v n
(cos t) (sin t)` is injective on `(0, π)` because `Real.injOn_cos` is, and `(0, π)` is infinite.

**`infinite_symmetryMatrices_of_independent_eigenpair`** — and merely **independent** eigenvectors
suffice, by the same Gram–Schmidt-and-rescale composition
`FieldEigenGramSchmidt.exists_rotation_symmetry_of_independent_eigenpair` uses.

**`infinite_symmetryMatrices_box`** — **so the Gaussian field on `boxGraph d (n+1)` has infinitely
many symmetries at every `2 ≤ d`, every side length `≥ 2` and every `mass ≠ 0`** — the physical
`d = 4` included. The chain's headline until now was *a* rotation; it is a circle of them.

## What is NOT here

**No claim that the symmetry group is EXACTLY this.** `symmetryMatrices` is shown infinite by
exhibiting an infinite family inside it. **Nothing here bounds it from above, and no member outside
the family is excluded** — describing the commutant remains untouched, which is the fence this file
does *not* close. **Not attempted, no cost claimed** (`ERRATUM 246`).

**No cardinality**, only `Set.Infinite`. The family is the injective image of an interval, so
"continuum many" is within reach and is **not claimed**, because it is not proved here.

**No group structure.** `symmetryMatrices` is a `Set`, not a subgroup, and nothing here shows it is
closed under multiplication — true and easy, and still not proved, so not claimed.
⚠ **SUPERSEDED THE NEXT UNIT, kept as written** (`ERRATUM 94`): `FieldSymmetryGroup` proves the
group law and bundles it as a `Submonoid`. **A fence that calls the thing behind it easy is a debt,
and this one was paid within the hour.**

**Nothing about the torus at `d > 1`.** Still `TorusFibreOrbitPartition`'s orbits, still not
composed.
⚠ **SUPERSEDED 2026-09-05, kept as written** (`ERRATUM 94`, `ERRATUM 458`):
`FieldTorusRotation.exists_rotation_symmetry_torus` puts a rotation on the torus in **every**
dimension `d ≥ 1`, and needed no orbit bookkeeping at all —
`TorusEigenspaceLowerBound.two_pow_mul_multinomial_le_finrank`, in the estate since 2026-08-31,
bounds the degeneracy below with **no hypotheses**, and the all-ones frequency has every axis
interior. **The route this sentence names was never necessary.**

**No wall moves, and the count makes that sentence more important rather than less.** `W1`'s open
part is `OS0` and `OS4`, and `OS1` in its continuum sense. **An infinite finite-volume symmetry
group is a wider shadow of an axiom, not a smaller gap in it** — and a result that sounds larger is
exactly where that sentence is easiest to forget.

**And the mass hypothesis is part of every claim below** (`FieldMassNecessity`, `ERRATUM 455`): at
`mass = 0` the field is a point mass, every isometry preserves it, and "infinitely many symmetries"
would be true of every graph for no interesting reason.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldRotationCount

open Matrix GraphLaplacian FieldRotation FieldOrthIsometry FieldEigenGramSchmidt
open FieldRotationInstance BoxGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The symmetries, as a set -/

/-- **THE ORTHOGONAL MATRICES COMMUTING WITH THE PROPAGATOR.** Every one of them is a symmetry of
the Gaussian field, by `gaussianField_map_of_mem`. -/
def symmetryMatrices (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) : Set (Matrix V V ℝ) :=
  {R | Rᵀ * R = 1 ∧ R * green G m = green G m * R}

/-- **SO A COUNT OF THIS SET IS A COUNT OF SYMMETRIES OF THE FIELD**, not of matrices. -/
theorem gaussianField_map_of_mem (hm : m ≠ 0) {R : Matrix V V ℝ} (hR : R ∈ symmetryMatrices G m) :
    MeasureTheory.Measure.map (orthIsometry hR.1) (gaussianField G m) = gaussianField G m :=
  gaussianField_map_orthIsometry hm hR.1 hR.2

/-! ## 2. Distinct angles give distinct rotations -/

/-- **THE ANGLE IS RECOVERABLE FROM THE MATRIX**: `rotMatrix` sends `u` to `c • u + s • v`, and an
orthogonal pair of equal non-zero length reads `c` and `s` back off it. -/
theorem rotMatrix_inj {u v : V → ℝ} {n c s c' s' : ℝ} (hn : n ≠ 0)
    (huu : u ⬝ᵥ u = n) (hvv : v ⬝ᵥ v = n) (huv : u ⬝ᵥ v = 0)
    (h : rotMatrix u v n c s = rotMatrix u v n c' s') : c = c' ∧ s = s' := by
  have hvu : v ⬝ᵥ u = 0 := by rw [dotProduct_comm]; exact huv
  have hu := rotMatrix_mulVec_left (u := u) (v := v) (c := c) (s := s) hn huu hvu
  rw [h, rotMatrix_mulVec_left (u := u) (v := v) (c := c') (s := s') hn huu hvu] at hu
  have hdu := congrArg (fun w : V → ℝ => u ⬝ᵥ w) hu
  have hdv := congrArg (fun w : V → ℝ => v ⬝ᵥ w) hu
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, huu, huv, hvv, hvu, mul_zero,
    add_zero, zero_add] at hdu hdv
  exact ⟨(mul_right_cancel₀ hn hdu).symm, (mul_right_cancel₀ hn hdv).symm⟩

/-- **THE MAP FROM THE PLANE OF ANGLES IS INJECTIVE**, with no circle condition needed. -/
theorem rotMatrix_injective {u v : V → ℝ} {n : ℝ} (hn : n ≠ 0)
    (huu : u ⬝ᵥ u = n) (hvv : v ⬝ᵥ v = n) (huv : u ⬝ᵥ v = 0) :
    Function.Injective (fun p : ℝ × ℝ => rotMatrix u v n p.1 p.2) := by
  intro p q h
  obtain ⟨h1, h2⟩ := rotMatrix_inj hn huu hvv huv h
  exact Prod.ext h1 h2

theorem rotMatrix_mem_symmetryMatrices (hm : m ≠ 0) {u v : V → ℝ} {n c s μ : ℝ} (hn : n ≠ 0)
    (huu : u ⬝ᵥ u = n) (hvv : v ⬝ᵥ v = n) (huv : u ⬝ᵥ v = 0) (hcs : c ^ 2 + s ^ 2 = 1)
    (hu : green G m *ᵥ u = μ • u) (hv : green G m *ᵥ v = μ • v) :
    rotMatrix u v n c s ∈ symmetryMatrices G m :=
  ⟨rotMatrix_transpose_mul_self hn huu hvv huv hcs, rotMatrix_mul_green_comm hm hu hv⟩

/-- **SO THE UNIT CIRCLE INJECTS INTO THE SYMMETRIES.** This is what "a circle's worth" means
here, and it is all it means: an injection *into* the set, with nothing said about what else the
set contains. -/
theorem circle_injects_symmetryMatrices (hm : m ≠ 0) {u v : V → ℝ} {n μ : ℝ} (hn : n ≠ 0)
    (huu : u ⬝ᵥ u = n) (hvv : v ⬝ᵥ v = n) (huv : u ⬝ᵥ v = 0)
    (hu : green G m *ᵥ u = μ • u) (hv : green G m *ᵥ v = μ • v) :
    Function.Injective (fun p : ℝ × ℝ => rotMatrix u v n p.1 p.2) ∧
      (fun p : ℝ × ℝ => rotMatrix u v n p.1 p.2) '' {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = 1}
        ⊆ symmetryMatrices G m := by
  refine ⟨rotMatrix_injective hn huu hvv huv, ?_⟩
  rintro R ⟨p, hp, rfl⟩
  exact rotMatrix_mem_symmetryMatrices hm hn huu hvv huv hp hu hv

/-! ## 3. So there are infinitely many -/

/-- **INFINITELY MANY SYMMETRIES, WHEREVER THE PROPAGATOR HAS AN ORTHOGONAL EIGENPAIR OF EQUAL
LENGTH AT ONE EIGENVALUE.** -/
theorem infinite_symmetryMatrices_of_orthogonal_eigenpair (hm : m ≠ 0) {u v : V → ℝ} {n μ : ℝ}
    (hn : n ≠ 0) (huu : u ⬝ᵥ u = n) (hvv : v ⬝ᵥ v = n) (huv : u ⬝ᵥ v = 0)
    (hu : green G m *ᵥ u = μ • u) (hv : green G m *ᵥ v = μ • v) :
    (symmetryMatrices G m).Infinite := by
  have hinj : Set.InjOn (fun t : ℝ => rotMatrix u v n (Real.cos t) (Real.sin t))
      (Set.Ioo 0 Real.pi) := by
    intro a ha b hb hab
    exact Real.injOn_cos ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩
      (rotMatrix_inj hn huu hvv huv hab).1
  refine Set.Infinite.mono ?_ ((Set.Ioo_infinite Real.pi_pos).image hinj)
  rintro R ⟨t, -, rfl⟩
  exact rotMatrix_mem_symmetryMatrices hm hn huu hvv huv (Real.cos_sq_add_sin_sq t) hu hv

/-- **AND MERELY INDEPENDENT EIGENVECTORS SUFFICE**, by the composition
`FieldEigenGramSchmidt.exists_rotation_symmetry_of_independent_eigenpair` uses. -/
theorem infinite_symmetryMatrices_of_independent_eigenpair (hm : m ≠ 0) {u v : V → ℝ} {μ : ℝ}
    (hu0 : u ⬝ᵥ u ≠ 0) (hind : ∀ c : ℝ, v ≠ c • u)
    (hu : green G m *ᵥ u = μ • u) (hv : green G m *ᵥ v = μ • v) :
    (symmetryMatrices G m).Infinite := by
  have hw0 : gramSchmidt u v ⬝ᵥ gramSchmidt u v ≠ 0 :=
    FieldCycleRotation.dotProduct_self_ne_zero (gramSchmidt_ne_zero hind)
  obtain ⟨u', v', n, hn, hu'u', hv'v', hu'v', hu', hv'⟩ :=
    exists_equal_length_eigenpair (G := G) (m := m) hu0 hw0
      (dotProduct_gramSchmidt hu0 v) hu (gramSchmidt_eigen hu hv)
  exact infinite_symmetryMatrices_of_orthogonal_eigenpair hm hn hu'u' hv'v' hu'v' hu' hv'

/-! ## 4. On the box -/

/-- **THE GAUSSIAN FIELD ON THE BOX HAS INFINITELY MANY SYMMETRIES**, at every `2 ≤ d`, every side
length `≥ 2` and every `mass ≠ 0` — the physical `d = 4` included. -/
theorem infinite_symmetryMatrices_box {d n : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n) {mass : ℝ}
    (hmass : mass ≠ 0) :
    (symmetryMatrices (boxGraph d (n + 1)) mass).Infinite := by
  obtain ⟨u, v, μ, hu0, hind, hu, hv⟩ :=
    FieldBoxRotation.exists_independent_eigenpair_box_of_two_le hd hn hmass
  exact infinite_symmetryMatrices_of_independent_eigenpair hmass hu0 hind hu hv

end FieldRotationCount
