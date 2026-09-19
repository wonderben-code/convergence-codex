import FieldSymmetryContinuum
import FieldTorusRotation

/-!
# Which infinity on the ISOMETRIC side: finite, or exactly the continuum, and nothing between

**`FieldSymmetryContinuum` computed the LINEAR side's cardinal and left the isometric one open in
as many words** (2026-09-19, `ERRATUM 654`). This file closes it, and closes it as a **dichotomy**
rather than a lower bound: the Gaussian field's isometric symmetry group — the orthogonal
matrices commuting with the propagator — is **either finite or exactly `𝔠`**, and the two cases
are separated by the same criterion that separates finite from infinite. Nothing lies between, and
no hypothesis beyond `mass ≠ 0` is needed anywhere.

## What is proved

**`mk_symmetryMatrices_eq_continuum_iff`** — `#(symmetryMatrices G m) = 𝔠` **if and only if the
propagator's spectrum is degenerate**. Both directions are short once the right pieces are named.
*Forward*: at a simple spectrum `FieldSymmetryFinite.finite_symmetryMatrices_of_injective` makes
the set finite, so its cardinal is below `ℵ₀` and cannot be `𝔠`. *Backward*: a repeated
eigenvalue gives an eigenspace of dimension two, hence a circle of rotations in the plane of an
eigenpair, and `FieldSymmetryContinuum.continuum_le_of_injOn` reads that circle for its
cardinality; the upper bound is the ambient matrix space, which is `𝔠` by
`FieldSymmetryContinuum.mk_matrix`.

**`mk_symmetryMatrices_of_independent_eigenpair`** — the same from two independent eigenvectors at
one eigenvalue, with no criterion in the way. This is the form every consumer below and outside
actually wants, and it needs no `[Nonempty V]`: a vector of non-zero squared length is already a
witness that the index type is inhabited (`nonempty_of_dotProduct_self_ne_zero`).

**`mk_symmetryMatrices_eq_continuum_iff_lapMatrix`** — the same in graph vocabulary, with no
propagator on either side: the symmetries are the continuum exactly when the Laplacian has an
eigenvalue of multiplicity two or more. This is `FieldBlockInfinite`'s criterion with `Infinite`
replaced by a cardinal.

**`mk_symmetryMatrices_lt_aleph0_or_eq_continuum`** — **the dichotomy with no criterion in it at
all**: at every finite graph and every non-zero mass the symmetry set is finite or has cardinality
exactly `𝔠`. It is CH-free — both alternatives are pinned, and nothing is said about what lies
between `ℵ₀` and `𝔠`.

**`mk_prod_unitaryGroup_eq_continuum_iff`, `mk_prod_unitaryGroup_of_two_le_card_fib`,
`mk_prod_unitaryGroup_lt_aleph0_or_eq_continuum`, `mk_symmetrySubmonoid_eq_continuum_iff`,
`mk_blockDiagSubmonoid_eq_continuum_iff`** — **the same statements on the other four objects this
cluster names**: the product `∀ c, O(Fib c)` over the propagator's distinct eigenvalues, the
bundled `symmetrySubmonoid`, and `FieldBlockGroup`'s `blockDiagSubmonoid`. They are transports
across `FieldBlockProduct.symmetry_mulEquiv_prod` and `FieldBlockGroup.conjEigEquiv`, both
`MulEquiv`s and therefore bijections, plus `submonoidEquivSet`, which says the submonoid and the
set are the same type. **Each is stated on its own object rather than left to a reader to
transport**, which is `ERRATUM 653`'s rule applied deliberately for once.

**`mk_symmetryMatrices_torus`** — **and on the torus, in every dimension `d ≥ 1`, at every side
length and every non-zero mass**, the physical `d = 4` included:
`FieldTorusRotation.exists_independent_eigenpair_torus` feeds the independent-eigenpair form
directly, and it is the same input `FieldTorusRotation.infinite_symmetryMatrices_torus` takes.

**`FieldEigenGramSchmidt.exists_equal_length_eigenpair_of_independent`** — not in this file, but
exported by this unit, with both of its previous consumers rewired. See below.

## The route this file did NOT take, and the one it took instead

`UNLOCK_WATCHLIST` item `L42705` named the route as *the same circle taken inside a block rather
than in the plane of two coordinate vectors*. **That is not what happens here.** No circle is
constructed inside a block, no block is decomposed, and `Fib` appears only in statements. The
circle is taken in the AMBIENT space, in the plane of an eigenpair at a repeated eigenvalue, where
`FieldRotationCount.rotMatrix_mem_symmetryMatrices` has put it since 5 September; the other four
objects' cardinals then come across the two `MulEquiv`s for free.

**That is the item's FOURTH wrong estimate about its own residues and its SECOND wrong route**
(`ERRATUM 194`): residue (1)'s route was wrong, residue (2)'s count was wrong, residue (3) was
wrongly called *not a rung*, and residue (3)'s re-scoped route is wrong here. The item is not
careless — it is the most carefully written item in the watchlist. **Naming a route is simply not
costing it**, and four misses on one item is the evidence.

## What this unit found on the way

**TWO THINGS, AND BOTH ARE COUNTS THAT WERE RECALLED RATHER THAN MADE** (`ERRATUM 450`).

**One.** The composition *independent eigenpair → orthogonal eigenpair of equal length* was
written out **twice** and named nowhere, in `FieldEigenGramSchmidt` and in `FieldRotationCount`.
That is `ERRATUM 653`'s shape — something true, used, and unreachable by name — and by the
watchlist item's own reckoning the **fourth** instance of it in this cluster. It is now
`FieldEigenGramSchmidt.exists_equal_length_eigenpair_of_independent`, both consumers call it, and
this file is the third.

**Two.** `FieldSymmetryContinuum`'s header and `ERRATUM 654` both say **seven** files carry the
*which infinity* refusal. Counted with newlines flattened **and the interpolated word *still*
allowed**, it is **eight**: `FieldAffineGroup` carries one, inserted by unit 125's own note the day
before, and unit 128's grep could not see it because it searched for the exact string
`Infinite` *is not a cardinal* and the sentence reads `Infinite` *is still not a cardinal*. Its
subject is the LINEAR side, so **unit 128 discharged it without knowing** and understated what it
closed. `ERRATUM 655`.

## What this closes, and in what words

**SIX SENTENCES IN SIX FILES, EACH ON ITS OWN OBJECT**, and each file carries a dated note rather
than a pointer to a theorem about something else (`ERRATUM 651` allows one note where the item
lives; `ERRATUM 94` requires one where the file's own claim is overtaken, and these are the
latter). `CompleteFieldSymmetry`, `FieldSymmetryFinite` and `MultipartiteEigenspace` say
*nothing about which infinity* of `symmetryMatrices`, which `mk_symmetryMatrices_eq_continuum_iff`
answers at every graph. `FieldBlockProduct` says it of the product and `FieldBlockGroup` of the
block-diagonal group, which have their own statements here. `FieldBlockInfinite`, which owns the
watchlist item, says it of all three.

**AND `FieldTorusRotation`'s *no exact count on the torus*, which said `Set.Infinite` was the
right answer rather than a missing one.** It was the right answer for three weeks and it is not
any more.

## What is NOT here

**NO CARDINAL FOR A SINGLE BLOCK.** `#(O(Fib c))` for one fibre is not stated. It is `𝔠` when the
fibre has two or more points and finite otherwise, by `FieldSymmetryContinuum.mk_unitaryGroup` on
a `Nontrivial` index type, and **this file does not restate it on `Fib`** because the product is
what the item asked for. **Not attempted here, 2026-09-19**, no cost claimed (`ERRATUM 246`).
⚠ **STATED THE SAME DAY, AND THIS PARAGRAPH IS KEPT AS WRITTEN** (`ERRATUM 94`).
`FieldFibreCardinal.mk_unitaryGroup_fib_eq_continuum_iff` is exactly the restatement on `Fib`,
with `2 ≤ Fintype.card (Fib d c)` in place of `[Nontrivial]`, at an arbitrary level function and
an arbitrary real level, attained or not; and
`FieldFibreCardinal.mk_prod_unitaryGroup_eq_continuum_iff_exists_factor` makes this file's
product theorem and that fibre theorem **one fact**: the product is `𝔠` if and only if some
single factor is. **The paragraph's *not attempted* was accurate when written and lasted one
unit**, which is the shortest interval in this cluster and is recorded rather than tidied away.

**NO FORMULA, AND A DICHOTOMY IS NOT A COUNT.** When the group is finite the count is `2 ^ |V|`
(`FieldSymmetryFinite.card_of_finite`); when it is infinite the cardinal is `𝔠`. **Neither is a
formula in the multiplicities**, and the six sentences above are answered in the sense of
cardinality and **not** in the sense of a size that varies with the graph. The block structure
`∀ c, O(d_c)` is in the estate (`symmetry_mulEquiv_prod`) and **nothing here computes anything
from the `d_c`** — which is exactly why the cardinal is the same at every degenerate graph.

**NOTHING ABOUT TOPOLOGY, DIMENSION OR MEASURE.** `𝔠` is a set-theoretic count. That `O(n)` is a
compact Lie group of dimension `n(n-1)/2`, that the symmetry group carries a Haar measure, that the
circle inside it is a closed subgroup — **none of that is in this estate at all**, and a cardinal
is evidence for none of it (2026-09-19).

**THE STATEMENTS ARE IN UNIVERSE 0, AND THAT IS FORCED.** `Cardinal.continuum` is a `Cardinal.{0}`,
so none of this typechecks for `V : Type*`; it would be about `lift 𝔠`, a different statement.
This file takes `V : Type`, as `FieldSymmetryContinuum` does and for the same reason. **The
general-universe form is not attempted by this file, 2026-09-19** (`ERRATUM 246`).

**NO WALL MOVES.** `W1`'s open part is `OS0`, `OS4`, and `OS1` in its continuum sense — a sense
this file's `continuum` has nothing to do with. The collision of words is worth one sentence so
nobody reads a wall as having moved.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldBlockContinuum

open Matrix GraphLaplacian FieldRotation FieldRotationCount FieldSymmetryGroup
open FieldBlockDiagonal FieldBlockProduct Cardinal

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. A vector of non-zero length needs somewhere to live -/

omit [DecidableEq V] in
/-- A non-zero squared length is already a witness that the index type is inhabited: on an empty
type every dot product is the empty sum. This is what saves a `[Nonempty V]` hypothesis on
everything below. -/
theorem nonempty_of_dotProduct_self_ne_zero {u : V → ℝ} (h : u ⬝ᵥ u ≠ 0) : Nonempty V := by
  rcases isEmpty_or_nonempty V with hV | hV
  · haveI := hV
    exact absurd (show u ⬝ᵥ u = 0 by simp [dotProduct]) h
  · exact hV

/-! ## 2. A circle inside an eigenspace is already a continuum of symmetries -/

/-- **THE CIRCLE OF ROTATIONS IN AN ORTHOGONAL EIGENPAIR'S PLANE HAS CARDINALITY `𝔠`**, and it
lies inside the symmetries. This is
`FieldRotationCount.infinite_symmetryMatrices_of_orthogonal_eigenpair` with `Set.Infinite`
replaced by a cardinal at each step: the same injectivity, the same membership, and
`FieldSymmetryContinuum.continuum_le_of_injOn` in place of `Set.Infinite.mono`. -/
theorem continuum_le_mk_symmetryMatrices (hm : m ≠ 0) {u v : V → ℝ} {n μ : ℝ} (hn : n ≠ 0)
    (huu : u ⬝ᵥ u = n) (hvv : v ⬝ᵥ v = n) (huv : u ⬝ᵥ v = 0)
    (hu : green G m *ᵥ u = μ • u) (hv : green G m *ᵥ v = μ • v) :
    𝔠 ≤ #(symmetryMatrices G m) := by
  refine FieldSymmetryContinuum.continuum_le_of_injOn
    (f := fun t : ℝ => rotMatrix u v n (Real.cos t) (Real.sin t)) ?_ ?_
  · intro a ha b hb hab
    exact Real.injOn_cos ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩
      (rotMatrix_inj hn huu hvv huv hab).1
  · rintro R ⟨t, -, rfl⟩
    exact rotMatrix_mem_symmetryMatrices hm hn huu hvv huv (Real.cos_sq_add_sin_sq t) hu hv

/-! ## 3. The set of symmetries: finite, or exactly `𝔠` -/

/-- **TWO INDEPENDENT EIGENVECTORS AT ONE EIGENVALUE MAKE THE SYMMETRIES THE CONTINUUM.** Below by
the circle in their plane, above by the ambient matrix space. The pair is made orthogonal and of
equal length by `FieldEigenGramSchmidt.exists_equal_length_eigenpair_of_independent`, exported by
this unit, and `Nonempty V` comes from the pair rather than being assumed. -/
theorem mk_symmetryMatrices_of_independent_eigenpair (hm : m ≠ 0) {u v : V → ℝ} {μ : ℝ}
    (hu0 : u ⬝ᵥ u ≠ 0) (hind : ∀ c : ℝ, v ≠ c • u)
    (hu : green G m *ᵥ u = μ • u) (hv : green G m *ᵥ v = μ • v) :
    #(symmetryMatrices G m) = 𝔠 := by
  obtain ⟨u', v', n, hn, hu'u', hv'v', hu'v', hu', hv'⟩ :=
    FieldEigenGramSchmidt.exists_equal_length_eigenpair_of_independent (G := G) (m := m)
      hu0 hind hu hv
  have hu'0 : u' ⬝ᵥ u' ≠ 0 := by rw [hu'u']; exact hn
  haveI : Nonempty V := nonempty_of_dotProduct_self_ne_zero hu'0
  refine le_antisymm ((mk_set_le _).trans (le_of_eq FieldSymmetryContinuum.mk_matrix)) ?_
  exact continuum_le_mk_symmetryMatrices hm hn hu'u' hv'v' hu'v' hu' hv'

/-- **AND FROM AN EIGENSPACE OF DIMENSION TWO**, which is the form the criteria below are stated
in. `FieldCycleRotation.exists_independent_of_two_le_finrank` is the only step. -/
theorem mk_symmetryMatrices_of_two_le_finrank (hm : m ≠ 0) {μ : ℝ}
    (h : 2 ≤ Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (green G m) - μ • LinearMap.id))) :
    #(symmetryMatrices G m) = 𝔠 := by
  obtain ⟨u, hu, v, hv, hu0, hind⟩ := FieldCycleRotation.exists_independent_of_two_le_finrank h
  exact mk_symmetryMatrices_of_independent_eigenpair hm
    (FieldCycleRotation.dotProduct_self_ne_zero hu0) hind
    ((FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).1 hu)
    ((FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).1 hv)

/-- **THE SAME FROM A REPEATED EIGENVALUE OF THE PROPAGATOR**, through
`FieldSymmetryFinite.exists_two_le_finrank_of_not_injective`. -/
theorem mk_symmetryMatrices_of_not_injective (hm : m ≠ 0)
    (h : ¬ Function.Injective (eigMu G m hm)) :
    #(symmetryMatrices G m) = 𝔠 := by
  obtain ⟨μ, hμ⟩ := FieldSymmetryFinite.exists_two_le_finrank_of_not_injective hm h
  exact mk_symmetryMatrices_of_two_le_finrank hm hμ

/-- **THE SYMMETRIES HAVE THE CARDINALITY OF THE CONTINUUM IF AND ONLY IF THE SPECTRUM IS
DEGENERATE.** The forward direction is the finite half: a finite set has cardinal below `ℵ₀`, and
`ℵ₀ ≤ 𝔠`. -/
theorem mk_symmetryMatrices_eq_continuum_iff (hm : m ≠ 0) :
    #(symmetryMatrices G m) = 𝔠 ↔ ¬ Function.Injective (eigMu G m hm) := by
  refine ⟨fun hc hinj => ?_, mk_symmetryMatrices_of_not_injective hm⟩
  haveI := (FieldSymmetryFinite.finite_symmetryMatrices_of_injective hm hinj).to_subtype
  have hlt : #(symmetryMatrices G m) < ℵ₀ := Cardinal.lt_aleph0_of_finite _
  rw [hc] at hlt
  exact absurd hlt (not_lt.2 aleph0_le_continuum)

/-- **AND IN GRAPH VOCABULARY, WITH NO PROPAGATOR ON EITHER SIDE**: the symmetries are the
continuum exactly when some eigenspace of the Laplacian is more than a line. -/
theorem mk_symmetryMatrices_eq_continuum_iff_lapMatrix (hm : m ≠ 0) :
    #(symmetryMatrices G m) = 𝔠 ↔ ∃ ν : ℝ, 1 < Module.finrank ℝ
      (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) := by
  rw [mk_symmetryMatrices_eq_continuum_iff hm]
  exact (FieldBlockInfinite.infinite_symmetryMatrices_iff_not_injective hm).symm.trans
    (FieldBlockInfinite.infinite_symmetryMatrices_iff_lapMatrix hm)

/-- **THE DICHOTOMY, WITH NO CRITERION IN IT**: at every finite graph and every non-zero mass the
symmetry set is finite or has cardinality exactly `𝔠`. Nothing lies between, and this says
nothing about what lies between `ℵ₀` and `𝔠` in general. -/
theorem mk_symmetryMatrices_lt_aleph0_or_eq_continuum (hm : m ≠ 0) :
    #(symmetryMatrices G m) < ℵ₀ ∨ #(symmetryMatrices G m) = 𝔠 := by
  by_cases h : Function.Injective (eigMu G m hm)
  · haveI := (FieldSymmetryFinite.finite_symmetryMatrices_of_injective hm h).to_subtype
    exact Or.inl (Cardinal.lt_aleph0_of_finite _)
  · exact Or.inr (mk_symmetryMatrices_of_not_injective hm h)

/-! ## 4. And the same for the product over the propagator's eigenvalues -/

/-- The symmetry submonoid and the set of symmetry matrices are the same type:
`FieldSymmetryGroup.mem_symmetrySubmonoid` is `Iff.rfl`, so both maps are the identity on
carriers. -/
def submonoidEquivSet : symmetrySubmonoid G m ≃ symmetryMatrices G m where
  toFun R := ⟨R.1, R.2⟩
  invFun R := ⟨R.1, R.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **THE PRODUCT OVER THE DISTINCT EIGENVALUES HAS THE CARDINALITY OF THE SYMMETRY SET.**
`FieldBlockProduct.symmetry_mulEquiv_prod` is a `MulEquiv`, hence a bijection. -/
theorem mk_prod_unitaryGroup_eq_mk_symmetryMatrices (hm : m ≠ 0) :
    #(∀ c : Lev (eigMu G m hm), Matrix.unitaryGroup (Fib (eigMu G m hm) (c : ℝ)) ℝ)
      = #(symmetryMatrices G m) :=
  (mk_congr (symmetry_mulEquiv_prod hm).toEquiv.symm).trans (mk_congr submonoidEquivSet)

/-- **THE PRODUCT IS THE CONTINUUM IF AND ONLY IF THE SPECTRUM IS DEGENERATE.** -/
theorem mk_prod_unitaryGroup_eq_continuum_iff (hm : m ≠ 0) :
    #(∀ c : Lev (eigMu G m hm), Matrix.unitaryGroup (Fib (eigMu G m hm) (c : ℝ)) ℝ) = 𝔠 ↔
      ¬ Function.Injective (eigMu G m hm) := by
  rw [mk_prod_unitaryGroup_eq_mk_symmetryMatrices hm]
  exact mk_symmetryMatrices_eq_continuum_iff hm

/-- **AND FROM A BLOCK OF SIZE TWO OR MORE**, which is the form the `UNLOCK_WATCHLIST` item asked
for: one degenerate eigenvalue anywhere makes the whole product the continuum. -/
theorem mk_prod_unitaryGroup_of_two_le_card_fib (hm : m ≠ 0)
    {c : Lev (eigMu G m hm)} (h : 2 ≤ Fintype.card (Fib (eigMu G m hm) (c : ℝ))) :
    #(∀ c : Lev (eigMu G m hm), Matrix.unitaryGroup (Fib (eigMu G m hm) (c : ℝ)) ℝ) = 𝔠 :=
  (mk_prod_unitaryGroup_eq_continuum_iff hm).2
    ((FieldBlockInfinite.infinite_symmetryMatrices_iff_not_injective hm).1
      (FieldBlockInfinite.infinite_symmetryMatrices_of_two_le_card_fib hm h))

/-- **THE DICHOTOMY ON THE PRODUCT.** -/
theorem mk_prod_unitaryGroup_lt_aleph0_or_eq_continuum (hm : m ≠ 0) :
    #(∀ c : Lev (eigMu G m hm), Matrix.unitaryGroup (Fib (eigMu G m hm) (c : ℝ)) ℝ) < ℵ₀ ∨
      #(∀ c : Lev (eigMu G m hm), Matrix.unitaryGroup (Fib (eigMu G m hm) (c : ℝ)) ℝ) = 𝔠 := by
  rw [mk_prod_unitaryGroup_eq_mk_symmetryMatrices hm]
  exact mk_symmetryMatrices_lt_aleph0_or_eq_continuum hm

/-- **AND ON THE BUNDLED SUBMONOID**, so the statement is available on the object that carries the
group law. -/
theorem mk_symmetrySubmonoid_eq_continuum_iff (hm : m ≠ 0) :
    #(symmetrySubmonoid G m) = 𝔠 ↔ ¬ Function.Injective (eigMu G m hm) := by
  rw [mk_congr (submonoidEquivSet (G := G) (m := m))]
  exact mk_symmetryMatrices_eq_continuum_iff hm

/-- **AND ON THE BLOCK-DIAGONAL GROUP** `FieldBlockGroup.blockDiagSubmonoid`, across
`FieldBlockGroup.conjEigEquiv`. This is the object whose *no number, and there is not going to be
one* paragraph the unit answers, so it is stated on that object and not left to a reader to
transport (`ERRATUM 653`). -/
theorem mk_blockDiagSubmonoid_eq_continuum_iff (hm : m ≠ 0) :
    #(FieldBlockGroup.blockDiagSubmonoid (eigMu G m hm)) = 𝔠 ↔
      ¬ Function.Injective (eigMu G m hm) := by
  rw [mk_congr (FieldBlockGroup.conjEigEquiv (G := G) (m := m) hm).toEquiv.symm]
  exact mk_symmetrySubmonoid_eq_continuum_iff hm

/-! ## 5. On the torus, in every dimension -/

/-- **THE GAUSSIAN FIELD ON THE TORUS HAS EXACTLY `𝔠` SYMMETRIES**, in every dimension `d ≥ 1`,
at every side length `N + 3` and every non-zero mass — the physical `d = 4` included.
`FieldTorusRotation.exists_independent_eigenpair_torus` is the only input, and it is the same input
`FieldTorusRotation.infinite_symmetryMatrices_torus` takes. -/
theorem mk_symmetryMatrices_torus {d : ℕ} (hd : 1 ≤ d) (N : ℕ) (hm : m ≠ 0) :
    #(symmetryMatrices (TorusReflection.torusGraph d (N + 3)) m) = 𝔠 := by
  obtain ⟨u, v, hu0, hind, hu, hv⟩ := FieldTorusRotation.exists_independent_eigenpair_torus hd N hm
  exact mk_symmetryMatrices_of_independent_eigenpair hm hu0 hind hu hv

end FieldBlockContinuum
