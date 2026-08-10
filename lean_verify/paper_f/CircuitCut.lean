import RayWalk

/-!
# A circuit's bonds are a cut

`CircuitSides` named this and proved its local half; ERRATUM 83 recorded that the enclosure
step did not need it after all. **It is needed for the other side of Peierls' comparison**,
and this file proves it:

> for a circuit `H` of the dual graph under `+` boundary conditions, there is a
> configuration `τ` whose contour is exactly `bonds σ H`.

## Why the energy side wants it

*This paragraph is a description of the textbook argument, not of anything proved here.*
The energy half of Peierls' estimate is an injection: configurations whose contour contains
a given circuit map to configurations with `|γ|` smaller by that circuit's length, and the
map is symmetric difference of contours. For that map to land among **realised** contours,
the circuit's bond set must itself be realised — which is what this file proves. Whether
the symmetric difference of two realised contours is realised is a **separate** statement
and is not proved here either.

What *is* delivered as a corollary is path-independence for a single circuit
(`crossings_parity_indep`), which `SurroundsParity`'s header records as false for a general
bond set and available only for cuts, and `isCocycle_bonds`, which is that file's own
vocabulary for the same fact.

**The injection itself is not built here**, and neither is any estimate.

## How it is proved, and what was already there

Not by topology, and not by defining an interior. `τ p` is the **parity of the crossings
along the leftward ray from `p`** — `RayWalk.leftRay`, the same walk the enclosure step
used. Then the contour equation is two cases:

* **horizontal bonds** hold *by construction*: the ray from the next column is the ray from
  this one with one step in front, so the two parities differ exactly when that step's bond
  is in the set (`RayWalk.crossings_leftRay` and the `cons` recursion);
* **vertical bonds** are `RowParity.partial_row` — the telescoping sum along a row, which
  says precisely that the two rays bounding a row differ in parity exactly at the vertical
  bond where they part. At the last column it is `RowParity.full_row` instead, and the
  bond there is on the box edge and unbroken.

So the construction is `IsingContourCocycle.contour_pathParity`'s **idea** with the walk
chosen concretely — and that theorem itself is deliberately **not used**, because its
hypothesis is `IsCocycle`, evenness along *every* closed walk, which is precisely the thing
that was missing. Choosing the walk instead of quantifying over walks is what makes the
proof two cases, and the harder of the two was proved two units ago for another purpose.
The `IsCocycle` property then falls out the other way round, from
`IsingContourClosed.cocycle_of_realised`.

## What this does not do

It does not build the Peierls injection, the Gibbs weight of a circuit, or the summation
over lengths. `IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace CircuitCut

open IsingFiniteVolume IsingContourEnergy IsingContourSeparation IsingContourClosed
open IsingContourPlaquette IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds CircuitSides RowParity RayWalk
open SimpleGraph

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The configuration a circuit induces -/

/-- **The parity of the crossings along the leftward ray.** -/
noncomputable def tau (σ : Config n) (H : SimpleGraph (Plaq n)) : Config n :=
  fun p => decide (¬ Even (crossings (bonds σ H) (leftRay p.2 p.1.val p.1.isLt)))

/-- Evaluated at a site named by its column, which is the form every step below uses. -/
@[simp] theorem tau_col (σ : Config n) (H : SimpleGraph (Plaq n)) (b : Fin n) (k : ℕ)
    (hk : k < n) :
    tau σ H (col b k hk) = decide (¬ Even (crossings (bonds σ H) (leftRay b k hk))) := rfl

/-! ## 2. The two rays bounding a row, as the two row counts

The ray in row `b` counts the bottom sides of that row's plaquettes; the ray in row `b + 1`
counts their top sides. The second is not an instance of the first — row `b + 1` need not
have a row of plaquettes above it — so it is its own induction. -/

/-- The upper side of a plaquette, as the step of the ray one row up. -/
theorem sideU_rowP_eq (b : Fin n) (hj : b.val + 1 < n) (k : ℕ) (hk : k + 1 < n) :
    sideU (rowP b.val hj k) =
      s(col (⟨b.val + 1, hj⟩ : Fin n) (k + 1) hk, col (⟨b.val + 1, hj⟩ : Fin n) k (by omega)) := by
  rw [show rowP b.val hj k = ⟨k, b.val, hk, hj⟩ from
    Plaq.ext (by simp only [rowP]; omega) rfl, Sym2.eq_swap]
  rfl

theorem crossings_ray_eq_cntD (σ : Config n) (H : SimpleGraph (Plaq n)) (b : Fin n)
    (hj : b.val + 1 < n) (k : ℕ) (hk : k < n) :
    crossings (bonds σ H) (leftRay b k hk) = cntD σ H b.val hj k :=
  crossings_leftRay _ b hj k hk

/-- **And the ray one row up counts the top sides**, by its own induction. -/
theorem crossings_ray_succ_eq_cntU (σ : Config n) (H : SimpleGraph (Plaq n)) (b : Fin n)
    (hj : b.val + 1 < n) :
    ∀ (k : ℕ) (hk : k < n),
      crossings (bonds σ H) (leftRay (⟨b.val + 1, hj⟩ : Fin n) k hk) = cntU σ H b.val hj k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [leftRay_succ, crossings_cons, ih (by omega), cntU_succ, sideU_rowP_eq b hj k (by omega)]
    omega

/-! ## 3. The two cases of the contour equation -/

theorem tau_step_horizontal (σ : Config n) (H : SimpleGraph (Plaq n)) (b : Fin n) (k : ℕ)
    (hk : k + 1 < n) :
    (tau σ H (col b (k + 1) hk) ≠ tau σ H (col b k (by omega))) ↔
      s(col b (k + 1) hk, col b k (by omega)) ∈ bonds σ H := by
  have hstep : crossings (bonds σ H) (leftRay b (k + 1) hk) =
      (if s(col b (k + 1) hk, col b k (by omega)) ∈ bonds σ H then 1 else 0) +
        crossings (bonds σ H) (leftRay b k (by omega)) := by
    rw [leftRay_succ]
    exact crossings_cons _ _ _
  simp only [tau_col, ne_eq, decide_eq_decide]
  by_cases hmem : s(col b (k + 1) hk, col b k (by omega)) ∈ bonds σ H
  · simp only [hmem, if_true] at hstep
    rw [hstep]
    simp only [hmem, iff_true]
    rw [Nat.even_iff, Nat.even_iff]
    omega
  · simp only [hmem, if_false, Nat.zero_add] at hstep
    rw [hstep]
    simp only [hmem, iff_false, not_not]

theorem tau_step_vertical (σ : Config n) {H : SimpleGraph (Plaq n)} (hσ : PlusBoundary σ)
    (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) (b : Fin n) (hj : b.val + 1 < n)
    (k : ℕ) (hk : k < n) :
    (tau σ H (col b k hk) ≠ tau σ H (col (⟨b.val + 1, hj⟩ : Fin n) k hk)) ↔
      s(col b k hk, col (⟨b.val + 1, hj⟩ : Fin n) k hk) ∈ bonds σ H := by
  have hD := crossings_ray_eq_cntD σ H b hj k hk
  have hU := crossings_ray_succ_eq_cntU σ H b hj k hk
  simp only [tau_col, ne_eq, decide_eq_decide, hD, hU]
  rcases Nat.lt_or_ge (k + 1) n with hlast | hlast
  · have hrow := partial_row hσ hle hcyc hj k hlast
    have hside : s(col b k hk, col (⟨b.val + 1, hj⟩ : Fin n) k hk) = sideL (rowP b.val hj k) := by
      rw [show rowP b.val hj k = ⟨k, b.val, hlast, hj⟩ from
        Plaq.ext (by simp only [rowP]; omega) rfl]
      rfl
    rw [hside]
    by_cases hmem : sideL (rowP b.val hj k) ∈ bonds σ H
    · simp only [hmem, if_true, iff_true] at hrow ⊢
      rw [Nat.even_iff, Nat.even_iff]
      omega
    · simp only [hmem, if_false, iff_false, not_not] at hrow ⊢
      rw [Nat.even_iff, Nat.even_iff]
      omega
  · have hk1 : k = n - 1 := by omega
    subst hk1
    have hrow := full_row hσ hle hcyc hj
    have hnot : s(col b (n - 1) hk, col (⟨b.val + 1, hj⟩ : Fin n) (n - 1) hk) ∉ bonds σ H := by
      refine fun hmem => notMem_contour_of_plusBoundary hσ ?_ ?_ (bonds_subset σ H hmem)
      · simp only [isBoundary, col, decide_eq_true_eq]
        omega
      · simp only [isBoundary, col, decide_eq_true_eq]
        omega
    simp only [hnot, iff_false, not_not]
    rw [Nat.even_iff, Nat.even_iff]
    omega

/-! ## 4. The contour equation

Four sub-cases of `adj`, and each is one of the two steps above read at the right pair.
The `Fin`-level equations have to be pushed down to `Nat` by hand before `omega` sees
them, which is the only friction here. -/

theorem tau_ne_iff_mem (σ : Config n) {H : SimpleGraph (Plaq n)} (hσ : PlusBoundary σ)
    (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) {p q : Site n} (hadj : adj p q) :
    (tau σ H p ≠ tau σ H q) ↔ s(p, q) ∈ bonds σ H := by
  have hp1 := p.1.isLt
  have hp2 := p.2.isLt
  have hq1 := q.1.isLt
  have hq2 := q.2.isLt
  have hpp : p = col p.2 p.1.val hp1 := rfl
  have hqq : q = col q.2 q.1.val hq1 := rfl
  rcases hadj with ⟨hfst, hsnd⟩ | ⟨hsnd, hfst⟩
  · -- same first coordinate: a vertical bond
    have e1 : p.1.val = q.1.val := congrArg Fin.val hfst
    rcases hsnd with h1 | h1
    · have hqc : q = col (⟨p.2.val + 1, by omega⟩ : Fin n) p.1.val hp1 :=
        Prod.ext (Fin.ext (by simp only [col]; omega)) (Fin.ext (by simp only [col]; omega))
      rw [hpp, hqc]
      exact tau_step_vertical σ hσ hle hcyc p.2 (by omega) p.1.val hp1
    · have hpc : p = col (⟨q.2.val + 1, by omega⟩ : Fin n) q.1.val hq1 :=
        Prod.ext (Fin.ext (by simp only [col]; omega)) (Fin.ext (by simp only [col]; omega))
      rw [hqq, hpc, Sym2.eq_swap, ne_comm]
      exact tau_step_vertical σ hσ hle hcyc q.2 (by omega) q.1.val hq1
  · -- same second coordinate: a horizontal bond
    have e2 : p.2.val = q.2.val := congrArg Fin.val hsnd
    rcases hfst with h1 | h1
    · have hqc : q = col p.2 (p.1.val + 1) (by omega) :=
        Prod.ext (Fin.ext (by simp only [col]; omega)) (Fin.ext (by simp only [col]; omega))
      rw [hpp, hqc, Sym2.eq_swap, ne_comm]
      exact tau_step_horizontal σ H p.2 p.1.val (by omega)
    · have hpc : p = col q.2 (q.1.val + 1) (by omega) :=
        Prod.ext (Fin.ext (by simp only [col]; omega)) (Fin.ext (by simp only [col]; omega))
      rw [hqq, hpc]
      exact tau_step_horizontal σ H q.2 q.1.val (by omega)

/-- **A circuit's bonds are a cut**: the parity-of-the-ray configuration has exactly them
as its contour. -/
theorem contour_tau {σ : Config n} (hσ : PlusBoundary σ) {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) :
    contour (tau σ H) = bonds σ H := by
  ext e
  induction e using Sym2.ind with
  | _ p q =>
    rw [mem_contour]
    constructor
    · rintro ⟨hadj, hne⟩
      exact (tau_ne_iff_mem σ hσ hle hcyc hadj).mp hne
    · intro hmem
      have hadj : adj p q := ((mem_contour σ p q).mp (bonds_subset σ H hmem)).1
      exact ⟨hadj, (tau_ne_iff_mem σ hσ hle hcyc hadj).mpr hmem⟩

/-- **The named statement, as `PlaqLocal` and `CircuitSides` wrote it.** -/
theorem exists_cut {σ : Config n} (hσ : PlusBoundary σ) {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) :
    ∃ τ : Config n, bonds σ H = contour τ :=
  ⟨tau σ H, (contour_tau hσ hle hcyc).symm⟩

/-! ## 5. What it buys: a cocycle, and path-independence for one circuit -/

/-- **A circuit's bonds are crossed evenly by every closed walk.** The estate's own
vocabulary for the same fact — and note the direction: `IsingContourCocycle` builds a
configuration *from* this property, whereas here the configuration came first and the
property follows from it, via `IsingContourClosed.cocycle_of_realised`. -/
theorem isCocycle_bonds {σ : Config n} (hσ : PlusBoundary σ) {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) :
    IsingContourCocycle.IsCocycle (bonds σ H) := by
  intro u w
  rw [← contour_tau hσ hle hcyc]
  exact even_crossings_closed (tau σ H) w


/-- **The crossing parity of a single circuit does not depend on the path.** This is what
`SurroundsParity`'s header records as false for a general bond set and true for a cut, and
it is now available for the pieces of the dual decomposition. -/
theorem crossings_parity_indep {σ : Config n} (hσ : PlusBoundary σ)
    {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H)
    {x b : Site n} (w w' : (latticeGraph n).Walk x b) :
    Even (crossings (bonds σ H) w) ↔ Even (crossings (bonds σ H) w') := by
  rw [contour_tau hσ hle hcyc |>.symm]
  exact SurroundsParity.crossings_parity_indep (tau σ H) w w'

/-- And the parity reads off the two ends, as it does for the whole contour. -/
theorem odd_crossings_iff_ne {σ : Config n} (hσ : PlusBoundary σ)
    {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H)
    {x b : Site n} (w : (latticeGraph n).Walk x b) :
    ¬ Even (crossings (bonds σ H) w) ↔ tau σ H x ≠ tau σ H b := by
  rw [contour_tau hσ hle hcyc |>.symm]
  exact SurroundsParity.odd_crossings_iff_ne (tau σ H) w

end CircuitCut
