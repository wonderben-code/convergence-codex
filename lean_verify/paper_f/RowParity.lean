import CircuitSides

/-!
# A circuit meets every horizontal line of the box an even number of times

`CircuitSides` proved the local half of "a circuit's bonds are a cut" and named sufficiency
— the global half — as what remained. **This file does not prove sufficiency, and it turns
out the Peierls estimate does not need it.**

What the estimate needs from the cut is one consequence: that a ray from `x` crossing a
circuit oddly forces the *opposite* ray to cross it oddly too, so the circuit is caught on
both sides of `x`. That does not need path-independence in general. It needs only

> **the whole horizontal line through `x` meets the circuit an even number of times**,

because then the two halves of the line have equal parity. This file proves that, and the
proof is the telescoping sum `CircuitSides.sides_ud_eq_lr` was written for.

## The two inductions

**Along a row.** Summing `sides_ud_eq_lr` across the plaquettes of one row, the vertical
sides cancel in pairs — `sideR P` *is* `sideL (rightP P)` — leaving the two ends. Both ends
are bonds with both feet on the edge of the box, which a `+`-boundary configuration never
breaks. So the bonds of row `j` and the bonds of row `j + 1` **have the same parity**.

**Up the rows.** Row `0` is the bottom edge of the box, so a `+`-boundary configuration
breaks none of it. Hence every row is even, by induction.

Neither step needs "surrounds", a cut, or any topology: they need the cycle (through
`sides_ud_eq_lr`), the `+` boundary condition at the two ends, and arithmetic.

## What this is not

It is **not** the enclosure step, which still has to put the two halves of the line
together with `PlaqLocal`'s diameter bound. It is not the cut either: a cut would give the
parity along *every* closed walk, and this gives it along the horizontal lines only, which
is all the ray argument reads. `IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace RowParity

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds CircuitSides SimpleGraph

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The plaquettes of a row, indexed by column

Truncating at the last column, in the style of `DualGraph`'s partner maps, so that the
indexing map is total and every fact about it is one `omega` away. -/

/-- The plaquette at column `k` of row `j`, or the last one when `k` runs off the end. -/
def rowP (j : ℕ) (hj : j + 1 < n) (k : ℕ) : Plaq n := ⟨min k (n - 2), j, by omega, hj⟩

@[simp] theorem rowP_j {j : ℕ} (hj : j + 1 < n) (k : ℕ) : (rowP j hj k).j = j := rfl

theorem rowP_i {j k : ℕ} (hj : j + 1 < n) (h : k + 1 < n) : (rowP j hj k).i = k := by
  simp only [rowP]
  omega

theorem rightP_rowP {j k : ℕ} (hj : j + 1 < n) (h : k + 2 < n) :
    rightP (rowP j hj k) = rowP j hj (k + 1) :=
  Plaq.ext (by simp only [rightP_i, rowP]; omega) rfl

/-- The upper side of a plaquette is the lower side of the plaquette above it. -/
theorem sideU_rowP {j k : ℕ} (hj : j + 1 < n) (hj' : j + 2 < n) :
    sideU (rowP j hj k) = sideD (rowP (j + 1) (by omega) k) := by
  have hdown : downP (rowP (j + 1) (by omega : j + 1 + 1 < n) k) = rowP j hj k :=
    Plaq.ext rfl (by simp only [downP_j, rowP]; omega)
  rw [← hdown, sideU_downP _ (by simp only [rowP]; omega)]

/-! ## 2. Two more boundary sides that no circuit uses

`CircuitSides.sideL_notMem_bonds` is the left edge; the telescoping sum needs the right
edge as well, and the induction up the rows needs the bottom. Both are the corresponding
`PlaquetteLattice` lemma composed with `bonds_subset`. -/

theorem sideR_notMem_bonds {σ : Config n} (hσ : PlusBoundary σ) (H : SimpleGraph (Plaq n))
    {P : Plaq n} (h : P.i + 2 = n) : sideR P ∉ bonds σ H :=
  fun hc => sideR_notMem_contour hσ P h (bonds_subset σ H hc)

theorem sideD_notMem_bonds {σ : Config n} (hσ : PlusBoundary σ) (H : SimpleGraph (Plaq n))
    {P : Plaq n} (h : P.j = 0) : sideD P ∉ bonds σ H :=
  fun hc => sideD_notMem_contour hσ P h (bonds_subset σ H hc)

/-! ## 3. Counting the broken bonds of a row

`cntD j a` counts the broken horizontal bonds of row `j` in the columns below `a`, read as
the bottom sides of that row's plaquettes; `cntU` reads the row above as their top sides.
Sums rather than filtered cards, so that `Finset.sum_range_succ` is the recursion. -/

/-- Broken bottom sides of row `j`, columns `< a`. -/
noncomputable def cntD (σ : Config n) (H : SimpleGraph (Plaq n)) (j : ℕ) (hj : j + 1 < n)
    (a : ℕ) : ℕ :=
  ∑ k ∈ Finset.range a, if sideD (rowP j hj k) ∈ bonds σ H then 1 else 0

/-- Broken top sides of row `j`, columns `< a` — the bonds of row `j + 1`. -/
noncomputable def cntU (σ : Config n) (H : SimpleGraph (Plaq n)) (j : ℕ) (hj : j + 1 < n)
    (a : ℕ) : ℕ :=
  ∑ k ∈ Finset.range a, if sideU (rowP j hj k) ∈ bonds σ H then 1 else 0

theorem cntD_succ (σ : Config n) (H : SimpleGraph (Plaq n)) {j : ℕ} (hj : j + 1 < n)
    (a : ℕ) : cntD σ H j hj (a + 1) =
      cntD σ H j hj a + if sideD (rowP j hj a) ∈ bonds σ H then 1 else 0 :=
  Finset.sum_range_succ _ _

theorem cntU_succ (σ : Config n) (H : SimpleGraph (Plaq n)) {j : ℕ} (hj : j + 1 < n)
    (a : ℕ) : cntU σ H j hj (a + 1) =
      cntU σ H j hj a + if sideU (rowP j hj a) ∈ bonds σ H then 1 else 0 :=
  Finset.sum_range_succ _ _

/-! ## 4. The telescoping sum along a row

The induction: below column `a`, the horizontal bonds of the two rows bounding row `j`
carry the same parity as the single vertical bond at column `a`. Every interior vertical
bond has been counted twice — once as a `sideR` and once as the `sideL` of the next
plaquette — and the left end is unbroken because it sits on the edge of the box. -/

theorem partial_row {σ : Config n} (hσ : PlusBoundary σ) {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) {j : ℕ} (hj : j + 1 < n) :
    ∀ a, a + 1 < n →
      (cntD σ H j hj a + cntU σ H j hj a) % 2 =
        (if sideL (rowP j hj a) ∈ bonds σ H then 1 else 0) % 2 := by
  intro a
  induction a with
  | zero =>
    intro _
    have h0 : sideL (rowP j hj 0) ∉ bonds σ H :=
      sideL_notMem_bonds hσ H (by simp only [rowP]; omega)
    simp [cntD, cntU, h0]
  | succ a ih =>
    intro ha
    have hIH := ih (by omega)
    have hlr := sides_ud_eq_lr hle hcyc (rowP j hj a)
    have hR : sideL (rowP j hj (a + 1)) = sideR (rowP j hj a) := by
      rw [← rightP_rowP hj (by omega), sideL_rightP _ (by rw [rowP_i hj (by omega)]; omega)]
    rw [cntD_succ, cntU_succ, hR]
    omega

/-- **The two rows bounding a row of plaquettes have the same parity.** The whole-row case
of the sum above: at the right-hand end the vertical bond is again on the edge of the box,
so the telescope closes on nothing. -/
theorem full_row {σ : Config n} (hσ : PlusBoundary σ) {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) {j : ℕ} (hj : j + 1 < n) :
    (cntD σ H j hj (n - 1) + cntU σ H j hj (n - 1)) % 2 = 0 := by
  have hn : 2 ≤ n := by omega
  have hsplit : n - 1 = (n - 2) + 1 := by omega
  have hprev := partial_row hσ hle hcyc hj (n - 2) (by omega)
  have hlr := sides_ud_eq_lr hle hcyc (rowP j hj (n - 2))
  have hend : sideR (rowP j hj (n - 2)) ∉ bonds σ H :=
    sideR_notMem_bonds hσ H (by simp only [rowP]; omega)
  simp only [hend, if_false] at hlr
  rw [hsplit, cntD_succ, cntU_succ]
  omega

/-! ## 5. Up the rows, from the bottom edge -/

/-- The top sides of row `j` are the bottom sides of row `j + 1`, count and all. -/
theorem cntU_eq_cntD (σ : Config n) (H : SimpleGraph (Plaq n)) {j : ℕ} (hj : j + 1 < n)
    (hj' : j + 2 < n) (a : ℕ) : cntU σ H j hj a = cntD σ H (j + 1) (by omega) a := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sideU_rowP hj hj']

/-- **Every horizontal line of the box meets a circuit an even number of times.** Row `0`
is the bottom edge, which a `+`-boundary configuration never breaks; each row after it has
the parity of the one below. -/
theorem even_row {σ : Config n} (hσ : PlusBoundary σ) {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) :
    ∀ j, (hj : j + 1 < n) → cntD σ H j hj (n - 1) % 2 = 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    have : ∀ k, sideD (rowP 0 hj k) ∉ bonds σ H := fun k =>
      sideD_notMem_bonds hσ H rfl
    simp [cntD, this]
  | succ j ih =>
    intro hj
    have hj0 : j + 1 < n := by omega
    have hrow := full_row hσ hle hcyc hj0
    have hswap := cntU_eq_cntD σ H hj0 (by omega) (n - 1)
    have hIH := ih hj0
    rw [hswap] at hrow
    omega

/-- The top row, stated in its own terms: the bonds of row `j + 1` counted as the top sides
of row `j`. Same theorem, and recorded because the topmost line of the box has no row of
plaquettes above it to be the bottom of. -/
theorem even_row_top {σ : Config n} (hσ : PlusBoundary σ) {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) {j : ℕ} (hj : j + 1 < n) :
    cntU σ H j hj (n - 1) % 2 = 0 := by
  have hrow := full_row hσ hle hcyc hj
  have hIH := even_row hσ hle hcyc j hj
  omega

/-! ## 6. What this gives, and what it does not

**Gives:** the horizontal line at any height meets a circuit evenly. So for a site `x` on
that line, the bonds to its left and the bonds to its right have the **same parity**, and
in particular if the leftward ray crosses the circuit oddly then so does the rightward one.
That is the two-sided catch the enclosure step needs, and it was obtained without the cut.

**Does not give:** the enclosure step itself. That still has to (i) choose the walk from `x`
to the corner to run along the row and then down the left edge, where the descent crosses
nothing because both feet of every bond on it are on the boundary; (ii) turn the odd count
on each side into a plaquette of the circuit on each side; and (iii) put those two
plaquettes together with `PlaqLocal.near_of_mem_support_closed_pair`, which bounds their
separation by the circuit's length, to conclude that the circuit passes within its own
length of `x`. **None of those three is done here.**

**And it does not give the cut.** `∃ τ, bonds σ H = contour τ` remains unproved and
unassumed; what this file shows is that the Peierls estimate can reach the enclosure step
without it, which is a statement about the estimate and not about the cut. -/

end RowParity
