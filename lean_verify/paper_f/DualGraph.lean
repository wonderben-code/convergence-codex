import PlaquetteLattice
import CycleDecomposition

/-!
# The dual graph, and the Peierls circuit decomposition

This is the assembly. `PlaquetteLattice` built the plaquettes and both halves of the
bijection this file needs; `CycleDecomposition` proved that an even-degree graph is an
edge-disjoint union of circuits; `IsingContourPlaquette.even_plaquette` proved that
every unit square has an even number of broken sides. Putting the three together gives
the step the Peierls argument has been blocked on:

> under `+` boundary conditions, the contour of any configuration, read on the **dual**
> lattice, is an edge-disjoint union of circuits.

## How the degree count works

The dual graph has the plaquettes as vertices, and `P` is joined to `Q` when the side of
`P` facing `Q` is **broken**. The four directions are indexed by `Fin 4` in the order
`even_plaquette` lists them — left, top, right, bottom — so that theorem's sum is
literally the number of broken directions.

Every partner map is **total**, and truncates rather than branching: `leftP` sends the
left column to itself because `P.i - 1 = P.i` there, and `rightP` uses `min` for the
same reason at the other edge. So `partnerOf P d = P` says exactly *"the `d` side of `P`
faces outwards"*, which by `PlaquetteLattice.bl_tl_boundary_iff` and its siblings is
exactly *"`P` is at the corresponding extreme"*, which under `PlusBoundary` is exactly
*"the `d` side of `P` is not broken"*. Those three "exactly"s are what make
`neighborSet_eq_image` true with no side conditions left over.

The neighbours of `P` are then the image of the broken directions under the partner map;
the map is injective there because distinct directions move different coordinates in
different directions; so the degree is the number of broken directions, which
`even_plaquette` says is even.

## What this does *not* do

`IsingBoundaryField.MagnetisationBound` is untouched, and it is not close. Peierls needs
the number of circuits **of a given length surrounding a fixed site**; neither "the
length of a dual circuit, as a contour length" nor "surrounds" is defined anywhere in
this estate, and nothing here defines them. What is proved is that the circuits exist
and are edge-disjoint — the structural half — with
`CircuitCount.three_mul_length_le_ncard_edgeSet` bounding how many there are. Nothing
bounds their shapes.

The `+` boundary condition is a hypothesis on the configuration, not a modification of
the model: `IsingFiniteVolume`'s box still has free boundary, and
`DualObstruction.not_plusBoundary_cornerDown` exhibits a configuration outside the
hypothesis. That is not a gap in the proof; it is where the textbook argument also puts
its boundary condition.
-/

namespace DualGraph

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette IsingBoundaryField
open DualObstruction PlaquetteLattice SimpleGraph

variable {n : ℕ}

/-! ## 1. Total partner maps

Each map sends `P` to the plaquette across the corresponding side, and to `P` itself
when there is none. Truncated arithmetic rather than a case split, so that every fact
below is one `omega` away. -/

/-- The plaquette to the left, or `P` at the left edge. -/
def leftP (P : Plaq n) : Plaq n := ⟨P.i - 1, P.j, by have := P.hi; omega, P.hj⟩
/-- The plaquette above, or `P` at the top edge. -/
def upP (P : Plaq n) : Plaq n :=
  ⟨P.i, min (P.j + 1) (n - 2), P.hi, by have := P.hj; omega⟩
/-- The plaquette to the right, or `P` at the right edge. -/
def rightP (P : Plaq n) : Plaq n :=
  ⟨min (P.i + 1) (n - 2), P.j, by have := P.hi; omega, P.hj⟩
/-- The plaquette below, or `P` at the bottom edge. -/
def downP (P : Plaq n) : Plaq n := ⟨P.i, P.j - 1, P.hi, by have := P.hj; omega⟩

@[simp] theorem leftP_i (P : Plaq n) : (leftP P).i = P.i - 1 := rfl
@[simp] theorem leftP_j (P : Plaq n) : (leftP P).j = P.j := rfl
@[simp] theorem rightP_i (P : Plaq n) : (rightP P).i = min (P.i + 1) (n - 2) := rfl
@[simp] theorem rightP_j (P : Plaq n) : (rightP P).j = P.j := rfl
@[simp] theorem downP_i (P : Plaq n) : (downP P).i = P.i := rfl
@[simp] theorem downP_j (P : Plaq n) : (downP P).j = P.j - 1 := rfl
@[simp] theorem upP_i (P : Plaq n) : (upP P).i = P.i := rfl
@[simp] theorem upP_j (P : Plaq n) : (upP P).j = min (P.j + 1) (n - 2) := rfl

theorem leftP_eq_self_iff (P : Plaq n) : leftP P = P ↔ P.i = 0 := by
  constructor
  · intro h; have := congrArg Plaq.i h; simp only [leftP_i] at this; omega
  · intro h; exact Plaq.ext (by simp [h]) rfl

theorem rightP_eq_self_iff (P : Plaq n) : rightP P = P ↔ P.i + 2 = n := by
  have hP := P.hi
  constructor
  · intro h; have := congrArg Plaq.i h; simp only [rightP_i] at this; omega
  · intro h; exact Plaq.ext (by simp; omega) rfl

theorem downP_eq_self_iff (P : Plaq n) : downP P = P ↔ P.j = 0 := by
  constructor
  · intro h; have := congrArg Plaq.j h; simp only [downP_j] at this; omega
  · intro h; exact Plaq.ext rfl (by simp [h])

theorem upP_eq_self_iff (P : Plaq n) : upP P = P ↔ P.j + 2 = n := by
  have hP := P.hj
  constructor
  · intro h; have := congrArg Plaq.j h; simp only [upP_j] at this; omega
  · intro h; exact Plaq.ext rfl (by simp; omega)

/-! ### The partner's own side, and the partner's partner

Both are needed for the symmetry of the dual adjacency: crossing a side from the far end
must give back the same bond and the plaquette one started from. The four
`PlaquetteLattice` sharing lemmas do the work; all that is added is the identification of
the truncated map with the hypothesis-carrying one. -/

theorem rightP_eq_rightPlaq (P : Plaq n) (h : P.i + 2 < n) : rightP P = rightPlaq P h :=
  Plaq.ext (by simp only [rightP_i]; simp only [rightPlaq]; omega) rfl

theorem upP_eq_upPlaq (P : Plaq n) (h : P.j + 2 < n) : upP P = upPlaq P h :=
  Plaq.ext rfl (by simp only [upP_j]; simp only [upPlaq]; omega)

theorem sideR_leftP (P : Plaq n) (h : P.i ≠ 0) : sideR (leftP P) = sideL P :=
  sideR_leftPlaq P h

theorem sideU_downP (P : Plaq n) (h : P.j ≠ 0) : sideU (downP P) = sideD P :=
  sideU_downPlaq P h

theorem sideL_rightP (P : Plaq n) (h : P.i + 2 < n) : sideL (rightP P) = sideR P := by
  rw [rightP_eq_rightPlaq P h]; exact sideL_rightPlaq P h

theorem sideD_upP (P : Plaq n) (h : P.j + 2 < n) : sideD (upP P) = sideU P := by
  rw [upP_eq_upPlaq P h]; exact sideD_upPlaq P h

theorem rightP_leftP (P : Plaq n) (h : P.i ≠ 0) : rightP (leftP P) = P := by
  have := P.hi
  exact Plaq.ext (by simp; omega) rfl

theorem leftP_rightP (P : Plaq n) (h : P.i + 2 < n) : leftP (rightP P) = P := by
  exact Plaq.ext (by simp; omega) rfl

theorem upP_downP (P : Plaq n) (h : P.j ≠ 0) : upP (downP P) = P := by
  have := P.hj
  exact Plaq.ext rfl (by simp; omega)

theorem downP_upP (P : Plaq n) (h : P.j + 2 < n) : downP (upP P) = P := by
  exact Plaq.ext rfl (by simp; omega)

/-! ## 2. The four directions

Indexed so that `sideOf P` lists the sides in the order `even_plaquette` sums them. -/

/-- The `d`-th side of `P`, in `even_plaquette`'s order: left, top, right, bottom. -/
def sideOf (P : Plaq n) : Fin 4 → Sym2 (Site n)
  | 0 => sideL P
  | 1 => sideU P
  | 2 => sideR P
  | 3 => sideD P

/-- The plaquette across the `d`-th side, or `P` itself when that side faces outwards. -/
def partnerOf (P : Plaq n) : Fin 4 → Plaq n
  | 0 => leftP P
  | 1 => upP P
  | 2 => rightP P
  | 3 => downP P

/-- The opposite direction. -/
def opp : Fin 4 → Fin 4
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1

/-- **Crossing a side from the far end gives back the same bond.** -/
theorem sideOf_partnerOf (P : Plaq n) (d : Fin 4) (h : partnerOf P d ≠ P) :
    sideOf (partnerOf P d) (opp d) = sideOf P d := by
  fin_cases d
  · exact sideR_leftP P fun hc => h ((leftP_eq_self_iff P).mpr hc)
  · have hne : P.j + 2 ≠ n := fun hc => h ((upP_eq_self_iff P).mpr hc)
    have := P.hj
    exact sideD_upP P (by omega)
  · have hne : P.i + 2 ≠ n := fun hc => h ((rightP_eq_self_iff P).mpr hc)
    have := P.hi
    exact sideL_rightP P (by omega)
  · exact sideU_downP P fun hc => h ((downP_eq_self_iff P).mpr hc)

/-- **Crossing a side and coming back returns to where one started.** -/
theorem partnerOf_partnerOf (P : Plaq n) (d : Fin 4) (h : partnerOf P d ≠ P) :
    partnerOf (partnerOf P d) (opp d) = P := by
  fin_cases d
  · exact rightP_leftP P fun hc => h ((leftP_eq_self_iff P).mpr hc)
  · have hne : P.j + 2 ≠ n := fun hc => h ((upP_eq_self_iff P).mpr hc)
    have := P.hj
    exact downP_upP P (by omega)
  · have hne : P.i + 2 ≠ n := fun hc => h ((rightP_eq_self_iff P).mpr hc)
    have := P.hi
    exact leftP_rightP P (by omega)
  · exact upP_downP P fun hc => h ((downP_eq_self_iff P).mpr hc)

/-! ## 3. The dual graph

`P` is joined to `Q` when the side of `P` facing `Q` is broken. The clause `Q ≠ P` is
what excludes the outward-facing sides, and it is also exactly the hypothesis the two
crossing lemmas need, which is why symmetry costs nothing. -/

/-- Adjacency of the dual graph of a configuration. -/
def dualAdj (σ : Config n) (P Q : Plaq n) : Prop :=
  ∃ d : Fin 4, sideOf P d ∈ contour σ ∧ Q = partnerOf P d ∧ Q ≠ P

/-- **The dual graph**: plaquettes joined across their broken sides. -/
def dualGraph (σ : Config n) : SimpleGraph (Plaq n) where
  Adj := dualAdj σ
  symm := by
    rintro P Q ⟨d, hmem, rfl, hne⟩
    refine ⟨opp d, ?_, (partnerOf_partnerOf P d hne).symm, hne.symm⟩
    rw [sideOf_partnerOf P d hne]
    exact hmem
  loopless := ⟨by rintro P ⟨d, -, -, hne⟩; exact hne rfl⟩

@[simp] theorem dualGraph_adj (σ : Config n) (P Q : Plaq n) :
    (dualGraph σ).Adj P Q ↔
      ∃ d : Fin 4, sideOf P d ∈ contour σ ∧ Q = partnerOf P d ∧ Q ≠ P :=
  Iff.rfl

/-! ## 4. Under `+` boundary conditions the `Q ≠ P` clause is automatic

A broken side is not outward-facing (`PlaquetteLattice` §5), and a side is
outward-facing exactly when its partner is `P` itself. So under `PlusBoundary` the dual
neighbours of `P` are precisely the partners across its broken sides. -/

theorem partnerOf_ne_of_mem {σ : Config n} (hσ : PlusBoundary σ) (P : Plaq n) (d : Fin 4)
    (hmem : sideOf P d ∈ contour σ) : partnerOf P d ≠ P := by
  fin_cases d
  · exact fun hc => exists_leftPlaq_of_sideL_mem hσ P hmem ((leftP_eq_self_iff P).mp hc)
  · have := exists_upPlaq_of_sideU_mem hσ P hmem
    exact fun hc => by have := (upP_eq_self_iff P).mp hc; omega
  · have := exists_rightPlaq_of_sideR_mem hσ P hmem
    exact fun hc => by have := (rightP_eq_self_iff P).mp hc; omega
  · exact fun hc => exists_downPlaq_of_sideD_mem hσ P hmem ((downP_eq_self_iff P).mp hc)

theorem neighborSet_eq_image {σ : Config n} (hσ : PlusBoundary σ) (P : Plaq n) :
    (dualGraph σ).neighborSet P = partnerOf P '' {d : Fin 4 | sideOf P d ∈ contour σ} := by
  ext Q
  constructor
  · rintro ⟨d, hmem, rfl, -⟩
    exact ⟨d, hmem, rfl⟩
  · rintro ⟨d, hmem, rfl⟩
    exact ⟨d, hmem, rfl, partnerOf_ne_of_mem hσ P d hmem⟩

/-! ## 5. The partner map is injective on the broken directions

Distinct directions move different coordinates, or the same coordinate the opposite way.
The bounds carried in `Plaq`, plus the fact that a broken side is not outward-facing, are
what rule out the truncated cases collapsing two directions onto one plaquette. -/

theorem partnerOf_injOn {σ : Config n} (hσ : PlusBoundary σ) (P : Plaq n) :
    Set.InjOn (partnerOf P) {d : Fin 4 | sideOf P d ∈ contour σ} := by
  have hPi := P.hi
  have hPj := P.hj
  intro d hd d' hd' hEq
  have h1 := partnerOf_ne_of_mem hσ P d hd
  have h2 := partnerOf_ne_of_mem hσ P d' hd'
  have hL : sideOf P 0 ∈ contour σ → P.i ≠ 0 :=
    fun hm => exists_leftPlaq_of_sideL_mem hσ P hm
  have hU : sideOf P 1 ∈ contour σ → P.j + 2 < n :=
    fun hm => exists_upPlaq_of_sideU_mem hσ P hm
  have hR : sideOf P 2 ∈ contour σ → P.i + 2 < n :=
    fun hm => exists_rightPlaq_of_sideR_mem hσ P hm
  have hD : sideOf P 3 ∈ contour σ → P.j ≠ 0 :=
    fun hm => exists_downPlaq_of_sideD_mem hσ P hm
  fin_cases d <;> fin_cases d' <;>
    first
      | rfl
      | (exfalso
         first
           | (have := hL hd) | (have := hU hd) | (have := hR hd) | (have := hD hd)
         first
           | (have := hL hd') | (have := hU hd') | (have := hR hd') | (have := hD hd')
         have e1 := congrArg Plaq.i hEq
         have e2 := congrArg Plaq.j hEq
         simp only [partnerOf, leftP_i, leftP_j, rightP_i, rightP_j, upP_i, upP_j,
           downP_i, downP_j] at e1 e2
         omega)

/-! ## 6. The degree is the number of broken sides, and it is even -/

theorem ncard_neighborSet {σ : Config n} (hσ : PlusBoundary σ) (P : Plaq n) :
    ((dualGraph σ).neighborSet P).ncard =
      (Finset.univ.filter fun d : Fin 4 => sideOf P d ∈ contour σ).card := by
  classical
  rw [neighborSet_eq_image hσ P,
    (partnerOf_injOn hσ P).ncard_image,
    show {d : Fin 4 | sideOf P d ∈ contour σ}
        = ↑(Finset.univ.filter fun d : Fin 4 => sideOf P d ∈ contour σ) from by ext d; simp,
    Set.ncard_coe_finset]

/-- **Every plaquette has an even number of dual neighbours.** The count is
`IsingContourPlaquette.even_plaquette`'s sum, term by term and in the same order — which
is why `sideOf` lists the sides the way it does. -/
theorem evenDegrees_dualGraph {σ : Config n} (hσ : PlusBoundary σ) :
    EvenDegrees (dualGraph σ) := by
  classical
  intro P
  rw [ncard_neighborSet hσ P, Finset.card_filter, Fin.sum_univ_four]
  exact even_plaquette σ P.i P.j P.hi P.hj

/-! ## 7. The decomposition -/

/-- **THE PEIERLS STEP.** Under `+` boundary conditions, the contour of a configuration,
read on the dual lattice, is an edge-disjoint union of circuits.

This is `CycleDecomposition.exists_cycle_decomposition` applied to `dualGraph σ`, whose
degrees are even by `evenDegrees_dualGraph`. -/
theorem exists_dual_cycle_decomposition {σ : Config n} (hσ : PlusBoundary σ) :
    ∃ L : List (SimpleGraph (Plaq n)), (∀ H ∈ L, IsCycleGraph H) ∧ L.Pairwise Disjoint ∧
      L.foldr (· ⊔ ·) ⊥ = dualGraph σ :=
  (dualGraph σ).exists_cycle_decomposition (evenDegrees_dualGraph hσ)

/-- The characterisation, inherited: the dual contour decomposes into circuits exactly
when every plaquette has an even number of broken sides. Recorded because the forward
direction is the one that needed `+` boundary conditions and the converse needs
nothing. -/
theorem evenDegrees_iff_dual_decomposes (σ : Config n) :
    EvenDegrees (dualGraph σ) ↔
      ∃ L : List (SimpleGraph (Plaq n)), (∀ H ∈ L, IsCycleGraph H) ∧
        L.Pairwise Disjoint ∧ L.foldr (· ⊔ ·) ⊥ = dualGraph σ :=
  (dualGraph σ).evenDegrees_iff_exists_cycle_decomposition

/-! ## 8. The statement is not vacuous

A conditional theorem whose hypothesis nothing satisfies proves nothing, and `+`
boundary conditions plus a nonempty contour is a real constraint on a small box. So:
a configuration that satisfies the hypothesis, whose dual graph is not empty, and
whose decomposition is therefore a nonempty list of genuine circuits. -/

/-- Down at one interior site of the 4×4 box, up everywhere else. The flipped site is
interior, so the boundary is untouched. -/
def sigmaPlus : Config 4 := fun p => decide (p ≠ ((1 : Fin 4), (1 : Fin 4)))

theorem plusBoundary_sigmaPlus : PlusBoundary sigmaPlus := by
  intro p hp
  revert hp
  revert p
  decide

/-- Two plaquettes of the 4×4 box, sharing the bond that runs up the left of the
flipped site. -/
def plaq01 : Plaq 4 := ⟨0, 1, by omega, by omega⟩
/-- The plaquette to its right. -/
def plaq11 : Plaq 4 := ⟨1, 1, by omega, by omega⟩

theorem plaq11_eq_rightP : plaq11 = rightP plaq01 :=
  Plaq.ext (by simp [rightP, plaq01, plaq11]) rfl

theorem plaq11_ne_plaq01 : plaq11 ≠ plaq01 := by
  intro hc
  simpa [plaq01, plaq11] using congrArg Plaq.i hc

theorem sideR_plaq01_mem : sideR plaq01 ∈ contour sigmaPlus := by
  rw [sideR, mem_contour]
  exact ⟨by decide, by decide⟩

theorem adj_sigmaPlus : (dualGraph sigmaPlus).Adj plaq01 plaq11 :=
  ⟨2, sideR_plaq01_mem, plaq11_eq_rightP, plaq11_ne_plaq01⟩

theorem dualGraph_sigmaPlus_ne_bot : dualGraph sigmaPlus ≠ ⊥ := by
  intro hEq
  have := adj_sigmaPlus
  rw [hEq] at this
  exact this

/-- **So the decomposition really does produce circuits here.** The hypothesis is
satisfiable with a nonempty contour, and the list the general theorem returns is not
the empty one. -/
theorem sigmaPlus_decomposes_nonempty :
    ∃ L : List (SimpleGraph (Plaq 4)), L ≠ [] ∧ (∀ H ∈ L, IsCycleGraph H) ∧
      L.Pairwise Disjoint ∧ L.foldr (· ⊔ ·) ⊥ = dualGraph sigmaPlus :=
  (dualGraph sigmaPlus).exists_cycle_decomposition_ne_nil
    (evenDegrees_dualGraph plusBoundary_sigmaPlus) dualGraph_sigmaPlus_ne_bot

end DualGraph
