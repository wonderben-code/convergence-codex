import PeierlsUnion

/-!
# The dual lattice without a configuration, and the entropy count that follows

`PeierlsUnion` needs a family `S` of contours that catches **every** down configuration.
Every object the estate has for building one carries a configuration in it: `dualGraph σ`,
`bonds σ H`, and hence `PlaqLocal.card_closed_walks_ball_le`, which counts walks of
`dualGraph σ`. A family that depends on `σ` cannot be the `S` of a union bound over all
`σ`. **This file removes the configuration.**

## The two objects

* **`fullDual`** — plaquettes joined to their partners, with no reference to any
  configuration. Every `dualGraph σ` is a subgraph of it (`dualGraph_le_fullDual`), and it
  has the same degree bound, `degree_le_four`, read off `partnerOf` exactly as
  `WalkCount`'s version was read off `dualAdj`.
* **`sideBonds H`** — the primal bonds crossed by the dual edges of `H`, defined by
  quantifying over `H` alone. **`bonds_eq_sideBonds`**: for `H ≤ dualGraph σ` this *is*
  `DualBonds.bonds σ H`. So a circuit's bond set never depended on the configuration; the
  definition merely mentioned it, and `CircuitSides.mem_bonds_iff_adj` is what shows the
  mention is inert.

## The count that follows

`card_closed_walks_ball_le` reappears for `fullDual`: **at most `(2r + 1) ^ 2 * 4 ^ L`
closed dual walks of length `L` are based within `r` of a plaquette**, now with no `σ`
anywhere in the statement. That is the bound the family's cardinality will be read off.

## What is still missing

**The family itself.** With `fullDual` and `sideBonds` in hand it is
`(ball P₀ (L+1)).biUnion (fun Q => ((fullDual.finsetWalkLength L Q Q).image
(fun w => sideBonds w.toSubgraph.spanningCoe)))`, graded by `L`, and the two things left to
prove about it are:

1. **covering** — every down configuration's circuit appears, which needs
   `RayWalk.exists_circuit_near_of_down` and then `Walk.rotate` to move the cycle's
   basepoint to the anchor plaquette (`Walk.rotate_edges` says the edges survive, which is
   what `sideBonds` reads);
2. **the summation** over `L` of `(2L + 3) ^ 2 * 4 ^ L * exp (-4βL)`, whose convergence for
   large `β` is unformalised.

Neither is begun here. `IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace DualFamily

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds CircuitSides PlaqLocal
open SimpleGraph

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The dual lattice of the box, with no configuration in it -/

/-- **The full dual graph**: every plaquette joined to each of its four partners that is
not itself. No configuration, no boundary condition. -/
def fullDual (n : ℕ) : SimpleGraph (Plaq n) where
  Adj P Q := ∃ d : Fin 4, Q = partnerOf P d ∧ Q ≠ P
  symm := by
    rintro P Q ⟨d, rfl, hne⟩
    exact ⟨opp d, (partnerOf_partnerOf P d hne).symm, hne.symm⟩
  loopless := ⟨by rintro P ⟨d, -, hne⟩; exact hne rfl⟩

@[simp] theorem fullDual_adj (P Q : Plaq n) :
    (fullDual n).Adj P Q ↔ ∃ d : Fin 4, Q = partnerOf P d ∧ Q ≠ P := Iff.rfl

/-- **Every configuration's dual graph sits inside it.** -/
theorem dualGraph_le_fullDual (σ : Config n) : dualGraph σ ≤ fullDual n := by
  rintro P Q ⟨d, -, hQ, hne⟩
  exact ⟨d, hQ, hne⟩

/-! ## 2. The degree bound, again and without a configuration -/

theorem neighborFinset_subset (P : Plaq n) :
    (fullDual n).neighborFinset P ⊆ Finset.univ.image (partnerOf P) := by
  intro Q hQ
  rw [mem_neighborFinset] at hQ
  obtain ⟨d, hQd, -⟩ := hQ
  exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, hQd.symm⟩

/-- **Every plaquette has at most four neighbours in the full dual graph.** -/
theorem degree_le_four (P : Plaq n) : (fullDual n).degree P ≤ 4 := by
  calc (fullDual n).degree P = ((fullDual n).neighborFinset P).card := rfl
    _ ≤ (Finset.univ.image (partnerOf P)).card := Finset.card_le_card (neighborFinset_subset P)
    _ ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
    _ = 4 := by simp

/-- **At most `4 ^ L` closed walks of length `L` at a plaquette**, with no configuration in
the statement. -/
theorem card_closed_walks_le (L : ℕ) (P : Plaq n) :
    ((fullDual n).finsetWalkLength L P P).card ≤ 4 ^ L :=
  SimpleGraph.card_finsetWalkLength_le degree_le_four L P P

/-- **And at most `(2r + 1) ^ 2 * 4 ^ L` based within `r` of a fixed plaquette.** The
`σ`-free twin of `PlaqLocal.card_closed_walks_ball_le`, and the bound the missing family's
cardinality is to be read off. -/
theorem card_closed_walks_ball_le (P : Plaq n) (r L : ℕ) :
    ∑ Q ∈ ball P r, ((fullDual n).finsetWalkLength L Q Q).card ≤ (2 * r + 1) ^ 2 * 4 ^ L := by
  calc ∑ Q ∈ ball P r, ((fullDual n).finsetWalkLength L Q Q).card
      ≤ ∑ _Q ∈ ball P r, 4 ^ L := Finset.sum_le_sum fun Q _ => card_closed_walks_le L Q
    _ = (ball P r).card * 4 ^ L := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (2 * r + 1) ^ 2 * 4 ^ L := Nat.mul_le_mul_right _ (card_ball_le P r)

/-- **THE SAME BALL SUM OVER CYCLES, WITH THE TEXTBOOK CONSTANT: `(2r+1)^2 · 4 · 3 ^ L`.**
`card_closed_walks_ball_le` above throws the cycle hypothesis away and counts every closed
walk; `SimpleGraph.card_cycles_nb_le` keeps it, and a cycle cannot immediately reverse. -/
theorem card_cycles_ball_le (P : Plaq n) (r L : ℕ) :
    ∑ Q ∈ ball P r,
        (((fullDual n).finsetWalkLength (L + 1) Q Q).filter fun w => w.IsCycle).card
      ≤ (2 * r + 1) ^ 2 * (4 * 3 ^ L) := by
  calc ∑ Q ∈ ball P r,
        (((fullDual n).finsetWalkLength (L + 1) Q Q).filter fun w => w.IsCycle).card
      ≤ ∑ _Q ∈ ball P r, 4 * 3 ^ L :=
        Finset.sum_le_sum fun Q _ => SimpleGraph.card_cycles_nb_le degree_le_four L Q
    _ = (ball P r).card * (4 * 3 ^ L) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (2 * r + 1) ^ 2 * (4 * 3 ^ L) := Nat.mul_le_mul_right _ (card_ball_le P r)

/-! ## 3. A dual subgraph's bonds do not depend on the configuration

`DualBonds.bonds` filters the contour, so its *definition* mentions `σ`. For a subgraph of
`dualGraph σ` the filter is inert — every side of an edge of such a subgraph is broken —
and `CircuitSides.mem_bonds_iff_adj` is exactly that fact. So the same set is definable
without `σ`. -/

/-- The primal bonds crossed by the dual edges of `H`, defined from `H` alone. -/
noncomputable def sideBonds (H : SimpleGraph (Plaq n)) : Finset (Sym2 (Site n)) :=
  Finset.univ.filter fun e => ∃ (P : Plaq n) (d : Fin 4), H.Adj P (partnerOf P d) ∧
    sideOf P d = e

theorem mem_sideBonds {H : SimpleGraph (Plaq n)} {e : Sym2 (Site n)} :
    e ∈ sideBonds H ↔ ∃ (P : Plaq n) (d : Fin 4), H.Adj P (partnerOf P d) ∧ sideOf P d = e := by
  simp [sideBonds]

/-- **A circuit's bond set never depended on the configuration.** For any subgraph of
`dualGraph σ`, the `σ`-indexed `bonds σ H` and the `σ`-free `sideBonds H` are the same
Finset. -/
theorem bonds_eq_sideBonds {σ : Config n} {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) : bonds σ H = sideBonds H := by
  ext e
  constructor
  · intro he
    obtain ⟨-, P, d, hadj, hside⟩ := mem_bonds.mp he
    exact mem_sideBonds.mpr ⟨P, d, hadj, hside⟩
  · intro he
    obtain ⟨P, d, hadj, rfl⟩ := mem_sideBonds.mp he
    exact (mem_bonds_iff_adj hle P d).mpr hadj

/-- Consequently a circuit's bonds are a realised contour, said without the configuration
that produced the circuit appearing in the *set*. -/
theorem sideBonds_mem_realised {σ : Config n} (hσ : PlusBoundary σ)
    {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) :
    sideBonds H ∈ IsingContourInvariant.realisedContours n :=
  bonds_eq_sideBonds hle ▸ ContourSubtract.bonds_mem_realised hσ hle hcyc

/-- And the containment the union bound consumes: a circuit's bonds lie in the contour of
any configuration whose dual graph contains the circuit. -/
theorem sideBonds_subset_contour {σ : Config n} {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) : sideBonds H ⊆ contour σ :=
  bonds_eq_sideBonds hle ▸ bonds_subset σ H

/-! ## 4. What the missing family will be

Recorded as a definition rather than as prose, so that the next attempt starts from an
object. **Its size is bounded here and its covering is not** — which is the whole of what
is left, and the two are not equally hard: the size is §2 with `Finset.card_biUnion_le` in
front of it, and the covering needs `RayWalk` and a rotation. -/

/-- The bond sets of closed dual walks of length `L` based within `r` of `P₀`. This is the
shape the Peierls family must take. **No theorem here says it covers anything** — only
`card_candidates_le`, which bounds how many members it has. -/
noncomputable def candidates (P₀ : Plaq n) (r L : ℕ) : Finset (Finset (Sym2 (Site n))) :=
  (ball P₀ r).biUnion fun Q =>
    ((fullDual n).finsetWalkLength L Q Q).image fun w =>
      sideBonds (w.toSubgraph.spanningCoe : SimpleGraph (Plaq n))

/-- **How big it is** — the one thing about `candidates` that is proved, and it follows
from §2 with nothing else. -/
theorem card_candidates_le (P₀ : Plaq n) (r L : ℕ) :
    (candidates P₀ r L).card ≤ (2 * r + 1) ^ 2 * 4 ^ L := by
  calc (candidates P₀ r L).card
      ≤ ∑ Q ∈ ball P₀ r,
          (((fullDual n).finsetWalkLength L Q Q).image fun w =>
            sideBonds (w.toSubgraph.spanningCoe : SimpleGraph (Plaq n))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ Q ∈ ball P₀ r, ((fullDual n).finsetWalkLength L Q Q).card :=
        Finset.sum_le_sum fun Q _ => Finset.card_image_le
    _ ≤ (2 * r + 1) ^ 2 * 4 ^ L := card_closed_walks_ball_le P₀ r L

end DualFamily
