import CycleNormFromColouring
import LaplacianTopEigenspace
import LaplacianSharpEquality

/-!
# The operator norm of the periodic lattice's Laplacian, in every dimension

This estate states the periodic lattice's sharpness in the **Loewner order**
(`TorusRegular.massive_torus_le_smul_one_iff`) and in the **quadratic form / spectrum**
(`TorusAttainmentBridge`). It has never stated it in the **norm**: probed 2026-09-03,
`‖` occurs in five files that mention `torusGraph` and in none of them is it applied to a
torus object.

That gap is what this file closes, using the general theorems of 2026-09-03:

```
‖massive (torusGraph d n) m‖ = 4d + m²   ↔   Even n        (d ≥ 1, n ≥ 3, m ≠ 0)
‖(torusGraph d n).lapMatrix ℝ‖ = 4d      ↔   Even n        (d ≥ 1, n ≥ 3)
```

**No spectrum is computed and no Fourier analysis appears.** Both directions come from the
colouring: `LaplacianNormSharp.norm_massive_eq_iff_exists_component_colorable` for the equality
and `CycleNormFromColouring.norm_massive_lt_of_no_component_colorable` for the strict inequality,
with `RegularSelfEmbedding.torusGraph_isRegularOfDegree` supplying regularity,
`TorusBipartite.torusGraph_colorable_two` the even half and
`LaplacianSharpEquality.torus_not_colorable_two_of_odd` the odd half.

## And the propagator's norm does not see the lattice at all

`norm_green_torus_eq` is `‖green (torusGraph d n) m‖ = (m²)⁻¹` — **no `d`, no `n`**. It is
`GreenNormExact.norm_green_eq` at this graph and is stated here only for the contrast: the
Laplacian's norm separates even from odd side length in every dimension, and on the same family
the propagator's norm is the free constant. The all-ones vector is the eigenvector on every graph
(`GreenExpansion.green_mulVec_one`, 2026-08-12), and the periodic lattice is not special for it.

## What is NOT new here

**Not the mathematics.** Every step is a 2026-09-03 general theorem or a 29 August torus fact;
this file supplies instantiation and the two shape juggles (`d = d' + 1`, `n = n' + 1`) that
`torus_not_colorable_two_of_odd` is stated in.

**Not the even/odd dichotomy.** `TorusRegular.massive_torus_le_smul_one_iff` has the even half in
the Loewner order and `LaplacianSharpEquality.torus_odd_no_attaining_vector` the odd half for
attaining vectors, both 2026-08-29. **Nothing here is stronger than those**; it is the same
dichotomy in a currency the estate did not carry for this family.

**Not a statement about the box.** `boxGraph` has a boundary and is not regular, so none of this
reaches it — `GreenLoewnerFloorSharp.norm_massive_boxGraph_eq` is the box's norm and it is a
different theorem with a different constant.

**Not a statement about a field or a measure.** No `gaussianField`, no OS axiom, and no wall
moves.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusNormSharp

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {d n : ℕ}

/-! ## 1. The component quantifier collapses, because the torus is connected -/

/-- **ON THE PERIODIC LATTICE THE COMPONENT QUANTIFIER IS THE GRAPH ITSELF.** The general norm
theorems are stated over connected components (`ERRATUM 435`'s route: no connectivity hypothesis);
`TorusDecay.torusGraph_connected` collapses that back to the graph. -/
theorem exists_component_colorable_torus_iff (hn : 1 ≤ n) :
    (∃ C : (torusGraph d n).ConnectedComponent,
        ((torusGraph d n).induce C.supp).Colorable 2)
      ↔ (torusGraph d n).Colorable 2 := by
  haveI : Nonempty (Site d n) := TorusRegular.nonempty_site hn
  have hconn : (torusGraph d n).Connected := TorusDecay.torusGraph_connected (n := n) d hn
  constructor
  · rintro ⟨C, hC⟩
    exact (LaplacianTopEigenspace.induce_colorable_iff_of_connected (torusGraph d n) hconn C).mp hC
  · intro hcol
    obtain ⟨v⟩ := ‹Nonempty (Site d n)›
    exact ⟨(torusGraph d n).connectedComponentMk v,
      (LaplacianTopEigenspace.induce_colorable_iff_of_connected (torusGraph d n) hconn _).mpr hcol⟩

/-! ## 2. The two halves -/

/-- **`‖massive (torusGraph d n) m‖ = 4d + m²` AT EVEN SIDE LENGTH, IN EVERY DIMENSION.** -/
theorem norm_massive_torus_eq (hn : 3 ≤ n) (hev : Even n) {m : ℝ} (hm : m ≠ 0) :
    ‖massive (torusGraph d n) m‖ = 4 * (d : ℝ) + m ^ 2 := by
  haveI : Nonempty (Site d n) := TorusRegular.nonempty_site (by omega)
  have h := (LaplacianNormSharp.norm_massive_eq_iff_exists_component_colorable (torusGraph d n)
      (RegularSelfEmbedding.torusGraph_isRegularOfDegree hn) hm).mpr
      ((exists_component_colorable_torus_iff (d := d) (by omega)).mpr
        (TorusBipartite.torusGraph_colorable_two (d := d) hev))
  rw [h]
  push_cast
  ring

/-- **AND STRICTLY BELOW IT AT ODD SIDE LENGTH FROM THREE, IN EVERY POSITIVE DIMENSION.**
At `d = 0` the lattice is a point, which is two-colourable, so the hypothesis is not an artefact. -/
theorem norm_massive_torus_lt (hd : 0 < d) (hn : 3 ≤ n) (hodd : Odd n) {m : ℝ} (hm : m ≠ 0) :
    ‖massive (torusGraph d n) m‖ < 4 * (d : ℝ) + m ^ 2 := by
  haveI : Nonempty (Site d n) := TorusRegular.nonempty_site (by omega)
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hncol : ¬ (torusGraph (d' + 1) (n' + 1)).Colorable 2 :=
    LaplacianSharpEquality.torus_not_colorable_two_of_odd hodd hn
  have h := CycleNormFromColouring.norm_massive_lt_of_no_component_colorable
    (torusGraph (d' + 1) (n' + 1))
    (RegularSelfEmbedding.torusGraph_isRegularOfDegree hn) hm
    (fun C hC => hncol ((exists_component_colorable_torus_iff (by omega)).mp ⟨C, hC⟩))
  push_cast at h ⊢
  linarith

/-! ## 3. The dichotomy, and the same statement at `m = 0` -/

/-- **THE NORM SEPARATES EVEN FROM ODD SIDE LENGTH, IN EVERY DIMENSION.** -/
theorem norm_massive_torus_eq_iff_even (hd : 0 < d) (hn : 3 ≤ n) {m : ℝ} (hm : m ≠ 0) :
    ‖massive (torusGraph d n) m‖ = 4 * (d : ℝ) + m ^ 2 ↔ Even n := by
  constructor
  · intro h
    by_contra hodd
    exact absurd h (ne_of_lt (norm_massive_torus_lt hd hn (Nat.not_even_iff_odd.mp hodd) hm))
  · intro hev
    exact norm_massive_torus_eq hn hev hm

/-- **AND THE SAME AT `m = 0`, ON THE LAPLACIAN ITSELF.** -/
theorem norm_lapMatrix_torus_eq_iff_even (hd : 0 < d) (hn : 3 ≤ n) :
    ‖(torusGraph d n).lapMatrix ℝ‖ = 4 * (d : ℝ) ↔ Even n := by
  haveI : Nonempty (Site d n) := TorusRegular.nonempty_site (by omega)
  have hcast : (4 : ℝ) * (d : ℝ) = 2 * ((2 * d : ℕ) : ℝ) := by push_cast; ring
  rw [hcast, LaplacianNormSharp.norm_lapMatrix_eq_iff_exists_component_colorable (torusGraph d n)
    (RegularSelfEmbedding.torusGraph_isRegularOfDegree hn),
    exists_component_colorable_torus_iff (by omega)]
  constructor
  · intro hcol
    by_contra hodd
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact LaplacianSharpEquality.torus_not_colorable_two_of_odd
      (Nat.not_even_iff_odd.mp hodd) hn hcol
  · intro hev
    exact TorusBipartite.torusGraph_colorable_two (d := d) hev

/-! ## 4. The contrast: the propagator's norm sees neither `d` nor `n` -/

/-- **`‖green (torusGraph d n) m‖ = (m²)⁻¹`, WITH NO `d` AND NO `n`.** An instance of
`GreenNormExact.norm_green_eq`, which holds at every finite nonempty graph; stated here only
against §3, where the Laplacian's norm separates even from odd in every dimension. -/
theorem norm_green_torus_eq (hn : 1 ≤ n) {m : ℝ} (hm : m ≠ 0) :
    ‖green (torusGraph d n) m‖ = (m ^ 2)⁻¹ := by
  haveI : Nonempty (Site d n) := TorusRegular.nonempty_site hn
  exact GreenNormExact.norm_green_eq (torusGraph d n) hm

end TorusNormSharp
