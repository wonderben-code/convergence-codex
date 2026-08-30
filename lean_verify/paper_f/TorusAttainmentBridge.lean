import TorusSpectrumExtremes

/-!
# The two shapes of "the bound is reached", joined on the periodic lattice

Two files in this estate prove that the degree bound fails to be reached on the odd periodic
lattice, in every dimension, and **they do not know about each other**.

* `LaplacianSharpEquality.torus_exists_quadForm_eq_iff_colorable`: a **vector** attains
  `xᵀLx = 2·(2d)·(x⬝ᵥx)` **iff** `torusGraph d n` is two-colourable. Proved by chromatic number;
  there is no spectrum anywhere in that file, which says in terms that it is *about a supplied
  vector, not about an eigenvalue list*, and that reading `∃ x ≠ 0` with equality in the quadratic
  form as *`2Δ` is the largest eigenvalue of `L`* is **not made** there.
* `TorusSpectrumExtremes.mem_spectrum_top_iff_even`: `4d + m²` is an **eigenvalue** of
  `massive (torusGraph d (N+3)) m` **iff** the side length is even. Proved by parity of cosines;
  there is no colouring anywhere in it.

In ordinary mathematics these say the same thing, and neither implies the other as stated. **This
file joins them, and the join is cheap for a reason worth stating: both sides turn out to be
equivalent to the same third condition**, `Even n`, so they can be chained through it.

> **`torus_not_colorable_of_odd`, `torus_colorable_two_iff_even`** — the missing biconditional,
> assembled from two halves that existed under mismatched index shapes:
> `TorusBipartite.torusGraph_colorable_two` forwards and
> `LaplacianSharpEquality.torus_not_colorable_two_of_odd` (stated at `torusGraph (d+1) (n+1)`)
> backwards.
>
> **`quadForm_attained_iff_even`** — hence the quadratic-form side, restated against the side
> length instead of against a colouring.
>
> **`quadForm_attained_iff_top_mem_spectrum`** and **`quadForm_attained_iff_isGreatest`** — the
> bridge: on the periodic lattice with at least one axis, a vector attains the quadratic-form bound
> **iff** `4d + m²` is an eigenvalue of `massive`, **iff** it is the greatest one.

## What this is NOT, and the distinction is the point

**THIS IS NOT THE RAYLEIGH STATEMENT.** *A symmetric matrix's quadratic form attains its upper
bound exactly when that bound is an eigenvalue* is a general theorem about symmetric matrices.
**It is not proved here and it is not used here.** What is proved is a biconditional for **one
family**, obtained because both sides were separately characterised by the same third condition.
A reader wanting the general fact will not find it below, and `LaplacianSharpEquality`'s refusal to
assert it stands exactly as written.

**AND THE SHIFT BY `m²` IS NOT PROVED EITHER.** `GraphLaplacian.massive G m` is
`G.lapMatrix ℝ + diagonal (fun _ => m^2)`, so `2Δ = 4d` for `L` and `4d + m²` for `massive` are the
corresponding constants — **that is arithmetic about the definitions, not a theorem that the
spectrum shifts**, and no such theorem is stated below. The two sides of the bridge meet at
`Even n`, not at a shift.

**`0 < d` throughout, and it is not decoration**: at `d = 0` the odd half of
`mem_spectrum_top_iff_even` is false (the empty sum makes the bound an equality) and
`torus_not_colorable_two_of_odd` has no content (a one-point graph is one-colourable). The side
length is `N + 3` on the spectrum side because the degree formula needs `3 ≤ n`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusAttainmentBridge

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection
open TorusSpectrumExtremes MassiveTorusSpectrum

variable {d : ℕ}

/-! ## 1. Two-colourability of the periodic lattice is exactly evenness -/

/-- **AT ODD SIDE LENGTH THE PERIODIC LATTICE IS NOT TWO-COLOURABLE**, at the index shape the rest
of the estate uses. `LaplacianSharpEquality.torus_not_colorable_two_of_odd` proves this at
`torusGraph (d+1) (n+1)`; the content is entirely there and what is added is the destructuring. -/
theorem torus_not_colorable_of_odd {d n : ℕ} (hd : 0 < d) (h3 : 3 ≤ n) (hodd : Odd n) :
    ¬ (torusGraph d n).Colorable 2 := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  exact LaplacianSharpEquality.torus_not_colorable_two_of_odd hodd h3

/-- **THE BICONDITIONAL THE ESTATE HELD IN TWO HALVES.** `TorusBipartite.torusGraph_colorable_two`
is one direction and the line above is the other; neither was stated as an `↔` and the shapes did
not line up. -/
theorem torus_colorable_two_iff_even {d n : ℕ} (hd : 0 < d) (h3 : 3 ≤ n) :
    (torusGraph d n).Colorable 2 ↔ Even n := by
  constructor
  · intro hc
    rcases Nat.even_or_odd n with he | ho
    · exact he
    · exact absurd hc (torus_not_colorable_of_odd hd h3 ho)
  · exact TorusBipartite.torusGraph_colorable_two

/-! ## 2. The quadratic-form side, against the side length -/

/-- **A VECTOR ATTAINS THE DEGREE BOUND ON THE PERIODIC LATTICE IFF THE SIDE LENGTH IS EVEN.** -/
theorem quadForm_attained_iff_even {d n : ℕ} (hd : 0 < d) (h3 : 3 ≤ n) :
    (∃ x : Site d n → ℝ, x ≠ 0 ∧
        x ⬝ᵥ ((torusGraph d n).lapMatrix ℝ) *ᵥ x = 2 * ((2 * d : ℕ) : ℝ) * (x ⬝ᵥ x))
      ↔ Even n :=
  (LaplacianSharpEquality.torus_exists_quadForm_eq_iff_colorable h3).trans
    (torus_colorable_two_iff_even hd h3)

/-! ## 3. The bridge -/

/-- **THE TWO STATEMENTS ARE THE SAME STATEMENT, ON THIS FAMILY.** A vector attains the
quadratic-form bound on `torusGraph d (N+3)` **iff** `4d + m²` is an eigenvalue of `massive`. The
left side is a colouring theorem and the right side is a parity-of-cosines theorem; they meet at
`Even (N + 3)` and **not** at any general fact about symmetric matrices. -/
theorem quadForm_attained_iff_top_mem_spectrum (N : ℕ) (hd : 0 < d) (m : ℝ) :
    (∃ x : Site d (N + 3) → ℝ, x ≠ 0 ∧
        x ⬝ᵥ ((torusGraph d (N + 3)).lapMatrix ℝ) *ᵥ x
          = 2 * ((2 * d : ℕ) : ℝ) * (x ⬝ᵥ x))
      ↔ (4 * d + m ^ 2) ∈ {μ : ℝ | ∃ x : Site d (N + 3) → ℝ, x ≠ 0 ∧
          massive (torusGraph d (N + 3)) m *ᵥ x = μ • x} :=
  (quadForm_attained_iff_even hd (by omega)).trans (mem_spectrum_top_iff_even N hd m).symm

/-- **AND THE SAME AGAIN AT THE TOP OF THE SPECTRUM.** Attaining the quadratic-form bound is
equivalent to `4d + m²` being the **greatest** eigenvalue, not merely one of them — which is a
strictly stronger right-hand side than the line above, and free once completeness is in hand. -/
theorem quadForm_attained_iff_isGreatest (N : ℕ) (hd : 0 < d) (m : ℝ) :
    (∃ x : Site d (N + 3) → ℝ, x ≠ 0 ∧
        x ⬝ᵥ ((torusGraph d (N + 3)).lapMatrix ℝ) *ᵥ x
          = 2 * ((2 * d : ℕ) : ℝ) * (x ⬝ᵥ x))
      ↔ IsGreatest {μ : ℝ | ∃ x : Site d (N + 3) → ℝ, x ≠ 0 ∧
          massive (torusGraph d (N + 3)) m *ᵥ x = μ • x} (4 * d + m ^ 2) := by
  constructor
  · intro hx
    obtain ⟨M, hM⟩ := (quadForm_attained_iff_even hd (by omega)).1 hx
    have hN : N + 3 = 2 * M := by omega
    exact isGreatest_spectrum_real_of_even hN m
  · intro hgreat
    exact (quadForm_attained_iff_top_mem_spectrum N hd m).2 hgreat.1

end TorusAttainmentBridge
