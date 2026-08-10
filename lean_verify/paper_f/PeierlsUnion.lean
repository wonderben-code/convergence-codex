import ContourSubtract

/-!
# The union bound, and the Peierls estimate as a ratio

`ContourSubtract` bounds the weight of the configurations whose contour contains **one**
given contour. Peierls' comparison needs the weight of the configurations that have **some**
contour from a family — a union bound — and then the ratio to the partition function, which
is what a probability is.

## What is proved

> **`peierls_union_bound`** — if every configuration in `A` has some `γ` of a finite family
> `S` inside its contour, and every member of `S` is a realised contour, then the weight of
> `A` is at most `(∑_{γ ∈ S} exp (-4β |γ|))` times the partition function.

and its ratio form, `peierls_ratio_bound`, together with `peierls_down_ratio` for the
down-set at a site. The partition function is positive (`partition_pos`), so the division is
honest.

The proof is the estate's own fibrewise decomposition: choose for each configuration one
member of `S` inside its contour, split `A` into the fibres of that choice, and bound each
fibre by `ContourSubtract.gibbs_bound_of_subset`. No new mathematics — the union bound is
where the *choice* happens, and `Finset.sum_fiberwise_of_maps_to` is what makes the choice
harmless.

## What is missing, and it is now a single construction

**The family `S` is a hypothesis here.** Building it is the last step of Peierls' argument
and everything it needs is proved:

* `RayWalk.exists_circuit_near_of_down` — a down site has a dual circuit whose plaquette
  lies in `PlaqLocal.ball (plaqAt x) (L + 1)`, `L` the circuit's length;
* `ContourSubtract.bonds_mem_realised` — that circuit's bonds are a realised contour;
* `PlaqLocal.card_closed_walks_ball_le` — at most `(2r + 1)^2 * 4^L` closed dual walks of
  length `L` are based in a ball of radius `r`.

What is **not** built is the Finset those three describe: the bond sets of dual circuits
anchored near `x`, graded by length, with its cardinality read off the walk count. That
needs a map from circuits to walks (choice again, and an injectivity argument — a circuit
is recovered from any walk that traverses it), and then the sum over `L` of
`(2L + 3)^2 * 4^L * exp (-4βL)`, which converges for large `β` and whose convergence is
itself unformalised. **Neither piece is begun**, and
`IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace PeierlsUnion

open IsingFiniteVolume IsingContourEnergy IsingContourSeparation IsingContourClosed
open IsingContourInvariant IsingContourCocycle IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds ContourSubtract SimpleGraph

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The partition function is positive -/

/-- **The partition function is positive**, so a ratio against it is well defined. Every
term is an exponential, and there is at least one configuration — even in the empty box,
where there is exactly one. -/
theorem partition_pos (β : ℝ) : 0 < ∑ σ : Config n, Real.exp (-β * isingH n σ) := by
  refine Finset.sum_pos (fun σ _ => Real.exp_pos _) ⟨fun _ => true, Finset.mem_univ _⟩

/-! ## 2. The union bound -/

/-- **THE UNION BOUND.** If every configuration of `A` contains some member of the family
`S` in its contour, the weight of `A` is at most `∑_{γ ∈ S} exp (-4β |γ|)` times the
partition function.

The choice of *which* member is where a Peierls argument usually waves its hand; here it is
`choose!`, and the fibres of the chosen map are what `Finset.sum_fiberwise_of_maps_to`
sums. -/
theorem peierls_union_bound (hn : 0 < n) (β : ℝ) (A : Finset (Config n))
    (S : Finset (Finset (Sym2 (Site n)))) (hS : ∀ γ ∈ S, γ ∈ realisedContours n)
    (hcov : ∀ σ ∈ A, ∃ γ, γ ∈ S ∧ γ ⊆ contour σ) :
    ∑ σ ∈ A, Real.exp (-β * isingH n σ) ≤
      (∑ γ ∈ S, Real.exp (-(4 * β) * (γ.card : ℝ))) *
        ∑ σ : Config n, Real.exp (-β * isingH n σ) := by
  classical
  choose! g hgS hgsub using hcov
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := S) hgS
    (fun σ => Real.exp (-β * isingH n σ)), Finset.sum_mul]
  refine Finset.sum_le_sum fun γ hγ => ?_
  calc ∑ σ ∈ A.filter (fun σ => g σ = γ), Real.exp (-β * isingH n σ)
      ≤ ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => γ ⊆ contour σ),
          Real.exp (-β * isingH n σ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Real.exp_nonneg _
        intro σ hσ
        obtain ⟨hσA, hgσ⟩ := Finset.mem_filter.mp hσ
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ σ, hgσ ▸ hgsub σ hσA⟩
    _ ≤ Real.exp (-(4 * β) * (γ.card : ℝ)) * ∑ σ : Config n, Real.exp (-β * isingH n σ) :=
        gibbs_bound_of_subset hn β (hS γ hγ)

/-! ## 3. As a ratio, which is what a probability is -/

/-- **The same bound as a ratio.** The left side is the Gibbs probability of `A` written
out: the weight of `A` over the weight of everything. -/
theorem peierls_ratio_bound (hn : 0 < n) (β : ℝ) (A : Finset (Config n))
    (S : Finset (Finset (Sym2 (Site n)))) (hS : ∀ γ ∈ S, γ ∈ realisedContours n)
    (hcov : ∀ σ ∈ A, ∃ γ, γ ∈ S ∧ γ ⊆ contour σ) :
    (∑ σ ∈ A, Real.exp (-β * isingH n σ)) / (∑ σ : Config n, Real.exp (-β * isingH n σ)) ≤
      ∑ γ ∈ S, Real.exp (-(4 * β) * (γ.card : ℝ)) :=
  (div_le_iff₀ (partition_pos β)).mpr (peierls_union_bound hn β A S hS hcov)

/-- **And at a site**: the Gibbs probability that `x` is down is at most the sum of the
Peierls weights of any family of contours that catches every down configuration. -/
theorem peierls_down_ratio (hn : 0 < n) (β : ℝ) (x : Site n)
    (S : Finset (Finset (Sym2 (Site n)))) (hS : ∀ γ ∈ S, γ ∈ realisedContours n)
    (hcov : ∀ σ : Config n, σ x = false → ∃ γ, γ ∈ S ∧ γ ⊆ contour σ) :
    (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => σ x = false),
        Real.exp (-β * isingH n σ)) /
      (∑ σ : Config n, Real.exp (-β * isingH n σ)) ≤
      ∑ γ ∈ S, Real.exp (-(4 * β) * (γ.card : ℝ)) :=
  peierls_ratio_bound hn β _ S hS fun σ hσ => hcov σ (Finset.mem_filter.mp hσ).2

/-! ## 4. The hypothesis is satisfiable

A conditional theorem is worth what its hypothesis is worth, so: the covering hypothesis
**holds** with `S` the set of *all* realised contours — no boundary condition needed, and
none used. That instance is useless as an estimate, the sum over all realised contours
being nothing like small, and it is proved here for one reason: it shows the hypothesis is
not vacuous, and it isolates what the missing construction has to improve, which is `S` and
not the argument around it.

**The circuits do not appear in this section**, and that is the point of the gap: turning
`RayWalk`'s circuit into a *small* `S` is the construction, not this. -/

/-- **The covering hypothesis holds with `S` the realised contours**: a configuration's own
contour is realised and certainly contains itself. Unconditional. -/
theorem cover_by_all_realised (σ : Config n) :
    ∃ γ, γ ∈ realisedContours n ∧ γ ⊆ contour σ :=
  ⟨contour σ, Finset.mem_image_of_mem contour (Finset.mem_univ σ), Finset.Subset.refl _⟩

/-- **The bound is therefore never vacuous** — it holds for `S = realisedContours n` at
every site and every `β`. It is also, at that `S`, worthless: the right-hand side is the
whole contour sum. **What a Peierls estimate needs is a small `S`**, and that is the
construction named in the header. -/
theorem peierls_down_ratio_all (hn : 0 < n) (β : ℝ) (x : Site n) :
    (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => σ x = false),
        Real.exp (-β * isingH n σ)) /
      (∑ σ : Config n, Real.exp (-β * isingH n σ)) ≤
      ∑ γ ∈ realisedContours n, Real.exp (-(4 * β) * (γ.card : ℝ)) :=
  peierls_down_ratio hn β x _ (fun _ h => h) fun σ _ => cover_by_all_realised σ

end PeierlsUnion
