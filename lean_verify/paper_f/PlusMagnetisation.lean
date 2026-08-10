import PeierlsConditional

/-!
# The conditional magnetisation is bounded below, uniformly in the box

`PeierlsConditional` bounds the probability that an **interior** site is down, given `+`
boundary conditions. Of the three things it named as remaining, this file does one and a
half: **every site** rather than every interior site, and the passage to a magnetisation
**as a ratio of sums** — not as the integral against a measure that
`IsingBoundaryField.MagnetisationBound` is written with.

## Every site, not just the interior ones

A boundary site is **never** down under `+` boundary conditions — that is what the
hypothesis says — so the event is empty there and its probability is zero. Removing the
interiority hypothesis therefore costs one lemma (`down_empty_of_boundary`) and is worth
having, because a magnetisation is a sum over **all** sites and cannot skip the edge.

## From probabilities to the magnetisation

`IsingBoundaryField.magnetisation` is `∑_p spin (σ p)`, so the conditional expectation of
the magnetisation is `∑_p (1 - 2 · P(p is down))`. With every term at least `1 - 2ε`:

> **`magnetisation_ge`** — at every low enough temperature, for **every box**, the
> conditional expectation of the magnetisation given `+` boundary conditions is at least
> `(1 - 2ε) n²`.

That is the Peierls conclusion in the shape physics states it: **magnetisation per site
bounded below, uniformly in the volume**.

## What this is not

**It is not `IsingBoundaryField.MagnetisationBound`, and the distance is not one step.**
That `def` is an integral against `isingMeasure n h β` — the Gibbs measure of the
boundary-**field** Hamiltonian, over **all** configurations, at a **fixed finite** `h`.
This file's expectation is a ratio of sums over the `+`-**boundary** configurations of the
**field-free** Hamiltonian. Two things separate them and **neither is worked out here**:

* **the set-ups.** A finite boundary field does not force the boundary up; it only favours
  it. Recovering a `+` boundary condition from a field is a limit in `h`, and this file
  does **not** determine which limit or on what terms — an earlier draft of this header
  asserted `h → 0⁺`, which is the standard route for a *bulk* field and is very likely the
  wrong statement for a *boundary* one. The honest position is that the comparison is
  unexamined.
* **the object.** `MagnetisationBound` integrates against a measure; this is a ratio of
  finite sums. The estate has no `+`-conditioned measure, and inventing one to make the
  shapes match would hide the first gap rather than close it.

`MagnetisationBound` remains untouched.
-/

namespace PlusMagnetisation

open IsingFiniteVolume IsingContourEnergy IsingBoundaryField DualObstruction
open PeierlsConditional Filter

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. A boundary site is never down -/

/-- Under `+` boundary conditions there is no configuration with a **boundary** site down,
so the event is empty and the estimate holds there for nothing. -/
theorem down_empty_of_boundary {x : Site n} (hx : isBoundary x = true) :
    (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ ∧ σ x = false) = ∅ := by
  refine Finset.filter_eq_empty_iff.mpr fun σ _ => ?_
  rintro ⟨hplus, hdown⟩
  rw [hplus x hx] at hdown
  exact Bool.noConfusion hdown

/-- **The estimate at every site.** For an interior site this is
`PeierlsConditional.peierls_conditional_small`; for a boundary site the numerator is zero. -/
theorem peierls_all_sites {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ β : ℝ in atTop, ∀ (n : ℕ), 0 < n → ∀ x : Site n,
      (∑ σ ∈ (Finset.univ : Finset (Config n)).filter
          (fun σ => PlusBoundary σ ∧ σ x = false), Real.exp (-β * isingH n σ)) /
        (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          Real.exp (-β * isingH n σ)) < ε := by
  filter_upwards [peierls_conditional_small hε] with β hβ n hn x
  by_cases hb : isBoundary x = true
  · rw [down_empty_of_boundary hb, Finset.sum_empty, zero_div]
    exact hε
  · have hx1 : x.1.val + 1 < n := by
      have := x.1.isLt
      by_contra hc
      exact hb (by simp only [isBoundary, decide_eq_true_eq]; omega)
    have hx2 : x.2.val + 1 < n := by
      have := x.2.isLt
      by_contra hc
      exact hb (by simp only [isBoundary, decide_eq_true_eq]; omega)
    exact hβ n hn x hx1 hx2

/-! ## 2. The magnetisation, site by site

`spin b` is `1` when `b` is up and `-1` when it is down, so summing the weights of the
`+`-boundary configurations against `spin (σ p)` is the total weight minus twice the weight
of the ones with `p` down. -/

theorem sum_spin_eq (β : ℝ) (p : Site n) :
    ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
        spin (σ p) * Real.exp (-β * isingH n σ) =
      (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          Real.exp (-β * isingH n σ)) -
        2 * ∑ σ ∈ ((Finset.univ : Finset (Config n)).filter
            (fun σ => PlusBoundary σ)).filter (fun σ => σ p = false),
              Real.exp (-β * isingH n σ) := by
  classical
  set F := (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ) with hF
  have hdown : ∀ σ ∈ F.filter (fun σ => σ p = false),
      spin (σ p) * Real.exp (-β * isingH n σ) = -Real.exp (-β * isingH n σ) := by
    intro σ hσ
    rw [(Finset.mem_filter.mp hσ).2]
    simp [spin]
  have hup : ∀ σ ∈ F.filter (fun σ => ¬ σ p = false),
      spin (σ p) * Real.exp (-β * isingH n σ) = Real.exp (-β * isingH n σ) := by
    intro σ hσ
    have h := (Finset.mem_filter.mp hσ).2
    cases hb : σ p
    · exact absurd hb h
    · simp [spin]
  rw [← Finset.sum_filter_add_sum_filter_not F (fun σ => σ p = false)
      (fun σ => spin (σ p) * Real.exp (-β * isingH n σ)),
    ← Finset.sum_filter_add_sum_filter_not F (fun σ => σ p = false)
      (fun σ => Real.exp (-β * isingH n σ)),
    Finset.sum_congr rfl hdown, Finset.sum_congr rfl hup, Finset.sum_neg_distrib]
  ring

/-! ## 3. So the conditional magnetisation is bounded below -/

/-- **THE PEIERLS CONCLUSION, AS PHYSICS STATES IT.** At every low enough temperature, for
**every box**, the conditional expectation of the magnetisation given `+` boundary
conditions is at least `(1 - 2ε)` times the number of sites.

Written as a ratio of finite sums, not as an integral against a measure: the estate has no
`+`-conditioned measure object, and the header says why building one here would hide a gap
instead of closing it. **This is not `IsingBoundaryField.MagnetisationBound`** — that is an
integral against the boundary-**field** measure at fixed finite `h`, and how a finite field
compares with a `+` boundary condition is not examined anywhere in this estate. -/
theorem magnetisation_ge {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ β : ℝ in atTop, ∀ (n : ℕ), 0 < n →
      (1 - 2 * ε) * ((n : ℝ) * n) ≤
        (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
            magnetisation n σ * Real.exp (-β * isingH n σ)) /
          (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
            Real.exp (-β * isingH n σ)) := by
  filter_upwards [peierls_all_sites hε] with β hβ n hn
  classical
  set Z : ℝ := ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
    Real.exp (-β * isingH n σ) with hZ
  have hZpos : 0 < Z := plus_partition_pos β
  rw [le_div_iff₀ hZpos]
  -- the numerator is a sum over sites of `Z - 2 * (weight of the down configurations)`
  have hsplit : ∀ p : Site n, ((Finset.univ : Finset (Config n)).filter
      (fun σ => PlusBoundary σ)).filter (fun σ => σ p = false) =
      (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ ∧ σ p = false) := by
    intro p; ext σ; simp
  have hnum : ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
      magnetisation n σ * Real.exp (-β * isingH n σ) =
      ∑ p : Site n, (Z - 2 * ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ => PlusBoundary σ ∧ σ p = false), Real.exp (-β * isingH n σ)) := by
    have hexp : ∀ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
        magnetisation n σ * Real.exp (-β * isingH n σ) =
          ∑ p : Site n, spin (σ p) * Real.exp (-β * isingH n σ) := by
      intro σ _
      rw [magnetisation, Finset.sum_mul]
    rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => by rw [sum_spin_eq β p, hsplit p]
  rw [hnum]
  -- each site contributes at least `(1 - 2ε) * Z`
  have hsite : ∀ p : Site n, (1 - 2 * ε) * Z ≤
      Z - 2 * ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ => PlusBoundary σ ∧ σ p = false), Real.exp (-β * isingH n σ) := by
    intro p
    have hlt := hβ n hn p
    rw [div_lt_iff₀ hZpos] at hlt
    nlinarith
  calc (1 - 2 * ε) * ((n : ℝ) * n) * Z
      = ∑ _p : Site n, (1 - 2 * ε) * Z := by
        rw [Finset.sum_const, Finset.card_univ]
        simp only [nsmul_eq_mul]
        rw [show (Fintype.card (Site n) : ℝ) = (n : ℝ) * n from by
          simp [Site, Fintype.card_prod]]
        ring
    _ ≤ _ := Finset.sum_le_sum fun p _ => hsite p

end PlusMagnetisation
