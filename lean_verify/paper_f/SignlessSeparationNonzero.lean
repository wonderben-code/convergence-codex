import SignlessColourableNecessary
import HermitianDimensionSum

/-!
# Zero is never the only place they differ

**THE QUESTION THE PREVIOUS UNIT LEFT OPEN, ANSWERED IN GENERAL RATHER THAN BY AN EXAMPLE.**
`SignlessColourableNecessary` proved that a graph is two-colourable exactly when `Q` and `L` have
the same multiplicity at every real `μ`, and that the reverse direction reads only `μ = 0`. It
fenced itself in these words: *it does not say `0` is the only separating value, and no example is
computed where some other `μ` separates — that would need a graph's full signless spectrum off the
two-colourable case, and the estate has exactly one.*

**NO SPECTRUM IS NEEDED, AND NO EXAMPLE.** Both matrices are real symmetric, so for each the
eigenspace dimensions over a finite set containing its spectrum add up to **the number of
vertices** — that is `HermitianDimensionSum.sum_finrank_eq_of_subset`, proved the same day as the
theorem this file extends. Take a finite set containing both spectra and `0`. The two totals are
the same number. **A deficit at `0` must therefore be paid back somewhere else**, and the previous
unit says the deficit at `0` is exactly the failure of two-colourability. So on **every** graph
that is not two-colourable there is a **non-zero** `μ` at which `Q` has *strictly more*
multiplicity than `L`.

**WHICH IS A STRONGER ANSWER THAN THE EXAMPLE WOULD HAVE BEEN**: not *some graph separates away
from zero* but *every graph that separates at all separates away from zero as well*, with no
hypothesis beyond a finite vertex type.

## What is proved

**`ker_sub_zero_smul`** — the eigenspace at `0` is the kernel. A rewrite the previous unit did
twice inline; named here because this file needs it three times.

**`sum_finrank_eq_card_spectra`** — over a finite set containing both spectra, the dimensions of
`Q`'s eigenspaces and of `L`'s each total the number of vertices. Two instances of one Hermitian
theorem, put together so the next line can subtract them.

**`exists_ne_zero_finrank_signlessLap_gt`** — **THE FILE'S THEOREM.** On a graph that is not
two-colourable there is a `μ ≠ 0` with `finrank ker (Q − μ) > finrank ker (L − μ)`. **`Q` is
short at zero and long somewhere else, always.**

**`exists_ne_zero_of_not_forall_finrank_eq`** — the same conclusion from the hypothesis in the
previous unit's own vocabulary: if the two disagree anywhere, they disagree away from zero.

## What is NOT here

* **NO `μ` IS NAMED.** The theorem is an existence statement got by counting, and the counting
  cannot say **which** value pays the deficit. On the odd cycle the estate could in principle name
  it; nothing here does, and no spectrum is computed anywhere in this file.
* **NO CONVERSE AT A FIXED `μ`.** Nothing says that a graph agreeing at some particular non-zero
  `μ` is two-colourable; the previous unit's biconditional quantifies over **all** `μ` and this
  one does not sharpen that.
* **NO STATEMENT ABOUT `L` EXCEEDING `Q` AWAY FROM ZERO.** The excess proved here runs one way —
  `Q` over `L` — because the deficit at zero runs the other. Whether `L` can also exceed `Q` at
  some value is not asked and not answered.
* **NOTHING ABOUT THE CHARACTERISTIC POLYNOMIAL, NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED
  TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a finite vertex type with decidable
equality and decidable adjacency, and `¬ G.Colorable 2`. **No connectivity, no `Nonempty`** — the
empty graph is two-colourable, so the hypothesis rules it out by itself.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessSeparationNonzero

open Matrix SimpleGraph LaplacianSignless SignlessColourableNecessary

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The eigenspace at zero is the kernel -/

/-- Named because this file needs it three times; `SignlessColourableNecessary` did it twice
inline. -/
theorem ker_sub_zero_smul (A : Matrix V V ℝ) :
    LinearMap.ker (Matrix.toLin' A - (0 : ℝ) • LinearMap.id) = LinearMap.ker (Matrix.toLin' A) := by
  simp

/-! ## 2. Both totals are the number of vertices -/

/-- The finite set this file counts over: both spectra, and `0`. -/
noncomputable def spectra : Finset ℝ :=
  insert 0 ((Finset.univ.image
      (LaplacianSignlessDefinite.signlessLap_isHermitian G).eigenvalues)
    ∪ (Finset.univ.image (SignlessBipartite.lapMatrix_isHermitian' G).eigenvalues))

theorem zero_mem_spectra : (0 : ℝ) ∈ spectra G := Finset.mem_insert_self _ _

/-- **BOTH SETS OF DIMENSIONS TOTAL THE NUMBER OF VERTICES.** -/
theorem sum_finrank_eq_card_spectra :
    (∑ μ ∈ spectra G, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap G) - μ • LinearMap.id)) = Fintype.card V)
    ∧ (∑ μ ∈ spectra G, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id)) = Fintype.card V) := by
  classical
  refine ⟨HermitianDimensionSum.sum_finrank_eq_of_subset
      (LaplacianSignlessDefinite.signlessLap_isHermitian G) ?_,
    HermitianDimensionSum.sum_finrank_eq_of_subset
      (SignlessBipartite.lapMatrix_isHermitian' G) ?_⟩
  · exact fun μ hμ => Finset.mem_insert_of_mem (Finset.mem_union_left _ hμ)
  · exact fun μ hμ => Finset.mem_insert_of_mem (Finset.mem_union_right _ hμ)

/-! ## 3. So the deficit at zero is paid somewhere else -/

/-- **`Q` IS SHORT AT ZERO AND LONG SOMEWHERE ELSE, ON EVERY GRAPH THAT IS NOT TWO-COLOURABLE.** -/
theorem exists_ne_zero_finrank_signlessLap_gt (hcol : ¬ G.Colorable 2) :
    ∃ μ : ℝ, μ ≠ 0 ∧
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id))
        < Module.finrank ℝ (LinearMap.ker
            (Matrix.toLin' (signlessLap G) - μ • LinearMap.id)) := by
  classical
  obtain ⟨hQ, hL⟩ := sum_finrank_eq_card_spectra G
  -- At zero `Q` is strictly short, by the previous unit.
  have hzero : Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap G) - (0 : ℝ) • LinearMap.id))
      < Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - (0 : ℝ) • LinearMap.id)) := by
    rw [ker_sub_zero_smul, ker_sub_zero_smul]
    exact lt_of_le_of_ne (finrank_ker_signlessLap_le_lap G)
      (fun h => hcol ((finrank_ker_eq_iff_colorable G).1 h))
  by_contra hno
  simp only [not_exists, not_and, not_lt] at hno
  -- Every other value has `Q` no longer than `L`, so the totals cannot agree.
  have hle : ∀ μ ∈ spectra G,
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G) - μ • LinearMap.id))
        ≤ Module.finrank ℝ (LinearMap.ker
            (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id)) := by
    intro μ _
    by_cases hμ : μ = 0
    · subst hμ; exact hzero.le
    · exact hno μ hμ
  have hlt : ∑ μ ∈ spectra G, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap G) - μ • LinearMap.id))
      < ∑ μ ∈ spectra G, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id)) :=
    Finset.sum_lt_sum hle ⟨0, zero_mem_spectra G, hzero⟩
  rw [hQ, hL] at hlt
  exact lt_irrefl _ hlt

/-- The same conclusion from the previous unit's own hypothesis. -/
theorem exists_ne_zero_of_not_forall_finrank_eq
    (h : ¬ ∀ μ : ℝ,
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G) - μ • LinearMap.id))
        = Module.finrank ℝ (LinearMap.ker
            (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id))) :
    ∃ μ : ℝ, μ ≠ 0 ∧
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id))
        < Module.finrank ℝ (LinearMap.ker
            (Matrix.toLin' (signlessLap G) - μ • LinearMap.id)) :=
  exists_ne_zero_finrank_signlessLap_gt G
    (fun hc => h ((colorable_two_iff_forall_finrank_eq G).1 hc))

end SignlessSeparationNonzero
