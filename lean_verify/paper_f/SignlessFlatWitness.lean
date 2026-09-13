import IndefiniteCoupling
import HermitianFlatSpectrum
import TorusMultiplicity

/-!
# A flat signless spectrum that is not a simple one

**THE HALF OF `HermitianFlatSpectrum`'s FENCE THAT STAYED SHUT.** That file proved the
multiplicity pigeonhole is attained exactly when every multiplicity is the same, exhibited an
infinite family of witnesses — the path at every length — and said in terms that all of them are
**simple**, so all attain the bound with `M = 1`: *a flat spectrum with `M ≥ 2` — every eigenvalue
equally degenerate, more than once — is attainment that is not simplicity, and no graph in this
estate is known to have one.* **Here is one, on four vertices.**

**`IndefiniteCoupling.crossGraph`** is `Adj p q ↔ p + q = 3 ∧ p ≠ q` on `Fin 4`: the perfect
matching `{0,3}, {1,2}`, two disjoint edges. The estate has had it since the indefinite-coupling
chain and has used it for a reflection, never for a spectrum. Every degree is `1`, so
`Q = D + A = 1 + A`, and `A² = 1` for a matching — hence **`signlessLap_sq`: `Q² = 2Q`**, so `Q/2`
is idempotent and every eigenvalue is `0` or `2` before any eigenvector is written down.

**AND BOTH MULTIPLICITIES ARE `2`.** `evBasis` is the eigenbasis — `e₀ − e₃`, `e₁ − e₂` at `0` and
`e₀ + e₃`, `e₁ + e₂` at `2` — and `TorusMultiplicity.finrank_eigenspace_of_basis`, generalised off
`ℂ` earlier today, turns it into exact multiplicities as fibre counts. Four vertices, two distinct
eigenvalues, both of multiplicity two: **`4 = 2 · 2`, the bound attained with `M = 2`.**

## What is proved

**`deg_one`**, **`signlessLap_sq`** — every degree is `1`, and `Q² = 2Q`.

**`ev`, `evVal`, `ev_eigen`, `ev_indep`, `evBasis`** — the four eigenvectors, their values, and
that they are a basis.

**`finrank_eigenspace_cross`** — every multiplicity as a fibre count; **`finrank_zero_cross`** and
**`finrank_two_cross`**, both `2`.

**`image_eigenvalues_cross`** — the spectrum is exactly `{0, 2}`.

**`herm_cross`**, **`ev_ne_zero`**, **`evBasis_apply`** — the symmetry, the four vectors being
non-zero, and the basis evaluating to them.

**`flat_cross`**, **`attained_cross`** — **THE FILE'S POINT**: every eigenvalue of `Q` on this
graph has multiplicity `2`, so `4 = 2 · 2` — the pigeonhole bound attained, and **the graph is not
simple**.

## What is NOT here

* **NO FAMILY, as of 2026-09-13 (entry 14).** `m` disjoint edges would give a flat spectrum with
  `M = m` for every `m`, by the same argument — `Q = 1 + A`, `A² = 1`, kernel and cokernel each of
  dimension `m`. **That family is not constructed here**: this estate has the four-vertex case as
  a named graph and no general disjoint-union constructor, and building one is a unit of its own.
  So what is exhibited is **one** graph with `M = 2`, not a sequence with `M` unbounded.
* **NOTHING ABOUT CONNECTED GRAPHS, as of 2026-09-13 (entry 14).** This witness is disconnected,
  and disconnectedness is doing real work — the two eigenvalues are the two ends of a single edge,
  repeated. **Whether a CONNECTED graph can have a flat signless spectrum with `M ≥ 2` is open**,
  is not attempted, and is the sharper form of the question this file answers (`ERRATUM 246`).
* **NOTHING ABOUT `L`.** The graph is two-colourable, so today's transfer says `L`'s multiplicities
  match `Q`'s and its spectrum is flat too; **that composition is not made here** and no
  declaration below mentions `lapMatrix`.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): **none.** Every theorem is about one named
four-vertex graph.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessFlatWitness

open Matrix SimpleGraph LaplacianSignless IndefiniteCoupling

/-! ## 1. Two disjoint edges: `Q = 1 + A` and `Q² = 2Q` -/

theorem deg_one (p : Fin 4) : ((crossGraph.degree p : ℕ) : ℝ) = 1 := by
  rw [degree_eq_one]; norm_num

/-- **`Q` IS TWICE AN IDEMPOTENT**, so its spectrum is inside `{0, 2}` before any eigenvector is
written down. A matching has `A² = 1` and every degree `1`, so `Q² = (1 + A)² = 2(1 + A)`. -/
theorem signlessLap_sq :
    signlessLap crossGraph * signlessLap crossGraph = 2 • signlessLap crossGraph := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [signlessLap, SimpleGraph.degMatrix, SimpleGraph.adjMatrix, Matrix.mul_apply,
      Fin.sum_univ_four, deg_one, Matrix.diagonal] <;> norm_num

/-! ## 2. The eigenbasis -/

/-- `e₀ − e₃` and `e₁ − e₂` at `0`; `e₀ + e₃` and `e₁ + e₂` at `2`. -/
def ev : Fin 4 → (Fin 4 → ℝ)
  | 0 => ![1, 0, 0, -1]
  | 1 => ![0, 1, -1, 0]
  | 2 => ![1, 0, 0, 1]
  | 3 => ![0, 1, 1, 0]

/-- The eigenvalue each one carries. -/
def evVal : Fin 4 → ℝ := ![0, 0, 2, 2]

theorem ev_eigen (k : Fin 4) : signlessLap crossGraph *ᵥ ev k = evVal k • ev k := by
  fin_cases k <;>
    (funext v; fin_cases v <;>
      simp +decide [ev, evVal, signlessLap, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
        Matrix.mulVec, dotProduct, Fin.sum_univ_four, deg_one, Matrix.diagonal] <;> norm_num)

theorem ev_indep : LinearIndependent ℝ ev := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrFun hg
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp [ev, Fin.sum_univ_four] at h0 h1 h2 h3
  fin_cases i <;> simp <;> linarith

noncomputable def evBasis : Module.Basis (Fin 4) ℝ (Fin 4 → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank ev_indep (by simp)

@[simp] theorem evBasis_apply (k : Fin 4) : evBasis k = ev k := by
  simp [evBasis]

/-! ## 3. So every multiplicity is two -/

theorem finrank_eigenspace_cross (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap crossGraph)
        - μ • LinearMap.id))
      = Nat.card {k : Fin 4 // evVal k = μ} :=
  TorusMultiplicity.finrank_eigenspace_of_basis _ evBasis evVal
    (fun k => by rw [evBasis_apply]; exact ev_eigen k) μ

theorem finrank_zero_cross :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap crossGraph)
      - (0 : ℝ) • LinearMap.id)) = 2 := by
  classical
  rw [finrank_eigenspace_cross, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : (Finset.univ.filter fun k : Fin 4 => evVal k = 0) = {0, 1} := by
    ext k; fin_cases k <;> simp [evVal]
  rw [h]; decide

theorem finrank_two_cross :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap crossGraph)
      - (2 : ℝ) • LinearMap.id)) = 2 := by
  classical
  rw [finrank_eigenspace_cross, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : (Finset.univ.filter fun k : Fin 4 => evVal k = 2) = {2, 3} := by
    ext k; fin_cases k <;> simp [evVal]
  rw [h]; decide

theorem herm_cross : (signlessLap crossGraph).IsHermitian :=
  LaplacianSignlessDefinite.signlessLap_isHermitian _

theorem ev_ne_zero (k : Fin 4) : ev k ≠ 0 := by
  fin_cases k <;>
    (intro h; have := congrFun h 0; have := congrFun h 1; simp [ev] at *)

/-- **THE SPECTRUM IS EXACTLY `{0, 2}`.** -/
theorem image_eigenvalues_cross :
    Finset.univ.image herm_cross.eigenvalues = ({0, 2} : Finset ℝ) := by
  classical
  ext μ
  rw [HermitianCharpoly.mem_image_eigenvalues_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx0, hx⟩
    have hpos : 0 < Nat.card {k : Fin 4 // evVal k = μ} := by
      rw [← finrank_eigenspace_cross]
      refine Module.finrank_pos_iff.mpr ⟨⟨x, ?_⟩, ⟨0, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker]
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
        rw [Matrix.toLin'_apply, hx, sub_self]
      · exact Submodule.zero_mem _
      · exact fun h => hx0 (congrArg Subtype.val h)
    obtain ⟨⟨k, hk⟩⟩ := Nat.card_pos_iff.mp hpos |>.1
    fin_cases k <;> simp [evVal] at hk <;> simp [← hk]
  · rintro (rfl | rfl)
    · exact ⟨ev 0, ev_ne_zero 0, by simpa [evVal] using ev_eigen 0⟩
    · exact ⟨ev 2, ev_ne_zero 2, by simpa [evVal] using ev_eigen 2⟩

/-- **EVERY MULTIPLICITY IS `2`, SO THE BOUND IS ATTAINED AND THE GRAPH IS NOT SIMPLE.** -/
theorem flat_cross :
    ∀ μ ∈ Finset.univ.image herm_cross.eigenvalues,
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap crossGraph)
        - μ • LinearMap.id)) = 2 := by
  intro μ hμ
  rw [image_eigenvalues_cross] at hμ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hμ
  rcases hμ with rfl | rfl
  · exact finrank_zero_cross
  · exact finrank_two_cross

/-- The pigeonhole bound, attained with `M = 2`: four vertices, two eigenvalues, both double. -/
theorem attained_cross :
    Fintype.card (Fin 4) = (Finset.univ.image herm_cross.eigenvalues).card * 2 :=
  (HermitianFlatSpectrum.forall_finrank_eq_iff herm_cross
    (fun μ hμ => le_of_eq (flat_cross μ hμ))).2 flat_cross

end SignlessFlatWitness
