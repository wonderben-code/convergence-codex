import FieldEigenReflection
import RegularBipartiteSharp

/-!
# A second reflection, on the graphs the OS programme is about

`FieldEigenReflection` gives one symmetry of the Gaussian field per eigenvector of `green`, and
closed on the honest gap: **no count** — no eigenvector but the all-ones one is exhibited anywhere
in the chain. **This file exhibits a second**, on every regular two-colourable graph, and the even
torus is one in every dimension.

`PROOF_STRATEGY` §6 question 3: the previous unit was a `B` and this is the `B → C` retry.

## And the transfer three files do by hand

`green` is `massive`'s inverse, so an eigenvector of one at `μ ≠ 0` is an eigenvector of the other
at `μ⁻¹`. **The estate has never stated that.** `GreenExpansion.green_mulVec_one`,
`IndefiniteCoupling.green_mulVec_cvec` and `LaplacianBoundSharp.green_mulVec_alt` each re-derive it
inline for their own vector, by the same four lines. **`green_mulVec_of_massive_mulVec`** is the
statement; the three originals keep their proofs (`ERRATUM 337`) and are not edited.

## What is proved

**`green_mulVec_of_massive_mulVec`** — the transfer, at every finite graph, every `m ≠ 0` and every
eigenvalue `μ ≠ 0`.

**`green_mulVec_signColouring`** — on a `Δ`-regular graph carrying a `±1` labelling that flips
across every edge, `green *ᵥ σ = (2Δ + m²)⁻¹ • σ`.
`RegularBipartiteSharp.massive_mulVec_signColouring` supplies the massive half **with no regularity
at all** — the factor is the site's own degree — and regularity is what turns *"a factor per site"*
into *"an eigenvalue"*.

**`gaussianField_map_signRefl`** — so the reflection along `σ` is a symmetry of the field.

**`signRefl_ne_house`** — and it is **not** the previous unit's reflection, at any graph with an
edge: across an edge the two matrices carry `−2/|V|` and `+2/|V|`. So the chain now exhibits **two**
distinct members of the family it named, rather than one.

## What is NOT here

**Still no count.** Two is not a count. The full family is indexed by the eigenvectors of `green`,
the torus's are the characters (`TorusLaplacianSpectrum.cx_massive_mulVec_chiD`, `chiDBasis`), and
**they are complex** — extracting a real eigenbasis from them is what a count needs and it is **not
attempted, with no cost claimed** (`ERRATUM 246`).

**No new graph.** Regularity and two-colourability are hypotheses here; `TorusBipartite` and
`RegularSelfEmbedding`'s regularity supply them for the even torus, and this file does not
instantiate that composition — it states the general case and names where the instance lives.

**Still no description of the commutant**, and the degenerate-eigenspace rotations remain unbuilt.

**Not OS3 and not any OS axiom. No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldSignReflection

open Matrix GraphLaplacian FieldEigenReflection RegularBipartiteSharp

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The transfer that three files do inline -/

/-- **AN EIGENVECTOR OF `massive` AT `μ ≠ 0` IS AN EIGENVECTOR OF `green` AT `μ⁻¹`.**
`GreenExpansion.green_mulVec_one`, `IndefiniteCoupling.green_mulVec_cvec` and
`LaplacianBoundSharp.green_mulVec_alt` each do this inline for their own vector. -/
theorem green_mulVec_of_massive_mulVec (hm : m ≠ 0) {v : V → ℝ} {μ : ℝ} (hμ : μ ≠ 0)
    (hev : massive G m *ᵥ v = μ • v) : green G m *ᵥ v = μ⁻¹ • v := by
  have key : green G m *ᵥ (massive G m *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, green_mul_massive G hm, Matrix.one_mulVec]
  rw [hev, Matrix.mulVec_smul] at key
  have := congrArg (fun w : V → ℝ => μ⁻¹ • w) key
  simpa [smul_smul, inv_mul_cancel₀ hμ] using this

/-! ## 2. The sign colouring is an eigenvector of the propagator -/

/-- **ON A REGULAR TWO-COLOURABLE GRAPH THE SIGN COLOURING IS AN EIGENVECTOR OF `green`**, at
`(2Δ + m²)⁻¹`. `RegularBipartiteSharp.massive_mulVec_signColouring` needs no regularity; regularity
is what turns a factor per site into an eigenvalue. -/
theorem green_mulVec_signColouring {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) {σ : V → ℝ}
    (hσ : IsSignColouring G σ) (hm : m ≠ 0) (hpos : 2 * (Δ : ℝ) + m ^ 2 ≠ 0) :
    green G m *ᵥ σ = (2 * (Δ : ℝ) + m ^ 2)⁻¹ • σ := by
  refine green_mulVec_of_massive_mulVec hm hpos ?_
  ext v
  rw [massive_mulVec_signColouring G hσ m v, hreg v]
  simp

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A sign colouring is never the zero vector: its self-product is `|V|`. -/
theorem dotProduct_signColouring_ne_zero [Nonempty V] {σ : V → ℝ}
    (hσ : IsSignColouring G σ) : σ ⬝ᵥ σ ≠ 0 := by
  rw [dotProduct_self_signColouring hσ]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- **AND SO THE REFLECTION ALONG IT IS A SYMMETRY OF THE FIELD.** -/
theorem gaussianField_map_signRefl [Nonempty V] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    {σ : V → ℝ} (hσ : IsSignColouring G σ) (hm : m ≠ 0) (hpos : 2 * (Δ : ℝ) + m ^ 2 ≠ 0) :
    MeasureTheory.Measure.map
        (FieldHouseholder.reflIsometry (eigenRefl_isSymm σ)
          (eigenRefl_mul_self (dotProduct_signColouring_ne_zero hσ)))
        (gaussianField G m)
      = gaussianField G m :=
  gaussianField_map_eigenRefl hm (dotProduct_signColouring_ne_zero hσ)
    (green_mulVec_signColouring hreg hσ hm hpos)

/-! ## 3. It is a different reflection -/

omit [DecidableRel G.Adj] in
/-- **NOT THE ALL-ONES REFLECTION**, at any graph with an edge: across that edge the two matrices
carry `−2/|V|` and `+2/|V|`. -/
theorem signRefl_ne_house [Nonempty V] {σ : V → ℝ} (hσ : IsSignColouring G σ) {p q : V}
    (hpq : G.Adj p q) : eigenRefl σ ≠ eigenRefl (fun _ : V => (1 : ℝ)) := by
  have hcard : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hone : (fun _ : V => (1 : ℝ)) ⬝ᵥ (fun _ : V => (1 : ℝ)) = (Fintype.card V : ℝ) := by
    simp [dotProduct, Finset.card_univ]
  have hne : p ≠ q := G.ne_of_adj hpq
  have hflip : σ q = -σ p := hσ.2 q p hpq.symm
  have hsq : σ p * σ p = 1 := by rcases hσ.1 p with h | h <;> rw [h] <;> norm_num
  intro hcontra
  have hval := congrFun (congrFun hcontra p) q
  rw [eigenRefl, eigenRefl, dotProduct_self_signColouring hσ, hone] at hval
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    Matrix.one_apply_ne hne, sub_zero] at hval
  rw [hflip] at hval
  have h2 : (2 / (Fintype.card V : ℝ)) * (σ p * -σ p)
      = -((2 / (Fintype.card V : ℝ)) * (σ p * σ p)) := by ring
  rw [h2, hsq, mul_one] at hval
  have : (2 / (Fintype.card V : ℝ)) = 0 := by linarith
  rw [div_eq_zero_iff] at this
  rcases this with h | h
  · norm_num at h
  · exact hcard h

end FieldSignReflection
