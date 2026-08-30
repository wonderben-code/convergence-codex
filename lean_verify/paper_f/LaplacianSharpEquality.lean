import TorusRegular

/-!
# The equality case: the degree bound is an IDENTITY, and attaining it FORCES two-colourability

`LaplacianDegreeBound` proved `xᵀLx ≤ 2Δ‖x‖²` when every degree is at most `Δ`, and
`RegularBipartiteSharp` proved that a **regular two-colourable** graph attains it. The item those
left open asks for the converse — which regular graphs attain it — and this file answers it for
**connected** ones: exactly the two-colourable ones.

**THE INEQUALITY WAS AN IDENTITY ALL ALONG, AND THAT IS THE WHOLE PROOF.** The bound is got by
throwing away `(xᵢ + xⱼ)²` at each edge, and on a regular graph nothing else is thrown away:

```
∑ᵢ ∑ⱼ [i ∼ j] (xᵢ + xⱼ)²  =  4Δ‖x‖²  −  2·xᵀLx        (`sum_adj_add_sq`)
```

Since the left side is a sum of squares this **re-proves** the bound at `deg ≡ Δ`; what it adds is
that equality holds **iff every summand vanishes**, i.e. iff `x` flips sign across every edge
(`quadForm_eq_iff_neg_adj`, and `massive_quadForm_eq_iff_neg_adj` on the operator this project
actually uses). No connectivity, no non-vanishing, no colouring: that equivalence is unconditional
over any regular graph.

**CONNECTIVITY IS WHERE THE COLOURING COMES FROM, AND IT IS NOT A CONVENIENCE.** A sign-flipping
`x` that is somewhere non-zero is non-zero **everywhere** on a connected graph
(`ne_zero_of_connected`, one induction along a walk), and then `v ↦ sign (x v)` is a proper
two-colouring. **Dropping connectivity makes the statement false**: `C₃ ⊔ C₄` is 2-regular, the
alternating vector on its `C₄` attains the bound, and the graph is not two-colourable. That
counterexample is stated, not formalised (`ERRATUM 246`: no cost is claimed for it).

**WHAT MATHLIB HAS IS THE OTHER END OF THE SPECTRUM.**
`SimpleGraph.lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj` characterises `xᵀLx = 0` by
`xᵢ = xⱼ` across every edge, and `…_forall_reachable` upgrades it. This file is the same statement
at the **top** of the spectrum, `xᵢ = −xⱼ`. **The absence is measured rather than asserted**
(`ERRATUM 194`): `lapMatrix` occurs in exactly **one** file of Mathlib v4.29.1,
`Combinatorics/SimpleGraph/LapMatrix.lean`, and the string `eigen` occurs in it **0** times — as it
does in **all 71** files of `Combinatorics/SimpleGraph/`. Mathlib carries no spectral graph theory
at all, so there is nothing there to relate a largest eigenvalue to bipartiteness. **No difficulty
is inferred from that** (`ERRATUM 194` again): an absence is an absence.

## What this does NOT settle, and one sentence elsewhere that it makes false

**It is about a supplied vector, not about an eigenvalue list.** `∃ x ≠ 0` with equality in the
quadratic form is exactly *the largest eigenvalue of `L` equals `2Δ`*, but that identification is
**not made here**: nothing in this file is phrased with `IsHermitian.eigenvalues`, and **no
Loewner-order converse is claimed**. In particular this does **not** prove that a
non-two-colourable connected regular graph admits `c < 2Δ + m²` with `massive ≼ c·1`, which is the
form `RegularBipartiteSharp` and `CycleSpectralBound` state their results in.

**AND THAT GAP IS NOT A WALL — the route is traced, and saying so is the honest fence**
(`ERRATUM 194`: an absence here would be an absence of work, not of mathematics). This estate
already has both variational directions for an arbitrary Hermitian matrix —
`RayleighPow.eigenvalues_le_of_quadForm_le` and `RayleighMatrix.quadForm_le_of_eigenvalues_le` —
and `RayleighMatrix.mv_eigenvectorBasis` supplies the vector that attains the form at each
eigenvalue. Composed with `colorable_two_of_quadForm_eq` below, they give: not two-colourable ⇒ no
eigenvector attains ⇒ every eigenvalue is strictly below ⇒ their maximum is the `c` wanted. **That
is `CycleSpectralBound.odd_cycle_lt`'s argument with the character basis replaced by the abstract
eigenbasis, and it is the successor unit, not this one** — it needs a `dotProduct`-to-`inner`
bridge no file states yet and an import (`RayleighPow`) outside this file's closure. **No cost is
claimed for it** (`ERRATUM 246`): a traced route is not a finished one.

> **^ THAT SUCCESSOR UNIT IS DONE, THE SAME DAY: `LaplacianLoewnerConverse`.** The route above is
> the route taken, step for step, and the two pieces of plumbing named were the two pieces of
> plumbing — `inner_mv_eq`, `inner_self_eq`, `import RayleighPow`.
> **`massive_le_smul_one_iff_colorable`**: for a connected `Δ`-regular graph the constant cannot be
> lowered **iff** the graph is two-colourable. The paragraph is kept because it was exact when
> written (`ERRATUM 94`), and because a traced route that then works is worth leaving visible
> beside the three this week that did not.

**`PerronPrimitive`'s header carries a false sentence, and this file is NOT what falsified it.**
That file says the classical route to its even case needs *primitive ⇒ not bipartite ⇒ the spectrum
is not symmetric about `0`*, and that *"`bipartite` appears here only as a property of specific
lattice graphs, and no theorem anywhere relates it to a spectrum"*. **Its own §3 falsified both
halves seven days ago**: `signOf_conj` and `trace_pow_eq_zero` state bipartiteness for an
**arbitrary matrix** through a `c : n → Bool`, not for a lattice graph, and conclude that every odd
power has trace zero — which `TracePowerSpectrum.herm_trace_pow` turns into a statement about the
eigenvalues. Checked against git rather than guessed: the sentence entered at `60e6eed`
(2026-08-22) and §3 at `77cbb25`, **the same day**, without touching it. `ERRATUM 338`.

**And its step does not move either way** (`ERRATUM 278`, `ERRATUM 335`: one route's obstacle is
not the statement's). `PerronPrimitive` needs the implication for an arbitrary non-negative
symmetric matrix; `RegularBipartiteSharp` and this file are about the Laplacian of a graph, which
is a different object — and its §4 removed the odd hypothesis by a route that never needed the
chain at all, so there is no gap left to open. A dated note is added there and nothing in that file
changes.

**WHAT §5 CLOSES, AND WHOSE FENCE IT IS.** The sentence is **`TorusRegular`'s**, not
`CycleSpectralBound`'s — *"at odd side length the periodic lattice is not two-colourable —
`CycleSpectralBound` proves the `d = 1` case of exactly that failure, and nothing here says whether
the bound is attained at odd side length in higher dimensions."* That paragraph asserts the
non-colourability and proves nothing about it; §5 proves both halves. `axisHom` puts a cycle inside
the periodic lattice as a graph homomorphism, so `Colorable.of_hom` pulls Mathlib's
`chromaticNumber_cycleGraph_of_odd` back: **`torus_not_colorable_two_of_odd`**, and then by the
characterisation above **no vector attains the bound, at every odd side length at least three and
in every dimension**. No spectrum is computed anywhere in that argument. `CycleSpectralBound`'s own
fence — *"`d = 1` only, `Δ = 2` only"* — is accurate about that file and is untouched.

**No measure is built, `OS4` does not move, and no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LaplacianSharpEquality

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The identity behind the bound -/

omit [DecidableEq V] in
/-- The degree-weighted square sum, read off the LEFT index of each edge. -/
theorem sum_adj_sq_left (x : V → ℝ) :
    (∑ i : V, ∑ j : V, if G.Adj i j then x i ^ 2 else 0)
      = ∑ i : V, (G.degree i : ℝ) * x i ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [G.degree_eq_sum_if_adj (R := ℝ) i, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by by_cases h : G.Adj i j <;> simp [h]

omit [DecidableEq V] in
/-- The same sum read off the RIGHT index, which is where `adj_comm` earns its keep. -/
theorem sum_adj_sq_right (x : V → ℝ) :
    (∑ i : V, ∑ j : V, if G.Adj i j then x j ^ 2 else 0)
      = ∑ i : V, (G.degree i : ℝ) * x i ^ 2 := by
  rw [Finset.sum_comm, ← sum_adj_sq_left G x]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : G.Adj b a
  · rw [if_pos h, if_pos ((G.adj_comm b a).mp h)]
  · rw [if_neg h, if_neg (fun hc => h ((G.adj_comm a b).mp hc))]

/-- **THE IDENTITY BEHIND THE BOUND, WITH NO REGULARITY.** For ANY finite graph, the sum of
`(xᵢ + xⱼ)²` over ordered adjacent pairs is `4·Σᵢ deg(i)·xᵢ² − 2·xᵀLx`. Regularity enters only when
the degree-weighted sum is collapsed to `Δ‖x‖²`, which is the corollary below. -/
theorem sum_adj_add_sq_of_degree (x : V → ℝ) :
    (∑ i : V, ∑ j : V, if G.Adj i j then (x i + x j) ^ 2 else 0)
      = 4 * (∑ i : V, (G.degree i : ℝ) * x i ^ 2) - 2 * (x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x) := by
  have hq : x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x
      = (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 := by
    rw [← Matrix.toLinearMap₂'_apply']
    exact G.lapMatrix_toLinearMap₂' ℝ x
  have hterm : ∀ i j : V, (if G.Adj i j then (x i + x j) ^ 2 else 0)
      + (if G.Adj i j then (x i - x j) ^ 2 else 0)
      = (if G.Adj i j then (2 * x i ^ 2) else 0)
        + (if G.Adj i j then (2 * x j ^ 2) else 0) := by
    intro i j
    by_cases h : G.Adj i j
    · simp only [if_pos h]; ring
    · simp [h]
  have hsum : (∑ i : V, ∑ j : V, if G.Adj i j then (x i + x j) ^ 2 else 0)
      + (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0)
      = (∑ i : V, ∑ j : V, if G.Adj i j then (2 * x i ^ 2) else 0)
        + (∑ i : V, ∑ j : V, if G.Adj i j then (2 * x j ^ 2) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hterm i j
  have e1 : (∑ i : V, ∑ j : V, if G.Adj i j then (2 * x i ^ 2) else 0)
      = 2 * ∑ i : V, ∑ j : V, if G.Adj i j then x i ^ 2 else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by by_cases h : G.Adj i j <;> simp [h]
  have e2 : (∑ i : V, ∑ j : V, if G.Adj i j then (2 * x j ^ 2) else 0)
      = 2 * ∑ i : V, ∑ j : V, if G.Adj i j then x j ^ 2 else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by by_cases h : G.Adj i j <;> simp [h]
  have hD : (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0)
      = 2 * (x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x) := by rw [hq]; ring
  rw [e1, e2, sum_adj_sq_left G x, sum_adj_sq_right G x, hD] at hsum
  linarith

/-- **THE SLACK IN `LaplacianDegreeBound`'s BOUND, EXACTLY.** On a `Δ`-regular graph the difference
between `2Δ‖x‖²` and the Laplacian quadratic form is a sum of squares over the edges, one square
`(xᵢ + xⱼ)²` per ordered adjacent pair. Nothing else is discarded, which is why the bound is sharp
where it is sharp. The regularity is used **only** to collapse the degree-weighted sum above, which
is why `LaplacianSignless` can drop it. -/
theorem sum_adj_add_sq {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (x : V → ℝ) :
    (∑ i : V, ∑ j : V, if G.Adj i j then (x i + x j) ^ 2 else 0)
      = 4 * (Δ : ℝ) * (x ⬝ᵥ x) - 2 * (x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x) := by
  have hdeg : (∑ i : V, (G.degree i : ℝ) * x i ^ 2) = (Δ : ℝ) * (x ⬝ᵥ x) := by
    rw [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hreg i]; ring
  rw [sum_adj_add_sq_of_degree G x, hdeg]
  ring

/-- The identity **re-proves** `LaplacianDegreeBound.lapMatrix_quadForm_le` at `deg ≡ Δ`, which is
the check that its constants are the ones claimed — the header says the bound falls out of the
identity, so the header is made to say it in Lean (`ERRATUM 201`). -/
example {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (x : V → ℝ) :
    x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x ≤ 2 * (Δ : ℝ) * (x ⬝ᵥ x) := by
  have hid := sum_adj_add_sq G hreg x
  have hnn : 0 ≤ ∑ i : V, ∑ j : V, if G.Adj i j then (x i + x j) ^ 2 else 0 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      by_cases h : G.Adj i j <;> simp [h, sq_nonneg]
  linarith

/-! ## 2. The equality case, over any regular graph and with no further hypothesis -/

/-- **EQUALITY IN THE DEGREE BOUND HOLDS EXACTLY WHEN `x` FLIPS SIGN ACROSS EVERY EDGE.**
The analogue at the top of the spectrum of Mathlib's
`lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj`, which is the case `Δ = 0` of the shape and
the bottom of the spectrum in content. -/
theorem quadForm_eq_iff_neg_adj {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (x : V → ℝ) :
    x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x = 2 * (Δ : ℝ) * (x ⬝ᵥ x)
      ↔ ∀ u v : V, G.Adj u v → x v = - x u := by
  have hid := sum_adj_add_sq G hreg x
  constructor
  · intro heq u v huv
    have hzero : (∑ i : V, ∑ j : V, if G.Adj i j then (x i + x j) ^ 2 else 0) = 0 := by
      rw [hid, heq]; ring
    have hnn : ∀ i ∈ (Finset.univ : Finset V),
        0 ≤ ∑ j : V, if G.Adj i j then (x i + x j) ^ 2 else 0 :=
      fun i _ => Finset.sum_nonneg fun j _ => by
        by_cases h : G.Adj i j <;> simp [h, sq_nonneg]
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero u (Finset.mem_univ u)
    have hnn2 : ∀ j ∈ (Finset.univ : Finset V),
        0 ≤ (if G.Adj u j then (x u + x j) ^ 2 else 0) :=
      fun j _ => by by_cases h : G.Adj u j <;> simp [h, sq_nonneg]
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn2).mp h1 v (Finset.mem_univ v)
    rw [if_pos huv] at h2
    have h3 : x u + x v = 0 := by
      have := sq_eq_zero_iff.mp h2
      linarith
    linarith
  · intro hflip
    have hzero : (∑ i : V, ∑ j : V, if G.Adj i j then (x i + x j) ^ 2 else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      by_cases h : G.Adj i j
      · rw [if_pos h, hflip i j h]; ring
      · rw [if_neg h]
    rw [hzero] at hid
    linarith

/-- The mass term is a multiple of the identity, so it moves through untouched. -/
theorem dotProduct_massive_mulVec (m : ℝ) (x : V → ℝ) :
    x ⬝ᵥ (massive G m) *ᵥ x = x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x + m ^ 2 * (x ⬝ᵥ x) := by
  have hd : x ⬝ᵥ (Matrix.diagonal (fun _ : V => m ^ 2)) *ᵥ x = m ^ 2 * (x ⬝ᵥ x) := by
    rw [dotProduct, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Matrix.mulVec_diagonal]; ring
  rw [massive, Matrix.add_mulVec, dotProduct_add, hd]

/-- **THE SAME EQUIVALENCE ON THE OPERATOR THIS PROJECT USES**, with the constant
`2Δ + m²` that `LaplacianDegreeBound` and `RegularBipartiteSharp` are about. -/
theorem massive_quadForm_eq_iff_neg_adj {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (m : ℝ)
    (x : V → ℝ) :
    x ⬝ᵥ (massive G m) *ᵥ x = (2 * (Δ : ℝ) + m ^ 2) * (x ⬝ᵥ x)
      ↔ ∀ u v : V, G.Adj u v → x v = - x u := by
  rw [dotProduct_massive_mulVec, ← quadForm_eq_iff_neg_adj G hreg x]
  constructor <;> intro h <;> linarith

/-! ## 3. Connectivity turns a sign flip into a colouring -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A sign-flipping vector cannot vanish at the far end of a walk if it does not vanish at the
near end. -/
theorem ne_zero_of_walk {x : V → ℝ} (hflip : ∀ u v : V, G.Adj u v → x v = - x u)
    {a b : V} (w : G.Walk a b) : x a ≠ 0 → x b ≠ 0 := by
  induction w with
  | nil => exact fun h => h
  | cons hadj _ ih =>
      intro ha
      exact ih (by rw [hflip _ _ hadj]; exact neg_ne_zero.mpr ha)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **SO ON A CONNECTED GRAPH IT VANISHES NOWHERE OR EVERYWHERE.** -/
theorem ne_zero_of_connected {x : V → ℝ} (hG : G.Connected)
    (hflip : ∀ u v : V, G.Adj u v → x v = - x u) (hx : x ≠ 0) (v : V) : x v ≠ 0 := by
  obtain ⟨u, hu⟩ : ∃ u, x u ≠ 0 := by
    by_contra hc
    exact hx (funext fun w => not_not.mp fun h => hc ⟨w, h⟩)
  obtain ⟨w⟩ := hG.preconnected u v
  exact ne_zero_of_walk G hflip w hu

/-- **THE CONVERSE OF `RegularBipartiteSharp`.** If a connected regular graph attains the degree
bound at any non-zero vector, it is two-colourable — the colours being the signs of that vector. -/
theorem colorable_two_of_quadForm_eq {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hG : G.Connected) {x : V → ℝ} (hx : x ≠ 0)
    (heq : x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x = 2 * (Δ : ℝ) * (x ⬝ᵥ x)) : G.Colorable 2 := by
  classical
  have hflip := (quadForm_eq_iff_neg_adj G hreg x).mp heq
  have hne := ne_zero_of_connected G hG hflip hx
  refine ⟨SimpleGraph.Coloring.mk (fun v => if 0 < x v then (0 : Fin 2) else 1) ?_⟩
  intro u v huv
  have hvu : x v = - x u := hflip u v huv
  rcases lt_trichotomy (x u) 0 with h | h | h
  · have hu : ¬ (0 < x u) := not_lt.mpr h.le
    have hv : 0 < x v := by rw [hvu]; exact neg_pos.mpr h
    simp only [if_neg hu, if_pos hv]
    decide
  · exact absurd h (hne u)
  · have hv : ¬ (0 < x v) := by
      rw [hvu]
      exact not_lt.mpr (neg_nonpos.mpr h.le)
    simp only [if_pos h, if_neg hv]
    decide

/-! ## 4. The characterisation, and what it says on this project's own lattice -/

/-- The forward half in the same language: `RegularBipartiteSharp`'s sign colouring IS a vector
attaining the bound. -/
theorem exists_quadForm_eq_of_colorable [Nonempty V] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (h : G.Colorable 2) :
    ∃ x : V → ℝ, x ≠ 0 ∧ x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x = 2 * (Δ : ℝ) * (x ⬝ᵥ x) := by
  obtain ⟨σ, hσ⟩ := RegularBipartiteSharp.exists_signColouring_of_colorable h
  refine ⟨σ, ?_, (quadForm_eq_iff_neg_adj G hreg σ).mpr fun u v huv => ?_⟩
  · intro hzero
    obtain ⟨v⟩ := ‹Nonempty V›
    have hv : σ v = 0 := by rw [hzero]; rfl
    rcases hσ.1 v with h1 | h1 <;> rw [hv] at h1 <;> norm_num at h1
  · have := hσ.2 u v huv
    linarith

/-- **WHICH CONNECTED REGULAR GRAPHS ATTAIN `LaplacianDegreeBound`'s CONSTANT: EXACTLY THE
TWO-COLOURABLE ONES.** The item left open by `LaplacianBoundSharp` and `CycleSpectralBound`,
answered in both directions. -/
theorem exists_quadForm_eq_iff_colorable [Nonempty V] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hG : G.Connected) :
    (∃ x : V → ℝ, x ≠ 0 ∧ x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x = 2 * (Δ : ℝ) * (x ⬝ᵥ x))
      ↔ G.Colorable 2 :=
  ⟨fun ⟨_, hx, heq⟩ => colorable_two_of_quadForm_eq G hreg hG hx heq,
    exists_quadForm_eq_of_colorable G hreg⟩

/-- **ON THE PERIODIC LATTICE, IN EVERY DIMENSION**: attaining `4d` is equivalent to
two-colourability. At even side length `TorusBipartite.torusGraph_colorable_two` supplies the right
side, which is `TorusRegular`'s theorem again; **at odd side length it turns a spectral question
into a colouring question**, and §5 answers that one. -/
theorem torus_exists_quadForm_eq_iff_colorable {d n : ℕ} (hn : 3 ≤ n) :
    (∃ x : Site d n → ℝ, x ≠ 0 ∧
        x ⬝ᵥ ((torusGraph d n).lapMatrix ℝ) *ᵥ x = 2 * ((2 * d : ℕ) : ℝ) * (x ⬝ᵥ x))
      ↔ (torusGraph d n).Colorable 2 :=
  haveI : Nonempty (Site d n) := TorusRegular.nonempty_site (by omega)
  exists_quadForm_eq_iff_colorable _ (RegularSelfEmbedding.torusGraph_isRegularOfDegree hn)
    (TorusDecay.torusGraph_connected d (by omega))

/-- **AND THE ODD CYCLE'S FAILURE COMES OUT WITHOUT AN EIGENVALUE LIST.** `CycleSpectralBound`
got it from the explicit spectrum; here it is Mathlib's chromatic number and the converse above.
**The two statements are not the same**: that one exhibits `c < 4 + m²` with `massive ≼ c·1`, a
strict gap in the Loewner order, and this one says only that no vector attains the constant. -/
theorem odd_cycle_no_attaining_vector (M : ℕ) :
    ¬ ∃ x : Fin (2 * M + 3) → ℝ, x ≠ 0 ∧
      x ⬝ᵥ ((cycleGraph (2 * M + 3)).lapMatrix ℝ) *ᵥ x = 2 * ((2 : ℕ) : ℝ) * (x ⬝ᵥ x) := by
  have hreg : (cycleGraph (2 * M + 3)).IsRegularOfDegree 2 := by
    intro v
    exact cycleGraph_degree_three_le (n := 2 * M) (v := v)
  have hconn : (cycleGraph (2 * M + 3)).Connected := by
    have := SimpleGraph.cycleGraph_connected (n := 2 * M + 2)
    simpa using this
  intro hex
  have hcol : (cycleGraph (2 * M + 3)).Colorable 2 :=
    (exists_quadForm_eq_iff_colorable _ hreg hconn).mp hex
  have hchi : (cycleGraph (2 * M + 3)).chromaticNumber = 3 :=
    chromaticNumber_cycleGraph_of_odd (2 * M + 3) (by omega) ⟨M + 1, by ring⟩
  have := hcol.chromaticNumber_le
  rw [hchi] at this
  norm_num at this

/-! ## 5. The odd side length, in every dimension — the fence `CycleSpectralBound` left -/

/-- **ONE AXIS OF THE PERIODIC LATTICE IS A CYCLE INSIDE IT**, as a graph homomorphism: put the
cycle coordinate on the first axis and zero on the rest. -/
def axisHom (d n : ℕ) : cycleGraph (n + 1) →g torusGraph (d + 1) (n + 1) where
  toFun a := fun j => if j = 0 then a else 0
  map_rel' := by
    intro a b hab
    simp only [torusGraph_adj, torusAdj]
    refine ⟨0, fun j hj => ?_, ?_⟩
    · simp [hj]
    · simpa using (TorusCycleGraph.adjT_iff_cycleGraph a b).mpr hab

/-- **SO AT ODD SIDE LENGTH THE PERIODIC LATTICE IS NOT TWO-COLOURABLE, IN EVERY DIMENSION.**
`TorusBipartite` supplies the colouring at even side length; this is the other side of it, and it
is a pullback along `axisHom` rather than a new count. -/
theorem torus_not_colorable_two_of_odd {d n : ℕ} (hodd : Odd (n + 1)) (h3 : 3 ≤ n + 1) :
    ¬ (torusGraph (d + 1) (n + 1)).Colorable 2 := by
  intro hc
  have hcyc : (cycleGraph (n + 1)).Colorable 2 := Colorable.of_hom (axisHom d n) hc
  have hchi : (cycleGraph (n + 1)).chromaticNumber = 3 :=
    chromaticNumber_cycleGraph_of_odd (n + 1) (by omega) hodd
  have hle := hcyc.chromaticNumber_le
  rw [hchi] at hle
  norm_num at hle

/-- **AND THEREFORE NO VECTOR ATTAINS THE DEGREE BOUND ON AN ODD PERIODIC LATTICE, IN EVERY
DIMENSION.** `CycleSpectralBound` settled `d = 1` from an explicit eigenvalue list; `TorusRegular`
fenced the rest — *"nothing here says whether the bound is attained at odd side length in higher
dimensions"* — and this is that, for every dimension, with no spectrum computed. -/
theorem torus_odd_no_attaining_vector {d n : ℕ} (hodd : Odd (n + 1)) (h3 : 3 ≤ n + 1) :
    ¬ ∃ x : Site (d + 1) (n + 1) → ℝ, x ≠ 0 ∧
      x ⬝ᵥ ((torusGraph (d + 1) (n + 1)).lapMatrix ℝ) *ᵥ x
        = 2 * ((2 * (d + 1) : ℕ) : ℝ) * (x ⬝ᵥ x) :=
  fun hex => torus_not_colorable_two_of_odd hodd h3
    ((torus_exists_quadForm_eq_iff_colorable h3).mp hex)

end LaplacianSharpEquality
