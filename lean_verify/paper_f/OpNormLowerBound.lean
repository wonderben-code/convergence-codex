import OpNormLoewnerConverse

/-!
# The other side of the operator norm, and the propagator gets two-sided bounds

`OpNormLoewnerConverse` turns `‖A‖ ≤ r` into a two-sided Loewner bound. **The same Cauchy–Schwarz
lemma runs the other way**: a Loewner bound from BELOW forces the operator norm up.
`PROOF_STRATEGY` §7 rule 3 — *deepen* — and its own clause that this is *"honest progress even when
no tag moves"*, which is the case here and is stated rather than implied.

> **`le_opNorm_of_smul_one_le`** — if `c • 1 ≼ A` then `c ≤ ‖A‖`. Evaluate
> `OpNormLoewnerConverse.abs_dotProduct_mulVec_le` at a standard basis vector, where the squared
> length is `1`: `c ≤ x ⬝ᵥ A *ᵥ x ≤ ‖A‖`. **No positivity and no symmetry hypothesis** — a lower
> Loewner bound already forces the quadratic form up, and the norm dominates it.

**WHAT IT GIVES AT THE PROPAGATOR.** `LaplacianOpNorm.norm_green_le` proved `‖green G m‖ ≤ (m²)⁻¹`
with no degree hypothesis at all. `LaplacianDegreeBound.smul_one_le_green` is the matching Loewner
lower bound from a degree bound, so **`norm_green_bounds`** sandwiches the propagator's operator
norm:

    (2Δ + m²)⁻¹  ≤  ‖green G m‖  ≤  (m²)⁻¹.

Both ends name a degree bound and a mass and **not the vertex count**, so on `boxGraph d n` the
sandwich is `(4d + m²)⁻¹ ≤ ‖green‖ ≤ m⁻²` **at every side length** — which is the property the whole
operator-norm chain of 2026-09-02 was built for, now on both sides of the object rather than one.

**WHAT THIS IS NOT.**
* **Nothing consumes it**, and that is written here rather than left to be discovered. The chain's
  consumers use the upper bound; **the lower bound has none**, and no wall or watchlist item asks
  for one. It is rule 3's kind of progress and not rule 1's or rule 2's.
* **It is not sharp at either end.** The upper bound is `green ≼ (m²)⁻¹ • 1` read as a norm, tight
  only when `green` has an eigenvalue at `(m²)⁻¹`, which needs an isolated vertex; the lower is a
  degree bound and loses whatever the degrees vary by. **No loss is quantified.**
  **⚠ EVERY CLAIM IN THAT BULLET IS WRONG AND IT IS KEPT AS WRITTEN** (`ERRATUM 94`,
  **`ERRATUM 434`**, 2026-09-03). `GreenExpansion.green_mulVec_one` — 2026-08-12, in a file this
  chain cites — gives `green G m *ᵥ 1 = (m²)⁻¹ • 1` on **every** finite graph, because the graph
  Laplacian kills constants with no hypotheses at all. So `(m²)⁻¹` is an eigenvalue of `green`
  always: **no isolated vertex is needed and none is relevant.** Hence
  `GreenNormExact.norm_green_eq` : **`‖green G m‖ = (m²)⁻¹`** on every finite nonempty graph at
  every `m ≠ 0`. The upper bound is **exactly attained**, so it is sharp rather than not; and
  `norm_green_ge` below is **strictly** below the truth at every graph with an edge
  (`GreenNormExact.norm_green_ge_lt_of_pos`), so the loss is now quantified — it is the whole of
  `(m²)⁻¹ − (2Δ + m²)⁻¹`. **Both theorems below stand**: they are Loewner bounds read as norms, and
  `LaplacianDegreeBound.smul_one_le_green` bounds every eigenvalue from below, which the equality
  does not.
* **No wall moves.** W1's ask is a lower bound on the cross form, a different object entirely, and
  nothing here is about a reflection.

**⚠ THE REASON THAT SENTENCE GIVES IS FALSE AND IT IS KEPT AS WRITTEN** (`ERRATUM 94`,
**`ERRATUM 441`**, 2026-09-03). *"No wall moves"* stands; what `W1` asks for does not.
`ReflectionPositive → hcross` has been a **theorem** since 2026-08-13 —
`ReflectionConverse.reflectionPositive_iff_hcross`, on every finite graph at every mass with no
fixed point — and with a fixed layer the converse is **refuted**
(`MirrorConverseFails.converse_fails_with_mirror`). `W1`'s open part is `OS0`/`OS1`/`OS4`, which is
what `W1`'s own row in `WALLS.md` says.

**`[Nonempty V]` IS REQUIRED AND IS NOT DECORATION**: on an empty vertex type both matrices are `0`,
`c • 1 ≼ 0` holds for every `c` including positive ones, and `‖0‖ = 0`. The upper-bound direction of
`OpNormLoewnerConverse` needs no such hypothesis; this one does, for the mirror-image reason.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace OpNormLowerBound

open Matrix GraphLaplacian
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. A Loewner bound from below forces the norm up -/

/-- **`c • 1 ≼ A` GIVES `c ≤ ‖A‖`.** One standard basis vector has squared length `1`, so
`OpNormLoewnerConverse.abs_dotProduct_mulVec_le` reads there as `x ⬝ᵥ A *ᵥ x ≤ ‖A‖`, and the
hypothesis puts `c` below the left side. **No positivity, no symmetry.** -/
theorem le_opNorm_of_smul_one_le [Nonempty V] {A : Matrix V V ℝ} {c : ℝ}
    (hc : c • (1 : Matrix V V ℝ) ≤ A) : c ≤ ‖A‖ := by
  classical
  set e : V → ℝ := Pi.single (Classical.arbitrary V) 1 with he
  have hee : e ⬝ᵥ e = 1 := by simp [he]
  have hlow : c * (e ⬝ᵥ e) ≤ e ⬝ᵥ A *ᵥ e := by
    have h := PosSemidefNormBound.dotProduct_mono hc e
    simpa [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] using h
  have hup := abs_le.mp (OpNormLoewnerConverse.abs_dotProduct_mulVec_le A e)
  rw [hee, mul_one] at hlow
  rw [hee, mul_one] at hup
  linarith [hup.2, hlow]

/-! ## 2. The propagator, from both sides -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **`(2Δ + m²)⁻¹ ≤ ‖green G m‖`**, from `LaplacianDegreeBound.smul_one_le_green`. -/
theorem norm_green_ge [Nonempty V] {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) {m : ℝ}
    (hm : m ≠ 0) (hpos : 0 < 2 * Δ + m ^ 2) : (2 * Δ + m ^ 2)⁻¹ ≤ ‖green G m‖ :=
  le_opNorm_of_smul_one_le (LaplacianDegreeBound.smul_one_le_green G hΔ hm hpos)

/-- **THE SANDWICH.** `(2Δ + m²)⁻¹ ≤ ‖green G m‖ ≤ (m²)⁻¹`, both ends naming a degree bound and a
mass and **not the vertex count**. On `boxGraph d n` that is `(4d + m²)⁻¹ ≤ ‖green‖ ≤ m⁻²` at every
side length. -/
theorem norm_green_bounds [Nonempty V] {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) {m : ℝ}
    (hm : m ≠ 0) (hpos : 0 < 2 * Δ + m ^ 2) :
    (2 * Δ + m ^ 2)⁻¹ ≤ ‖green G m‖ ∧ ‖green G m‖ ≤ (m ^ 2)⁻¹ :=
  ⟨norm_green_ge G hΔ hm hpos, LaplacianOpNorm.norm_green_le G hm⟩

end OpNormLowerBound
