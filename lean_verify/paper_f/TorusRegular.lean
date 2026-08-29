import RegularBipartiteSharp
import TorusDecay
import TorusBipartite

/-!
# The degree bound is exactly right on the periodic lattice, in every dimension

`RegularBipartiteSharp` proved that a `Δ`-regular graph carrying a `±1` labelling that flips across
every edge has `massive ≼ c·1` **iff** `2Δ + m² ≤ c`, and its header named the one step between
that and the family this project's field actually lives on:

> `TorusBipartite.torusGraph_colorable_two` proves the periodic lattice is two-colourable at even
> side length **in every dimension** … What is missing is that `torusGraph d n` is `2d`-**regular**:
> the estate has `TorusDecay.torusGraph_degree_le`, an inequality, and no equality.

**This file writes the equality**, and then the sharpness follows immediately:
**`massive_torus_le_smul_one_iff`** — at every even side length at least four and in every
dimension, `massive (torusGraph d n) m ≼ c·1` **iff** `4d + m² ≤ c` — with
**`le_inv_of_smul_one_le_green_torus`** on the propagator side, which is the side
`LaplacianDegreeBound`'s withdrawn sentence was about.

## Where the inequality was, and where the equality is

`TorusDecay.torusGraph_degree_le` maps each neighbour to one of the `2d` cyclic steps
`stepT p i b` and bounds the count by the number of steps. **Nothing in that argument needs the
steps to be neighbours, or to be distinct** — its own header says so: *"a step that lands on a
non-neighbour, or back on `p`, only makes the over-count larger."* The equality needs exactly the
two facts that argument does without:

* **`stepT_adj`** — each step really is a neighbour, which needs `2 ≤ n` (at side one a step returns
  to `p` and the graph is loopless);
* **`stepT_injective`** — the `2d` steps are pairwise distinct, which needs `3 ≤ n`: at side two,
  forward and backward along an axis land on the same site.

Both bounds are sharp in the sense that matters here — the theorem is stated at `3 ≤ n` and the
counterexamples at `n = 1, 2` are the reason.

## What is proved

* `stepT_apply_self`, `stepT_apply_of_ne` — a step changes its own coordinate and no other;
* **`stepT_adj`**, **`stepT_injective`** — the two facts above;
* **`torusGraph_degree`** and `torusGraph_isRegular` — `degree p = 2d` at every site, hence
  `IsRegularOfDegree (2*d)`;
* **`massive_torus_le_smul_one_iff`** — the sharpness, in every dimension;
* **`le_inv_of_smul_one_le_green_torus`** — and the propagator's lower bound cannot be raised.

## What this is NOT

**The box is not the torus and is not reached.** `boxGraph` has a boundary, is **not** regular, and
is not two-colourable-and-regular; only `RegularBipartiteSharp`'s averaged statement would apply to
it, and that is not instantiated here.

**Even side length is a hypothesis, not a convenience.** It is where the two-colouring comes from
(`TorusBipartite.torusGraph_colorable_two` assumes it), and at odd side length the periodic lattice
is not two-colourable — `CycleSpectralBound` proves the `d = 1` case of exactly that failure, and
**nothing here says whether the bound is attained at odd side length in higher dimensions.**

**It is a statement about a matrix, not about a field.** No measure appears; `gaussianField` is not
mentioned; `OS4` does not move and no published tag moves.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusRegular

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection TorusDecay
open scoped MatrixOrder

variable {d n : ℕ}

/-! ## 1. A cyclic step moves the site it is applied to -/

theorem stepT_apply_self (hn : 2 ≤ n) (p : Site d n) (i : Fin d) (b : Bool) :
    (stepT p i b) i ≠ p i := by
  have hlt := (p i).isLt
  rw [stepT, Function.update_self]
  cases b <;> simp only [Bool.false_eq_true, if_true, if_false, Ne, Fin.ext_iff] <;>
    split <;> omega

theorem stepT_apply_of_ne (p : Site d n) {i j : Fin d} (hj : j ≠ i) (b : Bool) :
    (stepT p i b) j = p j := by
  rw [stepT, Function.update_of_ne hj]

/-! ## 2. The step is a neighbour, and the `2d` steps are distinct -/

theorem stepT_adj (hn : 2 ≤ n) (p : Site d n) (i : Fin d) (b : Bool) :
    (torusGraph d n).Adj p (stepT p i b) := by
  have hlt := (p i).isLt
  refine ⟨i, fun j hj => (stepT_apply_of_ne p hj b).symm, ?_⟩
  refine ⟨fun h => stepT_apply_self hn p i b h.symm, ?_⟩
  rw [stepT, Function.update_self]
  cases b
  · by_cases h0 : (p i).val = 0
    · exact Or.inr (Or.inr (Or.inl ⟨h0, by simp [h0]; omega⟩))
    · exact Or.inr (Or.inl (by simp [h0]; omega))
  · by_cases h0 : (p i).val + 1 = n
    · exact Or.inr (Or.inr (Or.inr ⟨by simp [h0], h0⟩))
    · exact Or.inl (by simp [h0])

theorem stepT_ne_of_bool (hn : 3 ≤ n) (p : Site d n) (i : Fin d) :
    stepT p i true ≠ stepT p i false := by
  have hlt := (p i).isLt
  intro h
  have := congrFun h i
  rw [stepT, stepT, Function.update_self, Function.update_self, Fin.ext_iff] at this
  simp only [Bool.false_eq_true, if_true, if_false] at this
  split at this <;> split at this <;> omega

theorem stepT_injective (hn : 3 ≤ n) (p : Site d n) :
    Function.Injective (fun t : Fin d × Bool => stepT p t.1 t.2) := by
  rintro ⟨i, b⟩ ⟨i', b'⟩ h
  simp only at h
  have hii : i = i' := by
    by_contra hii
    have h1 := congrFun h i
    rw [stepT_apply_of_ne p hii b'] at h1
    exact stepT_apply_self (by omega) p i b h1
  subst hii
  cases b <;> cases b'
  · rfl
  · exact absurd h.symm (stepT_ne_of_bool hn p i)
  · exact absurd h (stepT_ne_of_bool hn p i)
  · rfl

/-! ## 3. So the periodic lattice is `2d`-regular -/

/-- **THE PERIODIC LATTICE IS `2d`-REGULAR AT EVERY SIDE LENGTH AT LEAST THREE.** -/
theorem torusGraph_degree (hn : 3 ≤ n) (p : Site d n) :
    (torusGraph d n).degree p = 2 * d := by
  classical
  have hset : (torusGraph d n).neighborFinset p
      = Finset.image (fun t : Fin d × Bool => stepT p t.1 t.2) Finset.univ := by
    ext q
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro h
      obtain ⟨t, ht⟩ := adjT_eq_stepT h
      exact ⟨t, ht.symm⟩
    · rintro ⟨t, rfl⟩
      exact stepT_adj (by omega) p t.1 t.2
  rw [SimpleGraph.degree, hset, Finset.card_image_of_injective _ (stepT_injective hn p),
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

theorem torusGraph_isRegular (hn : 3 ≤ n) :
    (torusGraph d n).IsRegularOfDegree (2 * d) := fun p => torusGraph_degree hn p

/-! ## 4. Hence the degree bound is exactly right there -/

instance nonempty_site (hn : 1 ≤ n) : Nonempty (Site d n) := ⟨fun _ => ⟨0, by omega⟩⟩

/-- **THE CONSTANT `2Δ + m²` IS EXACTLY RIGHT ON THE PERIODIC LATTICE, IN EVERY DIMENSION.** -/
theorem massive_torus_le_smul_one_iff (hn : 3 ≤ n) (hev : Even n) (m c : ℝ) :
    massive (torusGraph d n) m ≤ c • (1 : Matrix (Site d n) (Site d n) ℝ)
      ↔ 4 * (d : ℝ) + m ^ 2 ≤ c := by
  classical
  obtain ⟨σ, hσ⟩ := RegularBipartiteSharp.exists_signColouring_of_colorable
    (TorusBipartite.torusGraph_colorable_two (d := d) hev)
  haveI : Nonempty (Site d n) := nonempty_site (by omega)
  have h := RegularBipartiteSharp.massive_le_smul_one_iff_of_regular (torusGraph d n)
    (torusGraph_isRegular hn) hσ m c
  rw [h]
  push_cast
  constructor <;> intro hc <;> linarith

/-- **AND THE PROPAGATOR'S LOWER BOUND CANNOT BE RAISED THERE**, which is the side of the
statement `LaplacianDegreeBound` is about. -/
theorem le_inv_of_smul_one_le_green_torus (hn : 3 ≤ n) (hev : Even n) {m : ℝ} (hm : m ≠ 0)
    {c : ℝ} (hc : 0 < c)
    (h : c • (1 : Matrix (Site d n) (Site d n) ℝ) ≤ green (torusGraph d n) m) :
    c ≤ (4 * (d : ℝ) + m ^ 2)⁻¹ := by
  have hpos : (0 : ℝ) < 4 * (d : ℝ) + m ^ 2 := by positivity
  have hcPD : (c • (1 : Matrix (Site d n) (Site d n) ℝ)).PosDef :=
    (Matrix.PosDef.one).smul hc
  have hinv := MatrixLoewner.posDef_inv_le_inv hcPD h
  have hg : (green (torusGraph d n) m)⁻¹ = massive (torusGraph d n) m := by
    rw [green, Matrix.nonsing_inv_nonsing_inv]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (massive_isUnit _ hm)
  have hd : (c • (1 : Matrix (Site d n) (Site d n) ℝ))⁻¹
      = c⁻¹ • (1 : Matrix (Site d n) (Site d n) ℝ) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ (ne_of_gt hc), one_smul]
  rw [hg, hd] at hinv
  have hkey := (massive_torus_le_smul_one_iff hn hev m c⁻¹).mp hinv
  have h2 : c * (4 * (d : ℝ) + m ^ 2) ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hkey (le_of_lt hc)
    rwa [mul_inv_cancel₀ (ne_of_gt hc)] at hmul
  calc c = (c * (4 * (d : ℝ) + m ^ 2)) * (4 * (d : ℝ) + m ^ 2)⁻¹ := by
        field_simp
    _ ≤ 1 * (4 * (d : ℝ) + m ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right h2 (le_of_lt (inv_pos.mpr hpos))
    _ = (4 * (d : ℝ) + m ^ 2)⁻¹ := one_mul _

end TorusRegular
