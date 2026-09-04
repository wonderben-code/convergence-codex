import AdjNormSqrtDegree
import Mathlib.Algebra.Order.Chebyshev

/-!
# The star's adjacency norm is exactly `√n`, and `√(deg v)` is the best degree bound there is

Three files written on 3–4 September carry the same sentence and none of them proves it:
`SymmetricOpNorm`'s bullet, `AdjNormRegular`'s "what is not here" and `AdjNormSqrtDegree`'s — each
saying that `‖A‖ ≤ Δ` is loose off the regular class, witnessed by the star `K_{1,n}` whose
adjacency eigenvalues are `±√n`, and each saying in its own words that **the example is stated and
not formalised**. (A first draft of this header called it the estate's *oldest* looseness witness.
It is not: `git log -S` dates it to 2026-09-03, and `BoxMassiveBound`, `FlipEnergy` and
`GreenNormExact` all fence their own constants as unsharp earlier. The superlative was removed
before the commit, by checking it.)

**It is formalised here.** For the star with centre `c` on any finite vertex type,

```
‖(starGraph c).adjMatrix ℝ‖ = Real.sqrt (Fintype.card V - 1)
```

against a maximum degree of `Fintype.card V - 1`. The gap between `√n` and `n` is the whole distance
between the star and the regular class, and it is now a computed quantity rather than a remark.

## What it settles that yesterday's file explicitly refused to claim

`AdjNormSqrtDegree` proves `√(deg v) ≤ ‖A‖` at every vertex of every graph and then says, at length,
that **whether the constant is ATTAINED is classical and is proved nowhere in this estate** — the
first draft of that file claimed sharpness and the claim was retracted before the commit, because it
rested on exactly the star value nobody had proved. **That retraction is discharged rather than
softened, and by more than an instance.** §5 proves that **no function of the degree alone beats the
square root**: if `f : ℕ → ℝ` satisfies `f (G.degree v) ≤ ‖G.adjMatrix ℝ‖` at every vertex of every
finite graph, then `f n ≤ √n` for every `n`. The star is what forces it. So `AdjNormSqrtDegree`'s
constant is not merely attained somewhere — it is **optimal among all bounds of its form**, which is
the sentence the retracted draft wanted and could not have.

## The route, which is not the one that was predicted

`AdjNormSqrtDegree` named a route — compute `A²`, read `‖A²‖ = n` off the all-ones block, and close
with `‖A * A‖ = ‖A‖ ‖A‖` — and probed `Matrix.l2_opNorm_conjTranspose_mul_self` to confirm the
instrument exists at this pin. **The instrument was not needed.** The star's quadratic form is
`2·x c·∑_{v ≠ c} x v`, Cauchy–Schwarz bounds the sum by `√n` times the leaves' length, and
`2ab ≤ a² + b²` finishes it — so `−√n • 1 ≼ A ≼ √n • 1` directly, and `SymmetricOpNorm`'s existing
`l2_opNorm_le_of_abs_le` converts that to the norm bound with no matrix product formed at all.
**A named route is not a necessary one**, which is `ERRATUM 439`'s rule met from the other side: the
prediction was a route, was labelled a route, and a shorter one existed.

## What is NOT here

**Not a claim that `K_{1,n}` is new to mathematics.** The eigenvalues of a star are textbook. What
was missing was a formal object and a proof in this estate, and that is what is added.

**Not the Perron–Frobenius converse.** `‖A‖ = Δ ⟹ regular` for connected graphs stays open exactly
where `AdjNormRegular` left it. A star is a graph where the degree bound is loose; that is a
witness, not a proof that looseness is equivalent to irregularity.

**Not a bound on any other irregular family.** `SymmetricOpNorm`'s bullet says the graphs attaining
`‖A‖ = Δ` are not identified, and this file identifies none of them either — it identifies one graph
where the bound is not attained, and computes by how much.

**Not optimality among bounds of a different form.** §5 rules out better functions **of the degree
alone**. A bound reading the degree *and* something else — the vertex count, the second-largest
degree, connectivity — is untouched by it, and `AdjNormRegular` is exactly such a bound: on a
regular graph `‖A‖ = Δ`, far above `√Δ`. **The optimality is relative to a stated form**, and the
statement says so.

> ⚠ **2026-09-04, LATER: THIS PARAGRAPH IS NOW A THEOREM AND NOT A CAVEAT** (`ERRATUM 94`; kept as
> written, because it was right). `AdjNormAverageDegree` proves the average degree is also a floor,
> `(∑ deg)/card V ≤ ‖A‖`, and that **neither floor contains the other**: on a `Δ`-regular graph with
> `Δ ≥ 2` the average floor is strictly better (`sqrt_lt_avg_of_regular`, and `AdjNormRegular` makes
> it exact there), while on the star at `n ≥ 4` the root floor is strictly better
> (`avg_lt_sqrt_star`, since the star's average is `2n/(n+1) < 2`).
> `neither_floor_contains_the_other` exhibits both witnesses — the triangle and the star on five
> vertices. **The boundary of §5's quantifier is now visible rather than reconstructed.**

**No wall moves.** `W1`'s open part is `OS0`/`OS1`/`OS4` (`ERRATUM 441`).

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace StarAdjNormExact

open Matrix Finset SimpleGraph
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The star -/

/-- The star with centre `c`: every other vertex is joined to `c` and to nothing else. -/
def starGraph (c : V) : SimpleGraph V where
  Adj u v := (u = c ∧ v ≠ c) ∨ (v = c ∧ u ≠ c)
  symm := by
    intro u v h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
  loopless := ⟨fun _ h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact h2 h1⟩

instance decidableStarAdj (c : V) : DecidableRel (starGraph c).Adj := fun u v =>
  inferInstanceAs (Decidable ((u = c ∧ v ≠ c) ∨ (v = c ∧ u ≠ c)))

omit [Fintype V] [DecidableEq V] in
theorem starGraph_adj_centre {c v : V} : (starGraph c).Adj c v ↔ v ≠ c := by
  constructor
  · rintro (⟨_, h2⟩ | ⟨_, h2⟩)
    · exact h2
    · exact absurd rfl h2
  · exact fun h => Or.inl ⟨rfl, h⟩

omit [Fintype V] [DecidableEq V] in
theorem starGraph_adj_leaf {c u v : V} (hu : u ≠ c) : (starGraph c).Adj u v ↔ v = c := by
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, _⟩)
    · exact absurd h1 hu
    · exact h1
  · exact fun h => Or.inr ⟨h, hu⟩

/-- The centre's neighbours are everything else. -/
theorem neighborFinset_centre (c : V) :
    (starGraph c).neighborFinset c = Finset.univ.erase c := by
  ext v
  simp [SimpleGraph.mem_neighborFinset, starGraph_adj_centre, Finset.mem_erase]

/-- A leaf's only neighbour is the centre. -/
theorem neighborFinset_leaf {c v : V} (hv : v ≠ c) :
    (starGraph c).neighborFinset v = {c} := by
  ext w
  simp [SimpleGraph.mem_neighborFinset, starGraph_adj_leaf hv]

/-- **`deg c = card V - 1`.** -/
theorem degree_centre (c : V) : (starGraph c).degree c = Fintype.card V - 1 := by
  rw [SimpleGraph.degree, neighborFinset_centre, Finset.card_erase_of_mem (Finset.mem_univ c),
    Finset.card_univ]

/-- **The leaf count, in `ℝ`, with no truncated subtraction.** Every square root below is taken of
`(card V : ℝ) - 1`, and this is the one place the natural-number count is converted. -/
theorem cast_card_erase (c : V) :
    (((Finset.univ.erase c).card : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by
  have hpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨c⟩
  rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Nat.cast_sub hpos,
    Nat.cast_one]

/-- The centre's degree in `ℝ`, which is the form the norm statements need. -/
theorem cast_degree_centre (c : V) :
    (((starGraph c).degree c : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by
  rw [SimpleGraph.degree, neighborFinset_centre, cast_card_erase c]

/-- **`deg v = 1` at every leaf**, which is what makes the star irregular as soon as it has more
than two vertices. -/
theorem degree_leaf {c v : V} (hv : v ≠ c) : (starGraph c).degree v = 1 := by
  rw [SimpleGraph.degree, neighborFinset_leaf hv, Finset.card_singleton]

/-! ## 2. The quadratic form -/

/-- **`xᵀAx = 2·x c·∑_{v ≠ c} x v`.** The centre's row is the whole leaf sum and every leaf's row
is the single entry at the centre, so the two halves are equal and the form has one term. -/
theorem quadForm_star (c : V) (x : V → ℝ) :
    x ⬝ᵥ ((starGraph c).adjMatrix ℝ) *ᵥ x
      = 2 * x c * ∑ v ∈ Finset.univ.erase c, x v := by
  classical
  have hrow : ∀ u : V, ((starGraph c).adjMatrix ℝ *ᵥ x) u
      = if u = c then ∑ v ∈ Finset.univ.erase c, x v else x c := by
    intro u
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    by_cases hu : u = c
    · subst hu
      rw [neighborFinset_centre, if_pos rfl]
    · rw [neighborFinset_leaf hu, if_neg hu, Finset.sum_singleton]
  rw [dotProduct]
  rw [Finset.sum_congr rfl (fun u _ => by rw [hrow u])]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c), if_pos rfl]
  have hrest : ∑ u ∈ Finset.univ.erase c, (x u * if u = c then
      ∑ v ∈ Finset.univ.erase c, x v else x c)
      = ∑ u ∈ Finset.univ.erase c, x u * x c := by
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [if_neg (Finset.mem_erase.mp hu).1]
  rw [hrest, ← Finset.sum_mul]
  ring

/-! ## 3. Cauchy–Schwarz, and the Loewner bracket -/

/-- **`|xᵀAx| ≤ √n · (x ⬝ᵥ x)`** with `n = card V - 1`. Cauchy–Schwarz bounds the leaf sum by
`√n` times the leaves' length, and `2ab ≤ a² + b²` splits the product between the centre and the
leaves. -/
theorem abs_quadForm_le (c : V) (x : V → ℝ) :
    |x ⬝ᵥ ((starGraph c).adjMatrix ℝ) *ᵥ x|
      ≤ Real.sqrt (Fintype.card V - 1) * (x ⬝ᵥ x) := by
  classical
  set s : Finset V := Finset.univ.erase c with hs
  set n : ℕ := s.card with hn
  have hcard : (n : ℝ) = (Fintype.card V : ℝ) - 1 := by rw [hn, hs, cast_card_erase c]
  set S : ℝ := ∑ v ∈ s, x v with hS
  set Q : ℝ := ∑ v ∈ s, x v ^ 2 with hQ
  have hQnn : 0 ≤ Q := Finset.sum_nonneg fun v _ => sq_nonneg (x v)
  -- the vector's own length splits the same way
  have hlen : x ⬝ᵥ x = x c ^ 2 + Q := by
    rw [dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ c), hQ, hs]
    have : ∀ u ∈ Finset.univ.erase c, x u * x u = x u ^ 2 := fun u _ => (sq (x u)).symm
    rw [Finset.sum_congr rfl this, sq]
  -- Cauchy--Schwarz
  have hCS : S ^ 2 ≤ (n : ℝ) * Q := by
    rw [hS, hQ, hn]
    exact_mod_cast sq_sum_le_card_mul_sum_sq (s := s) (f := x)
  have hsqrtn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hSle : |S| ≤ Real.sqrt n * Real.sqrt Q := by
    rw [← Real.sqrt_mul (by positivity)]
    calc |S| = Real.sqrt (S ^ 2) := (Real.sqrt_sq_eq_abs S).symm
      _ ≤ Real.sqrt ((n : ℝ) * Q) := Real.sqrt_le_sqrt hCS
  have hQsq : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQnn
  have hQsqnn : (0 : ℝ) ≤ Real.sqrt Q := Real.sqrt_nonneg _
  -- 2ab <= a^2 + b^2
  have hAM : 2 * |x c| * Real.sqrt Q ≤ x c ^ 2 + Q := by
    nlinarith [sq_nonneg (|x c| - Real.sqrt Q), sq_abs (x c), hQsq]
  rw [quadForm_star, hlen, ← hcard]
  calc |2 * x c * S| = 2 * |x c| * |S| := by
        rw [abs_mul, abs_mul, abs_two]
    _ ≤ 2 * |x c| * (Real.sqrt n * Real.sqrt Q) :=
        mul_le_mul_of_nonneg_left hSle (by positivity)
    _ = Real.sqrt n * (2 * |x c| * Real.sqrt Q) := by ring
    _ ≤ Real.sqrt n * (x c ^ 2 + Q) := mul_le_mul_of_nonneg_left hAM hsqrtn

/-- `A ≼ √n • 1`. -/
theorem le_smul_one (c : V) :
    (starGraph c).adjMatrix ℝ
      ≤ Real.sqrt (Fintype.card V - 1) • (1 : Matrix V V ℝ) := by
  classical
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_)
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    refine Matrix.IsSymm.sub ?_ ((starGraph c).isSymm_adjMatrix (α := ℝ))
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.isSymm_diagonal _
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg]
    have hconst : x ⬝ᵥ (Real.sqrt (Fintype.card V - 1) • (1 : Matrix V V ℝ)) *ᵥ x
        = Real.sqrt (Fintype.card V - 1) * (x ⬝ᵥ x) := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    rw [hconst]
    exact le_trans (le_abs_self _) (abs_quadForm_le c x)

/-- `−√n • 1 ≼ A`. -/
theorem neg_smul_one_le (c : V) :
    -(Real.sqrt (Fintype.card V - 1) • (1 : Matrix V V ℝ))
      ≤ (starGraph c).adjMatrix ℝ := by
  classical
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_)
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    refine Matrix.IsSymm.sub ((starGraph c).isSymm_adjMatrix (α := ℝ)) ?_
    refine Matrix.IsSymm.neg ?_
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.isSymm_diagonal _
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg, Matrix.neg_mulVec,
      dotProduct_neg]
    have hconst : x ⬝ᵥ (Real.sqrt (Fintype.card V - 1) • (1 : Matrix V V ℝ)) *ᵥ x
        = Real.sqrt (Fintype.card V - 1) * (x ⬝ᵥ x) := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    rw [hconst]
    have h := abs_quadForm_le c x
    have h2 := neg_le_of_abs_le h
    linarith

/-! ## 4. The exact norm -/

/-- **`‖(starGraph c).adjMatrix ℝ‖ ≤ √(card V − 1)`**, from the Loewner bracket. -/
theorem norm_le (c : V) :
    ‖(starGraph c).adjMatrix ℝ‖ ≤ Real.sqrt (Fintype.card V - 1) := by
  haveI : Nonempty V := ⟨c⟩
  exact SymmetricOpNorm.l2_opNorm_le_of_abs_le (neg_smul_one_le c) (le_smul_one c)

/-- **`‖(starGraph c).adjMatrix ℝ‖ = √(card V − 1)`, AND THE ESTATE'S OLDEST LOOSENESS WITNESS IS
A THEOREM.** Three files state this value and none proved it; the lower half is
`AdjNormSqrtDegree.sqrt_degree_le_norm_adjMatrix` read at the centre, whose degree is `card V − 1`,
and the upper half is §3. Against a maximum degree of `card V − 1`, the degree bound
`SymmetricOpNorm.norm_adjMatrix_le` overstates the norm by a square root. -/
theorem norm_adjMatrix_starGraph_eq (c : V) :
    ‖(starGraph c).adjMatrix ℝ‖ = Real.sqrt (Fintype.card V - 1) := by
  refine le_antisymm (norm_le c) ?_
  have h := AdjNormSqrtDegree.sqrt_degree_le_norm_adjMatrix (G := starGraph c) c
  rwa [cast_degree_centre c] at h

/-- **The gap, as a statement rather than a remark.** On a star with at least two leaves the degree
bound is strictly loose: `‖A‖ < Δ`. This is the sentence `SymmetricOpNorm`'s bullet has carried
since it was written. -/
theorem norm_lt_degree (c : V) (h3 : 3 ≤ Fintype.card V) :
    ‖(starGraph c).adjMatrix ℝ‖ < (starGraph c).degree c := by
  rw [norm_adjMatrix_starGraph_eq c, cast_degree_centre c]
  set r : ℝ := (Fintype.card V : ℝ) - 1 with hr
  have hcard : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast h3
  have hr2 : (2 : ℝ) ≤ r := by rw [hr]; linarith
  have hrnn : (0 : ℝ) ≤ r := by linarith
  have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hrnn
  nlinarith [Real.sqrt_nonneg r, hsq, hr2]

/-! ## 5. No function of the degree alone does better -/

/-- The star on `Fin (n+1)` has a centre of degree exactly `n`. -/
theorem degree_centre_fin (n : ℕ) : (starGraph (0 : Fin (n + 1))).degree 0 = n := by
  rw [degree_centre, Fintype.card_fin, Nat.add_sub_cancel]

/-- Its adjacency norm is exactly `√n`. -/
theorem norm_starGraph_fin (n : ℕ) :
    ‖(starGraph (0 : Fin (n + 1))).adjMatrix ℝ‖ = Real.sqrt n := by
  rw [norm_adjMatrix_starGraph_eq, Fintype.card_fin]
  congr 1
  push_cast
  ring

/-- **`√(deg v)` IS THE BEST DEGREE BOUND THERE IS.** If `f` is any function of the degree that
lower-bounds the adjacency norm at every vertex of every finite graph, then `f n ≤ √n` at every `n`.
The witness is the star on `n + 1` vertices, whose centre has degree `n` and whose norm is `√n`, so
`f n ≤ √n` with no room anywhere. This is what `AdjNormSqrtDegree` wanted to claim and correctly
would not: it makes that file's constant **optimal for its form**, not merely attained. -/
theorem le_sqrt_of_universal_degree_bound (f : ℕ → ℝ)
    (hf : ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (G : SimpleGraph W)
      (_ : DecidableRel G.Adj) (v : W), f (G.degree v) ≤ ‖G.adjMatrix ℝ‖)
    (n : ℕ) : f n ≤ Real.sqrt n := by
  have h := hf (Fin (n + 1)) inferInstance inferInstance (starGraph (0 : Fin (n + 1)))
    inferInstance 0
  rwa [degree_centre_fin n, norm_starGraph_fin n] at h

/-- **And `AdjNormSqrtDegree` attains it**, so the optimum is not merely an upper limit on what is
possible: it is reached. Stated as the pair, because a sharpness claim is two statements and this
estate has previously written one and implied the other. -/
theorem sqrt_is_the_optimal_degree_bound :
    (∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (G : SimpleGraph W)
      (_ : DecidableRel G.Adj) (v : W),
        Real.sqrt (G.degree v) ≤ ‖G.adjMatrix ℝ‖)
    ∧ (∀ f : ℕ → ℝ, (∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (G : SimpleGraph W)
      (_ : DecidableRel G.Adj) (v : W), f (G.degree v) ≤ ‖G.adjMatrix ℝ‖) →
        ∀ n : ℕ, f n ≤ Real.sqrt n) := by
  refine ⟨fun W _ _ G _ v => ?_, le_sqrt_of_universal_degree_bound⟩
  exact AdjNormSqrtDegree.sqrt_degree_le_norm_adjMatrix v

end StarAdjNormExact
