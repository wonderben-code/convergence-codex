import SignlessStarExact
import SignlessPrimitive

/-!
# And only the star: `topEigen = Δ + 1` on a connected graph forces it

`SignlessStarExact` proved that the star attains the bracket's lower end, and fenced itself in
terms: *`Δ + 1 = topEigen` is proved **on the star**. The classical statement is that a connected
graph attains it **only** on a star, and the converse direction — attainment forces the star — is
not proved, not attempted, and not implied by anything here. One family of witnesses is not a
classification.* **This is the classification.**

## What is proved

**`star_of_topEigen_eq`** — **THE FILE'S THEOREM.** For a connected graph on two or more vertices,

```
topEigen (signlessLap G) = Δ + 1   →   ∃ v, G = starGraph v
```

and with the previous file's theorem this is an **iff**: `topEigen_eq_iff_star`. So the lower end of
`Δ + 1 ≤ topEigen ≤ 2Δ` is attained **exactly** on the stars, and the sentence the previous unit
could not write is now a biconditional rather than a family of examples.

## Where the equality is spent, and it is not where the item predicted

The watchlist item opened for this said the obstacle was *turning equality in
`RayleighVariational.quadForm_le_topEigen` into an eigenvector*, and named
`RayleighMatrix.mv_eq_smul_of_quadForm_eq` as the thing to read first. **Both halves of that were
wrong and are recorded rather than quietly dropped** (`ERRATUM 535`). That lemma exists and says
exactly *a vector achieving equality in the variational inequality is an eigenvector for `M`* — so
the step is not missing. **And this proof does not use it.** The equality is spent one level
earlier, on the test vector itself, and never becomes a statement about eigenvectors at all.

Here is why. The previous bound is a sandwich, `A ≤ B ≤ C`, where

* `A = Δ·(1 + 1/Δ)²` is the star at `v` inside the edge sum,
* `B = x ⬝ᵥ Q x` at the test vector `x`,
* `C = topEigen · (x ⬝ᵥ x) = (Δ + 1)(1 + 1/Δ)` **once the hypothesis is used**,

and `A` and `C` are the *same number*, `(Δ+1)²/Δ`. **That is the whole of the argument**: the
hypothesis collapses the sandwich, so `B = A` exactly, so the slack in the first inequality is
zero — and the slack in the first inequality is, term for term, the edge sum away from `v`.

## What the slack is, and the general lemma that names it

**`double_sum_split`** — for a symmetric kernel with zero diagonal,

```
∑ᵢ ∑ⱼ T i j = 2·(∑ⱼ T v j) + ∑_{i ≠ v} ∑_{j ≠ v} T i j
```

**an identity, where `SignlessMaxDegreeBound.two_row_le_double_sum` is an inequality.** That file
needed only `2·row ≤ double sum` and proved exactly that; the converse needs to know **what the
difference is**, and it is the sub-sum over pairs avoiding `v` — with no factor lost, which is why
this is stated and proved rather than extracted from the inequality's proof.

With `T i j = (x i + x j)²` on edges, every term is a square, so the sub-sum vanishing means every
term vanishes: **no edge avoiding `v` carries a nonzero `x i + x j`**. The test vector is `1` at
`v`, `1/Δ` on the neighbours and `0` elsewhere — **all non-negative, which is what makes a vanishing
sum of squares informative** — so a neighbour `u` of `v` can have no neighbour but `v`:
`(1/Δ + x w)² > 0` for every `w`.

**`nbr_only_centre`** — hence a neighbour of a maximum-degree vertex has no neighbour but the
centre, which is the whole graph-theoretic content. Connectedness then gives `V = N[v]` through
`TorusEmbeddingGeneral.mem_of_walk` — **which this file drafted and deleted**: that theorem is
already in the estate under the same name and inside this file's import closure, and
`newnames_scan` said so before the commit (`ERRATUM 536`). And `starGraph v` is what is left.

## What is NOT here

* **NOTHING ABOUT THE UPPER END.** `topEigen = 2Δ` holds on every regular graph and the converse
  there — does `2Δ` force regularity? — is **a different question and is not touched**. The two
  ends are not symmetric: `Δ + 1` is attained by one graph per degree, `2Δ` by a whole class.
* **NO SECOND EIGENVALUE, NO GAP**, five units running (`ERRATUM 246`).
* **NOTHING ABOUT DISCONNECTED GRAPHS**, and connectedness is genuinely needed rather than
  convenient: a star plus an isolated vertex has the same `Δ` and the same `topEigen` and is not a
  star. The hypothesis is doing work and the counterexample says which work.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a finite vertex type with decidable
equality and adjacency, `Nontrivial V`, and `G.Connected`. No colourability, no regularity, and no
positivity beyond what the test vector supplies.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessStarConverse

open Matrix Finset SimpleGraph LaplacianSignless RayleighVariational StarAdjNormExact
open SignlessMaxDegreeBound

/-! ## 1. The double sum, split exactly -/

section Kernel
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **THE IDENTITY BEHIND `two_row_le_double_sum`'s INEQUALITY.** The difference between the double
sum and twice one row is the sub-sum over pairs avoiding that row's index. -/
theorem double_sum_split (T : V → V → ℝ) (hsymm : ∀ i j, T i j = T j i) (hdiag : ∀ i, T i i = 0)
    (v : V) :
    ∑ i, ∑ j, T i j
      = 2 * (∑ j, T v j) + ∑ i ∈ univ.erase v, ∑ j ∈ univ.erase v, T i j := by
  classical
  have houter : ∑ i, ∑ j, T i j = (∑ j, T v j) + ∑ i ∈ univ.erase v, ∑ j, T i j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ v)).symm
  have hinner : ∀ i ∈ univ.erase v,
      ∑ j, T i j = T i v + ∑ j ∈ univ.erase v, T i j :=
    fun i _ => (Finset.add_sum_erase _ _ (Finset.mem_univ v)).symm
  have hcol : ∑ i ∈ univ.erase v, T i v = ∑ j, T v j := by
    have h1 : ∑ i ∈ univ.erase v, T i v = ∑ i ∈ univ.erase v, T v i :=
      Finset.sum_congr rfl fun i _ => hsymm i v
    rw [h1, ← Finset.add_sum_erase _ (fun i => T v i) (Finset.mem_univ v), hdiag v, zero_add]
  rw [houter, Finset.sum_congr rfl hinner, Finset.sum_add_distrib, hcol]
  ring

end Kernel

/-! ## 2. The equality collapses the sandwich -/

section Pointwise
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The edge kernel of the test vector at `v`, weighted by `d`. **No finiteness**: it is a function
of two vertices and the sums over it come later. -/
noncomputable def edgeSq (v : V) (d : ℝ) (i j : V) : ℝ :=
  if G.Adj i j then (testVec G v d i + testVec G v d j) ^ 2 else 0

theorem edgeSq_nonneg (v : V) (d : ℝ) (i j : V) : 0 ≤ edgeSq G v d i j := by
  unfold edgeSq; by_cases h : G.Adj i j <;> simp [h, sq_nonneg]

theorem edgeSq_symm (v : V) (d : ℝ) (i j : V) : edgeSq G v d i j = edgeSq G v d j i := by
  unfold edgeSq
  by_cases h : G.Adj i j
  · rw [if_pos h, if_pos h.symm]; ring
  · have h' : ¬ G.Adj j i := fun hh => h hh.symm
    rw [if_neg h, if_neg h']

theorem edgeSq_diag (v : V) (d : ℝ) (i : V) : edgeSq G v d i i = 0 := by
  unfold edgeSq; simp

end Pointwise

section Converse
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem sum_edgeSq_row (v : V) {d : ℝ} (hdeg : (G.degree v : ℝ) = d) :
    ∑ j, edgeSq G v d v j = d * (1 + 1 / d) ^ 2 := by
  have hcongr : ∀ j : V, edgeSq G v d v j = if G.Adj v j then (1 + 1 / d) ^ 2 else 0 := by
    intro j
    unfold edgeSq
    by_cases h : G.Adj v j
    · rw [if_pos h, if_pos h, testVec_self, testVec_adj G d h]
    · rw [if_neg h, if_neg h]
  rw [Finset.sum_congr rfl fun j _ => hcongr j, sum_ite_adj, hdeg]

/-- **THE SLACK, ISOLATED.** `x ⬝ᵥ Q x` is the star at `v` plus half the edge sum away from `v`. -/
theorem quadForm_eq_row_add_rest (v : V) {d : ℝ} (hdeg : (G.degree v : ℝ) = d) :
    (testVec G v d) ⬝ᵥ (signlessLap G) *ᵥ (testVec G v d)
      = d * (1 + 1 / d) ^ 2
        + (∑ i ∈ univ.erase v, ∑ j ∈ univ.erase v, edgeSq G v d i j) / 2 := by
  rw [dotProduct_signlessLap]
  have : ∀ i j : V, (if G.Adj i j then (testVec G v d i + testVec G v d j) ^ 2 else 0)
      = edgeSq G v d i j := fun i j => rfl
  simp only [this]
  rw [double_sum_split (edgeSq G v d) (edgeSq_symm G v d) (edgeSq_diag G v d) v,
    sum_edgeSq_row G v hdeg]
  ring

/-- **SO EQUALITY KILLS THE SLACK.** -/
theorem rest_eq_zero [Nonempty V] (v : V) (hv : G.maxDegree = G.degree v)
    (hΔ : 0 < G.maxDegree)
    (heq : topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G)
      = (G.maxDegree : ℝ) + 1) :
    ∀ i ∈ univ.erase v, ∀ j ∈ univ.erase v, edgeSq G v (G.maxDegree : ℝ) i j = 0 := by
  set d : ℝ := (G.maxDegree : ℝ) with hddef
  have hd : (0 : ℝ) < d := by rw [hddef]; exact_mod_cast hΔ
  have hdeg : (G.degree v : ℝ) = d := by rw [hddef, hv]
  set x := testVec G v d with hx
  set R : ℝ := ∑ i ∈ univ.erase v, ∑ j ∈ univ.erase v, edgeSq G v d i j with hR
  have hRnn : 0 ≤ R :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => edgeSq_nonneg G v d i j
  have hform := quadForm_eq_row_add_rest G v hdeg
  have hnorm : x ⬝ᵥ x = 1 + 1 / d := by rw [hx, dot_testVec G v hd.ne', hdeg]; field_simp
  have hray := RayleighVariational.quadForm_le_topEigen
    (LaplacianSignlessDefinite.signlessLap_isHermitian G) x
  rw [hnorm, heq] at hray
  have hcollapse : (d + 1) * (1 + 1 / d) = d * (1 + 1 / d) ^ 2 := by field_simp
  rw [← hx] at hform
  have hRle : R ≤ 0 := by rw [hform, hcollapse] at hray; linarith
  have hR0 : R = 0 := le_antisymm hRle hRnn
  intro i hi j hj
  have hinner : ∀ i ∈ univ.erase v, ∑ j ∈ univ.erase v, edgeSq G v d i j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => edgeSq_nonneg G v d i j)).mp hR0
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => edgeSq_nonneg G v d i j)).mp (hinner i hi) j hj

/-! ## 3. So every neighbour of `v` is a leaf -/

/-- **EVERY NEIGHBOUR OF A MAXIMUM-DEGREE VERTEX HAS DEGREE ONE.** The test vector is `1/Δ > 0` at
a neighbour and non-negative everywhere, so a vanishing square `(x u + x w)²` on an edge avoiding
`v` is impossible: such an edge cannot exist. -/
theorem nbr_only_centre [Nonempty V] {v : V} (hv : G.maxDegree = G.degree v)
    (hΔ : 0 < G.maxDegree)
    (heq : topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G)
      = (G.maxDegree : ℝ) + 1)
    {u w : V} (hu : G.Adj v u) (huw : G.Adj u w) : w = v := by
  classical
  set d : ℝ := (G.maxDegree : ℝ) with hddef
  have hd : (0 : ℝ) < d := by rw [hddef]; exact_mod_cast hΔ
  by_contra hwv
  have hune : u ≠ v := (G.ne_of_adj hu).symm
  have hzero := rest_eq_zero G v hv hΔ heq u (Finset.mem_erase.mpr ⟨hune, Finset.mem_univ u⟩)
    w (Finset.mem_erase.mpr ⟨hwv, Finset.mem_univ w⟩)
  rw [edgeSq, if_pos huw] at hzero
  have hxu : testVec G v d u = 1 / d := testVec_adj G d hu
  have hxw : 0 ≤ testVec G v d w := by
    unfold testVec
    by_cases h1 : w = v
    · simp [h1]
    · by_cases h2 : G.Adj v w
      · rw [if_neg h1, if_pos h2]
        exact le_of_lt (one_div_pos.mpr hd)
      · rw [if_neg h1, if_neg h2]
  have hsum : (0 : ℝ) < testVec G v d u + testVec G v d w := by
    rw [hxu]; have := one_div_pos.mpr hd; linarith
  nlinarith [hzero, hsum]

end Converse

/-! ## 4. Connectedness closes it

**AND THE WALK LEMMA IS NOT DECLARED HERE** (`ERRATUM 536`). A first draft of this section proved
*a set closed under adjacency contains everything a walk from inside it reaches* under the name
`mem_of_walk`, by induction along the walk. `TorusEmbeddingGeneral.mem_of_walk` is that theorem —
same name, same statement, same three-line proof, and inside this file's import closure.
`newnames_scan` refused the commit; the declaration is deleted and the original is called.
-/

section Classification
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **THE FILE'S THEOREM.** -/
theorem star_of_topEigen_eq [Nontrivial V] (hconn : G.Connected)
    (heq : topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G)
      = (G.maxDegree : ℝ) + 1) :
    ∃ v : V, G = starGraph v := by
  classical
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hΔ : 0 < G.maxDegree := by
    rw [hv]; exact SignlessPrimitive.degree_pos_of_connected G hconn v
  have heq' := heq
  -- every vertex is `v` or one of its neighbours
  have hall : ∀ u : V, u = v ∨ G.Adj v u := by
    intro u
    have hclosed : ∀ a b : V, (a = v ∨ G.Adj v a) → G.Adj a b → (b = v ∨ G.Adj v b) := by
      rintro a b (rfl | ha) hab
      · exact Or.inr hab
      · exact Or.inl (nbr_only_centre G hv hΔ heq' ha hab)
    obtain ⟨p⟩ := hconn.preconnected v u
    exact TorusEmbeddingGeneral.mem_of_walk (S := {x | x = v ∨ G.Adj v x})
      (fun x y hx hxy => hclosed x y hx hxy) p (Or.inl rfl)
  refine ⟨v, ?_⟩
  ext a b
  constructor
  · intro hab
    by_cases hav : a = v
    · exact Or.inl ⟨hav, fun hb => (hav ▸ hab).ne' (hb ▸ rfl) |>.elim⟩
    · have hbv : b = v := by
        rcases hall a with rfl | ha
        · exact absurd rfl hav
        · exact nbr_only_centre G hv hΔ heq' ha hab
      exact Or.inr ⟨hbv, hav⟩
  · rintro (⟨rfl, hb⟩ | ⟨rfl, ha⟩)
    · rcases hall b with rfl | h
      · exact absurd rfl hb
      · exact h
    · rcases hall a with rfl | h
      · exact absurd rfl ha
      · exact h.symm

/-- **AND SO THE LOWER END OF THE BRACKET IS ATTAINED EXACTLY ON THE STARS.** -/
theorem topEigen_eq_iff_star [Nontrivial V] (hconn : G.Connected) :
    topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G)
        = (G.maxDegree : ℝ) + 1 ↔ ∃ v : V, G = starGraph v := by
  constructor
  · intro h
    exact star_of_topEigen_eq G hconn h
  · rintro ⟨v, hGv⟩
    subst hGv
    obtain rfl : ‹DecidableRel (starGraph v).Adj› = StarAdjNormExact.decidableStarAdj v :=
      Subsingleton.elim _ _
    exact (SignlessStarExact.maxDegree_add_one_eq_topEigen_star v).symm

end Classification

end SignlessStarConverse
