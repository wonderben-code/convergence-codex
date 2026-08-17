import TorusEmbeddingGeneral

/-!
# Every dimension, because `d = 1` was my restriction and not the argument's

`TorusEmbeddingGeneral` proved the watchlist's clause at `d = 1` and wrote, of the general case:

> **`d = 1` only**, as everywhere in this chain: at `d ≥ 2` sites do not have degree `2` and the
> local-bijection step fails at its first line.

**The first half of that sentence is true and the second half is false.** At `d ≥ 2` a site has
degree `2d`, not `2` — and the local-bijection step does not care what the number is, only that
**the same exact count holds at both ends**. The step failed at nothing. What was missing was one
theorem, `torusGraph_degree_eq`, and the estate was most of the way to it already.

## What is proved

* **`stepT_adj`** — the converse of `TorusDecay.adjT_eq_stepT`. That file built the cyclic step map
  `stepT p i b` and proved **every neighbour is a step**, which is what an *upper* bound `≤ 2d`
  needs. This proves **every step is a neighbour**, which is what a lower bound needs, and it is
  where `3 ≤ n` enters: at `n ≤ 2` the forward and backward steps coincide, and
  `TorusDecay`'s own header says so.
* **`stepT_injective`** — the `2d` steps are distinct, again at `3 ≤ n`.
* **`torusGraph_degree_eq`** — hence **every site of `torusGraph d n` has degree exactly `2d`**, in
  every dimension, at every side length `≥ 3`. `TorusDecay.torusGraph_degree_le` gave `≤ 2d`;
  this closes it to an equality and so **strengthens
  `TorusCycleTheory.torusGraph_degree_le_attained` from `d = 1` to all `d`**.
* **`neighborFinset_image_of_torusEmbedding`**, **`side_eq_of_isTorusEmbedding`**,
  **`no_torus_embedding_of_ne`**, **`no_torus_embedding_double`** — the argument of
  `TorusEmbeddingGeneral`, with `2` replaced by `2d` and `n^1` by `n^d`. **No new idea appears
  here.** That is the point: the idea was never about `d = 1`. The leaves are renamed rather than
  shadowing that file's: `ERRATUM 193` recorded what leaf-name collisions cost this estate, and
  three more next door would have been the cheapest possible way to repeat it.
* **`isTorusEmbedding_one_iff`** and the `example` after it — the `d = 1` case is *definitionally*
  `TorusEmbedding.IsSiteEmbedding`, and `TorusEmbeddingGeneral.no_embedding_double` is re-derived
  from the general theorem by `rfl`-level agreement rather than by resemblance.

## So the watchlist clause is settled as written

`UNLOCK_WATCHLIST`'s infinite-volume item says *"no embedding of `torusGraph d n` into
`torusGraph d (2n)`"* — **with a `d`, and the `d` is now proved rather than specialised away.**

## What this is NOT

**`n = 2` remains the exception and is still the same exception.** `3 ≤ n` is not a convenience: at
`n = 2` the two cyclic steps along a coordinate *are* the same step, the degree is `d` rather than
`2d`, and `TorusEmbedding.embedding_two_into_four` exhibits an actual embedding. The hypothesis
excludes exactly the side length at which the torus **is** the box.

**Nothing here is about covariances.** The item this clause belongs to is about a compatible family
of measures; a missing graph embedding is not an incompatible family, and clause (i) remains
`ASSUMPTIONS_LEDGER` 47, an author's decision. **`OS4` does not move.** No sequence of measures, no
limit, no tightness. **No spectral gap is claimed and no published tag moves.**

**No girth, no `cycleGraph`, and no reflection positivity is used or affected.** The `d ≥ 2` torus
is a product of cycles and Mathlib's cycle theory says nothing about it; that is precisely why the
`cycleGraph` route could not have reached this and the degree route does.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusEmbeddingAllDims

open TorusReflection BoxGraph SimpleGraph

variable {d n : ℕ}

/-! ## 1. Every cyclic step is a neighbour -/

/-- The moved coordinate of a forward step, as a natural number. -/
theorem val_stepT_true (p : Site d n) (i : Fin d) :
    (TorusDecay.stepT p i true i).val = if (p i).val + 1 = n then 0 else (p i).val + 1 := by
  simp [TorusDecay.stepT]

/-- The moved coordinate of a backward step, as a natural number. -/
theorem val_stepT_false (p : Site d n) (i : Fin d) :
    (TorusDecay.stepT p i false i).val = if (p i).val = 0 then n - 1 else (p i).val - 1 := by
  simp [TorusDecay.stepT]

/-- Away from the coordinate it moves, a step changes nothing. -/
theorem stepT_apply_of_ne (p : Site d n) {i j : Fin d} (h : j ≠ i) (b : Bool) :
    TorusDecay.stepT p i b j = p j := Function.update_of_ne h _ _

/-- **A STEP MOVES.** At `n ≤ 2` this fails: the backward step from `0` lands on `n - 1`, which is
`0` when `n = 1`, and the two directions coincide when `n = 2`. -/
theorem stepT_ne_self (hn : 3 ≤ n) (p : Site d n) (i : Fin d) (b : Bool) :
    TorusDecay.stepT p i b i ≠ p i := by
  have hv := (p i).isLt
  rw [Ne, Fin.ext_iff]
  cases b
  · rw [val_stepT_false]; split_ifs <;> omega
  · rw [val_stepT_true]; split_ifs <;> omega

/-- **THE CONVERSE OF `TorusDecay.adjT_eq_stepT`.** Every cyclic step lands on a neighbour.

That file proved **every neighbour is a step**, which is what an *upper* bound `≤ 2d` needs. This
is the direction a *lower* bound needs, and `3 ≤ n` is where the side length enters. -/
theorem stepT_adj (hn : 3 ≤ n) (p : Site d n) (i : Fin d) (b : Bool) :
    (torusGraph d n).Adj p (TorusDecay.stepT p i b) := by
  have hv := (p i).isLt
  refine ⟨i, fun j hj => (Function.update_of_ne hj _ _).symm,
    (stepT_ne_self hn p i b).symm, ?_⟩
  cases b
  · rw [val_stepT_false]; split_ifs <;> omega
  · rw [val_stepT_true]; split_ifs <;> omega

/-- **AND THE `2d` STEPS ARE DISTINCT.** Different coordinates differ at the coordinate moved,
because a step moves; the two directions along one coordinate differ because `3 ≤ n` keeps
successor and predecessor apart. -/
theorem stepT_injective (hn : 3 ≤ n) (p : Site d n) :
    Function.Injective fun t : Fin d × Bool => TorusDecay.stepT p t.1 t.2 := by
  rintro ⟨i, b⟩ ⟨i', b'⟩ h
  simp only at h
  have hv := (p i).isLt
  have hi : i = i' := by
    by_contra hii
    have hx := congrFun h i
    rw [stepT_apply_of_ne p hii b'] at hx
    exact stepT_ne_self hn p i b hx
  subst hi
  have hval := congrFun h i
  rw [Fin.ext_iff] at hval
  have hbb : b = b' := by
    cases b <;> cases b'
    · rfl
    · exfalso
      rw [val_stepT_false, val_stepT_true] at hval
      split_ifs at hval <;> omega
    · exfalso
      rw [val_stepT_true, val_stepT_false] at hval
      split_ifs at hval <;> omega
    · rfl
  simp [hbb]

/-! ## 2. The degree, exactly -/

/-- **EVERY SITE OF `torusGraph d n` HAS DEGREE EXACTLY `2d`**, in every dimension, at every side
length `≥ 3`.

`TorusDecay.torusGraph_degree_le` supplied `≤ 2d` and remarked that at `n ≤ 2` the true degree is
smaller. This closes the bound to an equality in exactly the régime where that remark does not
bite, and it is the one theorem `TorusEmbeddingGeneral` was missing. -/
theorem torusGraph_degree_eq (hn : 3 ≤ n) (p : Site d n) :
    (torusGraph d n).degree p = 2 * d := by
  refine le_antisymm (TorusDecay.torusGraph_degree_le p) ?_
  have hcard : ((Finset.univ : Finset (Fin d × Bool))).card = 2 * d := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun t => TorusDecay.stepT p t.1 t.2) (fun t _ => ?_)
    ((stepT_injective hn p).injOn)
  simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset]
  exact stepT_adj hn p t.1 t.2

/-! ## 3. The embedding argument, with `2` replaced by `2d` -/

/-- An injective site map that preserves edges, in any dimension — `TorusEmbedding.IsSiteEmbedding`
with the `1` opened up. -/
def IsTorusEmbedding {d m n : ℕ} (φ : Site d m → Site d n) : Prop :=
  Function.Injective φ ∧
    ∀ p q, (torusGraph d m).Adj p q → (torusGraph d n).Adj (φ p) (φ q)

/-- **AN EMBEDDING IS A LOCAL BIJECTION**, at every dimension. The proof is
`TorusEmbeddingGeneral.neighborFinset_image` with the constant `2` replaced by `2d`, which is the
whole of the difference. -/
theorem neighborFinset_image_of_torusEmbedding {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    {φ : Site d a → Site d b} (h : IsTorusEmbedding φ) (v : Site d a) :
    ((torusGraph d a).neighborFinset v).image φ = (torusGraph d b).neighborFinset (φ v) := by
  refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [SimpleGraph.mem_neighborFinset] at hx ⊢
    exact h.2 _ _ hx
  · rw [Finset.card_image_of_injective _ h.1, SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.card_neighborFinset_eq_degree, torusGraph_degree_eq ha,
      torusGraph_degree_eq hb]

/-- **ANY EMBEDDING BETWEEN TORI OF SIDE `≥ 3` FORCES THE SIDES EQUAL, IN EVERY POSITIVE
DIMENSION.** -/
theorem side_eq_of_isTorusEmbedding {a b : ℕ} (hd : 1 ≤ d) (ha : 3 ≤ a) (hb : 3 ≤ b)
    {φ : Site d a → Site d b} (h : IsTorusEmbedding φ) : a = b := by
  have hbase : Site d a := fun _ => ⟨0, by omega⟩
  have hclosed : ∀ ⦃x y⦄, x ∈ Set.range φ → (torusGraph d b).Adj x y → y ∈ Set.range φ := by
    rintro _ y ⟨v, rfl⟩ hxy
    have hmem : y ∈ ((torusGraph d a).neighborFinset v).image φ := by
      rw [neighborFinset_image_of_torusEmbedding ha hb h v, SimpleGraph.mem_neighborFinset]
      exact hxy
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hmem
    exact ⟨w, rfl⟩
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨w⟩ := (TorusDecay.torusGraph_connected (n := b) d (by omega)).preconnected
      (φ hbase) y
    have hy : y ∈ Set.range φ := TorusEmbeddingGeneral.mem_of_walk hclosed w ⟨hbase, rfl⟩
    exact hy
  have hcard : a ^ d = b ^ d := by
    have := Fintype.card_of_bijective (f := φ) ⟨h.1, hsurj⟩
    simpa [Fintype.card_fun] using this
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd hcard (Nat.ne_of_lt (Nat.pow_lt_pow_left hlt (by omega : d ≠ 0)))
  · exact heq
  · exact absurd hcard.symm (Nat.ne_of_lt (Nat.pow_lt_pow_left hgt (by omega : d ≠ 0)))

/-- **SO THERE IS NO EMBEDDING BETWEEN TORI OF DIFFERENT SIDE LENGTHS `≥ 3`, IN ANY DIMENSION.** -/
theorem no_torus_embedding_of_ne {a b : ℕ} (hd : 1 ≤ d) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a ≠ b)
    (φ : Site d a → Site d b) : ¬ IsTorusEmbedding φ :=
  fun h => hab (side_eq_of_isTorusEmbedding hd ha hb h)

/-- **THE WATCHLIST'S CLAUSE, WITH ITS `d`.** There is no injective graph homomorphism
`torusGraph d n → torusGraph d (2n)` for any `n ≥ 3` and any `d ≥ 1`. -/
theorem no_torus_embedding_double (hd : 1 ≤ d) (n : ℕ) (hn : 3 ≤ n)
    (φ : Site d n → Site d (2 * n)) : ¬ IsTorusEmbedding φ :=
  no_torus_embedding_of_ne hd hn (by omega) (by omega) φ

/-! ## 4. Agreement with the `d = 1` file, checked by the kernel -/

/-- At `d = 1` this predicate **is** `TorusEmbedding.IsSiteEmbedding`, definitionally. -/
theorem isTorusEmbedding_one_iff {m n : ℕ} (φ : Site 1 m → Site 1 n) :
    IsTorusEmbedding φ ↔ TorusEmbedding.IsSiteEmbedding φ := Iff.rfl

/-- **AND `TorusEmbeddingGeneral`'S THEOREM IS THIS ONE AT `d = 1`.** Machine-checked, so the two
files agree rather than resemble each other. -/
example (n : ℕ) (hn : 3 ≤ n) (φ : Site 1 n → Site 1 (2 * n)) :
    ¬ TorusEmbedding.IsSiteEmbedding φ :=
  no_torus_embedding_double (d := 1) le_rfl n hn φ

end TorusEmbeddingAllDims
