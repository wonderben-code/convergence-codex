import StarAdjNormExact
import SignlessMaxDegreeBound
import SignlessConjugateMultiplicity
import SignlessFlatConnected

/-!
# The star attains `Δ + 1`, and the signless bracket is sharp at both ends at the same `Δ`

`SignlessTopDegreeBounds` put the top of a graph's signless spectrum between `Δ + 1` and `2Δ` and
proved the **upper** end exact on regular graphs. `SignlessMaxDegreeBound` proved the lower end and
fenced itself: *`Δ + 1` is attained exactly on a star, which is **not shown here**; the file
exhibits no graph where this bound is tight.* **This shows it**, and then does the thing the two
fences together make possible and neither could do alone.

## What is proved

**`topEigen_le_of_quadForm_le`** — the converse of Rayleigh's easy half, in `dotProduct`: a bound
`x ⬝ᵥ A *ᵥ x ≤ M · (x ⬝ᵥ x)` **at every vector** puts the top eigenvalue under `M`. Three lines from
`RayleighVariational.exists_quadForm_eq_topEigen`, which produces the vector where the form attains
the top, and stated in general because no graph enters it.

**AND THE ESTATE COULD ALREADY REACH IT, BY A LONGER ROUTE, WHICH IS SAID HERE RATHER THAN
DISCOVERED LATER** (`ERRATUM 532`). `RayleighPow.eigenvalues_le_of_quadForm_le` bounds **each**
eigenvalue from a form bound stated on `EuclideanSpace`, and `Finset.sup'_le` turns that into this
— at the cost of a currency conversion between `inner` and `⬝ᵥ`. No declaration states the
composite, `topEigen_le` and `le_of_quadForm` were both grepped for before this one was written,
and the proof below stays in `dotProduct` throughout instead.

**`dotProduct_self_split`** — a vector's length split at one point:
`x ⬝ᵥ x = x(c)² + ∑_{v ≠ c} x(v)²`. It is the `have` inside
`StarAdjNormExact.abs_quadForm_le`, promoted to a declaration and
generalised from that proof's vector to any vector, because this file needs it twice.

**`quadForm_signlessLap_star`** — the star's signless quadratic form, exactly:
`(|V| − 1)·x(c)² + ∑_{v ≠ c} x(v)² + 2·x(c)·∑_{v ≠ c} x(v)`. The degree matrix contributes the first
two terms — `|V| − 1` at the centre and `1` at each leaf — and `StarAdjNormExact.quadForm_star`
contributes the third, unchanged.

**`quadForm_signlessLap_star_le`** — that form never exceeds `|V|·(x ⬝ᵥ x)`. **Cauchy–Schwarz and
`2ab ≤ a² + b²`, the same two steps `StarAdjNormExact` spends on the adjacency matrix**, and it is
worth saying why the same steps land somewhere else: there they bound `2·x(c)·S` by `√n` times the
length, because the adjacency form is *all* cross term; here the cross term is carried by a
diagonal that is already `n` at the centre, and the two conspire to `n + 1` rather than to `√n`.

**`topEigen_signlessLap_star`** — **THE FILE'S THEOREM.** On the star with any centre, over any
finite vertex type with at least two points,

```
topEigen (signlessLap (starGraph c)) = Fintype.card V
```

exactly. The upper half is the bound above; the lower half is
`SignlessMaxDegreeBound.maxDegree_add_one_le_topEigen` with `maxDegree_starGraph`, and `Δ + 1` is
`(|V| − 1) + 1`. **No side length, no dimension, no mass** — the statement is about a vertex count.

**`maxDegree_add_one_eq_topEigen_star`** — so the lower bound of the bracket is **attained**, which
is the sentence the previous file could not write.

**`topEigen_lt_two_maxDegree_star`** — and the *upper* bound of the bracket is **strictly loose**
there, as soon as the star has three vertices: `|V| < 2(|V| − 1)`.

**`bracket_sharp_at_every_maxDegree`** — **and both ends are attained at the SAME maximum degree,
at EVERY maximum degree `≥ 1`.** On `Fin (m+2)` the star and `⊤` both have `Δ = m + 1`, so both are
bracketed by `[m+2, 2m+2]`; the star sits at the bottom and the complete graph at the top. **So
neither bound is improvable as a function of `Δ` alone** — not merely unimprovable somewhere, but
with a witness at each value of `Δ`. `bracket_sharp_at_both_ends` is `m = 1` written out: the path
at `3`, the triangle at `4`, both at `Δ = 2`.

**`topEigen_eq_of_finrank_eq`** — **the top of a Hermitian spectrum is determined by the
multiplicity function.** If two Hermitian matrices have the same `finrank` of eigenspace at every
real `μ`, their top eigenvalues agree. **THIS JOINS TWO CHAINS THAT HAD NOT BEEN JOINED**: every
multiplicity theorem in this estate is a `finrank` and every spectral-radius theorem is a
`Finset.sup'` of `hA.eigenvalues`, and the bridge is
`HermitianFibreCount.finrank_eigenspace_hermitian_eq_card_fibre` — positive multiplicity at `μ`
exactly when `μ` is an eigenvalue — through `HermitianFlatSpectrum.finrank_pos_of_mem_image` and
`SignlessFlatConnected.mem_image_of_finrank_pos`, one each way.

> ⚠ **A DRAFT OF THIS FILE FENCED THAT JOIN AS ABSENT, AND THE FENCE WAS FALSE** (`ERRATUM 531`'s
> rule, applied in review rather than after the commit). It read: *that is a statement about
> `finrank`s and `topEigen` is a `Finset.sup'` of `hA.eigenvalues`; the two are not joined in this
> estate, so the transfer is named as the route it would be and is not walked.* The two named
> lemmas above are the join and both predate this file. The paragraph is deleted and the transfer
> **is** walked, which is the whole of §6.

**`starGraph_colorable_two`, `topEigen_lapMatrix_star`** — so **the star's ORDINARY Laplacian has
the same spectral radius `|V|`**, by two-colourability and
`SignlessConjugateMultiplicity.finrank_eigenspace_signlessLap_eq_lap_of_colorable`. Free, once the
join above exists, and it is the second operator this file computes rather than a restatement of
the first: on a graph that is *not* two-colourable the two numbers genuinely differ, which
`SignlessExcessBothWays` proves.

## What is NOT here

* **NO CHARACTERISATION OF THE EQUALITY CASE.** `Δ + 1 = topEigen` is proved **on the star**. The
  classical statement is that a connected graph attains it *only* on a star, and the converse
  direction — attainment forces the star — is **not proved, not attempted, and not implied by
  anything here** (`ERRATUM 246`). One family of witnesses is not a classification.
* **NO UPPER SHARPENING, STILL.** `2Δ` is shown loose on the star and it is not replaced. Merris's
  bound and the edge-maximum of `deg u + deg v` are each a different argument and neither is
  attempted.
* **NOTHING ABOUT THE STAR'S OTHER EIGENVALUES.** The top is computed; the rest of the spectrum
  is not. In particular **no second eigenvalue and no gap**, exactly as its two predecessors.
* **NO OTHER FAMILY.** The path and the triangle are the only graphs computed here; the star is
  the only family.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a finite vertex type with decidable
equality, a centre `c`, and — for the exact value and everything after it — `Nontrivial V`. The
looseness statement additionally takes `3 ≤ Fintype.card V`. The general converse takes a Hermitian
matrix and `Nonempty V` and no graph at all.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessStarExact

open Matrix Finset SimpleGraph LaplacianSignless RayleighVariational StarAdjNormExact

/-! ## 1. The converse of Rayleigh's easy half, with no graph in it -/

section Converse
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- **A QUADRATIC-FORM CEILING AT EVERY VECTOR IS A CEILING ON THE TOP EIGENVALUE.**
`RayleighVariational.quadForm_le_topEigen` is the other direction and was already here. -/
theorem topEigen_le_of_quadForm_le {A : Matrix V V ℝ} (hA : A.IsHermitian) {M : ℝ}
    (h : ∀ x : V → ℝ, x ⬝ᵥ A *ᵥ x ≤ M * (x ⬝ᵥ x)) : topEigen hA ≤ M := by
  obtain ⟨x, hx0, hx⟩ := exists_quadForm_eq_topEigen hA
  have hxx : 0 < x ⬝ᵥ x := by
    refine lt_of_le_of_ne ?_ (Ne.symm fun h0 => hx0 (dotProduct_self_eq_zero.1 h0))
    rw [dotProduct]
    exact Finset.sum_nonneg fun p _ => mul_self_nonneg _
  have hle := h x
  rw [hx] at hle
  exact le_of_mul_le_mul_right hle hxx

end Converse

/-! ## 2. The star's signless quadratic form -/

section Star
variable {V : Type*} [Fintype V] [DecidableEq V] (c : V)

/-- The vector's own length, split at the centre. -/
theorem dotProduct_self_split (x : V → ℝ) :
    x ⬝ᵥ x = x c ^ 2 + ∑ v ∈ univ.erase c, x v ^ 2 := by
  rw [dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ c), sq]
  congr 1
  exact Finset.sum_congr rfl fun v _ => (sq (x v)).symm

/-- The degree matrix's contribution: `|V| − 1` at the centre and `1` at every leaf. -/
theorem sum_degree_sq_star (x : V → ℝ) :
    ∑ i : V, (((starGraph c).degree i : ℕ) : ℝ) * x i * x i
      = ((Fintype.card V : ℝ) - 1) * x c ^ 2 + ∑ v ∈ univ.erase c, x v ^ 2 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c), cast_degree_centre c]
  have hleaf : ∀ v ∈ univ.erase c,
      (((starGraph c).degree v : ℕ) : ℝ) * x v * x v = x v ^ 2 := by
    intro v hv
    rw [degree_leaf (Finset.mem_erase.mp hv).1]
    push_cast
    ring
  rw [Finset.sum_congr rfl hleaf]
  ring

/-- **THE STAR'S SIGNLESS QUADRATIC FORM, EXACTLY.** -/
theorem quadForm_signlessLap_star (x : V → ℝ) :
    x ⬝ᵥ (signlessLap (starGraph c)) *ᵥ x
      = ((Fintype.card V : ℝ) - 1) * x c ^ 2 + (∑ v ∈ univ.erase c, x v ^ 2)
        + 2 * x c * ∑ v ∈ univ.erase c, x v := by
  rw [signlessLap, Matrix.add_mulVec, dotProduct_add,
    SimpleGraph.dotProduct_mulVec_degMatrix, sum_degree_sq_star c x, quadForm_star c x]

/-! ## 3. Cauchy–Schwarz, and the ceiling at `|V|` -/

/-- **THE FORM NEVER EXCEEDS `|V|` TIMES THE LENGTH.** Cauchy–Schwarz bounds the leaf sum's square
by `(|V| − 1)` times the leaves' squared length, and `2ab ≤ a² + b²` spends the cross term against
the centre and that bound. -/
theorem quadForm_signlessLap_star_le (x : V → ℝ) :
    x ⬝ᵥ (signlessLap (starGraph c)) *ᵥ x ≤ (Fintype.card V : ℝ) * (x ⬝ᵥ x) := by
  classical
  set s : Finset V := univ.erase c with hs
  set S : ℝ := ∑ v ∈ s, x v with hS
  set T : ℝ := ∑ v ∈ s, x v ^ 2 with hT
  have hn : ((s.card : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by rw [hs, cast_card_erase c]
  have hCS : S ^ 2 ≤ ((Fintype.card V : ℝ) - 1) * T := by
    have hc := sq_sum_le_card_mul_sum_sq (s := s) (f := x)
    rwa [← hS, ← hT, hn] at hc
  rw [quadForm_signlessLap_star c x, dotProduct_self_split c x, ← hS, ← hT]
  nlinarith [sq_nonneg (x c - S), hCS]

/-! ## 4. The exact value -/

theorem topEigen_signlessLap_star_le [Nonempty V] :
    topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian (starGraph c))
      ≤ (Fintype.card V : ℝ) :=
  topEigen_le_of_quadForm_le _ (quadForm_signlessLap_star_le c)

/-- The star's maximum degree is the centre's. -/
theorem maxDegree_starGraph [Nontrivial V] :
    (starGraph c).maxDegree = Fintype.card V - 1 := by
  refine le_antisymm (SimpleGraph.maxDegree_le_of_forall_degree_le _ _ fun v => ?_) ?_
  · by_cases hv : v = c
    · rw [hv]; exact le_of_eq (degree_centre c)
    · rw [degree_leaf hv]
      have h2 := Fintype.one_lt_card (α := V)
      omega
  · rw [← degree_centre c]
    exact SimpleGraph.degree_le_maxDegree _ c

/-- **THE STAR'S SIGNLESS SPECTRAL RADIUS IS ITS VERTEX COUNT.** -/
theorem topEigen_signlessLap_star [Nontrivial V] :
    topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian (starGraph c))
      = (Fintype.card V : ℝ) := by
  refine le_antisymm (topEigen_signlessLap_star_le c) ?_
  have h2 : 2 ≤ Fintype.card V := Fintype.one_lt_card
  have hΔ : 0 < (starGraph c).maxDegree := by rw [maxDegree_starGraph c]; omega
  have h := SignlessMaxDegreeBound.maxDegree_add_one_le_topEigen (starGraph c) hΔ
  rw [maxDegree_starGraph c] at h
  have hc : ((Fintype.card V - 1 : ℕ) : ℝ) + 1 = (Fintype.card V : ℝ) := by
    have h1 : 1 ≤ Fintype.card V := by omega
    rw [Nat.cast_sub h1, Nat.cast_one]
    ring
  linarith

/-! ## 5. So the bracket's lower end is attained and its upper end is not -/

/-- **`Δ + 1` IS ATTAINED**, which is the sentence `SignlessMaxDegreeBound` could not write. -/
theorem maxDegree_add_one_eq_topEigen_star [Nontrivial V] :
    (((starGraph c).maxDegree : ℕ) : ℝ) + 1
      = topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian (starGraph c)) := by
  rw [topEigen_signlessLap_star c, maxDegree_starGraph c]
  have h1 : 1 ≤ Fintype.card V := Fintype.card_pos
  rw [Nat.cast_sub h1, Nat.cast_one]
  ring

/-- **AND `2Δ` IS STRICTLY LOOSE THERE**, from three vertices on. -/
theorem topEigen_lt_two_maxDegree_star [Nontrivial V] (h3 : 3 ≤ Fintype.card V) :
    topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian (starGraph c))
      < 2 * (((starGraph c).maxDegree : ℕ) : ℝ) := by
  rw [topEigen_signlessLap_star c, maxDegree_starGraph c]
  have h1 : 1 ≤ Fintype.card V := by omega
  rw [Nat.cast_sub h1, Nat.cast_one]
  have h3' : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast h3
  linarith

end Star

/-! ## 6. Both ends of the bracket, at the same maximum degree -/

section Both

/-- A regular graph's maximum degree is its degree. -/
theorem maxDegree_of_regular {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (h : G.IsRegularOfDegree k) : G.maxDegree = k := by
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  rw [hv, h v]

/-- **THE BRACKET `Δ + 1 ≤ topEigen ≤ 2Δ` IS SHARP AT BOTH ENDS, AT THE SAME `Δ`.**
On three vertices the star is the path and `⊤` is the triangle; both have maximum degree `2`, so
both are bracketed by `[3, 4]`, and the path sits at the bottom while the triangle sits at the top.
**Neither bound is improvable as a function of the maximum degree alone.** -/
theorem bracket_sharp_at_every_maxDegree (m : ℕ) :
    (starGraph (0 : Fin (m + 2))).maxDegree = m + 1
      ∧ (⊤ : SimpleGraph (Fin (m + 2))).maxDegree = m + 1
      ∧ topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian
          (starGraph (0 : Fin (m + 2)))) = (m : ℝ) + 2
      ∧ topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian
          (⊤ : SimpleGraph (Fin (m + 2)))) = 2 * ((m : ℝ) + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [maxDegree_starGraph (0 : Fin (m + 2)), Fintype.card_fin]
    omega
  · rw [maxDegree_of_regular _ (SimpleGraph.IsRegularOfDegree.top (V := Fin (m + 2))),
      Fintype.card_fin]
    omega
  · rw [topEigen_signlessLap_star (0 : Fin (m + 2)), Fintype.card_fin]
    push_cast
    ring
  · rw [SignlessTopDegreeBounds.topEigen_regular _
      (SimpleGraph.IsRegularOfDegree.top (V := Fin (m + 2))), Fintype.card_fin]
    push_cast
    ring

/-- The smallest instance, spelled out: on three vertices the path sits at `3` and the triangle at
`4`, and both have maximum degree `2`. -/
theorem bracket_sharp_at_both_ends :
    (starGraph (0 : Fin 3)).maxDegree = 2
      ∧ (⊤ : SimpleGraph (Fin 3)).maxDegree = 2
      ∧ topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian
          (starGraph (0 : Fin 3))) = 3
      ∧ topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian
          (⊤ : SimpleGraph (Fin 3))) = 4 := by
  obtain ⟨h1, h2, h3, h4⟩ := bracket_sharp_at_every_maxDegree 1
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [h3]; norm_num
  · rw [h4]; norm_num

end Both

/-! ## 7. The multiplicity function determines the top, and the star's Laplacian follows -/

section Transfer
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- **A MULTIPLICITY CEILING AT EVERY `μ` IS A CEILING ON THE TOP.** The top eigenvalue is attained,
so it has positive multiplicity; the hypothesis carries that to the other matrix, and positive
multiplicity there makes it an eigenvalue there. -/
theorem topEigen_le_of_finrank_le {A B : Matrix V V ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id))
        ≤ Module.finrank ℝ (LinearMap.ker (Matrix.toLin' B - μ • LinearMap.id))) :
    topEigen hA ≤ topEigen hB := by
  classical
  obtain ⟨i, hi⟩ := SignlessPerronSimple.exists_topEigen hA
  have hmem : topEigen hA ∈ Finset.univ.image hA.eigenvalues :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  have hposB := lt_of_lt_of_le (HermitianFlatSpectrum.finrank_pos_of_mem_image hA hmem) (h _)
  obtain ⟨j, -, hj⟩ :=
    Finset.mem_image.mp (SignlessFlatConnected.mem_image_of_finrank_pos hB hposB)
  rw [← hj]
  exact SignlessPerronSimple.le_topEigen hB j

/-- **THE TOP OF A HERMITIAN SPECTRUM IS DETERMINED BY THE MULTIPLICITY FUNCTION.** -/
theorem topEigen_eq_of_finrank_eq {A B : Matrix V V ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id))
        = Module.finrank ℝ (LinearMap.ker (Matrix.toLin' B - μ • LinearMap.id))) :
    topEigen hA = topEigen hB :=
  le_antisymm (topEigen_le_of_finrank_le hA hB fun μ => (h μ).le)
    (topEigen_le_of_finrank_le hB hA fun μ => (h μ).ge)

end Transfer

section Colouring
variable {V : Type*} (c : V)

/-- The star is two-colourable: the centre one colour, every leaf the other. **No finiteness and
no decidable equality**: the colouring is `classical` and its type mentions neither. -/
theorem starGraph_colorable_two : (starGraph c).Colorable 2 := by
  classical
  refine ⟨SimpleGraph.Coloring.mk (fun v => if v = c then (0 : Fin 2) else 1) ?_⟩
  intro u v h
  simp only []
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg h2]; decide
  · rw [if_neg h2, if_pos h1]; decide

end Colouring

section StarTransfer
variable {V : Type*} [Fintype V] [DecidableEq V] (c : V)

/-- **AND THE STAR'S ORDINARY LAPLACIAN HAS THE SAME SPECTRAL RADIUS.** -/
theorem topEigen_lapMatrix_star [Nontrivial V] :
    topEigen (SignlessBipartite.lapMatrix_isHermitian' (starGraph c))
      = (Fintype.card V : ℝ) := by
  rw [← topEigen_signlessLap_star c]
  exact (topEigen_eq_of_finrank_eq _ _ fun μ =>
    SignlessConjugateMultiplicity.finrank_eigenspace_signlessLap_eq_lap_of_colorable
      (starGraph_colorable_two c) μ).symm

end StarTransfer

end SignlessStarExact
