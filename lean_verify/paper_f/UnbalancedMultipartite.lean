import MultipartiteMultiplicity

/-!
# The complete multipartite graph with parts of different sizes

**THE PREVIOUS UNIT'S LAST FENCE WAS THIS FILE'S SUBJECT.** `MultipartiteMultiplicity` closed with
*"NOTHING UNBALANCED. Parts of different sizes change the degree per part and the row identity with
it."* Both change, and the Laplacian's spectrum survives the change **exactly**: `μ` is an
eigenvalue **iff** it is `0` with a vertex present, the vertex count `N` with two parts non-empty,
or `N − nᵢ` for a part of two or more vertices (`isEigenvalue_lapMatrix_unbal_iff`). No hypothesis
on the number of parts or on any part size — strictly fewer than the balanced chain needed.

**THE VERTEX TYPE IS NOW A SIGMA TYPE**, `Σ i, V i`, and the graph is Mathlib's
`SimpleGraph.completeMultipartiteGraph` — adjacency is `p.1 ≠ q.1`, decided here by one `instance`.
The balanced files work on `Fin r × Fin t` with `completeEquipartiteGraph`; nothing is transported
between the two settings, and this file proves its row identities from the sigma type directly.

**WHERE THE UNBALANCED CASE COSTS SOMETHING, MEASURED.** Three places, all in `§1`:
* the non-neighbours of `p` are the sigma-set over the **other** parts, so the adjacency row is
  `∑x − partTotal x p.1` and needs `Finset.sum_sigma` over `univ.erase p.1`;
* the degree is `N − n_{p.1}`, a **natural-number** subtraction, so `Finset.sum_erase_eq_sub` —
  which the ℝ-valued row above uses freely — is unavailable, and the count goes through
  `Finset.add_sum_erase` and `omega` instead;
* that truncated subtraction is only harmless because `card_part_le` proves `nᵢ ≤ N`, and
  `degMatrix_mulVec_multi` quotes it to push the cast into ℝ.

**THE ONE STRUCTURAL GAIN.** On a vector that depends only on which part its vertex is in, `L` acts
as `N·f − ∑ᵢ nᵢ fᵢ` (`lapMatrix_mulVec_comp_fst`) — the quotient matrix, visible with no quotient
construction. The constant vector and the `nᵢ`-weighted zero-sum vectors are its two eigenvector
families, and that is the whole of `§2`.

## What is proved

**`partTotal`, `sum_partTotal`, `neighborFinset_eq`, `adjMatrix_mulVec_multi`, `card_part_le`,
`degree_multi`, `degMatrix_mulVec_multi`, `lapMatrix_mulVec_multi`** — the row identities:
`(Lx)_p = (N − n_{p.1})·x_p − ∑x + partTotal x p.1`.

**`sum_card_part`, `partTotal_comp_fst`, `sum_comp_fst`, `lapMatrix_mulVec_comp_fst`,
`lapMatrix_mulVec_multi_const`, `lapMatrix_mulVec_comp_fst_of_sum_eq_zero`** — the quotient action,
`0` on the constants, and `N` on the weighted zero-sum part-dependent vectors.

**`lapMatrix_mulVec_multi_of_supported`** — `N − nᵢ` on the vectors supported in part `i` with
vanishing part total. **`lapMatrix_mulVec_multi_of_part_const`** — `N` again, from the part totals
alone, which is the form the exhaustion argument needs.

**`eigenvalue_lapMatrix_unbal`** — **AND THERE IS NOTHING ELSE, WITH THE SIZE CONDITIONS THAT MAKE
IT SHARP.** For `x ≠ 0`, `Lx = μx` forces `μ = 0`, or `μ = N` **and two parts are non-empty**, or
`μ = N − nᵢ` **for a part with two or more vertices**. Two steps carry the conditions. The
within-part difference trick gives `(N − nᵢ − μ)(x_p − x_q) = 0`, and a part is constant either
because that factor cancels — which needs `1 < nᵢ` to have two vertices to compare — or because it
is a singleton and there is nothing to compare; so the third disjunct can be restricted to parts of
size at least two. And at `μ = N` the total sum vanishes, which a single non-empty part cannot
manage, since the part totals are then `nᵢ x` and `nᵢ ≥ 1`. **No spectral theorem, no
diagonalisation, and — read from `#check` — no hypothesis beyond the finiteness instances.**

**`exists_eigenvector_multi_zero`, `exists_eigenvector_multi_part`,
`exists_eigenvector_multi_top`** — the converse, with explicit witnesses: `0` whenever there is a
vertex, `N − nᵢ` whenever part `i` has two vertices (a difference of two of its indicators), `N`
whenever two parts are non-empty (`nⱼ` on part `i` against `−nᵢ` on part `j`).

**`isEigenvalue_lapMatrix_unbal_iff`** — **SO THE TWO MEET AND THE SPECTRUM IS EXACT.** The
exhaustion's three disjuncts are precisely the three realisations' hypotheses, which is why this is
an **iff** and not a bound. This is a complete spectral description of an arbitrary complete
multipartite graph, and the estate's first for a family with a free parameter per part.

**`signlessLap_mulVec_multi`, `signlessLap_mulVec_multi_one`, `not_isEigenvector_one_signlessLap`**
— **the signless Laplacian's absence below is a theorem, not an excuse.** `Q` returns twice the
degree on the constant vector, so as soon as two parts differ in size the constant vector is an
eigenvector of `Q` for **no** scalar. The balanced family's top eigenvalue `2(r−1)t` has no
unbalanced analogue reachable by the balanced argument, and this file proves that instead of
asserting it.

**`card_path_example`, `path_example_spectrum`, `path_example_not_eigenvalue_two`** — a numerical
check of the whole description at one graph. Parts of sizes `1` and `2` give three vertices and the
eigenvalues **exactly** `0`, `1`, `3` — the Laplacian spectrum of the path on three vertices, known
before the instantiation was written. **The identification of that two-part family with the path is
not formalised**; what is machine-checked is that the general theorems yield those numerals and no
others. **And the size conditions are shown necessary, not decorative**: `2` is `N − n₀`, it passes
a size-blind reading of `§4`, and `path_example_not_eigenvalue_two` proves it is not an eigenvalue.

## What is NOT here

* **NO SIGNLESS SPECTRUM.** Only the row identity and the obstruction above. `Q`'s eigenvalues on
  an unbalanced family are not reachable by the balanced route, and
  `not_isEigenvector_one_signlessLap` is the measured reason rather than a guess.
* **NO EIGENSPACE DIMENSIONS, SO NO MULTIPLICITIES.** The balanced chain counts three eigenspaces
  and adds them to `rt` (`MultipartiteMultiplicity.finrank_eigenspaces_multi_add`). Here parts of
  equal size share an eigenvalue, so the eigenspace of `N − n` is the sum over **all** parts of
  that size and its dimension is a sum over a fibre of `i ↦ nᵢ` — a different count, not
  attempted, and no cost is offered for it (`ERRATUM 246`). The spectrum above is a description of
  the eigenvalue **set**, and says nothing about how often each occurs.
* **NO CHARACTERISTIC POLYNOMIAL**, as in the four units before this one: that step needs
  diagonalisability and these arguments avoid it.
* **NOTHING ABOUT FIELD SYMMETRIES.** `CompleteFieldSymmetry` and `MultipartiteEigenspace` compose
  their two-dimensional eigenspaces with `FieldSymmetryFinite.finite_iff_lapMatrix`; that
  composition needs the dimensions above and so is not available here.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and `OS1`
  in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `ι` a `Fintype` with `DecidableEq`, each
`V i` a `Fintype` with `DecidableEq` — the last needed only because `degMatrix` is a `diagonal`.
Beyond those instances the row identities, `eigenvalue_lapMatrix_unbal` and the `iff` take
**nothing**: no `1 ≤ r`, no `1 ≤ nᵢ`, no non-emptiness. The size conditions live in the statements,
where they are necessary, rather than in the hypotheses, where they were not. The three
realisation theorems take, respectively, `Nonempty (Σ i, V i)`, `1 < Fintype.card (V i)`, and
`i ≠ j` with both parts non-empty.

**A NAMING NOTE** (`newnames_scan`). The part sum is called `partTotal` here, not `partSum`, and the
exhaustion theorem `eigenvalue_lapMatrix_unbal`, not `eigenvalue_lapMatrix_multi`, only to keep
every short name in this file unique estate-wide; `MultipartiteSpectrum` owns those two names for
the balanced family. They are the same notions over a different vertex type, and no declaration
here is transported from there.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace UnbalancedMultipartite

open Matrix Finset SimpleGraph LaplacianSignless

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

instance : DecidableRel (completeMultipartiteGraph V).Adj := fun p q =>
  inferInstanceAs (Decidable (p.1 ≠ q.1))

/-! ## 1. The row identities, with the degree now depending on the part -/

/-- The sum of a vector over one part. Called `partTotal` rather than `partSum` only to keep the
short name unique; the header says why. -/
def partTotal (x : (Σ i, V i) → ℝ) (i : ι) : ℝ := ∑ a : V i, x ⟨i, a⟩

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem sum_partTotal (x : (Σ i, V i) → ℝ) : ∑ i, partTotal x i = ∑ p, x p := by
  simp only [partTotal]
  exact (Fintype.sum_sigma x).symm

omit [∀ i, DecidableEq (V i)] in
/-- A vertex's neighbours are everything outside its own part. -/
theorem neighborFinset_eq (p : Σ i, V i) :
    (completeMultipartiteGraph V).neighborFinset p
      = Finset.univ.filter (fun q : Σ i, V i => q.1 ≠ p.1) := by
  ext q
  simp [SimpleGraph.mem_neighborFinset, ne_comm]

omit [∀ i, DecidableEq (V i)] in
theorem adjMatrix_mulVec_multi (x : (Σ i, V i) → ℝ) (p : Σ i, V i) :
    ((completeMultipartiteGraph V).adjMatrix ℝ *ᵥ x) p = (∑ q, x q) - partTotal x p.1 := by
  classical
  rw [SimpleGraph.adjMatrix_mulVec_apply, neighborFinset_eq]
  have hset : Finset.univ.filter (fun q : Σ i, V i => q.1 ≠ p.1)
      = (Finset.univ.erase p.1).sigma (fun _ => Finset.univ) := by
    ext q
    simp [Finset.mem_sigma, Finset.mem_erase]
  rw [hset, Finset.sum_sigma]
  have hcongr : ∀ i ∈ Finset.univ.erase p.1, ∑ a : V i, x ⟨i, a⟩ = partTotal x i :=
    fun i _ => rfl
  rw [Finset.sum_congr rfl hcongr, Finset.sum_erase_eq_sub (Finset.mem_univ p.1), sum_partTotal]

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- Each part is no bigger than the whole, which is what makes the truncated subtraction in
`degree_multi` harmless. -/
theorem card_part_le (i : ι) : Fintype.card (V i) ≤ Fintype.card (Σ i, V i) :=
  Fintype.card_le_of_injective (Sigma.mk i) sigma_mk_injective

omit [∀ i, DecidableEq (V i)] in
/-- **The degree depends on the part**: it is `N − n_{p.1}`, and this is the identity the balanced
files did not need. -/
theorem degree_multi (p : Σ i, V i) :
    (completeMultipartiteGraph V).degree p
      = Fintype.card (Σ i, V i) - Fintype.card (V p.1) := by
  classical
  have hset : (completeMultipartiteGraph V).neighborFinset p
      = (Finset.univ.erase p.1).sigma (fun _ => Finset.univ) := by
    rw [neighborFinset_eq]
    ext q
    simp [Finset.mem_sigma, Finset.mem_erase]
  rw [SimpleGraph.degree, hset, Finset.card_sigma, Fintype.card_sigma]
  simp only [Finset.card_univ]
  have h := Finset.add_sum_erase Finset.univ (fun i => Fintype.card (V i)) (Finset.mem_univ p.1)
  simp only at h
  omega

theorem degMatrix_mulVec_multi (x : (Σ i, V i) → ℝ) (p : Σ i, V i) :
    ((completeMultipartiteGraph V).degMatrix ℝ *ᵥ x) p
      = ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V p.1)) * x p := by
  classical
  rw [SimpleGraph.degMatrix, Matrix.mulVec_diagonal, degree_multi]
  push_cast [Nat.cast_sub (card_part_le p.1)]
  ring

/-- **The Laplacian's row**, from which everything below is read off. -/
theorem lapMatrix_mulVec_multi (x : (Σ i, V i) → ℝ) (p : Σ i, V i) :
    ((completeMultipartiteGraph V).lapMatrix ℝ *ᵥ x) p
      = ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V p.1)) * x p
          - (∑ q, x q) + partTotal x p.1 := by
  rw [SimpleGraph.lapMatrix, Matrix.sub_mulVec, Pi.sub_apply, degMatrix_mulVec_multi,
    adjMatrix_mulVec_multi]
  ring

/-! ## 2. Vectors that depend only on the part: the quotient action -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem sum_card_part :
    ∑ i, (Fintype.card (V i) : ℝ) = (Fintype.card (Σ i, V i) : ℝ) := by
  rw [Fintype.card_sigma, Nat.cast_sum]

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem partTotal_comp_fst (f : ι → ℝ) (i : ι) :
    partTotal (fun q : Σ i, V i => f q.1) i = (Fintype.card (V i) : ℝ) * f i := by
  simp only [partTotal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem sum_comp_fst (f : ι → ℝ) :
    ∑ q : Σ i, V i, f q.1 = ∑ i, (Fintype.card (V i) : ℝ) * f i := by
  rw [← sum_partTotal]
  exact Finset.sum_congr rfl fun i _ => partTotal_comp_fst f i

/-- **On part-dependent vectors the Laplacian is the quotient matrix** `N·f − ∑ᵢ nᵢ fᵢ`, with no
quotient construction anywhere. -/
theorem lapMatrix_mulVec_comp_fst (f : ι → ℝ) (p : Σ i, V i) :
    ((completeMultipartiteGraph V).lapMatrix ℝ *ᵥ (fun q : Σ i, V i => f q.1)) p
      = (Fintype.card (Σ i, V i) : ℝ) * f p.1 - ∑ i, (Fintype.card (V i) : ℝ) * f i := by
  rw [lapMatrix_mulVec_multi, sum_comp_fst, partTotal_comp_fst]
  ring

theorem lapMatrix_mulVec_multi_const (c : ℝ) :
    (completeMultipartiteGraph V).lapMatrix ℝ *ᵥ (fun _ : Σ i, V i => c) = 0 := by
  funext p
  have h := lapMatrix_mulVec_comp_fst (fun _ : ι => c) p
  rw [← Finset.sum_mul, sum_card_part] at h
  simpa using h

theorem lapMatrix_mulVec_comp_fst_of_sum_eq_zero {f : ι → ℝ}
    (hf : ∑ i, (Fintype.card (V i) : ℝ) * f i = 0) :
    (completeMultipartiteGraph V).lapMatrix ℝ *ᵥ (fun q : Σ i, V i => f q.1)
      = (Fintype.card (Σ i, V i) : ℝ) • (fun q : Σ i, V i => f q.1) := by
  funext p
  rw [lapMatrix_mulVec_comp_fst, hf]
  simp

/-! ## 3. The vectors supported in one part -/

/-- **Eigenvalue `N − nᵢ`** on the vectors supported in part `i` whose part total vanishes. -/
theorem lapMatrix_mulVec_multi_of_supported {i : ι} {x : (Σ i, V i) → ℝ}
    (hsupp : ∀ q : Σ i, V i, q.1 ≠ i → x q = 0) (hzero : partTotal x i = 0) :
    (completeMultipartiteGraph V).lapMatrix ℝ *ᵥ x
      = ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) • x := by
  have hS : ∑ q, x q = 0 := by
    rw [← sum_partTotal]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = i
    · rw [hj]; exact hzero
    · exact Finset.sum_eq_zero fun a _ => hsupp ⟨j, a⟩ hj
  funext p
  rw [lapMatrix_mulVec_multi, hS]
  by_cases hp : p.1 = i
  · rw [hp, hzero]
    simp
  · have hxp : x p = 0 := hsupp p hp
    have hPp : partTotal x p.1 = 0 := Finset.sum_eq_zero fun a _ => hsupp ⟨p.1, a⟩ hp
    simp only [Pi.smul_apply, smul_eq_mul, hxp, hPp]
    ring

theorem lapMatrix_mulVec_multi_of_part_const {x : (Σ i, V i) → ℝ}
    (hpc : ∀ p : Σ i, V i, partTotal x p.1 = (Fintype.card (V p.1) : ℝ) * x p)
    (hS : ∑ q, x q = 0) :
    (completeMultipartiteGraph V).lapMatrix ℝ *ᵥ x
      = (Fintype.card (Σ i, V i) : ℝ) • x := by
  funext p
  rw [lapMatrix_mulVec_multi, hS, hpc p]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ## 4. And every eigenvalue is one of those, with the sizes that permit it -/

/-- **AND EVERY EIGENVALUE IS ONE OF THOSE, SHARPLY.** No hypothesis and no diagonalisation: the
within-part difference trick forces each part constant — a singleton part vacuously, so the third
disjunct only needs parts of size at least two — and then the vector itself. At `μ = N` the total
sum vanishes, which one non-empty part cannot manage, so two parts are non-empty there. -/
theorem eigenvalue_lapMatrix_unbal {μ : ℝ} {x : (Σ i, V i) → ℝ} (hx0 : x ≠ 0)
    (hx : (completeMultipartiteGraph V).lapMatrix ℝ *ᵥ x = μ • x) :
    μ = 0
      ∨ (μ = (Fintype.card (Σ i, V i) : ℝ)
          ∧ ∃ i j : ι, i ≠ j ∧ Nonempty (V i) ∧ Nonempty (V j))
      ∨ ∃ i : ι, 1 < Fintype.card (V i)
          ∧ μ = (Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i) := by
  classical
  set N : ℝ := (Fintype.card (Σ i, V i) : ℝ) with hN
  have hrow : ∀ p : Σ i, V i,
      (N - (Fintype.card (V p.1) : ℝ)) * x p - (∑ q, x q) + partTotal x p.1 = μ * x p := by
    intro p
    have hv := congrFun hx p
    rw [lapMatrix_mulVec_multi] at hv
    simpa [hN] using hv
  by_cases hex : ∃ i : ι, 1 < Fintype.card (V i) ∧ μ = N - (Fintype.card (V i) : ℝ)
  · exact Or.inr (Or.inr hex)
  simp only [not_exists, not_and] at hex
  -- every part is constant: a part with two vertices by the cancellation below, a singleton
  -- part because there is nothing to compare
  have hconst : ∀ (i : ι) (a b : V i), x ⟨i, a⟩ = x ⟨i, b⟩ := by
    intro i a b
    by_cases hab : a = b
    · rw [hab]
    have hcard : 1 < Fintype.card (V i) :=
      Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨a, b, hab⟩⟩
    have h1 := hrow ⟨i, a⟩
    have h2 := hrow ⟨i, b⟩
    have hdiff : (N - (Fintype.card (V i) : ℝ) - μ) * (x ⟨i, a⟩ - x ⟨i, b⟩) = 0 := by
      simp only at h1 h2
      ring_nf at h1 h2 ⊢
      linarith [h1, h2]
    have hne : (N - (Fintype.card (V i) : ℝ) - μ) ≠ 0 := fun h => hex i hcard (by linarith)
    have := (mul_eq_zero.mp hdiff).resolve_left hne
    linarith
  -- so the part sums are the part sizes times the value
  have hpc : ∀ p : Σ i, V i, partTotal x p.1 = (Fintype.card (V p.1) : ℝ) * x p := by
    intro p
    rw [partTotal, Finset.sum_congr rfl fun a _ => hconst p.1 a p.2, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hkey : ∀ p : Σ i, V i, (N - μ) * x p = ∑ q, x q := by
    intro p
    have h1 := hrow p
    rw [hpc p] at h1
    linarith [h1]
  obtain ⟨p, hp⟩ : ∃ p : Σ i, V i, x p ≠ 0 := by
    by_contra hall
    exact hx0 (funext fun q => by simpa using not_not.mp (not_exists.mp hall q))
  by_cases hμN : μ = N
  · -- at `μ = N` the total sum vanishes, and a single non-empty part cannot manage that
    refine Or.inr (Or.inl ⟨hμN, ?_⟩)
    by_contra hcon
    have hempty : ∀ j : ι, j ≠ p.1 → IsEmpty (V j) := by
      intro j hj
      by_contra hj2
      rw [not_isEmpty_iff] at hj2
      exact hcon ⟨j, p.1, hj, hj2, ⟨p.2⟩⟩
    have hsingle : ∑ j, partTotal x j = partTotal x p.1 := by
      refine Finset.sum_eq_single_of_mem p.1 (Finset.mem_univ _) ?_
      intro j _ hj
      haveI := hempty j hj
      simp [partTotal]
    have hS : ∑ q, x q = (Fintype.card (V p.1) : ℝ) * x p := by
      rw [← sum_partTotal, hsingle, hpc p]
    have hS0 : ∑ q, x q = 0 := by
      have h1 := hkey p
      rw [hμN] at h1
      simpa using h1.symm
    rw [hS] at hS0
    rcases mul_eq_zero.mp hS0 with h | h
    · have hpos : 0 < Fintype.card (V p.1) := Fintype.card_pos_iff.mpr ⟨p.2⟩
      have hzero : Fintype.card (V p.1) = 0 := Nat.cast_eq_zero.mp h
      omega
    · exact hp h
  · left
    have hNμ : (N - μ) ≠ 0 := fun h => hμN (by linarith)
    have hcc : ∀ q : Σ i, V i, x q = x p := by
      intro q
      have h1 := hkey p
      have h2 := hkey q
      have : (N - μ) * x q = (N - μ) * x p := by linarith
      exact mul_left_cancel₀ hNμ this
    have hSc : ∑ q, x q = N * x p := by
      rw [Finset.sum_congr rfl fun q _ => hcc q, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hN]
    have h1 := hkey p
    rw [hSc] at h1
    have hμ0 : μ * x p = 0 := by linarith
    exact (mul_eq_zero.mp hμ0).resolve_right hp

/-! ## 5. Each of the three values is attained -/

theorem exists_eigenvector_multi_zero (hne : Nonempty (Σ i, V i)) :
    ∃ x : (Σ i, V i) → ℝ, x ≠ 0 ∧
      (completeMultipartiteGraph V).lapMatrix ℝ *ᵥ x = (0 : ℝ) • x := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro h
    obtain ⟨p⟩ := hne
    have := congrFun h p
    simp at this
  · rw [lapMatrix_mulVec_multi_const]
    simp

/-- `N − nᵢ` **is** an eigenvalue as soon as part `i` has two vertices: the witness is the
difference of two of its indicators. -/
theorem exists_eigenvector_multi_part {i : ι} (h : 1 < Fintype.card (V i)) :
    ∃ x : (Σ i, V i) → ℝ, x ≠ 0 ∧
      (completeMultipartiteGraph V).lapMatrix ℝ *ᵥ x
        = ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) • x := by
  classical
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card h
  have hne : (⟨i, a⟩ : Σ i, V i) ≠ ⟨i, b⟩ := by simp [hab]
  refine ⟨fun q => (if q = (⟨i, a⟩ : Σ i, V i) then (1 : ℝ) else 0)
            - (if q = (⟨i, b⟩ : Σ i, V i) then (1 : ℝ) else 0), ?_, ?_⟩
  · intro hz
    have h1 := congrFun hz (⟨i, a⟩ : Σ i, V i)
    simp [hne] at h1
  · refine lapMatrix_mulVec_multi_of_supported (i := i) ?_ ?_
    · intro q hq
      have h1 : q ≠ (⟨i, a⟩ : Σ i, V i) := fun hh => hq (by rw [hh])
      have h2 : q ≠ (⟨i, b⟩ : Σ i, V i) := fun hh => hq (by rw [hh])
      simp [h1, h2]
    · rw [partTotal]
      simp [Sigma.mk.injEq]

/-- `N` **is** an eigenvalue as soon as two parts are non-empty: the witness is `nⱼ` on part `i`
against `−nᵢ` on part `j`, zero elsewhere. -/
theorem exists_eigenvector_multi_top {i j : ι} (hij : i ≠ j) (hi : Nonempty (V i))
    (hj : Nonempty (V j)) :
    ∃ x : (Σ i, V i) → ℝ, x ≠ 0 ∧
      (completeMultipartiteGraph V).lapMatrix ℝ *ᵥ x
        = (Fintype.card (Σ i, V i) : ℝ) • x := by
  classical
  set f : ι → ℝ := fun k => (if k = i then (Fintype.card (V j) : ℝ) else 0)
      - (if k = j then (Fintype.card (V i) : ℝ) else 0) with hf
  have hfi : f i = (Fintype.card (V j) : ℝ) := by simp [hf, hij]
  refine ⟨fun q => f q.1, ?_, lapMatrix_mulVec_comp_fst_of_sum_eq_zero ?_⟩
  · intro hz
    obtain ⟨a⟩ := hi
    have h1 := congrFun hz (⟨i, a⟩ : Σ i, V i)
    rw [hfi] at h1
    simp at h1
  · simp only [hf, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_true]
    ring

/-! ## 6. Why the signless Laplacian is not done here -/

/-- The signless Laplacian's row identity, the same computation with one sign changed. -/
theorem signlessLap_mulVec_multi (x : (Σ i, V i) → ℝ) (p : Σ i, V i) :
    (signlessLap (completeMultipartiteGraph V) *ᵥ x) p
      = ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V p.1)) * x p
          + (∑ q, x q) - partTotal x p.1 := by
  rw [signlessLap, Matrix.add_mulVec, Pi.add_apply, degMatrix_mulVec_multi,
    adjMatrix_mulVec_multi]
  ring

/-- **On the constant vector `Q` returns twice the degree**, which is not a constant unless the
parts all have the same size. -/
theorem signlessLap_mulVec_multi_one (p : Σ i, V i) :
    (signlessLap (completeMultipartiteGraph V) *ᵥ (fun _ : Σ i, V i => (1 : ℝ))) p
      = 2 * ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V p.1)) := by
  have h1 : ∑ _q : Σ i, V i, (1 : ℝ) = (Fintype.card (Σ i, V i) : ℝ) := by simp
  have h2 : partTotal (fun _ : Σ i, V i => (1 : ℝ)) p.1 = (Fintype.card (V p.1) : ℝ) := by
    simp [partTotal]
  rw [signlessLap_mulVec_multi, h1, h2]
  ring

/-- **AND SO THE BALANCED ARGUMENT'S EIGENVECTOR IS NOT ONE HERE.** As soon as two parts differ in
size, the constant vector is an eigenvector of `Q` for no scalar whatever — so the balanced
family's top eigenvalue `2(r−1)t` has no unbalanced analogue reachable this way, and this file
proves that rather than asserting it. -/
theorem not_isEigenvector_one_signlessLap {i j : ι}
    (hij : Fintype.card (V i) ≠ Fintype.card (V j)) (a : V i) (b : V j) (μ : ℝ) :
    signlessLap (completeMultipartiteGraph V) *ᵥ (fun _ : Σ i, V i => (1 : ℝ))
      ≠ μ • (fun _ : Σ i, V i => (1 : ℝ)) := by
  intro h
  have ha := congrFun h (⟨i, a⟩ : Σ i, V i)
  have hb := congrFun h (⟨j, b⟩ : Σ i, V i)
  rw [signlessLap_mulVec_multi_one] at ha hb
  simp only [Pi.smul_apply, smul_eq_mul, mul_one] at ha hb
  have hcard : (Fintype.card (V i) : ℝ) = (Fintype.card (V j) : ℝ) := by linarith
  exact hij (by exact_mod_cast hcard)

/-! ## 6. The spectrum, exactly -/

/-- **THE SPECTRUM, WITH NO HYPOTHESES AT ALL.** `μ` is an eigenvalue of the Laplacian **iff** it
is `0` and there is a vertex, or `N` and two parts are non-empty, or `N − nᵢ` for a part with two
vertices. Exhaustion above, realisation in `§5`, and the two meet exactly. -/
theorem isEigenvalue_lapMatrix_unbal_iff (μ : ℝ) :
    (∃ x : (Σ i, V i) → ℝ, x ≠ 0 ∧
        (completeMultipartiteGraph V).lapMatrix ℝ *ᵥ x = μ • x)
      ↔ (μ = 0 ∧ Nonempty (Σ i, V i))
          ∨ (μ = (Fintype.card (Σ i, V i) : ℝ)
              ∧ ∃ i j : ι, i ≠ j ∧ Nonempty (V i) ∧ Nonempty (V j))
          ∨ ∃ i : ι, 1 < Fintype.card (V i)
              ∧ μ = (Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i) := by
  constructor
  · rintro ⟨x, hx0, hx⟩
    rcases eigenvalue_lapMatrix_unbal hx0 hx with h | h | h
    · refine Or.inl ⟨h, ?_⟩
      by_contra hcon
      rw [not_nonempty_iff] at hcon
      exact hx0 (funext fun p => hcon.elim p)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (⟨rfl, h⟩ | ⟨rfl, i, j, hij, hi, hj⟩ | ⟨i, hi, rfl⟩)
    · exact exists_eigenvector_multi_zero h
    · exact exists_eigenvector_multi_top hij hi hj
    · exact exists_eigenvector_multi_part hi

/-! ## 7. A numerical check against a graph whose spectrum is known -/

/-- Two parts of sizes `1` and `2`: three vertices in all. -/
theorem card_path_example :
    Fintype.card (Σ i : Fin 2, Fin (i.1 + 1)) = 3 := by
  decide

/-- **THE WHOLE SPECTRUM OF ONE CONCRETE UNBALANCED GRAPH, AS AN IFF.** Parts of sizes `1` and
`2`: the eigenvalues of the Laplacian are exactly `0`, `1` and `3` — the known spectrum of the
path on three vertices, produced here from the general theorems with no spectral theorem in sight.
**The identification of this two-part family with that path is not formalised**; what is checked is
that the general statements, instantiated, give those three numerals and nothing else. -/
theorem path_example_spectrum (μ : ℝ) :
    (∃ x : (Σ i : Fin 2, Fin (i.1 + 1)) → ℝ, x ≠ 0 ∧
        (completeMultipartiteGraph (fun i : Fin 2 => Fin (i.1 + 1))).lapMatrix ℝ *ᵥ x = μ • x)
      ↔ μ = 0 ∨ μ = 1 ∨ μ = 3 := by
  rw [isEigenvalue_lapMatrix_unbal_iff, card_path_example]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨i, hi, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by exact_mod_cast h))
    · fin_cases i
      · simp at hi
      · norm_num at h
        exact Or.inr (Or.inl h)
  · rintro (rfl | rfl | rfl)
    · exact Or.inl ⟨rfl, ⟨⟨0, 0⟩⟩⟩
    · exact Or.inr (Or.inr ⟨1, by decide, by norm_num⟩)
    · exact Or.inr (Or.inl ⟨by norm_num, 0, 1, by decide, ⟨0⟩, ⟨0⟩⟩)

/-- **AND THE VALUE A SIZE-BLIND EXHAUSTION WOULD PERMIT IS NOT AN EIGENVALUE.** `N − n₀ = 2`
passes the list of `§4` read without its size condition; with the condition — part `0` is a
singleton — it does not, and `2` is genuinely not an eigenvalue here. This is the theorem that
makes `§4`'s size condition necessary rather than decorative. -/
theorem path_example_not_eigenvalue_two :
    ¬ ∃ x : (Σ i : Fin 2, Fin (i.1 + 1)) → ℝ, x ≠ 0 ∧
      (completeMultipartiteGraph (fun i : Fin 2 => Fin (i.1 + 1))).lapMatrix ℝ *ᵥ x
        = (2 : ℝ) • x := by
  rw [path_example_spectrum]
  norm_num

end UnbalancedMultipartite
