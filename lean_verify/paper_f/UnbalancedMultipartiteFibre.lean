import UnbalancedMultipartiteTwins

/-!
# The multiplicities of a complete multipartite graph, exactly

**TWO UNITS FENCED THIS AND THIS FILE CLOSES IT.** `UnbalancedMultipartite` fixed the eigenvalue
**set** of an arbitrary complete multipartite graph's Laplacian and said that it *says nothing
about how often each occurs*; `UnbalancedMultipartiteTwins` gave the first bound, `nᵢ − 1`, and
said it was a **lower** one that nothing here showed sharp. The multiplicity at `N − n` is
**exactly `k·(n − 1)`, where `k` is the number of parts of size `n`** — so the twin bound is sharp
precisely when the size is unique, and its deficit is a factor `k` and nothing else.

**THE EIGENSPACE, NAMED.** For `0 < n` and `n ≠ N`, `Lx = (N − n)x` **iff** `x` vanishes off the
parts of size `n` and **every** part total vanishes (`lapMatrix_mulVec_eq_size_iff`). The argument
is two summations of the row equation `(n − n_p)x_p = ∑x − T_{p.1}`: over one part it gives
`n·Tᵢ = nᵢ·∑x`, and over the parts it gives `n·∑x = N·∑x`, so `∑x = 0` because `n ≠ N`, so every
`Tᵢ = 0` because `n ≠ 0`, and the row equation then kills `x` at every vertex whose part has the
wrong size. **Both hypotheses are used and both are necessary** — see below.

**AND THEN IT IS ONE KERNEL.** `fibreForm n` sends `x` to its values **off** the size-`n` parts
paired with its part totals **on** them, and `x` is in the eigenspace iff both vanish
(`eigenspace_eq_ker_fibreForm`; the condition *every* part total vanishes needs no separate
clause, because off the fibre the vector is already zero). That map is **onto**
(`surjective_fibreForm`): given a target, put the prescribed values off the fibre and put each
prescribed total at one chosen vertex of its part — a choice that exists exactly because `n ≠ 0`.
Rank–nullity then gives the dimension, and the only counting left is that the size-`n` vertices
are the **disjoint union** of the size-`n` parts, which is `Finset.card_biUnion` over the previous
unit's `partImage` and `disjoint_partImage`.

## What is proved

**`row_eq_of_mulVec`, `card_mul_partTotal`, `sum_eq_zero_of_mulVec`** — the row equation at the
eigenvalue `N − n` and its two summations.

**`lapMatrix_mulVec_eq_size_iff`** — the characterisation above, both directions. The backward one
takes **no** hypothesis on `n` at all.

**`partTotalForm`, `partTotalForm_apply`, `fibreForm`, `fibreForm_apply`,
`mem_ker_fibreForm_iff`, `eigenspace_eq_ker_fibreForm`** — the eigenspace as the kernel of one
linear map, built from `LinearMap.pi`, `LinearMap.proj` and two `LinearMap.funLeft`s.

**`surjective_fibreForm`, `card_fibre_vertices`** — that map is onto, and the size-`n` parts hold
`k·n` vertices between them.

**`finrank_eigenspace_size`** — **THE MULTIPLICITY, EXACTLY: `k·(n − 1)`.** The estate's first
exact multiplicity on a family with a free parameter per part, and — with
`UnbalancedMultipartite`'s eigenvalue set — a complete description of this Laplacian's spectrum
**with** multiplicities at every eigenvalue of the form `N − n`.

**`finrank_eigenspace_size_of_unique`, `finrank_eigenspace_size_of_two`** — **SO THE TWIN BOUND'S
DEFICIT IS MEASURED.** At `k = 1` the dimension is `n − 1`: the twin-class bound of the previous
unit is **exact**. At `k = 2` it is `(n − 1) + (n − 1)`: `LaplacianTwoClasses`' two-class bound is
**exact**. `TwinClassNotExact.class_bound_lt_finrank` says a maximal class's bound can fail to be
sharp; on this family the failure is by the factor `k` and by nothing else.

**`finrank_eigenspace_size_pos_iff`, `finrank_pos_iff_isEigenvalue`** — **and the dimension count
and the previous unit's `iff` agree, as a theorem rather than as an observation**: the eigenspace
at `N − n` is non-trivial iff `1 < n` and some part has size `n`, which is exactly what
`UnbalancedMultipartite.isEigenvalue_lapMatrix_unbal_iff` says about that value by an argument
with no dimension in it. **Two independent routes to one criterion**, the third such pairing in
this chain.

**`finrank_eigenspace_equipartite`** — **and at equal sizes the number is the balanced chain's
own.** At `V := fun _ : Fin r => Fin t` the dimension is `rt − r`, which is
`MultipartiteEigenspace.finrank_ker_partForm`'s figure for `completeEquipartiteGraph r t` —
a **different** graph on a different vertex type, counted there by a different construction.
Nothing is transported; the two numbers are computed separately and agree.

## What is NOT here

* **NOTHING AT THE EIGENVALUE `N`.** Its eigenspace is the part-constant vectors with vanishing
  weighted sum, which needs a second `fibreForm`-shaped construction over the non-empty parts.
  **Not attempted, and no cost is offered** (`ERRATUM 246`).
* **NOTHING AT THE EIGENVALUE `0`.** Its multiplicity is the number of connected components
  (`FieldSimpleConnected.finrank_ker_lapMatrix_zero_eq_card_component`), and **this chain still
  does not prove this family connected**, which the previous unit also recorded.
* **SO THE TABLE DOES NOT YET ADD UP.** Summing the dimensions proved here over the distinct part
  sizes gives `N` minus the number of non-empty parts, and the two missing eigenvalues would
  supply the rest — **that sum is arithmetic in this sentence and is not a theorem in this file**,
  because the two pieces above are missing. `MultipartiteMultiplicity.finrank_eigenspaces_multi_add`
  is the statement this file does not yet have for the unbalanced family.
* **NO SIGNLESS LAPLACIAN.** `UnbalancedMultipartite.not_isEigenvector_one_signlessLap` still
  stands as the reason the cheap route there does not exist.
* **NO CHARACTERISTIC POLYNOMIAL** and no diagonalisation: as in the three units before this one,
  these arguments avoid both.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and
  `OS1` in its continuum sense.

**WHY BOTH HYPOTHESES ON `n` ARE NECESSARY, WITH THE WITNESSES.** At `n = 0` the eigenvalue is `N`
and the formula would read `k·(0 − 1) = 0` in `ℕ`, while `N` is a genuine eigenvalue as soon as two
parts are non-empty (`UnbalancedMultipartite.exists_eigenvector_multi_top`) — so the formula is
false there, and the proof's division by `n` is where it breaks. At `n = N` one part holds every
vertex, the graph is edgeless, `L = 0`, the eigenvalue `N − n` is `0` and its eigenspace is the
whole of `ℝ^N` of dimension `N`, against the formula's `N − 1`. Both are arithmetic, and both are
the points at which the two summations above are divided through.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the previous units' `Fintype` and
`DecidableEq` instances, plus `n ≠ 0` and `n ≠ N` on everything after the characterisation's
backward direction, `k = 1` and `k = 2` on the two sharpness statements, and `t ≠ 0` with `r ≠ 1`
on the equipartite instance — the second because `r = 1` makes the graph edgeless and `n = N`.
`partTotalForm` and `fibreForm` are `noncomputable` for the reason `partForm` is.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace UnbalancedMultipartiteFibre

open Matrix Finset SimpleGraph UnbalancedMultipartite UnbalancedMultipartiteTwins

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. The row equation at the eigenvalue `N - n` -/

theorem row_eq_of_mulVec {n : ℕ} {x : (Σ i, V i) → ℝ}
    (hx : (completeMultipartiteGraph V).lapMatrix ℝ *ᵥ x
      = ((Fintype.card (Σ i, V i) : ℝ) - n) • x) (p : Σ i, V i) :
    ((n : ℝ) - Fintype.card (V p.1)) * x p = (∑ q, x q) - partTotal x p.1 := by
  have hv := congrFun hx p
  rw [lapMatrix_mulVec_multi] at hv
  simp only [Pi.smul_apply, smul_eq_mul] at hv
  linarith [hv]

theorem card_mul_partTotal {n : ℕ} {x : (Σ i, V i) → ℝ}
    (hx : (completeMultipartiteGraph V).lapMatrix ℝ *ᵥ x
      = ((Fintype.card (Σ i, V i) : ℝ) - n) • x) (i : ι) :
    (n : ℝ) * partTotal x i = (Fintype.card (V i) : ℝ) * ∑ q, x q := by
  have hrow : ∀ a : V i, ((n : ℝ) - Fintype.card (V i)) * x ⟨i, a⟩
      = (∑ q, x q) - partTotal x i := fun a => row_eq_of_mulVec hx ⟨i, a⟩
  have hsum : ∑ a : V i, (((n : ℝ) - Fintype.card (V i)) * x ⟨i, a⟩)
      = ∑ _a : V i, ((∑ q, x q) - partTotal x i) := Finset.sum_congr rfl fun a _ => hrow a
  rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hT : ∑ a : V i, x (⟨i, a⟩ : Σ i, V i) = partTotal x i := rfl
  rw [hT] at hsum
  ring_nf at hsum ⊢
  linarith [hsum]

theorem sum_eq_zero_of_mulVec {n : ℕ} (hn : n ≠ Fintype.card (Σ i, V i))
    {x : (Σ i, V i) → ℝ}
    (hx : (completeMultipartiteGraph V).lapMatrix ℝ *ᵥ x
      = ((Fintype.card (Σ i, V i) : ℝ) - n) • x) :
    ∑ q, x q = 0 := by
  have hall : ∑ i, ((n : ℝ) * partTotal x i) = ∑ i, ((Fintype.card (V i) : ℝ) * ∑ q, x q) :=
    Finset.sum_congr rfl fun i _ => card_mul_partTotal hx i
  rw [← Finset.mul_sum, sum_partTotal, ← Finset.sum_mul, sum_card_part] at hall
  have hne : (n : ℝ) - (Fintype.card (Σ i, V i) : ℝ) ≠ 0 := by
    intro h
    exact hn (by exact_mod_cast sub_eq_zero.mp h)
  have : ((n : ℝ) - (Fintype.card (Σ i, V i) : ℝ)) * ∑ q, x q = 0 := by ring_nf; linarith [hall]
  exact (mul_eq_zero.mp this).resolve_left hne

/-! ## 2. The eigenspace at `N - n`, characterised -/

theorem lapMatrix_mulVec_eq_size_iff {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n ≠ Fintype.card (Σ i, V i)) (x : (Σ i, V i) → ℝ) :
    (completeMultipartiteGraph V).lapMatrix ℝ *ᵥ x
        = ((Fintype.card (Σ i, V i) : ℝ) - n) • x
      ↔ (∀ p : Σ i, V i, Fintype.card (V p.1) ≠ n → x p = 0)
          ∧ ∀ i : ι, partTotal x i = 0 := by
  constructor
  · intro hx
    have hS := sum_eq_zero_of_mulVec hnN hx
    have hT : ∀ i : ι, partTotal x i = 0 := by
      intro i
      have h := card_mul_partTotal hx i
      rw [hS, mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr hn0)
    refine ⟨fun p hp => ?_, hT⟩
    have h := row_eq_of_mulVec hx p
    rw [hS, hT p.1, sub_zero] at h
    have hne : ((n : ℝ) - Fintype.card (V p.1)) ≠ 0 := by
      intro hz
      exact hp (by exact_mod_cast (sub_eq_zero.mp hz).symm)
    exact (mul_eq_zero.mp h).resolve_left hne
  · rintro ⟨hsupp, hT⟩
    have hS : ∑ q, x q = 0 := by
      rw [← sum_partTotal]
      exact Finset.sum_eq_zero fun i _ => hT i
    funext p
    rw [lapMatrix_mulVec_multi, hS, hT p.1]
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hp : Fintype.card (V p.1) = n
    · rw [hp]; ring
    · rw [hsupp p hp]; ring

/-! ## 3. The same subspace as the kernel of one linear map -/

/-- Every part total at once, as a linear map. -/
noncomputable def partTotalForm : ((Σ i, V i) → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.pi fun i => ∑ a : V i, LinearMap.proj (⟨i, a⟩ : Σ i, V i)

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem partTotalForm_apply (x : (Σ i, V i) → ℝ) (i : ι) :
    partTotalForm x i = partTotal x i := by
  simp [partTotalForm, partTotal]

/-- The values off the parts of size `n`, and the part totals on those parts. -/
noncomputable def fibreForm (n : ℕ) :
    ((Σ i, V i) → ℝ) →ₗ[ℝ]
      (({p : Σ i, V i // Fintype.card (V p.1) ≠ n} → ℝ)
        × ({i : ι // Fintype.card (V i) = n} → ℝ)) :=
  (LinearMap.funLeft ℝ ℝ (Subtype.val : {p : Σ i, V i // Fintype.card (V p.1) ≠ n} → Σ i, V i)).prod
    ((LinearMap.funLeft ℝ ℝ (Subtype.val : {i : ι // Fintype.card (V i) = n} → ι)).comp
      partTotalForm)

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem fibreForm_apply (n : ℕ) (x : (Σ i, V i) → ℝ) :
    fibreForm (V := V) n x = (fun q => x q.1, fun i => partTotal x i.1) := by
  have h1 : (fibreForm (V := V) n x).1 = fun q => x q.1 := rfl
  have h2 : (fibreForm (V := V) n x).2 = fun i => partTotal x i.1 := by
    funext i
    exact partTotalForm_apply x i.1
  exact Prod.ext h1 h2

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem mem_ker_fibreForm_iff {n : ℕ} (x : (Σ i, V i) → ℝ) :
    x ∈ LinearMap.ker (fibreForm (V := V) n)
      ↔ (∀ p : Σ i, V i, Fintype.card (V p.1) ≠ n → x p = 0)
          ∧ ∀ i : ι, partTotal x i = 0 := by
  rw [LinearMap.mem_ker, fibreForm_apply, Prod.mk_eq_zero]
  simp only [funext_iff, Pi.zero_apply]
  constructor
  · rintro ⟨h1, h2⟩
    have hsupp : ∀ p : Σ i, V i, Fintype.card (V p.1) ≠ n → x p = 0 := fun p hp => h1 ⟨p, hp⟩
    refine ⟨hsupp, fun i => ?_⟩
    by_cases hi : Fintype.card (V i) = n
    · exact h2 ⟨i, hi⟩
    · exact Finset.sum_eq_zero fun a _ => hsupp ⟨i, a⟩ hi
  · rintro ⟨hsupp, hT⟩
    exact ⟨fun q => hsupp q.1 q.2, fun i => hT i.1⟩

theorem eigenspace_eq_ker_fibreForm {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n ≠ Fintype.card (Σ i, V i)) :
    LinearMap.ker (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ)
        - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id)
      = LinearMap.ker (fibreForm (V := V) n) := by
  refine Submodule.ext fun x => ?_
  rw [FieldCycleRotation.mem_eigenspace_iff_mulVec, mem_ker_fibreForm_iff]
  exact lapMatrix_mulVec_eq_size_iff hn0 hnN x

/-! ## 4. That map is onto, so rank-nullity applies -/

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem surjective_fibreForm {n : ℕ} (hn0 : n ≠ 0) :
    Function.Surjective (fibreForm (V := V) n) := by
  classical
  rintro ⟨u, c⟩
  have hne : ∀ i : {i : ι // Fintype.card (V i) = n}, Nonempty (V i.1) := fun i =>
    Fintype.card_pos_iff.mp (by rw [i.2]; omega)
  refine ⟨fun p => if h : Fintype.card (V p.1) = n
      then (if p.2 = (hne ⟨p.1, h⟩).some then c ⟨p.1, h⟩ else 0)
      else u ⟨p, h⟩, ?_⟩
  rw [fibreForm_apply]
  refine Prod.ext ?_ ?_
  · funext q
    exact dif_neg q.2
  · funext i
    simp only [partTotal]
    have hcongr : ∀ a : V i.1, (if h : Fintype.card (V i.1) = n
        then (if a = (hne ⟨i.1, h⟩).some then c ⟨i.1, h⟩ else 0)
        else u ⟨⟨i.1, a⟩, h⟩) = (if a = (hne i).some then c i else 0) := by
      intro a
      rw [dif_pos i.2]
    rw [Finset.sum_congr rfl fun a _ => hcongr a, Finset.sum_ite_eq' Finset.univ]
    simp

/-! ## 5. Counting the vertices in the parts of one size -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem card_fibre_vertices (n : ℕ) :
    Fintype.card {p : Σ i, V i // Fintype.card (V p.1) = n}
      = Fintype.card {i : ι // Fintype.card (V i) = n} * n := by
  classical
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have hset : (Finset.univ.filter fun p : Σ i, V i => Fintype.card (V p.1) = n)
      = (Finset.univ.filter fun i : ι => Fintype.card (V i) = n).biUnion (partImage V) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro hp
      exact ⟨p.1, hp, mem_partImage p.2⟩
    · rintro ⟨i, hi, hmem⟩
      rw [fst_eq_of_mem_partImage hmem]
      exact hi
  rw [hset, Finset.card_biUnion fun i _ j _ hij => disjoint_partImage hij]
  have hcongr : ∀ i ∈ Finset.univ.filter fun i : ι => Fintype.card (V i) = n,
      (partImage V i).card = n := by
    intro i hi
    rw [card_partImage]
    exact (Finset.mem_filter.mp hi).2
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul]

/-! ## 6. So the multiplicity is exactly the number of parts of that size, times `n - 1` -/

theorem finrank_eigenspace_size {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n ≠ Fintype.card (Σ i, V i)) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ)
          - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id))
      = Fintype.card {i : ι // Fintype.card (V i) = n} * (n - 1) := by
  classical
  rw [eigenspace_eq_ker_fibreForm hn0 hnN]
  have hrn := LinearMap.finrank_range_add_finrank_ker (fibreForm (V := V) n)
  rw [LinearMap.range_eq_top.mpr (surjective_fibreForm hn0), finrank_top,
    Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at hrn
  have hA : Fintype.card {p : Σ i, V i // Fintype.card (V p.1) = n}
      ≤ Fintype.card (Σ i, V i) := Fintype.card_subtype_le _
  have hQ : Fintype.card {p : Σ i, V i // Fintype.card (V p.1) ≠ n}
      = Fintype.card (Σ i, V i) - Fintype.card {p : Σ i, V i // Fintype.card (V p.1) = n} :=
    Fintype.card_subtype_compl _
  have hAk := card_fibre_vertices (V := V) n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.mul_succ] at hAk
  simp only [Nat.add_sub_cancel]
  omega

/-! ## 7. So the twin bound's deficit is exactly the number of parts of that size -/

theorem finrank_eigenspace_size_of_unique {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n ≠ Fintype.card (Σ i, V i))
    (huniq : Fintype.card {i : ι // Fintype.card (V i) = n} = 1) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ)
          - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id))
      = n - 1 := by
  rw [finrank_eigenspace_size hn0 hnN, huniq, one_mul]

theorem finrank_eigenspace_size_of_two {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n ≠ Fintype.card (Σ i, V i))
    (htwo : Fintype.card {i : ι // Fintype.card (V i) = n} = 2) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ)
          - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id))
      = (n - 1) + (n - 1) := by
  rw [finrank_eigenspace_size hn0 hnN, htwo]
  omega

theorem finrank_eigenspace_size_pos_iff {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n ≠ Fintype.card (Σ i, V i)) :
    0 < Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ)
          - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id))
      ↔ 1 < n ∧ ∃ i : ι, Fintype.card (V i) = n := by
  rw [finrank_eigenspace_size hn0 hnN]
  constructor
  · intro h
    have hk : 0 < Fintype.card {i : ι // Fintype.card (V i) = n} := by
      rcases Nat.eq_zero_or_pos (Fintype.card {i : ι // Fintype.card (V i) = n}) with h0 | h0
      · rw [h0, zero_mul] at h; omega
      · exact h0
    have hn : 0 < n - 1 := by
      rcases Nat.eq_zero_or_pos (n - 1) with h0 | h0
      · rw [h0, mul_zero] at h; omega
      · exact h0
    obtain ⟨i, hi⟩ := Fintype.card_pos_iff.mp hk
    exact ⟨by omega, ⟨i, hi⟩⟩
  · rintro ⟨hn, i, hi⟩
    have hk : 0 < Fintype.card {i : ι // Fintype.card (V i) = n} :=
      Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
    exact Nat.mul_pos hk (by omega)

/-! ## 8. And at equal part sizes it agrees with the balanced chain's own count -/

theorem finrank_eigenspace_equipartite {r t : ℕ} (ht : t ≠ 0) (hr : r ≠ 1) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((completeMultipartiteGraph (fun _ : Fin r => Fin t)).lapMatrix ℝ)
          - ((Fintype.card (Σ _ : Fin r, Fin t) : ℝ) - t) • LinearMap.id))
      = r * t - r := by
  have hcard : Fintype.card (Σ _ : Fin r, Fin t) = r * t := by
    simp [Fintype.card_sigma]
  have hk : Fintype.card {i : Fin r // Fintype.card (Fin t) = t} = r := by
    simp
  have hnN : t ≠ Fintype.card (Σ _ : Fin r, Fin t) := by
    rw [hcard]
    rcases Nat.eq_zero_or_pos r with rfl | hpos
    · simpa using ht
    · have h2 : 2 ≤ r := by omega
      intro hz
      have h2t : 2 * t ≤ r * t := Nat.mul_le_mul_right t h2
      omega
  rw [finrank_eigenspace_size (V := fun _ : Fin r => Fin t) ht hnN, hk]
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  simp [Nat.mul_succ]

/-! ## 9. The dimension count and the previous unit's `iff` agree, as a theorem -/

theorem finrank_pos_iff_isEigenvalue {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n ≠ Fintype.card (Σ i, V i)) :
    0 < Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ)
          - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id))
      ↔ ∃ x : (Σ i, V i) → ℝ, x ≠ 0 ∧
          (completeMultipartiteGraph V).lapMatrix ℝ *ᵥ x
            = ((Fintype.card (Σ i, V i) : ℝ) - n) • x := by
  rw [finrank_eigenspace_size_pos_iff hn0 hnN, isEigenvalue_lapMatrix_unbal_iff]
  constructor
  · rintro ⟨hn, i, hi⟩
    exact Or.inr (Or.inr ⟨i, by omega, by rw [hi]⟩)
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨i, hcard, h⟩)
    · have hc : (n : ℝ) = (Fintype.card (Σ i, V i) : ℝ) := by linarith [h]
      exact absurd (by exact_mod_cast hc : n = Fintype.card (Σ i, V i)) hnN
    · have hc : (n : ℝ) = 0 := by linarith [h]
      exact absurd (by exact_mod_cast hc : n = 0) hn0
    · have hni : Fintype.card (V i) = n := by
        have : ((Fintype.card (V i) : ℝ)) = (n : ℝ) := by linarith [h]
        exact_mod_cast this
      exact ⟨by omega, ⟨i, hni⟩⟩

end UnbalancedMultipartiteFibre
