import UnbalancedMultipartiteFibre

/-!
# The complete multipartite graph's multiplicity table, and it adds up

**THE PREVIOUS UNIT NAMED THREE GAPS AND THIS FILE CLOSES ALL THREE.**
`UnbalancedMultipartiteFibre` counted the eigenspace at every `N − n` exactly and listed what was
missing: the eigenvalue `N`, the eigenvalue `0` — *which needs this family proved connected, which
this chain still has not done* — and therefore the fact that the dimensions add to `N`. Here the
family is proved connected, both remaining eigenspaces are counted, and **the dimensions add to the
vertex count**: `1 + (r − 1) + ∑ₙ kₙ(n − 1) = N`.

**THE EIGENVALUE `N` IS THE PART-CONSTANT DIRECTION.** `Lx = Nx` **iff** `x` is constant on each
part and `∑x = 0` (`lapMatrix_mulVec_eq_top_iff`) — the forward direction sums the row equation
over one part, which gives `nᵢ·∑x = 0` and so kills the total sum, after which the row equation says
`Tᵢ = nᵢxₚ` and the part is constant. That subspace is the image under the part-constant lift
`LinearMap.funLeft ℝ ℝ Sigma.fst` of the hyperplane `∑ᵢ nᵢfᵢ = 0` in `ℝ^ι`, and the lift is
injective exactly because every part has a vertex, so the dimension is **`r − 1`**.

**AND THE GRAPH IS CONNECTED, WHICH THIS CHAIN HAD NOT SHOWN.** Two vertices in different parts are
adjacent; two in the same part go through a vertex of any other part, which exists because there are
at least two parts and none is empty (`connected_multi`). The eigenvalue `0` is then simple by
`FieldSimpleConnected.finrank_ker_lapMatrix_zero_connected`, which has been in the estate since the
component count was proved and which nothing in this chain could use until now.

## What is proved

**`lapMatrix_mulVec_eq_top_iff`** — the characterisation at `N`, both directions, needing only one
non-empty part.

**`partLift`, `partLift_apply`, `injective_partLift`, `wsum`, `wsum_apply`, `sum_partLift`,
`surjective_wsum`, `finrank_ker_wsum`** — the lift, the size-weighted sum `f ↦ ∑ᵢ nᵢfᵢ`, the fact
that the lift carries the one to the other, and `r − 1` for the weighted hyperplane by
rank–nullity.

**`eigenspace_top_eq`, `finrank_eigenspace_top`** — so the eigenspace at `N` **is** that
hyperplane's image, and its dimension is **`r − 1`**.

**`connected_multi`, `finrank_eigenspace_zero`** — the graph is connected, so the eigenvalue `0`
has multiplicity **one**.

**`card_part_ne_zero`, `card_part_ne_card`, `eigenvalue_size_ne`** — no part size is `0` or the
whole vertex count, so no `N − n` is `0` or `N`: **the eigenvalues in the sum below are pairwise
distinct**, which is what makes it a sum over eigenspaces rather than an arithmetic coincidence.

**`sum_card_sub_one`, `card_index_le`, `sum_fibre_dims`** — `∑ₙ kₙ(n − 1) = N − r`, by
`Finset.sum_comp` over the fibres of `i ↦ nᵢ` and the previous unit's count at each size.

**`finrank_eigenspaces_add`** — **AND THE TABLE ADDS TO `N`.** `1 + (r − 1) + (N − r) = N`. With
`UnbalancedMultipartite`'s eigenvalue set and the previous unit's count this is a **complete
spectral description with multiplicities of an arbitrary complete multipartite graph's Laplacian**:
every eigenvalue, and how often each occurs.

## What is NOT here

* **THE SUM DOES NOT BY ITSELF PROVE EXHAUSTION, AND IS NOT CLAIMED TO.** Reading *so there is no
  room for a fourth eigenvalue* off this table needs the eigenspaces at distinct eigenvalues to be
  independent — available in this estate **pairwise**, as
  `SymmetricEigenOrthogonal.dotProduct_eq_zero_of_eigen_ne`, and **not assembled here** into a
  spanning argument. Exhaustion is proved directly by
  `UnbalancedMultipartite.eigenvalue_lapMatrix_unbal` instead, and the table is a second,
  independent computation that agrees with it rather than a second proof of it.
* **NOTHING AT AN EMPTY PART.** Every statement here takes `∀ i, Nonempty (V i)`, and it is not
  decoration: an empty part is counted by `r` and contributes no vertex, so the lift stops being
  injective and `r − 1` stops being the dimension. The honest general statement would count the
  **non-empty** parts, and this file does not state it.
* **NOTHING AT ONE PART.** `2 ≤ r` is needed for connectedness — at one part the graph is edgeless,
  and with two or more vertices it is disconnected, so the eigenvalue `0` is not simple.
* **NO CHARACTERISTIC POLYNOMIAL**, and the missing step is now nameable rather than vague: it is
  the transfer from these eigenspace dimensions to the multiset `Matrix.IsHermitian.eigenvalues`
  enumerates, which `FieldEigenMultiplicity.finrank_eigenspace_eq_card_fibre` performs for the
  **propagator** — `lapMatrix` occurs nowhere in that file — and which nothing in this estate does
  for the Laplacian. Not attempted (`ERRATUM 246`).
* **NO SIGNLESS LAPLACIAN.** `UnbalancedMultipartite.not_isEigenvector_one_signlessLap` still
  stands as the reason the cheap route there does not exist.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and
  `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances; `Nonempty (Σ i, V i)` alone on the characterisation at `N` and on the weighted sum's
surjectivity; `∀ i, Nonempty (V i)` from the lift onwards; and `2 ≤ Fintype.card ι` wherever
connectedness or the table is involved. `partLift` and `wsum` are `noncomputable` for the reason
`partForm` is.

**A NAMING NOTE** (`newnames_scan`). The lift is `partLift` here, not `lift`, and its three lemmas
follow it, for the reason `partTotal` is not `partSum`: `MultipartiteMultiplicity` owns `lift` for
the balanced family's `Prod.fst`, this one is `Sigma.fst`, and no short name in this chain collides
estate-wide.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace UnbalancedMultipartiteTable

open Matrix Finset SimpleGraph UnbalancedMultipartite UnbalancedMultipartiteFibre

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. The eigenvalue `N`: part-constant vectors with vanishing sum -/

theorem lapMatrix_mulVec_eq_top_iff (hV : Nonempty (Σ i, V i)) (x : (Σ i, V i) → ℝ) :
    (completeMultipartiteGraph V).lapMatrix ℝ *ᵥ x = (Fintype.card (Σ i, V i) : ℝ) • x
      ↔ (∀ (i : ι) (a b : V i), x ⟨i, a⟩ = x ⟨i, b⟩) ∧ ∑ q, x q = 0 := by
  constructor
  · intro hx
    have hrow : ∀ p : Σ i, V i,
        partTotal x p.1 - (Fintype.card (V p.1) : ℝ) * x p = ∑ q, x q := by
      intro p
      have hv := congrFun hx p
      rw [lapMatrix_mulVec_multi] at hv
      simp only [Pi.smul_apply, smul_eq_mul] at hv
      linarith [hv]
    have hS : ∑ q, x q = 0 := by
      obtain ⟨p⟩ := hV
      have hsum : ∑ a : V p.1, (partTotal x p.1 - (Fintype.card (V p.1) : ℝ) * x ⟨p.1, a⟩)
          = ∑ _a : V p.1, ∑ q, x q :=
        Finset.sum_congr rfl fun a _ => hrow ⟨p.1, a⟩
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
      have hT : ∑ a : V p.1, x (⟨p.1, a⟩ : Σ i, V i) = partTotal x p.1 := rfl
      rw [hT] at hsum
      have hpos : (0 : ℝ) < Fintype.card (V p.1) := by
        have : 0 < Fintype.card (V p.1) := Fintype.card_pos_iff.mpr ⟨p.2⟩
        exact_mod_cast this
      have hz : (Fintype.card (V p.1) : ℝ) * ∑ q, x q = 0 := by linarith [hsum]
      exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hpos)
    refine ⟨fun i a b => ?_, hS⟩
    have h1 := hrow ⟨i, a⟩
    have h2 := hrow ⟨i, b⟩
    rw [hS] at h1 h2
    have hpos : (0 : ℝ) < Fintype.card (V i) := by
      have : 0 < Fintype.card (V i) := Fintype.card_pos_iff.mpr ⟨a⟩
      exact_mod_cast this
    have : (Fintype.card (V i) : ℝ) * x ⟨i, a⟩ = (Fintype.card (V i) : ℝ) * x ⟨i, b⟩ := by
      simp only at h1 h2
      linarith [h1, h2]
    exact mul_left_cancel₀ (ne_of_gt hpos) this
  · rintro ⟨hconst, hS⟩
    have hpc : ∀ p : Σ i, V i, partTotal x p.1 = (Fintype.card (V p.1) : ℝ) * x p := by
      intro p
      rw [partTotal, Finset.sum_congr rfl fun a _ => hconst p.1 a p.2, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    funext p
    rw [lapMatrix_mulVec_multi, hS, hpc p]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-! ## 2. The partLift from the parts, and the part sizes as weights -/

/-- A vector on the parts, lifted to a part-constant vector on the vertices. -/
noncomputable def partLift : (ι → ℝ) →ₗ[ℝ] ((Σ i, V i) → ℝ) := LinearMap.funLeft ℝ ℝ Sigma.fst

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] in
theorem partLift_apply (f : ι → ℝ) (p : Σ i, V i) : partLift f p = f p.1 := rfl

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] in
theorem injective_partLift (hne : ∀ i, Nonempty (V i)) : Function.Injective (partLift (V := V)) :=
  LinearMap.funLeft_injective_of_surjective ℝ ℝ _ fun i => ⟨⟨i, (hne i).some⟩, rfl⟩

/-- The weighted sum on the parts: `f ↦ ∑ᵢ nᵢ fᵢ`. -/
noncomputable def wsum : (ι → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i, (Fintype.card (V i) : ℝ) • LinearMap.proj i

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem wsum_apply (f : ι → ℝ) : wsum (V := V) f = ∑ i, (Fintype.card (V i) : ℝ) * f i := by
  simp [wsum]

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem sum_partLift (f : ι → ℝ) : ∑ q, partLift (V := V) f q = wsum (V := V) f := by
  rw [wsum_apply]
  simp only [partLift_apply]
  exact sum_comp_fst f

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem surjective_wsum (hV : Nonempty (Σ i, V i)) : Function.Surjective (wsum (V := V)) := by
  classical
  obtain ⟨p⟩ := hV
  have hpos : (0 : ℝ) < Fintype.card (V p.1) := by
    have : 0 < Fintype.card (V p.1) := Fintype.card_pos_iff.mpr ⟨p.2⟩
    exact_mod_cast this
  intro c
  refine ⟨fun i => if i = p.1 then c / Fintype.card (V p.1) else 0, ?_⟩
  rw [wsum_apply]
  rw [Finset.sum_eq_single_of_mem p.1 (Finset.mem_univ _)]
  · rw [if_pos rfl]
    field_simp
  · intro j _ hj
    rw [if_neg hj, mul_zero]

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem finrank_ker_wsum (hV : Nonempty (Σ i, V i)) :
    Module.finrank ℝ (LinearMap.ker (wsum (V := V))) = Fintype.card ι - 1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (wsum (V := V))
  rw [LinearMap.range_eq_top.mpr (surjective_wsum hV), finrank_top,
    Module.finrank_self, Module.finrank_fintype_fun_eq_card] at hrn
  omega

/-! ## 3. So that eigenspace is the partLift of a hyperplane, and its dimension is `r - 1` -/

theorem eigenspace_top_eq (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) :
    LinearMap.ker (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ)
        - (Fintype.card (Σ i, V i) : ℝ) • LinearMap.id)
      = (LinearMap.ker (wsum (V := V))).map (partLift (V := V)) := by
  obtain ⟨i₀⟩ := hι
  have hV : Nonempty (Σ i, V i) := ⟨⟨i₀, (hne i₀).some⟩⟩
  refine Submodule.ext fun x => ?_
  rw [FieldCycleRotation.mem_eigenspace_iff_mulVec, lapMatrix_mulVec_eq_top_iff hV,
    Submodule.mem_map]
  constructor
  · rintro ⟨hconst, hS⟩
    refine ⟨fun i => x ⟨i, (hne i).some⟩, ?_, ?_⟩
    · rw [LinearMap.mem_ker, ← sum_partLift]
      simp only [partLift_apply]
      rw [← hS]
      exact Finset.sum_congr rfl fun q _ => (hconst q.1 (hne q.1).some q.2)
    · funext p
      exact (hconst p.1 (hne p.1).some p.2)
  · rintro ⟨f, hf, rfl⟩
    refine ⟨fun i a b => rfl, ?_⟩
    rw [sum_partLift]
    exact LinearMap.mem_ker.mp hf

theorem finrank_eigenspace_top (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ)
          - (Fintype.card (Σ i, V i) : ℝ) • LinearMap.id))
      = Fintype.card ι - 1 := by
  obtain ⟨i₀⟩ := hι
  have hV : Nonempty (Σ i, V i) := ⟨⟨i₀, (hne i₀).some⟩⟩
  rw [eigenspace_top_eq hne ⟨i₀⟩,
    ← LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective (partLift (V := V)) (injective_partLift hne)
        (LinearMap.ker (wsum (V := V))))]
  exact finrank_ker_wsum hV

/-! ## 4. The graph is connected, so the eigenvalue `0` is simple -/

omit [DecidableEq ι] [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] in
theorem connected_multi (hne : ∀ i, Nonempty (V i)) (hι : 2 ≤ Fintype.card ι) :
    (completeMultipartiteGraph V).Connected := by
  have hV : Nonempty (Σ i, V i) := by
    obtain ⟨i⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card ι)
    exact ⟨⟨i, (hne i).some⟩⟩
  rw [SimpleGraph.connected_iff]
  refine ⟨fun u v => ?_, hV⟩
  by_cases huv : u.1 = v.1
  · obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega) u.1
    have h1 : (completeMultipartiteGraph V).Adj u ⟨j, (hne j).some⟩ := hj.symm
    have h2 : (completeMultipartiteGraph V).Adj (⟨j, (hne j).some⟩ : Σ i, V i) v := by
      rw [huv] at hj
      exact hj
    exact h1.reachable.trans h2.reachable
  · have h : (completeMultipartiteGraph V).Adj u v := huv
    exact h.reachable

theorem finrank_eigenspace_zero (hne : ∀ i, Nonempty (V i)) (hι : 2 ≤ Fintype.card ι) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ)
          - (0 : ℝ) • LinearMap.id)) = 1 :=
  FieldSimpleConnected.finrank_ker_lapMatrix_zero_connected (connected_multi hne hι)

/-! ## 5. No part size is `0` or the whole vertex count -/

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem card_part_ne_zero (hne : ∀ i, Nonempty (V i)) (i : ι) : Fintype.card (V i) ≠ 0 := by
  have : 0 < Fintype.card (V i) := Fintype.card_pos_iff.mpr (hne i)
  omega

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem card_part_ne_card (hne : ∀ i, Nonempty (V i)) (hι : 2 ≤ Fintype.card ι) (i : ι) :
    Fintype.card (V i) ≠ Fintype.card (Σ i, V i) := by
  classical
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
  have hpair : ∑ k ∈ ({i, j} : Finset ι), Fintype.card (V k)
      = Fintype.card (V i) + Fintype.card (V j) :=
    Finset.sum_pair (f := fun k => Fintype.card (V k)) (Ne.symm hj)
  have hle : ∑ k ∈ ({i, j} : Finset ι), Fintype.card (V k)
      ≤ ∑ k, Fintype.card (V k) :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hN : Fintype.card (Σ i, V i) = ∑ k, Fintype.card (V k) := Fintype.card_sigma
  have hjpos : 0 < Fintype.card (V j) := Fintype.card_pos_iff.mpr (hne j)
  omega

/-! ## 6. And the dimensions add to the vertex count -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem sum_card_sub_one (hne : ∀ i, Nonempty (V i)) :
    ∑ i, (Fintype.card (V i) - 1) = Fintype.card (Σ i, V i) - Fintype.card ι := by
  have hcongr : ∀ i : ι, (Fintype.card (V i) - 1) + 1 = Fintype.card (V i) := by
    intro i
    have := Fintype.card_pos_iff.mpr (hne i)
    omega
  have h1 : ∑ i, ((Fintype.card (V i) - 1) + 1) = ∑ i, Fintype.card (V i) :=
    Finset.sum_congr rfl fun i _ => hcongr i
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h1
  have hN : Fintype.card (Σ i, V i) = ∑ i, Fintype.card (V i) := Fintype.card_sigma
  omega

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem card_index_le (hne : ∀ i, Nonempty (V i)) :
    Fintype.card ι ≤ Fintype.card (Σ i, V i) := by
  refine Fintype.card_le_of_injective (fun i => ⟨i, (hne i).some⟩) fun i j hij => ?_
  simpa using congrArg Sigma.fst hij

theorem sum_fibre_dims (hne : ∀ i, Nonempty (V i)) (hι : 2 ≤ Fintype.card ι) :
    ∑ n ∈ (Finset.univ.image fun i : ι => Fintype.card (V i)),
        Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ)
            - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id))
      = Fintype.card (Σ i, V i) - Fintype.card ι := by
  classical
  rw [← sum_card_sub_one hne, Finset.sum_comp (fun n => n - 1) fun i : ι => Fintype.card (V i)]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hn
  rw [finrank_eigenspace_size (card_part_ne_zero hne i) (card_part_ne_card hne hι i),
    Fintype.card_subtype, smul_eq_mul]

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **THE EIGENVALUES SUMMED OVER ARE DISTINCT FROM THE OTHER TWO**, so the sum above really is
over the eigenspaces of pairwise distinct eigenvalues: distinct sizes give distinct values of
`N - n`, and no such value is `0` or `N`. -/
theorem eigenvalue_size_ne (hne : ∀ i, Nonempty (V i)) (hι : 2 ≤ Fintype.card ι) (i : ι) :
    ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) ≠ 0
      ∧ ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i))
          ≠ (Fintype.card (Σ i, V i) : ℝ) := by
  constructor
  · intro h
    exact card_part_ne_card hne hι i (by exact_mod_cast (sub_eq_zero.mp h).symm)
  · intro h
    have : (Fintype.card (V i) : ℝ) = 0 := by linarith [h]
    exact card_part_ne_zero hne i (by exact_mod_cast this)

theorem finrank_eigenspaces_add (hne : ∀ i, Nonempty (V i)) (hι : 2 ≤ Fintype.card ι) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ) - (0 : ℝ) • LinearMap.id))
      + Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ)
          - (Fintype.card (Σ i, V i) : ℝ) • LinearMap.id))
      + ∑ n ∈ (Finset.univ.image fun i : ι => Fintype.card (V i)),
          Module.finrank ℝ (LinearMap.ker
            (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ)
              - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id))
      = Fintype.card (Σ i, V i) := by
  obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card ι)
  rw [finrank_eigenspace_zero hne hι, finrank_eigenspace_top hne ⟨i₀⟩,
    sum_fibre_dims hne hι]
  have := card_index_le hne
  omega

end UnbalancedMultipartiteTable
