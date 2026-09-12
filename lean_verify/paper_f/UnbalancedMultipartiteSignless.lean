import MultipartiteSimpleSpectrum

/-!
# The signless Laplacian on the unbalanced family: the part eigenvalues are shared

**FOUR UNITS FENCED `Q` ON THIS FAMILY AND THIS OPENS IT BY A THIRD.** `UnbalancedMultipartite`
proved the fence rather than asserting it — `not_isEigenvector_one_signlessLap`: once two parts
differ in size the constant vector is a `Q`-eigenvector for **no** scalar, so the balanced family's
top eigenvalue has no unbalanced analogue by the balanced route. That is still true, and it is not
the whole story: **the vectors supported in one part with vanishing part total are eigenvectors of
`Q` as well as of `L`, at the same value `N − nᵢ`** — because for such a vector the adjacency row
contributes `∑x − Tᵢ = 0` and `Q = D + A` acts exactly as `D − A` does.

**AND THAT IS AN EIGENVALUE OF `Q` ON A GRAPH THIS ESTATE COULD NOT REACH.** The standing
`UNLOCK_WATCHLIST` item on the signless frontier asks for *any eigenvalue of `Q` at a graph that is
neither a cycle, a torus, nor two-colourable with a known Laplacian spectrum*, and
`CompleteSignlessSpectrum` narrowed it by the complete graph. The complete multipartite family with
three or more non-empty parts is **not two-colourable** (`not_colorable_two_unbal`, proved here),
is not a cycle, and is not a torus — and with any part of two or more vertices it now has a
computed `Q`-eigenvalue, with a multiplicity bounded below by the same count the Laplacian has.

## What is proved

**`signlessLap_mulVec_multi_of_supported`** — `Q x = (N − nᵢ)·x` for `x` supported in part `i` with
vanishing part total, from the previous chain's signless row identity.

**`signlessLap_mulVec_eq_size`** — the same for `x` supported on **all** the parts of one size with
every part total zero, which is the whole of `L`'s eigenspace there
(`UnbalancedMultipartiteFibre.lapMatrix_mulVec_eq_size_iff`).

**`eigenspace_size_le_signless`, `finrank_signless_eigenspace_size`** — **so `L`'s eigenspace at
`N − n` sits inside `Q`'s**, and `Q`'s multiplicity there is at least `kₙ(n − 1)`, the number the
Laplacian's is exactly.

**`exists_signless_eigenvector_part`** — hence the value is attained whenever a part has two
vertices, by a dimension count rather than by exhibiting a vector twice.

**`not_colorable_two_unbal`** — three non-empty parts give three pairwise adjacent vertices, so the
graph is not two-colourable. The proof is the balanced chain's, transposed to the sigma type.

**`card_diamond`, `not_colorable_two_diamond`, `exists_signless_eigenvector_diamond`** — the
smallest witness: parts of sizes `1`, `1`, `2`, four vertices, not two-colourable, and `2` is an
eigenvalue of `D + A`. **The classical name for that graph is `K₄` minus an edge**, and no
isomorphism to any other description is formalised, as everywhere in this chain.

## What is NOT here

* **`Q`'S SPECTRUM IS STILL NOT COMPLETE, AND THE MISSING PART IS NAMEABLE.** On vectors that
  depend only on the part, `Q` acts as `f ↦ (N − 2nₚ)fₚ + ∑ₖ nₖfₖ`, and an eigenvector needs
  `fₚ = −S/(N − 2nₚ − μ)`, so the remaining eigenvalues are the roots of
  `∑ₖ nₖ/(N − 2nₖ − μ) = −1`. **That is a secular equation, not a formula**, and nothing here
  solves it; at equal sizes it degenerates to the balanced family's `2(N − n)`, which is the case
  the constant vector covers and which `not_isEigenvector_one_signlessLap` says is the only case it
  covers. Not attempted (`ERRATUM 246`), and naming the equation is not a claim that solving it is
  short (`ERRATUM 194`).

⚠ **THE COMPUTATION IN THAT CLAUSE IS A THEOREM AS OF 2026-09-12 (entry 155), AND THE PARAGRAPH IS
KEPT AS WRITTEN** (`ERRATUM 94`). `UnbalancedMultipartiteSecular.secularMap` is the map the clause
writes out in prose, and the reduction is an **equality**: `Q`'s eigenspace at any `μ` splits as the
part-total-free half plus the kernel of that `r × r` map
(`finrank_signless_eigenspace_split`, `map_partTotalForm_eq`). **The clause's last sentence still
stands**: nothing there or here solves the secular equation, and no closed form for that kernel's
dimension in terms of the part sizes is proved. What changed is that it is now a finite linear
algebra question in `r` unknowns rather than a sentence about `N` of them.

* **NO UPPER BOUND ON `Q`'S MULTIPLICITY** at `N − n`. `L`'s is exact; `Q`'s eigenspace **contains**
  it and is not shown equal, which would need `Q`'s own characterisation.

⚠ **CLOSED 2026-09-12 (entry 155), AND THE PARAGRAPH IS KEPT AS WRITTEN** (`ERRATUM 94`).
`UnbalancedMultipartiteSecular.finrank_signless_size_le` bounds the multiplicity by
`kₙ(n − 1) + r`, and `finrank_signless_size_eq` gives the exact value. **The paragraph priced it
correctly** — it does need `Q`'s own characterisation, and that is what the later file's §2–§4
supply. `finrank_signless_eigenspace_diamond` then counts the witness below: multiplicity exactly
`2`, not merely `≥ 1`.
* **NO CHARACTERISTIC POLYNOMIAL FOR `Q`**, which needs the spectrum.
* **NOTHING AT AN EMPTY PART OR AT ONE PART**, inherited from the multiplicity table.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and
  `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances; `n ≠ 0` and `n ≠ N` on the eigenspace statements, as in the file they quote;
`1 < Fintype.card (V i)` on the realisation; `∀ i, Nonempty (V i)` with `3 ≤ Fintype.card ι` on the
colouring. **No mass, no propagator, and no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace UnbalancedMultipartiteSignless

open Matrix Finset SimpleGraph LaplacianSignless
open UnbalancedMultipartite UnbalancedMultipartiteFibre UnbalancedMultipartiteTable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. The part-supported vectors are `Q`-eigenvectors too, at the same eigenvalue -/

theorem signlessLap_mulVec_multi_of_supported {i : ι} {x : (Σ i, V i) → ℝ}
    (hsupp : ∀ q : Σ i, V i, q.1 ≠ i → x q = 0) (hzero : partTotal x i = 0) :
    signlessLap (completeMultipartiteGraph V) *ᵥ x
      = ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) • x := by
  have hS : ∑ q, x q = 0 := by
    rw [← sum_partTotal]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = i
    · rw [hj]; exact hzero
    · exact Finset.sum_eq_zero fun a _ => hsupp ⟨j, a⟩ hj
  funext p
  rw [signlessLap_mulVec_multi, hS]
  by_cases hp : p.1 = i
  · rw [hp, hzero]
    simp
  · have hxp : x p = 0 := hsupp p hp
    have hPp : partTotal x p.1 = 0 := Finset.sum_eq_zero fun a _ => hsupp ⟨p.1, a⟩ hp
    simp only [Pi.smul_apply, smul_eq_mul, hxp, hPp]
    ring

/-! ## 2. The whole size-`n` eigenspace of `L` is one of `Q` too -/

theorem signlessLap_mulVec_eq_size {n : ℕ} {x : (Σ i, V i) → ℝ}
    (hsupp : ∀ p : Σ i, V i, Fintype.card (V p.1) ≠ n → x p = 0)
    (hT : ∀ i : ι, partTotal x i = 0) :
    signlessLap (completeMultipartiteGraph V) *ᵥ x
      = ((Fintype.card (Σ i, V i) : ℝ) - n) • x := by
  have hS : ∑ q, x q = 0 := by
    rw [← sum_partTotal]
    exact Finset.sum_eq_zero fun i _ => hT i
  funext p
  rw [signlessLap_mulVec_multi, hS, hT p.1]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hp : Fintype.card (V p.1) = n
  · rw [hp]; ring
  · rw [hsupp p hp]; ring

theorem eigenspace_size_le_signless {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n ≠ Fintype.card (Σ i, V i)) :
    LinearMap.ker (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ)
        - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id)
      ≤ LinearMap.ker (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
        - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id) := by
  intro x hx
  rw [FieldCycleRotation.mem_eigenspace_iff_mulVec] at hx ⊢
  obtain ⟨hsupp, hT⟩ := (lapMatrix_mulVec_eq_size_iff hn0 hnN x).mp hx
  exact signlessLap_mulVec_eq_size hsupp hT

theorem finrank_signless_eigenspace_size {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n ≠ Fintype.card (Σ i, V i)) :
    Fintype.card {i : ι // Fintype.card (V i) = n} * (n - 1)
      ≤ Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
          - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id)) := by
  rw [← finrank_eigenspace_size hn0 hnN]
  exact Submodule.finrank_mono (eigenspace_size_le_signless hn0 hnN)

/-! ## 3. So the eigenvalue is attained, and the graph need not be two-colourable -/

theorem exists_signless_eigenvector_part {i : ι} (hcard : 1 < Fintype.card (V i))
    (hnN : Fintype.card (V i) ≠ Fintype.card (Σ i, V i)) :
    ∃ x : (Σ i, V i) → ℝ, x ≠ 0 ∧
      signlessLap (completeMultipartiteGraph V) *ᵥ x
        = ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) • x := by
  have hk : 1 ≤ Fintype.card {j : ι // Fintype.card (V j) = Fintype.card (V i)} :=
    Fintype.card_pos_iff.mpr ⟨⟨i, rfl⟩⟩
  have hbound := finrank_signless_eigenspace_size (V := V)
    (n := Fintype.card (V i)) (by omega) hnN
  have hpos : 0 < Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
        - ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) • LinearMap.id)) := by
    have : 1 ≤ Fintype.card {j : ι // Fintype.card (V j) = Fintype.card (V i)}
        * (Fintype.card (V i) - 1) := by
      calc 1 = 1 * 1 := by norm_num
        _ ≤ _ := Nat.mul_le_mul hk (by omega)
    omega
  haveI : Nontrivial (LinearMap.ker
      (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
        - ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) • LinearMap.id)) :=
    Module.finrank_pos_iff.mp hpos
  obtain ⟨y, hy⟩ := exists_ne (0 : LinearMap.ker
    (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
      - ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) • LinearMap.id))
  exact ⟨y.1, fun h => hy (Submodule.coe_eq_zero.mp h),
    (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mp y.2⟩

omit [DecidableEq ι] [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] in
theorem not_colorable_two_unbal (hne : ∀ i, Nonempty (V i)) (h3 : 3 ≤ Fintype.card ι) :
    ¬ (completeMultipartiteGraph V).Colorable 2 := by
  classical
  intro hcol
  obtain ⟨C⟩ := hcol
  obtain ⟨i, j, k, hij, hik, hjk⟩ : ∃ i j k : ι, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    have := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card ι)
    obtain ⟨i⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card ι)
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card ι) i
    obtain ⟨k, hk⟩ : ∃ k : ι, k ≠ i ∧ k ≠ j := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      have hsub : (Finset.univ : Finset ι) ⊆ {i, j} := by
        intro z _
        by_cases hz : z = i
        · simp [hz]
        · simp [hcon z hz]
      have := Finset.card_le_card hsub
      rw [Finset.card_univ, Finset.card_pair (Ne.symm hj)] at this
      omega
    exact ⟨i, j, k, Ne.symm hj, Ne.symm hk.1, fun h => hk.2 (by rw [← h])⟩
  have ha : (completeMultipartiteGraph V).Adj ⟨i, (hne i).some⟩ ⟨j, (hne j).some⟩ := hij
  have hb : (completeMultipartiteGraph V).Adj ⟨i, (hne i).some⟩ ⟨k, (hne k).some⟩ := hik
  have hc : (completeMultipartiteGraph V).Adj ⟨j, (hne j).some⟩ ⟨k, (hne k).some⟩ := hjk
  have h1 := C.valid ha
  have h2 := C.valid hb
  have h3' := C.valid hc
  have : (3 : ℕ) ≤ Fintype.card (Fin 2) := by
    refine Fintype.card_le_of_injective
      (fun z : Fin 3 => if z = 0 then C ⟨i, (hne i).some⟩
        else if z = 1 then C ⟨j, (hne j).some⟩ else C ⟨k, (hne k).some⟩) ?_
    intro z z' hzz
    fin_cases z <;> fin_cases z' <;> simp_all
  simp at this

/-! ## 4. A graph that is neither a cycle nor two-colourable, with an eigenvalue of `Q` -/

/-- Parts of sizes `1`, `1`, `2`: four vertices. -/
theorem card_diamond : Fintype.card (Σ i : Fin 3, Fin (i.1 / 2 + 1)) = 4 := by decide

theorem not_colorable_two_diamond :
    ¬ (completeMultipartiteGraph (fun i : Fin 3 => Fin (i.1 / 2 + 1))).Colorable 2 :=
  not_colorable_two_unbal (fun _ => ⟨0⟩) (by simp)

/-- **AN EIGENVALUE OF `Q` ON A GRAPH THAT IS NOT TWO-COLOURABLE, NOT A CYCLE AND NOT A TORUS.**
Parts of sizes `1`, `1`, `2` — four vertices, five edges — and `2` is an eigenvalue of `D + A`. -/
theorem exists_signless_eigenvector_diamond :
    ∃ x : (Σ i : Fin 3, Fin (i.1 / 2 + 1)) → ℝ, x ≠ 0 ∧
      signlessLap (completeMultipartiteGraph (fun i : Fin 3 => Fin (i.1 / 2 + 1))) *ᵥ x
        = (2 : ℝ) • x := by
  have h := exists_signless_eigenvector_part (V := fun i : Fin 3 => Fin (i.1 / 2 + 1))
    (i := 2) (by decide) (by rw [card_diamond]; decide)
  rw [card_diamond] at h
  norm_num at h
  simpa using h

end UnbalancedMultipartiteSignless
