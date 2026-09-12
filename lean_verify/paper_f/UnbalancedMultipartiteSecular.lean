import UnbalancedMultipartiteSignless

/-!
# The signless Laplacian's multiplicity on the unbalanced family, reduced to `r × r`

**THE PREVIOUS UNIT LEFT TWO THINGS OPEN AND THIS CLOSES ONE OF THEM AND FORMALISES THE OTHER.**
`UnbalancedMultipartiteSignless` proved that `Q = D + A` shares the Laplacian's eigenvalue
`N − nᵢ` on the vectors supported in one part with vanishing part total, so `Q`'s multiplicity
there is **at least** `kₙ(n − 1)`. Its own "what is NOT here" said, in two clauses, that there was
**no upper bound** and that the rest of the spectrum was a secular equation written out in prose.
**There is an upper bound now** (`finrank_signless_size_le`), and the prose computation is a
theorem: the rest of the spectrum is the kernel of an explicit `r × r` linear map, where `r` is
the number of parts, and the split is an equality, not a bound.

## The mechanism, in one sentence

Restrict the part-total map `partTotalForm : (Σ i, V i) → ℝ  ↦  ι → ℝ` to `Q`'s eigenspace at `μ`
and apply rank-nullity: **its kernel** is the part-total-free half, which is the *Laplacian's own*
eigenspace when `μ = N − n` and is zero when `μ` misses every part value; **its image** is exactly
the kernel of `secularMap μ`.

## What is proved

**`secularMap μ`** — `P ↦ ((N − 2nᵢ − μ)·Pᵢ + nᵢ·∑ⱼ Pⱼ)ᵢ`, an `r × r` map, no matrix and no
determinant. **`secularMap_partTotalForm`** — every `Q`-eigenvector's part totals lie in its
kernel; the proof is the signless row identity summed over one part.
**`exists_eigenvector_of_mem_ker_secular`** — and conversely, from any `P` in that kernel the
part-constant vector with value `Pᵢ/nᵢ` on part `i` is a `Q`-eigenvector whose part totals are `P`.
**`map_partTotalForm_eq`** — so the image is the kernel, exactly.

**`inf_ker_partTotalForm`** — a `Q`-eigenvector at `N − n` whose part totals all vanish is
supported on the parts of size `n`, which is precisely `UnbalancedMultipartiteFibre`'s `fibreForm`
kernel; **`inf_ker_partTotalForm_eq_bot`** — and at a `μ` that is no part's `N − nᵢ` there is no
such vector but zero.

**`finrank_signless_eigenspace_split`** — the multiplicity is the sum of the two halves.
**`finrank_signless_size_eq`** — hence at `μ = N − n` it is `kₙ(n − 1) + dim ker (secularMap μ)`,
**exactly**, where the first term is the number the Laplacian's multiplicity *equals*.
**`finrank_signless_size_le`** — hence `≤ kₙ(n − 1) + r`, the first upper bound this chain has on
`Q`. **`finrank_signless_eigenspace_of_ne`** — and off the part values the multiplicity **is** the
secular kernel's dimension, with `isEigenvalue_signless_iff_of_ne` the criterion stated without a
dimension count.

**`finrank_ker_secularMap_le_one`, `finrank_signless_size_le_of_no_half`** — and when **no part
has half the size** (`2nᵢ ≠ n` for every `i`) the secular kernel is at most a line, so the
multiplicity is the Laplacian's own count **or one more** and nothing else. That is the case the
previous unit's prose named: where every diagonal entry is invertible, the eigenvector is
determined by its total and the eigenvalues are the roots of one scalar equation.

**`finrank_signless_eigenspace_diamond`** — the smallest witness, counted: on `K₄` minus an edge
(parts of sizes `1`, `1`, `2`) the previous unit exhibited `2` as an eigenvalue of `Q`; **its
multiplicity is exactly `2`**, one from the Laplacian's eigenvector inside the part of size two and
one from the secular kernel, which `§9` computes to be a line. Note this is *not* a case of the
paragraph above — the singleton parts have exactly half the size `2` — so the line is computed
rather than bounded.

**WHAT THIS DOES NOT SUPERSEDE.** `UnbalancedMultipartiteSignless.finrank_signless_eigenspace_size`
bounds the same multiplicity below by `kₙ(n − 1)` **with no non-emptiness hypothesis at all**. The
equality here needs `∀ i, Nonempty (V i)`, so the two are incomparable, not nested.

## What is NOT here

* **NO CLOSED FORM FOR `dim ker (secularMap μ)`.** The reduction is exact and the object is
  explicit, but no formula in terms of the part sizes is proved — `§8` bounds it by `1` in one
  case and that is all. What the reduction buys is that the question is now linear algebra in `r`
  unknowns rather than `N`; at a concrete family it is a computation, which is what `§9` is.
  Naming the reduction is not a claim that the general dimension is short (`ERRATUM 194`).

⚠ **THE `§8` CASE IS NOW EXACT, NOT A BOUND, AS OF 2026-09-12 (entry 157)** (`ERRATUM 94`).
`UnbalancedMultipartiteSecularEquation.finrank_ker_secularMap_eq_one` and `ker_secularMap_eq_bot`
give `dim ker (secularMap μ) = 1` when `∑ᵢ nᵢ/(N − 2nᵢ − μ) = −1` and `0` otherwise, so under this
paragraph's own hypothesis the dimension **is** determined. **What the paragraph still gets right**:
deciding that equation is finding the roots of a polynomial of degree at most `r`, which no unit
does in general, and at a half-sized value nothing here or there applies at all.
* **THE `+ r` BOUND IS NOT SHARP, AND THIS FILE'S OWN WITNESS SHOWS IT.** At the diamond it reads
  `1 + 3 = 4` and the true multiplicity is `2`. The sharp statement is the split, not the bound.
* **THE OTHER HALF OF THE `≤ 1` ARGUMENT IS NOT DONE, AND ITS PRICE IS NAMEABLE.** When some part
  *does* satisfy `2nᵢ = n`, the same reading of the rows gives total zero and support inside
  `T = {i | 2nᵢ = n}`, so the kernel has dimension at most `|T| − 1` — which is `1` at the diamond
  and would make the bound sharp there. It is not proved: it needs a second rank-nullity over the
  subtype `{i // 2nᵢ ≠ n}`, of the kind `§3`–`§6` of `UnbalancedMultipartiteFibre` do for vertices.
  Naming it is not a claim that writing it is short (`ERRATUM 194`).

⚠ **CLOSED 2026-09-12 (entry 156), AND THE PARAGRAPH IS KEPT AS WRITTEN** (`ERRATUM 94`).
`UnbalancedMultipartiteSecularBound` is that second rank-nullity, over exactly the subtype named
here: `finrank_ker_secularMap_le_half` bounds the kernel by `|T| − 1`,
`finrank_signless_size_le_half` bounds the multiplicity by `kₙ(n − 1) + |T| − 1`, and
`bound_sharp_diamond` shows it **is** sharp at the diamond, as the paragraph predicted. It also
found something the paragraph did not: at `|T| = 1` the bound is `kₙ(n − 1)` **exactly**, so a
single half-sized part means `Q` gains no eigenvector over `L` at all
(`finrank_signless_size_eq_of_unique_half`). **What the paragraph above still gets right**: the
`+ r` bound of `§7` is the loose one, and the `T = ∅` case's `+ 1` is still not shown attained.
* **NO CHARACTERISTIC POLYNOMIAL FOR `Q`**, which needs the eigenvalue list, which needs the roots
  of the secular determinant. Not attempted (`ERRATUM 246`).
* **THE NON-EMPTY-PART HYPOTHESIS CANNOT SIMPLY BE DROPPED**, and the reason is sharper than a
  division by zero. If part `i` is empty then `nᵢ = 0`, so `secularMap N` annihilates the `i` row
  outright and leaves `Pᵢ` free — while every actual part total on an empty part is `0`. So at
  `μ = N` the image is strictly smaller than the kernel, and `map_partTotalForm_eq` is false
  without `hne`.
* **NOTHING OVER `ℂ`**, and nothing about `Q` at a graph outside this family.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and
  `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances; `∀ i, Nonempty (V i)` on everything that uses the sufficiency half; `n ≠ 0` and
`n ≠ N` on the statements at a part value, as in the file they quote; `∀ i, 2nᵢ ≠ n` on the
`≤ 1` half. **No mass, no propagator,
and no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace UnbalancedMultipartiteSecular

open Matrix Finset SimpleGraph LaplacianSignless
open UnbalancedMultipartite UnbalancedMultipartiteFibre UnbalancedMultipartiteTable
open UnbalancedMultipartiteSignless

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. The secular map -/

/-- **THE SECULAR MAP**: the `r × r` constraint the part totals of a `Q`-eigenvector obey,
`P ↦ ((N − 2nᵢ − μ)·Pᵢ + nᵢ·∑ⱼ Pⱼ)ᵢ`. No matrix, no determinant, and no division. -/
noncomputable def secularMap (μ : ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun P := fun i => ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ) * P i
      + (Fintype.card (V i) : ℝ) * ∑ j, P j
  map_add' P R := by
    funext i
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c P := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem secularMap_apply (μ : ℝ) (P : ι → ℝ) (i : ι) :
    secularMap (V := V) μ P i
      = ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ) * P i
        + (Fintype.card (V i) : ℝ) * ∑ j, P j := rfl

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem mem_ker_secularMap_iff (μ : ℝ) (P : ι → ℝ) :
    P ∈ LinearMap.ker (secularMap (V := V) μ)
      ↔ ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ) * P i
          + (Fintype.card (V i) : ℝ) * ∑ j, P j = 0 := by
  rw [LinearMap.mem_ker, funext_iff]
  exact forall_congr' fun i => by rw [secularMap_apply]; rfl

/-! ## 2. Necessity -/

/-- **NECESSITY**: the signless row identity, summed over one part. -/
theorem secularMap_partTotalForm {μ : ℝ} {x : (Σ i, V i) → ℝ}
    (hx : signlessLap (completeMultipartiteGraph V) *ᵥ x = μ • x) :
    secularMap (V := V) μ (partTotalForm x) = 0 := by
  funext i
  rw [secularMap_apply, Pi.zero_apply]
  simp only [partTotalForm_apply]
  rw [sum_partTotal]
  have hrow : ∀ a : V i,
      ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) * x ⟨i, a⟩
        + (∑ q, x q) - partTotal x i = μ * x ⟨i, a⟩ := by
    intro a
    have h := congrFun hx (⟨i, a⟩ : Σ i, V i)
    rw [signlessLap_mulVec_multi] at h
    simpa using h
  have hsum : ∑ a : V i, (((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) * x ⟨i, a⟩
        + (∑ q, x q) - partTotal x i) = ∑ a : V i, μ * x ⟨i, a⟩ :=
    Finset.sum_congr rfl fun a _ => hrow a
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [← partTotal] at hsum
  linear_combination hsum

/-! ## 3. Sufficiency -/

/-- **SUFFICIENCY**: from any `P` the secular map kills, the part-constant vector with value
`Pᵢ/nᵢ` on part `i` is a `Q`-eigenvector whose part totals are `P`. This is where every part is
required to be non-empty. -/
theorem exists_eigenvector_of_mem_ker_secular (hne : ∀ i, Nonempty (V i)) {μ : ℝ} {P : ι → ℝ}
    (hP : P ∈ LinearMap.ker (secularMap (V := V) μ)) :
    ∃ x : (Σ i, V i) → ℝ, signlessLap (completeMultipartiteGraph V) *ᵥ x = μ • x
      ∧ partTotalForm x = P := by
  have hcard : ∀ i, (Fintype.card (V i) : ℝ) ≠ 0 := fun i =>
    Nat.cast_ne_zero.mpr (card_part_ne_zero (V := V) hne i)
  obtain ⟨c, hPc⟩ : ∃ c : ι → ℝ, ∀ i, (Fintype.card (V i) : ℝ) * c i = P i :=
    ⟨fun i => P i / (Fintype.card (V i) : ℝ), fun i => by
      rw [mul_comm, div_mul_cancel₀ _ (hcard i)]⟩
  have hpt : ∀ i, partTotal (partLift (V := V) c) i = P i := by
    intro i
    change partTotal (fun q : Σ i, V i => c q.1) i = P i
    rw [partTotal_comp_fst]
    exact hPc i
  have hS : ∑ q, partLift (V := V) c q = ∑ j, P j := by
    rw [sum_partLift, wsum_apply]
    exact Finset.sum_congr rfl fun j _ => hPc j
  refine ⟨partLift (V := V) c, ?_, funext fun i => (partTotalForm_apply _ i).trans (hpt i)⟩
  have hsec := (mem_ker_secularMap_iff (V := V) μ P).mp hP
  funext p
  rw [signlessLap_mulVec_multi, hS, hpt p.1]
  have hs := hsec p.1
  rw [← hPc p.1] at hs
  have hkey : (Fintype.card (V p.1) : ℝ)
      * (((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V p.1) - μ) * c p.1
        + ∑ j, P j) = 0 := by
    linear_combination hs
  have hz := (mul_eq_zero.mp hkey).resolve_left (hcard p.1)
  simp only [Pi.smul_apply, smul_eq_mul, partLift_apply]
  linear_combination hz + hPc p.fst

/-! ## 4. The part totals of the eigenspace are exactly the secular kernel -/

/-- **So the part totals of `Q`'s eigenspace are exactly the secular kernel.** -/
theorem map_partTotalForm_eq (hne : ∀ i, Nonempty (V i)) (μ : ℝ) :
    Submodule.map (partTotalForm (V := V))
        (LinearMap.ker (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
          - μ • LinearMap.id))
      = LinearMap.ker (secularMap (V := V) μ) := by
  refine le_antisymm ?_ ?_
  · rintro P ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, FieldCycleRotation.mem_eigenspace_iff_mulVec] at hx
    exact LinearMap.mem_ker.mpr (secularMap_partTotalForm hx)
  · intro P hP
    obtain ⟨x, hx, hxp⟩ := exists_eigenvector_of_mem_ker_secular hne hP
    exact ⟨x, (FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).mpr hx, hxp⟩

/-! ## 5. The part-total-free half is the Laplacian's own eigenspace -/

/-- A `Q`-eigenvector at `N − n` with every part total zero is supported on the parts of size `n`
— which is exactly the Laplacian's own eigenspace there. -/
theorem inf_ker_partTotalForm (n : ℕ) :
    (LinearMap.ker (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
        - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id))
      ⊓ LinearMap.ker (partTotalForm (V := V))
      = LinearMap.ker (fibreForm (V := V) n) := by
  refine Submodule.ext fun x => ?_
  rw [Submodule.mem_inf, FieldCycleRotation.mem_eigenspace_iff_mulVec, LinearMap.mem_ker,
    mem_ker_fibreForm_iff]
  constructor
  · rintro ⟨hx, hT0⟩
    have hT : ∀ i, partTotal x i = 0 := fun i => by
      have h := congrFun hT0 i
      rwa [partTotalForm_apply] at h
    have hS : ∑ q, x q = 0 := by
      rw [← sum_partTotal]
      exact Finset.sum_eq_zero fun i _ => hT i
    refine ⟨fun p hp => ?_, hT⟩
    have h := congrFun hx p
    rw [signlessLap_mulVec_multi, hS, hT p.1] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    have hne0 : ((n : ℝ) - Fintype.card (V p.1)) ≠ 0 := fun hz =>
      hp (by exact_mod_cast (sub_eq_zero.mp hz).symm)
    have hzero : ((n : ℝ) - Fintype.card (V p.1)) * x p = 0 := by linear_combination h
    exact (mul_eq_zero.mp hzero).resolve_left hne0
  · rintro ⟨hsupp, hT⟩
    refine ⟨signlessLap_mulVec_eq_size hsupp hT, ?_⟩
    funext i
    rw [partTotalForm_apply]
    exact hT i

/-! ## 6. Rank-nullity: the multiplicity splits in two -/

/-- **THE MULTIPLICITY SPLITS.** Rank-nullity for the part-total map on the eigenspace. -/
theorem finrank_signless_eigenspace_split (hne : ∀ i, Nonempty (V i)) (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
        - μ • LinearMap.id))
      = Module.finrank ℝ ((LinearMap.ker
            (Matrix.toLin' (signlessLap (completeMultipartiteGraph V)) - μ • LinearMap.id)
          ⊓ LinearMap.ker (partTotalForm (V := V)) : Submodule ℝ ((Σ i, V i) → ℝ)))
        + Module.finrank ℝ (LinearMap.ker (secularMap (V := V) μ)) := by
  set E := LinearMap.ker (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
      - μ • LinearMap.id) with hE
  have hrn := LinearMap.finrank_range_add_finrank_ker ((partTotalForm (V := V)).domRestrict E)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, map_partTotalForm_eq hne] at hrn
  have hcomap : Submodule.comap E.subtype (LinearMap.ker (partTotalForm (V := V)))
      = Submodule.comap E.subtype (E ⊓ LinearMap.ker (partTotalForm (V := V))) := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
  rw [hcomap, (Submodule.comapSubtypeEquivOfLe
    (inf_le_left : E ⊓ LinearMap.ker (partTotalForm (V := V)) ≤ E)).finrank_eq] at hrn
  omega

/-- **THE EXACT MULTIPLICITY AT A PART VALUE**: the Laplacian's own count, plus the secular
kernel's dimension. -/
theorem finrank_signless_size_eq {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n ≠ Fintype.card (Σ i, V i)) (hne : ∀ i, Nonempty (V i)) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
        - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id))
      = Fintype.card {i : ι // Fintype.card (V i) = n} * (n - 1)
        + Module.finrank ℝ (LinearMap.ker
            (secularMap (V := V) ((Fintype.card (Σ i, V i) : ℝ) - n))) := by
  rw [finrank_signless_eigenspace_split hne, inf_ker_partTotalForm,
    ← eigenspace_eq_ker_fibreForm hn0 hnN, finrank_eigenspace_size hn0 hnN]

/-- **AND SO AN UPPER BOUND**, the first this chain has on `Q`. It is not sharp — see the diamond
in `§8`, where it reads `4` and the truth is `2`. -/
theorem finrank_signless_size_le {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n ≠ Fintype.card (Σ i, V i)) (hne : ∀ i, Nonempty (V i)) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
        - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id))
      ≤ Fintype.card {i : ι // Fintype.card (V i) = n} * (n - 1) + Fintype.card ι := by
  rw [finrank_signless_size_eq hn0 hnN hne]
  have h := Submodule.finrank_le (LinearMap.ker
    (secularMap (V := V) ((Fintype.card (Σ i, V i) : ℝ) - n)))
  rw [Module.finrank_fintype_fun_eq_card] at h
  omega

/-! ## 7. Away from the part values, `Q`'s eigenspace IS the secular kernel -/

/-- At a `μ` that is no part's `N − nᵢ`, no `Q`-eigenvector has all its part totals zero. -/
theorem inf_ker_partTotalForm_eq_bot {μ : ℝ}
    (hμ : ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) ≠ μ) :
    (LinearMap.ker (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
        - μ • LinearMap.id)) ⊓ LinearMap.ker (partTotalForm (V := V)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hxm
  rw [Submodule.mem_inf, FieldCycleRotation.mem_eigenspace_iff_mulVec, LinearMap.mem_ker] at hxm
  obtain ⟨hx, hT0⟩ := hxm
  have hT : ∀ i, partTotal x i = 0 := fun i => by
    have h := congrFun hT0 i
    rwa [partTotalForm_apply] at h
  have hS : ∑ q, x q = 0 := by
    rw [← sum_partTotal]
    exact Finset.sum_eq_zero fun i _ => hT i
  funext p
  have h := congrFun hx p
  rw [signlessLap_mulVec_multi, hS, hT p.1] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  have hne0 : ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V p.1) - μ) ≠ 0 := fun hz =>
    hμ p.1 (by linarith)
  have hzero : ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V p.1) - μ) * x p = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp hzero).resolve_left hne0

/-- **SO OFF THE PART VALUES, `Q`'S MULTIPLICITY IS THE SECULAR KERNEL'S, EXACTLY.** -/
theorem finrank_signless_eigenspace_of_ne {μ : ℝ} (hne : ∀ i, Nonempty (V i))
    (hμ : ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) ≠ μ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
        - μ • LinearMap.id))
      = Module.finrank ℝ (LinearMap.ker (secularMap (V := V) μ)) := by
  rw [finrank_signless_eigenspace_split hne, inf_ker_partTotalForm_eq_bot hμ, finrank_bot,
    zero_add]

/-- The eigenvalue criterion, without a dimension count. -/
theorem isEigenvalue_signless_iff_of_ne {μ : ℝ} (hne : ∀ i, Nonempty (V i))
    (hμ : ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) ≠ μ) :
    (∃ x : (Σ i, V i) → ℝ, x ≠ 0
        ∧ signlessLap (completeMultipartiteGraph V) *ᵥ x = μ • x)
      ↔ ∃ P : ι → ℝ, P ≠ 0 ∧ secularMap (V := V) μ P = 0 := by
  constructor
  · rintro ⟨x, hx0, hx⟩
    refine ⟨partTotalForm x, fun hP => hx0 ?_, secularMap_partTotalForm hx⟩
    have hmem : x ∈ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph V)) - μ • LinearMap.id))
        ⊓ LinearMap.ker (partTotalForm (V := V)) := by
      rw [Submodule.mem_inf, FieldCycleRotation.mem_eigenspace_iff_mulVec, LinearMap.mem_ker]
      exact ⟨hx, hP⟩
    rw [inf_ker_partTotalForm_eq_bot hμ] at hmem
    exact hmem
  · rintro ⟨P, hP0, hP⟩
    obtain ⟨x, hx, hxp⟩ := exists_eigenvector_of_mem_ker_secular hne (LinearMap.mem_ker.mpr hP)
    refine ⟨x, fun hx0 => hP0 ?_, hx⟩
    rw [← hxp, hx0, map_zero]

/-! ## 8. When no part sits at the secular map's own zero, that kernel is at most a line -/

/-- The unweighted total on the parts. -/
noncomputable def totalForm : (ι → ℝ) →ₗ[ℝ] ℝ := ∑ j, LinearMap.proj j

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem totalForm_apply (P : ι → ℝ) : totalForm (ι := ι) P = ∑ j, P j := by
  simp [totalForm]

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **THE SECULAR KERNEL IS AT MOST A LINE** once no part makes a diagonal entry vanish: a `P` in
it with total zero has every entry zero, so the total separates the kernel's points. This is the
case the previous unit's prose named — the one where the eigenvalues are the roots of
`∑ₖ nₖ/(N − 2nₖ − μ) = −1`, a scalar equation with a one-dimensional solution space where it
holds. -/
theorem finrank_ker_secularMap_le_one {μ : ℝ}
    (hT : ∀ i, ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - μ) ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (secularMap (V := V) μ)) ≤ 1 := by
  have hinj : Function.Injective
      ((totalForm (ι := ι)).domRestrict (LinearMap.ker (secularMap (V := V) μ))) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨P, hPmem⟩ hP0
    have hsum : ∑ j, P j = 0 := by
      have h := LinearMap.mem_ker.mp hP0
      rwa [LinearMap.domRestrict_apply, totalForm_apply] at h
    have hrow := (mem_ker_secularMap_iff (V := V) μ P).mp hPmem
    refine Subtype.ext (funext fun i => ?_)
    have h := hrow i
    rw [hsum, mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (hT i)
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_self] at h

/-- **SO AT A PART VALUE WITH NO PART OF HALF THAT SIZE, `Q`'S MULTIPLICITY IS THE LAPLACIAN'S OR
ONE MORE.** -/
theorem finrank_signless_size_le_of_no_half {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n ≠ Fintype.card (Σ i, V i)) (hne : ∀ i, Nonempty (V i))
    (hhalf : ∀ i, 2 * Fintype.card (V i) ≠ n) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
        - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id))
      ≤ Fintype.card {i : ι // Fintype.card (V i) = n} * (n - 1) + 1 := by
  rw [finrank_signless_size_eq hn0 hnN hne]
  have h := finrank_ker_secularMap_le_one (V := V)
    (μ := (Fintype.card (Σ i, V i) : ℝ) - n) fun i => by
      intro hz
      exact hhalf i (by exact_mod_cast (by linarith : (2 * Fintype.card (V i) : ℝ) = n))
  omega

/-! ## 9. The smallest witness, counted exactly -/

/-- The secular kernel at the diamond: the part of size two contributes nothing and the two
singletons cancel. -/
theorem mem_ker_secular_diamond (P : Fin 3 → ℝ) :
    P ∈ LinearMap.ker (secularMap (V := fun i : Fin 3 => Fin (i.1 / 2 + 1)) 2)
      ↔ P 2 = 0 ∧ P 0 + P 1 = 0 := by
  rw [mem_ker_secularMap_iff]
  rw [card_diamond]
  simp only [Fintype.card_fin, Fin.sum_univ_three]
  constructor
  · intro h
    have h0 := h 0
    have h2 := h 2
    norm_num at h0 h2
    constructor <;> linarith
  · rintro ⟨h2, h01⟩ i
    have hs : P 0 + P 1 + P 2 = 0 := by linarith
    rw [hs, mul_zero, add_zero]
    rcases eq_or_ne i 2 with rfl | hi
    · rw [h2, mul_zero]
    · have hlt : i.1 < 3 := i.isLt
      have hne2 : i.1 ≠ 2 := fun h => hi (Fin.ext h)
      have hdiv : i.1 / 2 = 0 := by omega
      rw [hdiv]
      norm_num


/-- Two independent conditions on three part totals. -/
def diaForm : (Fin 3 → ℝ) →ₗ[ℝ] ℝ × ℝ where
  toFun P := (P 2, P 0 + P 1)
  map_add' P Q := by
    simp only [Pi.add_apply, Prod.mk_add_mk, Prod.mk.injEq, true_and]
    ring
  map_smul' c P := by
    simp only [Pi.smul_apply, smul_eq_mul, Prod.smul_mk, RingHom.id_apply, Prod.mk.injEq,
      true_and]
    ring

theorem diaForm_apply (P : Fin 3 → ℝ) : diaForm P = (P 2, P 0 + P 1) := rfl

theorem surjective_diaForm : Function.Surjective diaForm := by
  rintro ⟨a, b⟩
  refine ⟨![b, 0, a], ?_⟩
  rw [diaForm_apply, show (![b, 0, a] : Fin 3 → ℝ) 2 = a from rfl,
    show (![b, 0, a] : Fin 3 → ℝ) 0 = b from rfl,
    show (![b, 0, a] : Fin 3 → ℝ) 1 = 0 from rfl, add_zero]

theorem ker_secular_diamond :
    LinearMap.ker (secularMap (V := fun i : Fin 3 => Fin (i.1 / 2 + 1)) 2)
      = LinearMap.ker diaForm := by
  refine Submodule.ext fun P => ?_
  rw [mem_ker_secular_diamond, LinearMap.mem_ker, diaForm_apply, Prod.mk_eq_zero]

/-- So it is a line. -/
theorem finrank_ker_secular_diamond :
    Module.finrank ℝ (LinearMap.ker
      (secularMap (V := fun i : Fin 3 => Fin (i.1 / 2 + 1)) 2)) = 1 := by
  rw [ker_secular_diamond]
  have hrn := LinearMap.finrank_range_add_finrank_ker diaForm
  rw [LinearMap.range_eq_top.mpr surjective_diaForm, finrank_top, Module.finrank_prod,
    Module.finrank_self, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrn
  omega

/-- **THE MULTIPLICITY, EXACTLY, ON THE SMALLEST WITNESS.** On `K₄` minus an edge the previous
unit showed `2` is an eigenvalue of `D + A`; it has multiplicity exactly `2` — one from the
Laplacian's eigenvector inside the part of size two, one from the secular kernel. Note that the
general upper bound reads `1 + 3 = 4` here, so it is not sharp; the split is. -/
theorem finrank_signless_eigenspace_diamond :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph (fun i : Fin 3 => Fin (i.1 / 2 + 1))))
      - (2 : ℝ) • LinearMap.id)) = 2 := by
  have hk : Fintype.card {i : Fin 3 // Fintype.card (Fin (i.1 / 2 + 1)) = 2} = 1 := by decide
  have hval : ((Fintype.card (Σ i : Fin 3, Fin (i.1 / 2 + 1)) : ℝ) - ((2 : ℕ) : ℝ)) = 2 := by
    rw [card_diamond]; norm_num
  have h := finrank_signless_size_eq (V := fun i : Fin 3 => Fin (i.1 / 2 + 1)) (n := 2)
    (by norm_num) (by rw [card_diamond]; norm_num) (fun _ => ⟨0⟩)
  rw [hval, hk] at h
  norm_num at h
  rw [h, finrank_ker_secular_diamond]

end UnbalancedMultipartiteSecular
