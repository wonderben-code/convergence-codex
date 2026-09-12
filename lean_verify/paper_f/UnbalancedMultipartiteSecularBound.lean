import UnbalancedMultipartiteSecular

/-!
# The secular kernel's other case: a part of exactly half the size

**THE PREVIOUS UNIT LEFT THIS AS ITS ONE NAMED, PRICED, UNDONE ITEM AND THIS IS IT.**
`UnbalancedMultipartiteSecular` reduced `Q`'s multiplicity at `N − n` to
`kₙ(n − 1) + dim ker (secularMap)` exactly, bounded that kernel by `1` **when no part satisfies
`2nᵢ = n`**, and said in its own "what is NOT here" that the other case would bound it by
`|T| − 1`, where `T = {i | 2nᵢ = n}`, and would need a second rank-nullity over a subtype of the
index type. **That is what is here**, and with it the chain's upper bound on `Q` is complete: every
part value is covered by one of the two cases.

## Why the two cases are genuinely different, and the answer is not monotone

`T = ∅` gives `≤ 1`; `|T| = 1` gives `≤ 0`; `|T| = 2` gives `≤ 1`; `|T| = 3` gives `≤ 2`. So the
bound **falls** from `1` to `0` as the first half-sized part appears and climbs again after. That is
not an artefact: the row of `secularMap` at a half-sized part has a **zero** diagonal entry, so
instead of constraining its own coordinate it forces the **total** to vanish, and a vanishing total
then kills every coordinate outside `T`. One half-sized part therefore removes the one degree of
freedom the `T = ∅` case had, and each further one gives a coordinate back.

## What is proved

**`offValues`** — the restriction of a vector on the parts to the parts that are *not* half-sized;
`finrank_ker_offValues` counts its kernel as `|T|` through Mathlib's `funLeft` surjectivity.
**`finrank_inf_ker_totalForm`** — cutting that kernel by the total costs exactly one dimension when
`T` is non-empty, the surjection being `Pi.single i₀`, so the space is `|T| − 1`-dimensional.
**`ker_secularMap_le_inf`** — and the secular kernel sits inside it: the row at a half-sized part
has coefficient zero on its own coordinate and `nᵢ₀ ≠ 0` on the total, so the total vanishes, and
then every row off `T` has an invertible coefficient.

**`finrank_ker_secularMap_le_half`, `finrank_signless_size_le_half`** — hence
`dim ker (secularMap) ≤ |T| − 1` and `Q`'s multiplicity at `N − n` is at most
`kₙ(n − 1) + |T| − 1`.

**`finrank_signless_size_eq_of_unique_half`** — **and when exactly one part is half-sized, `Q`
gains nothing at all**: its multiplicity at `N − n` is the Laplacian's, exactly. That is the
`|T| = 1` corner of the paragraph above, and it is an equality rather than a bound.

**`bound_sharp_diamond`** — **THE BOUND IS ATTAINED**, at the same witness the chain has used since
the signless unit: on `K₄` minus an edge the bound reads `1·1 + (2 − 1) = 2` and the multiplicity,
computed exactly in the previous unit, **is** `2`. The previous unit's own general bound read `4`
there and said so; this one is tight.

## What is NOT here

* **NEITHER BOUND IS SHARP IN GENERAL, AND NOTHING HERE EXHIBITS A FAMILY ATTAINING THE `T = ∅`
  ONE.** At two parts of size two the `T = ∅` bound reads `2 + 1 = 3`, and the multiplicity at `2`
  is `2` — **by hand**: `UnbalancedMultipartiteFibre.finrank_eigenspace_size` gives the Laplacian's
  `2`, and `SignlessBipartite.charpoly_signlessLap_eq_of_colorable` transfers it because that graph
  is two-colourable. **Neither step is instantiated in Lean here**, and the two-colourability of
  the two-part family is not proved anywhere in this chain (the chain proves the opposite for three
  or more parts). Sharp at one witness is not sharp.
* **NO LOWER BOUND ON THE SECULAR KERNEL IN GENERAL.** Nothing here says *when* the extra
  dimensions are actually there; the general question is the secular equation again, and no general
  criterion is proved. **One case is settled and it is not here**:
  `UnbalancedMultipartiteSecular.finrank_ker_secular_diamond` computes the diamond's secular kernel
  to be exactly a line, which is what makes `bound_sharp_diamond` an attainment rather than a
  coincidence. The general criterion is not attempted (`ERRATUM 246`); naming it is not a claim
  that it is short (`ERRATUM 194`).
* **NO CLOSED FORM AND NO CHARACTERISTIC POLYNOMIAL FOR `Q`**, inherited unchanged.
* **NOTHING AT AN EMPTY PART**: `∀ i, Nonempty (V i)` is used exactly where the previous unit uses
  it, and for the same reason — `nᵢ₀ ≠ 0` is what turns the half-sized row into a statement about
  the total.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0`
  and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances; a witness `i₀` with `2nᵢ₀ = n` on every statement in the half-sized case; plus
`∀ i, Nonempty (V i)`, `n ≠ 0` and `n ≠ N` where the previous unit's split is invoked. **No mass,
no propagator, and no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace UnbalancedMultipartiteSecularBound

open Matrix Finset SimpleGraph LaplacianSignless
open UnbalancedMultipartite UnbalancedMultipartiteFibre UnbalancedMultipartiteTable
open UnbalancedMultipartiteSignless UnbalancedMultipartiteSecular

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. The values off the half-sized parts -/

noncomputable def offValues (n : ℕ) :
    (ι → ℝ) →ₗ[ℝ] ({i : ι // 2 * Fintype.card (V i) ≠ n} → ℝ) :=
  LinearMap.funLeft ℝ ℝ (Subtype.val : {i : ι // 2 * Fintype.card (V i) ≠ n} → ι)

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem mem_ker_offValues_iff (n : ℕ) (P : ι → ℝ) :
    P ∈ LinearMap.ker (offValues (V := V) n)
      ↔ ∀ i, 2 * Fintype.card (V i) ≠ n → P i = 0 := by
  rw [LinearMap.mem_ker, funext_iff]
  constructor
  · exact fun h i hi => h ⟨i, hi⟩
  · exact fun h j => h j.1 j.2

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem finrank_ker_offValues (n : ℕ) :
    Module.finrank ℝ (LinearMap.ker (offValues (V := V) n))
      = Fintype.card {i : ι // 2 * Fintype.card (V i) = n} := by
  have hrange : LinearMap.range (offValues (V := V) n) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (LinearMap.funLeft_surjective_of_injective ℝ ℝ _ Subtype.val_injective)
  have hrn := LinearMap.finrank_range_add_finrank_ker (offValues (V := V) n)
  rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card] at hrn
  have hc : Fintype.card {i : ι // 2 * Fintype.card (V i) ≠ n}
      = Fintype.card ι - Fintype.card {i : ι // 2 * Fintype.card (V i) = n} :=
    Fintype.card_subtype_compl _
  have hle : Fintype.card {i : ι // 2 * Fintype.card (V i) = n} ≤ Fintype.card ι :=
    Fintype.card_subtype_le _
  omega

/-! ## 2. Cutting that space by the total -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem finrank_inf_ker_totalForm {n : ℕ} (i₀ : ι) (h0 : 2 * Fintype.card (V i₀) = n) :
    Module.finrank ℝ ((LinearMap.ker (offValues (V := V) n)
        ⊓ LinearMap.ker (totalForm (ι := ι))) : Submodule ℝ (ι → ℝ))
      = Fintype.card {i : ι // 2 * Fintype.card (V i) = n} - 1 := by
  classical
  set W := LinearMap.ker (offValues (V := V) n) with hW
  have hsurj : Function.Surjective ((totalForm (ι := ι)).domRestrict W) := by
    intro s
    refine ⟨⟨Pi.single i₀ s, ?_⟩, ?_⟩
    · rw [hW, mem_ker_offValues_iff]
      intro i hi
      have hne0 : i ≠ i₀ := fun h => hi (by rw [h]; exact h0)
      simp [hne0]
    · rw [LinearMap.domRestrict_apply, totalForm_apply]
      simp
  have hrn := LinearMap.finrank_range_add_finrank_ker ((totalForm (ι := ι)).domRestrict W)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    LinearMap.ker_domRestrict] at hrn
  have hcomap : Submodule.comap W.subtype (LinearMap.ker (totalForm (ι := ι)))
      = Submodule.comap W.subtype (W ⊓ LinearMap.ker (totalForm (ι := ι))) := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
  rw [hcomap, (Submodule.comapSubtypeEquivOfLe
    (inf_le_left : W ⊓ LinearMap.ker (totalForm (ι := ι)) ≤ W)).finrank_eq,
    finrank_ker_offValues] at hrn
  omega

/-! ## 3. The secular kernel sits inside that space -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem ker_secularMap_le_inf {n : ℕ} (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (h0 : 2 * Fintype.card (V i₀) = n) :
    LinearMap.ker (secularMap (V := V) ((Fintype.card (Σ i, V i) : ℝ) - n))
      ≤ LinearMap.ker (offValues (V := V) n) ⊓ LinearMap.ker (totalForm (ι := ι)) := by
  intro P hP
  have hrow := (mem_ker_secularMap_iff (V := V) _ P).mp hP
  have hS : ∑ j, P j = 0 := by
    have h := hrow i₀
    have hc0 : (2 : ℝ) * Fintype.card (V i₀) = n := by exact_mod_cast h0
    have hcoef : ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i₀)
        - ((Fintype.card (Σ i, V i) : ℝ) - n)) = 0 := by linarith
    rw [hcoef, zero_mul, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left
      (Nat.cast_ne_zero.mpr (card_part_ne_zero (V := V) hne i₀))
  refine Submodule.mem_inf.mpr ⟨?_, LinearMap.mem_ker.mpr ?_⟩
  · rw [mem_ker_offValues_iff]
    intro i hi
    have h := hrow i
    rw [hS, mul_zero, add_zero] at h
    have hcoef : ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)
        - ((Fintype.card (Σ i, V i) : ℝ) - n)) ≠ 0 := by
      intro hz
      exact hi (by exact_mod_cast (by linarith : (2 : ℝ) * Fintype.card (V i) = n))
    exact (mul_eq_zero.mp h).resolve_left hcoef
  · rw [totalForm_apply]
    exact hS

/-! ## 4. So the bound, in the case the previous unit could not reach -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem finrank_ker_secularMap_le_half {n : ℕ} (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (h0 : 2 * Fintype.card (V i₀) = n) :
    Module.finrank ℝ (LinearMap.ker (secularMap (V := V)
        ((Fintype.card (Σ i, V i) : ℝ) - n)))
      ≤ Fintype.card {i : ι // 2 * Fintype.card (V i) = n} - 1 := by
  rw [← finrank_inf_ker_totalForm (V := V) i₀ h0]
  exact Submodule.finrank_mono (ker_secularMap_le_inf hne i₀ h0)

theorem finrank_signless_size_le_half {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n ≠ Fintype.card (Σ i, V i)) (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (h0 : 2 * Fintype.card (V i₀) = n) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
        - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id))
      ≤ Fintype.card {i : ι // Fintype.card (V i) = n} * (n - 1)
        + (Fintype.card {i : ι // 2 * Fintype.card (V i) = n} - 1) := by
  rw [finrank_signless_size_eq hn0 hnN hne]
  have h := finrank_ker_secularMap_le_half (V := V) hne i₀ h0
  omega

/-! ## 5. One half-sized part and `Q` gains nothing at all -/

theorem finrank_signless_size_eq_of_unique_half {n : ℕ} (hn0 : n ≠ 0)
    (hnN : n ≠ Fintype.card (Σ i, V i)) (hne : ∀ i, Nonempty (V i)) (i₀ : ι)
    (h0 : 2 * Fintype.card (V i₀) = n)
    (huniq : ∀ i, 2 * Fintype.card (V i) = n → i = i₀) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap (completeMultipartiteGraph V))
        - ((Fintype.card (Σ i, V i) : ℝ) - n) • LinearMap.id))
      = Fintype.card {i : ι // Fintype.card (V i) = n} * (n - 1) := by
  have hc : Fintype.card {i : ι // 2 * Fintype.card (V i) = n} = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨i₀, h0⟩, fun j => Subtype.ext (huniq j.1 j.2)⟩
  have hle := finrank_ker_secularMap_le_half (V := V) hne i₀ h0
  rw [hc] at hle
  rw [finrank_signless_size_eq hn0 hnN hne]
  omega

/-! ## 6. And at the witness the bound is attained -/

theorem bound_sharp_diamond :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph (fun i : Fin 3 => Fin (i.1 / 2 + 1))))
      - (2 : ℝ) • LinearMap.id))
      = Fintype.card {i : Fin 3 // Fintype.card (Fin (i.1 / 2 + 1)) = 2} * (2 - 1)
        + (Fintype.card {i : Fin 3 // 2 * Fintype.card (Fin (i.1 / 2 + 1)) = 2} - 1) := by
  rw [finrank_signless_eigenspace_diamond]
  decide

end UnbalancedMultipartiteSecularBound
