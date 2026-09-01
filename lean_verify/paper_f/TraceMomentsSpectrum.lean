import PowerSumMultiset
import TracePowerSpectrum

/-!
# Equal trace moments give the same eigenvalue multiset

`UNLOCK_WATCHLIST`'s trace-moments item states, as its `ITEM:` line:

> `Tr(Aᵏ) = ∑ λᵢᵏ` for a complex matrix, and hence: equal trace moments imply the same eigenvalue
> multiset.

**This file is the second half of that sentence.** The first half — leg (i) — has been
`Matrix.trace_pow_eq_sum_roots_charpoly` since 16 August, over any algebraically closed field.

## Why the two halves did not meet until now, and it was not a missing theorem

Leg (i) delivers `(A ^ k).trace = (A.charpoly.roots.map (· ^ k)).sum` — a **`Multiset` of roots**.
Leg (ii), `PowerSumMultiset.multiset_eq_of_sum_pow_eq`, takes two **families** `f g : σ → K` over a
`Fintype`. The two were also, until 1 September, over different coefficients: leg (ii) was stated
for `ℝ` and leg (i) for an algebraically closed field, which `ℝ` is not. Removing the `ℝ` was one
edit; this file removes the shape mismatch, which is the other.

**And the shape mismatch turned out to be packaging, not mathematics.** `exists_fin_map` says every
multiset is `Multiset.map f Finset.univ.val` for some `f : Fin (card s) → K` — it is
`Multiset.coe_toList` and `List.ofFn_get` and nothing else — and leg (ii)'s conclusion is already a
multiset equality. So `eq_of_psum_eq` is leg (ii) restated at a bare multiset, with the two indexing
sets reconciled by `finCongr` on the cardinality hypothesis.

**`EsymmDeterminesMultiset.eq_of_esymm_eq` IS NOT USED HERE AND THE RECORD SAID IT WOULD BE.** The
1 September watchlist entry and this file's predecessor both name that theorem as the piece the
composition was waiting for. It is not: `PowerSumMultiset` already carries its own Vieta round trip
inside `multiset_eq_of_sum_pow_eq`, so the route from equal power sums to an equal multiset never
passes through a standalone `esymm` statement. `eq_of_esymm_eq` remains **unused by anything**, in
the more general form it was proved in, and this file is where that stops being a prediction and
becomes a fact (`ERRATUM 385`'s subject, one more turn of it).

## What is proved

* **`psum`** — the `k`-th power sum of a bare `Multiset`, which Mathlib does not have under any of
  four spellings probed on 1 September (`Multiset.psum` 0, `psum` case-insensitively 112 and all of
  them `finsuppSum`/`dfinsuppSum`/`PSum`/`MvPolynomial`, `powersum` 0, `newton` 8 and all of them
  `Polynomial.newtonMap`).
* **`eq_of_psum_eq`** — two multisets over a characteristic-zero domain with the same cardinality
  and the same power sums up to that cardinality are equal.
* **`charpoly_roots_eq_of_trace_pow_eq`** — the item. Over any algebraically closed field of
  characteristic zero, `(Aᵏ).trace = (Bᵏ).trace` for `1 ≤ k ≤ n` forces
  `A.charpoly.roots = B.charpoly.roots`.
* **`charpoly_roots_eq_of_trace_pow_eq_complex`** — the same at `ℂ`, which is the field the item
  names.

## Not covered, stated per `ERRATUM 60`

* **This is not similarity and cannot be.** A Jordan block and a diagonal matrix have the same
  charpoly roots and are not similar. The item asks for the eigenvalue multiset and that is what
  this gives. **The non-similarity itself is not proved here and is not proved anywhere in this
  estate**, which is worth saying because `TracePowerSpectrum` carries `jordanTwo` and proves
  `roots_charpoly_jordanTwo : jordanTwo.charpoly.roots = {2, 2}` — the same multiset a diagonal
  `!![2, 0; 0, 2]` has — and a reader could take that pair for a proved counterexample. It is half
  of one: the shared multiset is proved, the failure of similarity is not. Probed 1 September, by
  reading every hit rather than counting them (`ERRATUM 385`, `ERRATUM 386`): **no `theorem`, `def`
  or `lemma` anywhere under `paper_f/` mentions `IsConj`**, and the six files whose text contains
  "similar" use it in prose only — `PerronPrimitive`'s conjugation argument is proved as a
  statement about traces, not about conjugacy. **Not attempted, not costed** (`ERRATUM 194`,
  `ERRATUM 246`).
* **`n` moments are needed and `n` is not reduced here.** Nothing says fewer than `Fintype.card n`
  of them suffice, and nothing here is quantitative: two matrices whose trace moments are merely
  *close* are not shown to have close spectra. No cost is offered (`ERRATUM 194`, `ERRATUM 246`).
* **Characteristic zero is used, at the division by `k` inside leg (ii)**, and no attempt is made to
  say what survives in positive characteristic.
* **The eigenvalues are the roots of the characteristic polynomial with multiplicity, not
  `Matrix.IsHermitian.eigenvalues`.** For a Hermitian matrix `HermitianSpectralMapping` relates the
  two; nothing here does.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TraceMomentsSpectrum

open Finset

/-! ## 1. Power sums of a bare multiset -/

variable {K : Type*} [CommRing K]

/-- The `k`-th power sum of a multiset. Mathlib has `MvPolynomial.psum` and `Multiset.esymm`, and
no multiset-level power sum at all. -/
noncomputable def psum (s : Multiset K) (k : ℕ) : K := (s.map (· ^ k)).sum

/-- On a family's value multiset, `psum` is the family's power sum. -/
theorem psum_map_univ {σ : Type*} [Fintype σ] (f : σ → K) (k : ℕ) :
    psum (Multiset.map f Finset.univ.val) k = ∑ i, f i ^ k := by
  rw [psum, Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

/-- **EVERY MULTISET IS A FAMILY'S IMAGE.** `Multiset.coe_toList` produces a list, and
`List.ofFn_get` says that list is `List.ofFn` of its own indexing function; `Fin.univ_val_map`
carries that across. This is the whole of the shape mismatch between the two legs.

**Stated for an arbitrary type, not for `K`.** The `CommRing` in scope is not used and the linter
said so; the honest response is to state the true generality rather than to `omit` the binder
(`ERRATUM 274`, `ERRATUM 278` — a hypothesis in a statement that belongs to its proof, or here to
nothing at all). -/
theorem exists_fin_map {α : Type*} (s : Multiset α) :
    ∃ f : Fin (Multiset.card s) → α, Multiset.map f Finset.univ.val = s := by
  obtain ⟨l, rfl⟩ : ∃ l : List α, (l : Multiset α) = s := ⟨s.toList, s.coe_toList⟩
  exact ⟨l.get, (Fin.univ_val_map l.get).trans
    (congrArg (fun m : List α => (m : Multiset α)) (List.ofFn_get l))⟩

/-! ## 2. Leg (ii), restated at a bare multiset -/

/-- **EQUAL POWER SUMS FORCE EQUAL MULTISETS.** `PowerSumMultiset.multiset_eq_of_sum_pow_eq` with
both multisets written as families over `Fin (card s)`, the second one transported along
`finCongr` on the cardinality hypothesis. -/
theorem eq_of_psum_eq [IsDomain K] [CharZero K] {s t : Multiset K}
    (hcard : Multiset.card s = Multiset.card t)
    (h : ∀ k, 1 ≤ k → k ≤ Multiset.card s → psum s k = psum t k) : s = t := by
  obtain ⟨f, hf⟩ := exists_fin_map s
  obtain ⟨g, hg⟩ := exists_fin_map t
  have hg' : Multiset.map (fun i => g (finCongr hcard i)) Finset.univ.val = t := by
    rw [show (fun i => g (finCongr hcard i)) = g ∘ (finCongr hcard) from rfl,
      ← Multiset.map_map, Multiset.map_univ_val_equiv, hg]
  have key := PowerSumMultiset.multiset_eq_of_sum_pow_eq
    (f := f) (g := fun i => g (finCongr hcard i)) (fun k hk hkn => ?_)
  · rw [hf, hg'] at key; exact key
  · rw [Fintype.card_fin] at hkn
    have hthis := h k hk hkn
    rwa [← hf, ← hg', psum_map_univ, psum_map_univ] at hthis

/-! ## 3. The item: equal trace moments give the same eigenvalue multiset -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Over an algebraically closed field the characteristic polynomial splits, so its root multiset
has exactly `Fintype.card n` elements. This is the cardinality hypothesis `eq_of_psum_eq` needs,
and it is the one the eigenvalue consumer has for free. -/
theorem card_roots_charpoly {F : Type*} [Field F] [IsAlgClosed F] (A : Matrix n n F) :
    Multiset.card A.charpoly.roots = Fintype.card n := by
  rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _), Matrix.charpoly_natDegree_eq_dim]

/-- **THE WATCHLIST ITEM.** Over an algebraically closed field of characteristic zero, two matrices
whose first `Fintype.card n` trace moments agree have the same multiset of characteristic-polynomial
roots — the same eigenvalues with the same multiplicities.

Leg (i) turns each trace moment into a power sum of the roots; leg (ii) turns equal power sums back
into an equal multiset. **It is not similarity**: a Jordan block and a diagonal matrix share this
multiset. -/
theorem charpoly_roots_eq_of_trace_pow_eq {F : Type*} [Field F] [IsAlgClosed F] [CharZero F]
    {A B : Matrix n n F}
    (h : ∀ k, 1 ≤ k → k ≤ Fintype.card n → (A ^ k).trace = (B ^ k).trace) :
    A.charpoly.roots = B.charpoly.roots := by
  refine eq_of_psum_eq (by rw [card_roots_charpoly, card_roots_charpoly]) (fun k hk hkn => ?_)
  rw [card_roots_charpoly] at hkn
  have hA := Matrix.trace_pow_eq_sum_roots_charpoly A k
  have hB := Matrix.trace_pow_eq_sum_roots_charpoly B k
  have hk' := h k hk hkn
  rw [hA, hB] at hk'
  exact hk'

/-- **THE SAME OVER `ℂ`**, which is the field the item's own sentence names. -/
theorem charpoly_roots_eq_of_trace_pow_eq_complex {A B : Matrix n n ℂ}
    (h : ∀ k, 1 ≤ k → k ≤ Fintype.card n → (A ^ k).trace = (B ^ k).trace) :
    A.charpoly.roots = B.charpoly.roots :=
  charpoly_roots_eq_of_trace_pow_eq h

end TraceMomentsSpectrum
