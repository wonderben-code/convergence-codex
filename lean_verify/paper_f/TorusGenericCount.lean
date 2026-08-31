import TorusGenericFrequency

/-!
# How many generic frequencies there are, exactly

`TorusGenericFrequency` exhibited one frequency satisfying `TorusHyperoctahedral`'s three
hypotheses and closed by saying what it had not done:

> **No proportion, and *generic* is still an informal word.** The number of frequencies satisfying
> the three hypotheses is a finite combinatorial quantity — `2^d` times a descending factorial in
> `⌊(n−1)/2⌋`, by pairing each value with its mirror — and **nothing below counts it**.

**Counted here.** The non-zero frequencies of a single axis fall into `p = ⌊(n−1)/2⌋` mirror pairs
`{a, n−a}`, plus — when `n` is even — the halfway value `n/2`, which is its own mirror and which the
hypotheses exclude. So a generic frequency is exactly: an injection from the axes into the pairs,
together with a choice of side in each chosen pair.

> **`Generic`** — the three hypotheses as one predicate, so the statement below is about a set
> rather than about a conjunction.
>
> **`decode`** — from `(f, ε)` with `f : Fin d ↪ Fin p` and `ε : Fin d → Bool`, the frequency whose
> `i`-th coordinate is `f i + 1` or `n − (f i + 1)` according to `ε i`.
>
> **`decode_generic`, `decode_bijective`** — every decoded frequency is generic, and every generic
> frequency is decoded from exactly one pair. The forward halves are `omega` from `f i < p` and
> `2p ≤ n − 1`; **the surjectivity is where the hypotheses are consumed**, and the halfway value is
> excluded there by `hsum i i` and nowhere else.
>
> **`card_generic`** — hence **exactly `2^d · P(p, d)` generic frequencies**, `P` the descending
> factorial, via `Fintype.card_embedding_eq` and `Fintype.card_fun`.

So *generic* is now a number. At `d = 2` and side `12` it is `4 · 5 · 4 = 80` of the `144`
frequencies; at `d = 1` it is `2p`, which is `n − 1` less the halfway value when there is one.

**CROSS-CHECKED AGAINST A DIRECT ENUMERATION BEFORE THE COMMIT**, outside Lean and labelled as
such: the formula was compared with a brute-force count of the frequencies satisfying the three
conditions for every side length `3 … 12` and every `d ≤ 3` — **40 cases, 0 mismatches**. That is
not part of the proof and is not offered as one; it is the check that the *statement* says what it
was meant to say, which a proof of the wrong statement would pass.

## What is NOT here

**No proportion is asserted as a limit or an asymptotic.** `2^d · P(p, d) / n^d` is a ratio of two
numbers this file computes and does not study; **no statement is made about its behaviour in `n` or
`d`**, and none is guessed (`ERRATUM 246`).

**This counts frequencies, not eigenvalues.** Distinct generic frequencies can share an eigenvalue —
that is the entire subject of `TorusHyperoctahedral` — so this is **not** a count of eigenvalues
with large multiplicity, and no such count follows from it here.

**No upper bound on any multiplicity.** Unchanged, and `TorusNonReflectionCollision.sporadic_nuR_eq`
still says none can come from symmetry.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusGenericCount

open Matrix GraphLaplacian SimpleGraph Finset BoxGraph TorusReflection
open MassiveTorusSpectrum

variable {d : ℕ}

/-! ## 1. The predicate and the pair count -/

/-- **THE THREE HYPOTHESES AS ONE PREDICATE.** Exactly
`TorusHyperoctahedral.hyperoctahedral_le_finrank_eigenspace`'s, in the same order. -/
def Generic {N : ℕ} (k : Site d (N + 3)) : Prop :=
  Function.Injective k ∧ (∀ i, 0 < (k i).val) ∧ ∀ i j, (k i).val + (k j).val ≠ N + 3

/-- The number of mirror pairs `{a, n − a}` among the non-zero frequencies of one axis. -/
def pairs (N : ℕ) : ℕ := (N + 2) / 2

theorem two_mul_pairs_le (N : ℕ) : 2 * pairs N ≤ N + 2 := by
  unfold pairs; omega

theorem le_two_mul_pairs (N : ℕ) : N + 1 ≤ 2 * pairs N := by
  unfold pairs; omega

/-! ## 2. Building a frequency from a pair-choice and a sign -/

/-- **DECODE.** The `i`-th coordinate is `f i + 1`, or its mirror `n − (f i + 1)` if `ε i`. -/
def decode {N : ℕ} (fe : (Fin d ↪ Fin (pairs N)) × (Fin d → Bool)) : Site d (N + 3) :=
  fun i =>
    if fe.2 i then
      ⟨N + 3 - ((fe.1 i).val + 1), by
        have := (fe.1 i).isLt; have := two_mul_pairs_le N; omega⟩
    else
      ⟨(fe.1 i).val + 1, by
        have := (fe.1 i).isLt; have := two_mul_pairs_le N; omega⟩

theorem decode_val_true {N : ℕ} (fe : (Fin d ↪ Fin (pairs N)) × (Fin d → Bool)) {i : Fin d}
    (h : fe.2 i = true) : ((decode fe) i).val = N + 3 - ((fe.1 i).val + 1) := by
  unfold decode; simp [h]

theorem decode_val_false {N : ℕ} (fe : (Fin d ↪ Fin (pairs N)) × (Fin d → Bool)) {i : Fin d}
    (h : fe.2 i = false) : ((decode fe) i).val = (fe.1 i).val + 1 := by
  unfold decode; simp [h]

/-- **EVERY DECODED FREQUENCY IS GENERIC.** The same-sign cases are `omega` from `f i < p`; the
mixed cases are where the pair structure is used, and they turn on `2p ≤ n − 1`. -/
theorem decode_generic {N : ℕ} (fe : (Fin d ↪ Fin (pairs N)) × (Fin d → Bool)) :
    Generic (decode fe) := by
  have hp := two_mul_pairs_le N
  refine ⟨?_, ?_, ?_⟩
  · -- injective
    intro i j hij
    have h := congrArg Fin.val hij
    have hi := (fe.1 i).isLt
    have hj := (fe.1 j).isLt
    have hff : fe.1 i = fe.1 j := by
      cases hbi : fe.2 i <;> cases hbj : fe.2 j
      · rw [decode_val_false fe hbi, decode_val_false fe hbj] at h
        exact Fin.ext (by omega)
      · rw [decode_val_false fe hbi, decode_val_true fe hbj] at h
        exact absurd h (by omega)
      · rw [decode_val_true fe hbi, decode_val_false fe hbj] at h
        exact absurd h (by omega)
      · rw [decode_val_true fe hbi, decode_val_true fe hbj] at h
        exact Fin.ext (by omega)
    exact fe.1.injective hff
  · -- none at rest
    intro i
    have hi := (fe.1 i).isLt
    cases hbi : fe.2 i
    · rw [decode_val_false fe hbi]; omega
    · rw [decode_val_true fe hbi]; omega
  · -- no two are mirrors
    intro i j
    have hi := (fe.1 i).isLt
    have hj := (fe.1 j).isLt
    cases hbi : fe.2 i <;> cases hbj : fe.2 j
    · rw [decode_val_false fe hbi, decode_val_false fe hbj]; omega
    · rw [decode_val_false fe hbi, decode_val_true fe hbj]
      intro hcon
      have : fe.1 i = fe.1 j := Fin.ext (by omega)
      have hij : i = j := fe.1.injective this
      rw [hij] at hbi
      exact absurd (hbi.symm.trans hbj) (by simp)
    · rw [decode_val_true fe hbi, decode_val_false fe hbj]
      intro hcon
      have : fe.1 i = fe.1 j := Fin.ext (by omega)
      have hij : i = j := fe.1.injective this
      rw [hij] at hbi
      exact absurd (hbi.symm.trans hbj) (by simp)
    · rw [decode_val_true fe hbi, decode_val_true fe hbj]; omega

/-! ## 3. And every generic frequency is decoded from exactly one pair -/

instance instDecidableGeneric {N : ℕ} : DecidablePred (Generic (d := d) (N := N)) := by
  intro k; unfold Generic; infer_instance

/-- **ENCODE.** Which mirror pair the `i`-th coordinate lies in. -/
def pairOf {N : ℕ} {k : Site d (N + 3)} (hk : Generic k) (i : Fin d) : Fin (pairs N) :=
  ⟨if (k i).val ≤ pairs N then (k i).val - 1 else N + 2 - (k i).val, by
    have h1 := hk.2.1 i
    have h2 := hk.2.2 i i
    have h3 := (k i).isLt
    have h4 := two_mul_pairs_le N
    have h5 := le_two_mul_pairs N
    split <;> omega⟩

theorem pairOf_val {N : ℕ} {k : Site d (N + 3)} (hk : Generic k) (i : Fin d) :
    (pairOf hk i).val = if (k i).val ≤ pairs N then (k i).val - 1 else N + 2 - (k i).val := rfl

/-- **THE PAIR MAP IS INJECTIVE**, and the mixed case is exactly where `hsum` is used: two
coordinates in one pair on opposite sides would sum to `n`. -/
theorem pairOf_injective {N : ℕ} {k : Site d (N + 3)} (hk : Generic k) :
    Function.Injective (pairOf hk) := by
  intro i j hij
  have h := congrArg Fin.val hij
  rw [pairOf_val, pairOf_val] at h
  have hi := hk.2.1 i
  have hj := hk.2.1 j
  have hbi := (k i).isLt
  have hbj := (k j).isLt
  have hs := hk.2.2 i j
  have hp := two_mul_pairs_le N
  exact hk.1 (Fin.ext (by split at h <;> split at h <;> omega))

/-- The encoded pair-and-sign datum. -/
def encode {N : ℕ} {k : Site d (N + 3)} (hk : Generic k) :
    (Fin d ↪ Fin (pairs N)) × (Fin d → Bool) :=
  (⟨pairOf hk, pairOf_injective hk⟩, fun i => decide (pairs N < (k i).val))

/-- **DECODE UNDOES ENCODE.** The sign is `p < kᵢ`, and the two branches are one `omega` each. -/
theorem decode_encode {N : ℕ} {k : Site d (N + 3)} (hk : Generic k) :
    decode (encode hk) = k := by
  funext i
  have hi := hk.2.1 i
  have hbi := (k i).isLt
  have hp := two_mul_pairs_le N
  by_cases hle : (k i).val ≤ pairs N
  · have hb : (encode hk).2 i = false := by simp [encode, hle]
    refine Fin.ext ?_
    rw [decode_val_false _ hb]
    change (pairOf hk i).val + 1 = (k i).val
    rw [pairOf_val]
    simp only [hle, if_true]
    omega
  · have hb : (encode hk).2 i = true := by simp [encode]; omega
    refine Fin.ext ?_
    rw [decode_val_true _ hb]
    change N + 3 - ((pairOf hk i).val + 1) = (k i).val
    rw [pairOf_val]
    simp only [hle, if_false]
    omega

/-- **DECODE IS A BIJECTION ONTO THE GENERIC FREQUENCIES.** -/
theorem decode_bijective (N : ℕ) :
    Function.Bijective (fun fe : (Fin d ↪ Fin (pairs N)) × (Fin d → Bool) =>
      (⟨decode fe, decode_generic fe⟩ : {k : Site d (N + 3) // Generic k})) := by
  constructor
  · rintro ⟨f, ε⟩ ⟨g, δ⟩ h
    have hk : decode (f, ε) = decode (g, δ) := congrArg Subtype.val h
    have hp := two_mul_pairs_le N
    have hsign : ∀ i, ε i = δ i := by
      intro i
      have hv := congrArg Fin.val (congrFun hk i)
      have hi := (f i).isLt
      have hj := (g i).isLt
      cases hbi : ε i <;> cases hbj : δ i
      · rfl
      · rw [decode_val_false (f, ε) hbi, decode_val_true (g, δ) hbj] at hv
        dsimp only at hv
        exact absurd hv (by omega)
      · rw [decode_val_true (f, ε) hbi, decode_val_false (g, δ) hbj] at hv
        dsimp only at hv
        exact absurd hv (by omega)
      · rfl
    have hemb : ∀ i, f i = g i := by
      intro i
      have hv := congrArg Fin.val (congrFun hk i)
      have hi := (f i).isLt
      have hj := (g i).isLt
      cases hbi : ε i
      · have hbj : δ i = false := by rw [← hsign i, hbi]
        rw [decode_val_false (f, ε) hbi, decode_val_false (g, δ) hbj] at hv
        dsimp only at hv
        exact Fin.ext (by omega)
      · have hbj : δ i = true := by rw [← hsign i, hbi]
        rw [decode_val_true (f, ε) hbi, decode_val_true (g, δ) hbj] at hv
        dsimp only at hv
        exact Fin.ext (by omega)
    exact Prod.ext (Function.Embedding.ext hemb) (funext hsign)
  · rintro ⟨k, hk⟩
    exact ⟨encode hk, Subtype.ext (decode_encode hk)⟩

/-! ## 4. So the count -/

/-- **EXACTLY `2^d · P(p, d)` GENERIC FREQUENCIES**, `P` the descending factorial and `p` the
number of mirror pairs. `Fintype.card_embedding_eq` counts the injections into the pairs and
`Fintype.card_fun` the sign vectors. -/
theorem card_generic (N : ℕ) :
    Fintype.card {k : Site d (N + 3) // Generic k}
      = 2 ^ d * Nat.descFactorial (pairs N) d := by
  rw [← Fintype.card_of_bijective (decode_bijective (d := d) N), Fintype.card_prod,
    Fintype.card_embedding_eq, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Fintype.card_fin, Nat.mul_comm]

end TorusGenericCount
