import TorusDecay
import GreenDisconnected
import TorusNotStrict

/-!
# What torus connectivity was holding up, and where strictness actually fails

`TorusDecay.torusGraph_connected` was proved to settle a sentence, not to be used. This file is
`PROOF_STRATEGY` §6's first question — *what did that unlock?* — and the answer was obtained by
grepping rather than recalled, because the last three units of this campaign each shipped a
sentence about other files that turned out to be wrong (`ERRATA 163`, `164`, `165`).

**Seven declarations in `paper_f` take `G.Connected` as a hypothesis** — counted by
`grep -rn "(hG : G.Connected)" paper_f/*.lean`, which returns `GraphGreenPositive.green_pos`,
`GraphGreenPositive.twoPoint_pos`, `GraphLaplacian.lapMatrix_mulVec_eq_zero_iff_const`,
`GraphOS2.os2_pos_single`, and `GreenDisconnected`'s three re-derivations. **None had ever been
applied to the torus**: grepping those four names together with `torus` across `paper_f/*.lean`
returns nothing outside this file. The box could discharge the hypothesis; the torus could not,
for no better reason than that nobody had written three lines.

§1 instantiates three of the seven. It leaves `lapMatrix_mulVec_eq_zero_iff_const` and the two
`GreenDisconnected` duplicates alone — the first because nothing here needs the kernel of the
Laplacian, the second because they are the same statements by another route and instantiating
both spellings would add names rather than facts.

## §2 is the part worth the file

The estate proves **both** of the following about the periodic box of even side `n ≥ 6`, and
until now they had never been put next to each other:

* `TorusNotStrict.not_strict_torus` — the reflected form is **not** strictly positive on the
  vectors supported in a half. There is a nonzero such vector on which it is exactly `0`.
* and now `reflectedForm_single_pos` — it **is** strictly positive on every *single-site* vector,
  in the half or out of it, because that value is `green (θ p₀) p₀` and the torus is connected.

`strict_on_atoms_not_on_half` is the conjunction, and the content is a **localisation of the
failure**: reflection positivity on the torus does not degenerate site by site, it degenerates on
a spread-out combination. Any attempt to recover strictness by an argument that only ever looks at
one site at a time is therefore refuted before it starts, and that is the use this pair has.

## What is not claimed

**Nothing here is new mathematics and the file says so twice.** §1 is instantiation. §2 is a
conjunction of two theorems that already existed; what is new is only that they are stated
together, in one vocabulary, so the shape of the failure is visible instead of being spread over
two files that do not cite each other.

**And it does not repair strictness anywhere.** `not_strict_torus` stands exactly as it was; the
half of §2 that is positive is about a strictly smaller family of directions, and no argument here
extends it. In particular this is **not** progress on reflection positivity for the torus, which
`TorusNotStrict` refuted and which stays refuted.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusPositivity

open BoxGraph TorusReflection GraphLaplacian GraphReflection GraphHalfSpace Finset

variable {d n : ℕ} {m : ℝ}

/-! ## 1. The corollaries torus connectivity makes available

All three are one line and none is new mathematics. They are here because a hypothesis that no
theorem can discharge is, in practice, a theorem nobody can use.
-/

/-- **EVERY ENTRY OF THE TORUS PROPAGATOR IS POSITIVE**, at every side length and every distance. -/
theorem green_pos (d : ℕ) (hn : 0 < n) (hm : m ≠ 0) (p q : Site d n) :
    0 < green (torusGraph d n) m p q :=
  GraphGreenPositive.green_pos _ (TorusDecay.torusGraph_connected d hn) hm p q

/-- **AND THEREFORE EVERY TWO-POINT FUNCTION OF THE TORUS FIELD IS POSITIVE.** -/
theorem twoPoint_pos (d : ℕ) (hn : 0 < n) (hm : m ≠ 0) (p q : Site d n) :
    0 < ∫ ω, ω p * ω q ∂(gaussianField (torusGraph d n) m) :=
  GraphGreenPositive.twoPoint_pos _ (TorusDecay.torusGraph_connected d hn) hm p q

/-- **AND OS2 IS STRICT ON SINGLE-SITE OBSERVABLES ON THE TORUS**, for every reflection. -/
theorem os2_pos_single (d : ℕ) (hn : 0 < n) (hm : m ≠ 0) (θ : Site d n ≃ Site d n)
    (p : Site d n) :
    0 < ∫ ω, (∑ r, (if r = p then (1:ℝ) else 0) * ω (θ r))
            * (∑ q, (if q = p then (1:ℝ) else 0) * ω q)
        ∂(gaussianField (torusGraph d n) m) :=
  GraphOS2.os2_pos_single _ (TorusDecay.torusGraph_connected d hn) hm θ p

/-! ## 2. Where strictness fails, and where it does not -/

/-- The reflected form on a single-site vector is one entry of the propagator. -/
theorem reflectedForm_single (θ : Site d n ≃ Site d n) (p₀ : Site d n) :
    reflectedForm (torusGraph d n) m θ (fun p => if p = p₀ then (1:ℝ) else 0)
      = green (torusGraph d n) m (θ p₀) p₀ := by
  simp [reflectedForm, Finset.sum_ite_eq']

/-- **THE REFLECTED FORM IS STRICTLY POSITIVE ON EVERY SINGLE-SITE DIRECTION.** -/
theorem reflectedForm_single_pos (hn : 0 < n) (hm : m ≠ 0) (θ : Site d n ≃ Site d n)
    (p₀ : Site d n) :
    0 < reflectedForm (torusGraph d n) m θ (fun p => if p = p₀ then (1:ℝ) else 0) := by
  rw [reflectedForm_single]
  exact green_pos d hn hm _ _

/-- **THE FAILURE OF STRICTNESS ON THE TORUS IS NOT SITE BY SITE.** Both halves already existed;
the conjunction is what says where the degeneracy lives. The positive half holds for every
reflection and every site; the vanishing half is `TorusNotStrict`'s witness, which is supported in
the half and is not concentrated at a site. -/
theorem strict_on_atoms_not_on_half (i : Fin d) (hn : Even n) (h6 : 6 ≤ n) (hm : m ≠ 0) :
    (∀ p₀ : Site d n, 0 < reflectedForm (torusGraph d n) m (revSite (n := n) i)
        (fun p => if p = p₀ then (1:ℝ) else 0))
      ∧ ∃ c : Site d n → ℝ, c ≠ 0 ∧ (∀ p, p ∉ lowerHalf i n → c p = 0) ∧
          reflectedForm (torusGraph d n) m (revSite (n := n) i) c = 0 :=
  ⟨fun p₀ => reflectedForm_single_pos (by omega) hm _ p₀,
    TorusNotStrict.exists_null_direction_torus i hn h6 hm⟩

end TorusPositivity
