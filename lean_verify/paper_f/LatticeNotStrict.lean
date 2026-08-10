/-
  LatticeNotStrict.lean — the estate's own definition is proved, and sharp.

  WHY. This wall was held to one standard throughout: a general theorem about
  `boxGraph d n` was never accepted as closing it until the same statement was
  proved for `LatticeReflection.ReflectionPositive`, the `def` the estate
  itself wrote. `LatticeReflectionPositive` met that standard for the
  positivity. **`BoxNotStrict` then proved the inequality sharp — but again on
  `boxGraph`, and again not in the estate's vocabulary.** The same standard
  applies to a negative result as to a positive one, and this file applies it.

  **The transport is already built.** `LatticeReflectionPositive.sum_green_congr`
  says the reflected quadratic form itself moves along the isomorphism between
  the two encodings; it was written to carry positivity across and it carries
  the null direction across unchanged, because it is an equality of forms and
  not an inequality.

  WHAT THIS FILE PROVES:
  1. **`reflectedForm_lattice_eq`** — the estate's box and the general
     two-dimensional box have the SAME reflected form, under `sitePair`. A
     restatement of `sum_green_congr` in the vocabulary of
     `GraphReflection.reflectedForm`, so that the transport is visible as a
     statement about forms rather than about sums.
  2. **`exists_null_direction_lattice`** — **there is a nonzero coefficient
     family on the estate's box, supported on the first-coordinate half, whose
     reflected form is exactly zero**, for even side at least four.
  3. **`not_strict_lattice`** — hence `LatticeReflection.ReflectionPositive`
     holds and **cannot be improved to a strict inequality**. The `def` whose
     docstring once read "THIS IS A DEFINITION, NOT A THEOREM" is now a
     theorem whose sharpness is also settled.

  WHAT THIS DOES NOT DO.
  * **It does not weaken `LatticeReflectionPositive.reflectionPositive_lattice`.**
    That says the form is `≥ 0` on either side of the cut and is untouched.
  * **No second-coordinate version**, for the same reason as everywhere else
    on this wall: the estate's `def` hardcodes `refl n`, and the
    second-direction statement exists only in the general graph vocabulary
    (`LatticeReflectionTwo`), where `BoxNotStrict` already applies directly
    with no transport needed.
  * **No measure-level consequence.** `GraphOS2` and `GraphOS2Exponential`
    consume `0 ≤` only; checked when `BoxNotStrict` landed, unchanged here.
  * Still one axiom, free field, finite graph, even side.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import TorusNotStrict

namespace LatticeNotStrict

open Finset GraphLaplacian GraphReflection GraphHalfSpace BoxGraph
open LatticeReflectionPositive

variable {n : ℕ} {m : ℝ}

/-! ## 1. The reflected form transports

`sum_green_congr` was written to carry positivity from one encoding to the
other. It is an equality of forms, so it carries everything the form carries —
including the fact that the form vanishes somewhere.
-/

theorem reflectedForm_lattice_eq (c : IsingFiniteVolume.Site n → ℝ) :
    GraphReflection.reflectedForm (IsingContourSeparation.latticeGraph n) m
        (LatticeReflection.refl n) c
      = GraphReflection.reflectedForm (boxGraph 2 n) m
        (GraphReflection.revSite (n := n) (0 : Fin 2)) (fun p => c (sitePair n p)) :=
  sum_green_congr (sitePair n) adj_sitePair sitePair_revSite m c

/-! ## 2. The null direction, in the estate's own vocabulary -/

/-- **THE ESTATE'S OWN DEFINITION IS SHARP.** There is a nonzero coefficient
    family on `Fin n × Fin n`, supported on the first-coordinate half, whose
    reflected form is exactly zero. -/
theorem exists_null_direction_lattice (hn : Even n) (h4 : 4 ≤ n) (hm : m ≠ 0) :
    ∃ c : IsingFiniteVolume.Site n → ℝ, c ≠ 0 ∧
      (∀ p, p ∉ lowerHalfPair n → c p = 0) ∧
      GraphReflection.reflectedForm (IsingContourSeparation.latticeGraph n) m
        (LatticeReflection.refl n) c = 0 := by
  classical
  obtain ⟨v, hv0, hvsupp, hvform⟩ :=
    BoxNotStrict.exists_null_direction (d := 2) (m := m) (0 : Fin 2) hn h4 hm
  refine ⟨fun q => v ((sitePair n).symm q), ?_, ?_, ?_⟩
  · intro hc
    refine hv0 ?_
    funext p
    have := congrFun hc (sitePair n p)
    rwa [Equiv.symm_apply_apply] at this
  · intro q hq
    refine hvsupp _ fun hmem => hq ?_
    rw [← map_lowerHalf n]
    exact Finset.mem_map.mpr ⟨(sitePair n).symm q, hmem, by simp⟩
  · rw [reflectedForm_lattice_eq]
    simpa using hvform

/-- **SO `LatticeReflection.ReflectionPositive` IS PROVED AND CANNOT BE
    STRENGTHENED.** -/
theorem not_strict_lattice (hn : Even n) (h4 : 4 ≤ n) (hm : m ≠ 0) :
    ¬ (∀ c : IsingFiniteVolume.Site n → ℝ, c ≠ 0 →
        (∀ p, p ∉ lowerHalfPair n → c p = 0) →
        0 < GraphReflection.reflectedForm (IsingContourSeparation.latticeGraph n) m
              (LatticeReflection.refl n) c) := by
  intro hstrict
  obtain ⟨c, hc0, hcsupp, hcform⟩ := exists_null_direction_lattice (m := m) hn h4 hm
  exact absurd hcform (ne_of_gt (hstrict c hc0 hcsupp))

/-! ## 3. Review round 97 — the ways this could be hollow

**"Is this a transport or a theorem?"** A transport, and it is filed as one:
§1 is `sum_green_congr` restated and §2 is three applications of it. **The
reason it is worth a file is the standard this wall was held to** — a general
statement about `boxGraph` was never accepted as closing anything here until
it was proved for the estate's own `def`, and that standard was applied to the
positivity months of units ago. **Applying it to the positive result and not
to the negative one would be selective**, which is the only real risk this
unit addresses.

**"Does the transport really carry a NEGATIVE result?"** It does, and the
reason is worth stating rather than assuming: `sum_green_congr` is an EQUALITY
of quadratic forms, not an inequality between them. An equality carries
everything — the sign, the vanishing, the attaining vector — whereas a
transport stated as "positivity implies positivity" would carry only the sign.
**The lemma was written for the positive direction and happens to be strong
enough for both**, which is luck rather than foresight and is recorded as
such.

**"Why no second-coordinate version?"** Because there is nothing to transport
to. The estate's `def` hardcodes `refl n`; the second direction lives only in
the general graph vocabulary (`LatticeReflectionTwo`), and there
`BoxNotStrict` applies directly with no isomorphism in the way. **The absence
is a fact about the `def`, not a gap in this file**, and the one-def-or-two
question remains where it was put: DECISIONS NEEDED.

**"What is the state of this wall's flagship statement now?"**
`LatticeReflection.ReflectionPositive n m half` is: **proved** for even `n`,
nonzero `m` and every region wholly inside either side of the first-coordinate
cut; **lifted to the measure and to the exponential algebra**; and **sharp** —
the inequality is attained, from side four. What it is not is anything about
odd side, other cuts, interacting fields, or any limit. That list has not
changed today and this file adds nothing to it.
-/

end LatticeNotStrict
