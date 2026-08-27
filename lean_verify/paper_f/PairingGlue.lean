import PairingRestrict

/-!
# Gluing two matchings into one, and the split as a bijection

`PairingRestrict` cut a matching that respects a split down to one side and proved the result is
again a perfect matching. **That is one direction.** This file supplies the other — gluing a
matching of `S` and a matching of its complement into a matching of `ι` — and proves the two
inverse to each other, which turns *"respects the split"* into *"is a pair of matchings, one per
side"*.

Mathlib's `Equiv.Perm.subtypeCongr` glues; what has to be checked is that gluing two perfect
matchings gives a perfect matching, and that the round trips are the identity. The round trips are
where the work is, because `Equiv.Perm` is a structure and two permutations agreeing at every
point is not `rfl`.

## What is proved

* `restrictCompl` — the complement side's restriction, stated over `{x // x ∉ S}` rather than over
  `↥Sᶜ`, **because that is the subtype `subtypeCongr` consumes** and carrying the difference
  through every lemma would cost more than stating it twice;
* `glue`, `glue_apply_mem`, `glue_apply_notMem` — the glue and its two values;
* `glue_respectsSplit`, `glue_mem_perfectMatchings` — it respects the split and is a matching;
* **`restrict_glue`, `restrictCompl_glue`, `glue_restrict`** — the two round trips;
* **`splitEquiv`** — the bijection, as an `Equiv`;
* `card_respecting` — the respecting matchings counted by the product of the two sides' counts.
  **A corollary of the `Equiv`, and NOT a check**, since it cannot fail while the `Equiv`
  typechecks;
* **`card_respecting_fin_four`, `card_respecting_fin_four_via_formula`** — **the check**, and it
  is by enumeration: `decide` counts the matchings of `Fin 4` respecting `{0, 1}` and gets `1`,
  and counts the formula's two factors and gets `1 · 1`. Neither proof passes through
  `splitEquiv`. `Involutions.card_perfectMatchings_fin_four` is `3`, so the predicted number is
  one of three rather than all three, and a bijection that had lost or gained matchings would
  land somewhere else.

## What is NOT here

**The weight.** `splitEquiv` moves the INDEX SETS; it says nothing about the pairing product
attached to each matching, and the factorisation
`∑ respecting = (∑ over S)·(∑ over Sᶜ)` needs the product to factor along the bijection too.
`PairingRestrict.prod_split` and `restrict_isRepSet` are the two halves of that and they are not
assembled here. **Not costed** (`ERRATUM 194`). No measure, integral or test function appears.
-/

namespace PairingGlue

open Equiv Function Involutions PairWeightRep PairingSplit PairingRestrict

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The complement side, in the subtype `subtypeCongr` wants -/

/-- The restriction to the complement, over `{x // x ∉ S}`. `PairingRestrict.restrict` at `Sᶜ`
lands in `↥Sᶜ`, which is a different type from `{x // x ∉ S}` even though its members are the
same, and `subtypeCongr` wants the second. -/
def restrictCompl (S : Finset ι) (σ : Equiv.Perm ι) (h : RespectsSplit S σ) :
    Equiv.Perm {x : ι // x ∉ S} :=
  σ.subtypePerm fun x => not_congr (h x)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem restrictCompl_apply_coe {S : Finset ι} {σ : Equiv.Perm ι} (h : RespectsSplit S σ)
    (x : {x : ι // x ∉ S}) : ((restrictCompl S σ h) x : ι) = σ x := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem restrictCompl_mem_perfectMatchings {S : Finset ι} {σ : Equiv.Perm ι}
    (hσ : σ ∈ perfectMatchings ι) (h : RespectsSplit S σ) :
    restrictCompl S σ h ∈ perfectMatchings {x : ι // x ∉ S} := by
  refine ⟨fun x => by ext; simpa using hσ.1 (x : ι), ?_⟩
  intro x hx
  exact hσ.2 (x : ι) (by simpa using congrArg Subtype.val hx)

/-! ## 2. The glue -/

/-- Two permutations, one per side, read as one permutation of `ι`. -/
def glue (S : Finset ι) (g : Equiv.Perm {x : ι // x ∈ S}) (k : Equiv.Perm {x : ι // x ∉ S}) :
    Equiv.Perm ι :=
  g.subtypeCongr k

omit [Fintype ι] in
theorem glue_apply_mem (S : Finset ι) (g : Equiv.Perm {x : ι // x ∈ S})
    (k : Equiv.Perm {x : ι // x ∉ S}) {a : ι} (ha : a ∈ S) :
    glue S g k a = (g ⟨a, ha⟩ : ι) :=
  Equiv.Perm.subtypeCongr.left_apply g k ha

omit [Fintype ι] in
theorem glue_apply_notMem (S : Finset ι) (g : Equiv.Perm {x : ι // x ∈ S})
    (k : Equiv.Perm {x : ι // x ∉ S}) {a : ι} (ha : a ∉ S) :
    glue S g k a = (k ⟨a, ha⟩ : ι) :=
  Equiv.Perm.subtypeCongr.right_apply g k ha

omit [Fintype ι] in
theorem glue_respectsSplit (S : Finset ι) (g : Equiv.Perm {x : ι // x ∈ S})
    (k : Equiv.Perm {x : ι // x ∉ S}) : RespectsSplit S (glue S g k) := by
  intro a
  by_cases ha : a ∈ S
  · rw [glue_apply_mem S g k ha]
    simp [ha, (g ⟨a, ha⟩).2]
  · rw [glue_apply_notMem S g k ha]
    simp [ha, (k ⟨a, ha⟩).2]

omit [Fintype ι] in
/-- **GLUING TWO PERFECT MATCHINGS GIVES A PERFECT MATCHING.** Both clauses are checked on each
side separately, which is the whole point of the construction. -/
theorem glue_mem_perfectMatchings {S : Finset ι} {g : Equiv.Perm {x : ι // x ∈ S}}
    {k : Equiv.Perm {x : ι // x ∉ S}} (hg : g ∈ perfectMatchings _)
    (hk : k ∈ perfectMatchings _) : glue S g k ∈ perfectMatchings ι := by
  constructor
  · intro a
    by_cases ha : a ∈ S
    · rw [glue_apply_mem S g k ha, glue_apply_mem S g k (g ⟨a, ha⟩).2]
      have := hg.1 ⟨a, ha⟩
      simpa using congrArg Subtype.val this
    · rw [glue_apply_notMem S g k ha, glue_apply_notMem S g k (k ⟨a, ha⟩).2]
      have := hk.1 ⟨a, ha⟩
      simpa using congrArg Subtype.val this
  · intro a ha
    by_cases hm : a ∈ S
    · rw [glue_apply_mem S g k hm] at ha
      exact hg.2 ⟨a, hm⟩ (Subtype.ext ha)
    · rw [glue_apply_notMem S g k hm] at ha
      exact hk.2 ⟨a, hm⟩ (Subtype.ext ha)

/-! ## 3. The round trips -/

omit [Fintype ι] in
theorem restrict_glue (S : Finset ι) (g : Equiv.Perm {x : ι // x ∈ S})
    (k : Equiv.Perm {x : ι // x ∉ S}) :
    restrict S (glue S g k) (glue_respectsSplit S g k) = g := by
  ext x
  simpa [restrict_apply_coe] using glue_apply_mem S g k x.2

omit [Fintype ι] in
theorem restrictCompl_glue (S : Finset ι) (g : Equiv.Perm {x : ι // x ∈ S})
    (k : Equiv.Perm {x : ι // x ∉ S}) :
    restrictCompl S (glue S g k) (glue_respectsSplit S g k) = k := by
  ext x
  simpa [restrictCompl_apply_coe] using glue_apply_notMem S g k x.2

omit [Fintype ι] in
theorem glue_restrict {S : Finset ι} {σ : Equiv.Perm ι} (h : RespectsSplit S σ) :
    glue S (restrict S σ h) (restrictCompl S σ h) = σ := by
  ext a
  by_cases ha : a ∈ S
  · rw [glue_apply_mem S _ _ ha]; rfl
  · rw [glue_apply_notMem S _ _ ha]; rfl

/-! ## 4. The bijection -/

/-- **THE SPLIT, AS A BIJECTION.** A perfect matching respecting the split IS a pair of perfect
matchings, one per side. -/
def splitEquiv (S : Finset ι) :
    {σ : Equiv.Perm ι // σ ∈ perfectMatchings ι ∧ RespectsSplit S σ}
      ≃ {g : Equiv.Perm {x : ι // x ∈ S} // g ∈ perfectMatchings _}
        × {k : Equiv.Perm {x : ι // x ∉ S} // k ∈ perfectMatchings _} where
  toFun σ := (⟨restrict S σ.1 σ.2.2, restrict_mem_perfectMatchings σ.2.1 σ.2.2⟩,
              ⟨restrictCompl S σ.1 σ.2.2, restrictCompl_mem_perfectMatchings σ.2.1 σ.2.2⟩)
  invFun p := ⟨glue S p.1.1 p.2.1,
               glue_mem_perfectMatchings p.1.2 p.2.2, glue_respectsSplit S p.1.1 p.2.1⟩
  left_inv σ := Subtype.ext (glue_restrict σ.2.2)
  right_inv p := by
    ext1 <;> simp [restrict_glue, restrictCompl_glue]

/-! ## 5. Counting, and the check

`card_respecting` is a **corollary, not a check**: it is `Fintype.card_congr` applied to
`splitEquiv`, so it cannot fail while the `Equiv` typechecks. Recording it as a check would be the
mistake `SteinTermTransport` records deleting a lemma over — *a check that checks nothing does not
become informative by being labelled*. **The check is `card_respecting_fin_four`**, which computes
the left-hand side by `decide` — enumerating the permutations of `Fin 4` and testing both clauses
— and compares it with what the formula says. `Involutions.card_perfectMatchings_fin_four` gives
`3` for the unrestricted count, so the number the bijection predicts is one of three rather than
all three, and a bijection that had lost or gained matchings would land somewhere else. -/

/-- The respecting matchings are counted by the product of the two sides' counts. A corollary of
`splitEquiv` and nothing more. -/
theorem card_respecting (S : Finset ι) :
    Fintype.card {σ : Equiv.Perm ι // σ ∈ perfectMatchings ι ∧ RespectsSplit S σ}
      = Fintype.card {g : Equiv.Perm {x : ι // x ∈ S} // g ∈ perfectMatchings _}
        * Fintype.card {k : Equiv.Perm {x : ι // x ∉ S} // k ∈ perfectMatchings _} := by
  classical
  rw [Fintype.card_congr (splitEquiv S), Fintype.card_prod]

/-- **THE CHECK, BY ENUMERATION.** The perfect matchings of `Fin 4` respecting the split `{0, 1}`
number exactly one — pair `0` with `1` and `2` with `3`. `decide` enumerates the permutations and
tests both clauses; nothing in this proof passes through `splitEquiv`. -/
theorem card_respecting_fin_four :
    Fintype.card {σ : Equiv.Perm (Fin 4) //
      σ ∈ perfectMatchings (Fin 4) ∧ RespectsSplit ({0, 1} : Finset (Fin 4)) σ} = 1 := by
  decide

/-- And the formula's other side at the same instance, so the two are compared rather than
asserted equal: one matching of a two-element side, one of the other. -/
theorem card_respecting_fin_four_via_formula :
    Fintype.card {g : Equiv.Perm {x : Fin 4 // x ∈ ({0, 1} : Finset (Fin 4))} //
        g ∈ perfectMatchings _}
      * Fintype.card {k : Equiv.Perm {x : Fin 4 // x ∉ ({0, 1} : Finset (Fin 4))} //
        k ∈ perfectMatchings _} = 1 := by
  decide

end PairingGlue
