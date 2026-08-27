import PairingSharp
import PairingBound
import PairingParity

/-!
# The three kinds of pair, and why the crossing count fixes the other two

`LatticeTruncatedNorms` was sharpened to carry `max(Cs,Ct)²` in the factor that bounds every pair,
and its record said what that left: **sharpening past a maximum needs the count PER KIND carried
inside the sum over pairings**, which it called a different theorem. This is the combinatorial half
of that theorem, and the reason it is worth having is one identity.

A pairing splits the representatives into three kinds — both ends inside the near group, both ends
outside it, and one end each. **The three counts are not independent.** Writing `a`, `b`, `c` for
them, each near-near pair uses two members of `S` and each crossing pair uses exactly one, so

  `2a + c = |S|`   and   `2b + c = |Sᶜ|`.

**So `c` determines `a` and `b`.** A bound that knows how many pairs cross knows exactly how many
of each other kind there are, and the per-kind product it multiplies out is
`ε^c · (near bound)^a · (far bound)^b` with the exponents read off `c` — no case analysis, no
inequality, an equation.

## What is proved

* `nearSet`, `farSet` — the two other kinds, beside `PairingSharp.crossSet`;
* **`two_mul_card_nearSet_add_card_cross`** and its twin — the two identities above;
* **`card_kinds`** — and the three counts add to `|ι|/2`, which is every representative;
* **`card_kinds_near_fin_four`, `card_kinds_far_fin_four`** — **the check**, by `decide` at
  `Fin 4` and the split `{0, 1}`, over **every pairing at once**: both identities hold term by
  term, not on average. Two theorems and not one, because the near and far identities come from
  two different instances of the same lemma and a single check would exercise only one of them.

## What is NOT here

**The bound.** Turning these counts into `ε^c·Ms^a·Mt^b` means splitting the product over the
representatives three ways and applying a different bound on each — `Finset.prod_le_prod` on each
piece after `Finset.prod_union` twice. **Not done, not costed** (`ERRATUM 194`). And summing THAT
over pairings needs the number of pairings with exactly `c` crossings, which is a formula this
estate does not have — `PairingCount.card_crossing_doubleFactorial` counts the pairings that cross
at all, not those that cross a given number of times.

No measure, integral or test function appears in this file.
-/

namespace PairingKinds

open Equiv Function Involutions PairWeightRep PairingSplit PairingSharp PairingParity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-! ## 1. The two other kinds

`PairingSharp.crossSet` is the representatives whose pair crosses the split. These are the other
two, at the representative set every consumer uses — `Finset.univ.filter (· < σ ·)`. -/

/-- The representatives with BOTH ends inside `S`. -/
def nearSet (σ : Equiv.Perm ι) (S : Finset ι) : Finset ι :=
  Finset.univ.filter (fun i => i < σ i ∧ i ∈ S ∧ σ i ∈ S)

/-- The representatives with both ends OUTSIDE `S`. -/
def farSet (σ : Equiv.Perm ι) (S : Finset ι) : Finset ι :=
  Finset.univ.filter (fun i => i < σ i ∧ i ∉ S ∧ σ i ∉ S)

/-- The `σ`-invariant set a near-near pair lives in. -/
private def inside (σ : Equiv.Perm ι) (S : Finset ι) : Finset ι :=
  S.filter (fun i => σ i ∈ S)

/-! ## 2. Half of an invariant set

The one real step: a `σ`-invariant subset is matched by `σ` restricted to it, so exactly half its
members are below their partner. `Involutions.two_mul_card_lt_image` says that at a type; the work
is carrying it to a `Finset` and back. -/

omit [Fintype ι] [DecidableEq ι] in
/-- **HALF OF AN INVARIANT SET LIES BELOW ITS PARTNER.** `T` is `σ`-invariant and `σ` is a pairing,
so `σ` restricted to `T` is a pairing of `T`. -/
theorem two_mul_card_lt_of_invariant {σ : Equiv.Perm ι} (hσ : σ ∈ perfectMatchings ι)
    (T : Finset ι) (hmem : ∀ x, σ x ∈ T ↔ x ∈ T) :
    2 * (T.filter (fun i => i < σ i)).card = T.card := by
  classical
  have hinv : Function.Involutive σ := hσ.1
  have hpm : σ.subtypePerm hmem ∈ perfectMatchings {x : ι // x ∈ T} := by
    refine ⟨fun x => by ext; simpa using hinv (x : ι), ?_⟩
    intro x hx
    exact hσ.2 (x : ι) (by simpa using congrArg Subtype.val hx)
  have h := Involutions.two_mul_card_lt_image hpm
  rw [Fintype.card_coe] at h
  have hcard : (Finset.univ.filter
      (fun x : {x : ι // x ∈ T} => x < (σ.subtypePerm hmem) x)).card
        = (T.filter (fun i => i < σ i)).card := by
    refine Finset.card_bij' (fun x _ => (x : ι))
      (fun i hi => ⟨i, (Finset.mem_filter.mp hi).1⟩) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨x.2, hx⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi.2
    · intro x _; rfl
    · intro i _; rfl
  rwa [hcard] at h

/-! ## 3. The identities -/

/-- **`2a + c = |S|`.** Each near-near pair uses two members of `S`; each crossing pair uses one,
and `PairingSharp.card_crossSet` is what says "exactly one". -/
theorem two_mul_card_nearSet_add_card_cross {σ : Equiv.Perm ι} (hσ : σ ∈ perfectMatchings ι)
    (S : Finset ι) :
    2 * (nearSet σ S).card
        + (crossSet σ S (Finset.univ.filter (fun i => i < σ i))).card = S.card := by
  classical
  have hinv : Function.Involutive σ := hσ.1
  have hmem : ∀ x, σ x ∈ inside σ S ↔ x ∈ inside σ S := fun x => invariant_filter hinv S x
  have hhalf := two_mul_card_lt_of_invariant hσ (inside σ S) hmem
  have hnear : (inside σ S).filter (fun i => i < σ i) = nearSet σ S := by
    ext i
    simp only [nearSet, inside, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [hnear] at hhalf
  have hcross := card_crossSet (S := S) hσ (isRepSet_filter_lt hσ.1)
  rw [hhalf, hcross, inside]
  exact Finset.card_filter_add_card_filter_not (s := S) (fun i => σ i ∈ S)

/-- **`2b + c = |Sᶜ|`**, by the same argument at the complement. `RespectsSplit` is symmetric in
the two sides and so is a crossing pair, which is why the crossing count is the SAME `c`. -/
theorem two_mul_card_farSet_add_card_cross {σ : Equiv.Perm ι} (hσ : σ ∈ perfectMatchings ι)
    (S : Finset ι) :
    2 * (farSet σ S).card
        + (crossSet σ S (Finset.univ.filter (fun i => i < σ i))).card = Sᶜ.card := by
  classical
  have hinv : Function.Involutive σ := hσ.1
  have hmem : ∀ x, σ x ∈ inside σ Sᶜ ↔ x ∈ inside σ Sᶜ := fun x => invariant_filter hinv Sᶜ x
  have hhalf := two_mul_card_lt_of_invariant hσ (inside σ Sᶜ) hmem
  have hfar : (inside σ Sᶜ).filter (fun i => i < σ i) = farSet σ S := by
    ext i
    simp only [farSet, inside, Finset.mem_filter, Finset.mem_univ, Finset.mem_compl, true_and]
    tauto
  rw [hfar] at hhalf
  have hcross := card_crossSet (S := Sᶜ) hσ (isRepSet_filter_lt hσ.1)
  have hswap : (crossSet σ Sᶜ (Finset.univ.filter (fun i => i < σ i))).card
      = (crossSet σ S (Finset.univ.filter (fun i => i < σ i))).card := by
    congr 1
    ext i
    simp only [crossSet, Finset.mem_filter, Finset.mem_compl]
    tauto
  rw [hswap] at hcross
  rw [hhalf, hcross, inside]
  exact Finset.card_filter_add_card_filter_not (s := Sᶜ) (fun i => σ i ∈ Sᶜ)

/-- **AND THE THREE KINDS ARE EVERY REPRESENTATIVE.** Adding the two identities and halving:
`a + b + c = |ι|/2`, which `PairingBound.two_mul_card_filter_lt` says is the number of pairs. -/
theorem card_kinds {σ : Equiv.Perm ι} (hσ : σ ∈ perfectMatchings ι) (S : Finset ι) :
    2 * ((nearSet σ S).card + (farSet σ S).card
        + (crossSet σ S (Finset.univ.filter (fun i => i < σ i))).card) = Fintype.card ι := by
  have h1 := two_mul_card_nearSet_add_card_cross hσ S
  have h2 := two_mul_card_farSet_add_card_cross hσ S
  have hc : S.card + Sᶜ.card = Fintype.card ι := by
    rw [Finset.card_compl]
    have := Finset.card_le_univ S
    omega
  -- no parity needed: adding the two identities gives `2(a+b+c) = |S| + |Sᶜ| = |ι|` directly.
  omega

/-! ## 4. The check

Over EVERY pairing of `Fin 4` at once, not at a chosen one. `decide` enumerates the permutations,
keeps the pairings, and tests both identities on each — so a formula that held on average, or at
the pairing somebody happened to pick, would fail here. -/

set_option maxRecDepth 4000 in
/-- **THE CHECK, BY ENUMERATION.** At `Fin 4` split `{0, 1}`, every pairing satisfies
`2a + c = |S| = 2`. -/
theorem card_kinds_near_fin_four :
    ∀ σ : ↑(perfectMatchings (Fin 4)),
      2 * (nearSet σ.1 ({0, 1} : Finset (Fin 4))).card
        + (crossSet σ.1 ({0, 1} : Finset (Fin 4))
            (Finset.univ.filter (fun i => i < σ.1 i))).card = 2 := by
  decide

set_option maxRecDepth 4000 in
/-- And the twin at the complement: `2b + c = |Sᶜ| = 2`. Stated separately because the two are
proved by different instances of the same lemma and a single check would exercise one of them. -/
theorem card_kinds_far_fin_four :
    ∀ σ : ↑(perfectMatchings (Fin 4)),
      2 * (farSet σ.1 ({0, 1} : Finset (Fin 4))).card
        + (crossSet σ.1 ({0, 1} : Finset (Fin 4))
            (Finset.univ.filter (fun i => i < σ.1 i))).card = 2 := by
  decide

end PairingKinds
