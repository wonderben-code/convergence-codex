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

* **`abs_prod_le_kinds`** — and the bound the counts were for: the product over the
  representatives, estimated kind by kind, `Ms^a·Mt^b·ε^c`. **No hypothesis relates the three
  bounds**, so a caller holding only a uniform one takes all three equal and recovers the old
  estimate;
* **`abs_prod_le_worst`** — **and the exact count of pairings turns out not to be needed.** With
  the cross estimate no larger than either same-side estimate, the per-kind bound is worst at the
  SMALLEST admissible crossing count, which `PairingParity` fixes at `2`: raising `c` by two trades
  one `Ms` and one `Mt` for two `ε`, and `ε² ≤ Ms·Mt`. So one bound covers every crossing pairing,
  with no enumeration anywhere;
* **`abs_prod_le_of_card_cross`** — the same bound with the exponents **read off `c`**:
  `Ms^((|S|−c)/2)·Mt^((|Sᶜ|−c)/2)·ε^c`. **This is the theorem §3 was proved for, and the one above
  is not it** — that one states its exponents as cardinalities a caller holding only the crossing
  count cannot evaluate. A first version of this summary claimed the reading and the file proved
  only the cardinality form.

## What is NOT here

**The EXACT sum**, and the distinction is the correction §6 forced on this paragraph.

*A first version said: "Carrying the per-kind bound over the pairings needs the number of pairings
with exactly `c` crossings, which this estate does not have." That is false of the BOUND.*
`abs_prod_le_worst` covers every crossing pairing at once, so summing needs only the number that
cross AT ALL — which is `PairingCount.card_crossing_doubleFactorial`, and the estate has it.

What the per-`c` count is still needed for is an **equality**: the exact value of the sum, kind by
kind, rather than an estimate of it. That is a bijection onto `c`-subsets of each side together
with a matching between them, and it is **not done, not costed** (`ERRATUM 194`).

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

/-! ## 5. The bound the counts were for

The product over the representatives splits along the three kinds, and each piece takes its own
estimate. **The exponents are the counts of §3**, so a caller who knows `c` knows the whole
expression — which is what the identities were for. -/

/-- The three kinds partition the representative set `Finset.univ.filter (· < σ ·)`. Stated as a
`Finset` identity rather than three membership lemmas, because that is the form
`Finset.prod_union` consumes. -/
theorem union_kinds (σ : Equiv.Perm ι) (S : Finset ι) :
    nearSet σ S ∪ farSet σ S ∪ crossSet σ S (Finset.univ.filter (fun i => i < σ i))
      = Finset.univ.filter (fun i => i < σ i) := by
  ext i
  simp only [nearSet, farSet, crossSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and]
  by_cases hi : i ∈ S <;> by_cases hσi : σ i ∈ S <;> simp [hi, hσi]

theorem disjoint_near_far (σ : Equiv.Perm ι) (S : Finset ι) :
    Disjoint (nearSet σ S) (farSet σ S) := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  simp only [nearSet, farSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
  exact hi'.2.1 hi.2.1

theorem disjoint_union_cross (σ : Equiv.Perm ι) (S : Finset ι) :
    Disjoint (nearSet σ S ∪ farSet σ S)
      (crossSet σ S (Finset.univ.filter (fun i => i < σ i))) := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  rw [mem_crossSet_iff] at hi'
  simp only [nearSet, farSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and] at hi
  rcases hi with h | h
  · exact hi'.2 (iff_of_true h.2.1 h.2.2)
  · exact hi'.2 (iff_of_false h.2.1 h.2.2)

/-- **THE PRODUCT, ESTIMATED KIND BY KIND.** `ε` bounds the propagator across the split, `Ms`
bounds it inside the near group and `Mt` inside the far one; the exponents are the three counts,
and §3 says the last two are determined by the first. **No hypothesis relates `ε`, `Ms` and `Mt`**
— a caller with only a uniform bound takes all three equal and recovers the old estimate. -/
theorem abs_prod_le_kinds {σ : Equiv.Perm ι} (S : Finset ι) (w : ι → ι → ℝ)
    {ε Ms Mt : ℝ}
    (hcross : ∀ i, ¬ (i ∈ S ↔ σ i ∈ S) → |w i (σ i)| ≤ ε)
    (hnear : ∀ i, i ∈ S → σ i ∈ S → |w i (σ i)| ≤ Ms)
    (hfar : ∀ i, i ∉ S → σ i ∉ S → |w i (σ i)| ≤ Mt) :
    |∏ i ∈ Finset.univ.filter (fun i => i < σ i), w i (σ i)|
      ≤ Ms ^ (nearSet σ S).card * Mt ^ (farSet σ S).card
        * ε ^ (crossSet σ S (Finset.univ.filter (fun i => i < σ i))).card := by
  classical
  -- FORWARDS, NOT BACKWARDS. `rw [← union_kinds]` also rewrites the `R` sitting inside
  -- `crossSet σ S R` on the right-hand side, which turns the goal into one about
  -- `crossSet σ S (near ∪ far ∪ cross)`. Building the split as its own equation leaves the
  -- right-hand side alone.
  have hsplit : ∏ i ∈ Finset.univ.filter (fun i => i < σ i), |w i (σ i)|
      = (∏ i ∈ nearSet σ S, |w i (σ i)|) * (∏ i ∈ farSet σ S, |w i (σ i)|)
        * ∏ i ∈ crossSet σ S (Finset.univ.filter (fun i => i < σ i)), |w i (σ i)| := by
    rw [← Finset.prod_union (disjoint_near_far σ S),
      ← Finset.prod_union (disjoint_union_cross σ S), union_kinds σ S]
  rw [Finset.abs_prod, hsplit]
  have hn : ∏ i ∈ nearSet σ S, |w i (σ i)| ≤ Ms ^ (nearSet σ S).card := by
    refine (Finset.prod_le_prod (fun i _ => abs_nonneg _) ?_).trans_eq (Finset.prod_const _)
    intro i hi
    simp only [nearSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hnear i hi.2.1 hi.2.2
  have hf : ∏ i ∈ farSet σ S, |w i (σ i)| ≤ Mt ^ (farSet σ S).card := by
    refine (Finset.prod_le_prod (fun i _ => abs_nonneg _) ?_).trans_eq (Finset.prod_const _)
    intro i hi
    simp only [farSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hfar i hi.2.1 hi.2.2
  have hc : ∏ i ∈ crossSet σ S (Finset.univ.filter (fun i => i < σ i)), |w i (σ i)|
      ≤ ε ^ (crossSet σ S (Finset.univ.filter (fun i => i < σ i))).card := by
    refine (Finset.prod_le_prod (fun i _ => abs_nonneg _) ?_).trans_eq (Finset.prod_const _)
    intro i hi
    rw [mem_crossSet_iff] at hi
    exact hcross i hi.2
  have h0 : ∀ (T : Finset ι), (0:ℝ) ≤ ∏ i ∈ T, |w i (σ i)| :=
    fun T => Finset.prod_nonneg fun _ _ => abs_nonneg _
  have hMs0 : (0:ℝ) ≤ Ms ^ (nearSet σ S).card := le_trans (h0 _) hn
  have hMt0 : (0:ℝ) ≤ Mt ^ (farSet σ S).card := le_trans (h0 _) hf
  exact mul_le_mul (mul_le_mul hn hf (h0 _) hMs0) hc (h0 _) (mul_nonneg hMs0 hMt0)

/-- **THE SAME BOUND WITH THE EXPONENTS READ OFF `c`**, which is what §3 was proved for and what
`abs_prod_le_kinds` does NOT give: that theorem states its exponents as the cardinalities of
`nearSet` and `farSet`, and a caller holding only the crossing count cannot evaluate them. The
identities of §3 do the reading — `a = (|S| − c)/2` and `b = (|Sᶜ| − c)/2` — and the subtractions
are not truncated, because `2a + c = |S|` forces `c ≤ |S|`.

**A FIRST VERSION OF THIS FILE CLAIMED THIS IN ITS SUMMARY AND PROVED ONLY THE PREVIOUS THEOREM.**
The sentence *"a caller who knows `c` knows the whole expression"* was true of the mathematics and
not of the file. -/
theorem abs_prod_le_of_card_cross {σ : Equiv.Perm ι} (hσ : σ ∈ perfectMatchings ι) (S : Finset ι)
    (w : ι → ι → ℝ) {ε Ms Mt : ℝ}
    (hcross : ∀ i, ¬ (i ∈ S ↔ σ i ∈ S) → |w i (σ i)| ≤ ε)
    (hnear : ∀ i, i ∈ S → σ i ∈ S → |w i (σ i)| ≤ Ms)
    (hfar : ∀ i, i ∉ S → σ i ∉ S → |w i (σ i)| ≤ Mt)
    {c : ℕ} (hc : (crossSet σ S (Finset.univ.filter (fun i => i < σ i))).card = c) :
    |∏ i ∈ Finset.univ.filter (fun i => i < σ i), w i (σ i)|
      ≤ Ms ^ ((S.card - c) / 2) * Mt ^ ((Sᶜ.card - c) / 2) * ε ^ c := by
  have hn := two_mul_card_nearSet_add_card_cross hσ S
  have hf := two_mul_card_farSet_add_card_cross hσ S
  rw [hc] at hn hf
  have ha : (nearSet σ S).card = (S.card - c) / 2 := by omega
  have hb : (farSet σ S).card = (Sᶜ.card - c) / 2 := by omega
  have h := abs_prod_le_kinds (σ := σ) S w hcross hnear hfar
  rwa [ha, hb, hc] at h

/-! ## 6. The worst case is two crossings, and no count of pairings is needed for it

`PairingKinds`' own record called the number of pairings with exactly `c` crossings *"the one
thing left"*. **For the bound it is not needed at all.** When the cross estimate is the smallest of
the three — which is the whole situation clustering is about — the per-kind bound is WORST at the
smallest admissible `c`, and `PairingParity` says that is `2`. Raising `c` by two trades one `Ms`
and one `Mt` for two `ε`, and `ε² ≤ Ms·Mt`. So a single bound covers every crossing pairing, with
no enumeration anywhere. -/

/-- The crossing count is at most the size of the near side, because
`PairingSharp.card_crossSet` exhibits it as the cardinality of a subset of `S`. -/
theorem card_cross_le {σ : Equiv.Perm ι} (hσ : σ ∈ perfectMatchings ι) (S : Finset ι) :
    (crossSet σ S (Finset.univ.filter (fun i => i < σ i))).card ≤ S.card := by
  rw [card_crossSet hσ (isRepSet_filter_lt hσ.1)]
  exact Finset.card_filter_le _ _

omit [Fintype ι] [LinearOrder ι] in
/-- A pairing that does not respect the split has an element of `S` whose partner is outside it —
which is the hypothesis `PairingParity.two_le_card_cross` wants, phrased the way callers hold it. -/
theorem cross_nonempty_of_not_respects {σ : Equiv.Perm ι} (hσ : σ ∈ perfectMatchings ι)
    {S : Finset ι} (hns : ¬ RespectsSplit S σ) :
    (S.filter (fun i => σ i ∉ S)).Nonempty := by
  classical
  have hinv : Function.Involutive σ := hσ.1
  -- `not_forall` and not `push_neg`: the latter is deprecated in this toolchain, and it also
  -- turns the negated `Iff` into a disjunction, which is more case analysis than either witness
  -- needs.
  rw [RespectsSplit] at hns
  obtain ⟨i, hi⟩ := not_forall.mp hns
  by_cases hiS : i ∈ S
  · -- `i ∈ S`, so the failing `Iff` forces `σ i ∉ S` and `i` itself is the witness
    exact ⟨i, Finset.mem_filter.mpr ⟨hiS, fun h => hi (iff_of_true h hiS)⟩⟩
  · -- otherwise `σ i ∈ S`, and its partner is `i`, which is not
    have hσi : σ i ∈ S := by
      by_contra h
      exact hi (iff_of_false h hiS)
    exact ⟨σ i, Finset.mem_filter.mpr ⟨hσi, by rw [hinv i]; exact hiS⟩⟩

/-- **THE SINGLE BOUND, WITH NO COUNT OF PAIRINGS IN IT.** For every pairing that crosses an
even-sized split, with the cross estimate no larger than either same-side estimate. **The exponents
are those of the two-crossing case**, which is the worst one: raising the crossing count by two
trades one `Ms` and one `Mt` for two `ε`, and `ε² ≤ Ms·Mt`. -/
theorem abs_prod_le_worst {σ : Equiv.Perm ι} (hσ : σ ∈ perfectMatchings ι) (S : Finset ι)
    (w : ι → ι → ℝ) {ε Ms Mt : ℝ} (hε0 : 0 ≤ ε) (hεs : ε ≤ Ms) (hεt : ε ≤ Mt)
    (hcross : ∀ i, ¬ (i ∈ S ↔ σ i ∈ S) → |w i (σ i)| ≤ ε)
    (hnear : ∀ i, i ∈ S → σ i ∈ S → |w i (σ i)| ≤ Ms)
    (hfar : ∀ i, i ∉ S → σ i ∉ S → |w i (σ i)| ≤ Mt)
    (hS : Even S.card) (hns : ¬ RespectsSplit S σ) :
    |∏ i ∈ Finset.univ.filter (fun i => i < σ i), w i (σ i)|
      ≤ Ms ^ ((S.card - 2) / 2) * Mt ^ ((Sᶜ.card - 2) / 2) * ε ^ 2 := by
  classical
  set c := (crossSet σ S (Finset.univ.filter (fun i => i < σ i))).card with hcdef
  have hcross_eq : c = (S.filter (fun i => σ i ∉ S)).card := by
    rw [hcdef, card_crossSet hσ (isRepSet_filter_lt hσ.1)]
  have h2c : 2 ≤ c := by
    rw [hcross_eq]
    exact PairingParity.two_le_card_cross hσ hS (cross_nonempty_of_not_respects hσ hns)
  have hpar : c % 2 = S.card % 2 := by
    rw [hcross_eq]; exact PairingParity.card_cross_parity hσ S
  have hcS : c ≤ S.card := card_cross_le hσ S
  have hcT : c ≤ Sᶜ.card := by
    have := two_mul_card_farSet_add_card_cross hσ S
    omega
  obtain ⟨u, hu⟩ := hS
  obtain ⟨t, ht⟩ : ∃ t, c = 2 + 2 * t := ⟨(c - 2) / 2, by omega⟩
  have hA : (S.card - c) / 2 + t = (S.card - 2) / 2 := by omega
  have hB : (Sᶜ.card - c) / 2 + t = (Sᶜ.card - 2) / 2 := by omega
  have hMs0 : (0:ℝ) ≤ Ms := le_trans hε0 hεs
  have hMt0 : (0:ℝ) ≤ Mt := le_trans hε0 hεt
  refine (abs_prod_le_of_card_cross hσ S w hcross hnear hfar hcdef.symm).trans ?_
  -- `nlinarith` is not in scope here: this file's imports are the combinatorial ones and pull in
  -- no nonlinear arithmetic tactic. The step is one `mul_le_mul` anyway.
  have hε2 : ε ^ 2 ≤ Ms * Mt := by
    rw [sq]
    exact mul_le_mul hεs hεt hε0 hMs0
  have key : (ε ^ 2) ^ t ≤ (Ms * Mt) ^ t := pow_le_pow_left₀ (sq_nonneg ε) hε2 t
  have hbase : (0:ℝ) ≤ Ms ^ ((S.card - c) / 2) * Mt ^ ((Sᶜ.card - c) / 2) * ε ^ 2 := by positivity
  have hlhs : Ms ^ ((S.card - c) / 2) * Mt ^ ((Sᶜ.card - c) / 2) * ε ^ c
      = Ms ^ ((S.card - c) / 2) * Mt ^ ((Sᶜ.card - c) / 2) * ε ^ 2 * (ε ^ 2) ^ t := by
    -- forwards on the LEFT: `ε^(2+2t) = ε^2 * (ε^2)^t`, then `ring` reassociates. Going
    -- backwards from the right fails, because `ε^2` sits inside the left factor and `pow_add`
    -- has no `ε^2 * ε^(2t)` subterm to match.
    rw [ht, pow_add, pow_mul]
    ring
  rw [hlhs]
  refine (mul_le_mul_of_nonneg_left key hbase).trans (le_of_eq ?_)
  rw [mul_pow, ← hA, ← hB, pow_add, pow_add]
  ring

end PairingKinds
