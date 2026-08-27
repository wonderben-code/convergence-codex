import LatticeTruncatedKinds

/-!
# The bound class by class in the crossing number, instead of at the worst class

Every bound in this line ends the same way: `Finset.sum_le_card_nsmul`, which replaces **every**
crossing pairing by the worst one and multiplies by how many there are. `PairingKinds` already
proves the per-term bound at each crossing number `c`,

```
|∏ w| ≤ Ms^((|S|−c)/2) · Mt^((|Sᶜ|−c)/2) · ε^c        (`abs_prod_le_of_card_cross`)
```

and `LatticeTruncatedKinds` then throws `c` away by taking `c = 2`, the smallest it can be. **This
file does not throw it away.** The crossing pairings are partitioned by their crossing number and
each class is bounded at its own `c`:

```
|truncated| ≤ ∑_c  #{σ crossing with exactly c crossings} · Ms^((|S|−c)/2)·Mt^((|Sᶜ|−c)/2)·ε^c.
```

**This is strictly sharper wherever `ε` is smaller than `Ms` and `Mt`**, which is the regime the
bound exists for — `ε` is the propagator ACROSS the split, small by separation, and `Ms`, `Mt`
bound it within each side. The old bound charges every class the `c = 2` price; this one charges
the `c = 5` class `ε⁵`.

**AND THE CLASS COUNTS ARE LEFT AS COUNTS.** `#{σ : crossCard σ = c}` is written as a
`Finset.card` and not evaluated. Evaluating it — a formula in `|S|`, `k` and `c` — is the project
`LatticeTruncatedExplicit`'s record named and deferred, and it is still deferred: **this file
sharpens the bound without it**, which is the useful half and the half that was not obvious.

## What is proved

* `crossCard`, `crossing` — the crossing number of a pairing, and the pairings that cross;
* **`abs_integral_prod_sub_mul_le_byCross`** — the class-by-class bound;
* `crossCard_ne_zero` and `two_le_crossCard_of_even` — the `c = 0` class is empty because `c = 0`
  IS respecting the split, and at even `|S|` the `c = 1` class is empty by parity. **So the sum
  really does start at `c = 2` there**, which is where the sharp exponent came from and is now
  visible in the statement rather than argued for in a proof;
* `card_crossClass_fin_four` and **`byCross_fin_four`** — the instance where the counts ARE known:
  at `Fin 4` split `{0,1}` every crossing pairing has `c = 2` and there are two, so the bound is
  `2 ε²` with `Ms` and `Mt` at the power `0` and absent from the conclusion — exactly
  `LatticeTruncatedCount`'s numeral, reached from the classes;
* **`byCross_le_kinds`** — the check. The class-by-class bound is **at most** the worst-class bound
  of `LatticeTruncatedKinds`, given `ε ≤ Ms` and `ε ≤ Mt`. It is a comparison of the two
  right-hand sides, so it is a statement about the sharpening and not another instance of it.

## What is NOT here

**No count is evaluated**, so nothing here is a closed form. **Nothing is claimed about `k` odd**,
where `LatticeTruncatedContent` shows the whole quantity is `0` and every bound in this line is
`0 ≤ 0`. Finite volume throughout. **No wall moves. No published tag moves.**
-/

namespace LatticeTruncatedByCross

open Equiv Function Involutions PairWeightRep PairingSplit PairingSharp PairingParity PairingKinds
open PairingCluster LatticeTruncatedKinds
open MeasureTheory ProbabilityTheory GraphLaplacian
open LatticeIsserlisSmeared WickPairings

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The crossing number as a function on pairings -/

/-- How many pairs of `σ` cross the split `S`, counted at the representatives below their
partners. `PairingSharp.card_crossSet` identifies it with `|{i ∈ S : σ i ∉ S}|`. -/
def crossCard {k : ℕ} (S : Finset (Fin k)) (σ : ↑(perfectMatchings (Fin k))) : ℕ :=
  (crossSet σ.1 S (Finset.univ.filter (fun i => i < σ.1 i))).card

/-- The pairings that cross the split — the index set of `PairingCluster.integral_prod_sub_mul_eq`'s
sum, named so that the partition below can be stated. -/
def crossing {k : ℕ} (S : Finset (Fin k)) : Finset ↑(perfectMatchings (Fin k)) :=
  Finset.univ.filter (fun σ => ¬ RespectsSplit S σ.1)

theorem crossCard_le {k : ℕ} (S : Finset (Fin k)) (σ : ↑(perfectMatchings (Fin k))) :
    crossCard S σ ≤ S.card :=
  card_cross_le σ.2 S

/-- **`c = 0` IS RESPECTING THE SPLIT**, so no member of `crossing` has crossing number zero. -/
theorem crossCard_ne_zero {k : ℕ} {S : Finset (Fin k)} {σ : ↑(perfectMatchings (Fin k))}
    (hσ : σ ∈ crossing S) : crossCard S σ ≠ 0 := by
  have hns : ¬ RespectsSplit S σ.1 := (Finset.mem_filter.mp hσ).2
  rw [crossCard, card_crossSet σ.2 (isRepSet_filter_lt σ.2.1)]
  have h := Finset.card_pos.mpr (cross_nonempty_of_not_respects σ.2 hns)
  omega

/-- The crossing number carries the parity of `|S|` (`PairingParity.card_cross_parity`), which is
what makes the `c` odd classes empty at even `|S|` and is the arithmetic §3 runs on. -/
theorem crossCard_parity {k : ℕ} (S : Finset (Fin k)) (σ : ↑(perfectMatchings (Fin k))) :
    crossCard S σ % 2 = S.card % 2 := by
  rw [crossCard, card_crossSet σ.2 (isRepSet_filter_lt σ.2.1)]
  exact card_cross_parity σ.2 S

/-- **AND AT EVEN `|S|` THE `c = 1` CLASS IS EMPTY TOO**, by the parity argument
(`PairingParity.two_le_card_cross`). So the sum below starts at `c = 2`, which is where the sharp
exponent of `LatticeTruncatedSharp` comes from — visible in the statement rather than buried in a
proof. -/
theorem two_le_crossCard_of_even {k : ℕ} {S : Finset (Fin k)} (hS : Even S.card)
    {σ : ↑(perfectMatchings (Fin k))} (hσ : σ ∈ crossing S) : 2 ≤ crossCard S σ := by
  have hns : ¬ RespectsSplit S σ.1 := (Finset.mem_filter.mp hσ).2
  rw [crossCard, card_crossSet σ.2 (isRepSet_filter_lt σ.2.1)]
  exact two_le_card_cross σ.2 hS (cross_nonempty_of_not_respects σ.2 hns)

/-! ## 2. The bound, class by class -/

/-- **THE CLASS-BY-CLASS BOUND.** `PairingCluster.integral_prod_sub_mul_eq` makes the truncated
correlation the sum over the crossing pairings; `Finset.sum_fiberwise_of_maps_to` partitions that
sum by crossing number; and `PairingKinds.abs_prod_le_of_card_cross` bounds each class at **its
own** `c` instead of at the smallest one.

**AND IT CARRIES FEWER HYPOTHESES THAN THE BOUND IT SHARPENS.**
`LatticeTruncatedKinds.abs_integral_prod_sub_mul_le_kinds` needs `0 ≤ Ms`, `0 ≤ Mt`,
`ε² ≤ Ms·Mt` and `Even S.card`; this needs **none of the four**. A draft stated all of them, the
build reported every one unused, and they were removed rather than silenced. The reason is
structural: charging each class its own `c` never compares two different exponents, and it is the
comparison that wanted the side conditions. They come back in §3, where a comparison is exactly
what is being made. -/
theorem abs_integral_prod_sub_mul_le_byCross (hm : m ≠ 0) {k : ℕ}
    (a : Fin k → EuclideanSpace ℝ V) (S : Finset (Fin k)) {ε Ms Mt : ℝ}
    (hcross : ∀ i ∈ S, ∀ j ∉ S, |dotG G m (a i) (a j)| ≤ ε)
    (hnear : ∀ i ∈ S, ∀ j ∈ S, |dotG G m (a i) (a j)| ≤ Ms)
    (hfar : ∀ i ∉ S, ∀ j ∉ S, |dotG G m (a i) (a j)| ≤ Mt) :
    |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin k // x ∈ S}, (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin k // y ∉ S}, (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))|
      ≤ ∑ c ∈ Finset.range (S.card + 1),
          (((crossing S).filter (fun σ => crossCard S σ = c)).card : ℝ)
            * (Ms ^ ((S.card - c) / 2) * Mt ^ ((Sᶜ.card - c) / 2) * ε ^ c) := by
  classical
  rw [integral_prod_sub_mul_eq hm a S]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hmaps : ∀ σ ∈ crossing S, crossCard S σ ∈ Finset.range (S.card + 1) := fun σ _ =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (crossCard_le S σ))
  -- the sum arrives over the raw filter; `crossing S` is that filter by `rfl`, but `rw` matches
  -- syntactically and will not see through the definition, so it is named first
  rw [show (Finset.univ.filter
      (fun σ : ↑(perfectMatchings (Fin k)) => ¬ RespectsSplit S σ.1)) = crossing S from rfl,
    ← Finset.sum_fiberwise_of_maps_to hmaps
    (fun σ => |∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), dotG G m (a i) (a (σ.1 i))|)]
  refine Finset.sum_le_sum fun c _ => ?_
  have hterm : ∀ σ ∈ (crossing S).filter (fun σ => crossCard S σ = c),
      |∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), dotG G m (a i) (a (σ.1 i))|
        ≤ Ms ^ ((S.card - c) / 2) * Mt ^ ((Sᶜ.card - c) / 2) * ε ^ c := by
    intro σ hσ
    refine abs_prod_le_of_card_cross σ.2 S (fun i j => dotG G m (a i) (a j)) ?_ ?_ ?_
      (Finset.mem_filter.mp hσ).2
    · -- the two directions of "exactly one end is in `S`"; the second needs `dotG` symmetric
      intro i hi
      dsimp only
      by_cases hiS : i ∈ S
      · exact hcross i hiS (σ.1 i) (fun h => hi (iff_of_true hiS h))
      · have hσi : σ.1 i ∈ S := by
          by_contra h
          exact hi (iff_of_false hiS h)
        rw [dotG_comm hm]
        exact hcross (σ.1 i) hσi i hiS
    · intro i hiS hσi
      dsimp only
      exact hnear i hiS (σ.1 i) hσi
    · intro i hiS hσi
      dsimp only
      exact hfar i hiS (σ.1 i) hσi
  have := Finset.sum_le_card_nsmul _ _ _ hterm
  rwa [nsmul_eq_mul] at this

/-! ## 3. The check: it really is at least as good -/

/-- **AND IT IS AT LEAST AS GOOD AS THE WORST-CLASS BOUND.** A comparison of the two right-hand
sides under `LatticeTruncatedKinds`' own hypotheses — `ε² ≤ Ms·Mt`, and both sides of the split of
even size. Class by class: at even `|S|` the crossing number is even and at least `2`, so writing
`2a + c = |S|` and `2b + c = |Sᶜ|` the class at `c` pays `Ms^a·Mt^b·ε^c` where the old bound
charges `Ms^(a+t)·Mt^(b+t)·ε²` with `t = (c−2)/2`, and `ε^(2t) ≤ (Ms·Mt)^t` is exactly `hε2`
raised to `t`. The counts then add back up to the old count, because the classes partition
`crossing S`.

**It is a comparison and not another instance**, so it says the sharpening is a sharpening rather
than a differently-shaped bound of unknown strength. Equality holds when every crossing pairing
has `c = 2`, which is the case `LatticeTruncatedCount` computes at `Fin 4`. -/
theorem byCross_le_kinds {k : ℕ} (S : Finset (Fin k)) (hS : Even S.card) (hT : Even Sᶜ.card)
    {ε Ms Mt : ℝ} (hMs0 : 0 ≤ Ms) (hMt0 : 0 ≤ Mt) (hε2 : ε ^ 2 ≤ Ms * Mt) :
    (∑ c ∈ Finset.range (S.card + 1),
        (((crossing S).filter (fun σ => crossCard S σ = c)).card : ℝ)
          * (Ms ^ ((S.card - c) / 2) * Mt ^ ((Sᶜ.card - c) / 2) * ε ^ c))
      ≤ ((crossing S).card : ℝ)
          * (Ms ^ ((S.card - 2) / 2) * Mt ^ ((Sᶜ.card - 2) / 2) * ε ^ 2) := by
  classical
  have hK0 : (0 : ℝ) ≤ Ms ^ ((S.card - 2) / 2) * Mt ^ ((Sᶜ.card - 2) / 2) * ε ^ 2 := by positivity
  have hterm : ∀ c ∈ Finset.range (S.card + 1),
      (((crossing S).filter (fun σ => crossCard S σ = c)).card : ℝ)
          * (Ms ^ ((S.card - c) / 2) * Mt ^ ((Sᶜ.card - c) / 2) * ε ^ c)
        ≤ (((crossing S).filter (fun σ => crossCard S σ = c)).card : ℝ)
            * (Ms ^ ((S.card - 2) / 2) * Mt ^ ((Sᶜ.card - 2) / 2) * ε ^ 2) := by
    intro c _
    rcases Finset.eq_empty_or_nonempty ((crossing S).filter (fun σ => crossCard S σ = c)) with
      h | ⟨σ, hσ⟩
    · rw [h]; simp
    -- a nonempty class hands over a `σ`, and every arithmetic fact below comes from it
    have hmem : σ ∈ crossing S := (Finset.mem_filter.mp hσ).1
    have hcc : crossCard S σ = c := (Finset.mem_filter.mp hσ).2
    have h2c : 2 ≤ c := hcc ▸ two_le_crossCard_of_even hS hmem
    have hpar : c % 2 = 0 := by
      have := crossCard_parity S σ
      rw [hcc, Nat.even_iff.mp hS] at this
      exact this
    have hna := two_mul_card_nearSet_add_card_cross σ.2 S
    have hfa := two_mul_card_farSet_add_card_cross σ.2 S
    rw [show (crossSet σ.1 S (Finset.univ.filter (fun i => i < σ.1 i))).card = c from hcc]
      at hna hfa
    -- `(|S| − c)/2 = a` and `(|S| − 2)/2 = a + (c−2)/2`, and the same on the far side
    have hes : (S.card - c) / 2 + (c - 2) / 2 = (S.card - 2) / 2 := by omega
    have het : (Sᶜ.card - c) / 2 + (c - 2) / 2 = (Sᶜ.card - 2) / 2 := by
      have hTe := Nat.even_iff.mp hT
      omega
    have hεc : ε ^ c = ε ^ 2 * (ε ^ 2) ^ ((c - 2) / 2) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    -- rewrite only the two exponents and `ε ^ c`; rewriting `c` itself would also hit the
    -- exponents `(|S| − c)/2` and `(|Sᶜ| − c)/2`, which is what a first draft did
    rw [← hes, ← het, pow_add, pow_add, hεc]
    calc Ms ^ ((S.card - c) / 2) * Mt ^ ((Sᶜ.card - c) / 2) * (ε ^ 2 * (ε ^ 2) ^ ((c - 2) / 2))
        = Ms ^ ((S.card - c) / 2) * Mt ^ ((Sᶜ.card - c) / 2) * ε ^ 2 * (ε ^ 2) ^ ((c - 2) / 2) := by
          ring
      _ ≤ Ms ^ ((S.card - c) / 2) * Mt ^ ((Sᶜ.card - c) / 2) * ε ^ 2 * (Ms * Mt) ^ ((c - 2) / 2) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hε2 _) (by positivity)
      _ = Ms ^ ((S.card - c) / 2) * Ms ^ ((c - 2) / 2)
            * (Mt ^ ((Sᶜ.card - c) / 2) * Mt ^ ((c - 2) / 2)) * ε ^ 2 := by
          rw [mul_pow]; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul, ← Nat.cast_sum]
  refine mul_le_mul_of_nonneg_right ?_ hK0
  have hmaps : ∀ σ ∈ crossing S, crossCard S σ ∈ Finset.range (S.card + 1) := fun σ _ =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (crossCard_le S σ))
  exact_mod_cast le_of_eq (Finset.card_eq_sum_card_fiberwise hmaps).symm


/-! ## 4. The instance where the counts are known -/

set_option maxRecDepth 8000 in
/-- **AT `Fin 4` SPLIT `{0,1}` EVERY CROSSING PAIRING HAS `c = 2`, AND THERE ARE TWO OF THEM.**
By `decide` over the three matchings of `Fin 4`. This is the arithmetic behind
`LatticeTruncatedCount`'s numeral `2`, now as a statement about the classes. -/
theorem card_crossClass_fin_four (c : ℕ) :
    ((crossing ({0, 1} : Finset (Fin 4))).filter
        (fun σ => crossCard ({0, 1} : Finset (Fin 4)) σ = c)).card
      = if c = 2 then 2 else 0 := by
  match c with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | (n + 3) =>
    simp only [if_neg (by omega : n + 3 ≠ 2)]
    refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun σ hσ hcc => ?_)
    have := crossCard_le ({0, 1} : Finset (Fin 4)) σ
    rw [hcc] at this
    simp only [show ({0, 1} : Finset (Fin 4)).card = 2 from rfl] at this
    omega

/-- **AND THE CLASS-BY-CLASS BOUND RETURNS `LatticeTruncatedCount`'s `2` AT ORDER FOUR**, with
`Ms` and `Mt` raised to the power `0` and so absent from the conclusion. The two bounds agree
exactly at the one place the estate has computed the constant by hand, which is the check. -/
theorem byCross_fin_four (hm : m ≠ 0) (a : Fin 4 → EuclideanSpace ℝ V) {ε M : ℝ}
    (hcross : ∀ i ∈ ({0, 1} : Finset (Fin 4)), ∀ j ∉ ({0, 1} : Finset (Fin 4)),
      |dotG G m (a i) (a j)| ≤ ε)
    (hall : ∀ i j, |dotG G m (a i) (a j)| ≤ M) :
    |∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) ∂(gaussianField G m)
        - (∫ ω, (∏ x : {x : Fin 4 // x ∈ ({0, 1} : Finset (Fin 4))},
              (inner ℝ (a x) ω : ℝ)) ∂(gaussianField G m))
          * (∫ ω, (∏ y : {y : Fin 4 // y ∉ ({0, 1} : Finset (Fin 4))},
              (inner ℝ (a y) ω : ℝ)) ∂(gaussianField G m))|
      ≤ 2 * ε ^ 2 := by
  have h := abs_integral_prod_sub_mul_le_byCross (G := G) hm a ({0, 1} : Finset (Fin 4))
    (ε := ε) (Ms := M) (Mt := M) hcross (fun i _ j _ => hall i j) (fun i _ j _ => hall i j)
  refine h.trans (le_of_eq ?_)
  rw [show ({0, 1} : Finset (Fin 4)).card = 2 from rfl,
    show (({0, 1} : Finset (Fin 4))ᶜ).card = 2 from rfl]
  simp only [card_crossClass_fin_four, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

end LatticeTruncatedByCross
