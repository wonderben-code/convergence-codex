import PlaqLocal
import SeriesBound

/-!
# Counting dual walks that END somewhere, and the geometric tail they carry

`UNLOCK_WATCHLIST`'s step **S3b-ii** — the entropy half of the boundary-reaching Peierls
estimate — is recorded there as blocked, in these words: *"their edge boundaries are dual
PATHS from boundary to boundary rather than circuits, and NOTHING in the estate counts those
— every count here (`WalkCount`, `PlaqLocal`, `PeierlsCover`) is for CLOSED walks."*

**Two thirds of that sentence are false, and this file is what is left once they are removed.**

* `WalkCount.card_finsetWalkLength_le` is stated `(u v : V)` — **between any two vertices**.
  The `4 ^ L` bound for closed walks is the special case `v = u`, not the general statement.
* `PlaqLocal.near_of_mem_support` and `near_endpoint` take a `Walk P Q` for arbitrary `Q`;
  only their `_closed` corollaries specialise.
* Only `PeierlsCover` is genuinely circuit-bound, because `cycCandidates` filters on
  `Walk.IsCycle`.

So the per-endpoint count for open dual paths was already proved. What was actually missing is
the step from one endpoint to a **set** of them, the size of that set on the box, and the
series. That is this file.

## What it proves

> **`card_walksTo_le`** — for any target set `T` of plaquettes, at most `|T| · 4 ^ L` dual
> walks of length `L` run from a fixed plaquette into `T`.
>
> **`card_bdryPlaq_le`** — the plaquettes touching the edge of the box number at most `4n`,
> so the prefactor is **linear in the side**, not in the area.
>
> **`sum_walksTo_bdry_le`** — hence, under `4 e^{-4β} ≤ 1/2`, the Peierls sum over dual walks
> of length `≥ L₀` from a fixed plaquette to the edge is at most `8 n (4 e^{-4β}) ^ L₀`.

The shape `8 n t^{L₀}` is exactly what step S5 of the route wants: a **surface** term. Summed
over the sites of the box with `L₀` growing like the distance to the edge, it is `O(n)` beside
the `n²` of the interior estimate.

## What is still missing, and it is now one statement rather than two

**The covering.** Nothing here says that a down cluster reaching the boundary *has* a long
dual walk to the edge inside its contour. That is the open-path analogue of
`PeierlsCover.cover_cycCandidates`, and it is the whole of S3b-ii now. It is a geometric
statement about the dual graph, not a counting one, and it is **not begun**.

Nothing in this file mentions the Ising measure. `IsingBoundaryField.MagnetisationBound` is
untouched, and `FieldBoundaryEnergy.down_prob_le_cluster_sum` — the inequality whose
right-hand side this would bound — is unchanged.
-/

namespace DualPathCount

open IsingFiniteVolume IsingContourEnergy DualObstruction PlaquetteLattice DualGraph
open PlaqLocal WalkCount

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. From one endpoint to a set of them -/

/-- **AT MOST `|T| · 4 ^ L` DUAL WALKS OF LENGTH `L` REACH `T` FROM `P`.** The per-endpoint
bound is `WalkCount.card_finsetWalkLength_le_four_pow`, which is already stated for arbitrary
endpoints; this is the sum of it over the targets. -/
theorem card_walksTo_le (σ : Config n) (P : Plaq n) (T : Finset (Plaq n)) (L : ℕ) :
    ∑ Q ∈ T, ((dualGraph σ).finsetWalkLength L P Q).card ≤ T.card * 4 ^ L := by
  calc ∑ Q ∈ T, ((dualGraph σ).finsetWalkLength L P Q).card
      ≤ ∑ _Q ∈ T, 4 ^ L :=
        Finset.sum_le_sum fun Q _ => card_finsetWalkLength_le_four_pow σ L P Q
    _ = T.card * 4 ^ L := by rw [Finset.sum_const, smul_eq_mul]

/-! ## 2. The plaquettes at the edge of the box, and there are `O(n)` of them -/

/-- A plaquette at the edge of the plaquette grid: one of its sides lies on the outer
boundary of the box. -/
def IsBdryPlaq (P : Plaq n) : Prop :=
  P.i = 0 ∨ P.i + 2 = n ∨ P.j = 0 ∨ P.j + 2 = n

/-- Those plaquettes, as a finite set. -/
noncomputable def bdryPlaq (n : ℕ) : Finset (Plaq n) :=
  Finset.univ.filter fun P => IsBdryPlaq P

@[simp] theorem mem_bdryPlaq {P : Plaq n} : P ∈ bdryPlaq n ↔ IsBdryPlaq P := by
  simp [bdryPlaq]

/-- **THE PREFACTOR IS LINEAR IN THE SIDE.** At most `4n` plaquettes touch the edge — the
count that makes step S5's surface term a surface term. The injection sends a plaquette to
the first edge it lies on together with its free coordinate; the "first" is what keeps corners
from colliding. -/
theorem card_bdryPlaq_le (n : ℕ) : (bdryPlaq n).card ≤ 4 * n := by
  classical
  have hinj : (bdryPlaq n).card ≤ ((Finset.range 4) ×ˢ (Finset.range n)).card := by
    refine Finset.card_le_card_of_injOn
      (fun P => if P.i = 0 then (0, P.j) else if P.i + 2 = n then (1, P.j)
        else if P.j = 0 then (2, P.i) else (3, P.i)) ?_ ?_
    · intro P hP
      rw [Finset.mem_coe, mem_bdryPlaq] at hP
      have hi := P.hi
      have hj := P.hj
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
      split_ifs <;> exact ⟨by omega, by omega⟩
    · intro P hP Q hQ hEq
      rw [Finset.mem_coe, mem_bdryPlaq] at hP hQ
      have e1 := congrArg Prod.fst hEq
      have e2 := congrArg Prod.snd hEq
      simp only at e1 e2
      refine Plaq.ext ?_ ?_ <;>
        · unfold IsBdryPlaq at hP hQ
          split_ifs at e1 e2 <;> omega
  calc (bdryPlaq n).card ≤ ((Finset.range 4) ×ˢ (Finset.range n)).card := hinj
    _ = 4 * n := by rw [Finset.card_product, Finset.card_range, Finset.card_range]

/-- **AT MOST `4 n · 4 ^ L` DUAL WALKS OF LENGTH `L` RUN FROM `P` TO THE EDGE.** -/
theorem card_walksTo_bdry_le (σ : Config n) (P : Plaq n) (L : ℕ) :
    ∑ Q ∈ bdryPlaq n, ((dualGraph σ).finsetWalkLength L P Q).card ≤ 4 * n * 4 ^ L :=
  le_trans (card_walksTo_le σ P _ L)
    (Nat.mul_le_mul_right _ (card_bdryPlaq_le n))

/-! ### The same sum over TRAILS, with the textbook constant

Added 2026-08-12 alongside `WalkCount` §1b. **Nothing downstream of here consumes it, and
`ERRATUM 126` records that this file is not on the threshold path at all** — it is imported
by `OuterFaceObstruction` and by nothing else. The sentence that stood here said these sums
were "the target half of the rethreading"; they are not, because the rethreading the
threshold needs happens in `PeierlsCover`, where a **cycle** count is bounded by throwing
the cycle hypothesis away. These statements are kept: they are true, they are the
boundary-route analogue, and the boundary route may yet want them.
-/

/-- **AT MOST `|T| · 4 · 3 ^ L` DUAL TRAILS OF LENGTH `L + 1` REACH `T` FROM `P`.** -/
theorem card_trailsTo_le (σ : Config n) (P : Plaq n) (T : Finset (Plaq n)) (L : ℕ) :
    ∑ Q ∈ T, (((dualGraph σ).finsetWalkLength (L + 1) P Q).filter fun p => p.IsTrail).card
      ≤ T.card * (4 * 3 ^ L) := by
  calc ∑ Q ∈ T, (((dualGraph σ).finsetWalkLength (L + 1) P Q).filter fun p => p.IsTrail).card
      ≤ ∑ _Q ∈ T, 4 * 3 ^ L :=
        Finset.sum_le_sum fun Q _ => card_trails_le_three_pow σ L P Q
    _ = T.card * (4 * 3 ^ L) := by rw [Finset.sum_const, smul_eq_mul]

/-- **AND AT MOST `4 n · 4 · 3 ^ L` OF THEM RUN FROM `P` TO THE EDGE**, against `4 n · 4 ^ (L+1)`
for walks. **Not consumed by anything**, and `ERRATUM 126`: the sentence that stood here
said the chain above still uses the walk count "because the walks it quantifies over are
not known to be trails where they are produced". The threshold chain does not run through
this file. See `WalkCount` §4. -/
theorem card_trailsTo_bdry_le (σ : Config n) (P : Plaq n) (L : ℕ) :
    ∑ Q ∈ bdryPlaq n,
        (((dualGraph σ).finsetWalkLength (L + 1) P Q).filter fun p => p.IsTrail).card
      ≤ 4 * n * (4 * 3 ^ L) :=
  le_trans (card_trailsTo_le σ P _ L)
    (Nat.mul_le_mul_right _ (card_bdryPlaq_le n))

/-! ## 3. The geometric tail from a general starting length

`SeriesBound.geom_Ico_le` is the same sum from `L₀ = 3`, which is the minimum contour length
and the right floor for the interior estimate. The boundary-reaching estimate needs it from a
floor that grows with the distance to the edge, so the statement is redone for arbitrary `L₀`.
The proof is the same two lines. -/

/-- `∑_{L ∈ Ico L₀ M} t ^ L ≤ 2 t ^ L₀` for `0 ≤ t ≤ 1/2`, at any starting length. -/
theorem geom_Ico_le' (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (L₀ M : ℕ) :
    ∑ L ∈ Finset.Ico L₀ M, t ^ L ≤ 2 * t ^ L₀ := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hpow : ∀ k ∈ Finset.range (M - L₀), t ^ (L₀ + k) = t ^ L₀ * t ^ k :=
    fun k _ => pow_add t L₀ k
  rw [Finset.sum_congr rfl hpow, ← Finset.mul_sum, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg ht0 L₀)
  calc ∑ k ∈ Finset.range (M - L₀), t ^ k
      ≤ ∑ k ∈ Finset.range (M - L₀), (1 / 2 : ℝ) ^ k :=
        Finset.sum_le_sum fun k _ => pow_le_pow_left₀ ht0 ht k
    _ ≤ 2 := sum_geometric_two_le _

/-- **THE ENTROPY INPUT FOR S3b-ii, SUMMED.** Under the explicit threshold
`4 e^{-4β} ≤ 1/2`, the Peierls sum over dual walks of length at least `L₀` from a fixed
plaquette to the edge of the box is at most `8 n (4 e^{-4β}) ^ L₀`.

The prefactor is **linear in the side of the box** and the tail is **geometric in `L₀`**,
which is the pair of properties step S5 needs to turn this into an `O(n)` surface term.

**It is an entropy bound and nothing else.** No configuration appears in it beyond the `σ`
naming the dual graph, and nothing here says a boundary-reaching cluster produces such a walk
— that covering is the remaining content of S3b-ii. -/
theorem sum_walksTo_bdry_le (σ : Config n) (P : Plaq n) {β : ℝ}
    (hβ : 4 * Real.exp (-(4 * β)) ≤ 1 / 2) (L₀ M : ℕ) :
    ∑ L ∈ Finset.Ico L₀ M,
        ((∑ Q ∈ bdryPlaq n, ((dualGraph σ).finsetWalkLength L P Q).card : ℕ) : ℝ)
          * Real.exp (-(4 * β) * (L : ℝ))
      ≤ 8 * n * (4 * Real.exp (-(4 * β))) ^ L₀ := by
  classical
  set q : ℝ := Real.exp (-(4 * β)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hterm : ∀ L ∈ Finset.Ico L₀ M,
      ((∑ Q ∈ bdryPlaq n, ((dualGraph σ).finsetWalkLength L P Q).card : ℕ) : ℝ)
          * Real.exp (-(4 * β) * (L : ℝ))
        ≤ (4 * n : ℝ) * (4 * q) ^ L := by
    intro L _
    have hcount : ((∑ Q ∈ bdryPlaq n, ((dualGraph σ).finsetWalkLength L P Q).card : ℕ) : ℝ)
        ≤ ((4 * n * 4 ^ L : ℕ) : ℝ) := by
      exact_mod_cast card_walksTo_bdry_le σ P L
    have hexp : Real.exp (-(4 * β) * (L : ℝ)) = q ^ L := by
      rw [hq, ← Real.exp_nat_mul]
      congr 1
      ring
    calc ((∑ Q ∈ bdryPlaq n, ((dualGraph σ).finsetWalkLength L P Q).card : ℕ) : ℝ)
          * Real.exp (-(4 * β) * (L : ℝ))
        ≤ ((4 * n * 4 ^ L : ℕ) : ℝ) * q ^ L := by
          rw [hexp]
          exact mul_le_mul_of_nonneg_right hcount (pow_nonneg hq0.le L)
      _ = (4 * n : ℝ) * (4 * q) ^ L := by push_cast; ring
  calc ∑ L ∈ Finset.Ico L₀ M,
        ((∑ Q ∈ bdryPlaq n, ((dualGraph σ).finsetWalkLength L P Q).card : ℕ) : ℝ)
          * Real.exp (-(4 * β) * (L : ℝ))
      ≤ ∑ L ∈ Finset.Ico L₀ M, (4 * n : ℝ) * (4 * q) ^ L := Finset.sum_le_sum hterm
    _ = (4 * n : ℝ) * ∑ L ∈ Finset.Ico L₀ M, (4 * q) ^ L := by rw [Finset.mul_sum]
    _ ≤ (4 * n : ℝ) * (2 * (4 * q) ^ L₀) := by
        refine mul_le_mul_of_nonneg_left (geom_Ico_le' _ (by positivity) hβ L₀ M) ?_
        positivity
    _ = 8 * n * (4 * q) ^ L₀ := by ring

/-- The threshold used above is implied by the one the interior estimate already runs under,
so the two halves of the route can be taken at the same temperature. -/
theorem threshold_of_eight {β : ℝ} (hβ : 8 * Real.exp (-(4 * β)) ≤ 1 / 2) :
    4 * Real.exp (-(4 * β)) ≤ 1 / 2 := by
  have := Real.exp_pos (-(4 * β))
  linarith

end DualPathCount
