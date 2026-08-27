import WickPairings
import PairWeightRep

/-!
# The pairing side of Isserlis, recursive, at the index type the theorem actually uses

`PairWeightRep.sum_prod_perfectMatchings_option` is Wick's recursion on the pairing side at index
type `Option α`, and `WickPairings.IsserlisGeneral` sums `pairProduct` over
`perfectMatchings (Fin k)`. This file carries the first to the second.

## What the carrying costs, and why it was worth naming separately

`PairWeightRep` recorded the bridge as *"bookkeeping rather than mathematics — a claim about its
KIND and not about its size"*, and declined to estimate it (`ERRATUM 194`). Here is what it turned
out to be: `IsRepSet` transports along an `Equiv` (§1), `pairProduct` is a representative-set
product at any representative set (§2, off `PairWeightRep.prod_repSet_eq` and
`LatticeIsserlisSmeared.dotG_comm`), and the two together move the recursion across
`finSuccEquiv` (§3). No new idea appears; the classification was right.

## What is proved

* `isRepSet_permCongr`, `prod_repSet_permCongr` — representative sets and their products
  transport along any `Equiv`;
* **`pairProduct_eq_prod_repSet`** — `WickPairings.pairProduct` equals the product over **any**
  representative set of the pairing. This is what makes the `<`-device an implementation detail
  rather than part of the statement;
* **`sum_pairProduct_succ`** — **the recursion**: the pairing sum over `Fin (k+1)` is, for each
  `b : Fin k`, `⟨f 0, G f b.succ⟩` times the pairing sum of the rest;
* `perfectMatchings_fin_two_prod`, `recursion_rhs_fin_one`, `sum_pairProduct_two_consistent` —
  the recursion **evaluated at its smallest non-empty case from both ends**: the left side by
  enumerating the pairings of `Fin 2`, the right by enumerating the involutions of `Fin 1`,
  neither using the recursion. A specialisation of a theorem is not a check of it, and the two
  independent reductions are. **The check's own limitation is stated with it**: neither side needs
  `m ≠ 0`, so neither exercises `dotG_comm` — at two indices there is one pair and nothing to
  reorder, so an error in the symmetry-dependent half would survive it.

**WHAT IS STILL NOT PROVED, AND IT IS NOW EXACTLY ONE THING.** Everything above is a recursion
obeyed by the RIGHT-hand side of `IsserlisGeneral`. **The left-hand side — the Gaussian integral
`∫ ∏ᵢ⟪fᵢ,ω⟫` — obeys no proved recursion at general order in this estate.** That is the ladder,
whose analytic half is `LatticeSteinMajorant` and whose closed-form derivative is untouched. Until
the two sides are matched, general Isserlis follows from none of this, and **no estimate is
offered** (`ERRATUM 194`).
-/

namespace PairingRecursion

open Equiv Function Involutions PairWeightRep WickPairings
open LatticeIsserlisSmeared

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Representative sets transport along an equivalence -/

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] in
/-- Relabelling the index set relabels a representative set. -/
theorem isRepSet_permCongr (e : ι ≃ κ) {σ : Equiv.Perm ι} {S : Finset ι}
    (h : IsRepSet σ S) : IsRepSet (e.permCongr σ) (S.image e) := by
  have hap : ∀ x : κ, (e.permCongr σ) x = e (σ (e.symm x)) := fun x => by
    simp [Equiv.permCongr_apply]
  have hmem : ∀ x : κ, x ∈ S.image e ↔ e.symm x ∈ S := by
    intro x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩; simpa using hi
    · intro hx; exact ⟨e.symm x, hx, by simp⟩
  constructor
  · intro x hx
    rw [hap]
    have := h.ne ((hmem x).mp hx)
    exact fun hc => this (e.injective (by simpa using hc))
  · intro x hmv
    rw [hap] at hmv ⊢
    rw [hmem, hmem]
    simp only [Equiv.symm_apply_apply]
    exact h.2 _ (fun hc => hmv (by rw [hc]; simp))

omit [Fintype ι] [Fintype κ] [DecidableEq ι] in
/-- And the product over it is the product over the original. -/
theorem prod_repSet_permCongr {M : Type*} [CommMonoid M] (e : ι ≃ κ) (σ : Equiv.Perm ι)
    (S : Finset ι) (w : κ → κ → M) :
    ∏ x ∈ S.image e, w x ((e.permCongr σ) x) = ∏ i ∈ S, w (e i) (e (σ i)) := by
  rw [Finset.prod_image (fun x _ y _ h => e.injective h)]
  exact Finset.prod_congr rfl fun i _ => by simp [Equiv.permCongr_apply]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- Relabelling and relabelling back is the identity. -/
theorem permCongr_symm_permCongr (e : ι ≃ κ) (τ : Equiv.Perm κ) :
    e.permCongr (e.symm.permCongr τ) = τ := by
  ext x; simp [Equiv.permCongr_apply]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- `Involutions.perfectMatchingsCongr` is `permCongr` on the underlying permutation. -/
theorem perfectMatchingsCongr_coe (e : ι ≃ κ) (σ : ↑(perfectMatchings ι)) :
    ((perfectMatchingsCongr e) σ).1 = e.permCongr σ.1 := rfl

/-! ## 2. `pairProduct` is the representative-set product, at any representatives

`LatticeIsserlisSmeared.dotG_comm` is the symmetry `PairWeightRep.prod_repSet_eq` needs, and the
`<`-device is a representative set by `PairWeightRep.isRepSet_filter_lt`. -/

/-- **THE `<`-DEVICE IS AN IMPLEMENTATION DETAIL.** -/
theorem pairProduct_eq_prod_repSet (hm : m ≠ 0) {k : ℕ} (f : Fin k → EuclideanSpace ℝ V)
    {σ : Equiv.Perm (Fin k)} (hσ : σ ∈ involutions (Fin k)) {S : Finset (Fin k)}
    (hS : IsRepSet σ S) :
    pairProduct G m f σ = ∏ i ∈ S, dotG G m (f i) (f (σ i)) := by
  rw [pairProduct]
  exact prod_repSet_eq hσ (fun i j => dotG_comm (G := G) hm (f i) (f j))
    (isRepSet_filter_lt hσ) hS

/-! ## 3. The recursion, carried to `Fin (k+1)` -/

/-- **THE PAIRING-SIDE RECURSION AT `Fin (k+1)`.** Each pairing of `k+1` indices joins `0` to some
`b.succ` and pairs the rest; the sum factors accordingly. `finSuccEquiv` is the relabelling,
§1 carries the representatives across it, §2 says `pairProduct` does not notice, and
`PairWeightRep.sum_prod_perfectMatchings_option` is the recursion being carried. -/
theorem sum_pairProduct_succ (hm : m ≠ 0) {k : ℕ} (f : Fin (k + 1) → EuclideanSpace ℝ V) :
    ∑ σ : ↑(perfectMatchings (Fin (k + 1))), pairProduct G m f σ.1
      = ∑ b : Fin k, dotG G m (f 0) (f b.succ)
          * ∑ g : ↑(onlyFixing b),
              ∏ i ∈ Finset.univ.filter (fun i => i < g.1 i),
                dotG G m (f i.succ) (f (g.1 i).succ) := by
  classical
  set e : Fin (k + 1) ≃ Option (Fin k) := finSuccEquiv k with he
  set w : Option (Fin k) → Option (Fin k) → ℝ :=
    fun x y => dotG G m (f (e.symm x)) (f (e.symm y)) with hw
  have hwsymm : ∀ x y, w x y = w y x := fun x y => by
    simpa [hw] using dotG_comm (G := G) hm (f (e.symm x)) (f (e.symm y))
  -- the representative choices: transport the `<`-device on `Fin (k+1)`, and use it on `Fin k`.
  set rep : Equiv.Perm (Option (Fin k)) → Finset (Option (Fin k)) :=
    fun τ => (Finset.univ.filter
      (fun i : Fin (k + 1) => i < (e.symm.permCongr τ) i)).image e with hrepdef
  have hrep : ∀ τ ∈ perfectMatchings (Option (Fin k)), IsRepSet τ (rep τ) := by
    intro τ hτ
    have hinv : (e.symm.permCongr τ) ∈ involutions (Fin (k + 1)) :=
      ((perfectMatchingsCongr e.symm) ⟨τ, hτ⟩).2.1
    have h := isRepSet_permCongr e (isRepSet_filter_lt hinv)
    rw [permCongr_symm_permCongr] at h
    simpa [hrepdef] using h
  have hrepα : ∀ (b : Fin k) (g : Equiv.Perm (Fin k)), g ∈ onlyFixing b →
      IsRepSet g (Finset.univ.filter (fun i => i < g i)) :=
    fun b g hg => isRepSet_filter_lt hg.1
  have hmain := sum_prod_perfectMatchings_option (α := Fin k) w hwsymm rep hrep
    (fun g => Finset.univ.filter (fun i => i < g i)) hrepα
  -- the left side of `hmain` is the pairing sum over `Fin (k+1)`, relabelled
  have hleft : ∑ σ : ↑(perfectMatchings (Fin (k + 1))), pairProduct G m f σ.1
      = ∑ τ : ↑(perfectMatchings (Option (Fin k))), ∏ x ∈ rep τ.1, w x (τ.1 x) := by
    refine Fintype.sum_equiv (perfectMatchingsCongr e) _ _ fun σ => ?_
    have hσi : σ.1 ∈ involutions (Fin (k + 1)) := σ.2.1
    have hback : (e.symm.permCongr ((perfectMatchingsCongr e) σ).1) = σ.1 := by
      ext x; simp [perfectMatchingsCongr, Equiv.permCongr_apply]
    have hS : IsRepSet σ.1 (Finset.univ.filter (fun i : Fin (k + 1) => i < σ.1 i)) :=
      isRepSet_filter_lt hσi
    rw [pairProduct_eq_prod_repSet hm f hσi hS]
    have : rep ((perfectMatchingsCongr e) σ).1
        = (Finset.univ.filter (fun i : Fin (k + 1) => i < σ.1 i)).image e := by
      rw [hrepdef]; simp only [hback]
    rw [this]
    rw [show ((perfectMatchingsCongr e) σ).1 = e.permCongr σ.1 from rfl]
    rw [prod_repSet_permCongr e σ.1 _ w]
    · refine Finset.prod_congr ?_ fun i _ => by simp [hw]
      refine Finset.filter_congr fun i _ => ?_
      simp
  rw [hleft, hmain]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h0 : e.symm none = 0 := by simp [he]
  have hs : ∀ i : Fin k, e.symm (some i) = i.succ := by intro i; simp [he]
  simp only [hw, h0, hs]

/-! ## 4. The recursion evaluated, and compared with a directly computed answer

**A specialisation of a theorem is not a check of it.** `sum_pairProduct_succ` at `k + 1 = 4` is
the same statement with `k := 3` substituted, and proves nothing that was not already proved. A
check has to reduce **both** sides to a common closed form by routes that do not share a step.
`Fin 2` is where that is cheap, and it is done here rather than asserted for a larger `k` that
would be expensive. -/

/-- The one pairing of `Fin 2` is `swap 0 1`, and its representative set is `{0}`. **No mass
hypothesis is needed here, and that is a limitation of this check rather than a strength** — see
`sum_pairProduct_two_consistent`. -/
theorem perfectMatchings_fin_two_prod (f : Fin 2 → EuclideanSpace ℝ V) :
    ∑ σ : ↑(perfectMatchings (Fin 2)), pairProduct G m f σ.1 = dotG G m (f 0) (f 1) := by
  have hcard : Fintype.card ↑(perfectMatchings (Fin 2)) = 1 :=
    card_perfectMatchings_fin_two
  obtain ⟨σ, hσ⟩ := Fintype.card_eq_one_iff.mp hcard
  rw [Finset.sum_eq_single σ (fun b _ hb => absurd (hσ b) hb) (by simp)]
  have two_ne : ∀ y z : Fin 2, y ≠ z → y = 1 - z := by decide
  have hs : σ.1 = Equiv.swap 0 1 := by
    have h0 : σ.1 0 = 1 := by simpa using two_ne _ 0 (σ.2.2 0)
    have h1 : σ.1 1 = 0 := by simpa using two_ne _ 1 (σ.2.2 1)
    ext x
    fin_cases x
    · simp [h0]
    · simp [h1]
  have hfil : (Finset.univ.filter
      (fun i : Fin 2 => i < (Equiv.swap (0 : Fin 2) 1) i)) = {0} := by decide
  rw [pairProduct, hs, hfil]
  simp

/-- And the recursion's RIGHT-hand side at `k = 1`, computed from the other end: `Fin 1` has one
index, the involutions of `Fin 1` fixing only `0` are the identity alone, and its representative
set is empty, so the inner product is the empty product. -/
theorem recursion_rhs_fin_one (f : Fin 2 → EuclideanSpace ℝ V) :
    (∑ b : Fin 1, dotG G m (f 0) (f b.succ)
        * ∑ g : ↑(onlyFixing b), ∏ i ∈ Finset.univ.filter (fun i => i < g.1 i),
            dotG G m (f i.succ) (f (g.1 i).succ))
      = dotG G m (f 0) (f 1) := by
  have hprod : ∀ (b : Fin 1) (g : ↑(onlyFixing b)),
      (∏ i ∈ Finset.univ.filter (fun i => i < g.1 i),
        dotG G m (f i.succ) (f (g.1 i).succ)) = 1 := by
    intro b g
    have hemp : (Finset.univ.filter (fun i : Fin 1 => i < g.1 i)) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_lt]
      exact le_of_eq (Subsingleton.elim _ _)
    rw [hemp, Finset.prod_empty]
  have hone : ∀ b : Fin 1, Fintype.card ↑(onlyFixing b) = 1 := by decide
  simp only [Fin.sum_univ_one, hprod, Finset.sum_const, Finset.card_univ]
  rw [hone 0]
  simp

/-- **AND THE TWO COMPUTATIONS AGREE, WHICH IS THE CHECK.** `perfectMatchings_fin_two_prod`
reduces the left-hand side by enumerating the pairings of `Fin 2`; `recursion_rhs_fin_one` reduces
the right-hand side by enumerating the involutions of `Fin 1`. Neither uses `sum_pairProduct_succ`,
and the recursion says they are equal — so all three hold together only if the recursion is right.
A specialisation of `sum_pairProduct_succ` would have shown none of this.

**AND WHAT THIS CHECK CANNOT SEE, stated because the absence is visible in the statement.** Neither
side needs `m ≠ 0`, so **neither exercises `dotG_comm`** — and symmetry is the whole hypothesis
`PairWeightRep.prod_repSet_eq` runs on. At two indices there is one pair and nothing to reorder, so
an error in the symmetry-dependent half of the argument would survive this check untouched. The
smallest case that would see it is four indices, and it is not done here. -/
theorem sum_pairProduct_two_consistent (f : Fin 2 → EuclideanSpace ℝ V) :
    (∑ σ : ↑(perfectMatchings (Fin 2)), pairProduct G m f σ.1)
      = ∑ b : Fin 1, dotG G m (f 0) (f b.succ)
          * ∑ g : ↑(onlyFixing b), ∏ i ∈ Finset.univ.filter (fun i => i < g.1 i),
              dotG G m (f i.succ) (f (g.1 i).succ) := by
  rw [perfectMatchings_fin_two_prod f, recursion_rhs_fin_one f]

end PairingRecursion
