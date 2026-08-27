import PairingRecursion

/-!
# The recursion's consistency check at four indices, which is the first that could see a reordering

`PairingRecursion.sum_pairProduct_succ` is the pairing-side recursion, and that file checked it at
two indices by computing **both sides independently** — `perfectMatchings_fin_two_prod` by
enumerating the pairings of `Fin 2`, `recursion_rhs_fin_one` by enumerating the involutions of
`Fin 1` — and it named what that check could not see:

> Neither side needs `m ≠ 0`, so **neither exercises `dotG_comm`** — and symmetry is the whole
> hypothesis `PairWeightRep.prod_repSet_eq` runs on. At two indices there is one pair and nothing
> to reorder, so an error in the symmetry-dependent half of the argument would survive this check
> untouched. **The smallest case that would see it is four indices, and it is not done here.**

**This is four indices.** Both sides are computed independently, neither uses
`sum_pairProduct_succ`, and they agree:

```
∑_{σ ∈ pm(Fin 4)} pairProduct f σ  =  ⟨f₀,f₁⟩⟨f₂,f₃⟩ + ⟨f₀,f₂⟩⟨f₁,f₃⟩ + ⟨f₀,f₃⟩⟨f₁,f₂⟩
```

**AND THE PREDICTION IN THAT PARAGRAPH IS WRONG, WHICH IS THE FINDING.** Four indices does **not**
see a reordering. Neither theorem below takes `m ≠ 0`, neither uses `dotG_comm`, and the
symmetry-dependent half of `sum_pairProduct_succ` survives this check exactly as it survived the
two-index one — **that much is proved, by the two theorems below being stated without `m`.**

**Why, and this half is an argument rather than a theorem.** On the pairing side the representative
of a pair is its smaller end (`Finset.filter (· < σ ·)`). On the recursion side `0` is joined to
`b.succ`, which is larger, and the rest are relabelled by `Fin.succ`, which is order-preserving. So
both sides name every factor smaller-argument-first, and they never disagree about which end of a
pair comes first — **at any order, not just at four**. If that reading is right, no instance of
this check exercises `dotG_comm` and the symmetry-dependent half needs a different kind of test
altogether; §"What this does NOT do" says what that would be. **The reading is not formalised and
is not claimed as proved** — what is proved is the four-index instance, which is what
`PairingRecursion` asked for and what its prediction was about. That paragraph is annotated where
it stands (`ERRATUM 310`).

## What is proved

* `univ_perfectMatchings_fin_four` — the three pairings of `Fin 4`, by `decide`;
* **`perfectMatchings_fin_four_prod`** — the pairing side in closed form, by enumerating them;
* `univ_onlyFixing_fin_three_*` — the fibres `onlyFixing b` for each `b : Fin 3`, each a singleton;
* **`recursion_rhs_fin_three`** — the recursion side in closed form, by enumerating those;
* **`sum_pairProduct_four_consistent`** — the check the previous file named and declined.

## What this does NOT do

**It does not check the symmetry-dependent half**, which is the whole point of the finding above
and is why that half is still checked by nothing. What would see it is a weight `w` that is **not**
symmetric, run through the same two computations — and `PairWeightRep.prod_repSet_eq` takes
symmetry as a hypothesis, so the estate cannot state the two sides for such a `w` without first
generalising that file. **Named as the remaining leg rather than estimated** (`ERRATUM 194`).

**It is a check, not a proof of the recursion.** `sum_pairProduct_succ` is proved in the previous
file at every order; this agrees with it at one order by two routes that do not use it. Finite,
concrete, and no wall moves. **No published tag moves.**
-/

namespace PairingRecursionFour

open Equiv Function Involutions PairWeightRep PairingRecursion
open GraphLaplacian LatticeIsserlisSmeared WickPairings

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. A pairing's product, once its representative set is known -/

/-- `pairProduct` at a pairing whose representative set is a named two-element `Finset`. The
`rfl` is `WickPairings.pairProduct`'s definition; everything else is `Finset.prod_insert`. -/
theorem pairProduct_two (f : Fin 4 → EuclideanSpace ℝ V) (σ : Equiv.Perm (Fin 4)) (a b : Fin 4)
    (hfil : Finset.univ.filter (fun i => i < σ i) = ({a, b} : Finset (Fin 4))) (hab : a ≠ b) :
    pairProduct G m f σ = dotG G m (f a) (f (σ a)) * dotG G m (f b) (f (σ b)) := by
  rw [show pairProduct G m f σ
      = ∏ i ∈ Finset.univ.filter (fun i => i < σ i), dotG G m (f i) (f (σ i)) from rfl,
    hfil, Finset.prod_insert (by simpa using hab), Finset.prod_singleton]

/-! ## 2. The pairing side -/

set_option maxRecDepth 20000 in
/-- **THE THREE PAIRINGS OF `Fin 4`, NAMED.** `Involutions.card_perfectMatchings_fin_four` says
there are three; this says which three, which is what a sum needs. -/
theorem univ_perfectMatchings_fin_four :
    (Finset.univ : Finset ↑(perfectMatchings (Fin 4)))
      = {⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide⟩,
         ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by decide⟩,
         ⟨Equiv.swap 0 3 * Equiv.swap 1 2, by decide⟩} := by decide

set_option maxRecDepth 20000 in
/-- **THE PAIRING SIDE IN CLOSED FORM.** By enumeration — `sum_pairProduct_succ` is not used, which
is what makes the check below a check. **No `m ≠ 0`**: no factor is ever produced with its larger
argument first, so nothing here needs `dotG_comm`. -/
theorem perfectMatchings_fin_four_prod (f : Fin 4 → EuclideanSpace ℝ V) :
    (∑ σ : ↑(perfectMatchings (Fin 4)), pairProduct G m f σ.1)
      = dotG G m (f 0) (f 1) * dotG G m (f 2) (f 3)
        + dotG G m (f 0) (f 2) * dotG G m (f 1) (f 3)
        + dotG G m (f 0) (f 3) * dotG G m (f 1) (f 2) := by
  rw [univ_perfectMatchings_fin_four, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    pairProduct_two f _ 0 2 (by decide) (by decide),
    pairProduct_two f _ 0 1 (by decide) (by decide),
    pairProduct_two f _ 0 1 (by decide) (by decide)]
  norm_num [show (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 0 = 1 from by decide,
    show (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 2 = 3 from by decide,
    show (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) 0 = 2 from by decide,
    show (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) 1 = 3 from by decide,
    show (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) 0 = 3 from by decide,
    show (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) 1 = 2 from by decide]
  ring

/-! ## 3. The recursion side -/

set_option maxRecDepth 20000 in
theorem univ_onlyFixing_fin_three_zero :
    (Finset.univ : Finset ↑(onlyFixing (0 : Fin 3))) = {⟨Equiv.swap 1 2, by decide⟩} := by decide

set_option maxRecDepth 20000 in
theorem univ_onlyFixing_fin_three_one :
    (Finset.univ : Finset ↑(onlyFixing (1 : Fin 3))) = {⟨Equiv.swap 0 2, by decide⟩} := by decide

set_option maxRecDepth 20000 in
theorem univ_onlyFixing_fin_three_two :
    (Finset.univ : Finset ↑(onlyFixing (2 : Fin 3))) = {⟨Equiv.swap 0 1, by decide⟩} := by decide

set_option maxRecDepth 20000 in
/-- **THE RECURSION SIDE IN CLOSED FORM.** Each fibre `onlyFixing b` over `Fin 3` is a single
involution — the swap of the two points other than `b` — so each inner sum is one product of one
factor. **Again no `m ≠ 0`**, for the same reason: `Fin.succ` is order-preserving, so the
relabelled pair is named smaller-end-first here too. -/
theorem recursion_rhs_fin_three (f : Fin 4 → EuclideanSpace ℝ V) :
    (∑ b : Fin 3, dotG G m (f 0) (f b.succ)
        * ∑ g : ↑(onlyFixing b), ∏ i ∈ Finset.univ.filter (fun i => i < g.1 i),
            dotG G m (f i.succ) (f (g.1 i).succ))
      = dotG G m (f 0) (f 1) * dotG G m (f 2) (f 3)
        + dotG G m (f 0) (f 2) * dotG G m (f 1) (f 3)
        + dotG G m (f 0) (f 3) * dotG G m (f 1) (f 2) := by
  rw [Fin.sum_univ_three, univ_onlyFixing_fin_three_zero, univ_onlyFixing_fin_three_one,
    univ_onlyFixing_fin_three_two, Finset.sum_singleton, Finset.sum_singleton,
    Finset.sum_singleton,
    show (Finset.univ.filter (fun i => i < (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) i))
      = ({1} : Finset (Fin 3)) from by decide,
    show (Finset.univ.filter (fun i => i < (Equiv.swap 0 2 : Equiv.Perm (Fin 3)) i))
      = ({0} : Finset (Fin 3)) from by decide,
    show (Finset.univ.filter (fun i => i < (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) i))
      = ({0} : Finset (Fin 3)) from by decide,
    Finset.prod_singleton, Finset.prod_singleton, Finset.prod_singleton]
  norm_num [show ((0 : Fin 3).succ) = (1 : Fin 4) from by decide,
    show ((1 : Fin 3).succ) = (2 : Fin 4) from by decide,
    show ((2 : Fin 3).succ) = (3 : Fin 4) from by decide,
    show ((Equiv.swap 1 2 : Equiv.Perm (Fin 3)) 1).succ = (3 : Fin 4) from by decide,
    show ((Equiv.swap 0 2 : Equiv.Perm (Fin 3)) 0).succ = (3 : Fin 4) from by decide,
    show ((Equiv.swap 0 1 : Equiv.Perm (Fin 3)) 0).succ = (2 : Fin 4) from by decide]

/-! ## 4. The check -/

/-- **THE FOUR-INDEX CONSISTENCY CHECK, WHICH `PairingRecursion` NAMED AND DECLINED.**
`perfectMatchings_fin_four_prod` reduces the left-hand side by enumerating the pairings of `Fin 4`;
`recursion_rhs_fin_three` reduces the right-hand side by enumerating the fibres over `Fin 3`.
Neither uses `sum_pairProduct_succ`, and the recursion says they are equal — so all three hold
together only if the recursion is right at this order.

**AND IT STILL DOES NOT EXERCISE `dotG_comm`**, which is the finding this file exists for and is
the opposite of what the previous file predicted. See the header. -/
theorem sum_pairProduct_four_consistent (f : Fin 4 → EuclideanSpace ℝ V) :
    (∑ σ : ↑(perfectMatchings (Fin 4)), pairProduct G m f σ.1)
      = ∑ b : Fin 3, dotG G m (f 0) (f b.succ)
          * ∑ g : ↑(onlyFixing b), ∏ i ∈ Finset.univ.filter (fun i => i < g.1 i),
              dotG G m (f i.succ) (f (g.1 i).succ) := by
  rw [perfectMatchings_fin_four_prod f, recursion_rhs_fin_three f]

end PairingRecursionFour
