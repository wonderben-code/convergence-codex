/-
  TorusReflection.lean — the criterion behind the box, and the periodic box.

  WHY. Every reflection-positivity theorem in this estate is about ONE graph:
  the free-boundary box `boxGraph d n`. `GraphReflectionPositive` is general in
  the graph, the reflection and the half, but its only instance is that box,
  and `BoxCrossCoupling` reaches the instance by computing the box's geometry
  directly. **Generality with one instance is a claim about reusability that
  nobody has tested**, which is ERRATUM 48's situation exactly.

  This does two things about that. It extracts the CRITERION the box's
  computation was really establishing, in a form with no coordinates in it;
  and it applies the criterion to a second graph — **the periodic box**, which
  is not a decoration: periodic boundary conditions are the setting in which
  the infinite-volume limit of a lattice field theory is normally taken, so
  the graph W2 would need is this one and not the free-boundary box.

  WHAT THIS FILE PROVES:
  1. **`reflectionPositive_of_cross_diag`** — **THE CRITERION.** If the only
     edges crossing the cut join a site to its OWN mirror, the massive Green
     function is reflection positive. No coordinates, no box, no arithmetic;
     the hypothesis is a sentence about adjacency that can be checked graph by
     graph. It is strictly more general than `BoxCrossCoupling`'s route and
     the proof is shorter, because the box's two-case `Fin` argument was
     establishing this hypothesis rather than being needed by the conclusion.
  2. **`boxGraph_cross_diag`, `reflectionPositive_box'`** — the box satisfies
     it, and its reflection-positivity theorem comes back out. **This is the
     check, not decoration**: an abstraction that could not recover its own
     motivating case would be the wrong abstraction.
  3. **`torusGraph`** — the `d`-dimensional periodic box, as a `SimpleGraph`
     on the same vertex type as `boxGraph`, with `boxGraph_le_torusGraph`
     recording that it is the box plus the wrap-around bonds.
  4. **`adj_torus_revSite_iff`** — the cross-cut geometry of the torus: a
     lower-half site is adjacent to the mirror of a lower-half site exactly
     when the two are the same site and it lies on ONE OF TWO layers — the
     innermost, as for the box, and now also the outermost, `pᵢ = 0`, which is
     the second cut the periodic identification creates. **A torus reflection
     has two mirrors, and this is where that shows up.**
  5. **`reflectionPositive_torus`**, and hence **`os2_torus`** and
     **`os2_exponential_torus`** — measure-level and exponential-algebra OS2
     for the periodic lattice free field, in every dimension including four,
     for even side. The last two are immediate: `GraphOS2` and
     `GraphOS2Exponential` quantify over the graph and the reflection.

  WHAT THIS DOES NOT DO.
  * **Even side only, still**, and now for a second reason as well as the
    first: `GraphHalfSpace.isHalf_lowerHalf` needs it, and on an odd torus the
    wrap-around cut is a site reflection rather than a bond reflection.
  * **`n = 2` is degenerate and is not excluded.** On a two-site circle the
    two bonds between the same pair of sites collapse to one edge in a
    `SimpleGraph`, so `torusGraph d 2 = boxGraph d 2` and the theorem there is
    the box's. Recorded rather than hidden: the statement is true, it is just
    not about a torus. `torus_two_eq_box` proves the collapse.
  * **No infinite-volume limit.** Having the right finite graph is a
    prerequisite for W2, not progress on it. Nothing here takes any limit.
  * **The field is free, and this is OS2 only.** Unchanged from the four files
    this one extends.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import LatticeReflectionTwo

namespace TorusReflection

open Finset Matrix GraphLaplacian GraphReflection GraphHalfSpace BoxGraph
open scoped ComplexOrder

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H : Finset V}

/-! ## 1. The criterion

`BoxCrossCoupling` computed, for the box, that the coupling across the cut is
minus a diagonal indicator. Reading its proof, the box entered in exactly one
place: to establish that a half-site adjacent to the mirror of a half-site
must be that same site. **Everything after that is graph-independent**, so it
is extracted here with that statement as a hypothesis.
-/

/-- Off the diagonal of `θ` the mass and degree terms vanish, so the coupling
    across the cut is minus the adjacency indicator. -/
theorem crossOp_eq_neg_adj (hH : IsHalf θ H) {p q : V} (hp : p ∈ H) (hq : q ∈ H) :
    crossOp G m θ p q = if G.Adj p (θ q) then -1 else 0 := by
  classical
  have hne : p ≠ θ q := by
    intro hc
    exact hH.notMem_of_mem hq (hc ▸ hp)
  simp only [crossOp, Matrix.of_apply, GraphLaplacian.massive, Matrix.add_apply,
    Matrix.diagonal_apply, SimpleGraph.lapMatrix, Matrix.sub_apply,
    SimpleGraph.degMatrix, SimpleGraph.adjMatrix, Matrix.of_apply, if_neg hne]
  by_cases hadj : G.Adj p (θ q) <;> simp [hadj]

/-- **THE CRITERION, as a quadratic form.** If the only cut-crossing edges
    join a site to its own mirror, the cross-coupling is negative
    semidefinite on the half — because the double sum collapses to minus a sum
    of squares over the sites that actually have such an edge. -/
theorem crossOp_nonpos_of_cross_diag (hH : IsHalf θ H)
    (hcross : ∀ p ∈ H, ∀ q ∈ H, G.Adj p (θ q) → p = q) (w : H → ℝ) :
    ∑ p, ∑ q, w p * w q * crossOp G m θ (p : V) (q : V) ≤ 0 := by
  classical
  have hterm : ∀ p q : H, w p * w q * crossOp G m θ (p : V) (q : V)
      = if p = q then (if G.Adj (p : V) (θ (p : V)) then -(w p * w p) else 0) else 0 := by
    intro p q
    rw [crossOp_eq_neg_adj (m := m) hH p.2 q.2]
    by_cases hpq : p = q
    · subst hpq
      by_cases hadj : G.Adj (p : V) (θ (p : V)) <;> simp [hadj]
    · have hne : ¬ G.Adj (p : V) (θ (q : V)) := fun hc =>
        hpq (Subtype.ext (hcross (p : V) p.2 (q : V) q.2 hc))
      simp [hne, hpq]
  calc ∑ p, ∑ q, w p * w q * crossOp G m θ (p : V) (q : V)
      = ∑ p : H, ∑ q : H,
          if p = q then (if G.Adj (p : V) (θ (p : V)) then -(w p * w p) else 0) else 0 :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => hterm p q
    _ ≤ 0 := by
        refine Finset.sum_nonpos fun p _ => Finset.sum_nonpos fun q _ => ?_
        split_ifs
        · nlinarith [sq_nonneg (w p)]
        all_goals exact le_rfl

/-- **THE CRITERION.** Reflection positivity of the massive Green function
    follows from one sentence about adjacency. -/
theorem reflectionPositive_of_cross_diag (hH : IsHalf θ H) (h : IsRefl G θ) (hm : m ≠ 0)
    (hcross : ∀ p ∈ H, ∀ q ∈ H, G.Adj p (θ q) → p = q) :
    GraphReflection.ReflectionPositive G m θ H :=
  GraphReflectionPositive.reflectionPositive_of_crossOp_nonpos hH h hm
    (crossOp_nonpos_of_cross_diag hH hcross)

/-! ## 2. The box satisfies it

The check that §1 is the right abstraction. If the criterion could not
recover the case it was extracted from, it would be the wrong criterion.
-/

section Box

variable {d n : ℕ}

theorem boxGraph_cross_diag (i : Fin d) (hn : Even n) :
    ∀ p ∈ lowerHalf i n, ∀ q ∈ lowerHalf i n,
      (boxGraph d n).Adj p (GraphReflection.revSite (n := n) i q) → p = q := by
  intro p hp q hq hadj
  exact ((BoxCrossCoupling.adj_revSite_iff i hn hp hq).mp hadj).1

/-- `GraphReflectionPositive.reflectionPositive_box`, re-derived from the
    criterion. Both proofs are kept: the original computes the cross-coupling
    and this one only needs its geometric half. -/
theorem reflectionPositive_box' (i : Fin d) (hn : Even n) (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive (boxGraph d n) m
      (GraphReflection.revSite (n := n) i) (lowerHalf i n) :=
  reflectionPositive_of_cross_diag (isHalf_lowerHalf i hn)
    { invol := GraphReflection.revSite_involutive i
      adj := fun p q => by simpa using GraphReflection.adj_revSite (n := n) i p q }
    hm (boxGraph_cross_diag i hn)

end Box

/-! ## 3. The periodic box

Same vertex type as `BoxGraph.Site`, one extra bond per coordinate: the one
joining the last layer to the first. Written with explicit "step or wrap"
disjuncts rather than modular arithmetic, so that `omega` can see the
`Fin`-value inequalities the cross-cut computation needs.
-/

section Torus

variable {d n : ℕ}

/-- Adjacency of two coordinates on the periodic line: one step apart, or the
    two ends. The `a ≠ b` conjunct is what makes the graph loopless at every
    side length, including `n = 1`. -/
def adjT (a b : Fin n) : Prop :=
  a ≠ b ∧ (a.val + 1 = b.val ∨ b.val + 1 = a.val
    ∨ (a.val = 0 ∧ b.val + 1 = n) ∨ (b.val = 0 ∧ a.val + 1 = n))

instance (a b : Fin n) : Decidable (adjT a b) := by unfold adjT; infer_instance

theorem adjT_symm (a b : Fin n) : adjT a b → adjT b a := by
  rintro ⟨hne, h⟩
  exact ⟨hne.symm, by tauto⟩

/-- **THE PERIODIC BOX.** -/
def torusAdj (p q : BoxGraph.Site d n) : Prop :=
  ∃ i : Fin d, (∀ j, j ≠ i → p j = q j) ∧ adjT (p i) (q i)

instance (p q : BoxGraph.Site d n) : Decidable (torusAdj p q) := by
  unfold torusAdj; infer_instance

def torusGraph (d n : ℕ) : SimpleGraph (BoxGraph.Site d n) where
  Adj p q := torusAdj p q
  symm := by
    rintro p q ⟨i, h1, h2⟩
    exact ⟨i, fun j hj => (h1 j hj).symm, adjT_symm _ _ h2⟩
  loopless := ⟨by
    rintro p ⟨i, -, hne, -⟩
    exact hne rfl⟩

@[simp] theorem torusGraph_adj (p q : BoxGraph.Site d n) :
    (torusGraph d n).Adj p q ↔ torusAdj p q := Iff.rfl

instance : DecidableRel (torusGraph d n).Adj := fun p q =>
  inferInstanceAs (Decidable (torusAdj p q))

/-- **The torus is the box plus the wrap-around bonds.** -/
theorem boxGraph_le_torusGraph (d n : ℕ) : boxGraph d n ≤ torusGraph d n := by
  rintro p q ⟨i, h1, h2⟩
  refine ⟨i, h1, ?_, ?_⟩
  · intro hc
    rcases h2 with h | h <;> rw [hc] at h <;> omega
  · tauto

/-- **`n = 2` IS DEGENERATE and the file says so rather than excluding it.**
    On a two-site circle the two bonds joining the same pair collapse to one
    edge of a `SimpleGraph`, so the periodic box IS the box and the theorems
    below are the box's at that side length. -/
theorem torus_two_eq_box (d : ℕ) : torusGraph d 2 = boxGraph d 2 := by
  ext p q
  simp only [torusGraph_adj, BoxGraph.boxGraph_adj, torusAdj, BoxGraph.adj]
  constructor
  · rintro ⟨i, h1, hne, h2⟩
    refine ⟨i, h1, ?_⟩
    have hp := (p i).isLt
    have hq := (q i).isLt
    have hne' : (p i).val ≠ (q i).val := fun hc => hne (Fin.ext hc)
    omega
  · rintro ⟨i, h1, h2⟩
    refine ⟨i, h1, ?_, by tauto⟩
    intro hc
    rw [hc] at h2
    omega

/-! ## 4. The cross-cut geometry of the torus, and reflection positivity

The box has one mirror; the torus has two. That is the whole difference, and
it appears as a second layer in the characterisation below.
-/

theorem adj_torus_revSite_iff (i : Fin d) (hn : Even n) {p q : BoxGraph.Site d n}
    (hp : p ∈ lowerHalf i n) (hq : q ∈ lowerHalf i n) :
    (torusGraph d n).Adj p (GraphReflection.revSite (n := n) i q)
      ↔ (p = q ∧ (2 * (p i).val + 2 = n ∨ (p i).val = 0)) := by
  classical
  simp only [lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  obtain ⟨t, ht⟩ := hn
  have hrevq : (Fin.rev (q i)).val = n - ((q i).val + 1) := Fin.val_rev (q i)
  have hqlt : (q i).val < n := (q i).isLt
  have hplt : (p i).val < n := (p i).isLt
  constructor
  · rintro ⟨k, h1, hne, h2⟩
    have hki : k = i := by
      by_contra hk
      have hcoord : p i = GraphReflection.revSite (n := n) i q i := h1 i (Ne.symm hk)
      rw [GraphReflection.revSite_apply_self] at hcoord
      have : (p i).val = n - ((q i).val + 1) := by rw [hcoord, hrevq]
      omega
    subst hki
    rw [GraphReflection.revSite_apply_self] at h2
    have hval : (Fin.rev (q k)).val = n - ((q k).val + 1) := hrevq
    have hpk : (p k).val = (q k).val := by
      rcases h2 with h | h | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
    refine ⟨?_, by omega⟩
    funext j
    by_cases hj : j = k
    · subst hj; exact Fin.ext hpk
    · have := h1 j hj
      rwa [GraphReflection.revSite_apply_ne hj] at this
  · rintro ⟨rfl, hlayer⟩
    refine ⟨i, fun j hj => (GraphReflection.revSite_apply_ne hj p).symm, ?_, ?_⟩
    · intro hc
      have : (p i).val = (Fin.rev (p i)).val := by
        rw [← GraphReflection.revSite_apply_self (n := n) i p, ← hc]
      have hrp : (Fin.rev (p i)).val = n - ((p i).val + 1) := Fin.val_rev (p i)
      omega
    · rw [GraphReflection.revSite_apply_self]
      have hrp : (Fin.rev (p i)).val = n - ((p i).val + 1) := Fin.val_rev (p i)
      rcases hlayer with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))

theorem torus_cross_diag (i : Fin d) (hn : Even n) :
    ∀ p ∈ lowerHalf i n, ∀ q ∈ lowerHalf i n,
      (torusGraph d n).Adj p (GraphReflection.revSite (n := n) i q) → p = q :=
  fun _ hp _ hq hadj => ((adj_torus_revSite_iff i hn hp hq).mp hadj).1

theorem isRefl_torus (i : Fin d) :
    IsRefl (torusGraph d n) (GraphReflection.revSite (n := n) i) where
  invol := GraphReflection.revSite_involutive i
  adj := by
    intro p q
    simp only [torusGraph_adj, torusAdj]
    constructor
    · rintro ⟨k, h1, hne, h2⟩
      refine ⟨k, ?_, ?_, ?_⟩
      · intro j hj
        have := h1 j hj
        by_cases hjk : j = i
        · subst hjk
          rw [GraphReflection.revSite_apply_self, GraphReflection.revSite_apply_self] at this
          exact (Fin.rev_injective this)
        · rwa [GraphReflection.revSite_apply_ne hjk, GraphReflection.revSite_apply_ne hjk] at this
      · intro hc
        refine hne ?_
        by_cases hki : k = i
        · subst hki
          rw [GraphReflection.revSite_apply_self, GraphReflection.revSite_apply_self, hc]
        · rw [GraphReflection.revSite_apply_ne hki, GraphReflection.revSite_apply_ne hki, hc]
      · by_cases hki : k = i
        · subst hki
          rw [GraphReflection.revSite_apply_self, GraphReflection.revSite_apply_self] at h2
          have h1' : (Fin.rev (p k)).val = n - ((p k).val + 1) := Fin.val_rev (p k)
          have h2' : (Fin.rev (q k)).val = n - ((q k).val + 1) := Fin.val_rev (q k)
          have hp := (p k).isLt
          have hq := (q k).isLt
          rcases h2 with h | h | ⟨h, h'⟩ | ⟨h, h'⟩
          · exact Or.inr (Or.inl (by omega))
          · exact Or.inl (by omega)
          · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
        · rwa [GraphReflection.revSite_apply_ne hki,
            GraphReflection.revSite_apply_ne hki] at h2
    · rintro ⟨k, h1, hne, h2⟩
      refine ⟨k, ?_, ?_, ?_⟩
      · intro j hj
        by_cases hjk : j = i
        · subst hjk
          rw [GraphReflection.revSite_apply_self, GraphReflection.revSite_apply_self, h1 j hj]
        · rw [GraphReflection.revSite_apply_ne hjk, GraphReflection.revSite_apply_ne hjk]
          exact h1 j hj
      · intro hc
        refine hne ?_
        by_cases hki : k = i
        · subst hki
          rw [GraphReflection.revSite_apply_self, GraphReflection.revSite_apply_self] at hc
          exact Fin.rev_injective hc
        · rwa [GraphReflection.revSite_apply_ne hki,
            GraphReflection.revSite_apply_ne hki] at hc
      · by_cases hki : k = i
        · subst hki
          rw [GraphReflection.revSite_apply_self, GraphReflection.revSite_apply_self]
          have h1' : (Fin.rev (p k)).val = n - ((p k).val + 1) := Fin.val_rev (p k)
          have h2' : (Fin.rev (q k)).val = n - ((q k).val + 1) := Fin.val_rev (q k)
          have hp := (p k).isLt
          have hq := (q k).isLt
          rcases h2 with h | h | ⟨h, h'⟩ | ⟨h, h'⟩
          · exact Or.inr (Or.inl (by omega))
          · exact Or.inl (by omega)
          · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
        · rw [GraphReflection.revSite_apply_ne hki, GraphReflection.revSite_apply_ne hki]
          exact h2

/-- **REFLECTION POSITIVITY OF THE PERIODIC LATTICE FREE FIELD.** -/
theorem reflectionPositive_torus (i : Fin d) (hn : Even n) (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive (torusGraph d n) m
      (GraphReflection.revSite (n := n) i) (lowerHalf i n) :=
  reflectionPositive_of_cross_diag (isHalf_lowerHalf i hn) (isRefl_torus i) hm
    (torus_cross_diag i hn)

/-- **AND IN FOUR DIMENSIONS.** -/
theorem reflectionPositive_torus_four (i : Fin 4) (hn : Even n) (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive (torusGraph 4 n) m
      (GraphReflection.revSite (n := n) i) (lowerHalf i n) :=
  reflectionPositive_torus i hn hm

/-! ## 5. Both measure-level statements, free

Neither is proved here. `GraphOS2` and `GraphOS2Exponential` quantify over the
graph and the reflection and take reflection positivity as a hypothesis, so §4
is the only input — the same payoff `LatticeReflectionTwo` recorded, now
cashed across a change of GRAPH rather than a change of direction.
-/

theorem os2_torus (i : Fin d) (hn : Even n) (hm : m ≠ 0)
    {c : BoxGraph.Site d n → ℝ} (hc : ∀ p, p ∉ lowerHalf i n → c p = 0) :
    0 ≤ ∫ ω, (∑ p, c p * ω (GraphReflection.revSite (n := n) i p)) * (∑ q, c q * ω q)
        ∂(gaussianField (torusGraph d n) m) :=
  GraphOS2.os2_measure_level _ hm (reflectionPositive_torus i hn hm) hc

theorem os2_exponential_torus (i : Fin d) (hn : Even n) (hm : m ≠ 0)
    {M : ℕ} (t : Fin M → BoxGraph.Site d n → ℝ)
    (ht : ∀ k p, p ∉ lowerHalf i n → t k p = 0) (c : Fin M → ℂ) :
    0 ≤ ∫ ω, (∑ k, c k * Complex.exp
          ((∑ p, t k p * ω (GraphReflection.revSite (n := n) i p) : ℝ) * Complex.I))
        * (starRingEnd ℂ) (∑ l, c l * Complex.exp ((∑ p, t l p * ω p : ℝ) * Complex.I))
        ∂(gaussianField (torusGraph d n) m) :=
  GraphOS2Exponential.os2_exponential m hm (isRefl_torus i)
    (reflectionPositive_torus i hn hm) t ht c

end Torus

/-! ## 6. Review round 88 — the ways this could be hollow

**"Is the criterion actually more general, or is it the box's proof with the
box hidden inside the hypothesis?"** It is more general, and the torus is the
evidence rather than the argument. **A criterion with one instance proves
nothing about reusability**, which is why this file would have been
incomplete with §1 and §2 alone: §3–§4 exhibit a second graph, with a
different cut-crossing pattern — two mirror layers rather than one — that
satisfies the same hypothesis. What the box's `Fin` computation was really
establishing is visible now: it computed the whole cross-coupling, and only
the geometric half of that computation was ever used.

**"§2 could be circular — deriving the box from a criterion extracted from the
box."** It is not circular but it IS derived: `boxGraph_cross_diag` consumes
`BoxCrossCoupling.adj_revSite_iff`, which is the box's own theorem, so
`reflectionPositive_box'` is a re-derivation and not an independent proof.
**Both are kept and the docstring says which is which.** The value of the
re-derivation is that it shows the criterion is strong enough, not that it
gives a new fact.

**"Is the torus a real torus?"** In every dimension and at every even side
length above two, yes: `boxGraph_le_torusGraph` shows it strictly extends the
box by the wrap-around bonds. **At `n = 2` it is NOT**, and `torus_two_eq_box`
proves the collapse rather than leaving the reader to notice it: two bonds
between the same pair of sites are one edge in a `SimpleGraph`, so the
two-site circle is the two-site path. The theorems still hold there; they are
just not about a torus. This is exactly the kind of degenerate corner this
project has been caught leaving unstated before.

**"The second cut is suspicious — does the wrap-around really behave?"** It is
the substantive difference and `adj_torus_revSite_iff` is where it lives. On
the box the only cut-crossing bonds sit at the innermost layer; on the torus
there is a second family at `pᵢ = 0`, because the reflection `Fin.rev` sends
`0` to `n−1` and those two are adjacent through the wrap. **A torus
reflection has two mirrors** and this is standard — it is why periodic
boundary conditions are compatible with reflection positivity at all — but it
is also exactly the place a hand-waved proof would have gone wrong, and the
`omega` case split is over four disjuncts rather than two for that reason.

**"Why does this matter beyond one more instance?"** Because the free-boundary
box is not the graph the physics uses. Infinite-volume limits of lattice field
theories are normally taken along a sequence of PERIODIC boxes, so a
reflection-positivity theorem that only covers free boundaries is a theorem
about the wrong finite approximants. **This does not take that limit and
claims nothing about W2** — having the right finite graph is a prerequisite,
not progress. But the prerequisite is now met, and it was not this morning.
-/

end TorusReflection
