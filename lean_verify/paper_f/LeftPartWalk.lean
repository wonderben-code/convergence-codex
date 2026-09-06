import CycleRestriction

/-!
# Moving a walk down from `V ⊕ Unit`, which is the step both previous files fenced

`OddVertexAugment` adjoins one vertex to make every degree even; `CycleRestriction` cuts the
resulting cycles back down to `V`, gets the edge partition and the degree signature, and fences the
remainder in one sentence: *producing a walk requires moving a `Walk` in `V ⊕ Unit` whose support
avoids `Sum.inr` into a `Walk` in `V`, and nothing here does that.*

**This does that.**

## What is proved

**`exists_walk_aux`** — the induction, with both endpoints generalised so the motive is free. A
walk in `H` between two `Sum.inl` vertices, all of whose support is `Sum.inl`, yields a walk in
`CycleRestriction.leftPart H` between the corresponding vertices. The `cons` step is the whole
content: the middle vertex is `Sum.inl w` by hypothesis, and `H.Adj (Sum.inl u) (Sum.inl w)` **is**
`(leftPart H).Adj u w` by `rfl`, which is what `comap` buys.

**`exists_leftPart_walk`, `exists_leftPart_walk_of_notMem`** — the two usable forms, the second
with the hypothesis as *the added vertex is not on the walk*, which is how a cycle through it
presents the pieces on either side.

**`exists_walk_data_aux`, `exists_walk_support_aux`, `exists_walk_support_of_notMem`,
`exists_walk_data_of_notMem`, `exists_leftPart_path_of_notMem`** —
the same induction **with the support carried along**, and hence **a path comes down a path**. The
first three theorems return `Nonempty` and so throw the walk away, which is enough for reachability
and nothing else; the extraction residue (a) still wants needs the support, so §4 repeats the
induction once with it — and with the **edges** alongside, since an argument about the *edge set*
of the piece needs those and carrying them costs the same induction. The support-only form is a
corollary rather than a second copy of it. `Sum.inl` is injective, so nodup passes both ways along
the identification.

**`reachable_leftPart_of_notMem`, `not_reachable_lift`** — **so reachability transports downwards**:
two vertices joined in `H` by a walk missing the added vertex are joined in the part; and
contrapositively, if they are **not** joined in the part then every `H`-walk between them passes
through the added vertex. The second is the form a Peierls-style argument would want, since it turns
a separation statement in the part into a *forced visit* upstairs.

## What is NOT here

**A PATH IS PRODUCED ONLY FROM A PATH, AND NEVER A PATH GRAPH.** §4 carries `Walk.IsPath` down,
**given it upstairs**; it does **not** produce one from a cycle, and nothing here shows that
`leftPart H` **is** the edge set of one walk — the analogue of `IsCycleGraph` for paths is not
defined in this estate and is not defined here. **So residue (a) is not closed**, and what
remains of it after this file is: rotate a cycle to begin at the added vertex, drop its two end
edges, check the middle is a path, and check its edges are exactly `leftPart H`. **Not
attempted, no cost claimed** (`ERRATUM 246`).

**NO CYCLE IS ROTATED.** `Walk.rotate` is not used and no theorem here takes `IsCycleGraph` as a
hypothesis; this file is about walks in an arbitrary graph on `V ⊕ Unit` and mentions neither
cycles nor the augmentation.

**W3 DOES NOT MOVE, AND WOULD NOT MOVE IF RESIDUE (a) CLOSED.** `ERRATUM 97`, recorded in
`ExtendedDual` and in `UNLOCK_WATCHLIST`, is that circuits-plus-paths is **necessary and not
sufficient** for `S3b-ii`'s covering, because it does not say which piece the plaquette at `x` lies
on. Residue (b) is untouched here and everywhere. **No claim is made that the Peierls chain gains
anything.**

**THE TRANSPORT IS ONE-WAY AS STATED.** A walk in `leftPart H` lifts to one in `H` by
`Walk.map` along `SimpleGraph.Hom.comap Sum.inl H`, and **that direction is not stated** because
nothing needs it — which is a description of the step and **not** a claim about its difficulty
(`ERRATUM 194`). `not_reachable_lift` is the contrapositive of the direction that **is** proved,
not the converse.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): **no finiteness, no decidability, and no
hypothesis on `H` at all** — every theorem here holds for an arbitrary graph on `V ⊕ Unit` over an
arbitrary type `V`. That is the sense in which the step is small: it is `comap`'s defining property
plus an induction.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace LeftPartWalk

open CycleRestriction SimpleGraph

variable {V : Type*} {H : SimpleGraph (V ⊕ Unit)}

/-! ## 1. The induction -/

/-- The induction with both endpoints generalised, so that the `cons` step can rewrite them. -/
theorem exists_walk_aux : ∀ {a b : V ⊕ Unit} (p : H.Walk a b),
    (∀ x ∈ p.support, ∃ w : V, x = Sum.inl w) →
    ∀ u v : V, a = Sum.inl u → b = Sum.inl v → Nonempty ((leftPart H).Walk u v) := by
  intro a b p
  induction p with
  | nil =>
    intro _ u v hu hv
    have huv : u = v := Sum.inl_injective (hu.symm.trans hv)
    subst huv
    exact ⟨Walk.nil⟩
  | @cons x y z hadj q ih =>
    intro hp u v hu hv
    obtain ⟨w, rfl⟩ := hp y (by simp)
    subst hu
    obtain ⟨q'⟩ := ih (fun t ht => hp t (by simp [ht])) w v rfl hv
    exact ⟨Walk.cons hadj q'⟩

/-! ## 2. The two usable forms -/

/-- **A WALK WHOSE SUPPORT IS ALL `Sum.inl` COMES DOWN TO `V`.** -/
theorem exists_leftPart_walk {u v : V} (p : H.Walk (Sum.inl u) (Sum.inl v))
    (hp : ∀ x ∈ p.support, ∃ w : V, x = Sum.inl w) :
    Nonempty ((leftPart H).Walk u v) :=
  exists_walk_aux p hp u v rfl rfl

/-- **AND THE HYPOTHESIS IN THE FORM A CYCLE THROUGH THE ADDED VERTEX PRESENTS IT**: the added
vertex is simply not on the walk. -/
theorem exists_leftPart_walk_of_notMem {u v : V} (p : H.Walk (Sum.inl u) (Sum.inl v))
    (hp : Sum.inr () ∉ p.support) : Nonempty ((leftPart H).Walk u v) := by
  refine exists_leftPart_walk p fun x hx => ?_
  cases x with
  | inl w => exact ⟨w, rfl⟩
  | inr t => exact absurd hx (by cases t; exact hp)

/-! ## 3. So reachability comes down, and separation goes up -/

theorem reachable_leftPart_of_notMem {u v : V} (p : H.Walk (Sum.inl u) (Sum.inl v))
    (hp : Sum.inr () ∉ p.support) : (leftPart H).Reachable u v :=
  (exists_leftPart_walk_of_notMem p hp).elim fun q => ⟨q⟩

/-- **AND SO A SEPARATION DOWNSTAIRS FORCES EVERY WALK UPSTAIRS THROUGH THE ADDED VERTEX.** -/
theorem not_reachable_lift {u v : V} (h : ¬ (leftPart H).Reachable u v)
    (p : H.Walk (Sum.inl u) (Sum.inl v)) : Sum.inr () ∈ p.support :=
  not_not.mp fun hp => h (reachable_leftPart_of_notMem p hp)

/-! ## 4. And with the support carried along, so paths stay paths

`exists_walk_aux` returns `Nonempty` and therefore **throws away the walk**, which is enough for
reachability and not enough for anything about the walk's shape. The extraction residue (a) still
wants — cut a cycle at the added vertex and check the middle is a **path** — needs exactly the
support, so the induction is repeated once with it carried.
-/

/-- The same induction, returning the walk **with its support and its edges identified**. The
edges are what an argument about the *edge set* of the piece needs, and carrying them costs the
same induction, so they are carried here rather than in a third copy of it. -/
theorem exists_walk_data_aux : ∀ {a b : V ⊕ Unit} (p : H.Walk a b),
    (∀ x ∈ p.support, ∃ w : V, x = Sum.inl w) →
    ∀ u v : V, a = Sum.inl u → b = Sum.inl v →
      ∃ q : (leftPart H).Walk u v, q.support.map Sum.inl = p.support ∧
        q.edges.map (Sym2.map Sum.inl) = p.edges := by
  intro a b p
  induction p with
  | nil =>
    intro _ u v hu hv
    have huv : u = v := Sum.inl_injective (hu.symm.trans hv)
    subst huv
    subst hu
    exact ⟨Walk.nil, rfl, rfl⟩
  | @cons x y z hadj q ih =>
    intro hp u v hu hv
    obtain ⟨w, rfl⟩ := hp y (by simp)
    subst hu
    obtain ⟨q', hs, he⟩ := ih (fun t ht => hp t (by simp [ht])) w v rfl hv
    exact ⟨Walk.cons hadj q', by simp [hs], by simp [he]⟩

/-- The support half, which is all most callers want. -/
theorem exists_walk_support_aux {a b : V ⊕ Unit} (p : H.Walk a b)
    (hp : ∀ x ∈ p.support, ∃ w : V, x = Sum.inl w) (u v : V)
    (hu : a = Sum.inl u) (hv : b = Sum.inl v) :
    ∃ q : (leftPart H).Walk u v, q.support.map Sum.inl = p.support :=
  let ⟨q, hs, _⟩ := exists_walk_data_aux p hp u v hu hv
  ⟨q, hs⟩

/-- **A WALK MISSING THE ADDED VERTEX COMES DOWN WITH ITS SUPPORT.** -/
theorem exists_walk_support_of_notMem {u v : V} (p : H.Walk (Sum.inl u) (Sum.inl v))
    (hp : Sum.inr () ∉ p.support) :
    ∃ q : (leftPart H).Walk u v, q.support.map Sum.inl = p.support := by
  refine exists_walk_support_aux p (fun x hx => ?_) u v rfl rfl
  cases x with
  | inl w => exact ⟨w, rfl⟩
  | inr t => exact absurd hx (by cases t; exact hp)

/-- **AND THE EDGES COME DOWN WITH IT.** -/
theorem exists_walk_data_of_notMem {u v : V} (p : H.Walk (Sum.inl u) (Sum.inl v))
    (hp : Sum.inr () ∉ p.support) :
    ∃ q : (leftPart H).Walk u v, q.support.map Sum.inl = p.support ∧
      q.edges.map (Sym2.map Sum.inl) = p.edges := by
  refine exists_walk_data_aux p (fun x hx => ?_) u v rfl rfl
  cases x with
  | inl w => exact ⟨w, rfl⟩
  | inr t => exact absurd hx (by cases t; exact hp)

/-- **AND SO A PATH COMES DOWN A PATH.** `Sum.inl` is injective, so nodup passes both ways along
the support identification. -/
theorem exists_leftPart_path_of_notMem {u v : V} (p : H.Walk (Sum.inl u) (Sum.inl v))
    (hp : Sum.inr () ∉ p.support) (hpath : p.IsPath) :
    ∃ q : (leftPart H).Walk u v, q.IsPath := by
  obtain ⟨q, hq⟩ := exists_walk_support_of_notMem p hp
  refine ⟨q, (Walk.isPath_def q).mpr ?_⟩
  exact List.Nodup.of_map Sum.inl (hq ▸ (Walk.isPath_def p).mp hpath)

end LeftPartWalk
