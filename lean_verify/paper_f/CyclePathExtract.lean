import LeftPartWalk

/-!
# Cutting a cycle at the added vertex, and getting a path in the part

Three files have now built the same object one step at a time. `OddVertexAugment` adjoins a vertex
to make every degree even; `CycleRestriction` cuts the resulting cycles back to `V` and gets the
edge partition and the degree signature; `LeftPartWalk` brings a walk — and a path — down from
`V ⊕ Unit` to `V`. Each fenced the next step, and the fence `LeftPartWalk` left reads: *rotate a
cycle to begin at the added vertex, drop its two end edges, check the middle is a path, and check
its edges are exactly `leftPart H`.*

**This does the first three of those four.**

## What is proved

**`notMem_support_dropLast_tail`** — the list fact the whole thing rests on. A cycle based at the
added vertex has `support = (added vertex) :: rest` with `rest` **nodup** and ending at the added
vertex, so dropping that last entry leaves a list the added vertex is **not** in. Stated through
Mathlib's `Walk.tail` and `Walk.dropLast`, whose `support_dropLast_concat` gives the `++ [v]` shape
that `List.nodup_append` then reads.

**`exists_leftPart_path_of_cycle`** — **so a cycle through the added vertex yields a genuine
path in the part, joining the added vertex's two neighbours.** Both endpoints come back as
`Sum.inl` vertices, both adjacencies to the added vertex come back with them, and **the two are
proved distinct** — `y ≠ z` is part of the statement, by `Path.loop_eq` against
`IsCycle.three_le_length`: were they equal the cut-down walk would be a path from a vertex to
itself, hence nil, forcing the cycle to have length two. **No rotation is needed** because the
hypothesis is a cycle **based at** the added vertex, which is what `Walk.rotate` would produce.

**`exists_leftPart_path_of_mem`** — and the form that starts from an arbitrary cycle walk with the
added vertex merely **on** it: `Walk.rotate` moves the basepoint and `IsCycle.rotate` carries the
hypothesis, so the fence's first step is taken too.

## What is NOT here

**THE EDGES ARE NOT IDENTIFIED, AND THAT IS THE WHOLE OF WHAT REMAINS.** The path produced is a
path **in** `leftPart H`; **nothing shows its edges are exactly `leftPart H`'s**, which is the
fourth step of the fence and the one that would make `leftPart H` *a path graph* rather than *a
graph containing a path*. **Not attempted, no cost claimed** (`ERRATUM 246`). Until it is done there
is no path-graph analogue of `IsCycleGraph` in this estate, and `CycleRestriction`'s decomposition
still names its pieces only by their degree signature.

**NOTHING HANDLES A CYCLE THAT MISSES THE ADDED VERTEX.** `exists_leftPart_path_of_mem` takes the
added vertex **on** the walk. A cycle avoiding it restricts to a cycle, not a path, and **that case
is not stated here** — `CycleRestriction.card_odd_leftPart_le_two` covers it at the level of degrees
and nothing covers it at the level of walks.

**W3 DOES NOT MOVE, AND WOULD NOT MOVE IF RESIDUE (a) CLOSED.** `ERRATUM 97` is that
circuits-plus-paths is **necessary and not sufficient** for `S3b-ii`'s covering, because it does not
say which piece the plaquette at `x` lies on; residue (b) is untouched here and everywhere. **No
claim is made that the Peierls chain gains anything.**

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): **no finiteness, no decidability in
any statement, and no hypothesis on `H` beyond the cycle itself.** `V` is an arbitrary type and
`H` an arbitrary graph on `V ⊕ Unit`; `Walk.rotate` wants `DecidableEq` and it is produced by
`classical` inside the one proof that uses it, so no caller carries it. Nothing here knows about
`augment`, about degrees, or about the Ising model.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace CyclePathExtract

open CycleRestriction LeftPartWalk SimpleGraph

variable {V : Type*} {H : SimpleGraph (V ⊕ Unit)}

/-! ## 1. The list fact: dropping the closing step removes the only copy -/

/-- Anything in `V ⊕ Unit` other than the added vertex is a `Sum.inl`. -/
theorem eq_inl_of_ne {x : V ⊕ Unit} (h : x ≠ Sum.inr ()) : ∃ w : V, x = Sum.inl w := by
  cases x with
  | inl w => exact ⟨w, rfl⟩
  | inr t => exact absurd (by cases t; rfl) h

/-- **THE ADDED VERTEX IS NOT ON THE CUT-DOWN WALK.** A cycle based there has nodup tail ending
there, and `dropLast` removes exactly that occurrence. -/
theorem notMem_support_dropLast_tail (p : H.Walk (Sum.inr ()) (Sum.inr ()))
    (hp : p.IsCycle) :
    Sum.inr () ∉ (p.tail.dropLast).support ∧ (p.tail.dropLast).support.Nodup := by
  have hpn : ¬ p.Nil := hp.not_nil
  have htn : ¬ p.tail.Nil := by
    rw [Walk.nil_iff_length_eq]
    have h3 := hp.three_le_length
    have := Walk.length_tail_add_one hpn
    omega
  have hsplit : (p.tail.dropLast).support ++ [Sum.inr ()] = p.tail.support :=
    Walk.support_dropLast_concat htn
  have hnodup : p.tail.support.Nodup := by
    have hcs := Walk.cons_support_tail p hpn
    have hc := hp.support_nodup
    rw [← hcs] at hc
    simpa using hc
  rw [← hsplit] at hnodup
  rw [List.nodup_append] at hnodup
  exact ⟨fun hmem => hnodup.2.2 _ hmem _ (by simp) rfl, hnodup.1⟩

/-! ## 2. So the cycle yields a path in the part -/

/-- **A CYCLE THROUGH THE ADDED VERTEX YIELDS A PATH IN THE PART, JOINING ITS TWO NEIGHBOURS.** -/
theorem exists_leftPart_path_of_cycle (p : H.Walk (Sum.inr ()) (Sum.inr ()))
    (hp : p.IsCycle) :
    ∃ (y z : V) (q : (leftPart H).Walk y z), q.IsPath ∧ y ≠ z ∧
      H.Adj (Sum.inr ()) (Sum.inl y) ∧ H.Adj (Sum.inl z) (Sum.inr ()) := by
  have hpn : ¬ p.Nil := hp.not_nil
  have htn : ¬ p.tail.Nil := by
    rw [Walk.nil_iff_length_eq]
    have h3 := hp.three_le_length
    have := Walk.length_tail_add_one hpn
    omega
  obtain ⟨hnotmem, hnodup⟩ := notMem_support_dropLast_tail p hp
  have hsnd : H.Adj (Sum.inr ()) p.snd := p.adj_snd hpn
  have hpen : H.Adj p.tail.penultimate (Sum.inr ()) := p.tail.adj_penultimate htn
  obtain ⟨y, hy'⟩ := eq_inl_of_ne hsnd.ne'
  obtain ⟨z, hz'⟩ := eq_inl_of_ne hpen.ne
  have hadj1 : H.Adj (Sum.inr ()) (Sum.inl y) := hy' ▸ hsnd
  have hadj2 : H.Adj (Sum.inl z) (Sum.inr ()) := hz' ▸ hpen
  have hpath : (p.tail.dropLast).IsPath := (Walk.isPath_def _).mpr hnodup
  have hne : p.snd ≠ p.tail.penultimate := by
    intro hcon
    have hpath' : ((p.tail.dropLast).copy rfl hcon.symm).IsPath :=
      (Walk.isPath_copy _ rfl hcon.symm).mpr hpath
    have hnil : (p.tail.dropLast).copy rfl hcon.symm = Walk.nil :=
      congrArg Subtype.val (SimpleGraph.Path.loop_eq (⟨_, hpath'⟩ : H.Path p.snd p.snd))
    have hlen0 : ((p.tail.dropLast).copy rfl hcon.symm).length = 0 := by rw [hnil]; rfl
    have hlen : (p.tail.dropLast).length = 0 := by rwa [Walk.length_copy] at hlen0
    have h1 := Walk.length_dropLast_add_one htn
    have h2 := Walk.length_tail_add_one hpn
    have h3 := hp.three_le_length
    omega
  have hyz : y ≠ z := fun hcon =>
    hne ((hy'.trans (congrArg Sum.inl hcon)).trans hz'.symm)
  obtain ⟨q, hq⟩ := exists_leftPart_path_of_notMem
    ((p.tail.dropLast).copy hy' hz') (by rwa [Walk.support_copy]) (by rwa [Walk.isPath_copy])
  exact ⟨y, z, q, hq, hyz, hadj1, hadj2⟩

/-- **AND FROM ANY CYCLE THE ADDED VERTEX MERELY LIES ON**, by rotating it to start there. -/
theorem exists_leftPart_path_of_mem {a : V ⊕ Unit} (p : H.Walk a a) (hp : p.IsCycle)
    (hmem : Sum.inr () ∈ p.support) :
    ∃ (y z : V) (q : (leftPart H).Walk y z), q.IsPath ∧ y ≠ z ∧
      H.Adj (Sum.inr ()) (Sum.inl y) ∧ H.Adj (Sum.inl z) (Sum.inr ()) := by
  classical
  exact exists_leftPart_path_of_cycle (p.rotate _ hmem) (hp.rotate hmem)

end CyclePathExtract
