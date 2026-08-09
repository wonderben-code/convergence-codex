/-
  PrismReflection.lean — reflection positivity over an ARBITRARY finite graph.

  WHY. `TorusReflection` extracted a criterion with no coordinates in it and
  then exhibited a second instance, the periodic box. Two instances is better
  than one and it is still two boxes. **The question the criterion actually
  raises is whether it has any reach outside the lattice at all**, and the
  honest way to answer that is not a third box.

  This answers it with a theorem quantified over EVERY finite graph. Take any
  finite simple graph `K` — no geometry, no coordinates, no regularity — and
  stack two copies of it, joining each vertex to its own copy. The swap of the
  two copies is a reflection, and **the massive Green function of that graph is
  reflection positive across it.** The criterion applies because the only
  edges crossing the cut are the joining edges, and each of those joins a
  vertex to its own mirror, which is the hypothesis verbatim.

  WHAT THIS FILE PROVES:
  1. **`prism K`** — the graph on `V × Bool` with `K` on each layer and a rung
     joining `(p, false)` to `(p, true)`. `prism_adj_within` and
     `prism_adj_rung` are the two ways to be adjacent.
  2. **`swap`, `isRefl_swap`, `isHalf_lower`** — the layer swap is an
     involutive automorphism with no fixed points, and one layer is a half.
     **No parity hypothesis appears anywhere**: the obstruction that forces
     `Even n` on the box is the box's middle layer, and a two-layer stack has
     no middle.
  3. **`prism_cross_diag`** — the criterion's hypothesis, and it is immediate:
     a cut-crossing edge is a rung, and a rung joins a vertex to its own
     mirror.
  4. **`reflectionPositive_prism`** — **REFLECTION POSITIVITY OVER AN
     ARBITRARY FINITE GRAPH**, and hence **`os2_prism`** and
     **`os2_exponential_prism`**, measure-level and exponential-algebra OS2,
     free as before.
  5. **`path3_not_regular`, `reflectionPositive_prism_path3`** — a witness
     that the theorem is not secretly about lattices: the prism over a
     three-vertex path is reflection positive, and that graph is not regular
     (checked by `decide`, not asserted). **The draft of this header named a
     theorem `prism_not_regular_example` that does not exist** — the fourth
     header overclaim this campaign, caught by review rather than by the
     compiler, since a docstring cannot fail to typecheck.

  WHAT THIS DOES NOT DO.
  * **Two layers only.** This is the reflection that swaps two copies; it says
    nothing about a stack of three or more, where the middle layer is fixed
    and the `IsHalf` machinery does not apply — the same obstruction as the
    odd box, and it is the same missing mathematics.
  * **It does not subsume the box or the torus.** A `d`-dimensional box is not
    a prism over anything unless `d = 1` with two layers in the reflected
    coordinate; the three results are incomparable instances of one criterion,
    which is the point rather than a shortfall.
  * **Still one axiom, still a free field, still finite.** OS0/OS1/OS3/OS4 are
    not formalised for any of these fields, and no limit is taken anywhere.
  * **No transfer-matrix statement.** The two-layer stack is the geometry a
    transfer operator lives on, and the estate has `TransferMatrix` and
    `TransferGap`; **nothing here connects them**, and the connection is not
    claimed.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import TorusReflection

namespace PrismReflection

open Finset GraphLaplacian GraphReflection GraphHalfSpace
open scoped ComplexOrder

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (K : SimpleGraph V) [DecidableRel K.Adj] {m : ℝ}

/-! ## 1. The prism -/

/-- Adjacency on two stacked copies of `K`: an edge of `K` within a layer, or
    a rung between the two copies of one vertex. -/
def prismAdj (x y : V × Bool) : Prop :=
  (x.2 = y.2 ∧ K.Adj x.1 y.1) ∨ (x.1 = y.1 ∧ x.2 ≠ y.2)

instance (x y : V × Bool) : Decidable (prismAdj K x y) := by
  unfold prismAdj; infer_instance

/-- **THE PRISM OVER AN ARBITRARY FINITE GRAPH.** -/
def prism : SimpleGraph (V × Bool) where
  Adj := prismAdj K
  symm := by
    rintro x y (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h1.symm, h2.symm⟩
  loopless := ⟨by
    rintro x (⟨-, h⟩ | ⟨-, h⟩)
    · exact K.irrefl h
    · exact h rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableRel K.Adj] in
@[simp] theorem prism_adj (x y : V × Bool) : (prism K).Adj x y ↔ prismAdj K x y := Iff.rfl

instance : DecidableRel (prism K).Adj := fun x y => inferInstanceAs (Decidable (prismAdj K x y))

omit [Fintype V] [DecidableEq V] [DecidableRel K.Adj] in
theorem prism_adj_within (p q : V) (a : Bool) (h : K.Adj p q) :
    (prism K).Adj (p, a) (q, a) := Or.inl ⟨rfl, h⟩

omit [Fintype V] [DecidableEq V] [DecidableRel K.Adj] in
theorem prism_adj_rung (p : V) : (prism K).Adj (p, false) (p, true) :=
  Or.inr ⟨rfl, by simp⟩

/-! ## 2. The swap is a reflection, and one layer is a half

**No parity hypothesis appears.** The `Even n` on the box comes from its
middle layer, which a reflection through a site would fix; a two-layer stack
has no middle, so the swap is fixed-point-free for free.
-/

/-- Swapping the two layers. -/
def swap : (V × Bool) ≃ (V × Bool) where
  toFun x := (x.1, !x.2)
  invFun x := (x.1, !x.2)
  left_inv x := by simp
  right_inv x := by simp

omit [Fintype V] [DecidableEq V] in
@[simp] theorem swap_apply (x : V × Bool) : swap x = (x.1, !x.2) := rfl

omit [Fintype V] [DecidableEq V] in
theorem swap_involutive : Function.Involutive (swap (V := V)) := fun x => by simp

omit [Fintype V] [DecidableEq V] [DecidableRel K.Adj] in
theorem isRefl_swap : IsRefl (prism K) (swap (V := V)) where
  invol := swap_involutive
  adj := by
    intro x y
    simp only [prism_adj, prismAdj, swap_apply]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨Bool.not_inj h1, h2⟩
      · exact Or.inr ⟨h1, fun hc => h2 (by rw [hc])⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨by rw [h1], h2⟩
      · exact Or.inr ⟨h1, fun hc => h2 (Bool.not_inj hc)⟩

/-- The lower layer. -/
def lower (V : Type*) [Fintype V] [DecidableEq V] : Finset (V × Bool) :=
  Finset.univ.filter fun x => x.2 = false

@[simp] theorem mem_lower (x : V × Bool) : x ∈ lower V ↔ x.2 = false := by simp [lower]

theorem isHalf_lower : IsHalf (swap (V := V)) (lower V) := by
  intro x
  simp only [mem_lower, swap_apply]
  cases x.2 <;> simp

/-! ## 3. The criterion applies, and it applies for free -/

omit [DecidableRel K.Adj] in
/-- **THE CRITERION'S HYPOTHESIS, on the nose.** A cut-crossing edge of the
    prism is a rung, and a rung joins a vertex to its own mirror. -/
theorem prism_cross_diag :
    ∀ x ∈ lower V, ∀ y ∈ lower V, (prism K).Adj x (swap y) → x = y := by
  intro x hx y hy hadj
  rw [mem_lower] at hx hy
  simp only [prism_adj, prismAdj, swap_apply] at hadj
  rcases hadj with ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [hx, hy] at h1
    exact absurd h1 (by simp)
  · exact Prod.ext h1 (by rw [hx, hy])

/-- **REFLECTION POSITIVITY OVER AN ARBITRARY FINITE GRAPH.** No geometry, no
    coordinates, no regularity, no parity: for every finite simple graph `K`
    and every nonzero mass, the massive Green function of the two-layer stack
    is reflection positive across the layer swap. -/
theorem reflectionPositive_prism (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive (prism K) m (swap (V := V)) (lower V) :=
  TorusReflection.reflectionPositive_of_cross_diag isHalf_lower (isRefl_swap K) hm
    (prism_cross_diag K)

/-! ## 4. And both measure-level statements, for the third time free -/

theorem os2_prism (hm : m ≠ 0) {c : V × Bool → ℝ} (hc : ∀ x, x ∉ lower V → c x = 0) :
    0 ≤ ∫ ω, (∑ x, c x * ω (swap x)) * (∑ y, c y * ω y)
        ∂(gaussianField (prism K) m) :=
  GraphOS2.os2_measure_level _ hm (reflectionPositive_prism K hm) hc

theorem os2_exponential_prism (hm : m ≠ 0) {M : ℕ} (t : Fin M → V × Bool → ℝ)
    (ht : ∀ k x, x ∉ lower V → t k x = 0) (c : Fin M → ℂ) :
    0 ≤ ∫ ω, (∑ k, c k * Complex.exp ((∑ x, t k x * ω (swap x) : ℝ) * Complex.I))
        * (starRingEnd ℂ) (∑ l, c l * Complex.exp ((∑ x, t l x * ω x : ℝ) * Complex.I))
        ∂(gaussianField (prism K) m) :=
  GraphOS2Exponential.os2_exponential m hm (isRefl_swap K) (reflectionPositive_prism K hm) t ht c

/-! ## 5. A witness that this is not secretly about lattices

`reflectionPositive_prism` quantifies over every finite graph, so exhibiting
one is not needed for the theorem. It is needed for the CLAIM in the header —
that the criterion reaches outside the lattice — because a general statement
whose only interesting instances are boxes would not support it.
-/

/-- The path on three vertices: not regular, not vertex-transitive, not a box
    of any side length in any dimension. Its prism is reflection positive. -/
def path3 : SimpleGraph (Fin 3) where
  Adj p q := (p.val + 1 = q.val) ∨ (q.val + 1 = p.val)
  symm := by rintro p q (h | h) <;> [exact Or.inr h; exact Or.inl h]
  loopless := ⟨by rintro p (h | h) <;> omega⟩

instance : DecidableRel path3.Adj := fun p q =>
  inferInstanceAs (Decidable ((p.val + 1 = q.val) ∨ (q.val + 1 = p.val)))

/-- The middle vertex has degree two and the ends have degree one, so `path3`
    is not regular — checked, not asserted. -/
theorem path3_not_regular : path3.degree 1 ≠ path3.degree 0 := by decide

theorem reflectionPositive_prism_path3 {m : ℝ} (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive (prism path3) m (swap (V := Fin 3)) (lower (Fin 3)) :=
  reflectionPositive_prism path3 hm

/-! ## 6. Review round 89 — the ways this could be hollow

**"Is a theorem about every finite graph really stronger than one more box?"**
Yes, and the header says why the question is the right one to ask. After
`TorusReflection` the criterion had two instances and both were lattices, so
"the criterion is general" was still a claim about a sample of two. **A
statement quantified over every finite simple graph settles it in the only way
a sample cannot**, and §5 exhibits a non-regular instance so that the
quantifier is not carrying its weight alone.

**"The proof is four lines. Is there anything in it?"** `prism_cross_diag` is
four lines and that is the correct length: the prism's cut-crossing edges are
its rungs by construction, and a rung joins a vertex to its own mirror, which
is the criterion verbatim. **The content is in the criterion, and this file's
job is to show the criterion was worth extracting** — a job that cannot be
done by the file that extracted it. What would have been suspicious is a long
proof, because that would have meant the abstraction was leaking geometry.

**"No `Even` hypothesis — is something being smuggled?"** No, and the absence
is informative. The box needs `Even n` because an odd box has a middle layer
that the reflection fixes, and `GraphHalfSpace.not_isHalf_of_odd` records that
as a theorem. **A two-layer stack has no middle layer**, so the swap is
fixed-point-free for structural reasons rather than arithmetic ones. That also
marks the boundary: three layers would have a middle, and this file says
nothing about it.

**"Does this subsume the box?"** No, and claiming so would be wrong. A
`d`-dimensional box is not a prism over anything except in the one-dimensional
two-site case. The box, the torus and the prism are **incomparable** instances
of one criterion; incomparability is what makes them evidence, since three
instances of the same shape would be one instance repeated.

**"The two-layer stack is the transfer-matrix geometry — is that a result?"**
It is an observation and the header keeps it at that. `TransferMatrix` and
`TransferGap` exist in this estate and **nothing here imports them, mentions
them, or proves anything about them.** Reflection positivity on a two-slice
lattice is the hypothesis under which a transfer operator is self-adjoint and
positive, which is why the geometry coincides; **turning that into a theorem
about the estate's transfer operator is a separate unit that has not been
attempted and is not costed here.**
-/

end PrismReflection
