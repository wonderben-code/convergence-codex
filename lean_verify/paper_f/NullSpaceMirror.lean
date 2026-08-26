import MirrorStrictness

/-!
# The null space on the far side of the cut, and the operator that carries it there

`MirrorStrictness` settled **when** the reflected form is nondegenerate on the mirror half: exactly
when it is on the near half, because `mir θ` fixes the form. It says nothing about **what** the null
space is there, and the near-half files say exactly what it is — the massive image of the families
supported on `innerLower`, at every parity and on all three lattices.

The gap is one lemma. `mir θ` fixes the FORM (`MirrorStrictness.reflectedForm_mir`); what a
null-space description needs is that it also commutes with the OPERATOR.

## What is proved

* **`massive_mulVec_mir`** — `massive G m *ᵥ (mir θ v) = mir θ (massive G m *ᵥ v)`, on every finite
  graph, whenever `θ` is a reflection. It is `GraphReflection.IsRefl.massive` — the matrix identity
  `green_aut` is proved from — read as a statement about the operator's ACTION rather than about
  its entries, which is the same distinction `NullSpaceLattice`'s `massive_mulVec_congr` had to
  make for a relabelling.
* **`nullSpace_iff_mirror`** — and so a null-space description transfers: if the families supported
  on `H` that the form annihilates are exactly the massive images of families supported on `S`,
  then the same holds on `H.image θ` with `S.image θ`. **A transfer principle, not an instance** —
  it takes the near-half biconditional as a hypothesis and hands back the far-half one, so every
  such description this estate has or later proves crosses the cut for free.
* **`finrank_nullSub_image`** — the dimension is unchanged, because `θ` is injective and a
  `Finset`'s image under an injection has its cardinality.
* The box's instance worked through: `nullSpace_box_mirror`, `finrank_nullSub_box_mirror` and
  `codim_box_mirror`.

## What is NOT here

**The torus and the two lattice cuts are not instantiated.** Each would be `nullSpace_iff_mirror`
applied to `NullSpaceTorusAny.nullSpace_torus_any`, `NullSpaceLattice.nullSpace_lattice` or
`NullSpaceLatticeTwo.nullSpace_lattice_two` together with that graph's `IsRefl` — the shape the box
instance below shows, and a claim a reader can check rather than a cost claim (`ERRATUM 246`). The
box is instantiated so the general theorem is exercised rather than left standing (`ERRATUM 201`);
the other three are left to the point of use, because an instance nothing consumes grows the
declaration count without the estate learning anything.

No threshold appears anywhere below. `MirrorStrictness` has the thresholds; this has the
description behind them.
-/

namespace NullSpaceMirror

open Finset BoxGraph GraphHalfSpace GraphReflection MirrorStrictness

open scoped Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {m : ℝ} {θ : V ≃ V}

/-! ## 1. The massive operator commutes with the mirror -/

/-- **THE OPERATOR DOES NOT NOTICE THE MIRROR EITHER.** `IsRefl.massive` says the matrix is
invariant under relabelling both indices; this says the same thing about what the matrix does to a
vector, which is the form a null-space statement is written in. -/
theorem massive_mulVec_mir (h : IsRefl G θ) (m : ℝ) (v : V → ℝ) :
    GraphLaplacian.massive G m *ᵥ (mir θ v) = mir θ (GraphLaplacian.massive G m *ᵥ v) := by
  classical
  funext p
  simp only [mir, Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp θ fun q => GraphLaplacian.massive G m p q * v (θ q)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hmat := congrFun (congrFun (h.massive m) p) (θ q)
  simp only [Matrix.submatrix_apply, h.invol q] at hmat
  rw [h.invol q, ← hmat]

/-! ## 2. Support and cardinality across the cut -/

section Support

variable {W : Type*} [DecidableEq W] {ϑ : W ≃ W}

theorem mir_supported_image (h : Function.Involutive ϑ) {S : Finset W} {v : W → ℝ}
    (hv : ∀ p, p ∉ S → v p = 0) : ∀ p, p ∉ S.image ϑ → mir ϑ v p = 0 := by
  intro p hp
  refine hv _ fun hmem => hp ?_
  exact Finset.mem_image.mpr ⟨ϑ p, hmem, h p⟩

end Support

theorem finrank_nullSub_image (hm : m ≠ 0) (S : Finset V) :
    Module.finrank ℝ (NullSpaceDimension.nullSub G m (S.image θ)) = S.card := by
  classical
  rw [NullSpaceDimensionEven.finrank_nullSub hm, Finset.card_image_of_injective _ θ.injective]

/-! ## 3. The transfer principle -/

/-- **A NULL-SPACE DESCRIPTION CROSSES THE CUT.** The hypothesis is the near-half biconditional and
the conclusion is the far-half one, with both sets carried over by `θ`. Nothing about the graph,
the half or the parametrising set is used beyond `θ` being a reflection. -/
theorem nullSpace_iff_mirror (h : IsRefl G θ) {H S : Finset V}
    (hlow : ∀ c : V → ℝ, (∀ p, p ∉ H → c p = 0) →
      (reflectedForm G m θ c = 0
        ↔ ∃ v : V → ℝ, (∀ p, p ∉ S → v p = 0) ∧ GraphLaplacian.massive G m *ᵥ v = c))
    {c : V → ℝ} (hc : ∀ p, p ∉ H.image θ → c p = 0) :
    reflectedForm G m θ c = 0
      ↔ ∃ v : V → ℝ, (∀ p, p ∉ S.image θ → v p = 0) ∧ GraphLaplacian.massive G m *ᵥ v = c := by
  classical
  have hmirc : ∀ p, p ∉ H → mir θ c p = 0 := mir_supported hc
  constructor
  · intro hnull
    obtain ⟨v, hvsupp, hvc⟩ :=
      (hlow (mir θ c) hmirc).mp (by rwa [reflectedForm_mir h])
    refine ⟨mir θ v, mir_supported_image h.invol hvsupp, ?_⟩
    rw [massive_mulVec_mir h, hvc]
    exact mir_mir h.invol c
  · rintro ⟨v, hvsupp, hvc⟩
    have hback : GraphLaplacian.massive G m *ᵥ (mir θ v) = mir θ c := by
      rw [massive_mulVec_mir h, hvc]
    have hsupp : ∀ p, p ∉ S → mir θ v p = 0 := by
      intro p hp
      refine hvsupp _ fun hmem => hp ?_
      obtain ⟨k, hk, hke⟩ := Finset.mem_image.mp hmem
      rwa [θ.injective hke] at hk
    have := (hlow (mir θ c) hmirc).mpr ⟨mir θ v, hsupp, hback⟩
    rwa [reflectedForm_mir h] at this

/-! ## 4. The box, worked through -/

section Box

variable {d n : ℕ}

/-- **THE BOX'S NULL SPACE ABOVE THE CUT, AT EVERY SIDE LENGTH.**
`NullSpaceBoxAny.nullSpace_box_any` read through the mirror. -/
theorem nullSpace_box_mirror (i : Fin d) (n : ℕ) {m : ℝ} (hm : m ≠ 0)
    {c : Site d n → ℝ}
    (hc : ∀ p, p ∉ (lowerHalf i n).image (revSite (n := n) i) → c p = 0) :
    reflectedForm (boxGraph d n) m (revSite (n := n) i) c = 0
      ↔ ∃ v : Site d n → ℝ,
          (∀ p, p ∉ (InnerLowerSupport.innerLower i n).image (revSite (n := n) i) → v p = 0)
          ∧ GraphLaplacian.massive (boxGraph d n) m *ᵥ v = c :=
  nullSpace_iff_mirror (BoxNotStrict.isRefl_box i)
    (fun _ hc' => NullSpaceBoxAny.nullSpace_box_any (m := m) i n hm hc') hc

/-- **AND ITS DIMENSION IS THE SAME NUMBER**, since a reflection is injective. -/
theorem finrank_nullSub_box_mirror (i : Fin d) (n : ℕ) {m : ℝ} (hm : m ≠ 0) :
    Module.finrank ℝ (NullSpaceDimension.nullSub (boxGraph d n) m
        ((InnerLowerSupport.innerLower i n).image (revSite (n := n) i)))
      = (InnerLowerSupport.innerLower i n).card :=
  finrank_nullSub_image hm _

/-- **AND SO IS THE DEFICIENCY**: one layer, at every parity, above the cut as below it. -/
theorem codim_box_mirror (i : Fin d) {n : ℕ} (hn : 0 < n) {m : ℝ} (hm : m ≠ 0) :
    Module.finrank ℝ (NullSpaceDimension.nullSub (boxGraph d n) m
        ((InnerLowerSupport.innerLower i n).image (revSite (n := n) i))) + n ^ (d - 1)
      = Module.finrank ℝ (NullSpaceDimension.supportedOn
          ((lowerHalf i n).image (revSite (n := n) i))) := by
  classical
  rw [finrank_nullSub_box_mirror i n hm, NullSpaceDimension.finrank_supportedOn,
    Finset.card_image_of_injective _ (revSite (n := n) i).injective,
    ← NullSpaceBoxAny.card_lowerHalf_sdiff_innerLower i hn,
    ← Finset.card_sdiff_add_card_eq_card
      (NullSpaceDimensionEven.innerLower_subset_lowerHalf i n)]
  omega

end Box

end NullSpaceMirror
