import LatticeOS1
import TorusTranslation

/-!
# The torus is site-transitive, so OS1's finite-volume form is not vacuous there

`LatticeOS1.EuclideanCovariantFinVol` is the estate's finite-volume OS1: **every Schwinger function
is invariant under every graph automorphism.** `gaussianField_euclideanCovariantFinVol` proves the
lattice field satisfies it, at every order.

**But a `Prop` quantified over a group says nothing until the group is known to be large**, and
this estate had never said so. `TorusTranslation.isGraphAut_shift` gives a translation of **one**
coordinate; nothing composed them, and — grepped across `paper_f/` before this file was written —
**no statement anywhere said the automorphism group acts transitively on sites**, for the torus or
for any other graph. On a graph whose only automorphism is the identity, `EuclideanCovariantFinVol`
holds by `rfl`.

## What is proved

**`transl v`** translates *every* coordinate at once, `p ↦ fun j => p j + v j`, and
**`isGraphAut_transl`** shows it is an automorphism of `torusGraph d n` — with **no case split at
all**, where `isGraphAut_shift` needed one for each of `j = i` and `j ≠ i`. The reason is
`TorusTranslation`'s own finding read one step further: once the circle adjacency is
`adjT_iff_succ`, a *uniform* shift cancels on both sides of `∀ j, j ≠ i → p j = q j` by
`add_right_cancel` and on `adjT` by `adjT_add_right`, and nothing distinguishes the moved
coordinate from the others because none of them stays still.

**`exists_isGraphAut_mapsTo`** — for any two sites `p`, `q` there is an automorphism carrying `p`
to `q`, namely `transl (q - p)`. **That is site-transitivity**, and it is what makes the axiom's
quantifier non-empty.

**`transl_injective`** — distinct vectors give distinct automorphisms, so the torus has at least
`n ^ d` of them. Before this file the estate exhibited `d · n` translations and no composite.

**`exists_isGraphAut_ne_refl`** — at `0 < d` and `1 < n` the group is non-trivial, which is the
weakest honest form of "the axiom has content".

## What it buys downstream

**`green_transl`** — the two-point function is **homogeneous**: `green (p + v) (q + v) = green p q`,
so it depends only on the difference. **`schwinger_transl`** is the same at every order, through
`LatticeOS1.schwinger_perm`. Both were available in principle the moment `transl` existed; neither
was stated, because the composite automorphism was not.

## What is NOT here

**Not `E(d)`-covariance.** The torus's translations are a finite group and the Euclidean group is
not; `LatticeOS1`'s header says in capitals that the continuum axiom is untouched, and this file
does not touch it either. What is added is that the finite-volume statement is about a group that
moves every site to every other, rather than possibly about nothing.

**Not a proof that some graph has trivial automorphism group.** The sentence above — that
`EuclideanCovariantFinVol` would hold by `rfl` there — is an observation about the definition, not
a theorem, and **no asymmetric graph is constructed anywhere in this estate** (grepped). Exhibiting
one is **not attempted and not costed** (`ERRATUM 246`).

**Not the reflections.** Transitivity is proved from translations alone. The torus also has
coordinate permutations (`LatticePointGroup`) and reflections (`TorusReflection`), and this file
neither uses nor mentions them beyond this sentence.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` **in its continuum sense** — its
finite-volume form has been a theorem since 2026-08-28 (`LatticeOS1`), which `WALLS.md` did not
record until today (`ERRATUM 444`).

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusSiteTransitive

open BoxGraph TorusReflection TorusTranslation FieldAutInvariance

variable {n : ℕ} [NeZero n] {d : ℕ}

/-! ## 1. Translating every coordinate at once -/

/-- Translate every coordinate: `p ↦ p + v`, pointwise in `Fin n`. -/
def transl (v : Site d n) : Site d n ≃ Site d n where
  toFun p := fun j => p j + v j
  invFun p := fun j => p j - v j
  left_inv p := by funext j; simp
  right_inv p := by funext j; simp

@[simp] theorem transl_apply (v p : Site d n) (j : Fin d) : transl v p j = p j + v j := rfl

/-- **A UNIFORM TRANSLATION IS AN AUTOMORPHISM OF THE TORUS**, at every side length, dimension and
vector — and with no case split, because no coordinate stays still. -/
theorem isGraphAut_transl (v : Site d n) : IsGraphAut (torusGraph d n) (transl v) := by
  intro p q
  simp only [torusGraph_adj, torusAdj]
  constructor
  · rintro ⟨i, hsame, hstep⟩
    refine ⟨i, fun j hj => ?_, ?_⟩
    · have := hsame j hj
      rw [transl_apply, transl_apply] at this
      exact add_right_cancel this
    · rw [transl_apply, transl_apply] at hstep
      exact (adjT_add_right _ _ _).mp hstep
  · rintro ⟨i, hsame, hstep⟩
    refine ⟨i, fun j hj => ?_, ?_⟩
    · rw [transl_apply, transl_apply, hsame j hj]
    · rw [transl_apply, transl_apply]
      exact (adjT_add_right _ _ _).mpr hstep

/-! ## 2. Site-transitivity -/

/-- **THE TORUS IS SITE-TRANSITIVE**: some automorphism carries any site to any other. This is what
makes `LatticeOS1.EuclideanCovariantFinVol`'s quantifier non-empty on this graph. -/
theorem exists_isGraphAut_mapsTo (p q : Site d n) :
    ∃ θ : Site d n ≃ Site d n, IsGraphAut (torusGraph d n) θ ∧ θ p = q := by
  refine ⟨transl (fun j => q j - p j), isGraphAut_transl _, ?_⟩
  funext j
  rw [transl_apply]
  abel

/-- Distinct vectors give distinct automorphisms, so the torus has at least `n ^ d` of them.
Before this file the estate exhibited `d · n` translations and no composite. -/
theorem transl_injective : Function.Injective (transl (d := d) (n := n)) := by
  intro v w h
  funext j
  have := congrFun (congrArg (fun e : Site d n ≃ Site d n => (e : Site d n → Site d n) 0) h) j
  simpa using this

/-- **THE AUTOMORPHISM GROUP IS NON-TRIVIAL** at `0 < d` and `1 < n` — the weakest honest form of
"the finite-volume axiom has content". -/
theorem exists_isGraphAut_ne_refl (hd : 0 < d) (hn : 1 < n) :
    ∃ θ : Site d n ≃ Site d n, IsGraphAut (torusGraph d n) θ ∧ θ ≠ Equiv.refl _ := by
  have hone : ((1 : Fin n) : ℕ) = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt hn
  have h10 : (1 : Fin n) ≠ 0 := by
    intro h
    rw [h] at hone
    simp at hone
  refine ⟨transl (fun _ => 1), isGraphAut_transl _, ?_⟩
  intro hrefl
  have := congrFun (congrArg (fun e : Site d n ≃ Site d n => (e : Site d n → Site d n) 0) hrefl)
    ⟨0, hd⟩
  simp only [transl_apply, Equiv.coe_refl, id_eq] at this
  exact h10 (by simpa using this.symm)

/-! ## 3. What transitivity buys: homogeneity at every order -/

/-- **THE TWO-POINT FUNCTION IS HOMOGENEOUS**: it depends only on the difference of its arguments.
`LatticeReflectionPositive.green_congr` at a uniform translation. -/
theorem green_transl (v p q : Site d n) (m : ℝ) :
    GraphLaplacian.green (torusGraph d n) m (transl v p) (transl v q)
      = GraphLaplacian.green (torusGraph d n) m p q :=
  LatticeReflectionPositive.green_congr (transl v) (fun a b => isGraphAut_transl v a b) m p q

/-- **AND SO IS EVERY SCHWINGER FUNCTION**, at every order — `LatticeOS1.schwinger_perm` at a
uniform translation. -/
theorem schwinger_transl (v : Site d n) {m : ℝ} (hm : m ≠ 0) {k : ℕ} (p : Fin k → Site d n) :
    LatticeOS1.schwinger (torusGraph d n) m (transl v ∘ p)
      = LatticeOS1.schwinger (torusGraph d n) m p :=
  LatticeOS1.schwinger_perm (isGraphAut_transl v) hm p

/-- **The Gaussian field on the torus is invariant under every uniform translation**, as an
equality of measures. -/
theorem gaussianField_map_transl (v : Site d n) {m : ℝ} (hm : m ≠ 0) :
    (GraphLaplacian.gaussianField (torusGraph d n) m).map (permField (transl v))
      = GraphLaplacian.gaussianField (torusGraph d n) m :=
  gaussianField_map_perm (isGraphAut_transl v) hm

end TorusSiteTransitive
