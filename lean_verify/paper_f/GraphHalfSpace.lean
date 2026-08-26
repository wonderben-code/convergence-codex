/-
  GraphHalfSpace.lean — R1b, the block decomposition, without a single block
  matrix.

  WHY. W1's ladder reads R1a done, R1b open, R2 done, R3 open, R4 open.
  `UNLOCK_WATCHLIST`'s probe costed R1b as "an index `Equiv` onto `H ⊕ H`,
  `Matrix.reindex` and `fromBlocks`, and the inverse of
  `fromBlocks A (-B) (-B) A`", noted that Mathlib's Schur route factors
  through `A − B A⁻¹ B` rather than `A ∓ B`, and revised the estimate UP to
  two-to-three units on the strength of that.

  **NONE OF THAT IS USED HERE.** The classical decomposition says the
  operator acts as `A + B` on reflection-symmetric vectors and `A − B` on
  antisymmetric ones. That is a statement about `massive *ᵥ ·`, not about a
  block matrix, and it can be proved as one:

    `massive *ᵥ symExt v  = symExt  ((A + B) *ᵥ v)`
    `massive *ᵥ antiExt v = antiExt ((A − B) *ᵥ v)`

  where `symExt`/`antiExt` extend a function on the half to the whole graph
  evenly and oddly. The proof is one sum split along the half and one
  reindexing by `θ`. **The estimate was wrong in the other direction this
  time, and §6 says so.**

  WHAT THIS FILE PROVES:
  1. **`IsHalf`** — `H` is a half for `θ` when `p ∈ H ↔ θ p ∉ H`. For an
     involution this is disjointness and covering at once, and it forces `θ`
     to be fixed-point free (`IsHalf.no_fixed`).
  2. **`symExt`, `antiExt`** and their characterisations on and off `H`.
  3. **`crossOp`** — `B p q = massive p (θ q)`, the coupling across the cut.
     `A` needs no definition: on the half it is `massive` itself.
     `crossOp_symm` says `B` is symmetric, and that is where the
     automorphism is spent.
  4. **`massive_mulVec_symExt`, `massive_mulVec_antiExt`** — the
     decomposition, above. **This is R1b's content.**
  5. **`massive_mulVec_symExt'`, `massive_mulVec_antiExt'`** — the same in
     matrix shape, `massive *ᵥ symExt v = symExt ((A + B) *ᵥ v)` with
     `A + B` an actual matrix, for `v` supported on the half. And
     **`reflectionPositive_iff_ext`**, which puts R1a's comparison in terms
     of the two extensions.
  6. **`lowerHalf`, `isHalf_lowerHalf`** — and it is inhabited: on a box of
     EVEN side, the sites with `i`-th coordinate below the midline form a
     half for `revSite i`. For odd side the reflection has a fixed site and
     no half exists — `IsHalf.no_fixed` makes that a theorem rather than a
     remark.

  WHAT THIS DOES NOT DO, and the header of an earlier draft claimed two
  theorems this file does not contain — `energy_symExt` and `energy_antiExt`,
  the identification of R1a's energies with `2·vᵀ(A±B)⁻¹v`. **They are not
  here and the reason is worth stating**, because it is what is left of R1b:
  those need `A ± B` to be INVERTIBLE AS OPERATORS ON THE HALF, which means
  restricting them to the subtype `↥H` — the one place the subtype cannot be
  dodged. §4 gives the operator on each eigenspace; turning that into a
  statement about inverses is the remaining step.

  **So the ladder reads R1a done, R1b MOSTLY done, R2 done, R3 open, R4
  open.** Beyond the restriction-and-inverse step, R3 is that `0 ≼ B`, and
  **nothing in this file says anything whatever about the sign of `B`** —
  `crossOp_symm` says it is symmetric and that is all. No theorem here proves
  reflection positivity for any half with more than one element.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import GraphReflection

namespace GraphHalfSpace

open Finset Matrix GraphLaplacian GraphReflection

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. A half -/

/-- `H` is a HALF for the involution `θ`: every vertex is in exactly one of
    `H` and `θ H`. For an involution this single condition is disjointness
    and covering together. -/
def IsHalf (θ : V ≃ V) (H : Finset V) : Prop := ∀ p, p ∈ H ↔ θ p ∉ H

variable {θ : V ≃ V} {H : Finset V}

omit [Fintype V] [DecidableEq V] in
theorem IsHalf.mem_of_notMem (hH : IsHalf θ H) {p : V} (hp : p ∉ H) : θ p ∈ H := by
  by_contra hc
  exact hp ((hH p).mpr hc)

omit [Fintype V] [DecidableEq V] in
theorem IsHalf.notMem_of_mem (hH : IsHalf θ H) {p : V} (hp : p ∈ H) : θ p ∉ H :=
  (hH p).mp hp

omit [Fintype V] [DecidableEq V] in
/-- **A half forces the reflection to have no fixed point.** So on a box of
    odd side, where the middle row is fixed, no half exists — and that is a
    theorem rather than a remark. -/
theorem IsHalf.no_fixed (hH : IsHalf θ H) (p : V) : θ p ≠ p := by
  intro hfix
  have h1 : θ p ∈ H ↔ p ∈ H := by rw [hfix]
  have h2 := hH p
  rw [h1] at h2
  tauto

/-- `θ` carries the half onto its complement, which is what lets a sum over
    all vertices be folded onto a sum over the half. -/
theorem IsHalf.image_eq (hH : IsHalf θ H) (hinv : Function.Involutive θ) :
    H.image θ = Hᶜ := by
  ext p
  simp only [Finset.mem_image, Finset.mem_compl]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact hH.notMem_of_mem hk
  · intro hp
    exact ⟨θ p, hH.mem_of_notMem hp, hinv p⟩

omit [DecidableEq V] in
/-- The fold: a sum over all vertices splits into the half and its image. -/
theorem IsHalf.sum_split (hH : IsHalf θ H) (hinv : Function.Involutive θ) (f : V → ℝ) :
    ∑ p, f p = (∑ k ∈ H, f k) + ∑ k ∈ H, f (θ k) := by
  classical
  have himg : ∑ k ∈ H, f (θ k) = ∑ p ∈ Hᶜ, f p := by
    rw [← hH.image_eq hinv, Finset.sum_image]
    intro x _ y _ hxy
    exact θ.injective hxy
  rw [himg, ← Finset.sum_add_sum_compl H f]

/-! ## 2. Even and odd extensions -/

/-- Extend a function on the half to the whole graph, evenly. -/
noncomputable def symExt (θ : V ≃ V) (H : Finset V) (v : V → ℝ) : V → ℝ :=
  fun p => if p ∈ H then v p else v (θ p)

/-- Extend a function on the half to the whole graph, oddly. -/
noncomputable def antiExt (θ : V ≃ V) (H : Finset V) (v : V → ℝ) : V → ℝ :=
  fun p => if p ∈ H then v p else -v (θ p)

omit [Fintype V] in
@[simp] theorem symExt_of_mem {v : V → ℝ} {p : V} (hp : p ∈ H) :
    symExt θ H v p = v p := by simp [symExt, hp]

omit [Fintype V] in
@[simp] theorem antiExt_of_mem {v : V → ℝ} {p : V} (hp : p ∈ H) :
    antiExt θ H v p = v p := by simp [antiExt, hp]

omit [Fintype V] in
@[simp] theorem symExt_of_notMem {v : V → ℝ} {p : V} (hp : p ∉ H) :
    symExt θ H v p = v (θ p) := by simp [symExt, hp]

omit [Fintype V] in
@[simp] theorem antiExt_of_notMem {v : V → ℝ} {p : V} (hp : p ∉ H) :
    antiExt θ H v p = -v (θ p) := by simp [antiExt, hp]

/-! ## 3. The cross-coupling

`A` needs no definition: on the half it is `massive` itself, read at two
vertices of `H`. Only `B` is new.
-/

/-- `B` — the coupling across the cut: `B p q = massive p (θ q)`. Defined on
    all of `V`, and read on `H`; §4 never evaluates it anywhere else. -/
noncomputable def crossOp (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ)
    (θ : V ≃ V) : Matrix V V ℝ :=
  Matrix.of fun p q => GraphLaplacian.massive G m p (θ q)

/-- **`B` is symmetric**, and this is where the automorphism is spent: the
    proof reflects both arguments and then uses the symmetry of `massive`. -/
theorem crossOp_symm (h : IsRefl G θ) (p q : V) :
    crossOp G m θ p q = crossOp G m θ q p := by
  have hmass : ∀ x y : V, GraphLaplacian.massive G m (θ x) (θ y)
      = GraphLaplacian.massive G m x y := fun x y =>
    congrFun (congrFun (h.massive m) x) y
  have hsymm : ∀ x y : V, GraphLaplacian.massive G m x y
      = GraphLaplacian.massive G m y x := fun x y =>
    congrFun (congrFun (GraphLaplacian.massive_isSymm G m) y) x
  simp only [crossOp, Matrix.of_apply]
  rw [hsymm p (θ q), ← hmass (θ q) p, h.invol q]

/-! ## 4. The decomposition — R1b

`massive` acts as `A + B` on evenly extended functions and as `A − B` on
oddly extended ones. One sum split, one reindexing, and — for the half of
the statement off `H` — the invariance of `massive` under `θ`.
-/

private theorem mulVec_symExt_apply (hH : IsHalf θ H) (h : IsRefl G θ) (v : V → ℝ) (p : V) :
    (GraphLaplacian.massive G m *ᵥ symExt θ H v) p
      = ∑ k ∈ H, (GraphLaplacian.massive G m p k + crossOp G m θ p k) * v k := by
  classical
  have hexp : (GraphLaplacian.massive G m *ᵥ symExt θ H v) p
      = ∑ q, GraphLaplacian.massive G m p q * symExt θ H v q := rfl
  rw [hexp, hH.sum_split h.invol, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [symExt_of_mem hk, symExt_of_notMem (hH.notMem_of_mem hk), h.invol k]
  simp only [crossOp, Matrix.of_apply]
  ring

private theorem mulVec_antiExt_apply (hH : IsHalf θ H) (h : IsRefl G θ) (v : V → ℝ) (p : V) :
    (GraphLaplacian.massive G m *ᵥ antiExt θ H v) p
      = ∑ k ∈ H, (GraphLaplacian.massive G m p k - crossOp G m θ p k) * v k := by
  classical
  have hexp : (GraphLaplacian.massive G m *ᵥ antiExt θ H v) p
      = ∑ q, GraphLaplacian.massive G m p q * antiExt θ H v q := rfl
  rw [hexp, hH.sum_split h.invol, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [antiExt_of_mem hk, antiExt_of_notMem (hH.notMem_of_mem hk), h.invol k]
  simp only [crossOp, Matrix.of_apply]
  ring

/-- **THE MASSIVE OPERATOR PRESERVES EVEN EXTENSIONS AND ACTS AS `A + B`.**
    R1b, half of it, with no block matrix anywhere. -/
theorem massive_mulVec_symExt (hH : IsHalf θ H) (h : IsRefl G θ) (v : V → ℝ) :
    GraphLaplacian.massive G m *ᵥ symExt θ H v
      = symExt θ H (fun p => ∑ k ∈ H,
          (GraphLaplacian.massive G m p k + crossOp G m θ p k) * v k) := by
  classical
  funext p
  rw [mulVec_symExt_apply hH h v p]
  by_cases hp : p ∈ H
  · rw [symExt_of_mem hp]
  · rw [symExt_of_notMem hp]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hmass : ∀ x y : V, GraphLaplacian.massive G m (θ x) (θ y)
        = GraphLaplacian.massive G m x y := fun x y =>
      congrFun (congrFun (h.massive m) x) y
    have h1 : GraphLaplacian.massive G m (θ p) k = crossOp G m θ p k := by
      simp only [crossOp, Matrix.of_apply]
      rw [← hmass p (θ k), h.invol k]
    have h2 : crossOp G m θ (θ p) k = GraphLaplacian.massive G m p k := by
      simp only [crossOp, Matrix.of_apply]
      exact hmass p k
    rw [h1, h2]
    ring

/-- **AND AS `A − B` ON ODD EXTENSIONS.** -/
theorem massive_mulVec_antiExt (hH : IsHalf θ H) (h : IsRefl G θ) (v : V → ℝ) :
    GraphLaplacian.massive G m *ᵥ antiExt θ H v
      = antiExt θ H (fun p => ∑ k ∈ H,
          (GraphLaplacian.massive G m p k - crossOp G m θ p k) * v k) := by
  classical
  funext p
  rw [mulVec_antiExt_apply hH h v p]
  by_cases hp : p ∈ H
  · rw [antiExt_of_mem hp]
  · rw [antiExt_of_notMem hp]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hmass : ∀ x y : V, GraphLaplacian.massive G m (θ x) (θ y)
        = GraphLaplacian.massive G m x y := fun x y =>
      congrFun (congrFun (h.massive m) x) y
    have h1 : GraphLaplacian.massive G m (θ p) k = crossOp G m θ p k := by
      simp only [crossOp, Matrix.of_apply]
      rw [← hmass p (θ k), h.invol k]
    have h2 : crossOp G m θ (θ p) k = GraphLaplacian.massive G m p k := by
      simp only [crossOp, Matrix.of_apply]
      exact hmass p k
    rw [h1, h2]
    ring

/-- **`A + B` AS A MATRIX.** For `v` supported on the half, the sum over
    the half in §4 is an honest matrix–vector product. -/
theorem massive_mulVec_symExt' (hH : IsHalf θ H) (h : IsRefl G θ) {v : V → ℝ}
    (hv : ∀ p, p ∉ H → v p = 0) :
    GraphLaplacian.massive G m *ᵥ symExt θ H v
      = symExt θ H ((GraphLaplacian.massive G m + crossOp G m θ) *ᵥ v) := by
  classical
  rw [massive_mulVec_symExt hH h v]
  congr 1
  funext p
  have hfold : ((GraphLaplacian.massive G m + crossOp G m θ) *ᵥ v) p
      = ∑ k ∈ H, (GraphLaplacian.massive G m p k + crossOp G m θ p k) * v k := by
    have hsub : (∑ q, (GraphLaplacian.massive G m + crossOp G m θ) p q * v q)
        = ∑ k ∈ H, (GraphLaplacian.massive G m + crossOp G m θ) p k * v k :=
      (Finset.sum_subset (Finset.subset_univ H)
        (fun x _ hx => by rw [hv x hx, mul_zero])).symm
    calc ((GraphLaplacian.massive G m + crossOp G m θ) *ᵥ v) p
        = ∑ q, (GraphLaplacian.massive G m + crossOp G m θ) p q * v q := rfl
      _ = ∑ k ∈ H, (GraphLaplacian.massive G m + crossOp G m θ) p k * v k := hsub
      _ = ∑ k ∈ H, (GraphLaplacian.massive G m p k + crossOp G m θ p k) * v k :=
          Finset.sum_congr rfl fun k _ => by simp [Matrix.add_apply]
  rw [hfold]

/-- **`A − B` AS A MATRIX.** -/
theorem massive_mulVec_antiExt' (hH : IsHalf θ H) (h : IsRefl G θ) {v : V → ℝ}
    (hv : ∀ p, p ∉ H → v p = 0) :
    GraphLaplacian.massive G m *ᵥ antiExt θ H v
      = antiExt θ H ((GraphLaplacian.massive G m - crossOp G m θ) *ᵥ v) := by
  classical
  rw [massive_mulVec_antiExt hH h v]
  congr 1
  funext p
  have hfold : ((GraphLaplacian.massive G m - crossOp G m θ) *ᵥ v) p
      = ∑ k ∈ H, (GraphLaplacian.massive G m p k - crossOp G m θ p k) * v k := by
    have hsub : (∑ q, (GraphLaplacian.massive G m - crossOp G m θ) p q * v q)
        = ∑ k ∈ H, (GraphLaplacian.massive G m - crossOp G m θ) p k * v k :=
      (Finset.sum_subset (Finset.subset_univ H)
        (fun x _ hx => by rw [hv x hx, mul_zero])).symm
    calc ((GraphLaplacian.massive G m - crossOp G m θ) *ᵥ v) p
        = ∑ q, (GraphLaplacian.massive G m - crossOp G m θ) p q * v q := rfl
      _ = ∑ k ∈ H, (GraphLaplacian.massive G m - crossOp G m θ) p k * v k := hsub
      _ = ∑ k ∈ H, (GraphLaplacian.massive G m p k - crossOp G m θ p k) * v k :=
          Finset.sum_congr rfl fun k _ => by simp [Matrix.sub_apply]
  rw [hfold]

/-! ## 5. The energies of R1a, in terms of the half

`GraphReflection.reflectionPositive_iff_energy_le` compares
`energy (sym θ c)` with `energy (anti θ c)`. For `c` supported on the half
those are the even and odd extensions of `c`, and §4 identifies the operator
on each. What remains to compare them is R2, applied to `A ± B`.
-/

omit [Fintype V] in
theorem sym_eq_symExt (hH : IsHalf θ H) {c : V → ℝ} (hc : ∀ p, p ∉ H → c p = 0) :
    GraphReflection.sym θ c = symExt θ H c := by
  funext p
  by_cases hp : p ∈ H
  · rw [symExt_of_mem hp]
    simp only [GraphReflection.sym]
    rw [hc _ (hH.notMem_of_mem hp)]
    ring
  · rw [symExt_of_notMem hp]
    simp only [GraphReflection.sym]
    rw [hc p hp]
    ring

omit [Fintype V] in
theorem anti_eq_antiExt (hH : IsHalf θ H) {c : V → ℝ} (hc : ∀ p, p ∉ H → c p = 0) :
    GraphReflection.anti θ c = antiExt θ H c := by
  funext p
  by_cases hp : p ∈ H
  · rw [antiExt_of_mem hp]
    simp only [GraphReflection.anti]
    rw [hc _ (hH.notMem_of_mem hp)]
    ring
  · rw [antiExt_of_notMem hp]
    simp only [GraphReflection.anti]
    rw [hc p hp]
    ring

/-- **REFLECTION POSITIVITY, IN TERMS OF THE HALF.** Combining R1a with §4:
    the property compares the energies of the odd and even extensions, and
    §4 says which operator governs each. -/
theorem reflectionPositive_iff_ext (hH : IsHalf θ H) (h : IsRefl G θ) :
    GraphReflection.ReflectionPositive G m θ H
      ↔ ∀ c : V → ℝ, (∀ p, p ∉ H → c p = 0) →
          GraphReflection.energy G m (antiExt θ H c)
            ≤ GraphReflection.energy G m (symExt θ H c) := by
  rw [GraphReflection.reflectionPositive_iff_energy_le h H]
  constructor
  · intro hle c hc
    rw [← sym_eq_symExt hH hc, ← anti_eq_antiExt hH hc]
    exact hle c hc
  · intro hle c hc
    rw [sym_eq_symExt hH hc, anti_eq_antiExt hH hc]
    exact hle c hc

/-! ## 6. A half exists — on a box of even side -/

section Box

open BoxGraph

variable {d n : ℕ}

/-- The sites whose `i`-th coordinate lies below the midline. -/
def lowerHalf (i : Fin d) (n : ℕ) : Finset (BoxGraph.Site d n) :=
  Finset.univ.filter fun p => 2 * (p i).val < n

/-- **ON A BOX OF EVEN SIDE THE LOWER HALF IS A HALF.** -/
theorem isHalf_lowerHalf (i : Fin d) {n : ℕ} (hn : Even n) :
    IsHalf (GraphReflection.revSite (n := n) i) (lowerHalf i n) := by
  intro p
  simp only [lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and,
    GraphReflection.revSite_apply_self]
  have hrev := Fin.val_rev (p i)
  have hlt := (p i).isLt
  obtain ⟨k, hk⟩ := hn
  omega

/-- And on a box of ODD side there is none, because the middle site is
    fixed. Stated through `IsHalf.no_fixed` rather than asserted. -/
theorem not_isHalf_of_odd {k : ℕ} (i : Fin d)
    (H : Finset (BoxGraph.Site d (2 * k + 1))) :
    ¬ IsHalf (GraphReflection.revSite (n := 2 * k + 1) i) H := by
  intro hH
  refine hH.no_fixed (fun _ => ⟨k, by omega⟩) ?_
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [GraphReflection.revSite_apply_self]
    exact Fin.ext (by simp [Fin.val_rev]; omega)
  · exact GraphReflection.revSite_apply_ne hj _

end Box

/-! ## 7. Review round 81 — the ways this could be hollow

**"The probe costed this at two-to-three units. What happened?"** The probe
assumed the classical route — an index `Equiv` onto `H ⊕ H`,
`Matrix.reindex`, `fromBlocks`, and a derivation reconciling Mathlib's Schur
complement (`A − B A⁻¹ B`) with the `A ∓ B` the ladder needs. **None of it is
here.** The decomposition is a statement about `massive *ᵥ ·` on evenly and
oddly extended functions, and in that form it is one sum split plus one
reindexing. So the estimate was wrong, in the direction of over-costing this
time, and the reason is the same as ERRATUM 61's: **the estimate priced the
first route that came to mind.** Two estimates now, both wrong, one high and
one low, both from the same cause.

**"So is R1 done?"** Mostly, and the shortfall was found by adversarial
review of this file's own header rather than by the compiler. The draft
header advertised `energy_symExt` and `energy_antiExt` — the two energies as
`2·vᵀ(A±B)⁻¹v` — **and neither exists.** They need `A ± B` inverted as
operators on the half, which needs the subtype `↥H`; §4 and §5 identify the
operator on each eigenspace and stop there. That is the residue of R1b, it is
bounded, and it is now stated instead of advertised. **What is NOT done at
all is R3**: nothing here says anything about the sign of `B`, and without
`0 ≼ B` the comparison `A − B ≼ A + B` is unavailable and R2 has nothing to
act on.

**"§5 could be doing the support condition twice."** It is not:
`sym_eq_symExt` and `anti_eq_antiExt` are where the support condition is
consumed, and they consume it in the only place it is needed — turning
`GraphReflection.sym`, which mirrors an arbitrary vector, into `symExt`,
which extends a vector on the half. `reflectionPositive_iff_ext` then carries
it through the `Iff` unchanged. Both directions are proved because both are
used.

**"`IsHalf` could be the wrong definition."** It is one condition,
`p ∈ H ↔ θ p ∉ H`, and §1 derives from it everything the rest of the file
uses: `mem_of_notMem`, `notMem_of_mem`, `image_eq` and `sum_split`. It also
has a consequence that could have gone wrong and did not:
**`IsHalf.no_fixed` — a half forces the reflection to be fixed-point free.**
That is how §6 proves an odd box admits no half at all, which is a fact the
watchlist had recorded as a remark about the parity of `n` and which is now
a theorem.

**"§6 could be vacuous — is `lowerHalf` ever nonempty?"** For `n = 0` the
site type is empty and everything is vacuous; for `n ≥ 2` even, the sites
with `2·(p i) < n` are exactly half of them. The theorem does not assert
nonemptiness and does not need to: `IsHalf` is a statement about membership,
and `reflectionPositive_iff_ext` is an `Iff` that is content-free on an empty
half — which `LatticeReflection.reflectionPositive_empty` already recorded as
a degenerate corner to watch for. **No theorem here claims a nonempty half
is reflection-positive.**
-/

end GraphHalfSpace
