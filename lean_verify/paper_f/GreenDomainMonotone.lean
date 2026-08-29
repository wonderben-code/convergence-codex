import MatrixLoewner
import GraphGreenPositive

/-!
# Cutting a subdomain out lowers the propagator: domain monotonicity in the Loewner order

`LatticeFieldTight` proved the placed lattice Gaussian fields are a **tight** family, and its
header says what tightness is not:

> it is **not** the infinite-volume limit. Tightness gives *a* limit measure along a subnet;
> identifying that limit as the `ℤ^d` free field needs `G_n(x,y) → G(x,y)`, which nothing here
> touches and which `FieldTightness` named as where the analysis actually lives. **W2's leg does
> not move.**

`G_n(x,y) → G(x,y)` is a statement about propagators on **growing domains**, and the estate had
nothing at all about how a propagator changes when the domain changes. `GreenLargeMass` bounds it
above by `m⁻²` at a fixed graph; `MatrixLoewner.green_antitone` compares two graphs on the **same**
vertex set; and all **nine** occurrences of an `inv_submatrix` lemma in `paper_f` — one in
`GraphReflection`, four in `LatticeReflection`, one in `LatticeReflectionPositive`, two in
`PrismGreen`, one in `PrismTransfer` — are `Matrix.inv_submatrix_equiv`, at an `Equiv`, where
nothing is cut and the statement is an **equality**.

**This file is the inequality that holds when something is cut.**

## What is proved

* `isGreatest_dotProduct_inv_mulVec` — `xᵀA⁻¹x` is the **greatest** value of `2⟨x,z⟩ − zᵀAz`,
  attained at `z = A⁻¹x`;
* `posDef_submatrix` — a principal submatrix along an **injection** is positive definite. Mathlib
  v4.29.1 has `Matrix.PosSemidef.submatrix` at an arbitrary index map and no definite counterpart;
  injectivity is what the definite case needs, and the `Finsupp` route is the same one;
* **`inv_submatrix_le_submatrix_inv`** — `(A_W)⁻¹ ≼ (A⁻¹)_W`, for `A` positive definite and `W`
  placed in the ambient index type by any injection;
* **`greenDirichlet_le_submatrix`** — the same statement about the propagator, for
  `greenDirichlet K m e := ((massive K m)_W)⁻¹`;
* **`greenDirichlet_mono`** — nested subdomains: cutting further can only lower it;
* **`greenDirichlet_le_green_comap`** — and it lies below the **free** propagator of the induced
  subgraph as well, the gap being the boundary degree (`massive_comap_le_submatrix`, and
  `comap_degree_le` for why that degree is non-negative);
* `greenDirichlet_equiv` — at an `Equiv` it is an **equality**, so the general inequality has not
  quietly changed the object;
* **`greenDirichlet_lt_green_of_degree_pos`** — and at a one-site cut of a connected graph it is
  **strict**, so the inequality is not an equality wearing a general statement. The identity behind
  that is `(deg v + m²)·G(v,v) = 1 + Σ_{u ∼ v} G(u,v)`, read off one entry of `massive · green = 1`.

## The proof is completing the square

`(z − A⁻¹x)ᵀA(z − A⁻¹x) = zᵀAz − 2⟨x,z⟩ + xᵀA⁻¹x` (`quadForm_shift`), which is the `IsGreatest`
statement and nothing else. The main theorem is that statement used twice: on the submatrix it
gives the exact value at `x`, and on the ambient matrix it gives an **upper bound** at the
extension by zero of the maximiser. Extension by zero is the only other ingredient, and the two
facts about it that are needed — `dotProduct_ext` and `quadForm_ext` — are exactly what makes the
submatrix's form a restriction of the ambient one. **No block decomposition appears**, which is
worth saying only because a Schur complement is the route a reader expects; whether that route also
works here is untested.

## What this is NOT

**It is not a convergence theorem, and `W2`'s leg does not move.** The fence quoted above asks for
`G_n(x,y) → G(x,y)`. Three things stand between a monotonicity and that: there is no infinite
ambient object in this estate for a limit to live in — everything here sits inside **one finite
graph** `K`; no sequence of subdomains is indexed, so "monotone and bounded" is not applied to
anything; and no limit is taken. **A step an argument uses is not the argument.** That is the same
distinction `LatticeUniformStein` draws about tightness, drawn here *before* anything downstream
reads this file rather than after (`ERRATUM 334`).

> **^ AND "THREE THINGS STAND BETWEEN" IS ABOUT THIS ROUTE, NOT ABOUT THE STATEMENT** — added the
> same day, with the paragraph above kept as written (`ERRATUM 94`, `ERRATUM 335`). The three are
> what monotone-plus-bounded would need, because that argument needs every domain inside one fixed
> ambient graph. `WALLS.md` §W2.1 §4 is the account of this step and reaches the same convergence
> without an infinite-volume operator anywhere in it. **A reader arriving at the paragraph above
> should not conclude that the convergence waits on `ℤ^d` being a graph here; only this route
> does.**

**`greenDirichlet` is a new object and nothing in the estate uses it.** `gaussianField K m` has
covariance `green K m`, the propagator of the graph itself — on a box, the free boundary condition
and not this one. So no theorem about `gaussianField`, about `LatticeFieldWitness`, or anywhere in
the Poincaré chain changes, and nothing here supersedes anything.
`greenDirichlet_le_green_comap` is the one place the two objects meet, and it relates them by an
inequality rather than identifying them.

**No measure is built from `greenDirichlet`.** It is positive definite (`greenDirichlet_posDef`),
so the estate's Gaussian machinery would accept it as a covariance. That construction is not done
here and no probabilistic statement is made about it.

**`Dirichlet` in the name is the standard name for the inverse of the compressed operator, and the
killed-walk reading of it is not formalised here.** Everything proved is about a principal
submatrix of `massive`.

**The estate already had extension by zero, in another packaging, and this file does not use it.**
`NullSpaceDimension.supportedOn` bundles *"vanishes off `H`"* as a submodule and
`supportedOnEquiv` is that same extension by zero; thirteen files mention it. It is indexed by a
`Finset V`, where `ext` here is indexed by an arbitrary injection `W → V` — which is what
`greenDirichlet_mono` needs, since composing two injections is how "nested subdomains" gets said.
**Neither of the two facts this file actually consumes — `dotProduct_ext` and `quadForm_ext` —
exists for either packaging**, so nothing was re-proved; what was missed is that the estate had
the notion at all, and it was found by grepping for the SHAPE only after the file was written.
A bridge is deliberately not built here — `NullSpaceDimension` transitively imports 51 files of
`paper_f` against this file's 12 — and is recorded on the watchlist instead.

**`OS4` does not move, no spectral gap is claimed, and no published tag or website page moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace GreenDomainMonotone

open Matrix GraphLaplacian
open scoped MatrixOrder

variable {V W W' : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable [Fintype W'] [DecidableEq W']

/-! ## 1. Completing the square -/

section Square

variable {A : Matrix V V ℝ}

omit [DecidableEq V] in
/-- For a symmetric matrix the quadratic pairing may be moved across. -/
theorem dotProduct_mulVec_symm (hA : A.IsSymm) (u z : V → ℝ) :
    u ⬝ᵥ (A *ᵥ z) = (A *ᵥ u) ⬝ᵥ z := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA]

/-- **COMPLETING THE SQUARE.** -/
theorem quadForm_shift (hA : A.IsSymm) (h : IsUnit A.det) (x z : V → ℝ) :
    (z - A⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (z - A⁻¹ *ᵥ x))
      = z ⬝ᵥ (A *ᵥ z) - (2 * (x ⬝ᵥ z) - x ⬝ᵥ (A⁻¹ *ᵥ x)) := by
  have hAu : A *ᵥ (A⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h, Matrix.one_mulVec]
  have h1 : z ⬝ᵥ (A *ᵥ (A⁻¹ *ᵥ x)) = x ⬝ᵥ z := by rw [hAu, dotProduct_comm]
  have h2 : (A⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ z) = x ⬝ᵥ z := by
    rw [dotProduct_mulVec_symm hA, hAu]
  have h3 : (A⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (A⁻¹ *ᵥ x)) = x ⬝ᵥ (A⁻¹ *ᵥ x) := by
    rw [hAu, dotProduct_comm]
  rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, h1, h2, h3]
  ring

/-- Every quadratic tangent lies below the inverse form. -/
theorem le_dotProduct_inv_mulVec (hps : A.PosSemidef) (h : IsUnit A.det) (x z : V → ℝ) :
    2 * (x ⬝ᵥ z) - z ⬝ᵥ (A *ᵥ z) ≤ x ⬝ᵥ (A⁻¹ *ᵥ x) := by
  have hA : A.IsSymm := by
    have hh := hps.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at hh
  have hnn := hps.dotProduct_mulVec_nonneg (z - A⁻¹ *ᵥ x)
  rw [star_trivial, quadForm_shift hA h] at hnn
  linarith

/-- The tangent is attained at `z = A⁻¹x`. -/
theorem dotProduct_inv_mulVec_eq (h : IsUnit A.det) (x : V → ℝ) :
    2 * (x ⬝ᵥ (A⁻¹ *ᵥ x)) - (A⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (A⁻¹ *ᵥ x)) = x ⬝ᵥ (A⁻¹ *ᵥ x) := by
  have hAu : A *ᵥ (A⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h, Matrix.one_mulVec]
  rw [hAu, dotProduct_comm]
  ring

/-- **THE VARIATIONAL CHARACTERISATION OF THE INVERSE FORM.** -/
theorem isGreatest_dotProduct_inv_mulVec (hps : A.PosSemidef) (h : IsUnit A.det) (x : V → ℝ) :
    IsGreatest {c : ℝ | ∃ z : V → ℝ, c = 2 * (x ⬝ᵥ z) - z ⬝ᵥ (A *ᵥ z)} (x ⬝ᵥ (A⁻¹ *ᵥ x)) :=
  ⟨⟨A⁻¹ *ᵥ x, (dotProduct_inv_mulVec_eq h x).symm⟩, by
    rintro c ⟨z, rfl⟩
    exact le_dotProduct_inv_mulVec hps h x z⟩

end Square

/-! ## 2. Extension by zero -/

section Ext

variable {e : W → V}

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
/-- Extension by zero along a map of index types. -/
noncomputable def ext (e : W → V) (y : W → ℝ) : V → ℝ := Function.extend e y 0

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
theorem ext_apply (he : Function.Injective e) (y : W → ℝ) (w : W) : ext e y (e w) = y w :=
  he.extend_apply y 0 w

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
theorem ext_apply_of_not_mem {v : V} (hv : ¬ ∃ w, e w = v) (y : W → ℝ) : ext e y v = 0 :=
  Function.extend_apply' y (0 : V → ℝ) v hv

omit [DecidableEq V] [DecidableEq W] in
/-- A sum over `V` of something supported on the image of `e` is a sum over `W`. -/
theorem sum_ext {M : Type*} [AddCommMonoid M] (he : Function.Injective e) (f : V → M)
    (hf : ∀ v : V, (¬ ∃ w, e w = v) → f v = 0) : ∑ v, f v = ∑ w, f (e w) := by
  classical
  have h1 : ∑ v ∈ (Finset.univ.image e), f v = ∑ w, f (e w) :=
    Finset.sum_image fun a _ b _ hab => he hab
  rw [← h1]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro v _ hv
  refine hf v ?_
  rintro ⟨w, rfl⟩
  exact hv (Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩)

omit [DecidableEq V] [DecidableEq W] in
theorem dotProduct_ext (he : Function.Injective e) (x y : W → ℝ) :
    ext e x ⬝ᵥ ext e y = x ⬝ᵥ y := by
  rw [dotProduct, dotProduct]
  refine (sum_ext he _ ?_).trans (Finset.sum_congr rfl fun w _ => ?_)
  · intro v hv
    rw [ext_apply_of_not_mem hv, zero_mul]
  · rw [ext_apply he, ext_apply he]

omit [DecidableEq V] [DecidableEq W] in
/-- **THE QUADRATIC FORM OF `A` ON EXTENDED VECTORS IS THE FORM OF THE SUBMATRIX.** -/
theorem quadForm_ext (he : Function.Injective e) (A : Matrix V V ℝ) (y : W → ℝ) :
    ext e y ⬝ᵥ (A *ᵥ ext e y) = y ⬝ᵥ ((A.submatrix e e) *ᵥ y) := by
  rw [dotProduct, dotProduct]
  refine (sum_ext he _ ?_).trans (Finset.sum_congr rfl fun w _ => ?_)
  · intro v hv
    rw [ext_apply_of_not_mem hv, zero_mul]
  · rw [ext_apply he]
    congr 1
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
    refine (sum_ext he _ ?_).trans (Finset.sum_congr rfl fun w' _ => ?_)
    · intro v hv
      rw [ext_apply_of_not_mem hv, mul_zero]
    · rw [ext_apply he, Matrix.submatrix_apply]

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
theorem ext_ne_zero (he : Function.Injective e) {x : W → ℝ} (hx : x ≠ 0) : ext e x ≠ 0 := by
  intro hz
  refine hx (funext fun w => ?_)
  have hw := congrFun hz (e w)
  rwa [ext_apply he] at hw

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
/-- **A PRINCIPAL SUBMATRIX ALONG AN INJECTION IS POSITIVE DEFINITE.** Mathlib has this for
`PosSemidef` at an arbitrary index map; definiteness needs the map to be injective, and the
`Finsupp` route is the same one. -/
theorem posDef_submatrix (he : Function.Injective e) {A : Matrix V V ℝ} (hA : A.PosDef) :
    (A.submatrix e e).PosDef := by
  refine ⟨hA.isHermitian.submatrix e, fun {x} hx => ?_⟩
  have hne : Finsupp.mapDomain e x ≠ 0 := by
    intro h
    exact hx (Finsupp.mapDomain_injective he (by rw [h, Finsupp.mapDomain_zero]))
  simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using hA.2 hne

omit [Fintype V] [DecidableEq V] in
/-- The one-site placement is injective, so the strict statement in §5 is an instance of the
general inequality rather than a separate claim. -/
theorem injective_const_unit (v : V) : Function.Injective (fun _ : Unit => v) :=
  fun a b _ => Subsingleton.elim a b

end Ext

/-! ## 3. Domain monotonicity -/

/-- **THE INVERSE OF A PRINCIPAL SUBMATRIX SITS BELOW THE SUBMATRIX OF THE INVERSE.** -/
theorem inv_submatrix_le_submatrix_inv {e : W → V} (he : Function.Injective e)
    {A : Matrix V V ℝ} (hA : A.PosDef) :
    (A.submatrix e e)⁻¹ ≤ (A⁻¹).submatrix e e := by
  have hB : (A.submatrix e e).PosDef := posDef_submatrix he hA
  have hdetA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hdetB : IsUnit (A.submatrix e e).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_)
  · exact (hA.inv.isHermitian.submatrix e).sub hB.inv.isHermitian
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg]
    have hkey := le_dotProduct_inv_mulVec hA.posSemidef hdetA (ext e x)
      (ext e ((A.submatrix e e)⁻¹ *ᵥ x))
    rw [dotProduct_ext he, quadForm_ext he, quadForm_ext he,
      dotProduct_inv_mulVec_eq hdetB] at hkey
    exact hkey

omit [Fintype V] [DecidableEq V] in
/-- Nested subdomains: cutting further can only lower the inverse form. -/
theorem inv_submatrix_comp_le {e₁ : W → W'} {e₂ : W' → V} (he₁ : Function.Injective e₁)
    (he₂ : Function.Injective e₂) {A : Matrix V V ℝ} (hA : A.PosDef) :
    (A.submatrix (e₂ ∘ e₁) (e₂ ∘ e₁))⁻¹ ≤ ((A.submatrix e₂ e₂)⁻¹).submatrix e₁ e₁ := by
  have h := inv_submatrix_le_submatrix_inv he₁ (posDef_submatrix he₂ hA)
  rwa [Matrix.submatrix_submatrix] at h

omit [Fintype W] [DecidableEq W] in
/-- A Loewner inequality compares diagonal entries. -/
theorem diag_le_of_le {A B : Matrix W W ℝ} (h : A ≤ B) (w : W) : A w w ≤ B w w := by
  have hd := (Matrix.le_iff.mp h).diag_nonneg (i := w)
  rw [Matrix.sub_apply, sub_nonneg] at hd
  exact hd

/-! ## 4. The graph reading -/

section Graph

variable (K : SimpleGraph V) [DecidableRel K.Adj] {m : ℝ}

/-- **THE DIRICHLET PROPAGATOR OF A SUBDOMAIN**: invert the ambient massive operator's principal
submatrix, rather than the subdomain's own massive operator. -/
noncomputable def greenDirichlet (m : ℝ) (e : W → V) : Matrix W W ℝ :=
  ((massive K m).submatrix e e)⁻¹

theorem greenDirichlet_posDef {e : W → V} (he : Function.Injective e) (hm : m ≠ 0) :
    (greenDirichlet K m e).PosDef :=
  (posDef_submatrix he (massive_posDef K hm)).inv

/-- **DOMAIN MONOTONICITY OF THE PROPAGATOR.** -/
theorem greenDirichlet_le_submatrix {e : W → V} (he : Function.Injective e) (hm : m ≠ 0) :
    greenDirichlet K m e ≤ (green K m).submatrix e e :=
  inv_submatrix_le_submatrix_inv he (massive_posDef K hm)

/-- **NESTED SUBDOMAINS.** -/
theorem greenDirichlet_mono {e₁ : W → W'} {e₂ : W' → V} (he₁ : Function.Injective e₁)
    (he₂ : Function.Injective e₂) (hm : m ≠ 0) :
    greenDirichlet K m (e₂ ∘ e₁) ≤ (greenDirichlet K m e₂).submatrix e₁ e₁ :=
  inv_submatrix_comp_le he₁ he₂ (massive_posDef K hm)

/-- The diagonal form of domain monotonicity. -/
theorem greenDirichlet_diag_le {e : W → V} (he : Function.Injective e) (hm : m ≠ 0) (w : W) :
    greenDirichlet K m e w w ≤ green K m (e w) (e w) := by
  have h := diag_le_of_le (greenDirichlet_le_submatrix K he hm) w
  rwa [Matrix.submatrix_apply] at h

/-! ### And below the FREE propagator of the induced subgraph -/

/-- The induced adjacency is decidable when the ambient one is. -/
instance decidableRelComap (e : W → V) : DecidableRel (K.comap e).Adj :=
  fun a b => inferInstanceAs (Decidable (K.Adj (e a) (e b)))

omit [DecidableEq V] [DecidableEq W] in
/-- **THE INDUCED SUBGRAPH HAS NO MORE NEIGHBOURS THAN THE AMBIENT GRAPH.** Injectivity is what
makes this a statement about neighbours rather than about a multiset of them. -/
theorem comap_degree_le {e : W → V} (he : Function.Injective e) (w : W) :
    (K.comap e).degree w ≤ K.degree (e w) := by
  classical
  rw [SimpleGraph.degree, SimpleGraph.degree]
  refine Finset.card_le_card_of_injOn e (fun w' hw' => ?_) (he.injOn)
  simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw' ⊢
  exact hw'

/-- **THE DIRICHLET OPERATOR IS THE FREE ONE PLUS THE BOUNDARY DEGREE**, and the boundary degree
is a non-negative diagonal. Off the diagonal the two operators agree entry for entry, because
`(K.comap e).Adj a b` is `K.Adj (e a) (e b)` by definition. -/
theorem massive_comap_le_submatrix {e : W → V} (he : Function.Injective e) (m : ℝ) :
    massive (K.comap e) m ≤ (massive K m).submatrix e e := by
  have hdiff : (massive K m).submatrix e e - massive (K.comap e) m
      = Matrix.diagonal (fun w => (K.degree (e w) : ℝ) - ((K.comap e).degree w : ℝ)) := by
    ext a b
    rw [Matrix.sub_apply, Matrix.submatrix_apply, massive_apply, massive_apply,
      Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab, he.ne hab, SimpleGraph.comap_adj]
  rw [Matrix.le_iff, hdiff]
  refine Matrix.posSemidef_diagonal_iff.mpr fun w => ?_
  rw [sub_nonneg, Nat.cast_le]
  exact comap_degree_le K he w

/-- **CUTTING WITH DIRICHLET CONDITIONS SITS BELOW CUTTING WITH FREE ONES.** The subdomain's own
propagator — the estate's `green` at the induced subgraph, which is what `gaussianField` is built
from — is the larger of the two. -/
theorem greenDirichlet_le_green_comap {e : W → V} (he : Function.Injective e) (hm : m ≠ 0) :
    greenDirichlet K m e ≤ green (K.comap e) m :=
  MatrixLoewner.posDef_inv_le_inv (massive_posDef (K.comap e) hm)
    (massive_comap_le_submatrix K he m)

/-! ## 5. Where it is an equality, and where it is strict -/

/-- **NOTHING CUT, NOTHING LOST.** At an `Equiv` the subdomain is the whole graph relabelled and
domain monotonicity is an equality — this is Mathlib's `Matrix.inv_submatrix_equiv`, and it is the
instance that says the general inequality has not quietly changed the object. -/
theorem greenDirichlet_equiv (m : ℝ) (σ : W ≃ V) :
    greenDirichlet K m (σ : W → V) = (green K m).submatrix σ σ := by
  rw [greenDirichlet, green, Matrix.inv_submatrix_equiv]

/-- **THE SINGLE-SITE DIRICHLET PROPAGATOR** is the reciprocal of `deg v + m²`: cut away
everything but one site and what is left is that site's own diagonal entry, inverted. -/
theorem greenDirichlet_const (hm : m ≠ 0) (v : V) :
    greenDirichlet K m (fun _ : Unit => v)
      = Matrix.of (fun _ _ : Unit => ((K.degree v : ℝ) + m ^ 2)⁻¹) := by
  have hm2 : (0 : ℝ) < m ^ 2 := lt_of_le_of_ne (sq_nonneg m) (Ne.symm (pow_ne_zero 2 hm))
  have hD : (0 : ℝ) < (K.degree v : ℝ) + m ^ 2 := by positivity
  have hvv : massive K m v v = (K.degree v : ℝ) + m ^ 2 := by
    rw [massive_apply]
    simp
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  obtain rfl : i = j := Subsingleton.elim i j
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.univ_unique, Finset.sum_singleton,
    Matrix.submatrix_apply, Matrix.of_apply, hvv, mul_inv_cancel₀ (ne_of_gt hD)]

/-- **AND CUTTING IS STRICT.** On a connected graph, at a site with at least one neighbour, the
one-site Dirichlet propagator is strictly below the ambient propagator's diagonal entry. The
identity behind it is `(deg v + m²)·G(v,v) = 1 + Σ_{u ~ v} G(u,v)`, read off the `(v,v)` entry of
`massive · green = 1`; the sum is positive because `GraphGreenPositive.green_pos` says every entry
of the propagator of a connected graph is. -/
theorem inv_degree_lt_green_diag (hK : K.Connected) (hm : m ≠ 0) {v : V}
    (hdeg : 0 < K.degree v) :
    ((K.degree v : ℝ) + m ^ 2)⁻¹ < green K m v v := by
  have hm2 : (0 : ℝ) < m ^ 2 := lt_of_le_of_ne (sq_nonneg m) (Ne.symm (pow_ne_zero 2 hm))
  have hD : (0 : ℝ) < (K.degree v : ℝ) + m ^ 2 := by positivity
  have hmg : massive K m * green K m = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (massive_isUnit K hm))
  have hentry : ∑ u, massive K m v u * green K m u v = 1 := by
    have h := congrFun (congrFun hmg v) v
    rwa [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have hsplit : ∑ u, massive K m v u * green K m u v
      = (∑ u, (if v = u then ((K.degree v : ℝ) + m ^ 2) * green K m u v else 0))
        - ∑ u, (if K.Adj v u then green K m u v else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [massive_apply, sub_mul]
    congr 1
    · by_cases h : v = u
      · subst h; simp
      · simp [h]
    · by_cases h : K.Adj v u <;> simp [h]
  have hdiag : (∑ u, (if v = u then ((K.degree v : ℝ) + m ^ 2) * green K m u v else 0))
      = ((K.degree v : ℝ) + m ^ 2) * green K m v v := by simp
  obtain ⟨u₀, hu₀⟩ := (K.degree_pos_iff_exists_adj v).mp hdeg
  have hSpos : 0 < ∑ u, (if K.Adj v u then green K m u v else 0) := by
    refine Finset.sum_pos' (fun w _ => ?_) ⟨u₀, Finset.mem_univ u₀, ?_⟩
    · by_cases h : K.Adj v w
      · simpa [h] using GraphGreenPositive.green_nonneg K hm w v
      · simp [h]
    · simpa [hu₀] using GraphGreenPositive.green_pos K hK hm u₀ v
  rw [hsplit, hdiag] at hentry
  have hgt : ((K.degree v : ℝ) + m ^ 2)⁻¹ * 1
      < ((K.degree v : ℝ) + m ^ 2)⁻¹ * (((K.degree v : ℝ) + m ^ 2) * green K m v v) :=
    mul_lt_mul_of_pos_left (by linarith) (inv_pos.mpr hD)
  rwa [mul_one, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hD), one_mul] at hgt

/-- **THE GENERAL INEQUALITY IS NOT AN EQUALITY**, stated at the same matrix entry the general
theorem bounds. -/
theorem greenDirichlet_lt_green_of_degree_pos (hK : K.Connected) (hm : m ≠ 0) {v : V}
    (hdeg : 0 < K.degree v) :
    greenDirichlet K m (fun _ : Unit => v) () () < green K m v v := by
  rw [greenDirichlet_const K hm v]
  exact inv_degree_lt_green_diag K hK hm hdeg

/-- The same entry, non-strictly, straight from the general theorem — so the strict statement above
is a refinement of `greenDirichlet_diag_le` at a point where that theorem applies, not a claim
about a different object. -/
example (hm : m ≠ 0) (v : V) :
    greenDirichlet K m (fun _ : Unit => v) () () ≤ green K m v v :=
  greenDirichlet_diag_le K (injective_const_unit v) hm ()

end Graph

end GreenDomainMonotone
