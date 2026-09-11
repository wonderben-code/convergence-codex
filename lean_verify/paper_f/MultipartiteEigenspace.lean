import MultipartiteSpectrum
import CompleteFieldSymmetry

/-!
# One eigenspace of the equipartite family, named and counted — and the field symmetries that follow

**THE PREVIOUS TWO UNITS LEFT EXACTLY THIS.** `MultipartiteSpectrum` proved that the complete
equipartite graph's two Laplacians have three eigenvalues each and that those three exhaust, and
fenced the multiplicities: *nothing of the kind is done here … the dimensions `1`, `r − 1`,
`r(t − 1)` are **not** computed*. `CompleteFieldSymmetry` then showed what a multiplicity buys — a
dimension of two or more in one eigenspace turns `FieldSymmetryFinite`'s criterion into a statement
about the **measure** — and fenced that the same composition was unavailable for this family.
**This file does the third eigenspace and takes the composition.**

**WHY THE THIRD AND NOT ALL THREE.** The eigenvalue `(r − 1)t` belongs to the vectors whose every
part sum vanishes, and that subspace is the **kernel of one linear map** — the part sums, taken
together — so its dimension is `rt − r` by rank–nullity and one explicit surjectivity witness. The
other two eigenspaces are the constants (dimension one, and easy) and the part-constant vectors of
zero total sum, whose dimension `r − 1` needs an isomorphism with the zero-sum vectors of `ℝ^r` that
this file does **not** build. One eigenspace of dimension `≥ 2` is all the field-symmetry
composition needs, and the fence says the rest is undone.

**AND THE CHARACTERISATION HAS A HYPOTHESIS THAT IS NOT DECORATION.** `Q x = (r − 1)t·x` **iff**
every part sum vanishes holds for `r ≥ 2` and **fails at `r = 1`**, where the graph has no edges
at all, `Q` is the zero matrix, the eigenvalue is `0` and its eigenspace is everything while the
vanishing-part-sum vectors are a hyperplane. The proof shows where: summing the row equation over
the parts gives `r·∑x = ∑x`, which forces `∑x = 0` **because `r ≠ 1`**.

## What is proved

**`signlessLap_multi_mulVec_eq_iff`, `lapMatrix_multi_mulVec_eq_iff`** — for `r ≥ 2`, both
`Q x = (r−1)t·x` and `L x = (r−1)t·x` hold **iff** every part sum of `x` vanishes. (The two
eigenvalues coincide at this family, which is visible in the row identities: the `∑x` and
`partSum` terms cancel there.)

**`partForm`, `partForm_apply`, `surjective_partForm`, `finrank_ker_partForm`** — the part sums
as a linear map `ℝ^(r×t) → ℝ^r`, surjective once the parts are non-empty (send `y` to the vector
supported on one vertex per part), so its kernel has dimension **`rt − r`**.

**`eigenspace_signlessLap_multi_eq`, `eigenspace_lapMatrix_multi_eq`** — hence both eigenspaces at
`(r − 1)t` **are** that kernel, as submodule equalities in the `ker (toLin' M − μ • id)` form.

**`two_le_finrank_eigenspace_multi`** — and for `r ≥ 2`, `t ≥ 2` the dimension is at least two,
since `rt − r ≥ 2r − r = r ≥ 2`.

**`infinite_symmetryMatrices_multi`** — **SO THE GAUSSIAN FIELD ON A COMPLETE EQUIPARTITE GRAPH WITH
AT LEAST TWO PARTS OF AT LEAST TWO VERTICES HAS INFINITELY MANY SYMMETRIES**, at every non-zero
mass. That is `CompleteFieldSymmetry`'s conclusion for `K_n` on a two-parameter family — and
the two families overlap nowhere, `K_n` being the case `t = 1` this theorem excludes.

## What is NOT here

* **THE OTHER TWO MULTIPLICITIES.** The constants (dimension one) and the part-constant zero-sum
  vectors (dimension `r − 1`) are **not** counted, so *the three dimensions add to `rt`* — which
  `CompleteSpectrumTwoPoints` proved for `K_n` — is **not** available here. The second of the two is
  where the work is: it needs an isomorphism between the part-constant vectors and `ℝ^r`, and this
  file builds none. Neither is attempted and no cost is offered for either (`ERRATUM 246`); the
  watchlist item records both.
* **NO CARDINALITY.** `Set.Infinite` again says nothing about which infinity.
* **NOTHING AT `r = 1` OR `t = 1`.** At `r = 1` the graph is edgeless and the characterisation is
  false, which the header explains; at `t = 1` it is `K_n` and `CompleteFieldSymmetry` has it.
* **NOTHING FOR AN UNBALANCED COMPLETE MULTIPARTITE GRAPH**, as in the previous unit.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and `OS1`
  in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `r` and `t` natural numbers; `2 ≤ r` on the
two characterisations and the two eigenspace equalities, `1 ≤ t` on the surjectivity and the
dimension, `2 ≤ r` with `2 ≤ t` on the two-dimensionality and the symmetry theorem, and `m ≠ 0` only
on the last. `partForm` is `noncomputable` because the ambient inner-product structure is.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace MultipartiteEigenspace

open Matrix Finset SimpleGraph LaplacianSignless MultipartiteSpectrum
open FieldRotationCount

variable {r t : ℕ}

/-! ## 1. The third eigenvalue's eigenspace is exactly the vanishing-part-sum subspace -/

theorem signlessLap_multi_mulVec_eq_iff (hr : 2 ≤ r) {x : Fin r × Fin t → ℝ} :
    signlessLap (completeEquipartiteGraph r t) *ᵥ x = (((r : ℝ) - 1) * t) • x
      ↔ ∀ i, partSum x i = 0 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos t with ht0 | ht0
    · haveI : IsEmpty (Fin t) := by rw [ht0]; infer_instance
      intro i
      simp [partSum, Finset.univ_eq_empty]
    have hrow : ∀ v : Fin r × Fin t, (∑ u, x u) = partSum x v.1 := by
      intro v
      have hv := congrFun h v
      rw [signlessLap_multi_mulVec] at hv
      simp only [Pi.smul_apply, smul_eq_mul] at hv
      linarith
    have hne : ((r : ℝ) - 1) ≠ 0 := by
      have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    have hS : ∑ u, x u = 0 := by
      have hsum : ∑ i, partSum x i = ∑ _i : Fin r, ∑ u, x u :=
        Finset.sum_congr rfl fun i _ => (hrow (i, ⟨0, ht0⟩)).symm
      rw [sum_partSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at hsum
      have hfac : ((r : ℝ) - 1) * ∑ u, x u = 0 := by linarith
      exact (mul_eq_zero.mp hfac).resolve_left hne
    intro i
    have hi := hrow (i, ⟨0, ht0⟩)
    rw [hS] at hi
    exact hi.symm
  · exact fun h => signlessLap_multi_mulVec_of_partSum_eq_zero h

theorem lapMatrix_multi_mulVec_eq_iff (hr : 2 ≤ r) {x : Fin r × Fin t → ℝ} :
    (completeEquipartiteGraph r t).lapMatrix ℝ *ᵥ x = (((r : ℝ) - 1) * t) • x
      ↔ ∀ i, partSum x i = 0 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos t with ht0 | ht0
    · haveI : IsEmpty (Fin t) := by rw [ht0]; infer_instance
      intro i
      simp [partSum, Finset.univ_eq_empty]
    have hrow : ∀ v : Fin r × Fin t, (∑ u, x u) = partSum x v.1 := by
      intro v
      have hv := congrFun h v
      rw [lapMatrix_multi_mulVec] at hv
      simp only [Pi.smul_apply, smul_eq_mul] at hv
      linarith
    have hne : ((r : ℝ) - 1) ≠ 0 := by
      have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    have hS : ∑ u, x u = 0 := by
      have hsum : ∑ i, partSum x i = ∑ _i : Fin r, ∑ u, x u :=
        Finset.sum_congr rfl fun i _ => (hrow (i, ⟨0, ht0⟩)).symm
      rw [sum_partSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at hsum
      have hfac : ((r : ℝ) - 1) * ∑ u, x u = 0 := by linarith
      exact (mul_eq_zero.mp hfac).resolve_left hne
    intro i
    have hi := hrow (i, ⟨0, ht0⟩)
    rw [hS] at hi
    exact hi.symm
  · exact fun h => lapMatrix_multi_mulVec_of_partSum_eq_zero h

/-! ## 2. That subspace is the kernel of the part-sum map, of dimension `r(t − 1)` -/

/-- The part sums, as a linear map to one scalar per part. -/
noncomputable def partForm (r t : ℕ) : (Fin r × Fin t → ℝ) →ₗ[ℝ] (Fin r → ℝ) :=
  LinearMap.pi fun i => ∑ j : Fin t, LinearMap.proj (i, j)

theorem partForm_apply (x : Fin r × Fin t → ℝ) (i : Fin r) :
    partForm r t x i = partSum x i := by
  simp [partForm, partSum]

theorem surjective_partForm (ht : 1 ≤ t) : Function.Surjective (partForm r t) := by
  intro y
  refine ⟨fun v => if v.2 = ⟨0, by omega⟩ then y v.1 else 0, ?_⟩
  funext i
  rw [partForm_apply, partSum]
  simp

theorem finrank_ker_partForm (ht : 1 ≤ t) :
    Module.finrank ℝ (LinearMap.ker (partForm r t)) = r * t - r := by
  have hrange : Module.finrank ℝ (LinearMap.range (partForm r t)) = r := by
    rw [LinearMap.range_eq_top.mpr (surjective_partForm ht), finrank_top,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have htotal := LinearMap.finrank_range_add_finrank_ker (partForm r t)
  rw [hrange, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin] at htotal
  omega

theorem eigenspace_signlessLap_multi_eq (hr : 2 ≤ r) :
    LinearMap.ker (Matrix.toLin' (signlessLap (completeEquipartiteGraph r t))
        - (((r : ℝ) - 1) * t) • LinearMap.id) = LinearMap.ker (partForm r t) := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero, Matrix.toLin'_apply]
  rw [signlessLap_multi_mulVec_eq_iff hr]
  constructor
  · intro h
    funext i
    rw [partForm_apply, h i, Pi.zero_apply]
  · intro h i
    rw [← partForm_apply]
    exact congrFun h i

theorem eigenspace_lapMatrix_multi_eq (hr : 2 ≤ r) :
    LinearMap.ker (Matrix.toLin' ((completeEquipartiteGraph r t).lapMatrix ℝ)
        - (((r : ℝ) - 1) * t) • LinearMap.id) = LinearMap.ker (partForm r t) := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero, Matrix.toLin'_apply]
  rw [lapMatrix_multi_mulVec_eq_iff hr]
  constructor
  · intro h
    funext i
    rw [partForm_apply, h i, Pi.zero_apply]
  · intro h i
    rw [← partForm_apply]
    exact congrFun h i

/-! ## 3. So the field on this family has infinitely many symmetries -/

theorem two_le_finrank_eigenspace_multi (hr : 2 ≤ r) (ht : 2 ≤ t) :
    2 ≤ Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
      ((completeEquipartiteGraph r t).lapMatrix ℝ) - (((r : ℝ) - 1) * t) • LinearMap.id)) := by
  rw [eigenspace_lapMatrix_multi_eq hr, finrank_ker_partForm (by omega)]
  have : 2 * r ≤ r * t := by
    calc 2 * r = r * 2 := by ring
      _ ≤ r * t := Nat.mul_le_mul_left r ht
  omega

theorem infinite_symmetryMatrices_multi {m : ℝ} (hm : m ≠ 0) (hr : 2 ≤ r) (ht : 2 ≤ t) :
    (symmetryMatrices (completeEquipartiteGraph r t) m).Infinite := by
  intro hfin
  have hall := (FieldSymmetryFinite.finite_iff_lapMatrix hm).mp hfin
  have h2 := two_le_finrank_eigenspace_multi (r := r) (t := t) hr ht
  have := hall (((r : ℝ) - 1) * t)
  omega

end MultipartiteEigenspace
