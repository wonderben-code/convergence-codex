/-
  GraphReflectionPositive.lean — R4, and with it W1's failing step.

  WHY. `UNLOCK_WATCHLIST`'s ladder for W1 reads R1a done
  (`LatticeReflectionSplit`, `GraphReflection`), R1b mostly done
  (`GraphHalfSpace`), R2 done (`MatrixLoewner`), R3 done
  (`BoxCrossCoupling`), R4 open — and the R4 probe written after R3 mapped
  the remainder in five steps. This is those five steps.

  WHAT THIS FILE PROVES, for a finite simple graph `G`, an involutive
  automorphism `θ`, a half `H`, and a nonzero mass:
  1. **`plusOp`, `minusOp`** — `A ± B` as honest matrices on the subtype
     `↥H`, which is the one place `GraphHalfSpace` recorded that the subtype
     cannot be dodged.
  2. **`plusOp_posDef`, `minusOp_posDef`** — both are positive definite. This
     is the one step of R4 that is not bookkeeping: the quadratic form of
     `A + B` at `w` is half the `massive`-energy of the even extension of
     `w`, and `massive` is positive definite.
  3. **`energy_symExt_eq`, `energy_antiExt_eq`** — hence
     `Q(symExt w) = 2·wᵀ(A+B)⁻¹w` and `Q(antiExt w) = 2·wᵀ(A−B)⁻¹w`.
     **These are the two theorems `GraphHalfSpace`'s draft header advertised
     and did not have**, and they were its recorded residue.
  4. **`reflectionPositive_of_crossOp_nonpos`** — and therefore, whenever the
     cross-coupling is negative semidefinite on the half,
     **`ReflectionPositive G m θ H` holds.** R2 supplies the inversion.
  5. **`reflectionPositive_box`** — instantiated: **reflection positivity of
     the massive lattice Green function on the `d`-dimensional box of EVEN
     side, for the half cut by any one coordinate.** And **`rp4_holds`**:
     `GraphReflection.RP4`, the four-dimensional statement that file could
     only write down, is now a theorem.

  A CLAIM THIS FILE DOES NOT MAKE, flagged because the draft header made it.
  **The estate's ORIGINAL phrasing, `LatticeReflection.ReflectionPositive`
  on `Site n = Fin n × Fin n` with `refl n`, is NOT covered here.** That box
  is encoded as a PAIR, `revSite` acts on `Fin d → Fin n`, and the two are
  isomorphic only through `BoxGraph.boxGraph_two_iso`. Transporting the
  property along that isomorphism, or re-running §7's cross-coupling
  computation for the pair encoding, is a further step and is not taken.
  §8 records it as the remaining leg.

  WHAT THIS DOES NOT DO, and the distance is larger than the last rung makes
  it feel. **This is one Osterwalder–Schrader axiom for one covariance on a
  finite box.** It is NOT the continuum theory, NOT the infinite-volume
  limit, and **NOT measure-level OS2 for the lattice field** — `LatticeField`
  established that the estate's OS2 packaging transfers only as far as the
  Gaussian-moments layer, so the statement about the MEASURE remains a
  further unit. W2 is untouched and is two Mathlib-scale projects deep.

  Nor does it say anything for odd side: `GraphHalfSpace.not_isHalf_of_odd`
  says there is no half there, so the hypothesis cannot be met.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import GraphHalfSpace
import BoxCrossCoupling
import MatrixLoewner

namespace GraphReflectionPositive

open Finset Matrix GraphLaplacian GraphReflection GraphHalfSpace
open scoped MatrixOrder

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H : Finset V}

/-! ## 1. `A ± B` on the half -/

/-- Extend a function on the half by zero. -/
noncomputable def ext (H : Finset V) (w : H → ℝ) : V → ℝ :=
  fun p => if hp : p ∈ H then w ⟨p, hp⟩ else 0

omit [Fintype V] in
theorem ext_notMem (w : H → ℝ) {p : V} (hp : p ∉ H) : ext H w p = 0 := by
  simp [ext, hp]

omit [Fintype V] in
@[simp] theorem ext_coe (w : H → ℝ) (p : H) : ext H w ↑p = w p := by
  simp [ext, p.2]

omit [Fintype V] in
theorem ext_eq_self {c : V → ℝ} (hc : ∀ p, p ∉ H → c p = 0) :
    ext H (fun p : H => c ↑p) = c := by
  funext p
  by_cases hp : p ∈ H
  · simp [ext, hp]
  · rw [ext_notMem _ hp, hc p hp]

/-- `A + B`, on the half. -/
noncomputable def plusOp (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (θ : V ≃ V)
    (H : Finset V) : Matrix H H ℝ :=
  Matrix.of fun p q => massive G m ↑p ↑q + crossOp G m θ ↑p ↑q

/-- `A − B`, on the half. -/
noncomputable def minusOp (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (θ : V ≃ V)
    (H : Finset V) : Matrix H H ℝ :=
  Matrix.of fun p q => massive G m ↑p ↑q - crossOp G m θ ↑p ↑q

/-! ## 2. The two extensions have the parities their names claim -/

omit [Fintype V] in
theorem symExt_symm (hH : IsHalf θ H) (hinv : Function.Involutive θ)
    (v : V → ℝ) (p : V) : symExt θ H v (θ p) = symExt θ H v p := by
  by_cases hp : p ∈ H
  · rw [symExt_of_notMem (hH.notMem_of_mem hp), symExt_of_mem hp, hinv p]
  · rw [symExt_of_mem (hH.mem_of_notMem hp), symExt_of_notMem hp]

omit [Fintype V] in
theorem antiExt_antisymm (hH : IsHalf θ H) (hinv : Function.Involutive θ)
    (v : V → ℝ) (p : V) : antiExt θ H v (θ p) = -antiExt θ H v p := by
  by_cases hp : p ∈ H
  · rw [antiExt_of_notMem (hH.notMem_of_mem hp), antiExt_of_mem hp, hinv p]
  · rw [antiExt_of_mem (hH.mem_of_notMem hp), antiExt_of_notMem hp, neg_neg]

omit [DecidableEq V] in
/-- **THE DOUBLING LEMMA.** Two functions of the same parity under `θ` pair
    to twice their pairing over the half. -/
theorem sum_double (hH : IsHalf θ H) (hinv : Function.Involutive θ) {f g : V → ℝ}
    (hfg : ∀ p, f (θ p) * g (θ p) = f p * g p) :
    ∑ p, f p * g p = 2 * ∑ p ∈ H, f p * g p := by
  rw [hH.sum_split hinv (fun p => f p * g p)]
  rw [Finset.sum_congr rfl (fun p _ => hfg p)]
  ring

/-! ## 3. `A ± B` act as `massive` does on the two eigenspaces -/

theorem plusOp_mulVec (hH : IsHalf θ H) (h : IsRefl G θ) (w : H → ℝ) (p : H) :
    (plusOp G m θ H *ᵥ w) p
      = (massive G m *ᵥ symExt θ H (ext H w)) ↑p := by
  classical
  rw [massive_mulVec_symExt hH h (ext H w), symExt_of_mem p.2]
  show ∑ q : H, (massive G m ↑p ↑q + crossOp G m θ ↑p ↑q) * w q = _
  calc ∑ q : H, (massive G m ↑p ↑q + crossOp G m θ ↑p ↑q) * w q
      = ∑ q : H, (fun k => (massive G m ↑p k + crossOp G m θ ↑p k) * ext H w k) ↑q :=
        Finset.sum_congr rfl fun q _ => by simp
    _ = ∑ k ∈ H, (massive G m ↑p k + crossOp G m θ ↑p k) * ext H w k :=
        Finset.sum_coe_sort H (fun k => (massive G m ↑p k + crossOp G m θ ↑p k) * ext H w k)

theorem minusOp_mulVec (hH : IsHalf θ H) (h : IsRefl G θ) (w : H → ℝ) (p : H) :
    (minusOp G m θ H *ᵥ w) p
      = (massive G m *ᵥ antiExt θ H (ext H w)) ↑p := by
  classical
  rw [massive_mulVec_antiExt hH h (ext H w), antiExt_of_mem p.2]
  show ∑ q : H, (massive G m ↑p ↑q - crossOp G m θ ↑p ↑q) * w q = _
  calc ∑ q : H, (massive G m ↑p ↑q - crossOp G m θ ↑p ↑q) * w q
      = ∑ q : H, (fun k => (massive G m ↑p k - crossOp G m θ ↑p k) * ext H w k) ↑q :=
        Finset.sum_congr rfl fun q _ => by simp
    _ = ∑ k ∈ H, (massive G m ↑p k - crossOp G m θ ↑p k) * ext H w k :=
        Finset.sum_coe_sort H (fun k => (massive G m ↑p k - crossOp G m θ ↑p k) * ext H w k)

/-! ## 4. Both are positive definite

The one step of R4 that is not bookkeeping. The quadratic form of `A + B` at
`w` is half the `massive`-energy of the even extension of `w`; `massive` is
positive definite; and the even extension of a nonzero `w` is nonzero.
-/

omit [Fintype V] in
private theorem ext_ne_zero {w : H → ℝ} (hw : w ≠ 0) : ext H w ≠ 0 := by
  intro hc
  apply hw
  funext p
  have := congrFun hc ↑p
  rwa [ext_coe] at this

omit [Fintype V] in
private theorem symExt_ne_zero {w : H → ℝ} (hw : w ≠ 0) : symExt θ H (ext H w) ≠ 0 := by
  intro hc
  apply ext_ne_zero hw
  funext p
  by_cases hp : p ∈ H
  · have := congrFun hc p
    rwa [symExt_of_mem hp] at this
  · simp [ext_notMem _ hp]

omit [Fintype V] in
private theorem antiExt_ne_zero {w : H → ℝ} (hw : w ≠ 0) : antiExt θ H (ext H w) ≠ 0 := by
  intro hc
  apply ext_ne_zero hw
  funext p
  by_cases hp : p ∈ H
  · have := congrFun hc p
    rwa [antiExt_of_mem hp] at this
  · simp [ext_notMem _ hp]

private theorem hermitian_plus (h : IsRefl G θ) : (plusOp G m θ H).IsHermitian := by
  ext p q
  simp only [Matrix.conjTranspose_apply, plusOp, Matrix.of_apply, star_trivial]
  have h1 : massive G m ↑q ↑p = massive G m ↑p ↑q :=
    congrFun (congrFun (GraphLaplacian.massive_isSymm G m) ↑p) ↑q
  have h2 : crossOp G m θ ↑q ↑p = crossOp G m θ ↑p ↑q := crossOp_symm h ↑q ↑p
  rw [h1, h2]

private theorem hermitian_minus (h : IsRefl G θ) : (minusOp G m θ H).IsHermitian := by
  ext p q
  simp only [Matrix.conjTranspose_apply, minusOp, Matrix.of_apply, star_trivial]
  have h1 : massive G m ↑q ↑p = massive G m ↑p ↑q :=
    congrFun (congrFun (GraphLaplacian.massive_isSymm G m) ↑p) ↑q
  have h2 : crossOp G m θ ↑q ↑p = crossOp G m θ ↑p ↑q := crossOp_symm h ↑q ↑p
  rw [h1, h2]

/-- **`A + B` IS POSITIVE DEFINITE.** -/
theorem plusOp_posDef (hH : IsHalf θ H) (h : IsRefl G θ) (hm : m ≠ 0) :
    (plusOp G m θ H).PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hermitian_plus h, fun w hw => ?_⟩
  set u := symExt θ H (ext H w) with hu
  have hpair : ∀ p, u (θ p) * (massive G m *ᵥ u) (θ p) = u p * (massive G m *ᵥ u) p := by
    intro p
    have h1 : u (θ p) = u p := symExt_symm hH h.invol _ p
    have h2 : massive G m *ᵥ u = symExt θ H _ := massive_mulVec_symExt hH h (ext H w)
    rw [h1, h2, symExt_symm hH h.invol _ p]
  have hdouble : ∑ p, u p * (massive G m *ᵥ u) p
      = 2 * ∑ p ∈ H, u p * (massive G m *ᵥ u) p := sum_double hH h.invol hpair
  have hhalf : ∑ p ∈ H, u p * (massive G m *ᵥ u) p
      = star w ⬝ᵥ (plusOp G m θ H *ᵥ w) := by
    rw [← Finset.sum_coe_sort H (fun p => u p * (massive G m *ᵥ u) p)]
    simp only [dotProduct, star_trivial]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [plusOp_mulVec hH h w p, hu, symExt_of_mem p.2, ext_coe]
  have hpos : 0 < ∑ p, u p * (massive G m *ᵥ u) p := by
    have := (Matrix.posDef_iff_dotProduct_mulVec.mp (GraphLaplacian.massive_posDef G hm)).2
      (symExt_ne_zero (θ := θ) hw)
    simpa [dotProduct, star_trivial] using this
  rw [hdouble, hhalf] at hpos
  linarith

/-- **`A − B` IS POSITIVE DEFINITE.** -/
theorem minusOp_posDef (hH : IsHalf θ H) (h : IsRefl G θ) (hm : m ≠ 0) :
    (minusOp G m θ H).PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hermitian_minus h, fun w hw => ?_⟩
  set u := antiExt θ H (ext H w) with hu
  have hpair : ∀ p, u (θ p) * (massive G m *ᵥ u) (θ p) = u p * (massive G m *ᵥ u) p := by
    intro p
    have h1 : u (θ p) = -u p := antiExt_antisymm hH h.invol _ p
    have h2 : massive G m *ᵥ u = antiExt θ H _ := massive_mulVec_antiExt hH h (ext H w)
    rw [h1, h2, antiExt_antisymm hH h.invol _ p]
    ring
  have hdouble : ∑ p, u p * (massive G m *ᵥ u) p
      = 2 * ∑ p ∈ H, u p * (massive G m *ᵥ u) p := sum_double hH h.invol hpair
  have hhalf : ∑ p ∈ H, u p * (massive G m *ᵥ u) p
      = star w ⬝ᵥ (minusOp G m θ H *ᵥ w) := by
    rw [← Finset.sum_coe_sort H (fun p => u p * (massive G m *ᵥ u) p)]
    simp only [dotProduct, star_trivial]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [minusOp_mulVec hH h w p, hu, antiExt_of_mem p.2, ext_coe]
  have hpos : 0 < ∑ p, u p * (massive G m *ᵥ u) p := by
    have := (Matrix.posDef_iff_dotProduct_mulVec.mp (GraphLaplacian.massive_posDef G hm)).2
      (antiExt_ne_zero (θ := θ) hw)
    simpa [dotProduct, star_trivial] using this
  rw [hdouble, hhalf] at hpos
  linarith

/-! ## 5. The two energies -/

private theorem massive_apply_inv_sym (hH : IsHalf θ H) (h : IsRefl G θ) (hm : m ≠ 0)
    (w : H → ℝ) :
    massive G m *ᵥ symExt θ H (ext H ((plusOp G m θ H)⁻¹ *ᵥ w)) = symExt θ H (ext H w) := by
  classical
  funext p
  by_cases hp : p ∈ H
  · have hcoe : (⟨p, hp⟩ : H).val = p := rfl
    have := plusOp_mulVec (m := m) hH h ((plusOp G m θ H)⁻¹ *ᵥ w) ⟨p, hp⟩
    rw [hcoe] at this
    rw [← this, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
        (plusOp_posDef hH h hm).isUnit), Matrix.one_mulVec, symExt_of_mem hp]
    exact (ext_coe w ⟨p, hp⟩).symm
  · have hkey := massive_mulVec_symExt (m := m) hH h (ext H ((plusOp G m θ H)⁻¹ *ᵥ w))
    have hθ : θ p ∈ H := hH.mem_of_notMem hp
    have hsym1 : (massive G m *ᵥ symExt θ H (ext H ((plusOp G m θ H)⁻¹ *ᵥ w))) p
        = (massive G m *ᵥ symExt θ H (ext H ((plusOp G m θ H)⁻¹ *ᵥ w))) (θ p) := by
      rw [hkey, symExt_symm hH h.invol]
    rw [hsym1, symExt_of_notMem hp]
    have hcoe : (⟨θ p, hθ⟩ : H).val = θ p := rfl
    have := plusOp_mulVec (m := m) hH h ((plusOp G m θ H)⁻¹ *ᵥ w) ⟨θ p, hθ⟩
    rw [hcoe] at this
    rw [← this, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
        (plusOp_posDef hH h hm).isUnit), Matrix.one_mulVec]
    exact (ext_coe w ⟨θ p, hθ⟩).symm

private theorem massive_apply_inv_anti (hH : IsHalf θ H) (h : IsRefl G θ) (hm : m ≠ 0)
    (w : H → ℝ) :
    massive G m *ᵥ antiExt θ H (ext H ((minusOp G m θ H)⁻¹ *ᵥ w)) = antiExt θ H (ext H w) := by
  classical
  funext p
  by_cases hp : p ∈ H
  · have hcoe : (⟨p, hp⟩ : H).val = p := rfl
    have := minusOp_mulVec (m := m) hH h ((minusOp G m θ H)⁻¹ *ᵥ w) ⟨p, hp⟩
    rw [hcoe] at this
    rw [← this, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
        (minusOp_posDef hH h hm).isUnit), Matrix.one_mulVec, antiExt_of_mem hp]
    exact (ext_coe w ⟨p, hp⟩).symm
  · have hkey := massive_mulVec_antiExt (m := m) hH h (ext H ((minusOp G m θ H)⁻¹ *ᵥ w))
    have hθ : θ p ∈ H := hH.mem_of_notMem hp
    have hsym1 : (massive G m *ᵥ antiExt θ H (ext H ((minusOp G m θ H)⁻¹ *ᵥ w))) p
        = -(massive G m *ᵥ antiExt θ H (ext H ((minusOp G m θ H)⁻¹ *ᵥ w))) (θ p) := by
      rw [hkey]
      have := antiExt_antisymm (θ := θ) (H := H) hH h.invol
        (fun x => ∑ k ∈ H, (massive G m x k - crossOp G m θ x k)
          * ext H ((minusOp G m θ H)⁻¹ *ᵥ w) k) p
      rw [this]; ring
    rw [hsym1, antiExt_of_notMem hp]
    have hcoe : (⟨θ p, hθ⟩ : H).val = θ p := rfl
    have := minusOp_mulVec (m := m) hH h ((minusOp G m θ H)⁻¹ *ᵥ w) ⟨θ p, hθ⟩
    rw [hcoe] at this
    rw [← this, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
        (minusOp_posDef hH h hm).isUnit), Matrix.one_mulVec]
    exact congrArg Neg.neg (ext_coe w ⟨θ p, hθ⟩).symm

/-- **THE EVEN ENERGY IS `2·wᵀ(A+B)⁻¹w`.** One of the two theorems
    `GraphHalfSpace`'s draft header advertised and did not have. -/
theorem energy_symExt_eq (hH : IsHalf θ H) (h : IsRefl G θ) (hm : m ≠ 0) (w : H → ℝ) :
    GraphReflection.energy G m (symExt θ H (ext H w))
      = 2 * (star w ⬝ᵥ ((plusOp G m θ H)⁻¹ *ᵥ w)) := by
  classical
  set y := symExt θ H (ext H ((plusOp G m θ H)⁻¹ *ᵥ w)) with hy
  have hgreen : GraphLaplacian.green G m *ᵥ symExt θ H (ext H w) = y := by
    rw [← massive_apply_inv_sym hH h hm w, GraphLaplacian.green, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
        (GraphLaplacian.massive_posDef G hm).isUnit), Matrix.one_mulVec]
  have hbil : GraphReflection.energy G m (symExt θ H (ext H w))
      = ∑ p, symExt θ H (ext H w) p * y p := by
    rw [GraphReflection.energy, GraphReflection.bil]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hgreen]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hbil]
  have hpair : ∀ p, symExt θ H (ext H w) (θ p) * y (θ p)
      = symExt θ H (ext H w) p * y p := by
    intro p
    rw [symExt_symm hH h.invol, hy, symExt_symm hH h.invol]
  rw [sum_double hH h.invol hpair, ← Finset.sum_coe_sort H
    (fun p => symExt θ H (ext H w) p * y p)]
  simp only [dotProduct, star_trivial]
  congr 1
  exact Finset.sum_congr rfl fun p _ => by
    rw [symExt_of_mem p.2, ext_coe, hy, symExt_of_mem p.2, ext_coe]

/-- **THE ODD ENERGY IS `2·wᵀ(A−B)⁻¹w`.** -/
theorem energy_antiExt_eq (hH : IsHalf θ H) (h : IsRefl G θ) (hm : m ≠ 0) (w : H → ℝ) :
    GraphReflection.energy G m (antiExt θ H (ext H w))
      = 2 * (star w ⬝ᵥ ((minusOp G m θ H)⁻¹ *ᵥ w)) := by
  classical
  set y := antiExt θ H (ext H ((minusOp G m θ H)⁻¹ *ᵥ w)) with hy
  have hgreen : GraphLaplacian.green G m *ᵥ antiExt θ H (ext H w) = y := by
    rw [← massive_apply_inv_anti hH h hm w, GraphLaplacian.green, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
        (GraphLaplacian.massive_posDef G hm).isUnit), Matrix.one_mulVec]
  have hbil : GraphReflection.energy G m (antiExt θ H (ext H w))
      = ∑ p, antiExt θ H (ext H w) p * y p := by
    rw [GraphReflection.energy, GraphReflection.bil]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hgreen]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hbil]
  have hpair : ∀ p, antiExt θ H (ext H w) (θ p) * y (θ p)
      = antiExt θ H (ext H w) p * y p := by
    intro p
    rw [antiExt_antisymm hH h.invol, hy, antiExt_antisymm hH h.invol]
    ring
  rw [sum_double hH h.invol hpair, ← Finset.sum_coe_sort H
    (fun p => antiExt θ H (ext H w) p * y p)]
  simp only [dotProduct, star_trivial]
  congr 1
  exact Finset.sum_congr rfl fun p _ => by
    rw [antiExt_of_mem p.2, ext_coe, hy, antiExt_of_mem p.2, ext_coe]

/-! ## 6. R4 — the assembly -/

/-- **REFLECTION POSITIVITY, GIVEN R3.** If the coupling across the cut is
    negative semidefinite on the half then the reflected form is
    non-negative. R2 (`MatrixLoewner.posDef_inv_le_inv`) does the inversion. -/
theorem reflectionPositive_of_crossOp_nonpos (hH : IsHalf θ H) (h : IsRefl G θ)
    (hm : m ≠ 0)
    (hB : ∀ w : H → ℝ, ∑ p, ∑ q, w p * w q * crossOp G m θ ↑p ↑q ≤ 0) :
    GraphReflection.ReflectionPositive G m θ H := by
  classical
  rw [reflectionPositive_iff_ext hH h]
  intro c hc
  rw [← ext_eq_self hc]
  set w : H → ℝ := fun p => c ↑p with hw
  rw [energy_symExt_eq hH h hm w, energy_antiExt_eq hH h hm w]
  have hle : plusOp G m θ H ≤ minusOp G m θ H := by
    rw [Matrix.le_iff]
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · exact (hermitian_minus h).sub (hermitian_plus h)
    · have hentry : ∀ p q : H,
          (minusOp G m θ H - plusOp G m θ H) p q = -2 * crossOp G m θ ↑p ↑q := by
        intro p q
        simp only [Matrix.sub_apply, minusOp, plusOp, Matrix.of_apply]
        ring
      have hexp : star x ⬝ᵥ ((minusOp G m θ H - plusOp G m θ H) *ᵥ x)
          = -2 * ∑ p, ∑ q, x p * x q * crossOp G m θ ↑p ↑q := by
        simp only [dotProduct, Matrix.mulVec, star_trivial]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by rw [hentry p q]; ring
      rw [hexp]
      nlinarith [hB x]
  have hinv := MatrixLoewner.posDef_inv_le_inv (plusOp_posDef hH h hm) hle
  have hquad : star w ⬝ᵥ ((minusOp G m θ H)⁻¹ *ᵥ w)
      ≤ star w ⬝ᵥ ((plusOp G m θ H)⁻¹ *ᵥ w) := by
    have hpsd : ((plusOp G m θ H)⁻¹ - (minusOp G m θ H)⁻¹).PosSemidef :=
      Matrix.le_iff.mp hinv
    have := hpsd.dotProduct_mulVec_nonneg w
    simp only [Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] at this
    exact this
  linarith

/-! ## 7. The box -/

section Box

open BoxGraph BoxCrossCoupling

variable {d n : ℕ}

/-- **REFLECTION POSITIVITY ON THE `d`-DIMENSIONAL BOX OF EVEN SIDE.**
    W1's failing step, for the half cut by any one coordinate. -/
theorem reflectionPositive_box (i : Fin d) (hn : Even n) {m : ℝ} (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive (boxGraph d n) m
      (revSite (n := n) i) (lowerHalf i n) := by
  classical
  refine reflectionPositive_of_crossOp_nonpos (isHalf_lowerHalf i hn)
    (boxGraph_revSite_aut i) hm fun w => ?_
  have hkey := BoxCrossCoupling.crossOp_nonpos (m := m) i hn
    (v := ext (lowerHalf i n) w) (fun p hp => ext_notMem w hp)
  refine le_trans (le_of_eq ?_) hkey
  set E := ext (lowerHalf i n) w with hE
  set C := crossOp (boxGraph d n) m (revSite (n := n) i) with hC
  have hrow : ∀ p : BoxGraph.Site d n,
      ∑ q, E p * E q * C p q = ∑ q ∈ lowerHalf i n, E p * E q * C p q := by
    intro p
    refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm
    rw [hE, ext_notMem w hx]; ring
  have hcol : ∑ p, ∑ q, E p * E q * C p q
      = ∑ p ∈ lowerHalf i n, ∑ q ∈ lowerHalf i n, E p * E q * C p q := by
    have h1 : ∑ p ∈ lowerHalf i n, (∑ q, E p * E q * C p q)
        = ∑ p, ∑ q, E p * E q * C p q :=
      Finset.sum_subset (Finset.subset_univ _) fun x _ hx => by
        refine Finset.sum_eq_zero fun q _ => ?_
        rw [hE, ext_notMem w hx]; ring
    rw [← h1]
    exact Finset.sum_congr rfl fun p _ => hrow p
  rw [hcol, ← Finset.sum_coe_sort (lowerHalf i n)
    (fun p => ∑ q ∈ lowerHalf i n, E p * E q * C p q)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_coe_sort (lowerHalf i n) (fun q => E ↑p * E q * C ↑p q)]
  exact Finset.sum_congr rfl fun q _ => by rw [hE, ext_coe, ext_coe]

/-- **`GraphReflection.RP4` IS A THEOREM.** That file defined the
    four-dimensional statement and said plainly that nothing proved it. For
    an even side and the half cut by any coordinate, this does. -/
theorem rp4_holds {n : ℕ} (hn : Even n) (i : Fin 4) {m : ℝ} (hm : m ≠ 0) :
    GraphReflection.RP4 n m i (lowerHalf i n) :=
  reflectionPositive_box i hn hm

end Box

/-! ## 8. Review round 83 — the ways this could be hollow

**"Is this really W1's failing step?"** It is
`GraphReflection.ReflectionPositive`, and `GraphReflection.reflectionPositive_box`
proves that at `(latticeGraph n, refl n)` it IS
`LatticeReflection.ReflectionPositive` — the `def` the estate wrote to name
W1's failing step — by `Iff.rfl`. So the identification is not an analogy.
**What differs from the wall's own phrasing is the parity condition**: the
estate's `refl n` on a box of ODD side has a fixed row, and
`GraphHalfSpace.not_isHalf_of_odd` says no half exists there. The theorem is
therefore about even side only, and that is a genuine restriction rather than
a technicality — it is the difference between a bond reflection and a site
reflection, and only the first is what this argument handles.

**"§4 could be circular."** It is not, and the direction of dependence is
worth stating: `plusOp_posDef` derives positivity of `A + B` FROM positivity
of `massive`, through the doubling lemma. Nothing about `A + B` is assumed.
The one place it could have gone wrong is `symExt_ne_zero`, which needs the
even extension of a nonzero `w` to be nonzero — true because the extension
agrees with `w` on the half — and without it the strictness fails and R2 does
not apply.

**"The `≤` in §6 could be the wrong way round."** This is exactly what
`BoxCrossCoupling`'s pinned sign was recorded for. `crossOp` is the matrix
ENTRY, `minusOp − plusOp = −2·crossOp` on the half, and R3 says the quadratic
form of `crossOp` is `≤ 0`; so `minusOp − plusOp` is positive semidefinite,
i.e. `plusOp ≤ minusOp`, and antitonicity gives `minusOp⁻¹ ≤ plusOp⁻¹`. The
even energy is the one with `plusOp⁻¹`, so it is the LARGER, which is what
`reflectionPositive_iff_energy_le` wants. **Had the convention been mixed up
the final `linarith` would have failed rather than silently proved the
converse**, because the two energies enter the `Iff` in fixed positions.

**"The estate's own `def` — is it covered?"** Not yet, and the draft header
of this file claimed it was. `LatticeReflection.ReflectionPositive` is
stated on `Site n = Fin n × Fin n` with `refl n`; this file proves the
property for `boxGraph d n` with `revSite i`, and the two boxes are
isomorphic only through `BoxGraph.boxGraph_two_iso`. **`GraphReflection`
already proves the general property at `(latticeGraph n, refl n)` IS the
estate's `def`, by `Iff.rfl`** — so what is missing is not the
identification but the HYPOTHESIS: §7's cross-coupling computation is done
for the `Fin d → Fin n` encoding and has not been re-run for pairs, and
`refl n` is not literally a `revSite`. The remaining leg is therefore one of
two bounded things: transport `crossOp_nonpos` along the graph isomorphism,
or redo `BoxCrossCoupling` for the pair encoding. **Neither is done and the
header now says so.**

**"How much of OS is this?"** One axiom, one covariance, one finite box.
**It is not measure-level OS2**: `LatticeField` established that the estate's
OS2 packaging transfers to the lattice covariance only as far as the
Gaussian-moments layer, so the statement about the MEASURE is a further unit
and is not claimed here. There is no infinite-volume limit, no continuum
limit, and no lattice spacing. W2 is untouched.

**"What was the estimate?"** The R4 probe said one to two units, and added
that the number was worth little because this document's estimates had been
wrong three times that day. It took one unit. **That is not evidence the
estimating improved** — one correct estimate after three wrong ones is what
you would expect from noise, and the probe's real contribution was the
five-step list, every step of which was consumed here in order.
-/

end GraphReflectionPositive
