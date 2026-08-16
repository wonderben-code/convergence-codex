import LatticeFieldProduct

/-!
# The identity the correlated Poincaré inequality was waiting on

`LatticeFieldProduct` reduced the correlated Poincaré inequality to a single missing statement,
and the `UNLOCK_WATCHLIST` records it in exactly these words:

> *"**What is actually left, and it is one identity:** `∑ᵢ (DΦ(x)(√G eᵢ))² = ⟪∇Φ(x), G ∇Φ(x)⟫` —
> the gradient representation of the Fréchet derivative, then `sqrt_green_mul_self`."*

**This is that identity**, and it turns out to need no gradient representation at all.

## Why the Riesz representative is not needed, which is what makes this short

The obvious route is to write the Fréchet derivative `DΦ(x)` as an inner product against a gradient
vector and then push the matrix across. That needs the Riesz machinery on `EuclideanSpace`.

It is unnecessary. In finite dimensions a linear functional is *determined by its values on the
coordinate directions*, so taking

```
w j := DΦ(x) (toLp 2 (eⱼ))
```

as the definition of the partial derivatives, linearity alone gives `DΦ(x)(toLp 2 v) = ∑ⱼ v j · w j`
— and the identity becomes a statement about a matrix and a vector with no analysis in it. That is
`sum_sq_col_eq_quadForm`, and it is proved here for an **arbitrary** symmetric `S` with `S·S = A`,
because nothing in it is about propagators.

## What is proved

* **`sum_sq_col_eq_quadForm`** — for `S` symmetric with `S · S = A`:

  ```
  ∑ᵢ (∑ⱼ w j · (S *ᵥ eᵢ) j)² = w ⬝ᵥ A *ᵥ w
  ```

  The left side is what a Poincaré inequality produces after a change of variables by `S`; the
  right side is the quadratic form of `A`. **Pure linear algebra**, no measure and no field;
* `isSymm_sqrt_green` — the square root of the propagator is symmetric, via `CFC.sqrt_nonneg` and
  `Matrix.nonneg_iff_posSemidef`, and it needs **no hypothesis on the mass at all** — see its
  docstring, the third time today a linter warning has turned out to be a mathematical
  observation;
* **`sum_sq_sqrt_green_col`** — the two combined, at `S = √G` and `A = green G m`: the identity
  in the form the assembly will cite, at every mass and on every graph with vertex type `Fin n`.

## What this is NOT

**It is not the Poincaré inequality.** What remains between this file and that inequality is the
*analytic* assembly, and it is now the only thing left: that `Φ ∘ (√G ·)` is `C¹` when `Φ` is, that
its partial derivatives are what the chain rule says, and that the two `MemLp` side conditions
`SteinGeneralPi.poincare_contDiff` wants transport across
`LatticeFieldProduct.gaussianField_eq_map_gaussPi`. **That assembly is named, not costed**
(`ERRATUM 183`) — the fourth time on this chain that the next step has been named rather than
guessed at, and the previous three guesses were all wrong in the same direction.

*Sections 1–3 were committed first (`e53c703`); §4 below closes the algebraic half completely, so
the residue named above is now purely the calculus.*

**And the vertex type is still `Fin n`**, for the reason `LatticeFieldProduct` records: the
estate's concrete lattices have product vertex types. **No published tag moves. OS4 does not
move.**
-/

namespace LatticeGradientForm

open Matrix GraphLaplacian
open scoped MatrixOrder

/-! ## 1. The identity, with no analysis in it -/

/-- **THE MISSING IDENTITY.** For `S` symmetric with `S · S = A`, summing the squared values of a
linear functional along the `S`-images of the coordinate directions gives the quadratic form of
`A`.

`w` is the tuple of partial derivatives; **no Riesz representative appears**, because in finite
dimensions linearity on the coordinate directions is all the information a functional has. -/
theorem sum_sq_col_eq_quadForm {n : ℕ} (S A : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm)
    (hSA : S * S = A) (w : Fin n → ℝ) :
    ∑ i : Fin n, (∑ j, w j * (S *ᵥ Pi.single i (1 : ℝ)) j) ^ 2 = w ⬝ᵥ A *ᵥ w := by
  have hsym : ∀ a b, S a b = S b a := fun a b => congrFun (congrFun hS b) a
  have hcol : ∀ i : Fin n, (∑ j, w j * (S *ᵥ Pi.single i (1 : ℝ)) j) = (S *ᵥ w) i := by
    intro i
    have h1 : ∀ j, (S *ᵥ Pi.single i (1 : ℝ)) j = S j i := by
      intro j; simp [Matrix.mulVec, dotProduct_single]
    rw [show (S *ᵥ w) i = ∑ j, S i j * w j from rfl]
    exact Finset.sum_congr rfl fun j _ => by rw [h1 j, hsym j i]; ring
  simp only [hcol]
  have hstep : w ⬝ᵥ A *ᵥ w = (S *ᵥ w) ⬝ᵥ (S *ᵥ w) := by
    rw [← hSA, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hS]
  rw [hstep, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## 2. The propagator's square root is symmetric -/

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {m : ℝ}

/-- A `CFC` square root is positive semidefinite, hence Hermitian, hence — over `ℝ` — symmetric.

**No hypothesis on the mass.** This was first written with `m ≠ 0`, by habit, because everything
around it needs that; the linter reported the hypothesis unused and it is genuinely unnecessary —
`CFC.sqrt_nonneg` holds of *any* matrix, so the square root is symmetric even where `green G m` is
not a propagator at all. -/
theorem isSymm_sqrt_green : (CFC.sqrt (green G m)).IsSymm := by
  have hps : (CFC.sqrt (green G m)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (green G m))
  simpa [Matrix.IsSymm, Matrix.IsHermitian] using hps.1

/-! ## 3. The two combined -/

/-- **THE IDENTITY AT THE PROPAGATOR**, in the form the analytic assembly will cite: the sum of
squared partial derivatives along the `√G`-images of the coordinate directions **is** the Green
quadratic form of the partial-derivative tuple. -/
theorem sum_sq_sqrt_green_col (hm : m ≠ 0) (w : Fin n → ℝ) :
    ∑ i : Fin n,
        (∑ j, w j * (CFC.sqrt (green G m) *ᵥ Pi.single i (1 : ℝ)) j) ^ 2
      = w ⬝ᵥ green G m *ᵥ w :=
  sum_sq_col_eq_quadForm _ _ isSymm_sqrt_green
    (LatticeFieldProduct.sqrt_green_mul_self hm) w

/-! ## 4. The algebraic half of the assembly, closed

What a Poincaré inequality produces after a change of variables by `√G` is a sum of squares of the
**derivative** evaluated along the `√G`-images of the coordinate directions. The derivative at a
point is a continuous linear functional and nothing else about it matters here, so this section is
stated for an arbitrary one. -/

/-- **A LINEAR FUNCTIONAL IS ITS VALUES ON THE AXES.** In finite dimensions, with no
completeness, no Riesz representative and no inner product: `T` on any vector is the coordinate
combination of `T` on the coordinate directions. -/
theorem apply_eq_sum_coords {n : ℕ} (T : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    T (WithLp.toLp 2 v) = ∑ j, v j * T (WithLp.toLp 2 (Pi.single j (1 : ℝ))) := by
  have hv : (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))
      = ∑ j, v j • (WithLp.toLp 2 (Pi.single j (1 : ℝ)) : EuclideanSpace ℝ (Fin n)) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul]; simp

/-- **THE ALGEBRAIC HALF OF THE CORRELATED POINCARÉ INEQUALITY, COMPLETE.**

For any continuous linear functional `T` — in the application, the Fréchet derivative of the
observable at a point — the sum of its squared values along the `√G`-images of the coordinate
directions **is** the Green quadratic form of its coordinate values.

The left side is exactly what `SteinGeneralPi.poincare_contDiff` produces once
`LatticeFieldProduct.gaussianField_eq_map_gaussPi` has changed variables; the right side is
exactly `⟪∇Φ, G ∇Φ⟫`. **Nothing analytic is left in the identity** — what remains between this and
the inequality is the chain rule and two integrability transports, and both are calculus rather
than algebra. -/
theorem sum_sq_apply_sqrt_green (hm : m ≠ 0) (T : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    ∑ i : Fin n, (T (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ Pi.single i (1 : ℝ)))) ^ 2
      = (fun j => T (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
          ⬝ᵥ green G m *ᵥ (fun j => T (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) := by
  have hexp : ∀ i : Fin n,
      T (WithLp.toLp 2 (CFC.sqrt (green G m) *ᵥ Pi.single i (1 : ℝ)))
        = ∑ j, (fun k => T (WithLp.toLp 2 (Pi.single k (1 : ℝ)))) j
            * (CFC.sqrt (green G m) *ᵥ Pi.single i (1 : ℝ)) j := by
    intro i
    rw [apply_eq_sum_coords]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [hexp]
  exact sum_sq_sqrt_green_col hm _

end LatticeGradientForm
