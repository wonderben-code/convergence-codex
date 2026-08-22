import LovelockSectionalUnit
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The orthonormal-frame bridge, and the sectional route's conclusion made unconditional

`LovelockSectionalUnit` closed with the residual gap in one sentence:

> every orthonormal pair in `Fin n → ℝ` is a pair of rows of some orthogonal matrix

**This file proves it, and discharges the hypothesis `LovelockWitnessPairing.eq_zero_of_ip_orbit`
was carrying.** The gap was recorded as a *bridge* rather than a missing theorem — `WALLS` §W5.0
§5g, after the library was opened rather than guessed at — and that turned out to be the right
description: Mathlib supplies both mathematical steps and the work here is the coercion layer.

## What is proved

* `inner_eq_dotp` — this estate's `dotp` **is** the Euclidean inner product, once `Fin n → ℝ` is
  read as `EuclideanSpace ℝ (Fin n)` through `WithLp.toLp`. `PiLp.inner_apply` plus
  `RCLike.inner_apply'` termwise. **This is the bridge the estate had never built**;
* `dotp_comm`;
* **`exists_isOrth_rows`** — given `i ≠ j` and an orthonormal pair `x, y`, an orthogonal `Q` whose
  `i`-th and `j`-th rows are `x` and `y`. `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`
  extends `{x, y}` to an `OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))` — the cardinality
  side condition is `finrank_euclideanSpace_fin` — and `orthonormal_iff_ite` turns the basis's
  orthonormality into `IsOrth`'s `rows`. `IsOrth`'s `cols` is `QᵀQ = 1` from `QQᵀ = 1`, by
  `mul_eq_one_comm`;
* **`sec_eq_zero_of_rows`** — hence, at `n ≥ 2`, sectional vanishing on pairs of rows of orthogonal
  matrices forces sectional vanishing on **all** pairs. That is exactly the `hext` hypothesis;
* **`eq_zero_of_ip_orbit_uncond`** — **and so the sectional route's conclusion is unconditional:**
  a Ricci-flat algebraic curvature tensor `ip`-orthogonal to `act P W` for **every** orthogonal `P`
  and every witness `W = weylPart (knSquare (twoProj i j))` **is zero**.

## What this does and does not settle

**It settles `WALLS` §W5.0 §5b's question in the form the route needs.** The orbit of the explicit
Weyl witness has trivial orthogonal complement inside the Ricci-flat algebraic curvature tensors —
which is the spanning statement, in orthogonality form, with **no subspace type, no Schur, no
semisimplicity, no Haar averaging and no compactness of `O(n)`**.

**IT IS NOT `KillsWeyl`, AND THE REMAINING STEP IS AN ASSEMBLY, NOT A GAP.** `KillsWeyl T`
quantifies over every algebraic curvature tensor. Reaching it from here runs through
`LovelockAdjoint.killsWeyl_iff_adjoint` and `LovelockEquivariantAdjoint`: the Weyl part of the
equivariant adjoint is Ricci-flat and, by `LovelockWitnessRowSum.T_weyl_twoProj_eq_zero`, orthogonal
to the whole orbit — so this theorem makes it zero. **That chain is not written here**, and until it
is, **`KillsWeyl` at `n ≥ 4` is not proved and the watchlist item does not move.** Writing "the
assembly is routine" is precisely the kind of sentence `ERRATUM 175` exists about; what is claimed
here is only what is compiled here.


**⚠ SUPERSEDED — `LovelockKillsWeyl.killsWeyl_of_equivariant` PROVES `KillsWeyl` AT EVERY `n ≥ 3`**
(`171d474`, 15 August), and the paragraph above is kept per `ERRATUM 94`. Every additive,
homogeneous, `O(n)`-equivariant `T` annihilates the Weyl summand; `classification` follows, and the
watchlist's Lovelock item is CLOSED — its sweep record reads *"the closure is `KillsWeyl` at every
`n ≥ 3`"*. **So *"the watchlist item does not move"* is true only in the sense that a closed item
cannot move, and it invites the opposite reading.** What is still open at W5 is not this: it is
rung 2 of `WALLS` §W5.1's staircase, an **affine connection and Levi-Civita** — zero names in
Mathlib. `ERRATUM 230`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockOrthonormalFrame

open AlgebraicCurvature LovelockProjections LovelockOrthogonality LovelockSectionalOrthogonal
  LovelockSectionalUnit Finset Matrix

variable {n : ℕ}

/-- **THE ESTATE'S DOT PRODUCT IS THE EUCLIDEAN INNER PRODUCT.** The coercion layer `Fin n → ℝ` →
`EuclideanSpace ℝ (Fin n)` that this estate had never built. -/
theorem inner_eq_dotp (x y : Fin n → ℝ) :
    inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 y) = dotp x y := by
  rw [PiLp.inner_apply]
  simp only [dotp]
  exact Finset.sum_congr rfl fun t _ => RCLike.inner_apply' (x t) (y t)

theorem dotp_comm (x y : Fin n → ℝ) : dotp x y = dotp y x := by
  simp only [dotp]
  exact Finset.sum_congr rfl fun t _ => mul_comm (x t) (y t)

/-- **EVERY ORTHONORMAL PAIR IS A PAIR OF ROWS OF AN ORTHOGONAL MATRIX.** Extend to an
`OrthonormalBasis` by `exists_orthonormalBasis_extension_of_card_eq`, read the basis as a matrix,
and get `IsOrth` from `orthonormal_iff_ite` (rows) and `mul_eq_one_comm` (columns). -/
theorem exists_isOrth_rows {i j : Fin n} (hij : i ≠ j) (x y : Fin n → ℝ)
    (hxx : dotp x x = 1) (hyy : dotp y y = 1) (hxy : dotp x y = 0) :
    ∃ Q : Fin n → Fin n → ℝ, IsOrth Q ∧ (∀ t, Q i t = x t) ∧ (∀ t, Q j t = y t) := by
  classical
  set X : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x with hX
  set Y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 y with hY
  set v : Fin n → EuclideanSpace ℝ (Fin n) := fun k => if k = i then X else Y with hv
  have hvi : v i = X := by simp [hv]
  have hvj : v j = Y := by simp [hv, Ne.symm hij]
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by
    simp
  have hyx : dotp y x = 0 := by rw [dotp_comm]; exact hxy
  have horth : Orthonormal ℝ (({i, j} : Set (Fin n)).restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨a, ha⟩ ⟨c, hc⟩
    have hmem : ∀ u : Fin n, u ∈ ({i, j} : Set (Fin n)) → u = i ∨ u = j := by
      intro u hu; simpa using hu
    simp only [Set.restrict_apply, Subtype.mk.injEq]
    rcases hmem a ha with rfl | rfl <;> rcases hmem c hc with rfl | rfl
    · rw [hvi, hX, inner_eq_dotp, hxx, if_pos rfl]
    · rw [hvi, hvj, hX, hY, inner_eq_dotp, hxy, if_neg hij]
    · rw [hvj, hvi, hY, hX, inner_eq_dotp, hyx, if_neg (Ne.symm hij)]
    · rw [hvj, hY, inner_eq_dotp, hyy, if_pos rfl]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  have hrows : ∀ a a' : Fin n, ∑ t, (b a).ofLp t * (b a').ofLp t = delta a a' := by
    intro a a'
    have hin := orthonormal_iff_ite.mp b.orthonormal a a'
    have hcast : inner ℝ (b a) (b a') = dotp ((b a).ofLp) ((b a').ofLp) :=
      inner_eq_dotp ((b a).ofLp) ((b a').ofLp)
    rw [hcast] at hin
    simp only [dotp] at hin
    rw [hin]
    by_cases h : a = a' <;> simp [delta, h]
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun a t => (b a).ofLp t) with hM
  have hmul : M * Mᵀ = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext a a'
    simp only [hM, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [hrows a a']
    by_cases h : a = a' <;> simp [delta, h]
  have hmul' : Mᵀ * M = (1 : Matrix (Fin n) (Fin n) ℝ) := mul_eq_one_comm.mp hmul
  refine ⟨fun a t => (b a).ofLp t, ⟨hrows, ?_⟩, ?_, ?_⟩
  · intro p q
    have hpq := congrFun (congrFun hmul' p) q
    simp only [hM, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.one_apply] at hpq
    rw [hpq]
    by_cases h : p = q <;> simp [delta, h]
  · intro t
    have hbi : b i = X := by rw [hb i (Set.mem_insert i _), hvi]
    have hval : (b i).ofLp t = x t := by rw [hbi, hX]
    exact hval
  · intro t
    have hbj : b j = Y := by rw [hb j (Set.mem_insert_of_mem _ rfl), hvj]
    have hval : (b j).ofLp t = y t := by rw [hbj, hY]
    exact hval

/-- **THE HYPOTHESIS `eq_zero_of_ip_orbit` WAS CARRYING, DISCHARGED.** -/
theorem sec_eq_zero_of_rows (hn : 2 ≤ n) {Z : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hZ : IsAlgCurv Z)
    (hrows : ∀ P : Fin n → Fin n → ℝ, IsOrth P → ∀ i j,
      LovelockSectional.sec Z (fun t => P i t) (fun t => P j t) = 0)
    (x y : Fin n → ℝ) : LovelockSectional.sec Z x y = 0 := by
  refine sec_eq_zero_of_orthonormal hZ (fun u v huu hvv huv => ?_) x y
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  have hij : (⟨0, h0⟩ : Fin n) ≠ ⟨1, h1⟩ := by
    intro hc
    exact absurd (congrArg Fin.val hc) (by norm_num)
  obtain ⟨Q, hQ, hQi, hQj⟩ := exists_isOrth_rows hij u v huu hvv huv
  have hkey := hrows Q hQ ⟨0, h0⟩ ⟨1, h1⟩
  rw [funext hQi, funext hQj] at hkey
  exact hkey

/-- **AND SO THE ROUTE'S CONCLUSION IS UNCONDITIONAL.** -/
theorem eq_zero_of_ip_orbit_uncond (hn : 2 ≤ n)
    {Z : Fin n → Fin n → Fin n → Fin n → ℝ} (hZ : IsAlgCurv Z)
    (h0 : ∀ b c, ricci Z b c = 0)
    (horth : ∀ P : Fin n → Fin n → ℝ, IsOrth P → ∀ i j,
      ip Z (act P (weylPart (knSquare (WeylNonzeroGeneral.twoProj i j)))) = 0)
    (a b c d : Fin n) : Z a b c d = 0 :=
  LovelockWitnessPairing.eq_zero_of_ip_orbit
    (fun _ hW hrows xx yy => sec_eq_zero_of_rows hn hW hrows xx yy) hZ h0 horth a b c d

end LovelockOrthonormalFrame
