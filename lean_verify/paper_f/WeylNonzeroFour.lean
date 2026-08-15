import LovelockDiagonalise

/-!
# The Weyl summand is not zero in four dimensions, so `KillsWeyl` is a real condition there

`LovelockDiagonalise` closed `RicciProportional` and, with `WeylVanishesThree`, the whole
classification at `n = 3`. Its header then said, of why that does not generalise:

> `n = 3` falls out only because `WeylVanishesThree` shows the Weyl summand is *identically zero*
> there, which is a fact about three dimensions and not a method.

**That sentence was prose, and the estate had nothing behind it.** Grepped before this file was
written: `weylPart` appears in `LovelockProjections`, `LovelockEquivariance`,
`LovelockOrthogonality`, `LovelockReduction` and `WeylVanishesThree`, and **no statement anywhere
says it is non-zero, in any dimension.** So for as long as the estate has had `KillsWeyl`, nothing
in it ruled out the summand being identically zero at every `n` — in which case `KillsWeyl` would
be **automatic everywhere**, `LovelockReduction`'s split into two `Prop`s would be a split into one
and a triviality, and the remaining wall would not exist.

This is `AlgebraicCurvature` §3's own standard — *do not state a theorem about a class whose only
evident member is trivial* — applied to the one place in this group where it had not been.

## What is proved

`plane` is the diagonal form `diag(1,1,0,0)` on `Fin 4`, and `knSquare plane` is its
Kulkarni–Nomizu square: an algebraic curvature tensor by `isAlgCurv_knSquare`, symmetric by
inspection. It is the algebraic shadow of a product of a round surface with a flat plane.

**`weylPart_plane_entry`** computes one entry outright:

    weylPart (knSquare plane) 0 1 1 0  =  1/3

and **`weylPart_ne_zero_four`** and **`exists_weylPart_ne_zero_four`** are the consequences. So:

* the Weyl summand is **not** identically zero at `n = 4`;
* `WeylVanishesThree.weylPart_eq_zero`, which says it *is* identically zero at `n = 3`, does not
  extend — and that is now a machine-checked contrast rather than a remark;
* **`KillsWeyl T` at `n = 4` is a genuine constraint on `T`**, not a statement that holds because
  its subject vanishes.

## What this is NOT

**It is not progress on `KillsWeyl`.** It says the question is real, not that it is answerable. The
missing invariant theory — that the Weyl summand contains no copy of the symmetric-2-tensor
representation of `O(n)` — is exactly as absent as it was, and the watchlist item does not move.

**And it is one witness, not a dimension count.** The file does not compute the rank of the Weyl
summand, does not claim `n = 4` is the first dimension where it is non-zero, and does not touch
`n ≥ 5`. One non-zero entry in one tensor in one dimension is all that is claimed, because that is
all that is needed to make `KillsWeyl` non-vacuous where the classification is still open.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace WeylNonzeroFour

open AlgebraicCurvature LovelockProjections Finset

/-! ## 1. The witness -/

/-- **`diag(1, 1, 0, 0)`**, written in the estate's idiom: the metric with two coordinates
projected out, the same shape as `projOff` with two indices instead of one. -/
def plane (a b : Fin 4) : ℝ := delta a b - delta a 2 * delta b 2 - delta a 3 * delta b 3

theorem plane_symm (a b : Fin 4) : plane a b = plane b a := by
  simp only [plane]
  rw [delta_symm a b]
  ring

/-- Its Kulkarni–Nomizu square is an algebraic curvature tensor. -/
theorem isAlgCurv_planeCurv : IsAlgCurv (knSquare plane) :=
  isAlgCurv_knSquare plane_symm

/-! ## 2. One entry of its Weyl part, computed

Everything below is arithmetic on `Fin 4`: `ricci` is a sum of four terms, `scal` a sum of four of
those, and `weylPart` is `R` minus two explicit multiples. The entry `(0,1,1,0)` is chosen because
`R` there is `1` while the two projections contribute `1/2` and `1/6`.

`+decide` is on the `norm_num` call and is load-bearing: without it `simp` leaves `if (0 : Fin 4) =
2 then …` standing, because the index equalities are decidable propositions the default simp set
does not reduce here. It adds no axiom — `#print axioms` on the result is the three standard ones.
-/

/-- **THE COMPUTATION.** -/
theorem weylPart_plane_entry : weylPart (knSquare plane) 0 1 1 0 = 1 / 3 := by
  norm_num +decide [weylPart, ricciPart, scalPart, tracefreeRicci, ricci, scal, kn, knSquare,
    plane, delta, Fin.sum_univ_four]

/-! ## 3. And therefore `KillsWeyl` is not vacuous at `n = 4` -/

/-- **THE WEYL SUMMAND IS NOT IDENTICALLY ZERO IN FOUR DIMENSIONS.** -/
theorem weylPart_ne_zero_four : weylPart (knSquare plane) ≠ fun _ _ _ _ => (0 : ℝ) := by
  intro h
  have h0 : weylPart (knSquare plane) 0 1 1 0 = 0 := by rw [h]
  rw [weylPart_plane_entry] at h0
  norm_num at h0

/-- **SO THE SUBJECT OF `KillsWeyl` EXISTS AT `n = 4`.** Compare
`WeylVanishesThree.weylPart_eq_zero`, which says the summand is identically zero at `n = 3`: that
is what makes the three-dimensional classification fall out, and it is a fact about three
dimensions and not a method. -/
theorem exists_weylPart_ne_zero_four :
    ∃ R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ,
      IsAlgCurv R ∧ weylPart R ≠ fun _ _ _ _ => (0 : ℝ) :=
  ⟨knSquare plane, isAlgCurv_planeCurv, weylPart_ne_zero_four⟩

/-- **AND THE CONTRAST, STATED AS ONE THEOREM.** At `n = 3` every algebraic curvature tensor has
zero Weyl part; at `n = 4` some does not. This is the whole reason `LovelockDiagonalise`'s
three-dimensional classification does not generalise, and it is now checked rather than asserted. -/
theorem weylPart_zero_three_nonzero_four :
    (∀ R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ, IsAlgCurv R →
        weylPart R = fun _ _ _ _ => (0 : ℝ))
      ∧ ∃ R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ,
          IsAlgCurv R ∧ weylPart R ≠ fun _ _ _ _ => (0 : ℝ) :=
  ⟨fun _ hR => WeylVanishesThree.weylPart_eq_zero_fun hR, exists_weylPart_ne_zero_four⟩

end WeylNonzeroFour
