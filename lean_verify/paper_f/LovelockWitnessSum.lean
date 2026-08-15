import LovelockWeylTwoValues
import LovelockDiagonalSum

/-!
# The second guess, discharged: the witnesses sum to the constant-curvature tensor

`LovelockWeylWitness` and `LovelockWeylTwoValues` both ended by naming the same unproved step and
labelling it a **hand sketch, hence a guess**:

> `∑_{i<j} knSquare (twoProj i j)` should be `constCurv`, whose Weyl part vanishes, giving one
> linear relation between the two numbers and leaving one. **That is still a hand sketch and it is
> still not proved here.**

**It is proved here, and the sketch was right.** Summing over *ordered* pairs — which is what Lean
wants and which double-counts, the diagonal terms `i = j` vanishing on their own — gives exactly
`2 · constCurv n`.

## What is proved

* `quart`, `quart_symm` and `sum_twoProj_pair` — the two-index contraction that the double sum
  produces, and the one symmetry of it the subtraction needs;
* **`sum_knSquare_twoProj`** — `∑_i ∑_j knSquare (twoProj i j) = 2 · constCurv n`, in every
  dimension, with no hypothesis;
* **`weylPart_constCurv`** — the constant-curvature tensor has no Weyl part. Its traceless Ricci
  tensor vanishes, so `ricciPart` does, and `scalPart` recovers the whole of it;
* `ricci_sum`, `scal_sum`, `tracefreeRicci_sum`, `kn_sum_left`, `ricciPart_sum`, `scalPart_sum` and
  **`weylPart_sum`** — **the three projections pass through a finite sum**, over an arbitrary
  `Fintype` index. The estate has never needed this and did not have it; each is one `simp only`
  or one `Finset.sum_comm`;
* **`sum_weylPart_twoProj`** — so the Weyl parts of the witnesses sum to **zero**;
* **`T_sum_weyl_twoProj`** — and therefore, for any additive homogeneous `T`,
  `∑_i ∑_j T (weylPart (knSquare (twoProj i j))) b c = 0`. **A linear relation among the values
  `T` takes on the witness family.**

## What this does and does not give

**It does not by itself cut the two numbers to one**, and the reason is worth stating exactly.
`LovelockWeylTwoValues` proved that for a **fixed** pair `(i,j)` the tensor `T W_{ij}` is diagonal
with two values. Collapsing the double sum above into a count of those two values needs one more
thing: **that the two values do not depend on which pair `(i,j)` was chosen.** That follows from
permutation equivariance moving one pair to another, and **it is not proved here** — the transport
lemma exists in spirit (`act_knSquare` plus `act2_permMat` send `knSquare (twoProj i j)` to
`knSquare (twoProj (σ⁻¹ i) (σ⁻¹ j))`) but constructing the permutation carrying an arbitrary pair
to another is a step nobody has written.

**So the count still stands at two.** `KillsWeyl` asks for zero; `n²` → `n` → `2` → **2**. The
watchlist item does not move.

**And even one would not be `KillsWeyl`**, for the reason both predecessors give: one witness family
is not every algebraic curvature tensor, and whether the orbit of a Weyl tensor spans the Weyl
summand is `WALLS` §W5.0 §5b's irreducibility question, untouched.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockWitnessSum

open AlgebraicCurvature LovelockProjections LovelockEquivariance WeylNonzeroGeneral
  LovelockWeylTwoValues LovelockDiagonalSum Finset

variable {n : ℕ}
variable {T : (Fin n → Fin n → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ}

/-! ## 1. The sum over the witness family -/

/-- The quartic delta contraction, which the free index of the double sum multiplies. -/
def quart (a b c d : Fin n) : ℝ := ∑ i, delta a i * delta d i * (delta b i * delta c i)

theorem quart_symm (a b c d : Fin n) : quart a b c d = quart a b d c := by
  simp only [quart]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sum_twoProj_pair (a d b c : Fin n) :
    ∑ i, ∑ j, twoProj i j a d * twoProj i j b c
      = 2 * ((n : ℝ) * quart a b c d) + 2 * (delta a d * delta b c) := by
  have expand : ∀ i j : Fin n, twoProj i j a d * twoProj i j b c
      = delta a i * delta d i * (delta b i * delta c i)
        + delta a i * delta d i * (delta b j * delta c j)
        + delta a j * delta d j * (delta b i * delta c i)
        + delta a j * delta d j * (delta b j * delta c j) := by
    intro i j; simp only [twoProj]; ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => expand i j]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  simp only [quart, sum_delta_right]
  ring

theorem sum_knSquare_twoProj (a b c d : Fin n) :
    ∑ i, ∑ j, knSquare (twoProj i j) a b c d = 2 * constCurv n a b c d := by
  have hsplit : ∀ i j : Fin n, knSquare (twoProj i j) a b c d
      = twoProj i j a d * twoProj i j b c - twoProj i j a c * twoProj i j b d := by
    intro i j; simp only [knSquare]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j]
  simp only [Finset.sum_sub_distrib]
  rw [sum_twoProj_pair a d b c, sum_twoProj_pair a c b d]
  have hq : quart a b d c = quart a b c d := (quart_symm a b c d).symm
  simp only [constCurv]
  rw [hq]
  ring

theorem weylPart_constCurv (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0) (a b c d : Fin n) :
    weylPart (constCurv n) a b c d = 0 := by
  have hric : ∀ x y : Fin n, tracefreeRicci (constCurv n) x y = 0 := by
    intro x y
    simp only [tracefreeRicci, ricci_constCurv, scal_constCurv]
    field_simp
    ring
  have hr : ricciPart (constCurv n) a b c d = 0 := by
    simp only [ricciPart, kn, hric]
    ring
  have hs : scalPart (constCurv n) a b c d = constCurv n a b c d := by
    simp only [scalPart, scal_constCurv, knSquare_delta]
    field_simp
  simp only [weylPart, hr, hs]
  ring

/-! ## 2. The three projections pass through a finite sum -/

variable {ι : Type} [Fintype ι]

theorem ricci_sum (F : ι → Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) :
    ricci (fun a b' c' d' => ∑ i, F i a b' c' d') b c = ∑ i, ricci (F i) b c := by
  simp only [ricci]
  exact Finset.sum_comm

theorem scal_sum (F : ι → Fin n → Fin n → Fin n → Fin n → ℝ) :
    scal (fun a b' c' d' => ∑ i, F i a b' c' d') = ∑ i, scal (F i) := by
  simp only [scal]
  rw [Finset.sum_congr rfl fun b _ => ricci_sum F b b]
  exact Finset.sum_comm

theorem tracefreeRicci_sum (F : ι → Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) :
    tracefreeRicci (fun a b' c' d' => ∑ i, F i a b' c' d') b c
      = ∑ i, tracefreeRicci (F i) b c := by
  simp only [tracefreeRicci, ricci_sum, scal_sum, Finset.sum_div, Finset.sum_mul,
    ← Finset.sum_sub_distrib]

theorem kn_sum_left (H : ι → Fin n → Fin n → ℝ) (k : Fin n → Fin n → ℝ) (a b c d : Fin n) :
    kn (fun x y => ∑ i, H i x y) k a b c d = ∑ i, kn (H i) k a b c d := by
  simp only [kn, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]

theorem ricciPart_sum (F : ι → Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    ricciPart (fun x y z w => ∑ i, F i x y z w) a b c d = ∑ i, ricciPart (F i) a b c d := by
  simp only [ricciPart]
  rw [show (tracefreeRicci fun x y z w => ∑ i, F i x y z w)
      = fun x y => ∑ i, tracefreeRicci (F i) x y from
    funext fun x => funext fun y => tracefreeRicci_sum F x y, kn_sum_left, Finset.mul_sum]

theorem scalPart_sum (F : ι → Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    scalPart (fun x y z w => ∑ i, F i x y z w) a b c d = ∑ i, scalPart (F i) a b c d := by
  simp only [scalPart, scal_sum, Finset.sum_div, Finset.sum_mul]

theorem weylPart_sum (F : ι → Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    weylPart (fun x y z w => ∑ i, F i x y z w) a b c d = ∑ i, weylPart (F i) a b c d := by
  simp only [weylPart, ricciPart_sum, scalPart_sum, ← Finset.sum_sub_distrib]

/-! ## 3. And therefore the Weyl parts sum to zero -/

theorem sum_weylPart_twoProj (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0) (a b c d : Fin n) :
    ∑ i, ∑ j, weylPart (knSquare (twoProj i j)) a b c d = 0 := by
  have hfun : (fun x y z w => ∑ i : Fin n, ∑ j : Fin n, knSquare (twoProj i j) x y z w)
      = fun x y z w => ∑ _i : Fin 2, constCurv n x y z w := by
    funext x y z w
    rw [sum_knSquare_twoProj]
    simp [Finset.sum_const]
  have h1 : weylPart (fun x y z w => ∑ i : Fin n, ∑ j : Fin n, knSquare (twoProj i j) x y z w)
      a b c d = ∑ i : Fin n, ∑ j : Fin n, weylPart (knSquare (twoProj i j)) a b c d := by
    rw [weylPart_sum (fun i => fun x y z w => ∑ j : Fin n, knSquare (twoProj i j) x y z w)]
    exact Finset.sum_congr rfl fun i _ => weylPart_sum (fun j => knSquare (twoProj i j)) a b c d
  rw [hfun] at h1
  rw [weylPart_sum (fun _ : Fin 2 => constCurv n)] at h1
  rw [Finset.sum_congr rfl fun (_ : Fin 2) _ => weylPart_constCurv hn0 hn1 a b c d] at h1
  simpa using h1.symm

theorem T_sum_weyl_twoProj
    (hadd : ∀ R S, T (fun a b c d => R a b c d + S a b c d) = fun b c => T R b c + T S b c)
    (hsmul : ∀ (lam : ℝ) R, T (fun a b c d => lam * R a b c d) = fun b c => lam * T R b c)
    (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0) (b c : Fin n) :
    ∑ i, ∑ j, T (weylPart (knSquare (twoProj i j))) b c = 0 := by
  have hzero : (fun x y z w => ∑ i : Fin n, ∑ j : Fin n,
      weylPart (knSquare (twoProj i j)) x y z w) = fun _ _ _ _ => (0 : ℝ) :=
    funext fun x => funext fun y => funext fun z => funext fun w =>
      sum_weylPart_twoProj hn0 hn1 x y z w
  have h1 : T (fun x y z w => ∑ i : Fin n, ∑ j : Fin n,
      weylPart (knSquare (twoProj i j)) x y z w) b c
      = ∑ i : Fin n, ∑ j : Fin n, T (weylPart (knSquare (twoProj i j))) b c := by
    rw [T_sum hadd hsmul univ
      (fun i => fun x y z w => ∑ j : Fin n, weylPart (knSquare (twoProj i j)) x y z w) b c]
    exact Finset.sum_congr rfl fun i _ =>
      T_sum hadd hsmul univ (fun j => weylPart (knSquare (twoProj i j))) b c
  rw [hzero, T_zero hsmul] at h1
  exact h1.symm

end LovelockWitnessSum
