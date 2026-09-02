import WeylNonzeroFour

/-!
# The Weyl summand in every dimension, as a formula that vanishes exactly at three

`WeylNonzeroFour` exhibited one non-zero Weyl entry in one tensor in one dimension, and fenced
itself in as plainly as it could:

> **And it is one witness, not a dimension count.** The file does not compute the rank of the Weyl
> summand, does not claim `n = 4` is the first dimension where it is non-zero, and does not touch
> `n ≥ 5`.

`PROOF_STRATEGY` §7 item 3 says to take a result proved under a restrictive hypothesis and remove
one. **The fence here is the dimension, and it comes off entirely.**

## What is proved

`twoProj i j` is the orthogonal projector onto the plane spanned by two distinct coordinate axes,
written in the estate's `delta` idiom as `δ_{ai}δ_{bi} + δ_{aj}δ_{bj}`. It is symmetric, has trace
`2`, and is idempotent — the three facts `projOff` needed, proved the same way. Its
Kulkarni–Nomizu square is an algebraic curvature tensor, and:

**`weylPart_twoProj_entry`** — for `i ≠ j` and `(n:ℝ) ∉ {0, 1, 2}`,

    weylPart (knSquare (twoProj i j)) i j j i  =  (n − 3) / (n − 1)

**One formula for every dimension.** It is **non-zero** from `n = 4` up
(`weylPart_ne_zero_of_four_le` — non-zero is what is proved and what is used; positivity is
visible but not claimed), and **it is zero at `n = 3`**.

`WeylNonzeroFour` is **subsumed in scope** by this and is kept deliberately: its `n = 4` value
comes from `norm_num +decide` on concrete `Fin 4` entries, which is an independent route, and
`agrees_with_four` below turns that into a check the estate runs rather than a coincidence a reader
notices.

## What the vanishing at three is, and what it is not

**It is a consistency check, not a second proof of `WeylVanishesThree`.** That theorem says the
Weyl summand vanishes for *every* algebraic curvature tensor in three dimensions; this formula says
*this one witness* has a zero entry there. The second does not imply the first, and the file does
not claim it does. What it does buy is that the three-dimensional collapse now appears as **the
zero of an explicit function of `n`** rather than as an unrelated fact, so the reader can see where
the special dimension comes from.

**And the four-dimensional value agrees with the number `WeylNonzeroFour` obtained by a completely
different route** — `norm_num +decide` on concrete `Fin 4` entries, against symbolic algebra in
general `n`. `agrees_with_four` states that agreement as a theorem, because two computations
landing on `1/3` is a check the estate can run and a coincidence of prose is not.

## What is still NOT proved

**Nothing here bears on `KillsWeyl`.** It says the subject of that statement is non-trivial in
every dimension from four up rather than only in four — a strictly larger *non*-vacuity claim, and
still not a step toward the statement itself. The watchlist item does not move.


**⚠ SUPERSEDED — `LovelockKillsWeyl.killsWeyl_of_equivariant` PROVES `KillsWeyl` AT EVERY `n ≥ 3`**
(`171d474`, 15 August), and the paragraph above is kept per `ERRATUM 94`. Every additive,
homogeneous, `O(n)`-equivariant `T` annihilates the Weyl summand; `classification` follows, and the
watchlist's Lovelock item is CLOSED — its sweep record reads *"the closure is `KillsWeyl` at every
`n ≥ 3`"*. **So *"the watchlist item does not move"* is true only in the sense that a closed item
cannot move, and it invites the opposite reading.** What is still open at W5 is not this: it is
rung 2 of `WALLS` §W5.1's staircase, an **affine connection and Levi-Civita** — zero names in
Mathlib. `ERRATUM 230`.

**And still no dimension count.** The rank of the Weyl summand is not computed here either. One
entry of one tensor is all that is claimed, now for every `n`.

**^ THE CLAUSE ABOVE PUTTING THE AFFINE CONNECTION AT *ZERO NAMES IN MATHLIB* IS FALSE, AND IS
KEPT AS WRITTEN** (`ERRATUM 416`, 2026-09-02). Mathlib has **`CovariantDerivative`** — 73 names in
this estate's own `env_names.txt` — and `IsCovariantDerivativeOn` (24), with `torsion` beside them;
the probe behind the clause asked for the lower-case `covariantDerivative`, which is **0**
(`ERRATUM 411`). **EVERY OTHER CLAUSE STANDS, RE-PROBED TODAY RATHER THAN INHERITED**: `LeviCivita`
**0**, `HeatKernel` and `heatKernel` **0** each, and curvature **0** in four spellings
(`Curvature`, `curvature`, `riemannianCurvature`, `RiemannCurvature`). **So rung 2 is still the
wall's remaining step, this file still does not bear on it, and no verdict here changes** — what
moved is the rung W5 fails at, which `WALLS` §W5.1 records. **The clause reached eight files by
header inheritance, which is the mechanism `ERRATUM 230` already names**, and no absence mode caught
it because the sentence names no identifier to probe.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace WeylNonzeroGeneral

open AlgebraicCurvature LovelockProjections Finset

variable {n : ℕ}

/-! ## 1. The rank-two projector

Written in the `delta` idiom `projOff` uses, so that `sum_delta_left` does all the contractions.
-/

/-- **THE PROJECTOR ONTO THE PLANE OF TWO COORDINATE AXES.** -/
def twoProj (i j : Fin n) (a b : Fin n) : ℝ := delta a i * delta b i + delta a j * delta b j

theorem twoProj_symm (i j : Fin n) (a b : Fin n) : twoProj i j a b = twoProj i j b a := by
  simp only [twoProj]; ring

/-- `δ` is idempotent entrywise. -/
theorem delta_sq (a b : Fin n) : delta a b * delta a b = delta a b := by
  by_cases h : a = b <;> simp [delta, h]

/-- And two distinct axes are orthogonal: no index is both. -/
theorem delta_mul_delta_of_ne {i j : Fin n} (hij : i ≠ j) (a : Fin n) :
    delta a i * delta a j = 0 := by
  by_cases h : a = i
  · have hj : a ≠ j := by rw [h]; exact hij
    simp [delta, hj]
  · simp [delta, h]

/-- **ITS TRACE IS `2`**, and this needs no hypothesis: two rank-one projectors, each of trace
one, whether or not they are the same one. -/
theorem sum_twoProj_diag (i j : Fin n) : ∑ a, twoProj i j a a = 2 := by
  have hpt : ∀ a : Fin n, twoProj i j a a = delta a i * delta a i + delta a j * delta a j :=
    fun _ => rfl
  rw [Finset.sum_congr rfl fun a _ => hpt a, Finset.sum_add_distrib,
    sum_delta_left i fun a => delta a i, sum_delta_left j fun a => delta a j, delta_self,
    delta_self]
  norm_num

/-- **AND IT IS IDEMPOTENT**, which is where `i ≠ j` is spent: the two rank-one pieces are
orthogonal exactly when the axes are distinct. -/
theorem sum_twoProj_mul {i j : Fin n} (hij : i ≠ j) (b c : Fin n) :
    ∑ a, twoProj i j a c * twoProj i j b a = twoProj i j b c := by
  have hpt : ∀ a : Fin n, twoProj i j a c * twoProj i j b a
      = delta a i * (delta c i * delta b i) + delta a j * (delta c j * delta b j) := by
    intro a
    simp only [twoProj]
    linear_combination (delta c i * delta b i) * delta_sq a i
      + (delta c j * delta b j) * delta_sq a j
      + (delta c i * delta b j + delta c j * delta b i) * delta_mul_delta_of_ne hij a
  rw [Finset.sum_congr rfl fun a _ => hpt a, Finset.sum_add_distrib,
    sum_delta_left i fun _ => delta c i * delta b i,
    sum_delta_left j fun _ => delta c j * delta b j]
  simp only [twoProj]
  ring

theorem isAlgCurv_twoProjCurv (i j : Fin n) : IsAlgCurv (knSquare (twoProj i j)) :=
  isAlgCurv_knSquare (twoProj_symm i j)

/-! ## 2. Its Ricci tensor is the projector back again -/

theorem ricci_twoProjCurv {i j : Fin n} (hij : i ≠ j) (b c : Fin n) :
    ricci (knSquare (twoProj i j)) b c = twoProj i j b c := by
  rw [ricci_knSquare, sum_twoProj_diag, sum_twoProj_mul hij]
  ring

theorem scal_twoProjCurv {i j : Fin n} (hij : i ≠ j) :
    scal (knSquare (twoProj i j)) = 2 := by
  have hs : scal (knSquare (twoProj i j)) = ∑ b, ricci (knSquare (twoProj i j)) b b := rfl
  rw [hs, Finset.sum_congr rfl fun b _ => ricci_twoProjCurv hij b b, sum_twoProj_diag]

/-! ## 3. The three entries the computation needs -/

theorem twoProj_left {i j : Fin n} (hij : i ≠ j) : twoProj i j i i = 1 := by
  simp [twoProj, delta, hij]

theorem twoProj_right {i j : Fin n} (hij : i ≠ j) : twoProj i j j j = 1 := by
  simp [twoProj, delta, Ne.symm hij]

theorem twoProj_off {i j : Fin n} (hij : i ≠ j) : twoProj i j i j = 0 := by
  simp [twoProj, delta, hij, Ne.symm hij]

/-! ## 4. The entry, in every dimension -/

/-- **THE FORMULA.** One entry of the Weyl summand of the plane projector's square, in every
dimension where the decomposition exists. It is `0` exactly at `n = 3`. -/
theorem weylPart_twoProj_entry (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0)
    (hn2 : (n : ℝ) - 2 ≠ 0) {i j : Fin n} (hij : i ≠ j) :
    weylPart (knSquare (twoProj i j)) i j j i = ((n : ℝ) - 3) / ((n : ℝ) - 1) := by
  have hji : delta j i = (0 : ℝ) := by simp [delta, Ne.symm hij]
  have hij0 : delta i j = (0 : ℝ) := by simp [delta, hij]
  -- the tensor itself
  have hR : knSquare (twoProj i j) i j j i = 1 := by
    simp only [knSquare]
    rw [twoProj_left hij, twoProj_right hij, twoProj_off hij,
      twoProj_symm i j j i, twoProj_off hij]
    ring
  -- the traceless Ricci tensor at the two diagonal entries
  have hdiag : ∀ b : Fin n, twoProj i j b b = 1 →
      tracefreeRicci (knSquare (twoProj i j)) b b = 1 - 2 / (n : ℝ) := by
    intro b hb
    rw [tracefreeRicci, ricci_twoProjCurv hij, scal_twoProjCurv hij, hb, delta_self]
    ring
  have hoff : tracefreeRicci (knSquare (twoProj i j)) i j = 0 := by
    rw [tracefreeRicci, ricci_twoProjCurv hij, twoProj_off hij, hij0]
    ring
  have hoff' : tracefreeRicci (knSquare (twoProj i j)) j i = 0 := by
    rw [tracefreeRicci, ricci_twoProjCurv hij, twoProj_symm i j j i, twoProj_off hij, hji]
    ring
  -- the Ricci summand
  have hric : ricciPart (knSquare (twoProj i j)) i j j i = 2 / (n : ℝ) := by
    have hdef : ricciPart (knSquare (twoProj i j)) i j j i
        = (1 / ((n : ℝ) - 2))
          * kn (tracefreeRicci (knSquare (twoProj i j))) delta i j j i := rfl
    rw [hdef, kn, hdiag i (twoProj_left hij), hdiag j (twoProj_right hij), hoff, hoff',
      delta_self, delta_self, hji, hij0]
    field_simp
    ring
  -- the scalar summand
  have hsc : scalPart (knSquare (twoProj i j)) i j j i = 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    have hdef : scalPart (knSquare (twoProj i j)) i j j i
        = (scal (knSquare (twoProj i j)) / ((n : ℝ) * ((n : ℝ) - 1)))
          * knSquare delta i j j i := rfl
    rw [hdef, scal_twoProjCurv hij, knSquare, delta_self, delta_self, hji, hij0]
    ring
  have hw : weylPart (knSquare (twoProj i j)) i j j i
      = knSquare (twoProj i j) i j j i - ricciPart (knSquare (twoProj i j)) i j j i
        - scalPart (knSquare (twoProj i j)) i j j i := rfl
  rw [hw, hR, hric, hsc]
  field_simp
  ring

/-! ## 5. And therefore the summand is non-zero in every dimension from four up -/

/-- **THE FENCE REMOVED.** -/
theorem weylPart_ne_zero_of_four_le (hn : 4 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    weylPart (knSquare (twoProj i j)) ≠ fun _ _ _ _ => (0 : ℝ) := by
  have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
  intro h
  have h0 : weylPart (knSquare (twoProj i j)) i j j i = 0 := by rw [h]
  rw [weylPart_twoProj_entry hn0 hn1 hn2 hij] at h0
  have hne : (n : ℝ) - 3 ≠ 0 := by linarith
  exact hne (by field_simp at h0; linarith)

/-- **THE SUBJECT OF `KillsWeyl` EXISTS IN EVERY DIMENSION FROM FOUR UP**, not only in four. -/
theorem exists_weylPart_ne_zero (hn : 4 ≤ n) :
    ∃ R : Fin n → Fin n → Fin n → Fin n → ℝ,
      IsAlgCurv R ∧ weylPart R ≠ fun _ _ _ _ => (0 : ℝ) := by
  have h2 : (2 : ℕ) ≤ n := by omega
  refine ⟨knSquare (twoProj ⟨0, by omega⟩ ⟨1, by omega⟩), isAlgCurv_twoProjCurv _ _,
    weylPart_ne_zero_of_four_le hn ?_⟩
  intro h
  exact absurd (congrArg Fin.val h) (by norm_num)

/-! ## 6. Two checks, labelled as checks -/

/-- **THE FORMULA AGREES WITH `WeylNonzeroFour`'s NUMBER**, obtained there by `norm_num +decide` on
concrete `Fin 4` entries against symbolic algebra here. Two computations landing on `1/3` is a
check the estate can run; a coincidence noticed in prose is not. -/
theorem agrees_with_four :
    weylPart (knSquare (twoProj (0 : Fin 4) 1)) 0 1 1 0
      = weylPart (knSquare WeylNonzeroFour.plane) 0 1 1 0 := by
  rw [WeylNonzeroFour.weylPart_plane_entry,
    weylPart_twoProj_entry (by norm_num) (by norm_num) (by norm_num) (by decide)]
  norm_num

/-- **AND IT VANISHES AT `n = 3`**, which is where `WeylVanishesThree` says the whole summand
vanishes. **This is a consistency check and not a second proof of that theorem** — it concerns one
entry of one tensor, where `WeylVanishesThree` quantifies over every algebraic curvature tensor.
What it buys is that the three-dimensional collapse is visibly the zero of an explicit function of
`n` rather than an unrelated fact. -/
theorem vanishes_at_three {i j : Fin 3} (hij : i ≠ j) :
    weylPart (knSquare (twoProj i j)) i j j i = 0 := by
  rw [weylPart_twoProj_entry (by norm_num) (by norm_num) (by norm_num) hij]
  norm_num

end WeylNonzeroGeneral
