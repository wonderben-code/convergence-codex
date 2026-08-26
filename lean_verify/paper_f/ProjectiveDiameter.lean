import IsingTransferSym

/-!
# The Hilbert projective diameter of the two-dimensional transfer matrix, and it is unbounded

`WALLS §W4 §6 item 3` — the sub-top eigenvalue ratio bounded away from one **uniformly in the strip
width** — has one route recorded and killed. `SpectralEntryRatio` bounds the ratio by
`√(b² − a²)/a` for entries in `[a, b]` with no dependence on the matrix's size, which is the right
shape; and the entry ratio of `transferSym β n` is `exp(Θ(β n))`, so the route is silent at every
`β > 0`. The watch-list block names what would replace it:

> *"an estimate that sees the matrix's STRUCTURE — that the large entries are few and correlated
> across rows — where this one sees only their range. The classical route with that property is the
> Birkhoff-Hopf contraction coefficient, which needs the Hilbert projective metric. Probed rather
> than assumed: `grep -rn Birkhoff Mathlib` returns three hits, two of them Poincare-Birkhoff-Witt
> and one an unrelated comment, and there is no projective metric of any kind. **A build, not a
> citation.**"*

(Quoted with the record's own ASCII spelling of the names. A quotation that has been tidied is not
a quotation.)

**This is the first piece of that build, and it is a negative.** The quantity the Birkhoff–Hopf
coefficient consumes is the projective DIAMETER, and this file computes it for the estate's own
transfer matrix and shows it diverges — at an exhibited quadruple of columns, with the value in
closed form, not as an estimate.

## What is proved

* **`crossRatio`** — `(A i k * A j l) / (A i l * A j k)`, the four-index quantity whose logarithm's
  supremum is the Hilbert projective diameter, and **`HasDiameterLE`**, the predicate that every
  such logarithm is at most `D`. The predicate rather than the supremum, deliberately: a lower
  bound on a diameter is a witness, and a witness refutes a `∀`.
* **`log_crossRatio_transferSym`** — the cross-ratio of `transferSym β n` is
  `exp (β * (inter σ τ + inter σ' τ' − inter σ τ' − inter σ' τ))`. **The `intra` factors cancel
  exactly**: each column's own weight appears once in the numerator and once in the denominator,
  which is the whole reason a cross-ratio is the right quantity and an entry ratio is not.
* **`log_crossRatio_allConst`** — at the four constant columns it is `4 * β * (n + 1)`, computed
  rather than bounded.
* **`inter_bracket_eq`, `term_le_four`, `hasDiameterLE_transferSym`** — and that quadruple is
  EXTREMAL, so the diameter is exactly `4 * β * (n + 1)` rather than at least it. The bracket is
  `∑ᵢ (spin σᵢ − spin σ'ᵢ)(spin τᵢ − spin τ'ᵢ)`, a sum of `n + 1` terms each of which is `−4`, `0`
  or `4`, every factor being a difference of two signs. **A closed form, not an estimate.**
* **`not_hasDiameterLE`** and **`diameter_unbounded`** — so for `0 < β` no `D` bounds it at every
  width.

## WHAT THIS DOES NOT SHOW, AND THE DISTINCTION IS THE POINT

**It does not refute the Birkhoff-Hopf route.** The contraction coefficient is `tanh (Δ / 4)`, and
that identity is a fact from the literature which is **not proved here and not used below** — this
paragraph is the only place in the file where the function is named, and **no declaration below
mentions it**. What is proved is that `Δ` diverges. If the classical formula holds then the
classical bound tends to `1` and cannot be uniform; that inference is stated in this paragraph and
nowhere in the Lean.

**And it does not touch `UniformSubTopRatio`.** That `Prop` is still proved at no `β` but `0`. What
this adds is that the second recorded route's input is unbounded for the same reason the first
one's was — `SpectralEntryRatio` died on a quantity already unbounded, and so does this — which is
information about the shape of any argument that will work, not about this one.

**The projective metric itself is not built.** No metric space, no triangle inequality, no
contraction theorem. `crossRatio` and `HasDiameterLE` are the two definitions the negative needs
and are all that is here.
-/

namespace ProjectiveDiameter

open Finset Real IsingTransfer2D IsingTransferSym

variable {ι : Type*} {β : ℝ} {n : ℕ}

/-! ## 1. The cross-ratio, and a bound on its logarithm -/

/-- The four-index cross-ratio of a matrix. For a matrix with positive entries the Hilbert
projective diameter is the supremum of its logarithm. -/
noncomputable def crossRatio (A : Matrix ι ι ℝ) (i j k l : ι) : ℝ :=
  (A i k * A j l) / (A i l * A j k)

/-- **THE DIAMETER IS AT MOST `D`.** Stated as a `∀` rather than as a supremum, so that a lower
bound is an exhibited quadruple and refuting it needs no analysis. -/
def HasDiameterLE (A : Matrix ι ι ℝ) (D : ℝ) : Prop :=
  ∀ i j k l, Real.log (crossRatio A i j k l) ≤ D

/-! ## 2. The transfer matrix's cross-ratio, in closed form

The point of a cross-ratio rather than a ratio of entries: `transferSym` gives each column half its
own vertical weight on both sides, so every `intra` factor occurs once above the line and once
below and cancels **exactly**. What survives is the horizontal coupling alone.
-/

theorem crossRatio_transferSym (β : ℝ) (n : ℕ) (σ σ' τ τ' : Col n) :
    crossRatio (transferSym β n) σ σ' τ τ'
      = exp (β * (inter σ τ + inter σ' τ' - inter σ τ' - inter σ' τ)) := by
  simp only [crossRatio, transferSym_apply, ← Real.exp_add, ← Real.exp_sub]
  congr 1
  ring

theorem log_crossRatio_transferSym (β : ℝ) (n : ℕ) (σ σ' τ τ' : Col n) :
    Real.log (crossRatio (transferSym β n) σ σ' τ τ')
      = β * (inter σ τ + inter σ' τ' - inter σ τ' - inter σ' τ) := by
  rw [crossRatio_transferSym, Real.log_exp]

/-! ## 3. The witness: the two constant columns -/

/-- The all-up column. -/
def allTrue (n : ℕ) : Col n := fun _ => true

/-- The all-down column. -/
def allFalse (n : ℕ) : Col n := fun _ => false

theorem inter_true_true (n : ℕ) : inter (allTrue n) (allTrue n) = (n : ℝ) + 1 := by
  simp [inter, allTrue, spin]

theorem inter_false_false (n : ℕ) : inter (allFalse n) (allFalse n) = (n : ℝ) + 1 := by
  simp [inter, allFalse, spin]

theorem inter_true_false (n : ℕ) : inter (allTrue n) (allFalse n) = -((n : ℝ) + 1) := by
  simp [inter, allTrue, allFalse, spin]

theorem inter_false_true (n : ℕ) : inter (allFalse n) (allTrue n) = -((n : ℝ) + 1) := by
  simp [inter, allFalse, allTrue, spin]

/-- **THE DIAMETER IS AT LEAST `4·β·(n+1)`, AND THIS IS AN EQUALITY AT THIS QUADRUPLE.** All four
horizontal couplings are extremal there — two aligned and two anti-aligned — so the four terms add
rather than cancel. -/
theorem log_crossRatio_allConst (β : ℝ) (n : ℕ) :
    Real.log (crossRatio (transferSym β n) (allTrue n) (allFalse n) (allTrue n) (allFalse n))
      = 4 * β * ((n : ℝ) + 1) := by
  rw [log_crossRatio_transferSym, inter_true_true, inter_false_false, inter_true_false,
    inter_false_true]
  ring

/-! ## 4. And the witness is extremal, so the diameter is EXACTLY `4·β·(n+1)`

The bracket is `∑ᵢ (spin σᵢ − spin σ'ᵢ)(spin τᵢ − spin τ'ᵢ)`: a sum of `n + 1` terms each of which
is `−4`, `0` or `4`, because every factor is a difference of two signs. So `4 (n+1)` is not merely
attained at the constant columns — it is the maximum, and the diameter is a closed form rather
than a bound.
-/

theorem inter_bracket_eq (σ σ' τ τ' : Col n) :
    inter σ τ + inter σ' τ' - inter σ τ' - inter σ' τ
      = ∑ i : Fin (n + 1), (spin (σ i) - spin (σ' i)) * (spin (τ i) - spin (τ' i)) := by
  simp only [inter, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem term_le_four (a b c d : Bool) :
    (spin a - spin b) * (spin c - spin d) ≤ 4 := by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [spin]

theorem inter_bracket_le (σ σ' τ τ' : Col n) :
    inter σ τ + inter σ' τ' - inter σ τ' - inter σ' τ ≤ 4 * ((n : ℝ) + 1) := by
  rw [inter_bracket_eq]
  calc ∑ i : Fin (n + 1), (spin (σ i) - spin (σ' i)) * (spin (τ i) - spin (τ' i))
      ≤ ∑ _i : Fin (n + 1), (4 : ℝ) :=
        Finset.sum_le_sum fun i _ => term_le_four _ _ _ _
    _ = 4 * ((n : ℝ) + 1) := by
        simp [Finset.sum_const, Finset.card_univ]
        ring

/-- **THE MATCHING UPPER BOUND**, so `4·β·(n+1)` is the diameter and not a lower estimate. -/
theorem hasDiameterLE_transferSym {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    HasDiameterLE (transferSym β n) (4 * β * ((n : ℝ) + 1)) := by
  intro σ σ' τ τ'
  rw [log_crossRatio_transferSym]
  have := inter_bracket_le (n := n) σ σ' τ τ'
  nlinarith [this, hβ]

/-! ## 5. So no `D` bounds it at every width -/

/-- **NOT BOUNDED BY `D` ONCE THE STRIP IS WIDE ENOUGH.** -/
theorem not_hasDiameterLE {β D : ℝ} {n : ℕ} (h : D < 4 * β * ((n : ℝ) + 1)) :
    ¬ HasDiameterLE (transferSym β n) D := by
  intro hall
  have := hall (allTrue n) (allFalse n) (allTrue n) (allFalse n)
  rw [log_crossRatio_allConst] at this
  linarith

/-- **THE PROJECTIVE DIAMETER OF THE TRANSFER MATRIX IS UNBOUNDED IN THE WIDTH**, at every positive
inverse temperature. This is the quantity a Birkhoff–Hopf argument consumes. -/
theorem diameter_unbounded {β : ℝ} (hβ : 0 < β) (D : ℝ) :
    ∃ n : ℕ, ¬ HasDiameterLE (transferSym β n) D := by
  obtain ⟨N, hN⟩ := exists_nat_gt (D / (4 * β))
  refine ⟨N, not_hasDiameterLE ?_⟩
  have h4β : 0 < 4 * β := by linarith
  rw [div_lt_iff₀ h4β] at hN
  nlinarith [hN, h4β]

end ProjectiveDiameter
