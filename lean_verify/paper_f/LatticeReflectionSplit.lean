/-
  LatticeReflectionSplit.lean — reflection positivity is a comparison of two
  ordinary energies, and no block matrices are needed to say so.

  WHY. `UNLOCK_WATCHLIST`'s ladder for W1 is R1 block-diagonalise → R2 the
  operator inequality → R3 the cross-coupling → R4 assemble. **R2 landed
  today** (`MatrixLoewner.posDef_inv_le_inv`), and `PROOF_STRATEGY` §3 says a
  rung is not a landing: re-attempt the next leg at once. The probe written
  after R2 recorded that R1 splits into a cheap algebraic half and a real
  one. **This is the cheap half, and it is cheap only in hindsight.**

  WHAT THIS FILE PROVES:
  1. **`reflectedForm_eq`** — for EVERY coefficient vector, with no support
     condition,
       `4 · R(c)  =  Q(sym c) − Q(anti c)`,
     where `Q` is the ordinary Green-function energy, `R` the reflected one
     that `ReflectionPositive` asks to be non-negative, and `sym`/`anti` are
     the reflection-symmetric and antisymmetric parts of `c`. The only
     inputs are `LatticeReflection.green_refl`, the symmetry of `green`, and
     the fact that `refl n` is an involutive `Equiv`.
  2. **`reflectionPositive_iff_energy_le`** — hence **reflection positivity
     IS the statement that symmetrising costs at least as much energy as
     antisymmetrising**: `ReflectionPositive n m H ↔ ∀ c supported on H,
     Q(anti c) ≤ Q(sym c)`. Two quadratic forms of one matrix, compared.
  3. **`sym_eq_zero_iff`** — and the reformulation is not vacuous: on a half
     disjoint from its mirror, `sym c = 0` forces `c = 0`, so the comparison
     never degenerates into `0 ≤ 0` by accident.

  WHY THIS IS WORTH A FILE. The classical proof of R1 goes through block
  matrices: an index `Equiv` onto `H ⊕ H`, `Matrix.fromBlocks`, and a Schur
  complement. **None of that appears here.** The identity is 3
  substitutions `p ↦ refl n p` in a sum plus 1 swap of the order of
  summation. What it means is that R1's remaining content
  is exactly one step — identifying `Q(sym c)` and `Q(anti c)` with
  `cᵀ(A∓B)⁻¹c`, where R2 then applies — and that step, not the algebra, is
  where the blocks are unavoidable.

  WHAT THIS DOES NOT DO. **It is not reflection positivity and does not
  reduce its difficulty.** An equivalent statement is not a proof, and this
  one is equivalent by construction. `ReflectionPositive` remains a `def`
  that nothing proves for a general half. There is no block decomposition
  here, no `A ∓ B`, no use of R2, and no theorem about a half of a box
  larger than a singleton.

  ^ **"NOTHING PROVES FOR A GENERAL HALF" HAS BEEN FALSE SINCE 10 AUGUST
    2026 AND THE CLAUSE IS KEPT AS WRITTEN** (`ERRATUM 94`, `ERRATUM 364`).
    `StrictCriterion.reflectionPositive_strict_of_gap`, the next day, and
    `GraphReflectionPositive.reflectionPositive_of_crossOp_nonpos`, on
    26 August, both quantify over an arbitrary half of an arbitrary graph.
    This file mentions neither.
    **AND THE CLAUSE NAMED THE ROUTE THEY TOOK.** *"No block decomposition,
    no `A ∓ B`, no use of R2"* is exactly `plusOp`/`minusOp` and
    `MatrixLoewner.posDef_inv_le_inv`, which is what both are built from.
    **WHAT REMAINS TRUE, so the correction is not itself an overclaim**:
    both carry a hypothesis on the cross-coupling — the condition this
    file's own ladder calls **R3** — so nothing proves it UNCONDITIONALLY,
    and this file never said that.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import LatticeReflection

namespace LatticeReflectionSplit

open IsingFiniteVolume LatticeLaplacian LatticeReflection Finset

variable {n : ℕ} {m : ℝ}

/-! ## 1. The bilinear form everything is built from -/

/-- The Green function as a bilinear form on coefficient vectors. Every
    quantity below is this at two arguments, which is why §3 is algebra
    rather than block matrices. -/
noncomputable def bil (n : ℕ) (m : ℝ) (c d : Site n → ℝ) : ℝ :=
  ∑ p, ∑ q, c p * d q * green n m p q

/-- The ordinary Green-function energy of a coefficient vector. -/
noncomputable def energy (n : ℕ) (m : ℝ) (c : Site n → ℝ) : ℝ := bil n m c c

/-- The REFLECTED form — the one `LatticeReflection.ReflectionPositive` asks
    to be non-negative. -/
noncomputable def reflectedForm (n : ℕ) (m : ℝ) (c : Site n → ℝ) : ℝ :=
  ∑ p, ∑ q, c p * c q * green n m (refl n p) q

/-- The reflection-symmetric part (unnormalised). -/
def sym (n : ℕ) (c : Site n → ℝ) : Site n → ℝ := fun p => c p + c (refl n p)

/-- The reflection-antisymmetric part (unnormalised). -/
def anti (n : ℕ) (c : Site n → ℝ) : Site n → ℝ := fun p => c p - c (refl n p)

/-- `c` composed with the reflection. -/
def mir (n : ℕ) (c : Site n → ℝ) : Site n → ℝ := fun p => c (refl n p)

theorem reflectionPositive_iff_reflectedForm (n : ℕ) (m : ℝ) (half : Finset (Site n)) :
    ReflectionPositive n m half
      ↔ ∀ c : Site n → ℝ, (∀ p, p ∉ half → c p = 0) → 0 ≤ reflectedForm n m c :=
  Iff.rfl

/-! ## 2. Eight facts about `bil`

Bilinearity in each argument, symmetry (from the symmetry of `green`), and
invariance under reflecting BOTH arguments (from
`LatticeReflection.green_refl`). Nothing else is used.
-/

private theorem green_symm (p q : Site n) : green n m p q = green n m q p := by
  have hsym : (massive n m).IsSymm := massive_isSymm n m
  have hs : (green n m).IsSymm := by
    unfold Matrix.IsSymm green
    rw [Matrix.transpose_nonsing_inv]
    exact congrArg (fun M => M⁻¹) hsym
  exact (hs.apply p q).symm

theorem bil_add_left (c d e : Site n → ℝ) :
    bil n m (fun p => c p + d p) e = bil n m c e + bil n m d e := by
  simp only [bil, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

theorem bil_sub_left (c d e : Site n → ℝ) :
    bil n m (fun p => c p - d p) e = bil n m c e - bil n m d e := by
  simp only [bil, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

theorem bil_add_right (c d e : Site n → ℝ) :
    bil n m c (fun q => d q + e q) = bil n m c d + bil n m c e := by
  simp only [bil, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

theorem bil_sub_right (c d e : Site n → ℝ) :
    bil n m c (fun q => d q - e q) = bil n m c d - bil n m c e := by
  simp only [bil, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- **`bil` is symmetric**, because `green` is. -/
theorem bil_comm (c d : Site n → ℝ) : bil n m c d = bil n m d c := by
  rw [bil, bil, Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    rw [green_symm (m := m) y x]; ring

/-- **`bil` is invariant under reflecting both arguments**, which is
    `LatticeReflection.green_refl` and is the only geometric input. -/
theorem bil_mir_mir (c d : Site n → ℝ) : bil n m (mir n c) (mir n d) = bil n m c d := by
  have hsum : ∀ f : Site n → ℝ, ∑ p, f (refl n p) = ∑ p, f p :=
    fun f => Fintype.sum_equiv (refl n) _ _ (fun _ => rfl)
  rw [bil, bil, ← hsum (fun p => ∑ q, c p * d q * green n m p q)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← hsum (fun q => c (refl n p) * d q * green n m (refl n p) q)]
  exact Finset.sum_congr rfl fun q _ => by simp only [mir]; rw [green_refl n m p q]

/-- **The reflected form is `bil` with one argument mirrored.** -/
theorem reflectedForm_eq_bil (c : Site n → ℝ) :
    reflectedForm n m c = bil n m (mir n c) c := by
  have hsum : ∀ f : Site n → ℝ, ∑ p, f (refl n p) = ∑ p, f p :=
    fun f => Fintype.sum_equiv (refl n) _ _ (fun _ => rfl)
  rw [reflectedForm, bil, ← hsum (fun p => ∑ q, mir n c p * c q * green n m p q)]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [mir]
  rw [(refl_involutive n) p]

/-! ## 3. The identity

`4·R(c) = Q(sym c) − Q(anti c)`, for every `c`, with no support condition.
-/

private theorem energy_sym_expand (c : Site n → ℝ) :
    energy n m (sym n c) = 2 * energy n m c + 2 * reflectedForm n m c := by
  have hs : sym n c = fun p => c p + mir n c p := rfl
  rw [energy, hs, bil_add_left, bil_add_right, bil_add_right,
    bil_mir_mir, reflectedForm_eq_bil, bil_comm (m := m) c (mir n c)]
  rw [energy]
  ring

private theorem energy_anti_expand (c : Site n → ℝ) :
    energy n m (anti n c) = 2 * energy n m c - 2 * reflectedForm n m c := by
  have hs : anti n c = fun p => c p - mir n c p := rfl
  rw [energy, hs, bil_sub_left, bil_sub_right, bil_sub_right,
    bil_mir_mir, reflectedForm_eq_bil, bil_comm (m := m) c (mir n c)]
  rw [energy]
  ring

/-- **THE REFLECTED FORM IS THE DIFFERENCE OF TWO ORDINARY ENERGIES.**
    `4·R(c) = Q(sym c) − Q(anti c)`, for every `c`, with no support
    condition and no block matrices. -/
theorem reflectedForm_eq (n : ℕ) (m : ℝ) (c : Site n → ℝ) :
    4 * reflectedForm n m c = energy n m (sym n c) - energy n m (anti n c) := by
  rw [energy_sym_expand, energy_anti_expand]; ring

/-! ## 4. What reflection positivity says -/

/-- **REFLECTION POSITIVITY IS AN ENERGY COMPARISON.** For coefficients
    supported on a half: symmetrising costs at least as much as
    antisymmetrising.

    This is the whole of `ReflectionPositive`, restated with no reference to
    the reflection inside the kernel. What R1 still has to supply is the
    identification of these two energies with `cᵀ(A∓B)⁻¹c`, and that is
    where the block decomposition becomes unavoidable — see §5. -/
theorem reflectionPositive_iff_energy_le (n : ℕ) (m : ℝ) (half : Finset (Site n)) :
    ReflectionPositive n m half
      ↔ ∀ c : Site n → ℝ, (∀ p, p ∉ half → c p = 0) →
          energy n m (anti n c) ≤ energy n m (sym n c) := by
  rw [reflectionPositive_iff_reflectedForm]
  constructor
  · intro h c hc
    have h1 := h c hc
    have h4 := reflectedForm_eq n m c
    linarith
  · intro h c hc
    have h1 := h c hc
    have h4 := reflectedForm_eq n m c
    linarith

/-- **The reformulation is not vacuous.** On a half disjoint from its
    mirror, the symmetric part of a half-supported vector determines it, so
    `sym c = 0` forces `c = 0` and the comparison in §4 never degenerates
    into `0 ≤ 0` by accident. -/
theorem sym_eq_zero_iff (n : ℕ) {half : Finset (Site n)}
    (hdisj : ∀ p ∈ half, refl n p ∉ half) {c : Site n → ℝ}
    (hc : ∀ p, p ∉ half → c p = 0) : sym n c = 0 ↔ c = 0 := by
  constructor
  · intro h
    funext p
    by_cases hp : p ∈ half
    · have hmirror : c (refl n p) = 0 := hc _ (hdisj p hp)
      have hx := congrFun h p
      simp only [sym, Pi.zero_apply, hmirror, add_zero] at hx
      simpa using hx
    · simpa using hc p hp
  · rintro rfl
    funext p; simp [sym]

/-! ## 5. Review round 79 — the ways this could be hollow

**"An equivalent restatement is not progress."** Correct, and the header
says so twice. `reflectionPositive_iff_energy_le` is an `Iff` proved by
`linarith` from an algebraic identity; it cannot make anything easier,
because it is the same statement. What it does is separate R1 into two
pieces and show that **one of them needs no block machinery at all** — the
identity is four reindexings of a double sum, and the probe that costed R1
had assumed `fromBlocks` and an index `Equiv` throughout.

**"So what is actually left of R1?"** One step, and it is stated here rather
than gestured at: identify `energy n m (sym n c)` with `cᵀ(A−B)⁻¹c` and
`energy n m (anti n c)` with `cᵀ(A+B)⁻¹c`, where `A` is the half-box
operator and `−B` the cross-block. **That is where the blocks are
unavoidable**, and nothing here touches it. Once it exists, R2
(`MatrixLoewner.posDef_inv_le_inv`) finishes the ladder given R3.

**"§3 could be hiding a use of the support condition."** It is not: both
expansions and `reflectedForm_eq` quantify over ALL `c`. The support
condition appears for the first time in §4, where it is inherited from the
definition of `ReflectionPositive` and does no work in the proof. That
matters, because a reformulation that secretly used the support would be
weaker than it looks.

**"The `m = 0` case could be a gap."** It is not, and the file carries no
`m ≠ 0` hypothesis anywhere. The estate's `LatticeLaplacian.green_isSymm`
does require `m ≠ 0`; `green_symm` here does not, because
`Matrix.transpose_nonsing_inv` is unconditional and `massive_isSymm` needs
no hypothesis either — so symmetry of the inverse holds whether or not the
inverse means anything. **§3 and §4 are therefore stated for every real
`m`, including the value at which the operator is singular and Mathlib's
`⁻¹` returns junk.** The degenerate case is uninteresting, and it is not
excluded rather than being excluded silently.

**"`sym_eq_zero_iff` could be decoration."** It is the check that §4 is not
comparing two zeros. Its hypothesis — that the half is disjoint from its
mirror — is the condition a reader would assume and which
`LatticeReflection.ReflectionPositive` does NOT require, since that
definition accepts any `Finset`. So the theorem also records where the
definition is looser than the physics: on a half meeting its own mirror,
`sym c = 0` is possible for nonzero `c`, and the comparison can degenerate.
-/

end LatticeReflectionSplit
