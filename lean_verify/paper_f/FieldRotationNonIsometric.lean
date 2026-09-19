import FieldSqrtConjugation
import FieldRotationCount
import FieldLinearClassified

/-!
# How many linear symmetries are NOT isometries? A circle's worth, and off the quarter turn

`FieldSqrtConjugation` built the first linear symmetry of the Gaussian field that is not an
isometry, and its own *What is NOT here* says what it left: *"One non-isometric element is
exhibited; the group is neither counted nor identified."* The `UNLOCK_WATCHLIST` item that has
carried the linear-symmetry clause since 5 September now records exactly two residues, and one of
them is **no index** — `FieldSymmetryHom.range_symHom_ne_top` says the isometric symmetries are a
**proper** subgroup of the linear ones and **nothing measures what is missing.** This file measures
it from below.

**THE RESTRICTIVE HYPOTHESIS THAT CAME OFF.** `FieldSqrtConjugation.rotMatrix_not_comm` is proved
at the **quarter turn only** — its statement names `FieldRotation.rotMatrix u v n 0 1`, the literal
constants `0` and `1` — because a quarter turn sends `u` to `v` and that makes the two sides of the
commutator visibly different. **`rotMatrix_green_not_comm` takes any `c` and any `s ≠ 0`**, which
is what a circle's worth needs and what the single witness did not.

## What is proved

**`rotMatrix_green_not_comm`** — at eigenvectors of `green` sitting at **distinct** eigenvalues, the
rotation `rotMatrix u v n c s` fails to commute with `green` **for every `s ≠ 0`**, at every `c`.
This is the exact mirror of `FieldRotationCount.rotMatrix_mem_symmetryMatrices`, which commutes
because there the two eigenvalues are the **same**; the two theorems together say the rotation
commutes with the propagator precisely to the extent that it stays inside one eigenspace. **It takes
no `c ^ 2 + s ^ 2 = 1`**: failing to commute is not a statement about orthogonality.

**No `conjSq_injective` — the estate already had it.** The injectivity of
`O ↦ C^{1/2} O C^{-1/2}` is what turns a circle of rotations into a circle of symmetries rather
than one symmetry named many ways, and it is `FieldLinearClassified.conjSq_injective`, with the
same statement and the same hypothesis. **This file wrote it again before finding it**, and
`newnames_scan.py` caught the name at the gate; the duplicate was deleted rather than accepted
(`ERRATUM 650`).

**`infinite_nonIsometric`** — **THE COUNT.** Wherever `green` has two orthogonal eigenvectors of
equal non-zero length at distinct eigenvalues, the linear symmetries that are **not** isometries are
**infinite** in number. The witnesses are `conjSq (rotMatrix u v n (cos t) (sin t))` for
`t ∈ (0, π)`, where `sin t ≠ 0` gives non-commutation and `cos` is injective on the closed interval.

**`infinite_linSym_quadForm`** — so the linear symmetry group itself is infinite, under the same
hypotheses.

**`infinite_nonIsometric_of_eigenvalues_ne`** — **THE COUNT AT THE HYPOTHESIS THAT IS THE WHOLE
DICHOTOMY.** `FieldSymmetryProper.exists_nonIsometric_of_eigenvalues_ne` exhibits one witness
whenever two of the propagator's eigenvalues differ, and
`FieldSymmetryProper.symmetryMatrices_eq_linSym_iff` says that condition is **exactly** when the two
symmetry groups differ at all on a non-empty graph. So: **on every graph where they differ, they
differ by infinitely much.**

**`infinite_nonIsometric_line`** — **AND IT LANDS ON A NAMED GRAPH.** The field on a line of
`k + 1 ≥ 2` sites has infinitely many linear symmetries that are not isometries, at every non-zero
mass.

**AND TWO LEMMAS WERE LIFTED OUT OF OTHER FILES' PROOFS TO GET THERE**, in
`FieldSqrtConjugation`: **`exists_orthonormal_eigenpair_of_eigenvalues_ne`**, the eigenbasis
extraction, which stood at twenty lines **twice** — once specialised to the line inside
`exists_nonIsometric_line` and once general inside
`FieldSymmetryProper.exists_nonIsometric_of_eigenvalues_ne` — and
**`exists_eigenvalues_ne_line`**, the line's index pair, which is the part that is actually about
the line. Both are now named and all four callers apply them; **no statement anywhere changed.**
Same move as `FieldSymmetryHom.isoMat` lifting a construction out of an existential, and the
consolidation unit 108 made for `zeta_pow_eq_exp`.

**WHAT THIS SETTLES AGAINST THE COUNT ALREADY ON RECORD.** `FieldLineCount.card_symmetries_line`
says the line's **isometric** symmetries number exactly `2 ^ (k + 1)`. With
`infinite_nonIsometric_line` the linear symmetries are infinite, so on the line the isometric group
is not merely proper inside the linear one — it is **finite inside an infinite group.**

## What is NOT here

**THE INDEX ITSELF IS NOT COMPUTED, AND THIS FILE DOES NOT CLAIM IT.** What the watchlist item asks
for is `Subgroup.index` of `FieldSymmetryHom.symHom`'s range inside
`FieldSymmetryInclusion.linSymGL` — a number about two `Subgroup`s of `GL V ℝ`. Everything here is
about **sets of matrices**, and the transport across that boundary is not made. On the line the two
facts assembled above do determine the index — `Subgroup.card_mul_index` with a finite subgroup of
an infinite group forces it to be `0` — and **that assembly is the next rung, not this one.** Not
attempted, no cost claimed (`ERRATUM 246`), and naming a route is not walking it (`ERRATUM 194`).

**NO LOWER BOUND BETTER THAN INFINITE.** *A circle's worth* here means an injection of an interval
into the set, and nothing more — the same reading that
`FieldRotationCount.circle_injects_symmetryMatrices` insists on for the isometric side.

**NOTHING ABOUT `d ≥ 2`.** The general theorem applies wherever its eigenpair hypothesis holds; the
only graph on which it is **discharged** is the line, exactly as in `FieldSqrtConjugation`.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. A larger
symmetry group in finite volume is a wider shadow of an axiom, not a smaller gap in it.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldRotationNonIsometric

open Matrix GraphLaplacian FieldRotation FieldSqrtConjugation
open BoxGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Off the quarter turn -/

/-- **A ROTATION BETWEEN EIGENVECTORS AT DISTINCT EIGENVALUES NEVER COMMUTES WITH THE PROPAGATOR,
AT ANY ANGLE THAT MOVES `u` AT ALL.**

Both sides are read at `u`. The rotation sends `u` to `c • u + s • v`; `green` then multiplies the
`u` part by `μ₁` and the `v` part by `μ₂`, while `green` first multiplies all of `u` by `μ₁`.
Pairing with `v` isolates the `v` components — `s * μ₂ * n` against `μ₁ * s * n` — and `s ≠ 0`,
`n ≠ 0` force `μ₁ = μ₂`.

`FieldSqrtConjugation.rotMatrix_not_comm` is the case `c = 0`, `s = 1`. **No `c ^ 2 + s ^ 2 = 1`
is needed**: this is a statement about the commutator, not about orthogonality. -/
theorem rotMatrix_green_not_comm {u v : V → ℝ} {n c s μ₁ μ₂ : ℝ} (hn : n ≠ 0)
    (huu : u ⬝ᵥ u = n) (hvv : v ⬝ᵥ v = n) (hvu : v ⬝ᵥ u = 0) (hs : s ≠ 0)
    (hu : green G m *ᵥ u = μ₁ • u) (hv : green G m *ᵥ v = μ₂ • v) (hne : μ₁ ≠ μ₂) :
    rotMatrix u v n c s * green G m ≠ green G m * rotMatrix u v n c s := by
  intro hcomm
  have hru : rotMatrix u v n c s *ᵥ u = c • u + s • v := rotMatrix_mulVec_left hn huu hvu
  have h1 : (rotMatrix u v n c s * green G m) *ᵥ u = μ₁ • (c • u + s • v) := by
    rw [← Matrix.mulVec_mulVec, hu, Matrix.mulVec_smul, hru]
  have h2 : (green G m * rotMatrix u v n c s) *ᵥ u
      = c • (μ₁ • u) + s • (μ₂ • v) := by
    rw [← Matrix.mulVec_mulVec, hru, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hu, hv]
  rw [hcomm, h2] at h1
  -- pair with `v`, which annihilates every `u` component
  have hpair := congrArg (fun w : V → ℝ => v ⬝ᵥ w) h1
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hvu, hvv, mul_zero, zero_add] at hpair
  have hsn : s * n ≠ 0 := mul_ne_zero hs hn
  refine hne (mul_right_cancel₀ hsn ?_)
  linear_combination -hpair

/-- **SO IT IS NOT ONE OF THE ISOMETRIC SYMMETRIES**, whatever else it is.
`FieldRotationCount.symmetryMatrices`' second clause is exactly the commutation this denies. -/
theorem rotMatrix_not_mem_symmetryMatrices {u v : V → ℝ} {n c s μ₁ μ₂ : ℝ} (hn : n ≠ 0)
    (huu : u ⬝ᵥ u = n) (hvv : v ⬝ᵥ v = n) (hvu : v ⬝ᵥ u = 0) (hs : s ≠ 0)
    (hu : green G m *ᵥ u = μ₁ • u) (hv : green G m *ᵥ v = μ₂ • v) (hne : μ₁ ≠ μ₂) :
    rotMatrix u v n c s ∉ FieldRotationCount.symmetryMatrices G m := fun h =>
  rotMatrix_green_not_comm hn huu hvv hvu hs hu hv hne h.2

/-! ## 2. Conjugation by the square root is injective — and the estate already had it -/

/- **`FieldLinearClassified.conjSq_injective` IS THE INJECTIVITY THIS FILE NEEDS**, with the same
statement and the same `m ≠ 0`, so nothing is declared here. It is what turns a circle of rotations
into a circle of symmetries rather than one symmetry named many ways: without it, infinitely many
`O` could name one `L`.

⚠ **AND I WROTE IT AGAIN BEFORE FINDING IT** (`ERRATUM 650`). `newnames_scan.py` flagged the name
against `FieldLinearClassified.lean` at the unit's gate and the two statements are identical —
`(hm : m ≠ 0) : Function.Injective (conjSq G m)` both times. **The duplicate was deleted, not
accepted**, because there is no hypothesis to prefer either way (`ERRATUM 457`/`ERRATUM 465`'s
rule). `FieldLinearClassified` had to be imported for the citation; it was not in this file's
import closure, which is why the name resolved cleanly in the first place. -/

/-! ## 3. The count -/

/-- **INFINITELY MANY LINEAR SYMMETRIES THAT ARE NOT ISOMETRIES**, wherever the propagator has two
orthogonal eigenvectors of equal non-zero length at **distinct** eigenvalues.

The mirror of `FieldRotationCount.infinite_symmetryMatrices_of_orthogonal_eigenpair`, which counts
the isometric symmetries at a **repeated** eigenvalue: there the interval of angles lands inside the
symmetries, here it lands outside them and inside the linear ones. -/
theorem infinite_nonIsometric (hm : m ≠ 0) {u v : V → ℝ} {n μ₁ μ₂ : ℝ} (hn : n ≠ 0)
    (huu : u ⬝ᵥ u = n) (hvv : v ⬝ᵥ v = n) (huv : u ⬝ᵥ v = 0)
    (hu : green G m *ᵥ u = μ₁ • u) (hv : green G m *ᵥ v = μ₂ • v) (hne : μ₁ ≠ μ₂) :
    {L : Matrix V V ℝ | L * green G m * Lᵀ = green G m ∧ Lᵀ * L ≠ 1}.Infinite := by
  have hvu : v ⬝ᵥ u = 0 := by rw [dotProduct_comm]; exact huv
  have hinj : Set.InjOn (fun t : ℝ => conjSq G m (rotMatrix u v n (Real.cos t) (Real.sin t)))
      (Set.Ioo 0 Real.pi) := by
    intro a ha b hb hab
    have hrot := FieldLinearClassified.conjSq_injective hm hab
    exact Real.injOn_cos ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩
      (FieldRotationCount.rotMatrix_inj hn huu hvv huv hrot).1
  refine Set.Infinite.mono ?_ ((Set.Ioo_infinite Real.pi_pos).image hinj)
  rintro L ⟨t, ht, rfl⟩
  have hO : (rotMatrix u v n (Real.cos t) (Real.sin t))ᵀ
      * rotMatrix u v n (Real.cos t) (Real.sin t) = 1 :=
    rotMatrix_transpose_mul_self hn huu hvv huv (Real.cos_sq_add_sin_sq t)
  refine ⟨conjSq_mul_green_mul_transpose hm hO, fun hc => ?_⟩
  exact rotMatrix_green_not_comm hn huu hvv hvu (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
    hu hv hne ((eq_one_iff_comm hm hO).mp hc)

/-- **SO THE LINEAR SYMMETRY GROUP IS INFINITE** under the same hypotheses — the set is a superset
of the one counted above.

⚠ **SUPERSEDED 2026-09-18, kept as written** (`ERRATUM 94`): **the conclusion needs none of these
hypotheses.** `FieldLinSymInfinite.infinite_setOf_linSym` proves it from `Nontrivial V` at a
non-zero mass, and its `_iff_nontrivial` shows that is the exact condition. The eigenpair is
earned by `infinite_nonIsometric` directly above, where the symmetries must also FAIL to be
isometries and the two distinct eigenvalues are the whole reason they do. Here they are inherited
and unused. This statement is true; it is no longer the best available. -/
theorem infinite_linSym_quadForm (hm : m ≠ 0) {u v : V → ℝ} {n μ₁ μ₂ : ℝ} (hn : n ≠ 0)
    (huu : u ⬝ᵥ u = n) (hvv : v ⬝ᵥ v = n) (huv : u ⬝ᵥ v = 0)
    (hu : green G m *ᵥ u = μ₁ • u) (hv : green G m *ᵥ v = μ₂ • v) (hne : μ₁ ≠ μ₂) :
    {L : Matrix V V ℝ | L * green G m * Lᵀ = green G m}.Infinite :=
  (infinite_nonIsometric hm hn huu hvv huv hu hv hne).mono fun _ h => h.1

/-! ## 4. On any graph with two distinct eigenvalues, and then on a named one -/

/-- **INFINITELY MANY NON-ISOMETRIC LINEAR SYMMETRIES WHEREVER THE PROPAGATOR HAS TWO DISTINCT
EIGENVALUES**, on any finite graph at any non-zero mass.

This is the count for exactly the hypothesis
`FieldSymmetryProper.exists_nonIsometric_of_eigenvalues_ne` states its single witness under, and
`FieldSymmetryProper.symmetryMatrices_eq_linSym_iff` says that hypothesis is the whole dichotomy on
a non-empty graph — so **on every graph where the two symmetry groups differ at all, they differ by
infinitely much.** -/
theorem infinite_nonIsometric_of_eigenvalues_ne (hm : m ≠ 0) {i j : V}
    (hne : (green_posDef G hm).isHermitian.eigenvalues i
      ≠ (green_posDef G hm).isHermitian.eigenvalues j) :
    {L : Matrix V V ℝ | L * green G m * Lᵀ = green G m ∧ Lᵀ * L ≠ 1}.Infinite := by
  obtain ⟨u, v, huu, hvv, huv, -, hu, hv⟩ :=
    exists_orthonormal_eigenpair_of_eigenvalues_ne hm hne
  exact infinite_nonIsometric hm one_ne_zero huu hvv huv hu hv hne

/-- **SO THE LINEAR SYMMETRY GROUP IS INFINITE** on any such graph.

⚠ **SUPERSEDED 2026-09-18, kept as written** (`ERRATUM 94`): `FieldSymmetryIndex` was this
theorem's only consumer in the estate and no longer calls it. The distinct eigenvalues buy nothing
on this side of the pair — `FieldLinSymInfinite.infinite_setOf_linSym` reaches the same set from two
vertices — and everything they do buy is in `infinite_nonIsometric_of_eigenvalues_ne` above. -/
theorem infinite_linSym_quadForm_of_eigenvalues_ne (hm : m ≠ 0) {i j : V}
    (hne : (green_posDef G hm).isHermitian.eigenvalues i
      ≠ (green_posDef G hm).isHermitian.eigenvalues j) :
    {L : Matrix V V ℝ | L * green G m * Lᵀ = green G m}.Infinite :=
  (infinite_nonIsometric_of_eigenvalues_ne hm hne).mono fun _ h => h.1

open BoxGraph in
/-- **THE FIELD ON A LINE OF AT LEAST TWO SITES HAS INFINITELY MANY LINEAR SYMMETRIES THAT ARE NOT
ISOMETRIES**, at every non-zero mass.

`FieldSqrtConjugation.exists_nonIsometric_line` gives one; this gives a circle's worth, off the same
index pair and the same eigenpair — which is why both are now named lemmas rather than twenty lines
inside its proof.

**READ THIS BESIDE `FieldLineCount.card_symmetries_line`**, which says the line's **isometric**
symmetries number exactly `2 ^ (k + 1)`. A finite group inside an infinite one: that is what the
watchlist item's *proper subgroup* amounts to on this graph. **The index is still not computed
here** — see this file's *What is NOT here*. -/
theorem infinite_nonIsometric_line {k : ℕ} (hk : 1 ≤ k) {mass : ℝ} (hmass : mass ≠ 0) :
    {L : Matrix (Site 1 (k + 1)) (Site 1 (k + 1)) ℝ |
        L * green (boxGraph 1 (k + 1)) mass * Lᵀ = green (boxGraph 1 (k + 1)) mass ∧
          Lᵀ * L ≠ 1}.Infinite := by
  obtain ⟨i, j, hne⟩ := exists_eigenvalues_ne_line hk hmass
  exact infinite_nonIsometric_of_eigenvalues_ne hmass hne

open BoxGraph in
/-- **SO THE LINE'S LINEAR SYMMETRY GROUP IS INFINITE.**

⚠ **SUPERSEDED 2026-09-18, kept as written** (`ERRATUM 94`): the line needs no eigenpair for this.
`Nontrivial (Fin (k + 1))` follows from `1 ≤ k` and `FieldLinSymInfinite.infinite_setOf_linSym`
does the rest, which is the route `FieldSymmetryIndex.index_range_symHom_eq_zero_line` now takes.
`infinite_nonIsometric_line` above is untouched and is where `hk` is really spent. -/
theorem infinite_linSym_quadForm_line {k : ℕ} (hk : 1 ≤ k) {mass : ℝ} (hmass : mass ≠ 0) :
    {L : Matrix (Site 1 (k + 1)) (Site 1 (k + 1)) ℝ |
        L * green (boxGraph 1 (k + 1)) mass * Lᵀ = green (boxGraph 1 (k + 1)) mass}.Infinite :=
  (infinite_nonIsometric_line hk hmass).mono fun _ h => h.1

end FieldRotationNonIsometric
