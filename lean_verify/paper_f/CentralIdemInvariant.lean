import CliffordModelSplitCases
import QuaternionCenter

/-!
# Split versus simple: the central-idempotent invariant

`WALLS §W7`, item 3 of *"WHAT W7 STILL RECORDS"*, has said since 18 August:

> **No non-isomorphism is proved.** `M ⊕ M` is visibly not a matrix algebra, but these files prove
> isomorphisms, not invariants, and nothing here separates `Cl_{2k+1}(ℂ)` from a matrix algebra of
> the same dimension. `CliffordDimension.finrank_cliffordAlgebra_congr` is the standing reminder
> that dimension does not do it.

`CliffordOddLadder`'s own header says the same in its own voice: *"no non-isomorphism to
`M_{2^k}(ℂ)` of the right size is proved here — that would need an invariant"*. **This file supplies
the invariant.**

## The invariant

`OnlyTrivialCentralIdem A` — the only `e` that is central and satisfies `e * e = e` is `0` or `1`.
Three facts, and each is stated at the generality its proof has:

* **`OnlyTrivialCentralIdem.of_ringEquiv`** — it transports along any **ring** isomorphism. No
  algebra structure, no base field, no dimension.
* **`matrix_onlyTrivialCentralIdem`** — `Mₙ(α)` has it whenever `α` has it, for **any** ring `α`
  and any nonempty finite index type. Mathlib's `Matrix.center_eq_scalar_image` computes the centre
  of a matrix ring over a *non-commutative* base, which is what makes this uniform in `α`; the
  commutative-base `Matrix.center_eq_range` would not have covered `Mₙ(ℍ)`. **The non-commutative
  base is instantiated and not merely advertised** (`ERRATUM 201`):
  `onlyTrivialCentralIdem_quaternion` and `matrix2H_onlyTrivialCentralIdem`.
* **`prod_not_onlyTrivialCentralIdem`** — a product of two nontrivial rings does not have it,
  witnessed by `(1, 0)`.

So `A × B` is never a matrix ring over anything whose centre has only trivial idempotents. That is
`isEmpty_ringEquiv_matrix_of_prod`, and `isEmpty_ringEquiv_of_prod_of_trivial` is the two-sided form
both halves of this file consume.

## What is separated

**The complex odd rank.** `cliffordOdd_not_onlyTrivialCentralIdem` — for every `k`, every complex
space of dimension `2k+1` and every nondegenerate `Q` on it, `CliffordAlgebra Q` **has a central
idempotent other than `0` and `1`**. Hence `cliffordOdd_isEmpty_ringEquiv_matrix`: it is not
isomorphic, **as a ring**, to `Mₙ(D)` for any nonempty finite `n` and any ring `D` whose centre has
only trivial idempotents — `ℂ`, `ℝ`, `ℍ`, any field, any domain, any matrix ring over one.

**AN HONEST LABEL ON WHAT THAT BUYS OVER ℂ, BECAUSE THE ANSWER IS "LESS THAN IT LOOKS"**
(`ERRATUM 204` — a route or an observation is not a theorem, and is not written as one). Against
`Mₙ(ℂ)` *specifically*, a dimension count would also do it: `dim_ℂ Cl_{2k+1}(ℂ) = 2·4^k`, and
`2·4^k = n²` would make `√2` rational. **That is an observation about the complex case and is not
formalised here.** What the invariant buys over ℂ is that it is blind to the base: it rules out
`Mₙ(D)` for every `D` at once, where no dimension is available to count.

**The real mirror pairs, where dimension provably cannot.** `finrank_clifford_sigForm_comm`:
`dim_ℝ Cl(p,q;ℝ) = 2^(p+q) = dim_ℝ Cl(q,p;ℝ)` for **every** `p` and `q`. So no dimension count
separates a signature from its mirror, ever.

> **THE COUNT IN THIS PARAGRAPH WAS WRONG WHEN FIRST WRITTEN AND THE CORRECTED VERSION IS BELOW
> (`ERRATUM 331`).** It read *"Three mirror pairs have one split side … and this invariant separates
> all three"*, with a three-row table. **There are four**, and the omitted one is `(5,0)`/`(0,5)`,
> whose split side — `CliffordModelSplitCases.clifford_pos_five_split` — sits four lines from the
> one that was used, **in the same imported file**. The cause was reading that file's header table
> by eye instead of enumerating the nine ranks (`ERRATUM 58`: a number about the estate is produced
> by counting). The fourth pair is proved, and the census below is now over all nine ranks.

**FOUR mirror pairs at rank `≤ 8` have one split side and one side that is a matrix ring over a
field, and this invariant separates all four:**

| pair | split side | simple side | common `dim_ℝ` |
|------|-----------|-------------|----------------|
| `(1,0)` / `(0,1)` | `ℝ × ℝ` | `ℂ` | `2` |
| `(0,3)` / `(3,0)` | `ℍ × ℍ` | `M₂(ℂ)` | `8` |
| `(5,0)` / `(0,5)` | `M₂(ℍ) × M₂(ℍ)` | `M₄(ℂ)` | `32` |
| `(0,7)` / `(7,0)` | `M₈(ℝ) × M₈(ℝ)` | `M₈(ℂ)` | `128` |

Each is stated as a `RingEquiv` non-existence and then as the `ℝ`-algebra corollary. **Which side
splits is not a choice**: at rank `r ≡ 1 (mod 4)` it is the positive diagonal and at `r ≡ 3` the
negative one, over the ranks this estate names. That is an observed pattern in the table above and
nothing here proves it holds beyond rank `8` (`ERRATUM 204`).

## The census over the diagonals, complete at rank `≤ 8` and counted rather than eyeballed

Nine ranks, `r = 0` to `8`, each pairing `Cl(r,0;ℝ)` against `Cl(0,r;ℝ)`. **Every one is
accounted for, and eight of the nine are theorems in this file:**

* **Three are the same algebra, so there is nothing to separate.** `r = 0` is literally one form.
  `algEquiv_pos_four_neg_four`: both sides of `r = 4` are `M₂(ℍ)`. `algEquiv_pos_eight_neg_eight`:
  both sides of `r = 8k` are `M_{16^k}(ℝ)`, for every `k` — the general statement was free.
* **Four are separated by the central-idempotent invariant** — the table above.
* **One, `r = 2`, is separated by a second invariant**, because neither side splits: `M₂(ℝ)` has a
  square-zero matrix and `ℍ` is a division ring. `NoSquareZero`, `noSquareZero_of_divisionRing`,
  `matrix_not_noSquareZero`, and `isEmpty_ringEquiv_pos_two_neg_two`.
* **One is open here: `r = 6`**, `M₄(ℍ)` against `M₈(ℝ)`, both of real dimension `64`. Neither
  splits, both contain square-zero elements, so **both invariants in this file are blind to it**.
  **The route is named and not attempted, and no cost is claimed** (`ERRATUM 246`, `ERRATUM 204`):
  `IdempotentRankInvariant.orthIdem_card_le` with the quaternionic dimension step generalised from
  `M₂(ℍ)` on `ℍ²` to `Mₙ(ℍ)` on `ℍⁿ` — nothing in `four_le_finrank_range`'s proof looks at `n` —
  would cap `M₄(ℍ)` at four orthogonal idempotents against `M₈(ℝ)`'s eight. Whether that closes it
  has not been checked.

## What this does NOT do, and it is a real limitation rather than a formality

**It does not subsume `IdempotentRankInvariant`, and cannot.** That file separates `M₂(ℍ)` from
`M₄(ℝ)`, and hence `Cl(1,3;ℝ)` from `Cl(3,1;ℝ)` — the fourth mirror pair, at `dim_ℝ = 16`. **Both
of those algebras have only trivial central idempotents**, so the invariant here is blind to that
pair, and **that limitation is two theorems in this file rather than a claim about it**:
`matrix2H_onlyTrivialCentralIdem` and `matrix4R_onlyTrivialCentralIdem`. The orthogonal-idempotent
*count* is strictly finer; it costs a dimension bound proved separately for each algebra, which is
why it is not the tool for a statement quantified over every base ring. **The two invariants are
complementary and neither implies the other.**

**Nothing here computes a centre.** `CliffordCenter` and `SpinKernel` do that for `Cl(1,3;ℝ)`; this
file needs only that a central idempotent exists on one side and that none does on the other.

**Nothing here is about simplicity.** *"Not a matrix ring"* is proved; *"not simple"* is not, and no
Artin–Wedderburn statement is used or implied.

**And neither invariant here reaches rank `6`**, which is the census's one open row and is stated
above with its route rather than glossed.

## WHAT THE ADVERSARIAL REVIEW CHANGED, RECORDED BECAUSE BOTH FINDINGS WERE THE SAME MISTAKE

The first draft compiled and was wrong in a way no build catches. Two claims sat in this header as
prose that the file did not prove:

1. *"the image form is what makes `Mₙ(ℍ)` an instance"* — advertised, never instantiated. Now
   `onlyTrivialCentralIdem_quaternion` and `matrix2H_onlyTrivialCentralIdem`.
2. *"both of those algebras have only trivial central idempotents"*, the sentence carrying the
   limitation against `IdempotentRankInvariant` — an assertion about two algebras, in a file whose
   whole subject is that assertions about algebras need invariants. Now two theorems.

Both are `ERRATUM 201`: **a generalisation that is not instantiated is a claim, and a claim in a
header is not a theorem.** A third instance was added for the same reason —
`cliffordRfOdd_isEmpty_algEquiv_matrixC`, so the complex statement is visibly non-vacuous.

**A THIRD FINDING CAME AFTER THE COMMIT, FROM `PROOF_STRATEGY` §6 QUESTION 1**, and it is the
largest: the mirror-pair count was wrong. It is `ERRATUM 331`, recorded in place above, and the
answer was the same as for the first two — **count, then write the number**. The census that
replaced it covers all nine ranks and names the one it cannot reach.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CentralIdemInvariant

open scoped Quaternion
open CliffordSignatureModel

/-! ## 1. The invariant and its transport -/

/-- **THE INVARIANT.** A ring has *only trivial central idempotents* when every central `e` with
`e * e = e` is `0` or `1`. Purely ring-theoretic: no base ring, no dimension, no algebra structure
appears, which is what lets the separations below quantify over every base at once. -/
def OnlyTrivialCentralIdem (A : Type*) [Ring A] : Prop :=
  ∀ e : A, e ∈ Set.center A → e * e = e → e = 0 ∨ e = 1

/-- **THE INVARIANT PASSES ALONG ANY RING ISOMORPHISM.** Surjectivity produces the preimage,
injectivity carries centrality and idempotency back to it. `CliffordCenter.mem_center_congr` is the
`AlgEquiv` form of the centrality half; this needs the `RingEquiv` form, which is why the two lines
are here rather than a reuse. -/
theorem OnlyTrivialCentralIdem.of_ringEquiv {A B : Type*} [Ring A] [Ring B]
    (f : A ≃+* B) (h : OnlyTrivialCentralIdem A) : OnlyTrivialCentralIdem B := by
  intro e he hidem
  obtain ⟨a, rfl⟩ := f.surjective e
  have hcen : a ∈ Set.center A := by
    rw [Semigroup.mem_center_iff] at he ⊢
    intro g
    exact f.injective (by rw [map_mul, map_mul, he (f g)])
  have hid : a * a = a := f.injective (by rw [map_mul]; exact hidem)
  rcases h a hcen hid with rfl | rfl
  · exact Or.inl (map_zero f)
  · exact Or.inr (map_one f)

/-! ## 2. Who has it -/

/-- **AN IDEMPOTENT IN A COMMUTATIVE DOMAIN IS `0` OR `1`.** `e * (e - 1) = 0` and no zero
divisors. Stated without the centrality wrapper because the quaternion case below needs it in this
bare form, on the base field rather than on the algebra. -/
theorem eq_zero_or_one_of_mul_self {R : Type*} [CommRing R] [IsDomain R] {e : R}
    (h : e * e = e) : e = 0 ∨ e = 1 := by
  have h0 : e * (e - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h0 with h' | h'
  · exact Or.inl h'
  · exact Or.inr (by linear_combination h')

/-- **A COMMUTATIVE DOMAIN HAS IT.** The centrality hypothesis is free here and is kept only so the
statement is an instance of the definition. -/
theorem onlyTrivialCentralIdem_of_isDomain {R : Type*} [CommRing R] [IsDomain R] :
    OnlyTrivialCentralIdem R := fun _ _ h => eq_zero_or_one_of_mul_self h

/-- **`ℍ[ℝ]` HAS IT, AND IT IS NOT COMMUTATIVE**, which is the case the definition was written
ring-theoretically for. `QuaternionCenter.center_eq_range` says a central quaternion is real, and a
ring hom out of a field is injective, so the idempotency descends to `ℝ`. -/
theorem onlyTrivialCentralIdem_quaternion : OnlyTrivialCentralIdem ℍ[ℝ] := by
  intro e he hidem
  rw [QuaternionCenter.center_eq_range] at he
  obtain ⟨c, rfl⟩ := he
  have hc : c * c = c := (algebraMap ℝ ℍ[ℝ]).injective (by rw [map_mul]; exact hidem)
  rcases eq_zero_or_one_of_mul_self hc with rfl | rfl
  · exact Or.inl (map_zero _)
  · exact Or.inr (map_one _)

/-- **MATRIX RINGS INHERIT IT FROM THEIR BASE**, for an **arbitrary** ring of entries. A central
matrix is `Matrix.scalar n r` with `r` central in the base (`Matrix.center_eq_scalar_image`, which
does not ask the base to be commutative), `Matrix.scalar_inj` moves the idempotency down to `r`, and
the base's own trichotomy finishes.

The commutative-base `Matrix.center_eq_range` would have been enough for `Mₙ(ℂ)` and no more; the
image form is what makes `Mₙ(ℍ)` and `Mₙ(Mₘ(ℂ))` instances of the same theorem. -/
theorem matrix_onlyTrivialCentralIdem {α : Type*} [Ring α] {n : Type*} [Fintype n]
    [DecidableEq n] [Nonempty n] (hα : OnlyTrivialCentralIdem α) :
    OnlyTrivialCentralIdem (Matrix n n α) := by
  intro e he hidem
  rw [Matrix.center_eq_scalar_image] at he
  obtain ⟨r, hr, rfl⟩ := he
  have hscal : Matrix.scalar n (r * r) = Matrix.scalar n r := by
    rw [map_mul]; exact hidem
  rcases hα r hr (Matrix.scalar_inj.mp hscal) with rfl | rfl
  · exact Or.inl (map_zero (Matrix.scalar n))
  · exact Or.inr (map_one (Matrix.scalar n))

/-- **A PRODUCT OF TWO NONTRIVIAL RINGS DOES NOT HAVE IT.** `(1, 0)` is central, idempotent, and
neither `0` nor `1`. This is the whole of the split side of every separation below. -/
theorem prod_not_onlyTrivialCentralIdem {A B : Type*} [Ring A] [Ring B]
    [Nontrivial A] [Nontrivial B] : ¬ OnlyTrivialCentralIdem (A × B) := by
  intro h
  have hc : ((1 : A), (0 : B)) ∈ Set.center (A × B) := by
    rw [Semigroup.mem_center_iff]
    rintro ⟨a, b⟩
    simp
  have hi : ((1 : A), (0 : B)) * ((1 : A), (0 : B)) = ((1 : A), (0 : B)) := by
    simp
  rcases h _ hc hi with h0 | h1
  · rw [Prod.ext_iff] at h0
    exact one_ne_zero h0.1
  · rw [Prod.ext_iff] at h1
    exact zero_ne_one h1.2

/-- **`M₂(ℍ)` HAS IT** — the instance `matrix_onlyTrivialCentralIdem` was stated over an arbitrary
base ring for (`ERRATUM 201`: a generalisation is instantiated, not left standing). -/
theorem matrix2H_onlyTrivialCentralIdem :
    OnlyTrivialCentralIdem (Matrix (Fin 2) (Fin 2) ℍ[ℝ]) :=
  matrix_onlyTrivialCentralIdem onlyTrivialCentralIdem_quaternion

/-- **AND SO DOES `M₄(ℝ)`.** The two together are why this invariant **cannot** separate
`Cl(1,3;ℝ)` from `Cl(3,1;ℝ)`: `IdempotentRankInvariant` does that with the finer
orthogonal-idempotent count, and the limitation recorded in this file's header is a pair of
theorems rather than an assertion about them. -/
theorem matrix4R_onlyTrivialCentralIdem :
    OnlyTrivialCentralIdem (Matrix (Fin 4) (Fin 4) ℝ) :=
  matrix_onlyTrivialCentralIdem onlyTrivialCentralIdem_of_isDomain

/-! ## 3. The separation -/

/-- **THE SEPARATION, IN THE FORM BOTH HALVES OF THIS FILE CONSUME.** If `C₁` is isomorphic to a
product of two nontrivial rings and `C₂` to a ring with only trivial central idempotents, then `C₁`
and `C₂` are not isomorphic as rings. -/
theorem isEmpty_ringEquiv_of_prod_of_trivial {C₁ C₂ A B S : Type*} [Ring C₁] [Ring C₂]
    [Ring A] [Ring B] [Ring S] [Nontrivial A] [Nontrivial B]
    (g : C₁ ≃+* A × B) (h : C₂ ≃+* S) (hS : OnlyTrivialCentralIdem S) :
    IsEmpty (C₁ ≃+* C₂) :=
  ⟨fun f => prod_not_onlyTrivialCentralIdem
    (OnlyTrivialCentralIdem.of_ringEquiv ((h.symm.trans f.symm).trans g) hS)⟩

/-- **A SPLIT RING IS NEVER A MATRIX RING**, over any base whose centre has only trivial
idempotents and any nonempty finite index type.

**No `DecidableEq n` is asked for**, and that is not tidying: a `RingEquiv` needs only `Mul` and
`Add`, and matrix multiplication does not see decidability. `Matrix.one` does, so the *proof* takes
a `classical` instance — but the statement is then about the additive-multiplicative structure
alone, and applies at a concrete index type whatever instance the caller carries. -/
theorem isEmpty_ringEquiv_matrix_of_prod {C A B D : Type*} [Ring C] [Ring A] [Ring B] [Ring D]
    [Nontrivial A] [Nontrivial B] {n : Type*} [Fintype n] [Nonempty n]
    (g : C ≃+* A × B) (hD : OnlyTrivialCentralIdem D) :
    IsEmpty (C ≃+* Matrix n n D) := by
  classical
  exact isEmpty_ringEquiv_of_prod_of_trivial g (RingEquiv.refl _)
    (matrix_onlyTrivialCentralIdem hD)

/-! ## 4. The complex odd rank — `WALLS §W7` item 3 -/

/-- **THE ODD COMPLEX CLIFFORD ALGEBRA HAS A NON-TRIVIAL CENTRAL IDEMPOTENT.** For every `k`, every
complex space of dimension `2k+1` and every nondegenerate form on it. This is the positive content;
everything below is a consequence. -/
theorem cliffordOdd_not_onlyTrivialCentralIdem (k : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (hV : Module.finrank ℂ V = 2 * k + 1) (Q : QuadraticForm ℂ V)
    (hQ : (QuadraticMap.associated (R := ℂ) Q).SeparatingLeft) :
    ¬ OnlyTrivialCentralIdem (CliffordAlgebra Q) := by
  obtain ⟨g⟩ := CliffordOddLadder.clifford_iso_of_nondegenerate_odd k hV Q hQ
  exact fun h => prod_not_onlyTrivialCentralIdem
    (OnlyTrivialCentralIdem.of_ringEquiv g.toRingEquiv h)

/-- **AND SO IT IS NOT A MATRIX RING OVER ANYTHING SENSIBLE.** For every ring `D` whose centre has
only trivial idempotents and every nonempty finite `n`, `CliffordAlgebra Q` is not ring-isomorphic
to `Mₙ(D)`. No dimension is compared and no base field is fixed. -/
theorem cliffordOdd_isEmpty_ringEquiv_matrix (k : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (hV : Module.finrank ℂ V = 2 * k + 1) (Q : QuadraticForm ℂ V)
    (hQ : (QuadraticMap.associated (R := ℂ) Q).SeparatingLeft)
    {D : Type*} [Ring D] (hD : OnlyTrivialCentralIdem D)
    {n : Type*} [Fintype n] [Nonempty n] :
    IsEmpty (CliffordAlgebra Q ≃+* Matrix n n D) := by
  obtain ⟨g⟩ := CliffordOddLadder.clifford_iso_of_nondegenerate_odd k hV Q hQ
  exact isEmpty_ringEquiv_matrix_of_prod g.toRingEquiv hD

/-- **THE `ℂ`-ALGEBRA FORM AT THE MATRIX ALGEBRAS THE LADDER NAMES.** `Cl_{2k+1}(ℂ)` is not
isomorphic to `Mₙ(ℂ)` for **any** `n`, in particular not for the `2^k` and `2^(k+1)` a reader might
try. -/
theorem cliffordOdd_isEmpty_algEquiv_matrixC (k : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (hV : Module.finrank ℂ V = 2 * k + 1) (Q : QuadraticForm ℂ V)
    (hQ : (QuadraticMap.associated (R := ℂ) Q).SeparatingLeft)
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    IsEmpty (CliffordAlgebra Q ≃ₐ[ℂ] Matrix n n ℂ) :=
  ⟨fun φ => (cliffordOdd_isEmpty_ringEquiv_matrix k hV Q hQ
    (D := ℂ) onlyTrivialCentralIdem_of_isDomain).elim φ.toRingEquiv⟩

/-- **THE INSTANCE AT THE LADDER'S OWN FORM** (`ERRATUM 201`). `Rf (2k+1)` is the sum of `2k+1`
squares on `Fin (2k+1) → ℂ`, so the general statement above is not vacuous: for every `k` there is
a form it applies to, and `CliffordOddLadder.cliffordRfOdd` supplies the splitting directly. -/
theorem cliffordRfOdd_isEmpty_algEquiv_matrixC (k : ℕ) {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] :
    IsEmpty (CliffordAlgebra (CliffordEvenLadder.Rf (2 * k + 1)) ≃ₐ[ℂ] Matrix n n ℂ) := by
  obtain ⟨g⟩ := CliffordOddLadder.cliffordRfOdd k
  exact ⟨fun φ => (isEmpty_ringEquiv_matrix_of_prod (D := ℂ) (n := n) g.toRingEquiv
    onlyTrivialCentralIdem_of_isDomain).elim φ.toRingEquiv⟩

/-! ## 5. The real mirror pairs, where no dimension count can help -/

/-- `dim_ℝ Cl(p,q;ℝ) = 2^(p+q)`, from `CliffordDimension.finrank_cliffordAlgebra_real` and
`finrank_sigSpace`. -/
theorem finrank_clifford_sigForm (p q : ℕ) :
    Module.finrank ℝ (CliffordAlgebra (sigForm p q)) = 2 ^ (p + q) := by
  rw [CliffordDimension.finrank_cliffordAlgebra_real (sigSpace p q) (sigForm p q),
    finrank_sigSpace]

/-- **A SIGNATURE AND ITS MIRROR ALWAYS HAVE THE SAME REAL DIMENSION**, so no dimension count
separates `Cl(p,q;ℝ)` from `Cl(q,p;ℝ)` for any `p`, `q`. This is why the three separations below
need an invariant, and it is `CliffordDimension.finrank_cliffordAlgebra_congr`'s standing warning
made concrete on the family it actually bites. -/
theorem finrank_clifford_sigForm_comm (p q : ℕ) :
    Module.finrank ℝ (CliffordAlgebra (sigForm p q))
      = Module.finrank ℝ (CliffordAlgebra (sigForm q p)) := by
  rw [finrank_clifford_sigForm, finrank_clifford_sigForm, Nat.add_comm]

/-- **`Cl(1,0;ℝ) ≇ Cl(0,1;ℝ)`** — `ℝ × ℝ` against `ℂ`, both of real dimension `2`. -/
theorem isEmpty_ringEquiv_pos_one_neg_one :
    IsEmpty (CliffordAlgebra (sigForm 1 0) ≃+* CliffordAlgebra (sigForm 0 1)) := by
  obtain ⟨g⟩ := CliffordModelTable.clifford_pos_one
  obtain ⟨h⟩ := CliffordModelTable.clifford_neg_one
  exact isEmpty_ringEquiv_of_prod_of_trivial g.toRingEquiv h.toRingEquiv
    onlyTrivialCentralIdem_of_isDomain

/-- The `ℝ`-algebra form of `isEmpty_ringEquiv_pos_one_neg_one`. -/
theorem isEmpty_algEquiv_pos_one_neg_one :
    IsEmpty (CliffordAlgebra (sigForm 1 0) ≃ₐ[ℝ] CliffordAlgebra (sigForm 0 1)) :=
  ⟨fun φ => isEmpty_ringEquiv_pos_one_neg_one.elim φ.toRingEquiv⟩

/-- **`Cl(0,3;ℝ) ≇ Cl(3,0;ℝ)`** — `ℍ × ℍ` against `M₂(ℂ)`, both of real dimension `8`. -/
theorem isEmpty_ringEquiv_neg_three_pos_three :
    IsEmpty (CliffordAlgebra (sigForm 0 3) ≃+* CliffordAlgebra (sigForm 3 0)) := by
  obtain ⟨g⟩ := CliffordModelTable.clifford_neg_three
  obtain ⟨h⟩ := CliffordModelTable.clifford_pos_three
  exact isEmpty_ringEquiv_of_prod_of_trivial g.toRingEquiv h.toRingEquiv
    (matrix_onlyTrivialCentralIdem onlyTrivialCentralIdem_of_isDomain)

/-- The `ℝ`-algebra form of `isEmpty_ringEquiv_neg_three_pos_three`. -/
theorem isEmpty_algEquiv_neg_three_pos_three :
    IsEmpty (CliffordAlgebra (sigForm 0 3) ≃ₐ[ℝ] CliffordAlgebra (sigForm 3 0)) :=
  ⟨fun φ => isEmpty_ringEquiv_neg_three_pos_three.elim φ.toRingEquiv⟩

/-- **`Cl(5,0;ℝ) ≇ Cl(0,5;ℝ)`** — `M₂(ℍ) × M₂(ℍ)` against `M₄(ℂ)`, both of real dimension `32`.

**THIS PAIR WAS MISSED BY THE FIRST VERSION OF THIS FILE AND IS `ERRATUM 331`.** The header claimed
*three* such pairs; there are four at rank `≤ 8`, and the split side of the one omitted —
`CliffordModelSplitCases.clifford_pos_five_split` — sits four lines from the one that was used, in
the same imported file. The cause was reading a table by eye instead of enumerating the nine ranks
(`ERRATUM 58`). -/
theorem isEmpty_ringEquiv_pos_five_neg_five :
    IsEmpty (CliffordAlgebra (sigForm 5 0) ≃+* CliffordAlgebra (sigForm 0 5)) := by
  obtain ⟨g⟩ := CliffordModelSplitCases.clifford_pos_five_split
  obtain ⟨h⟩ := CliffordModelResidues.clifford_neg_five
  exact isEmpty_ringEquiv_of_prod_of_trivial g.toRingEquiv h.toRingEquiv
    (matrix_onlyTrivialCentralIdem onlyTrivialCentralIdem_of_isDomain)

/-- The `ℝ`-algebra form of `isEmpty_ringEquiv_pos_five_neg_five`. -/
theorem isEmpty_algEquiv_pos_five_neg_five :
    IsEmpty (CliffordAlgebra (sigForm 5 0) ≃ₐ[ℝ] CliffordAlgebra (sigForm 0 5)) :=
  ⟨fun φ => isEmpty_ringEquiv_pos_five_neg_five.elim φ.toRingEquiv⟩

/-- **`Cl(0,7;ℝ) ≇ Cl(7,0;ℝ)`** — `M₈(ℝ) × M₈(ℝ)` against `M₈(ℂ)`, both of real dimension `128`.
The split side is `CliffordModelSplitCases.clifford_neg_seven_split`, which is exactly the shape
this invariant consumes. -/
theorem isEmpty_ringEquiv_neg_seven_pos_seven :
    IsEmpty (CliffordAlgebra (sigForm 0 7) ≃+* CliffordAlgebra (sigForm 7 0)) := by
  obtain ⟨g⟩ := CliffordModelSplitCases.clifford_neg_seven_split
  obtain ⟨h⟩ := CliffordModelResidues.clifford_pos_seven
  exact isEmpty_ringEquiv_of_prod_of_trivial g.toRingEquiv h.toRingEquiv
    (matrix_onlyTrivialCentralIdem onlyTrivialCentralIdem_of_isDomain)

/-- The `ℝ`-algebra form of `isEmpty_ringEquiv_neg_seven_pos_seven`. -/
theorem isEmpty_algEquiv_neg_seven_pos_seven :
    IsEmpty (CliffordAlgebra (sigForm 0 7) ≃ₐ[ℝ] CliffordAlgebra (sigForm 7 0)) :=
  ⟨fun φ => isEmpty_ringEquiv_neg_seven_pos_seven.elim φ.toRingEquiv⟩

/-! ## 6. One mirror pair the centre cannot reach, and a second invariant that can -/

/-- **A SECOND INVARIANT**, for the pair where neither side splits. A ring *has no square-zero
element* when `a * a = 0` forces `a = 0`. Like the first, it is purely ring-theoretic. -/
def NoSquareZero (A : Type*) [Ring A] : Prop := ∀ a : A, a * a = 0 → a = 0

/-- **IT PASSES ALONG ANY RING ISOMORPHISM**, by the same two lines as the first invariant. -/
theorem NoSquareZero.of_ringEquiv {A B : Type*} [Ring A] [Ring B]
    (f : A ≃+* B) (h : NoSquareZero A) : NoSquareZero B := by
  intro b hb
  obtain ⟨a, rfl⟩ := f.surjective b
  have : a * a = 0 := f.injective (by rw [map_mul, hb, map_zero])
  rw [h a this, map_zero]

/-- **A DIVISION RING HAS IT** — `mul_self_eq_zero`, which is `NoZeroDivisors`. -/
theorem noSquareZero_of_divisionRing {D : Type*} [DivisionRing D] : NoSquareZero D :=
  fun _ h => mul_self_eq_zero.mp h

/-- **A MATRIX RING OVER A NONTRIVIAL BASE DOES NOT**, as soon as the index type has two distinct
elements: `single i j 1` squares to zero because `j ≠ i`, and it is not itself zero. -/
theorem matrix_not_noSquareZero {α : Type*} [Ring α] [Nontrivial α] {n : Type*} [Fintype n]
    [DecidableEq n] {i j : n} (hij : i ≠ j) : ¬ NoSquareZero (Matrix n n α) := by
  intro h
  have hsq : Matrix.single i j (1 : α) * Matrix.single i j (1 : α) = 0 := by
    rw [Matrix.single_mul_single_of_ne]
    exact hij.symm
  have hne : Matrix.single i j (1 : α) ≠ 0 := by
    intro hz
    have h1 := congrFun (congrFun hz i) j
    simp at h1
  exact hne (h _ hsq)

/-- **`Cl(2,0;ℝ) ≇ Cl(0,2;ℝ)`** — `M₂(ℝ)` against `ℍ`, both of real dimension `4`, and **neither
side splits**, so the central-idempotent invariant is blind to this pair. The quaternions are a
division ring and `M₂(ℝ)` has a square-zero matrix; that is the whole separation. -/
theorem isEmpty_ringEquiv_pos_two_neg_two :
    IsEmpty (CliffordAlgebra (sigForm 2 0) ≃+* CliffordAlgebra (sigForm 0 2)) := by
  refine ⟨fun f => ?_⟩
  obtain ⟨g⟩ := CliffordModelTable.clifford_pos_two
  obtain ⟨h⟩ := CliffordModelTable.clifford_neg_two
  exact matrix_not_noSquareZero (α := ℝ) (i := 0) (j := 1) (by decide)
    (NoSquareZero.of_ringEquiv ((h.symm.toRingEquiv.trans f.symm).trans g.toRingEquiv)
      noSquareZero_of_divisionRing)

/-- The `ℝ`-algebra form of `isEmpty_ringEquiv_pos_two_neg_two`. -/
theorem isEmpty_algEquiv_pos_two_neg_two :
    IsEmpty (CliffordAlgebra (sigForm 2 0) ≃ₐ[ℝ] CliffordAlgebra (sigForm 0 2)) :=
  ⟨fun φ => isEmpty_ringEquiv_pos_two_neg_two.elim φ.toRingEquiv⟩

/-! ## 7. The three ranks where there is nothing to separate -/

/-- **`Cl(4,0;ℝ) ≅ Cl(0,4;ℝ)`** — both are `M₂(ℍ)`, so this mirror pair is not a separation problem
at all. Stated so that the census below is theorems rather than a reading of a table. -/
theorem algEquiv_pos_four_neg_four :
    Nonempty (CliffordAlgebra (sigForm 4 0) ≃ₐ[ℝ] CliffordAlgebra (sigForm 0 4)) := by
  obtain ⟨g⟩ := CliffordModelTable.clifford_pos_four
  obtain ⟨h⟩ := CliffordModelTable.clifford_neg_four
  exact ⟨g.trans h.symm⟩

/-- **`Cl(8k,0;ℝ) ≅ Cl(0,8k;ℝ)` FOR EVERY `k`** — both are `M_{16^k}(ℝ)`. The general statement is
free here, since `CliffordModelTable` proves both diagonals at every `k`. -/
theorem algEquiv_pos_eight_neg_eight (k : ℕ) :
    Nonempty (CliffordAlgebra (sigForm (8 * k) 0) ≃ₐ[ℝ] CliffordAlgebra (sigForm 0 (8 * k))) := by
  obtain ⟨g⟩ := CliffordModelTable.clifford_pos_eight_zero k
  obtain ⟨h⟩ := CliffordModelTable.clifford_neg_eight_zero k
  exact ⟨g.trans h.symm⟩

end CentralIdemInvariant
