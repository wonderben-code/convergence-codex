import LovelockPerpPieces

/-!
# The scalar summand is a line, and a line is irreducible for a reason that has nothing to do with
the group

`LovelockInvariantSplitting` produced a four-way decomposition — Weyl, traceless-Ricci, scalar,
`Curv^⊥` — with every summand `act`-stable and the four mutually orthogonal.
`LovelockPerpPieces` then proved the fourth one **reducible**. This file settles the third one, in
the other direction, and is written to be very hard to over-read.

## What is proved

* **`scalPart_eq_smul`** — hoisted to `LovelockProjections`, where it belongs: `scalPart R` is
  `(scal R / n(n−1)) · constCurv n`. It was already proved, as an anonymous `have` inside
  `LovelockReduction.scalPart_eq`; `ERRATUM 174` records the duplication and this unit removes it,
  so the fact is now proved once and cited twice;
* **`scalPart_constCurv`** — every multiple of `constCurv n` is `scalPart` of something, namely of
  itself. So the scalar summand is not a *proper* subset of the line: it is the whole line;
* **`onScalarLine_iff`** — the two together: **an array is `scalPart` of something exactly when it
  is a multiple of `constCurv n`.** This is the headline. The scalar summand of the decomposition
  is exactly the line `ℝ · constCurv n`;
* `scalPart_proportional` — any two elements are proportional, with the ratio computed from the
  scalar curvatures;
* **`act_onScalarLine`** — a frame change does not merely preserve the scalar summand, it **fixes
  every element of it pointwise**, by `AlgebraicCurvature.act_constCurv` and `act_smul`. So the
  summand is a *trivial* one-dimensional subrepresentation, not merely a stable one;
* `exists_ne_zero_onScalarLine` — at `n ≥ 2` the line has a non-zero point, so the next item is not
  a theorem about nothing;
* **`scalarLine_irreducible`** — a family inside the line, closed under scalar multiples and under
  pointwise equality, containing one non-zero element, contains **every** element of the line.
  That is "no proper non-zero invariant subfamily", stated without a subspace type in the style
  `LovelockPerpPieces.perp_not_irreducible` fixed.

## Read this before reading `scalarLine_irreducible` as evidence about anything

**`scalarLine_irreducible` takes no `act`-stability hypothesis and its proof never mentions the
group.** That is not an oversight and it is not a strengthening worth boasting about: it is the
whole character of the result. A one-dimensional space has no proper non-zero subspace *at all* —
invariant or otherwise — so irreducibility here is a fact about the number 1 and not a fact about
`O(n)`. The theorem is stated in the invariant-subfamily form only so that it sits beside
`perp_not_irreducible` in the same idiom, and the hypothesis it does **not** have is the honest
signal of how little it costs.

**So this is the first irreducibility statement in the estate, and it is worth almost nothing.**
It is worth the two things it is worth: the four-summand map now reads *one reducible, one
irreducible, two unknown*, and the "irreducible" entry is pinned down rather than assumed; and the
proof technique — exhibit the summand explicitly, then count — is **exactly the technique that does
not generalise**, because the Weyl summand is not a line and cannot be enumerated this way.

**Nothing here bears on the Weyl summand.** `WALLS` §W5.0 §5b's question — whether the Weyl
summand is irreducible over `ℝ`, which is what a Schur argument would consume — is untouched, and
so is the `O(n)`-orbit-spans question that §5d and §5e both terminate at. **`KillsWeyl` at
`n ≥ 4` is untouched and the watchlist item does not move.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.


## ⚠ THE DOCSTRING BELOW SAYS THE ESTATE HAS NO SUBSPACE TYPE. IT HAS. Annotated 1 September 2026

Kept as written (`ERRATUM 94`, `ERRATUM 391`). `OnScalarLine` is *"a predicate rather than a
subspace, for the reason `LovelockReduction` §1 records: the estate has no subspace type for
four-index arrays."* **`LovelockCompleteReducibility` and `LovelockWeylSubmodule`, both 2026-08-22,
use `Submodule ℝ` on exactly this carrier.** The reason the docstring gives is no longer a reason.

**The predicate is not withdrawn.** It is used as a predicate throughout this file and restating it
as a `Submodule` would change every consumer; that is a carrier decision for the author and is not
taken here.
-/

namespace LovelockScalarLine

open AlgebraicCurvature LovelockProjections LovelockEquivariance LovelockOrthogonality Finset

variable {n : ℕ} {Q : Fin n → Fin n → ℝ}

/-! ## 1. The summand is contained in the line, and fills it -/

/-- **EVERY MULTIPLE OF `constCurv` IS ATTAINED**, by the multiple itself: `scalPart` is the
identity on the line. The scalar curvature of `lam · constCurv n` is `lam · n(n−1)`, which is
exactly the normalising factor in `scalPart`'s definition. -/
theorem scalPart_constCurv (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0) (lam : ℝ)
    (a b c d : Fin n) :
    scalPart (fun x y z w => lam * constCurv n x y z w) a b c d = lam * constCurv n a b c d := by
  have hbase : ∑ x : Fin n, ∑ y : Fin n, constCurv n y x x y = (n : ℝ) * ((n : ℝ) - 1) := by
    simpa [scal, ricci] using scal_constCurv n
  have hscal : scal (fun x y z w => lam * constCurv n x y z w)
      = lam * ((n : ℝ) * ((n : ℝ) - 1)) := by
    simp only [scal, ricci, ← Finset.mul_sum, hbase]
  rw [scalPart_eq_smul, hscal]
  field_simp

/-- **ANY TWO ELEMENTS OF THE SCALAR SUMMAND ARE PROPORTIONAL**, with the ratio read off the
scalar curvatures. -/
theorem scalPart_proportional (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0)
    (R S : Fin n → Fin n → Fin n → Fin n → ℝ) (hS : scal S ≠ 0) (a b c d : Fin n) :
    scalPart R a b c d = (scal R / scal S) * scalPart S a b c d := by
  rw [scalPart_eq_smul, scalPart_eq_smul]
  field_simp

/-! ## 2. The line, as a predicate -/

/-- **LYING ON THE LINE SPANNED BY `constCurv n`.** A predicate rather than a subspace, for the
reason `LovelockReduction` §1 records: the estate has no subspace type for four-index arrays. -/
def OnScalarLine (A : Fin n → Fin n → Fin n → Fin n → ℝ) : Prop :=
  ∃ lam : ℝ, ∀ a b c d, A a b c d = lam * constCurv n a b c d

/-- Every scalar part lies on the line — `scalPart_eq_smul`, with the coefficient hidden. -/
theorem onScalarLine_scalPart (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    OnScalarLine (scalPart R) :=
  ⟨scal R / ((n : ℝ) * ((n : ℝ) - 1)), scalPart_eq_smul R⟩

/-- And every point of the line is a scalar part — of itself. -/
theorem scalPart_surj (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0)
    {A : Fin n → Fin n → Fin n → Fin n → ℝ} (hA : OnScalarLine A) :
    ∃ R, ∀ a b c d, A a b c d = scalPart R a b c d := by
  obtain ⟨lam, hlam⟩ := hA
  refine ⟨fun x y z w => lam * constCurv n x y z w, fun a b c d => ?_⟩
  rw [hlam a b c d, scalPart_constCurv hn0 hn1]

/-- **THE SCALAR SUMMAND IS EXACTLY THE LINE `ℝ · constCurv n`.** Not contained in it — equal to
it. -/
theorem onScalarLine_iff (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0)
    (A : Fin n → Fin n → Fin n → Fin n → ℝ) :
    OnScalarLine A ↔ ∃ R, ∀ a b c d, A a b c d = scalPart R a b c d := by
  constructor
  · exact scalPart_surj hn0 hn1
  · rintro ⟨R, hR⟩
    obtain ⟨lam, hlam⟩ := onScalarLine_scalPart R
    exact ⟨lam, fun a b c d => (hR a b c d).trans (hlam a b c d)⟩

/-- The line has a non-zero point once `n ≥ 2`, so §3 is not a theorem about the empty family.
The witness is `constCurv n` itself, at the quadruple `(0, 1, 1, 0)`. -/
theorem exists_ne_zero_onScalarLine (hn : 2 ≤ n) :
    ∃ A : Fin n → Fin n → Fin n → Fin n → ℝ, OnScalarLine A ∧ ∃ a b c d, A a b c d ≠ 0 := by
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  refine ⟨constCurv n, ⟨1, fun a b c d => (one_mul _).symm⟩,
    ⟨⟨0, h0⟩, ⟨1, h1⟩, ⟨1, h1⟩, ⟨0, h0⟩, ?_⟩⟩
  simp [constCurv, delta]

/-! ## 3. The action on it is trivial, and it is irreducible for free -/

/-- **A FRAME CHANGE FIXES THE SCALAR SUMMAND POINTWISE.** Stronger than `act`-stability, which is
all `LovelockEquivariance.act_scalPart` gives: nothing moves at all. So this summand is the
**trivial** one-dimensional subrepresentation. -/
theorem act_onScalarLine (hQ : IsOrth Q) {A : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hA : OnScalarLine A) (a b c d : Fin n) :
    act Q A a b c d = A a b c d := by
  obtain ⟨lam, hlam⟩ := hA
  have hfun : A = fun x y z w => lam * constCurv n x y z w := by
    funext x y z w; exact hlam x y z w
  rw [hfun, act_smul, act_constCurv hQ]

/-- **THE SCALAR SUMMAND HAS NO PROPER NON-ZERO SUBFAMILY.** `V` is closed under scalar multiples
and under pointwise equality; it holds of one array that lies on the line and is somewhere
non-zero; then it holds of **every** point of the line.

**There is no `act`-stability hypothesis, and the proof never uses the group.** Read the header:
that absence is the result's real content. Irreducibility of a line is arithmetic, not
representation theory, and this says nothing whatever about the Weyl summand. -/
theorem scalarLine_irreducible
    {V : (Fin n → Fin n → Fin n → Fin n → ℝ) → Prop}
    (hsmul : ∀ (mu : ℝ) A, V A → V (fun a b c d => mu * A a b c d))
    (hcongr : ∀ A B : Fin n → Fin n → Fin n → Fin n → ℝ, (∀ a b c d, A a b c d = B a b c d) →
      V A → V B)
    {A : Fin n → Fin n → Fin n → Fin n → ℝ} (hV : V A) (hline : OnScalarLine A)
    (hAne : ∃ a b c d, A a b c d ≠ 0) (lam : ℝ) :
    V (fun a b c d => lam * constCurv n a b c d) := by
  obtain ⟨mu, hmu⟩ := hline
  have hmune : mu ≠ 0 := by
    intro h
    obtain ⟨a, b, c, d, hne⟩ := hAne
    exact hne (by rw [hmu a b c d, h, zero_mul])
  refine hcongr (fun a b c d => (lam / mu) * A a b c d) _ (fun a b c d => ?_)
    (hsmul (lam / mu) A hV)
  simp only [hmu]
  field_simp

end LovelockScalarLine
