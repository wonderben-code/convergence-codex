import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Polynomial.Roots

/-!
# Elementary symmetric functions determine a multiset — leg (iii)

`UNLOCK_WATCHLIST`'s **`Tr(Aᵏ) = ∑ λᵢᵏ` … equal trace moments imply the same eigenvalue multiset**
item is *"a genuine piece of linear algebra in three legs"*. Leg (i) — `Tr(Aᵏ) = ∑ λᵢᵏ` — was
proved on 16 August (`TracePowerSpectrum`). Legs (ii) and (iii) are recorded there as **not
touched**:

> (ii) power sums determine elementary symmetric functions in characteristic zero …
> (iii) [the elementary symmetric functions determine the multiset].

**This file is leg (iii), and only leg (iii).**

> **`eq_of_esymm_eq`** — two multisets over an integral domain with the same cardinality and the
> same elementary symmetric function at every index are **equal**.

## Why it is short, and why that is not a reason it was already done

Both halves are in Mathlib and neither is joined to the other there.
`Multiset.prod_X_sub_C_coeff` says the coefficients of `∏ (X − a)` over a multiset **are** its
elementary symmetric functions up to sign, and `Polynomial.roots_multiset_prod_X_sub_C` says that
product's roots are the multiset back. So equal `esymm` gives equal coefficients, equal
coefficients give equal polynomials, and equal polynomials give equal root multisets.

**Probed by concept and counted, on 1 September 2026** (`ERRATUM 384`'s rule, `ERRATUM 42`'s):
**102** names contain `esymm`; **12** of those also mention `roots`, `multiset` or `prod_X_sub`,
and they are the definition and its `eq_1`, `esymm_neg`, the two `esymm_pair_*` cases,
`pow_smul_esymm`, the two Vieta identities `prod_X_add_C_eq_sum_esymm` and
`prod_X_sub_X_eq_sum_esymm`, the two `MvPolynomial` transports, and
`Polynomial.coeff_eq_esymm_roots_of_card`/`_of_splits`. **Not one states that `esymm` determines
the multiset**, and the direction all twelve run is *multiset → symmetric function*, never back.

**The cardinality hypothesis is not removable.** `esymm k` vanishes for `k` above the cardinality,
so `{0}` and `{0, 0}` agree at every index and differ; the hypothesis is what excludes that, and it
is exactly the hypothesis the eigenvalue consumer has for free (both multisets have `n` elements).

## What this is NOT

**It is not leg (ii)**, which is the one with the work in it: power sums determine the elementary
symmetric functions in characteristic zero. Mathlib has Newton's identities only between formal
symmetric polynomials — `MvPolynomial.psum`, `MvPolynomial.psum_eq_mul_esymm_sub_sum` and
`MvPolynomial.sum_antidiagonal_card_esymm_psum_eq_zero` — and **there is no power sum for a
multiset at all**. That absence was measured under four spellings against the pinned dump on
1 Sep 2026, not guessed from one (`ERRATUM 384`): `Multiset.psum` exactly, 0 names; `psum`
case-insensitively anywhere in a name, 112, every one of them a `finsuppSum`/`dfinsuppSum`, the
type-former `PSum`, or an `MvPolynomial` name; `powersum` case-insensitively, 0; `newton`
case-insensitively, 8, all `Polynomial.newtonMap` — Newton's *method*, not his identities. By
contrast `Multiset.esymm` does exist, which is what makes this a real gap rather than a missing
namespace: the elementary side was transported to multisets and the power side was not. So the
transport from the symmetric-polynomial identity to a multiset of scalars has to be built, and
**it is not built here**. No cost is offered (`ERRATUM 194`, `ERRATUM 246`).

**So the item does not close**, and nothing here says anything about a trace, a matrix or an
eigenvalue.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace EsymmDeterminesMultiset

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The monic polynomial whose roots are the multiset. -/
noncomputable def poly (s : Multiset R) : Polynomial R :=
  (s.map fun a => X - C a).prod

theorem natDegree_poly (s : Multiset R) : (poly s).natDegree = Multiset.card s :=
  Polynomial.natDegree_multiset_prod_X_sub_C_eq_card s

theorem roots_poly (s : Multiset R) : (poly s).roots = s :=
  Polynomial.roots_multiset_prod_X_sub_C s

/-- **EQUAL ELEMENTARY SYMMETRIC FUNCTIONS GIVE THE SAME POLYNOMIAL.** -/
theorem poly_eq_of_esymm_eq {s t : Multiset R} (hcard : Multiset.card s = Multiset.card t)
    (h : ∀ k, s.esymm k = t.esymm k) : poly s = poly t := by
  refine Polynomial.ext fun k => ?_
  by_cases hk : k ≤ Multiset.card s
  · rw [poly, poly, Multiset.prod_X_sub_C_coeff s hk,
      Multiset.prod_X_sub_C_coeff t (hcard ▸ hk), hcard, h]
  · have hs : (poly s).natDegree < k := by rw [natDegree_poly]; omega
    have ht : (poly t).natDegree < k := by rw [natDegree_poly, ← hcard]; omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hs,
      Polynomial.coeff_eq_zero_of_natDegree_lt ht]

/-- **HENCE THE MULTISETS ARE EQUAL.** -/
theorem eq_of_esymm_eq {s t : Multiset R} (hcard : Multiset.card s = Multiset.card t)
    (h : ∀ k, s.esymm k = t.esymm k) : s = t := by
  have hp := poly_eq_of_esymm_eq hcard h
  have hs := roots_poly s
  rw [hp, roots_poly t] at hs
  exact hs.symm

end EsymmDeterminesMultiset
