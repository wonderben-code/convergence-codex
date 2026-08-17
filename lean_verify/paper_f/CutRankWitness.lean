import CutRank

/-!
# The rank certificate is sharp, and it fires on a cut nothing else in the estate can see

`CutRank.not_strict_of_rank_lt` says a rank-deficient cut is not strict, on any graph with a mirror
reflection. Its header says the converse fails — that full rank is *necessary* and not *sufficient*
— and says it from the shape of the proof. **That is an assertion until a graph makes it one.**

> **`rank_full_not_strict_crossGraph`** — on `IndefiniteCoupling.crossGraph` the cut has **full
> rank** on the half and the reflected form is **not strict**. The converse of the certificate is
> false, and here is the witness.

`IndefiniteCoupling` built that graph for exactly this kind of duty: it is the estate's only graph
whose coupling is indefinite, and it exists because *"a conditional theorem whose hypothesis nothing
satisfies proves nothing"*. The same standard applies to a caveat.

## And the certificate fires, on a cut with no block structure

`GreenLargeMass.not_isCrossBlock_stepGraph` proves `stepGraph`'s cut is **not** in blocks, so
`CrossBlockStructure.strict_iff_cut_perfect` cannot be stated there. The cut is not diagonal either
— site `0` is joined to site `1`'s mirror — so `HalfBlockStructure.not_strict_of_untouched` does not
apply. **`rank_lt_stepGraph`** says the cut is nevertheless rank-deficient, because site `2` meets
it nowhere, and `CutRank.not_strict_of_isolated` fires.

**The conclusion it reaches is NOT new and this file does not claim it is.**
`StepGraphSmallMass.stepGraph_not_reflectionPositive` already refutes reflection positivity there,
and non-strictness is two lines from that. What is new is the **rank**, which no file states, and
the observation that the certificate reaches the conclusion from a *decidable combinatorial*
hypothesis where the existing route needs a Green's-function computation spread over two files. The
agreement is recorded as an `example`, not as a theorem, because the theorem already exists.

**No published tag moves**, `OS4` does not move, and no spectral gap is claimed.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CutRankWitness

open SimpleGraph GraphReflection GraphMirrorReflection CrossFormMatrix CrossBlockStructure
open CrossPosSemidef NullSpaceDimension ReachKernelDimension CutRank

/-! ## 1. `stepGraph`: an isolated site on a cut with no block structure -/

open GreenLargeMass in
/-- **SITE `2` OF THE HALF MEETS THE CUT NOWHERE.** Decidable, and decided. -/
theorem isolated_two : ∀ q ∈ Hs, ¬ stepGraph.Adj q (sigma6 2) := by decide

open GreenLargeMass in
/-- **AND SO THE CUT IS RANK-DEFICIENT THERE.** The first rank statement about this graph. -/
theorem rank_lt_stepGraph :
    Module.finrank ℝ (LinearMap.range (cutRows stepGraph sigma6 Hs)) < Hs.card :=
  rank_lt_of_isolated (Mir := (∅ : Finset (Fin 6))) isMirrorHalf_Hs isRefl_sigma6
    (by decide : (2 : Fin 6) ∈ Hs) isolated_two

open GreenLargeMass in
/-- **THE CERTIFICATE FIRES.** `stepGraph` is not strict on `Hs`, from a rank alone.

**The conclusion is the estate's already** — `StepGraphSmallMass.stepGraph_not_reflectionPositive`
gives it in two lines, and this is an `example` rather than a theorem for that reason. What the
certificate changes is the *hypothesis*: a decidable statement about which sites meet the cut, in
place of a Green's-function computation. -/
example {m : ℝ} (hm : m ≠ 0) :
    ¬ (∀ c : Fin 6 → ℝ, c ≠ 0 → (∀ p, p ∉ Hs → p ∉ (∅ : Finset (Fin 6)) → c p = 0) →
        0 < GraphReflection.reflectedForm stepGraph m sigma6 c) :=
  not_strict_of_isolated (m := m) isMirrorHalf_Hs isRefl_sigma6 hm
    (by decide : (2 : Fin 6) ∈ Hs) isolated_two

/-! ## 2. `crossGraph`: full rank, and still not strict -/

open IndefiniteCoupling in
/-- The four entries of the cut matrix on `{0,1}`. Each half-site is joined to the **other**
one's mirror image and to neither its own — which is the whole of `IndefiniteCoupling`'s
construction, read off the matrix. -/
theorem cross_entries :
    crossMatrix crossGraph rho Hh 0 0 = 0 ∧ crossMatrix crossGraph rho Hh 0 1 = 1
      ∧ crossMatrix crossGraph rho Hh 1 0 = 1 ∧ crossMatrix crossGraph rho Hh 1 1 = 0 := by
  refine ⟨?_, (crossMatrix_eq_one_iff 0 1).mpr ⟨by decide, by decide, by decide⟩,
    (crossMatrix_eq_one_iff 1 0).mpr ⟨by decide, by decide, by decide⟩, ?_⟩
  · rcases crossMatrix_entries (G := crossGraph) (θ := rho) (H := Hh) 0 0 with h0 | h1
    · exact h0
    · exact absurd ((crossMatrix_eq_one_iff 0 0).mp h1).2.2 (by decide)
  · rcases crossMatrix_entries (G := crossGraph) (θ := rho) (H := Hh) 1 1 with h0 | h1
    · exact h0
    · exact absurd ((crossMatrix_eq_one_iff 1 1).mp h1).2.2 (by decide)

open IndefiniteCoupling in
/-- **THE CUT IS INVERTIBLE ON THE HALF**, so nothing is in the reach kernel. Off-diagonal ones and
a zero diagonal: the reflection sends each half-site across to the other. -/
theorem reachKer_crossGraph_eq_bot (m : ℝ) :
    reachKer crossGraph m Hh (∅ : Finset (Fin 4)) = ⊥ := by
  obtain ⟨e00, e01, e10, e11⟩ := cross_entries
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [mem_reachKer, inReachKernel_iff_rows isMirrorHalf_Hh isRefl_rho m] at hv
  obtain ⟨hsupp, hrows⟩ := hv
  have hpair : ∀ f : Fin 4 → ℝ, ∑ q ∈ Hh, f q = f 0 + f 1 :=
    fun f => Finset.sum_pair (by decide : (0 : Fin 4) ≠ 1)
  have h0 := hrows 0 (by decide)
  have h1 := hrows 1 (by decide)
  rw [hpair, e00, e01] at h0
  rw [hpair, e10, e11] at h1
  funext p
  fin_cases p
  · simpa using by linarith [h1]
  · simpa using by linarith [h0]
  · exact hsupp 2 (by decide)
  · exact hsupp 3 (by decide)

open IndefiniteCoupling in
/-- **FULL RANK.** `2` on a half of size `2`. -/
theorem rank_crossGraph (m : ℝ) :
    Module.finrank ℝ (LinearMap.range (cutRows crossGraph rho Hh)) = Hh.card := by
  have hid := finrank_reachKer_add_rank (Mir := (∅ : Finset (Fin 4))) isMirrorHalf_Hh isRefl_rho m
  rw [reachKer_crossGraph_eq_bot m, finrank_bot] at hid
  omega

open IndefiniteCoupling in
/-- **THE CONVERSE OF THE CERTIFICATE IS FALSE, AND HERE IS THE GRAPH.**

Full rank on the half, and the reflected form is still not strict — indeed not even nonnegative
(`IndefiniteCoupling.not_strict`, whose witness makes the coupling **positive**). So
`CutRank.rank_cutRows_eq_card_of_strict` cannot be upgraded to a biconditional, and
`CutRank`'s header sentence — *necessary in general, sufficient only where the estate already had
sufficiency* — is now a statement about a graph rather than about a proof. -/
theorem rank_full_not_strict_crossGraph {m : ℝ} (hm : m ≠ 0) :
    Module.finrank ℝ (LinearMap.range (cutRows crossGraph rho Hh)) = Hh.card
      ∧ ¬ (∀ c : Fin 4 → ℝ, c ≠ 0 → (∀ p, p ∉ Hh → p ∉ (∅ : Finset (Fin 4)) → c p = 0) →
          0 < GraphReflection.reflectedForm crossGraph m rho c) :=
  ⟨rank_crossGraph m, IndefiniteCoupling.not_strict hm⟩

end CutRankWitness
