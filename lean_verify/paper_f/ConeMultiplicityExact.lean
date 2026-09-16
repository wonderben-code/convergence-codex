/-
  ConeMultiplicityExact: WHICH of the two values — the one hub dimension decided, and the two
  eigenvalues it turns on written down

  WHY THIS FILE EXISTS. `PROOF_STRATEGY` §7 item 2: *finish every unfinished chain.* Unit 82
  proved that the cone's eigenspace at `lam` has the dimension of the rim's zero-sum eigenspace
  at `lam - d - 1` **or exactly one more**, and fenced what it did not do in its own words:
  *the kernel is one-dimensional exactly when `lam` is a root of the hub quadratic and
  zero-dimensional otherwise; the `≤ 1` bound is proved and the two-way determination is not.*
  This file proves that sentence, both ways, and then spends it.

  WHAT IS PROVED.

  * **`rimPart_hubVec`** — unit 79's hub eigenvector has rim part zero, because all of its rim
    entries are `1` and the rim part subtracts their mean. One line, and it is the whole reason
    the hub eigenvector lands in the kernel of the projection rather than merely near it.
  * **`ker_ne_bot_of_hubRoot`** — if `lam` is a root of the hub quadratic then that kernel is
    non-trivial, by exhibiting unit 79's `hubVec` inside it.
  * **`hubRoot_of_ker_ne_bot`** — the converse, and the only new mathematics here. An element of
    the kernel has constant rim part; unit 82's `eq_zero_of_hubRead_eq_zero` says that constant
    cannot be zero for a non-zero element, so it can be cancelled, and cancelling it in the hub
    row's equation **is** the hub quadratic. The rim row supplies the hub entry as
    `(lam - 2d - 1)` times the constant on the way.
  * **`finrank_ker_eq_one_iff`** — the two together, against unit 82's `finrank_ker_le_one`: the
    hub term is `1` exactly when the quadratic holds, and `0` exactly when it does not.
  * **`finrank_coneEig_of_hubRoot`, `finrank_coneEig_of_not_hubRoot`, `finrank_coneEig_cases`** —
    the multiplicity itself, with no ambiguity left: the cone's eigenspace at `lam` has the
    dimension of the rim's zero-sum eigenspace at `lam - d - 1`, plus one exactly at the two hub
    roots and plus nothing anywhere else.
  * **`hubRoot_not_three_distinct`** — three reals cannot all be hub roots without two of them
    coinciding. This is the engine of the next group rather than a remark: it turns *at most two*
    into *these two*. **The one factorisation in this file is the DIFFERENCE of two instances
    of the quadratic**, `(a - b) * (a + b - S) = 0`; the quadratic itself is never factored as
    `(lam - r_plus) * (lam - r_minus)`, which is the step this route exists to avoid.
  * **`hubDisc`, `hubDisc_pos`, `hubRootPlus`, `hubRootMinus`, `hubRoot_hubRootPlus`,
    `hubRoot_hubRootMinus`, `hubRootMinus_lt_hubRootPlus`, `hubRoot_iff_eq`** — the two roots,
    **written down**, proved to satisfy the quadratic, proved distinct, and proved to be the only
    two. **This spends unit 79's `cone_disc_pos`, which until now had no consumer anywhere in
    `paper_f`** — checked by grep, not assumed. It was proved with no hypothesis at all, which is
    exactly what makes the quadratic formula applicable at every `n` and `d`.
  * **`one_le_finrank_coneEig_hubRootPlus`, `..._hubRootMinus`** — both roots really are in the
    cone's spectrum, since at a hub root the dimension is the rim's plus one.
  * **`finrank_coneEig_eq_of_ne_roots`** — and away from those two named reals the cone's
    multiplicity **is** the rim's zero-sum multiplicity, with nothing added and nothing left to
    decide.

  **A FENCE THIS FILE FALSIFIES, AND IT IS THIS CHAIN'S OWN.** Units 79, 80 and 82 each carry
  the line *No eigenvalue is EVALUATED — nothing in this file computes a number*. That was true
  of those three files and is **false once `hubRootPlus` and `hubRootMinus` exist**: two
  eigenvalues of the cone's signless Laplacian are now written in closed form, at every regular
  rim, and proved to be eigenvalues. All three headers are amended in place rather than rewritten
  (`ERRATUM 94`), and the amendment names the half that survives: the RIM half still evaluates
  nothing, because it takes `G`'s adjacency spectrum as input.

  WHAT IS **NOT** CLAIMED.

  * **THE RIM HALF EVALUATES NOTHING, AND IT IS THE BIGGER HALF.** Everything about the rim is
    relative to `finrank (rimEig G (lam - d - 1))`, which this chain has never computed for any
    `G`. Two eigenvalues out of `n + 1` are now explicit; the other `n - 1` are inputs.
  * **NO CHARACTERISTIC POLYNOMIAL, NO SPECTRAL THEOREM, NO ENUMERATION.** The two roots are
    reals that are shown to be eigenvalues; ~~nothing here says they are the TOP two, nothing
    orders the spectrum,~~ and nothing connects to Mathlib's `IsHermitian.eigenvalues` indexing —
    the fence this cluster keeps meeting, and untouched here.
    **THE STRUCK HALF WAS TRUE OF THIS FILE FOR THREE UNITS AND IS NOW FALSE OF THE ESTATE**
    (2026-09-16, unit 86, `ConeTopEigen.isGreatest_coneSpectrum`): `hubRootPlus` is proved the
    GREATEST eigenvalue of the cone's `Q`, and `finrank_coneEig_hubRootPlus` proves its
    eigenspace exactly one-dimensional, so the top is identified AND simple. What made it
    reachable was unit 85's eigenvector-form degree bound plus the observation that
    `hubDisc − (2d + 1 − n)² = 4n`; neither needed a spectral theorem. **The enumeration half of
    the sentence stands** — nothing here or there touches `IsHermitian.eigenvalues` — and so does
    *nothing orders the REST of the spectrum*: one eigenvalue is separated, and which of the
    remaining `n − 1` is second is still unknown. Original kept per `ERRATUM 94`.
  * **NOTHING ABOUT A NON-REGULAR RIM.** `hreg` is carried unchanged from unit 80; the projection
    is not `Q`-invariant without it and the chain says so four files running. **The companion
    hypothesis `hrow` — *the adjacency row sums total `d` times the total* — was carried beside
    `hreg` in sixty-one places across this chain and is GONE from all of them**, because it is
    exactly `ConeSignlessExhaustion.sum_adjMatrix_mulVec G hreg`, a theorem sitting above every
    consumer in the file that declared it. Found by reading this file's own signatures and
    removed the same day; it is an interface simplification and **not** a generalisation, since
    `hrow` never restricted anything.
  * **NOTHING ABOUT THE CASCADE, THE SPINE OR ANY WALL.** This is `L34948` clause (b)'s family,
    deepened; it is not on the spine and it moves no wall.

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import ConeMultiplicity

namespace ConeMultiplicityExact

open SimpleGraph LaplacianSignless Matrix ConeSignlessSpectrum ConeSignlessExhaustion
open ConeMultiplicity

/-! ## The hub quadratic, named -/

section Root

/-- The equation unit 79's two hub modes satisfy, given a name so that the statements below read
as sentences rather than as arithmetic. `n` is the rim's vertex count and `d` its degree. -/
def HubRoot (n d : ℕ) (lam : ℝ) : Prop :=
  lam ^ 2 = ((n : ℝ) + 2 * d + 1) * lam - 2 * d * (n : ℝ)

theorem hubRoot_def {n d : ℕ} {lam : ℝ} :
    HubRoot n d lam ↔ lam ^ 2 = ((n : ℝ) + 2 * d + 1) * lam - 2 * d * (n : ℝ) := Iff.rfl

/-- **AT MOST TWO HUB ROOTS.** Three reals cannot all satisfy the hub quadratic with all three
distinct — the standard argument, written out because it is what makes the multiplicity
statement below sharp: the `+1` occurs at two eigenvalues, not at many. -/
theorem hubRoot_not_three_distinct {n d : ℕ} {a b c : ℝ}
    (ha : HubRoot n d a) (hb : HubRoot n d b) (hc : HubRoot n d c) :
    a = b ∨ a = c ∨ b = c := by
  by_cases hab : a = b
  · exact Or.inl hab
  by_cases hac : a = c
  · exact Or.inr (Or.inl hac)
  refine Or.inr (Or.inr ?_)
  -- `HubRoot` is a definition, and `linear_combination` needs a syntactic `Eq`: unfold first,
  -- or the hypotheses are read as opaque constants and contribute nothing.
  have ha' := hubRoot_def.1 ha
  have hb' := hubRoot_def.1 hb
  have hc' := hubRoot_def.1 hc
  have h1 : (a - b) * (a + b - ((n : ℝ) + 2 * d + 1)) = 0 := by
    linear_combination ha' - hb'
  have h2 : (a - c) * (a + c - ((n : ℝ) + 2 * d + 1)) = 0 := by
    linear_combination ha' - hc'
  have hb' : a + b - ((n : ℝ) + 2 * d + 1) = 0 :=
    (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hab)
  have hc' : a + c - ((n : ℝ) + 2 * d + 1) = 0 :=
    (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hac)
  linarith

end Root

/-! ## The two hub roots, written down

This is the section that makes the multiplicity statement sharp, and it is also the section
that falsifies a fence three files of this chain have carried. Unit 79 proved the hub
quadratic's discriminant strictly positive at every `n` and `d` (`cone_disc_pos`) and then never
used it: the theorem had **no consumer anywhere in `paper_f`**, checked by grep. It has one now.
With the discriminant positive the quadratic formula applies, so the two hub roots can be
written down — and once they are written down, the chain's *no eigenvalue is EVALUATED* fence is
false in its hub half, which is said here and amended in all three headers. -/

section Roots

/-- The hub quadratic's discriminant, named so that `cone_disc_pos` can be quoted about it. -/
def hubDisc (n d : ℕ) : ℝ := ((n : ℝ) + 2 * d + 1) ^ 2 - 4 * (2 * d * (n : ℝ))

theorem hubDisc_pos (n d : ℕ) : 0 < hubDisc n d := by
  change 0 < ((n : ℝ) + 2 * d + 1) ^ 2 - 4 * (2 * d * (n : ℝ))
  exact cone_disc_pos n d

theorem sq_sqrt_hubDisc (n d : ℕ) :
    Real.sqrt (hubDisc n d) ^ 2 = ((n : ℝ) + 2 * d + 1) ^ 2 - 4 * (2 * d * (n : ℝ)) :=
  Real.sq_sqrt (hubDisc_pos n d).le

/-- The larger hub root. -/
noncomputable def hubRootPlus (n d : ℕ) : ℝ :=
  (((n : ℝ) + 2 * d + 1) + Real.sqrt (hubDisc n d)) / 2

/-- The smaller hub root. -/
noncomputable def hubRootMinus (n d : ℕ) : ℝ :=
  (((n : ℝ) + 2 * d + 1) - Real.sqrt (hubDisc n d)) / 2

theorem hubRoot_hubRootPlus (n d : ℕ) : HubRoot n d (hubRootPlus n d) := by
  rw [hubRoot_def, hubRootPlus]
  linear_combination sq_sqrt_hubDisc n d / 4

theorem hubRoot_hubRootMinus (n d : ℕ) : HubRoot n d (hubRootMinus n d) := by
  rw [hubRoot_def, hubRootMinus]
  linear_combination sq_sqrt_hubDisc n d / 4

/-- **THE TWO ROOTS ARE DISTINCT AT EVERY `n` AND `d`**, because unit 79's discriminant is
strictly positive with no hypothesis at all. -/
theorem hubRootMinus_lt_hubRootPlus (n d : ℕ) : hubRootMinus n d < hubRootPlus n d := by
  have h : 0 < Real.sqrt (hubDisc n d) := Real.sqrt_pos.2 (hubDisc_pos n d)
  rw [hubRootMinus, hubRootPlus]
  linarith

/-- **THE HUB ROOTS ARE EXACTLY TWO NAMED REALS.** The forward direction is
`hubRoot_not_three_distinct` applied to `lam` and the two roots: it returns *two of the three
coincide*, and the two roots do not, so `lam` is one of them. -/
theorem hubRoot_iff_eq (n d : ℕ) (lam : ℝ) :
    HubRoot n d lam ↔ (lam = hubRootPlus n d ∨ lam = hubRootMinus n d) := by
  constructor
  · intro h
    rcases hubRoot_not_three_distinct h (hubRoot_hubRootPlus n d)
      (hubRoot_hubRootMinus n d) with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd h1 (hubRootMinus_lt_hubRootPlus n d).ne'
  · rintro (rfl | rfl)
    · exact hubRoot_hubRootPlus n d
    · exact hubRoot_hubRootMinus n d

end Roots

/-! ## The hub eigenvector sits in the kernel of the projection

The first statement below needs neither the graph nor a decidable equality on its vertices —
only enough of a `Fintype` to average over the rim — so it gets its own section. Three files of
this chain have paid for letting a section's instances reach a theorem that does not use them,
and the cure each time was a smaller section rather than a `set_option`. -/

section Rim

variable {V : Type*} [Fintype V]

/-- Unit 79's hub eigenvector has **rim part zero**: every rim entry is `1`, so each differs
from their mean by nothing. -/
theorem rimPart_hubVec (hV : 0 < Fintype.card V) (d : ℕ) (lam : ℝ) :
    rimPart (V := V) (hubVec d lam) = 0 := by
  have hc : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  funext i
  simp only [rimPart, hubVec, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Pi.zero_apply]
  field_simp
  ring

end Rim

section Kernel

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem hubVec_mem_coneEig {d : ℕ} (hreg : ∀ i, G.degree i = d) {lam : ℝ}
    (hlam : HubRoot (Fintype.card V) d lam) :
    hubVec (V := V) d lam ∈ coneEig G lam :=
  (mem_coneEig G).2 (cone_signless_hub_eigen G hreg (hubRoot_def.1 hlam))

/-- **ONE DIRECTION.** At a hub root the kernel of the projection is non-trivial, witnessed by
unit 79's `hubVec`. -/
theorem ker_ne_bot_of_hubRoot [Nonempty V] (hV : 0 < Fintype.card V) {d : ℕ}
    (hreg : ∀ i, G.degree i = d)
    {lam : ℝ}
    (hlam : HubRoot (Fintype.card V) d lam) :
    LinearMap.ker ((rimPartL (V := V)).restrict (rimPartL_mapsTo G hV hreg lam)) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨⟨hubVec (V := V) d lam, hubVec_mem_coneEig G hreg hlam⟩, ?_, ?_⟩
  · rw [LinearMap.mem_ker]
    apply Subtype.ext
    simpa using rimPart_hubVec (V := V) hV d lam
  · intro hzero
    exact hubVec_ne_zero (V := V) d lam (Subtype.ext_iff.1 hzero)

/-- **THE CONVERSE, and the only new mathematics in this file.** A non-zero element of the kernel
has all its rim entries equal to one constant, and unit 82's `eq_zero_of_hubRead_eq_zero` says
that constant is not zero — so the rim row determines the hub entry and the hub row, divided by
the constant, **is** the hub quadratic. -/
theorem hubRoot_of_ker_ne_bot [Nonempty V] (hV : 0 < Fintype.card V) {d : ℕ}
    (hreg : ∀ i, G.degree i = d)
    (lam : ℝ)
    (h : LinearMap.ker ((rimPartL (V := V)).restrict (rimPartL_mapsTo G hV hreg lam))
          ≠ ⊥) :
    HubRoot (Fintype.card V) d lam := by
  rw [Submodule.ne_bot_iff] at h
  obtain ⟨z, hzmem, hz0⟩ := h
  have hrp : rimPart (V := V) ((z : Option V → ℝ)) = 0 := by
    have h1 : (rimPartL (V := V)) ((z : Option V → ℝ)) = 0 :=
      Subtype.ext_iff.1 (LinearMap.mem_ker.1 hzmem)
    simpa using h1
  have hall : ∀ i, (z : Option V → ℝ) (some i)
      = (z : Option V → ℝ) (some (Classical.arbitrary V)) := by
    intro i
    have h1 := congrFun hrp i
    have h2 := congrFun hrp (Classical.arbitrary V)
    simp only [rimPart, Pi.zero_apply, sub_eq_zero] at h1 h2
    rw [h1, h2]
  have hcne : (z : Option V → ℝ) (some (Classical.arbitrary V)) ≠ 0 := by
    intro hc0
    have hzz := eq_zero_of_hubRead_eq_zero G hV hreg lam ⟨z, hzmem⟩ hc0
    exact hz0 (Subtype.ext_iff.1 hzz)
  have heq := (mem_coneEig G).1 z.2
  have hnb : ∑ j ∈ G.neighborFinset (Classical.arbitrary V), (z : Option V → ℝ) (some j)
      = (d : ℝ) * (z : Option V → ℝ) (some (Classical.arbitrary V)) := by
    rw [Finset.sum_congr rfl fun j _ => hall j, Finset.sum_const,
      show (G.neighborFinset (Classical.arbitrary V)).card
        = G.degree (Classical.arbitrary V) from rfl, hreg]
    simp
  have hsum : ∑ j, (z : Option V → ℝ) (some j)
      = (Fintype.card V : ℝ) * (z : Option V → ℝ) (some (Classical.arbitrary V)) := by
    rw [Finset.sum_congr rfl fun j _ => hall j, Finset.sum_const, Finset.card_univ]
    simp
  have hrim := congrFun heq (some (Classical.arbitrary V))
  rw [cone_signless_mulVec_rim, hreg (Classical.arbitrary V), hnb] at hrim
  simp only [Pi.smul_apply, smul_eq_mul] at hrim
  have hhub := congrFun heq none
  rw [cone_signless_mulVec_hub, hsum] at hhub
  simp only [Pi.smul_apply, smul_eq_mul] at hhub
  have ha : (z : Option V → ℝ) none
      = (lam - 2 * d - 1) * (z : Option V → ℝ) (some (Classical.arbitrary V)) := by
    linarith [hrim]
  rw [ha] at hhub
  have hkey : (lam ^ 2 - ((Fintype.card V : ℝ) + 2 * d + 1) * lam
      + 2 * d * (Fintype.card V : ℝ))
        * (z : Option V → ℝ) (some (Classical.arbitrary V)) = 0 := by
    linear_combination -hhub
  have := (mul_eq_zero.1 hkey).resolve_right hcne
  rw [hubRoot_def]
  linarith

/-- **THE HUB TERM, DECIDED.** It is `1` at a hub root and `0` away from one — unit 82's `≤ 1`
with both directions of the determination it left open. -/
theorem finrank_ker_eq_one_iff [Nonempty V] (hV : 0 < Fintype.card V) {d : ℕ}
    (hreg : ∀ i, G.degree i = d)
    (lam : ℝ) :
    Module.finrank ℝ
        (LinearMap.ker ((rimPartL (V := V)).restrict (rimPartL_mapsTo G hV hreg lam))) = 1
      ↔ HubRoot (Fintype.card V) d lam := by
  constructor
  · intro h1
    refine hubRoot_of_ker_ne_bot G hV hreg lam ?_
    intro hbot
    rw [hbot] at h1
    simp at h1
  · intro hlam
    have hle := finrank_ker_le_one G hV hreg lam
    have h1 : 1 ≤ Module.finrank ℝ
        (LinearMap.ker ((rimPartL (V := V)).restrict (rimPartL_mapsTo G hV hreg lam))) :=
      Submodule.one_le_finrank_iff.2 (ker_ne_bot_of_hubRoot G hV hreg hlam)
    omega

theorem finrank_ker_eq_zero_of_not_hubRoot [Nonempty V] (hV : 0 < Fintype.card V) {d : ℕ}
    (hreg : ∀ i, G.degree i = d)
    (lam : ℝ)
    (hlam : ¬ HubRoot (Fintype.card V) d lam) :
    Module.finrank ℝ
        (LinearMap.ker ((rimPartL (V := V)).restrict (rimPartL_mapsTo G hV hreg lam)))
      = 0 := by
  have hle := finrank_ker_le_one G hV hreg lam
  have hne : Module.finrank ℝ
      (LinearMap.ker ((rimPartL (V := V)).restrict (rimPartL_mapsTo G hV hreg lam))) ≠ 1 :=
    fun hc => hlam ((finrank_ker_eq_one_iff G hV hreg lam).1 hc)
  omega

end Kernel

/-! ## The multiplicity, with nothing left over -/

section Multiplicity

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **THE MULTIPLICITY AT A HUB ROOT**: the rim's zero-sum dimension, plus exactly one. -/
theorem finrank_coneEig_of_hubRoot [Nonempty V] {d : ℕ}
    (hreg : ∀ i, G.degree i = d)
    {lam : ℝ}
    (hlam : HubRoot (Fintype.card V) d lam) :
    Module.finrank ℝ (coneEig G lam)
      = Module.finrank ℝ (rimEig G (lam - (d : ℝ) - 1)) + 1 := by
  have he := finrank_coneEig G Fintype.card_pos hreg lam
  have hk := (finrank_ker_eq_one_iff G Fintype.card_pos hreg lam).2 hlam
  omega

/-- **AND AWAY FROM ONE**: the rim's zero-sum dimension, exactly. -/
theorem finrank_coneEig_of_not_hubRoot [Nonempty V] {d : ℕ}
    (hreg : ∀ i, G.degree i = d)
    {lam : ℝ}
    (hlam : ¬ HubRoot (Fintype.card V) d lam) :
    Module.finrank ℝ (coneEig G lam)
      = Module.finrank ℝ (rimEig G (lam - (d : ℝ) - 1)) := by
  have he := finrank_coneEig G Fintype.card_pos hreg lam
  have hk := finrank_ker_eq_zero_of_not_hubRoot G Fintype.card_pos hreg lam hlam
  omega

/-- **THE STATEMENT UNIT 82 LEFT OPEN, CLOSED.** At every `lam`, the cone's eigenspace has the
rim's zero-sum eigenspace dimension at `lam - d - 1`, plus one exactly at a hub root and plus
nothing otherwise — and `hubRoot_not_three_distinct` bounds the exceptional set at two. -/
theorem finrank_coneEig_cases [Nonempty V] {d : ℕ}
    (hreg : ∀ i, G.degree i = d)
    (lam : ℝ) :
    (HubRoot (Fintype.card V) d lam ∧ Module.finrank ℝ (coneEig G lam)
        = Module.finrank ℝ (rimEig G (lam - (d : ℝ) - 1)) + 1)
      ∨ (¬ HubRoot (Fintype.card V) d lam ∧ Module.finrank ℝ (coneEig G lam)
        = Module.finrank ℝ (rimEig G (lam - (d : ℝ) - 1))) := by
  by_cases hlam : HubRoot (Fintype.card V) d lam
  · exact Or.inl ⟨hlam, finrank_coneEig_of_hubRoot G hreg hlam⟩
  · exact Or.inr ⟨hlam, finrank_coneEig_of_not_hubRoot G hreg hlam⟩

/-! ## What the two roots buy: two eigenvalues, written down -/

/-- **THE LARGER HUB ROOT IS AN EIGENVALUE OF THE CONE'S `Q`**, at every regular rim. This is
the first place in this chain where an eigenvalue is WRITTEN DOWN rather than described, and it
is why the *no eigenvalue is EVALUATED* line in units 79, 80 and 82 is amended in place. -/
theorem one_le_finrank_coneEig_hubRootPlus [Nonempty V] {d : ℕ}
    (hreg : ∀ i, G.degree i = d)
    :
    1 ≤ Module.finrank ℝ (coneEig G (hubRootPlus (Fintype.card V) d)) := by
  have h := finrank_coneEig_of_hubRoot G hreg
    (hubRoot_hubRootPlus (Fintype.card V) d)
  omega

/-- and so is the smaller one. -/
theorem one_le_finrank_coneEig_hubRootMinus [Nonempty V] {d : ℕ}
    (hreg : ∀ i, G.degree i = d)
    :
    1 ≤ Module.finrank ℝ (coneEig G (hubRootMinus (Fintype.card V) d)) := by
  have h := finrank_coneEig_of_hubRoot G hreg
    (hubRoot_hubRootMinus (Fintype.card V) d)
  omega

/-- **THE `+1` HAPPENS AT EXACTLY TWO EIGENVALUES AND NOWHERE ELSE**, and both are named. Away
from the two roots the cone's multiplicity IS the rim's zero-sum multiplicity, with nothing
added and nothing to decide. -/
theorem finrank_coneEig_eq_of_ne_roots [Nonempty V] {d : ℕ}
    (hreg : ∀ i, G.degree i = d)
    {lam : ℝ}
    (hp : lam ≠ hubRootPlus (Fintype.card V) d)
    (hm : lam ≠ hubRootMinus (Fintype.card V) d) :
    Module.finrank ℝ (coneEig G lam)
      = Module.finrank ℝ (rimEig G (lam - (d : ℝ) - 1)) := by
  refine finrank_coneEig_of_not_hubRoot G hreg ?_
  intro hlam
  rcases (hubRoot_iff_eq (Fintype.card V) d lam).1 hlam with h1 | h1
  · exact hp h1
  · exact hm h1

end Multiplicity

end ConeMultiplicityExact
