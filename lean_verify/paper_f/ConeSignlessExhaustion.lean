/-
  ConeSignlessExhaustion: EVERY eigenvalue of the cone's signless Laplacian is accounted for —
  unit 79's B turned into a C

  WHY THIS FILE EXISTS. `PROOF_STRATEGY` §6's third question: *if the unit I just finished WAS a
  B, retry B→C right now, before touching the queue.* Unit 79 exhibited two families of
  eigenvectors for the cone over a `d`-regular graph and named, as the larger half of what it had
  not done, that **exhaustion is not proved — eigenvectors are exhibited and not shown to span.**
  This file proves it.

  **AND UNIT 79'S STATED REASON FOR EXHAUSTION BEING OUT OF REACH WAS WRONG, in the cheap
  direction.** It said: *independence of the rim modes is a property of `G`'s eigenvectors that
  this file does not assume and cannot supply.* That sentence is true, and it is **not what
  exhaustion needs.** Independence is what a MULTIPLICITY count needs. Exhaustion needs only that
  the two summands are `Q`-invariant and that the decomposition is direct — and both are
  elementary. **So the obstacle named was real but misidentified, and the honest record is that
  the C was one unit away and the B's own header did not see it.**

  WHAT IS PROVED.
  * **`sum_adjMatrix_mulVec`** — the total of the adjacency row sums is `d` times the total.
    **This is the one place regularity is spent**, and it is exactly what makes the zero-sum rim
    subspace `Q`-invariant: `∑ᵢ (Qx)ᵢ` over the rim picks up `∑ᵢ (A_G x)ᵢ`, which vanishes on a
    zero-sum vector only because every vertex has the same degree.
  * **`hubPart`, `rimPart`, `hubPart_add_rimPart`** — the projection onto the
    hub-plus-constant-rim plane (hub value at the hub, rim AVERAGE on the rim) and its
    complement, with `w = hubPart w + liftRim (rimPart w)` pointwise. `rimPart_sum`: the
    complement really does sum to zero. **The last was called `decomp` in the first draft, and
    `newnames_scan` reported the name taken by two Clifford-periodicity files** — unrelated
    matrix decompositions over a Clifford algebra, with no import path either way. Renamed
    rather than accepted: `decomp` was too generic a name to have reached for.
  * **`hubPart_smul`** and **`hubPart_comm` — THE WHOLE CONTENT.** The projection commutes with
    `Q`. Given that, an eigenvector's two parts are separately eigenvectors, by nothing more than
    linearity — no orthogonality, no self-adjointness, no basis.
  * **`eigenvalue_dichotomy` — THE RESULT.** For a nonzero eigenvector at `λ`: either `λ` is a
    root of the hub block's quadratic `λ² = (n + 2d + 1)λ − 2dn`, or `λ − d − 1` is an eigenvalue
    of `G`'s adjacency matrix on a NONZERO zero-sum vector. **Together with unit 79's two
    families, which prove the converse of each disjunct, the cone's spectrum is now determined
    rather than merely populated.**

  WHAT IS **NOT** CLAIMED.
  * ~~**MULTIPLICITIES ARE STILL NOT COMPUTED**, and this is where unit 79's independence remark
    belongs. The dichotomy does not say how many times each eigenvalue occurs, and that
    genuinely does need independence of `G`'s zero-sum eigenvectors.~~ **COMPUTED THE NEXT UNIT
    (82), TO WITHIN THE ONE HUB DIMENSION, AND INDEPENDENCE WAS NOT NEEDED FOR THAT EITHER.**
    `ConeMultiplicity.finrank_coneEig_bounds`: the cone's multiplicity at `λ` is the rim's
    zero-sum multiplicity at `λ − d − 1`, **or exactly one more, and never anything else**.
    `finrank_coneEig` is the exact identity behind it, by rank–nullity on the projection
    restricted to the eigenspace; `finrank_ker_le_one` bounds the hub term. **So the sentence
    above was this file's own version of unit 79's mistake, one level down**: it named a real
    ingredient (independence) and attached it to the wrong claim (the multiplicity), when what
    the multiplicity actually needs is the same commuting projection read at the level of
    eigenSPACES rather than eigenVECTORS. What survives is narrower still: **WHICH of the two
    values it is, is not decided** — the kernel is one-dimensional exactly when `λ` is a root of
    the hub quadratic and zero otherwise, and only the `≤ 1` bound is proved. The ambiguity is
    one dimension and it is LOCATED: it is the hub plane and nothing else.
  * ~~**No eigenvalue is EVALUATED.** As in unit 79, both disjuncts are stated in terms of
    inputs — a root of a quadratic, an eigenvalue of `G` — so nothing here computes a number.~~
    **FALSE IN ITS HUB HALF FROM 2026-09-16 (unit 83):** `ConeMultiplicityExact.hubRootPlus` and
    `hubRootMinus` are the roots of that quadratic in closed form, so *a root of a quadratic* is
    an input that has since been evaluated. The eigenvalue-of-`G` half stands. Original kept per
    `ERRATUM 94`.
  * **The wheel is still not instantiated**, and the cost of instantiating it is unchanged from
    unit 79's corrected estimate: a real eigenvector where the estate holds a complex character,
    and the character sum.
  * **Nothing about the cascade, the spine, or any wall.** `UNLOCK_WATCHLIST` L34948 clause (b) is
    narrowed further; clause (c) is untouched.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import ConeSignlessSpectrum

namespace ConeSignlessExhaustion

open SimpleGraph LaplacianSignless Matrix ConeSignlessSpectrum

/-! ## Regularity, in the form the decomposition needs -/

section Regular

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **REGULARITY, IN THE FORM THE DECOMPOSITION NEEDS.** The total of the adjacency matrix's
row sums is the degree times the total, because every vertex is counted once per neighbour. This
is the one place regularity is spent, and it is what makes the zero-sum rim subspace
`Q`-invariant. -/
theorem sum_adjMatrix_mulVec {d : ℕ} (hreg : ∀ i, G.degree i = d) (y : V → ℝ) :
    ∑ i, (G.adjMatrix ℝ *ᵥ y) i = (d : ℝ) * ∑ i, y i := by
  have h : ∀ i, (G.adjMatrix ℝ *ᵥ y) i = ∑ u, if G.Adj i u then y u else 0 := by
    intro i
    rw [adjMatrix_mulVec_apply, ← Finset.sum_filter]
    congr 1
    ext u
    simp [mem_neighborFinset]
  simp_rw [h]
  rw [Finset.sum_comm]
  have h2 : ∀ u : V, (∑ i, if G.Adj i u then y u else 0) = (d : ℝ) * y u := by
    intro u
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 2
    rw [show (Finset.univ.filter fun i => G.Adj i u) = G.neighborFinset u from ?_, ← degree,
      hreg u]
    ext i
    simp [mem_neighborFinset, G.adj_comm]
  simp_rw [h2]
  rw [Finset.mul_sum]

end Regular

/-! ## The projection onto the hub plane, and its complement -/

section Parts

variable {V : Type*} [Fintype V]

/-- The hub part of a vector: `w none` at the hub and the rim AVERAGE on the rim. -/
noncomputable def hubPart (w : Option V → ℝ) : Option V → ℝ
  | none => w none
  | some _ => (∑ i, w (some i)) / (Fintype.card V : ℝ)

theorem hubPart_none (w : Option V → ℝ) : hubPart w none = w none := rfl
theorem hubPart_some (w : Option V → ℝ) (i : V) :
    hubPart w (some i) = (∑ j, w (some j)) / (Fintype.card V : ℝ) := rfl

/-- The rim part: what is left after removing the hub part. It vanishes at the hub and sums to
zero on the rim. -/
noncomputable def rimPart (w : Option V → ℝ) : V → ℝ :=
  fun i => w (some i) - (∑ j, w (some j)) / (Fintype.card V : ℝ)

theorem rimPart_sum (hV : 0 < Fintype.card V) (w : Option V → ℝ) :
    ∑ i, rimPart (V := V) w i = 0 := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  simp only [rimPart, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

theorem hubPart_smul (c : ℝ) (w : Option V → ℝ) :
    hubPart (V := V) (c • w) = c • hubPart (V := V) w := by
  funext a
  cases a with
  | none => simp [hubPart_none]
  | some i =>
      simp only [hubPart_some, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      ring

theorem hubPart_add_rimPart (w : Option V → ℝ) (a : Option V) :
    w a = hubPart (V := V) w a + liftRim (rimPart (V := V) w) a := by
  cases a with
  | none => simp [hubPart_none]
  | some i => simp [hubPart_some, rimPart]

end Parts

/-! ## The projection commutes with `Q`, and the exhaustion -/

section Exhaustion

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **THE PROJECTION COMMUTES WITH `Q`.** This is the whole content of the exhaustion: both
summands are `Q`-invariant and the decomposition is direct, so an eigenvector's two parts are
separately eigenvectors. -/
theorem hubPart_comm (hV : 0 < Fintype.card V) {d : ℕ} (hreg : ∀ i, G.degree i = d)
    (x : Option V → ℝ) :
    hubPart (signlessLap (coneGraph G) *ᵥ x)
      = signlessLap (coneGraph G) *ᵥ hubPart (V := V) x := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  funext a
  cases a with
  | none =>
      rw [hubPart_none, cone_signless_mulVec_hub, cone_signless_mulVec_hub]
      simp only [hubPart_none, hubPart_some, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      field_simp
  | some i =>
      rw [hubPart_some, cone_signless_mulVec_rim, hreg i]
      have hs : ∑ j, (signlessLap (coneGraph G) *ᵥ x) (some j)
          = ((d : ℝ) + 1) * (∑ j, x (some j)) + (Fintype.card V : ℝ) * x none
            + (d : ℝ) * ∑ j, x (some j) := by
        have : ∀ j, (signlessLap (coneGraph G) *ᵥ x) (some j)
            = ((d : ℝ) + 1) * x (some j) + x none
              + (G.adjMatrix ℝ *ᵥ fun u => x (some u)) j := by
          intro j
          rw [cone_signless_mulVec_rim, hreg j, adjMatrix_mulVec_apply]
        simp_rw [this]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sum_adjMatrix_mulVec G hreg]
      rw [hs, hubPart_none, hubPart_some]
      simp only [hubPart_some, Finset.sum_const, nsmul_eq_mul]
      rw [show (G.neighborFinset i).card = G.degree i from rfl, hreg i]
      field_simp

/-- **THE RIM PART OF AN EIGENVECTOR IS AN EIGENVECTOR OF `G`'s ADJACENCY MATRIX**, at the
eigenvalue shifted down by `d + 1`. **EXTRACTED FROM `eigenvalue_dichotomy`'s PROOF 2026-09-16
(unit 82) rather than re-derived there** — `ERRATUM 348`'s rule, and the second time in this
campaign it was applied before a duplicate existed. The multiplicity count needs this as a
mapping property of a linear map, which a step buried inside a case split cannot serve. -/
theorem rimPart_eigen (hV : 0 < Fintype.card V) {d : ℕ} (hreg : ∀ i, G.degree i = d)
    {lam : ℝ} {x : Option V → ℝ}
    (hQ : signlessLap (coneGraph G) *ᵥ x = lam • x) :
    G.adjMatrix ℝ *ᵥ rimPart (V := V) x = (lam - (d : ℝ) - 1) • rimPart (V := V) x := by
  have hhub : signlessLap (coneGraph G) *ᵥ hubPart (V := V) x = lam • hubPart (V := V) x := by
    rw [← hubPart_comm G hV hreg x, hQ, hubPart_smul]
  funext i
  have hxi := congrFun hQ (some i)
  rw [cone_signless_mulVec_rim, hreg i] at hxi
  have hhi := congrFun hhub (some i)
  rw [cone_signless_mulVec_rim, hreg i] at hhi
  simp only [hubPart_none, hubPart_some, Finset.sum_const,
    show (G.neighborFinset i).card = G.degree i from rfl, hreg i, nsmul_eq_mul,
    Pi.smul_apply, smul_eq_mul] at hhi
  rw [adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  simp only [rimPart]
  have hsum : ∑ u ∈ G.neighborFinset i, (x (some u)
      - (∑ j, x (some j)) / (Fintype.card V : ℝ))
      = (∑ u ∈ G.neighborFinset i, x (some u))
        - (d : ℝ) * ((∑ j, x (some j)) / (Fintype.card V : ℝ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const,
      show (G.neighborFinset i).card = G.degree i from rfl, hreg i, nsmul_eq_mul]
  rw [hsum]
  simp only [Pi.smul_apply, smul_eq_mul] at hxi
  linarith [hxi, hhi]

/-- **THE EXHAUSTION.** Every eigenvalue of the cone's signless Laplacian is either a root of
the hub block's quadratic or `d + 1 + μ` for `μ` an eigenvalue of `G`'s adjacency matrix on a
NONZERO zero-sum vector. **Nothing about independence of `G`'s eigenvectors is used**: the two
summands are `Q`-invariant, the projection commutes with `Q`, and an eigenvector's parts are
therefore separately eigenvectors. -/
theorem eigenvalue_dichotomy [Nonempty V] {d : ℕ} (hreg : ∀ i, G.degree i = d)
    {lam : ℝ} {x : Option V → ℝ} (hx : x ≠ 0)
    (hQ : signlessLap (coneGraph G) *ᵥ x = lam • x) :
    lam ^ 2 = ((Fintype.card V : ℝ) + 2 * d + 1) * lam - 2 * d * (Fintype.card V : ℝ)
      ∨ ∃ y : V → ℝ, y ≠ 0 ∧ (∑ i, y i = 0)
          ∧ G.adjMatrix ℝ *ᵥ y = (lam - (d : ℝ) - 1) • y := by
  have hV : 0 < Fintype.card V := Fintype.card_pos
  have hn : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hhub : signlessLap (coneGraph G) *ᵥ hubPart (V := V) x = lam • hubPart (V := V) x := by
    rw [← hubPart_comm G hV hreg x, hQ, hubPart_smul]
  by_cases hr : rimPart (V := V) x = 0
  · left
    set a := x none with ha
    set b := (∑ j, x (some j)) / (Fintype.card V : ℝ) with hb
    have e1 : (Fintype.card V : ℝ) * a + (Fintype.card V : ℝ) * b = lam * a := by
      have := congrFun hhub none
      rw [cone_signless_mulVec_hub] at this
      simpa [hubPart_none, hubPart_some, Finset.sum_const, Finset.card_univ, ← hb, ← ha] using this
    have e2 : ((d : ℝ) + 1) * b + a + (d : ℝ) * b = lam * b := by
      have := congrFun hhub (some (Classical.arbitrary V))
      rw [cone_signless_mulVec_rim, hreg] at this
      simpa [hubPart_none, hubPart_some, Finset.sum_const,
        show (G.neighborFinset (Classical.arbitrary V)).card
          = G.degree (Classical.arbitrary V) from rfl, hreg, ← hb, ← ha] using this
    have hbne : b ≠ 0 := by
      intro hb0
      apply hx
      funext c
      have hane : a = 0 := by rw [hb0] at e2; simpa using e2
      have := hubPart_add_rimPart x c
      rw [this]
      cases c with
      | none => simp [hubPart_none, ← ha, hane, hr]
      | some i => simp [hubPart_some, ← hb, hb0, hr]
    have hae : a = (lam - 2 * d - 1) * b := by
      field_simp at e2 ⊢
      linarith [e2]
    rw [hae] at e1
    have : (Fintype.card V : ℝ) * ((lam - 2 * d - 1) * b) + (Fintype.card V : ℝ) * b
        = lam * ((lam - 2 * d - 1) * b) := e1
    have hq : (lam ^ 2 - ((Fintype.card V : ℝ) + 2 * d + 1) * lam
        + 2 * d * (Fintype.card V : ℝ)) * b = 0 := by linarith [this]
    have := mul_eq_zero.1 hq
    rcases this with h | h
    · linarith [h]
    · exact absurd h hbne
  · right
    exact ⟨rimPart (V := V) x, hr, rimPart_sum hV x,
      rimPart_eigen G hV hreg hQ⟩

end Exhaustion

end ConeSignlessExhaustion
