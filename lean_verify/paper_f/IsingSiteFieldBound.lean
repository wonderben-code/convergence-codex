/-
  IsingSiteFieldBound.lean — one Ising box with an ARBITRARY field profile, and the theorem that
  says how much a field profile can ever buy.

  WHY. This estate now holds two field models proved by the same six steps: `IsingBoundaryField`'s
  `isingHB`, which puts the field on the boundary, and `IsingBulkFieldBound`'s `isingHBulk`, which
  puts it on every site. `WALLS §W3.6` states the difference between them as arithmetic — *"a
  boundary is smaller than an area"* — and the two files demonstrate it by being two files. **That
  is a restrictive hypothesis in disguise: the SHAPE of the field is fixed before anything is
  proved.** `IsingIndependentSpins` was generalised to a site-varying field `c : V → ℝ` earlier
  today for exactly this reason, and nothing consumed the generality. This file consumes it.

  WHAT IS PROVED. `isingHSite n c` carries a field `c p` at site `p`, with no assumption on `c`
  beyond what each theorem needs. Both existing models are DEFINITIONALLY instances —
  `isingHSite_const` and `isingHSite_boundary` — so this is a generalisation that is instantiated
  rather than one left hanging (`ERRATUM 201`), and the two are one theorem apart rather than two
  files apart.

  THE PART THAT IS NEW MATHEMATICS AND NOT REPACKAGING. `sum_tanh_le_card_of_support`: for **every**
  profile, the total this comparison route delivers is at most the NUMBER OF SITES CARRYING A FIELD.
  No hypothesis on `β`, on the sign of `c`, or on the geometry — the only input is
  `Real.tanh_lt_one`. So the ceiling that stopped the boundary model is not a fact about boundaries:

  * `route_insufficient_of_sublinear` — if the support grows like `O(n)`, no `m > 0` survives, for
    ANY profile, at ANY temperature. The boundary is one such profile and so is every other one.
  * `card_ge_of_route_bound` — contrapositive and sharper: a bound proportional to the AREA forces
    the field onto at least that many sites. The field must be extensive before the answer can be.

  IT DOES NOT SUBSUME `IsingBoundaryRouteCeiling.route_bound_le` AND THE FIRST DRAFT OF THIS HEADER
  SAID IT DID. That theorem bounds the boundary total by `4·n·tanh (β·h)`, which is SHARPER than
  `4·n` and is why it asks for `0 ≤ β·h`. The two are not comparable: this file is more general in
  the profile and weaker in the constant. What this file does subsume is the CONCLUSION —
  `route_insufficient_boundary` derives `IsingBoundaryRouteCeiling.route_insufficient` from the
  general statement, and derives it without that theorem's `0 ≤ β·h`, because the sign of the field
  never entered the argument. The derivation is a theorem below, not a sentence here
  (`ERRATUM 201`, `ERRATUM 204`).

  **AND THAT IS A STATEMENT ABOUT THE ROUTE, NOT ABOUT THE MODEL.** Nothing here says
  `MagnetisationBound` is false. It says the Griffiths-comparison route cannot decide it for any
  field profile whose support is sub-extensive, which is strictly more than `route_insufficient`
  said and is proved with strictly less.

  WHAT IS NOT HERE. The bound needs `0 ≤ β` and `0 ≤ c p` — Griffiths' inequalities need
  non-negative couplings and that is not a fence this file can remove. A profile with a sign change
  is outside every theorem below and no route to it is claimed (`ERRATUM 246`).

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingBulkFieldBound
import IsingBoundaryRouteCeiling

namespace IsingSiteFieldBound

open Finset Real MeasureTheory
open IsingFiniteVolume IsingBoundaryField IsingBoxInteraction IsingBulkFieldBound
open IsingGriffiths IsingGriffithsMono IsingIndependentSpins

noncomputable section

variable {n : ℕ}

/-! ## 1. The Hamiltonian, with the field's shape left free -/

/-- The Ising Hamiltonian of `IsingFiniteVolume` plus a field `c p` at site `p`. Both existing
field models are instances; see §2. -/
def isingHSite (n : ℕ) (c : Site n → ℝ) (σ : Config n) : ℝ :=
  isingH n σ - ∑ p : Site n, c p * IsingFiniteVolume.spin (σ p)

/-- The Gibbs measure of that Hamiltonian. -/
def siteMeasure (n : ℕ) (c : Site n → ℝ) (β : ℝ) : Measure (Config n) :=
  FiniteGibbs.gibbs β (isingHSite n c) Measure.count

/-! ## 2. The two existing models, as instances -/

/-- **THE BULK MODEL IS THE CONSTANT PROFILE.** -/
theorem isingHSite_const (n : ℕ) (h : ℝ) : isingHSite n (fun _ => h) = isingHBulk n h := by
  funext σ
  rw [isingHSite, isingHBulk, Finset.mul_sum]

/-- **THE BOUNDARY-FIELD MODEL IS THE INDICATOR PROFILE.** -/
theorem isingHSite_boundary (n : ℕ) (h : ℝ) :
    isingHSite n (fun p => if isBoundary p then h else 0) = isingHB n h := by
  funext σ
  rw [isingHSite, isingHB, boundaryTerm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : isBoundary p <;> simp [hp]

/-- And therefore so are the measures. -/
theorem siteMeasure_const (n : ℕ) (h β : ℝ) :
    siteMeasure n (fun _ => h) β = bulkMeasure n h β := by
  rw [siteMeasure, bulkMeasure, isingHSite_const]

theorem siteMeasure_boundary (n : ℕ) (h β : ℝ) :
    siteMeasure n (fun p => if isBoundary p then h else 0) β = isingMeasure n h β := by
  rw [siteMeasure, isingMeasure, isingHSite_boundary]

/-! ## 3. The interaction presentation -/

/-- The couplings: `β` on a bond, `β · c p` at site `p`. -/
def siteCoup (n : ℕ) (β : ℝ) (c : Site n → ℝ) : BoxIdx n → ℝ
  | Sum.inl (p, q) => if adj p q then β else 0
  | Sum.inr p => β * c p

theorem siteCoup_nonneg {β : ℝ} {c : Site n → ℝ} (hβ : 0 ≤ β) (hc : ∀ p, 0 ≤ c p) :
    ∀ i : BoxIdx n, 0 ≤ siteCoup n β c i := by
  rintro (⟨p, q⟩ | p)
  · by_cases hpq : adj p q <;> simp [siteCoup, hpq, hβ]
  · exact mul_nonneg hβ (hc p)

/-- **`−β · isingHSite` IS A SUM OF INTERACTION TERMS**, by the route
`IsingBoxInteraction.energy_eq` takes, with the site term carrying its own coefficient. -/
theorem energy_eq_site (n : ℕ) (β : ℝ) (c : Site n → ℝ) (σ : Config n) :
    ∑ i : BoxIdx n, siteCoup n β c i * ∏ v ∈ boxSet n i, IsingTransfer2D.spin (σ v)
      = -β * isingHSite n c σ := by
  rw [Fintype.sum_sum_type, isingHSite, isingH]
  have hpair : ∑ i : Site n × Site n,
      siteCoup n β c (Sum.inl i) * ∏ v ∈ boxSet n (Sum.inl i), IsingTransfer2D.spin (σ v)
      = β * ∑ p : Site n, ∑ q : Site n,
          if adj p q then IsingTransfer2D.spin (σ p) * IsingTransfer2D.spin (σ q) else 0 := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hpq : adj p q
    · rw [if_pos hpq, prod_boxSet_inl p q hpq σ]
      simp [siteCoup, hpq]
    · rw [if_neg hpq]
      simp [siteCoup, hpq]
  have hsite : ∑ p : Site n,
      siteCoup n β c (Sum.inr p) * ∏ v ∈ boxSet n (Sum.inr p), IsingTransfer2D.spin (σ v)
      = β * ∑ p : Site n, c p * IsingTransfer2D.spin (σ p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [boxSet, Finset.prod_singleton, siteCoup, mul_assoc]
  rw [hpair, hsite, ← spin_eq]
  ring

/-! ## 4. The comparison field: the same profile, with the bonds switched off -/

def siteFieldCoup (n : ℕ) (β : ℝ) (c : Site n → ℝ) : BoxIdx n → ℝ
  | Sum.inl _ => 0
  | Sum.inr p => β * c p

theorem siteFieldCoup_nonneg {β : ℝ} {c : Site n → ℝ} (hβ : 0 ≤ β) (hc : ∀ p, 0 ≤ c p) :
    ∀ i : BoxIdx n, 0 ≤ siteFieldCoup n β c i := by
  rintro (⟨p, q⟩ | p)
  · exact le_refl 0
  · exact mul_nonneg hβ (hc p)

theorem siteFieldCoup_le_siteCoup {β : ℝ} {c : Site n → ℝ} (hβ : 0 ≤ β) :
    ∀ i : BoxIdx n, siteFieldCoup n β c i ≤ siteCoup n β c i := by
  rintro (⟨p, q⟩ | p)
  · by_cases hpq : adj p q <;> simp [siteFieldCoup, siteCoup, hpq, hβ]
  · exact le_refl _

/-- The comparison model is a site field with strength `β · c p`, which is exactly the generality
`IsingIndependentSpins.IsSiteField` was widened to and which the uniform statement cannot express
for a profile that varies. -/
theorem isSiteField_site (n : ℕ) (β : ℝ) (c : Site n → ℝ) :
    IsSiteField (boxSet n) (siteFieldCoup n β c) (fun p => β * c p) := by
  intro σ
  rw [Fintype.sum_sum_type]
  have hpair : ∑ i : Site n × Site n,
      siteFieldCoup n β c (Sum.inl i)
        * ∏ v ∈ boxSet n (Sum.inl i), IsingTransfer2D.spin (σ v) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨p, q⟩ := i
    rw [siteFieldCoup, zero_mul]
  rw [hpair, zero_add]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [boxSet, Finset.prod_singleton, siteFieldCoup]

/-! ## 5. The bound, at the measure -/

theorem part_eq_partition_site (n : ℕ) (β : ℝ) (c : Site n → ℝ) :
    part (boxSet n) (siteCoup n β c) = FiniteGibbsSum.partition β (isingHSite n c) := by
  rw [part, FiniteGibbsSum.partition]
  exact Finset.sum_congr rfl fun σ _ => by rw [energy_eq_site n β c σ]

theorem num_eq_sum_site (n : ℕ) (β : ℝ) (c : Site n → ℝ) (A : Finset (Site n)) :
    num (boxSet n) (siteCoup n β c) A
      = ∑ σ : Config n, exp (-β * isingHSite n c σ) * ∏ p ∈ A, IsingTransfer2D.spin (σ p) := by
  rw [num]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [energy_eq_site n β c σ, mul_comm]

/-- **EVERY CORRELATION IS AT LEAST THE PRODUCT OF THE LOCAL `tanh`s, FOR EVERY PROFILE.**
`IsingBoxInteraction.prod_boxField_le_integral` and `IsingBulkFieldBound.tanh_pow_le_integral_bulk`
are the two instances this estate had; they are now one theorem. -/
theorem prod_tanh_le_integral_site (β : ℝ) (c : Site n → ℝ) (hβ : 0 ≤ β) (hc : ∀ p, 0 ≤ c p)
    (A : Finset (Site n)) :
    (∏ p ∈ A, tanh (β * c p))
      ≤ ∫ σ, ∏ p ∈ A, IsingTransfer2D.spin (σ p) ∂(siteMeasure n c β) := by
  have hb := prod_tanh_le_expect (boxSet n) (siteCoup n β c) (fun p => β * c p)
    (siteFieldCoup n β c) (isSiteField_site n β c) (siteFieldCoup_nonneg hβ hc)
    (siteFieldCoup_le_siteCoup hβ) A
  rw [num_eq_sum_site n β c A, part_eq_partition_site n β c] at hb
  rw [siteMeasure]
  exact FiniteGibbsSum.le_integral_gibbs_count β (isingHSite n c) _ hb

/-- The one-site case. -/
theorem tanh_le_integral_site (β : ℝ) (c : Site n → ℝ) (hβ : 0 ≤ β) (hc : ∀ p, 0 ≤ c p)
    (p₀ : Site n) :
    tanh (β * c p₀) ≤ ∫ σ, IsingTransfer2D.spin (σ p₀) ∂(siteMeasure n c β) := by
  have h₁ := prod_tanh_le_integral_site β c hβ hc {p₀}
  rw [Finset.prod_singleton] at h₁
  simpa using h₁

/-! ## 6. What a profile can buy — and this is the part that is not repackaging -/

/-- **A SUM OF `tanh`s IS AT MOST THE NUMBER OF SITES WHERE ITS ARGUMENT IS NONZERO.** Stated for an
arbitrary `f` rather than for `β · c`, because the inverse temperature plays no part: the only input
is `Real.tanh_lt_one`. No sign hypothesis, no geometry, no model.

**This does NOT subsume `IsingBoundaryRouteCeiling.route_bound_le`**, which bounds the boundary
total by `4·n·tanh (β·h)` — sharper in the constant, and that is what its `0 ≤ β·h` pays for. -/
theorem sum_tanh_le_card_of_support (f : Site n → ℝ) (S : Finset (Site n))
    (hsupp : ∀ p, p ∉ S → f p = 0) :
    ∑ p : Site n, tanh (f p) ≤ (S.card : ℝ) := by
  have h1 : ∑ p ∈ S, tanh (f p) = ∑ p : Site n, tanh (f p) := by
    refine Finset.sum_subset (Finset.subset_univ S) ?_
    intro p _ hpS
    rw [hsupp p hpS, Real.tanh_zero]
  rw [← h1]
  calc ∑ p ∈ S, tanh (f p) ≤ ∑ _p ∈ S, (1 : ℝ) :=
        Finset.sum_le_sum fun p _ => (Real.tanh_lt_one _).le
    _ = (S.card : ℝ) := by simp

/-- The form this file's own route produces. -/
theorem sum_tanh_le_card (β : ℝ) (c : Site n → ℝ) (S : Finset (Site n))
    (hsupp : ∀ p, p ∉ S → c p = 0) :
    ∑ p : Site n, tanh (β * c p) ≤ (S.card : ℝ) :=
  sum_tanh_le_card_of_support (fun p => β * c p) S fun p hp => by simp [hsupp p hp]

/-- **CONTRAPOSITIVE, AND IT IS THE SHARP FORM: A BOUND PROPORTIONAL TO THE AREA FORCES THE FIELD
ONTO AT LEAST THAT MANY SITES.** The field has to be extensive before the answer can be. -/
theorem card_ge_of_route_bound (β : ℝ) (c : Site n → ℝ) (S : Finset (Site n))
    (hsupp : ∀ p, p ∉ S → c p = 0) {m : ℝ}
    (hb : m * ((n : ℝ) * n) ≤ ∑ p : Site n, tanh (β * c p)) :
    m * ((n : ℝ) * n) ≤ (S.card : ℝ) :=
  le_trans hb (sum_tanh_le_card β c S hsupp)

/-- **AND SO NO SUB-EXTENSIVE PROFILE CAN EVER REACH THE TARGET**, at any temperature, for any
field strength — the boundary was never the point. -/
theorem route_insufficient_of_sublinear {m K : ℝ} (hm : 0 < m)
    (f : ∀ n : ℕ, Site n → ℝ) (S : ∀ n : ℕ, Finset (Site n))
    (hsupp : ∀ n : ℕ, ∀ p : Site n, p ∉ S n → f n p = 0)
    (hcard : ∀ n : ℕ, ((S n).card : ℝ) ≤ K * n) :
    ¬ ∀ n : ℕ, 0 < n → m * ((n : ℝ) * n) ≤ ∑ p : Site n, tanh (f n p) := by
  intro hall
  obtain ⟨N, hN⟩ := exists_nat_gt (K / m)
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h3 : m * (((N : ℝ) + 1) * ((N : ℝ) + 1)) ≤ K * ((N : ℝ) + 1) := by
    have h1 := hall (N + 1) (Nat.succ_pos N)
    have h2 := le_trans h1
      (sum_tanh_le_card_of_support (f (N + 1)) (S (N + 1)) (hsupp (N + 1)))
    have h3' := le_trans h2 (hcard (N + 1))
    push_cast at h3'
    exact h3'
  have h4 : m * ((N : ℝ) + 1) ≤ K := by
    by_contra hcon
    have hcon' : K < m * ((N : ℝ) + 1) := not_le.mp hcon
    nlinarith [h3, hpos, hcon']
  have h5 : K / m < (N : ℝ) + 1 := lt_trans hN (by linarith)
  rw [div_lt_iff₀ hm] at h5
  nlinarith [h4, h5]

/-- **`IsingBoundaryRouteCeiling.route_insufficient`, DERIVED**: the case `S n = ∂`, `K = 4`. Proved
rather than asserted (`ERRATUM 201`), and **without that theorem's `0 ≤ β·h`** — the sign of the
field never entered the argument, which is only visible once the profile is arbitrary. -/
theorem route_insufficient_boundary {β h m : ℝ} (hm : 0 < m) :
    ¬ ∀ n : ℕ, 0 < n → m * ((n : ℝ) * n) ≤ ∑ p : Site n, tanh (boxField n β h p) :=
  route_insufficient_of_sublinear (K := 4) hm (fun n => boxField n β h)
    (fun n => (Finset.univ : Finset (Site n)).filter fun p => isBoundary p)
    (fun n p hp => by
      have hb : ¬ (isBoundary p = true) := by simpa using hp
      simp [boxField, hb])
    (fun n => by exact_mod_cast IsingBoundaryRouteCeiling.card_boundary_le n)

/-! ## 7. ADDENDUM 23 AUGUST 2026 — the route's output, COMPUTED, for the class both models live in

§6 bounds the route's total. For the profiles this estate actually holds it can be computed
exactly, and the computation supersedes one of §6's own claims. -/

/-- An **indicator** profile: strength `h₀` on `S`, nothing off it. Both models here are of this
shape — `IsingBoxInteraction.boxField` with `S = ∂`, and the bulk field with `S = univ`. -/
def IsIndicator (f : Site n → ℝ) (S : Finset (Site n)) (h₀ : ℝ) : Prop :=
  (∀ p ∈ S, f p = h₀) ∧ (∀ p, p ∉ S → f p = 0)

/-- **FOR AN INDICATOR PROFILE THE ROUTE'S TOTAL IS NOT BOUNDED BUT COMPUTED**: exactly
`|S| · tanh h₀`. **No monotonicity of `tanh` is used, and that is not a stylistic remark** — this
Mathlib has `Real.tanh_lt_one` and `Real.neg_one_lt_tanh` and no `tanh_le_tanh` at all, so an
argument needing monotonicity would have had to prove it first. This one needs `Real.tanh_zero`. -/
theorem sum_tanh_of_indicator (f : Site n → ℝ) (S : Finset (Site n)) (h₀ : ℝ)
    (hf : IsIndicator f S h₀) :
    ∑ p : Site n, tanh (f p) = (S.card : ℝ) * tanh h₀ := by
  obtain ⟨hon, hoff⟩ := hf
  have h1 : ∑ p ∈ S, tanh (f p) = ∑ p : Site n, tanh (f p) := by
    refine Finset.sum_subset (Finset.subset_univ S) ?_
    intro p _ hpS
    rw [hoff p hpS, Real.tanh_zero]
  rw [← h1, Finset.sum_congr rfl fun p hp => by rw [hon p hp], Finset.sum_const, nsmul_eq_mul]

/-- The boundary field is the indicator of `∂` at strength `β·h`. -/
theorem isIndicator_boxField (n : ℕ) (β h : ℝ) :
    IsIndicator (boxField n β h) ((Finset.univ : Finset (Site n)).filter fun p => isBoundary p)
      (β * h) := by
  constructor
  · intro p hp
    have hb : isBoundary p = true := by simpa using hp
    rw [boxField, if_pos hb]
  · intro p hp
    have hb : ¬ (isBoundary p = true) := by simpa using hp
    rw [boxField, if_neg hb]

/-- A constant profile is the indicator of everything. -/
theorem isIndicator_const (n : ℕ) (x : ℝ) :
    IsIndicator (fun _ : Site n => x) Finset.univ x :=
  ⟨fun _ _ => rfl, fun p hp => absurd (Finset.mem_univ p) hp⟩

/-- **THE EXACT VALUE FOR THE BOUNDARY MODEL.** -/
theorem sum_tanh_boxField (n : ℕ) (β h : ℝ) :
    ∑ p : Site n, tanh (boxField n β h p)
      = (((Finset.univ : Finset (Site n)).filter fun p => isBoundary p).card : ℝ) * tanh (β * h) :=
  sum_tanh_of_indicator _ _ _ (isIndicator_boxField n β h)

/-- **AND SO `IsingBoundaryRouteCeiling.route_bound_le` IS DERIVED AFTER ALL — HYPOTHESIS AND ALL.**

§6's header says this file is "more general in the profile and weaker in the constant" than
`route_bound_le`, and that the two are *incomparable*. **That sentence is true of
`sum_tanh_le_card_of_support` and is SUPERSEDED HERE** (`ERRATUM 94`, kept above rather than
rewritten): once the total is computed rather than bounded, `route_bound_le` follows from
`sum_tanh_boxField` and `card_boundary_le`, and the `0 ≤ β·h` it carries is exactly what the last
step needs — `0 ≤ tanh (β·h)`. The constant was never the obstacle; the inequality was. -/
theorem route_bound_le_of_indicator (n : ℕ) {β h : ℝ} (hβh : 0 ≤ β * h) :
    ∑ p : Site n, tanh (boxField n β h p) ≤ 4 * (n : ℝ) * tanh (β * h) := by
  rw [sum_tanh_boxField n β h]
  have hcard : (((Finset.univ : Finset (Site n)).filter fun p => isBoundary p).card : ℝ)
      ≤ 4 * (n : ℝ) := by exact_mod_cast IsingBoundaryRouteCeiling.card_boundary_le n
  have htanh : (0 : ℝ) ≤ tanh (β * h) := by
    rcases eq_or_lt_of_le hβh with heq | hlt
    · rw [← heq, Real.tanh_zero]
    · exact (tanh_pos_of_pos hlt).le
  exact mul_le_mul_of_nonneg_right hcard htanh

/-- **THE OTHER HALF OF THE DICHOTOMY: AN EXTENSIVE SUPPORT DOES REACH THE TARGET.** With §6's
`route_insufficient_of_sublinear` this makes the route's behaviour a statement about the SIZE of
the support and nothing else — sub-extensive fails, extensive succeeds, and the boundary and bulk
models are the two ends of the same one-parameter fact rather than two files. -/
theorem indicator_bound_of_card (f : Site n → ℝ) (S : Finset (Site n)) (h₀ : ℝ)
    (hf : IsIndicator f S h₀) (hh₀ : 0 ≤ h₀) {δ : ℝ}
    (hcard : δ * ((n : ℝ) * n) ≤ (S.card : ℝ)) :
    (δ * tanh h₀) * ((n : ℝ) * n) ≤ ∑ p : Site n, tanh (f p) := by
  rw [sum_tanh_of_indicator f S h₀ hf]
  have htanh : (0 : ℝ) ≤ tanh h₀ := by
    rcases eq_or_lt_of_le hh₀ with heq | hlt
    · rw [← heq, Real.tanh_zero]
    · exact (tanh_pos_of_pos hlt).le
  calc (δ * tanh h₀) * ((n : ℝ) * n) = (δ * ((n : ℝ) * n)) * tanh h₀ := by ring
    _ ≤ (S.card : ℝ) * tanh h₀ := mul_le_mul_of_nonneg_right hcard htanh

end

end IsingSiteFieldBound
