import BoundaryFieldLimit

/-!
# At any finite field, the `+` class is asymptotically invisible

`BoundaryFieldLimit` left `IsingBoundaryField.MagnetisationBound` one quantifier away: a
threshold in the field strength `h` per box, where the target needs one `h` for every box.
It said, honestly, that nothing there decided whether the quantifier can be moved.

**This file decides it for the obvious route, and the answer is no.**

## The route, and why it looked promising

On the `+` class the field term is the *constant* `h · B` — every boundary spin is up — so the
boundary-field measure **conditioned on `+` is exactly the field-free `+`-conditioned
measure**, at every finite `h`, with no limit at all. That is `conditional_eq`, proved here
rather than asserted, and it makes the following decomposition irresistible:

`∫ M dμ_h  =  P_h(+) · E_h[M ∣ +]  +  P_h(¬+) · E_h[M ∣ ¬+]  ≥  P_h(+) (1-2ε) n² - P_h(¬+) n²`,

with the first conditional expectation supplied verbatim by the Peierls chain. All it needs is
`P_h(+)` close to `1`.

## Why it fails, and this is a theorem rather than a difficulty

**`P_h(+) → 0` as the box grows, at every temperature and every finite field.** The reason is
entropy of the boundary layer, and it is quantitative: flipping a single boundary spin of a
`+` configuration costs at most `16 + 2h` in energy — `16` because a site has at most four
neighbours, and `2h` because exactly one boundary spin turned over — and there are `B ≥ n`
boundary sites to flip, each giving a *distinct* configuration.

> **`plus_prob_le`** — `P_h(+) ≤ 1 / (1 + B · exp (-β (16 + 2h)))`, so
> **`tendsto_plus_prob_zero`**: for every `β ≥ 0` and every `h`, `P_h(+) → 0` as `n → ∞`.

So the class the entire Peierls chain conditions on carries vanishing probability in the very
limit `MagnetisationBound` is about. Put the bound into the decomposition and read the two
terms: the first is at most `n² / (1 + B t) = O(n)`, and the second subtracts
`(1 - o(1)) · n²`. The sum is negative for all large boxes. **No amount of sharpening the
conditional estimate repairs that, because the conditional estimate is not what is failing.**

## What this does and does not say

* It does **not** refute `MagnetisationBound`. **A guess, labelled as one because ERRATUM 86
  is about exactly this kind of sentence**: at fixed `h > 0` a typical configuration probably
  has only a few boundary spins down, so the magnetisation deficit they cost may well be
  `O(n)` against a target of order `n²`. The estate has no estimate of that deficit in either
  direction, and this file adds none.
* It **does** rule out reaching `MagnetisationBound` by conditioning on `+` and paying for the
  complement — the route the finished chain supplies most directly, and the one
  `conditional_eq` makes look free.
* What that leaves is what `BoundaryFieldLimit` could not settle: an argument that does not
  condition on `+`. The obvious candidate is the contour argument re-run with the field in
  the Hamiltonian, so that contours may end on the boundary at a price rather than being
  forbidden to — **but that this is the right candidate is, again, a guess and not a
  result.**

`MagnetisationBound` is untouched, and is still known false only at `h = 0`.
-/

namespace PlusClassVanishes

open IsingFiniteVolume IsingBoundaryField DualObstruction BoundaryFieldLimit
open MeasureTheory Filter

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. Every site has at most four neighbours

Absent from the estate until now, and needed the moment one asks what a single spin flip
costs. The proof is `DualFamily.degree_le_four`'s: exhibit a map from a four-element type
whose image contains the neighbours. -/

/-- Four candidate neighbours of `x`, indexed by `Fin 4`. When the step would leave the box
the candidate is `x` itself, which costs nothing: only the *containment* is used. -/
def nbr (x : Site n) (d : Fin 4) : Site n :=
  match d with
  | 0 => (x.1, if h : x.2.val + 1 < n then ⟨x.2.val + 1, h⟩ else x.2)
  | 1 => (x.1, ⟨x.2.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) x.2.isLt⟩)
  | 2 => ((if h : x.1.val + 1 < n then ⟨x.1.val + 1, h⟩ else x.1), x.2)
  | 3 => (⟨x.1.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) x.1.isLt⟩, x.2)

/-- Every neighbour of `x` is one of the four candidates. -/
theorem exists_nbr {x q : Site n} (h : adj x q) : ∃ d : Fin 4, q = nbr x d := by
  rcases h with ⟨hrow, hstep | hstep⟩ | ⟨hcol, hstep | hstep⟩
  · refine ⟨0, ?_⟩
    have hlt : x.2.val + 1 < n := by rw [hstep]; exact q.2.isLt
    refine Prod.ext hrow.symm (Fin.ext ?_)
    simp only [nbr, dif_pos hlt]
    omega
  · refine ⟨1, ?_⟩
    refine Prod.ext hrow.symm (Fin.ext ?_)
    simp only [nbr]
    omega
  · refine ⟨2, ?_⟩
    have hlt : x.1.val + 1 < n := by rw [hstep]; exact q.1.isLt
    refine Prod.ext (Fin.ext ?_) hcol.symm
    simp only [nbr, dif_pos hlt]
    omega
  · refine ⟨3, ?_⟩
    refine Prod.ext (Fin.ext ?_) hcol.symm
    simp only [nbr]
    omega

/-- **At most four neighbours.** -/
theorem card_adj_le_four (x : Site n) :
    ((Finset.univ : Finset (Site n)).filter (fun q => adj x q)).card ≤ 4 := by
  classical
  calc ((Finset.univ : Finset (Site n)).filter (fun q => adj x q)).card
      ≤ ((Finset.univ : Finset (Fin 4)).image (nbr x)).card := by
        refine Finset.card_le_card fun q hq => ?_
        obtain ⟨d, hd⟩ := exists_nbr (Finset.mem_filter.mp hq).2
        exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, hd.symm⟩
    _ ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
    _ = 4 := by simp

theorem card_adj_le_four' (x : Site n) :
    ((Finset.univ : Finset (Site n)).filter (fun p => adj p x)).card ≤ 4 := by
  classical
  refine le_trans (le_of_eq ?_) (card_adj_le_four x)
  refine Finset.card_nbij id (fun p hp => ?_) (fun _ _ _ _ h => h) ?_
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_symm _ _).mp (Finset.mem_filter.mp hp).2⟩
  · intro q hq
    exact ⟨q, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (adj_symm _ _).mpr (Finset.mem_filter.mp hq).2⟩, rfl⟩

/-! ## 2. One spin flip costs at most sixteen

With the ordered-pair convention of `isingH` (each bond twice) the four neighbours give
`4 · 4 = 16`. The constant is irrelevant; that it does not grow with the box is not. -/

/-- Flip the spin at `x` and leave the rest. -/
def flipAt (σ : Config n) (x : Site n) : Config n :=
  fun p => if p = x then !(σ p) else σ p

@[simp] theorem flipAt_self (σ : Config n) (x : Site n) : flipAt σ x x = !(σ x) := by
  simp [flipAt]

theorem flipAt_of_ne {σ : Config n} {x p : Site n} (hp : p ≠ x) : flipAt σ x p = σ p := by
  simp [flipAt, hp]

/-- **A single flip changes the energy by at most sixteen, uniformly in the box.** -/
theorem isingH_flipAt_le (σ : Config n) (x : Site n) :
    isingH n (flipAt σ x) ≤ isingH n σ + 16 := by
  classical
  have hflip : ∀ p q : Site n, p ≠ q → (p = x ∨ q = x) →
      spin (flipAt σ x p) * spin (flipAt σ x q) = -(spin (σ p) * spin (σ q)) := by
    intro p q hpq hor
    rcases hor with hp | hq
    · subst hp
      rw [flipAt_self, flipAt_of_ne (fun h => hpq h.symm), spin_not]
      ring
    · subst hq
      rw [flipAt_self, flipAt_of_ne hpq, spin_not]
      ring
  have hsame : ∀ p q : Site n, p ≠ x → q ≠ x →
      spin (flipAt σ x p) * spin (flipAt σ x q) = spin (σ p) * spin (σ q) := by
    intro p q hp hq
    rw [flipAt_of_ne hp, flipAt_of_ne hq]
  have key : ∀ p q : Site n,
      (if adj p q then spin (σ p) * spin (σ q) else (0 : ℝ))
        - (if adj p q then spin (flipAt σ x p) * spin (flipAt σ x q) else 0)
      ≤ (if p = x then (if adj x q then (2 : ℝ) else 0) else 0)
        + (if q = x then (if adj p x then (2 : ℝ) else 0) else 0) := by
    intro p q
    by_cases hadj : adj p q
    · have hpq : p ≠ q := fun h => adj_irrefl p (h ▸ hadj)
      have habs : |spin (σ p) * spin (σ q)| = 1 := by
        rw [abs_mul, abs_spin, abs_spin]; norm_num
      have hs := abs_le.mp habs.le
      simp only [if_pos hadj]
      by_cases hp : p = x
      · have hq : q ≠ x := fun h => hpq (hp.trans h.symm)
        rw [hflip p q hpq (Or.inl hp), if_pos hp, if_neg hq, if_pos (hp ▸ hadj)]
        linarith [hs.2]
      · by_cases hq : q = x
        · rw [hflip p q hpq (Or.inr hq), if_neg hp, if_pos hq, if_pos (hq ▸ hadj)]
          linarith [hs.2]
        · rw [hsame p q hp hq, if_neg hp, if_neg hq]
          simp
    · simp only [if_neg hadj, sub_self]
      split_ifs <;> norm_num
  have hA : ∀ p : Site n, ∑ _q : Site n, (if p = x then (0 : ℝ) else 0) = 0 := by
    intro p; simp
  have hstep : ∑ p : Site n, ∑ q : Site n,
      ((if p = x then (if adj x q then (2 : ℝ) else 0) else 0)
        + (if q = x then (if adj p x then (2 : ℝ) else 0) else 0))
      = (∑ q : Site n, (if adj x q then (2 : ℝ) else 0))
        + ∑ p : Site n, (if adj p x then (2 : ℝ) else 0) := by
    rw [Finset.sum_congr rfl fun p _ => Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    · have hcol : ∀ p : Site n,
          ∑ q : Site n, (if p = x then (if adj x q then (2 : ℝ) else 0) else 0)
            = if p = x then ∑ q : Site n, (if adj x q then (2 : ℝ) else 0) else 0 := by
        intro p; by_cases hp : p = x <;> simp [hp]
      rw [Finset.sum_congr rfl fun p _ => hcol p,
        Finset.sum_ite_eq' Finset.univ x
          (fun _ => ∑ q : Site n, (if adj x q then (2 : ℝ) else 0))]
      simp
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_ite_eq' Finset.univ x (fun _ => if adj p x then (2 : ℝ) else 0)]
      simp
  have h1 : ∑ q : Site n, (if adj x q then (2 : ℝ) else 0) ≤ 8 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hc : (((Finset.univ : Finset (Site n)).filter (fun q => adj x q)).card : ℝ) ≤ 4 := by
      exact_mod_cast card_adj_le_four x
    linarith
  have h2 : ∑ p : Site n, (if adj p x then (2 : ℝ) else 0) ≤ 8 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hc : (((Finset.univ : Finset (Site n)).filter (fun p => adj p x)).card : ℝ) ≤ 4 := by
      exact_mod_cast card_adj_le_four' x
    linarith
  have hdiff : isingH n (flipAt σ x) - isingH n σ
      = ∑ p : Site n, ∑ q : Site n,
        ((if adj p q then spin (σ p) * spin (σ q) else (0 : ℝ))
          - (if adj p q then spin (flipAt σ x p) * spin (flipAt σ x q) else 0)) := by
    simp only [isingH, neg_sub_neg]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => (Finset.sum_sub_distrib _ _).symm
  have hle : isingH n (flipAt σ x) - isingH n σ ≤ 16 := by
    rw [hdiff]
    calc ∑ p : Site n, ∑ q : Site n,
          ((if adj p q then spin (σ p) * spin (σ q) else (0 : ℝ))
            - (if adj p q then spin (flipAt σ x p) * spin (flipAt σ x q) else 0))
        ≤ ∑ p : Site n, ∑ q : Site n,
            ((if p = x then (if adj x q then (2 : ℝ) else 0) else 0)
              + (if q = x then (if adj p x then (2 : ℝ) else 0) else 0)) :=
          Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => key p q
      _ = _ := hstep
      _ ≤ 16 := by linarith
  linarith

/-! ## 3. Flipping one boundary spin of a `+` configuration

The result is not `+`, has exactly one down boundary spin, and different `(site,
configuration)` pairs give different results. That is all the combinatorics the count
needs. -/

theorem mem_bdrySites {p : Site n} : p ∈ bdrySites n ↔ isBoundary p = true := by
  rw [bdrySites, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem not_plus_flipAt {σ : Config n} (hσ : PlusBoundary σ) {x : Site n}
    (hx : isBoundary x = true) : ¬ PlusBoundary (flipAt σ x) := by
  intro hplus
  have hup := hplus x hx
  rw [flipAt_self, hσ x hx] at hup
  exact Bool.noConfusion hup

theorem downCount_flipAt {σ : Config n} (hσ : PlusBoundary σ) {x : Site n}
    (hx : isBoundary x = true) : downCount n (flipAt σ x) = 1 := by
  classical
  have hset : (bdrySites n).filter (fun p => flipAt σ x p = false) = {x} := by
    ext p
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hdown⟩
      by_contra hne
      rw [flipAt_of_ne hne, hσ p (mem_bdrySites.mp hp)] at hdown
      exact Bool.noConfusion hdown
    · rintro rfl
      refine ⟨mem_bdrySites.mpr hx, ?_⟩
      rw [flipAt_self, hσ p hx]
      rfl
  rw [downCount, hset, Finset.card_singleton]

/-- The flip map is injective on `(boundary site, `+` configuration)` pairs: the image
remembers the site, as its unique down boundary spin, and then the configuration. -/
theorem flipAt_injOn (n : ℕ) :
    ∀ z ∈ (bdrySites n) ×ˢ ((Finset.univ : Finset (Config n)).filter fun σ => PlusBoundary σ),
      ∀ w ∈ (bdrySites n) ×ˢ ((Finset.univ : Finset (Config n)).filter fun σ => PlusBoundary σ),
        flipAt z.2 z.1 = flipAt w.2 w.1 → z = w := by
  classical
  rintro ⟨x, σ⟩ hz ⟨y, ρ⟩ hw heq
  rw [Finset.mem_product] at hz hw
  have hxb : isBoundary x = true := mem_bdrySites.mp hz.1
  have hσ : PlusBoundary σ := (Finset.mem_filter.mp hz.2).2
  have hρ : PlusBoundary ρ := (Finset.mem_filter.mp hw.2).2
  have hxy : x = y := by
    by_contra hne
    have h1 : flipAt σ x x = false := by rw [flipAt_self, hσ x hxb]; rfl
    have h2 : flipAt ρ y x = true := by rw [flipAt_of_ne hne, hρ x hxb]
    rw [congrFun heq x, h2] at h1
    exact Bool.noConfusion h1
  subst hxy
  refine Prod.ext rfl ?_
  funext p
  by_cases hp : p = x
  · subst hp
    have := congrFun heq p
    rw [flipAt_self, flipAt_self] at this
    exact Bool.not_inj this
  · have := congrFun heq p
    rwa [flipAt_of_ne hp, flipAt_of_ne hp] at this

/-! ## 4. On the `+` class the field is a constant — which is why the route looks free -/

/-- Every boundary spin up means `boundaryTerm = B`, so the field contributes the same factor
to every `+` configuration. -/
theorem exp_isingHB_of_plus {σ : Config n} (hσ : PlusBoundary σ) (h β : ℝ) :
    Real.exp (-β * isingHB n h σ)
      = Real.exp (β * h * ((bdrySites n).card : ℝ)) * Real.exp (-β * isingH n σ) := by
  rw [exp_isingHB_factor, (downCount_eq_zero_iff n σ).mpr hσ]
  norm_num

/-- **CONDITIONED ON `+`, THE BOUNDARY-FIELD MODEL *IS* THE FIELD-FREE MODEL** — at every
finite `h`, with no limit taken. The constant factor cancels between numerator and
denominator, so every theorem the Peierls chain proves about the `+`-conditioned field-free
average holds verbatim for the `+`-conditioned boundary-field average.

**This is what makes conditioning look like a free route to `MagnetisationBound`**, and §6 is
why it is not. -/
theorem conditional_eq (n : ℕ) (h β : ℝ) (f : Config n → ℝ) :
    (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
        f σ * Real.exp (-β * isingHB n h σ)) /
      (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
        Real.exp (-β * isingHB n h σ))
    = (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
        f σ * Real.exp (-β * isingH n σ)) /
      (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
        Real.exp (-β * isingH n σ)) := by
  classical
  have hnum : ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
        f σ * Real.exp (-β * isingHB n h σ)
      = Real.exp (β * h * ((bdrySites n).card : ℝ)) *
        ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          f σ * Real.exp (-β * isingH n σ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [exp_isingHB_of_plus (Finset.mem_filter.mp hσ).2]
    ring
  have hden : ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
        Real.exp (-β * isingHB n h σ)
      = Real.exp (β * h * ((bdrySites n).card : ℝ)) *
        ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          Real.exp (-β * isingH n σ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ hσ => exp_isingHB_of_plus (Finset.mem_filter.mp hσ).2 h β
  rw [hnum, hden]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

/-! ## 5. So the `+` class is a vanishing fraction of the partition sum -/

/-- The weight of the `+`-boundary configurations under the boundary-field Hamiltonian. -/
noncomputable def plusWeight (n : ℕ) (h β : ℝ) : ℝ :=
  ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
    Real.exp (-β * isingHB n h σ)

/-- The full partition sum. -/
noncomputable def fullWeight (n : ℕ) (h β : ℝ) : ℝ :=
  ∑ σ : Config n, Real.exp (-β * isingHB n h σ)

theorem plusWeight_pos (n : ℕ) (h β : ℝ) : 0 < plusWeight n h β := by
  refine Finset.sum_pos (fun σ _ => Real.exp_pos _) ⟨fun _ => true, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _ => rfl⟩

theorem fullWeight_pos (n : ℕ) (h β : ℝ) : 0 < fullWeight n h β :=
  BoundaryFieldRatio.partition_pos n h β

/-- One flipped boundary spin costs at most `16 + 2h` in the boundary-field energy: `16` from
`isingH_flipAt_le`, and `2h` because exactly one boundary spin turned over. -/
theorem isingHB_flipAt_le {σ : Config n} (hσ : PlusBoundary σ) {x : Site n}
    (hx : isBoundary x = true) (h : ℝ) :
    isingHB n h (flipAt σ x) ≤ isingHB n h σ + (16 + 2 * h) := by
  have hd1 : (downCount n (flipAt σ x) : ℝ) = 1 := by
    rw [downCount_flipAt hσ hx]; norm_num
  have hd0 : (downCount n σ : ℝ) = 0 := by
    rw [(downCount_eq_zero_iff n σ).mpr hσ]; norm_num
  rw [isingHB, isingHB, boundaryTerm_eq, boundaryTerm_eq, hd1, hd0]
  have := isingH_flipAt_le σ x
  ring_nf
  linarith

/-- **THE COUNT.** The full partition sum is at least `(1 + B t)` times the `+`-class weight,
with `t = exp (-β (16 + 2h))` and `B` the number of boundary sites — because each of the `B`
single-boundary-flips of each `+` configuration is a distinct configuration outside the
class, of weight at least `t` times its parent's. -/
theorem fullWeight_ge (n : ℕ) (h : ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    (1 + ((bdrySites n).card : ℝ) * Real.exp (-β * (16 + 2 * h))) * plusWeight n h β
      ≤ fullWeight n h β := by
  classical
  set P := (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ) with hP
  set S := bdrySites n with hS
  set T := (S ×ˢ P).image (fun z : Site n × Config n => flipAt z.2 z.1) with hT
  have hdisj : Disjoint P T := by
    refine Finset.disjoint_left.mpr fun τ hτP hτT => ?_
    obtain ⟨⟨x, σ⟩, hz, rfl⟩ := Finset.mem_image.mp hτT
    rw [Finset.mem_product] at hz
    exact not_plus_flipAt (Finset.mem_filter.mp hz.2).2 (mem_bdrySites.mp hz.1)
      (Finset.mem_filter.mp hτP).2
  have hsub : P ∪ T ⊆ (Finset.univ : Finset (Config n)) := Finset.subset_univ _
  have hpw : plusWeight n h β = ∑ σ ∈ P, Real.exp (-β * isingHB n h σ) := rfl
  have hstep1 : (∑ σ ∈ P, Real.exp (-β * isingHB n h σ))
      + ∑ τ ∈ T, Real.exp (-β * isingHB n h τ) ≤ fullWeight n h β := by
    rw [← Finset.sum_union hdisj, fullWeight]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => (Real.exp_pos _).le
  have hstep2 : ∑ τ ∈ T, Real.exp (-β * isingHB n h τ)
      = ∑ z ∈ S ×ˢ P, Real.exp (-β * isingHB n h (flipAt z.2 z.1)) :=
    Finset.sum_image (flipAt_injOn n)
  have hstep3 : (S.card : ℝ) * Real.exp (-β * (16 + 2 * h))
        * (∑ σ ∈ P, Real.exp (-β * isingHB n h σ))
      ≤ ∑ z ∈ S ×ˢ P, Real.exp (-β * isingHB n h (flipAt z.2 z.1)) := by
    rw [Finset.sum_product]
    have hterm : ∀ x ∈ S, Real.exp (-β * (16 + 2 * h))
          * (∑ σ ∈ P, Real.exp (-β * isingHB n h σ))
        ≤ ∑ σ ∈ P, Real.exp (-β * isingHB n h (flipAt σ x)) := by
      intro x hx
      have hxb : isBoundary x = true := mem_bdrySites.mp hx
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun σ hσP => ?_
      have hσ : PlusBoundary σ := (Finset.mem_filter.mp hσP).2
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hle := isingHB_flipAt_le hσ hxb h
      nlinarith [hle, hβ]
    calc (S.card : ℝ) * Real.exp (-β * (16 + 2 * h))
          * (∑ σ ∈ P, Real.exp (-β * isingHB n h σ))
        = ∑ _x ∈ S, Real.exp (-β * (16 + 2 * h))
            * (∑ σ ∈ P, Real.exp (-β * isingHB n h σ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ ∑ x ∈ S, ∑ σ ∈ P, Real.exp (-β * isingHB n h (flipAt σ x)) :=
          Finset.sum_le_sum hterm
  rw [add_mul, one_mul, hpw]
  rw [hstep2] at hstep1
  linarith [hstep1, hstep3]

/-- The probability, under the boundary-field measure, that the boundary is entirely up. -/
noncomputable def plusProb (n : ℕ) (h β : ℝ) : ℝ := plusWeight n h β / fullWeight n h β

/-- It is a probability in the estate's own sense: the integral of the indicator against
`isingMeasure`. -/
theorem plusProb_eq_integral (n : ℕ) (h β : ℝ) :
    ∫ σ, (if PlusBoundary σ then (1 : ℝ) else 0) ∂(isingMeasure n h β) = plusProb n h β := by
  classical
  rw [BoundaryFieldRatio.integral_isingMeasure, plusProb, plusWeight, fullWeight]
  congr 1
  have hterm : ∀ σ : Config n,
      (if PlusBoundary σ then (1 : ℝ) else 0) * Real.exp (-β * isingHB n h σ)
        = if PlusBoundary σ then Real.exp (-β * isingHB n h σ) else 0 := by
    intro σ; by_cases hc : PlusBoundary σ <;> simp [hc]
  rw [Finset.sum_congr rfl fun σ _ => hterm σ, ← Finset.sum_filter]

/-- **`P(boundary all up) ≤ 1 / (1 + B t)`.** -/
theorem plusProb_le (n : ℕ) (h : ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    plusProb n h β ≤ 1 / (1 + ((bdrySites n).card : ℝ) * Real.exp (-β * (16 + 2 * h))) := by
  have hpos := plusWeight_pos n h β
  have hfull := fullWeight_pos n h β
  have hden : 0 < 1 + ((bdrySites n).card : ℝ) * Real.exp (-β * (16 + 2 * h)) := by
    have : (0 : ℝ) ≤ ((bdrySites n).card : ℝ) * Real.exp (-β * (16 + 2 * h)) := by positivity
    linarith
  rw [plusProb, div_le_div_iff₀ hfull hden]
  nlinarith [fullWeight_ge n h hβ]

/-! ## 6. And it tends to zero as the box grows -/

/-- The boundary has at least `n` sites: the bottom row is boundary. -/
theorem n_le_card_bdrySites (n : ℕ) : n ≤ (bdrySites n).card := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hinj : ∀ j ∈ (Finset.univ : Finset (Fin n)), ∀ k ∈ (Finset.univ : Finset (Fin n)),
        ((⟨0, hn⟩ : Fin n), j) = ((⟨0, hn⟩ : Fin n), k) → j = k := by
      intro j _ k _ hjk
      exact (Prod.ext_iff.mp hjk).2
    calc n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ (bdrySites n).card := by
          refine Finset.card_le_card_of_injOn (fun j => ((⟨0, hn⟩ : Fin n), j)) (fun j _ => ?_)
            (fun j hj k hk => hinj j hj k hk)
          exact mem_bdrySites.mpr (by simp [isBoundary])

/-- **THE OBSTRUCTION.** At every inverse temperature `β ≥ 0` and every field strength `h`,
the probability that the boundary is entirely up tends to zero as the box grows.

So the `+` class — the class the whole Peierls chain conditions on — is asymptotically
invisible under the measure `IsingBoundaryField.MagnetisationBound` is written with, and the
decomposition `∫ M = P(+) E[M ∣ +] + P(¬+) E[M ∣ ¬+]` cannot deliver a positive lower bound
however good the conditional estimate is. -/
theorem tendsto_plusProb_zero (h : ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    Tendsto (fun n : ℕ => plusProb n h β) atTop (nhds 0) := by
  set t : ℝ := Real.exp (-β * (16 + 2 * h)) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have hmaj : ∀ n : ℕ, plusProb n h β ≤ 1 / (1 + (n : ℝ) * t) := by
    intro n
    refine le_trans (plusProb_le n h hβ) ?_
    have hle : (n : ℝ) * t ≤ ((bdrySites n).card : ℝ) * t := by
      have : (n : ℝ) ≤ ((bdrySites n).card : ℝ) := by exact_mod_cast n_le_card_bdrySites n
      nlinarith [ht0]
    have h1 : (0 : ℝ) < 1 + (n : ℝ) * t := by positivity
    exact one_div_le_one_div_of_le h1 (by linarith)
  have hnonneg : ∀ n : ℕ, 0 ≤ plusProb n h β := fun n =>
    le_of_lt (div_pos (plusWeight_pos n h β) (fullWeight_pos n h β))
  refine squeeze_zero hnonneg hmaj ?_
  have hdiv : Tendsto (fun n : ℕ => 1 + (n : ℝ) * t) atTop atTop := by
    have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact Filter.tendsto_atTop_add_const_left _ 1 (hcast.atTop_mul_const ht0)
  simpa [one_div] using hdiv.inv_tendsto_atTop

end PlusClassVanishes
