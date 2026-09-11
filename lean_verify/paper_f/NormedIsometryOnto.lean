import InnerIsometryOnto

/-!
# A distance-preserving self-map of a finite-dimensional normed space is onto

`InnerIsometryOnto.surjective` proved this for a finite-dimensional real **inner product** space,
and the `UNLOCK_WATCHLIST` item it closed then recorded what its own first filing had got wrong: it
had called the missing statement *a Mathlib-shaped gap about metric spaces*, which is the
**normed**-space statement, and narrowed itself to exactly that — *whether a distance-preserving
self-map of a finite-dimensional normed space is onto. Nothing in this estate needs it.* **This
file proves it.**

**`surjective_of_isometry`** takes `f : E → E` with `Isometry f` on a finite-dimensional real
normed space and concludes `Function.Surjective f`. No inner product, no strict convexity and no
Mazur–Ulam: the inner-product proof is polarisation — it makes the recentred map preserve inner
products, then linear, then bijective — and **a general norm has no polarisation identity**, so the
route has to be different. It is compactness.

**AND THE ITEM WAS ASKING FOR MORE THAN IT SAID.** Surjectivity is exactly what Mazur–Ulam takes as
its input, so §4 gets the rest for free: **`recentreLinearIsometryEquiv`** — every
distance-preserving self-map of a finite-dimensional real normed space is **affine**, its recentring
a linear isometry equivalence — via `normedIsometryEquiv` and Mathlib's
`IsometryEquiv.toRealLinearIsometryEquiv`. So the residue this file closes was not *one missing
lemma about metric spaces* but the normed-space form of `FieldIsometryLinear`'s whole conclusion.

## The route, and it is compactness rather than algebra

* **`dist_iterate`** — an isometry's iterates are isometries, by induction.
* **`surjOn_of_isometry_of_isCompact`** — **an isometric self-map of a COMPACT set is onto it.**
  This is the whole content and Mathlib does not carry it: if `y` is missed, then `f '' K` is
  compact hence closed, so `ε := infDist y (f '' K)` is positive, and the orbit
  `y, f y, f² y, …` is `ε`-separated — because `dist (f^m y) (f^n y) = dist y (f^(n-m) y) ≥ ε` for
  `m < n`, the right-hand point lying in the image. An `ε`-separated sequence in a compact set
  contradicts `IsCompact.tendsto_subseq`.
* **`surjective_of_isometry`** — recentre so the map fixes the origin, which makes it
  norm-preserving and so a self-map of every closed ball; closed balls are compact because the
  space is finite-dimensional (`FiniteDimensional.proper_real`); apply the compact case at radius
  `‖z‖` to hit `z`.

## What is NOT here

* **`InnerIsometryOnto`'s elementary route is NOT made redundant, and this matters.** That file
  proves the inner-product case by polarisation — self-contained, no Mazur–Ulam, and it produces
  `recentreLinear` and `recentreIsometry` on the way. This file's §4 reaches the same conclusion at
  greater generality **by leaning on Mathlib's Mazur–Ulam**, which is a heavier import and a
  different kind of proof. `surjective_of_isometry_inner` records the subsumption of the
  SURJECTIVITY as a theorem; neither file's proof subsumes the other's, and `ERRATUM 465`'s rule —
  compare what each establishes, not only its hypotheses — is why both stay.
* **Nothing in this estate consumes it.** The watchlist item said so when it narrowed itself and it
  is still true: the estate's objects form an inner product space, where
  `InnerIsometryOnto.surjective` already applies and is cheaper. **This file closes a named
  residue at its true generality and buys no theorem below it**, which is recorded rather than
  dressed up.
* **No infinite-dimensional statement.** Finite-dimensionality is used exactly once, for
  compactness of closed balls, and the result is FALSE without it — the right shift on `ℓ²` is an
  isometry that is not onto. That counterexample is named, not formalised.
* **No `IsometryEquiv`.** Surjectivity plus injectivity would give one, and injectivity is
  immediate from `Isometry`, but no bundled equivalence is constructed. **Not attempted,
  11 September 2026**, and no cost is claimed (`ERRATUM 246`).

**No wall moves.** `W1`'s open part is still `OS0`, `OS4` and `OS1` in its continuum sense. This is
a metric-space fact with no field in it.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`, and this paragraph was written LAST, from
`binder_scan.py NormedIsometryOnto.lean` — the lesson three consecutive units before this one
taught): **all eight declarations take `Isometry f` or `Isometry g` and nothing about a field** —
no graph, no mass, no measure, and the word `gaussianField` appears nowhere in the file.
`dist_iterate` takes a `PseudoMetricSpace` and nothing more; `surjOn_of_isometry_of_isCompact`
takes a `MetricSpace` and a compact set, and is the only declaration that takes a `Set.MapsTo`; the
six in §§3–4 take `[NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]`, of which
**finite-dimensionality is the one the result genuinely needs** — it is used exactly once, for
compactness of closed balls — and `surjective_of_isometry_inner` swaps `NormedSpace` for
`InnerProductSpace` only to record the subsumption.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace NormedIsometryOnto

open Metric Filter Topology

/-! ## 1. Iterates of an isometry -/

/-- An isometry's iterates are isometries. -/
theorem dist_iterate {α : Type*} [PseudoMetricSpace α] {f : α → α} (hf : Isometry f) :
    ∀ (n : ℕ) (x y : α), dist (f^[n] x) (f^[n] y) = dist x y := by
  intro n
  induction n with
  | zero => intro x y; simp
  | succ k ih =>
      intro x y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hf.dist_eq, ih]

/-! ## 2. An isometric self-map of a compact set is onto it -/

/-- **AN ISOMETRIC SELF-MAP OF A COMPACT SET IS ONTO IT.** Mathlib does not carry this. If `y` is
missed then the orbit of `y` is `infDist y (f '' K)`-separated, which no sequence in a compact set
can be. -/
theorem surjOn_of_isometry_of_isCompact {α : Type*} [MetricSpace α] {K : Set α}
    (hK : IsCompact K) {f : α → α} (hf : Isometry f) (hmaps : Set.MapsTo f K K) :
    Set.SurjOn f K K := by
  intro y hy
  by_contra hny
  have himg : IsCompact (f '' K) := hK.image hf.continuous
  have hne : (f '' K).Nonempty := ⟨f y, ⟨y, hy, rfl⟩⟩
  have hpos : 0 < infDist y (f '' K) := (himg.isClosed.notMem_iff_infDist_pos hne).1 hny
  -- the orbit stays in `K`
  have horb : ∀ n, f^[n] y ∈ K := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ k ih => rw [Function.iterate_succ_apply']; exact hmaps ih
  -- and it is `infDist`-separated
  have hsep : ∀ m n : ℕ, m < n → infDist y (f '' K) ≤ dist (f^[m] y) (f^[n] y) := by
    intro m n hmn
    have hsplit : f^[n] y = f^[m] (f^[n - m] y) := by
      rw [← Function.iterate_add_apply f m (n - m) y, Nat.add_sub_cancel' hmn.le]
    have hmem : f^[n - m] y ∈ f '' K := by
      obtain ⟨j, hj⟩ : ∃ j, n - m = j + 1 := ⟨n - m - 1, by omega⟩
      exact ⟨f^[j] y, horb j, by rw [hj, Function.iterate_succ_apply']⟩
    calc infDist y (f '' K) ≤ dist y (f^[n - m] y) := infDist_le_dist_of_mem hmem
      _ = dist (f^[m] y) (f^[m] (f^[n - m] y)) := (dist_iterate hf m _ _).symm
      _ = dist (f^[m] y) (f^[n] y) := by rw [hsplit]
  obtain ⟨a, _, φ, hφ, htend⟩ := hK.tendsto_subseq horb
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend (infDist y (f '' K) / 2) (by positivity)
  have h1 := hN N le_rfl
  have h2 := hN (N + 1) (by omega)
  have hlt : dist (f^[φ N] y) (f^[φ (N + 1)] y) < infDist y (f '' K) := by
    calc dist (f^[φ N] y) (f^[φ (N + 1)] y)
        ≤ dist (f^[φ N] y) a + dist a (f^[φ (N + 1)] y) := dist_triangle _ _ _
      _ < infDist y (f '' K) / 2 + infDist y (f '' K) / 2 := by
          rw [dist_comm a]; exact add_lt_add h1 h2
      _ = infDist y (f '' K) := by ring
  exact absurd hlt (not_lt.2 (hsep _ _ (hφ (Nat.lt_succ_self N))))

/-! ## 3. The normed-space statement -/

/-- **A DISTANCE-PRESERVING SELF-MAP OF A FINITE-DIMENSIONAL REAL NORMED SPACE IS ONTO.** No inner
product, no strict convexity, no Mazur–Ulam and **no linearity**: the recentred map need not be
linear at a general norm, so this is compactness rather than polarisation. -/
theorem surjective_of_isometry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → E} (hf : Isometry f) : Function.Surjective f := by
  set g : E → E := fun x => f x - f 0 with hgdef
  have hgi : Isometry g := by
    rw [isometry_iff_dist_eq]
    intro a b
    simpa [hgdef, dist_sub_right] using hf.dist_eq a b
  have hg0 : g 0 = 0 := by simp [hgdef]
  have hnorm : ∀ x, ‖g x‖ = ‖x‖ := by
    intro x
    have h := hgi.dist_eq x 0
    rwa [hg0, dist_zero_right, dist_zero_right] at h
  have hsurj : Function.Surjective g := by
    intro z
    have hmaps : Set.MapsTo g (closedBall (0 : E) ‖z‖) (closedBall (0 : E) ‖z‖) := by
      intro x hx
      simp only [mem_closedBall, dist_zero_right] at hx ⊢
      rw [hnorm x]
      exact hx
    obtain ⟨x, _, hxz⟩ := surjOn_of_isometry_of_isCompact (isCompact_closedBall (0 : E) ‖z‖)
      hgi hmaps (show z ∈ closedBall (0 : E) ‖z‖ by simp)
    exact ⟨x, hxz⟩
  intro z
  obtain ⟨x, hx⟩ := hsurj (z - f 0)
  exact ⟨x, sub_left_inj.mp hx⟩

/-! ## 4. And therefore affine: Mazur–Ulam applies -/

section Affine
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → E}

/-- An isometric self-map of a finite-dimensional real normed space bundled as an
`IsometryEquiv`: injectivity is free and §3 supplies the surjectivity. **Named
`normedIsometryEquiv` rather than `toIsometryEquiv` because `InnerIsometryOnto.toIsometryEquiv` is
the inner-product version** — a collision `newnames_scan.py` flagged, answered by renaming so a
reader grepping the estate for either name finds one theorem. -/
noncomputable def normedIsometryEquiv (hf : Isometry f) : E ≃ᵢ E :=
  { Equiv.ofBijective f ⟨hf.injective, surjective_of_isometry hf⟩ with
    isometry_toFun := hf }

@[simp] theorem coe_normedIsometryEquiv (hf : Isometry f) :
    ((normedIsometryEquiv hf) : E → E) = f := rfl

/-- **SO EVERY DISTANCE-PRESERVING SELF-MAP OF A FINITE-DIMENSIONAL REAL NORMED SPACE IS AFFINE**:
recentred at the origin it is a linear isometry equivalence. **The surjectivity §3 supplies is
exactly what Mazur–Ulam needs as input**, which is why the watchlist item that asked for §3 was
asking for more than it said. -/
noncomputable def recentreLinearIsometryEquiv (hf : Isometry f) : E ≃ₗᵢ[ℝ] E :=
  (normedIsometryEquiv hf).toRealLinearIsometryEquiv

@[simp] theorem coe_recentreLinearIsometryEquiv (hf : Isometry f) (x : E) :
    ((recentreLinearIsometryEquiv hf) : E → E) x = f x - f 0 := by
  rw [recentreLinearIsometryEquiv, IsometryEquiv.toRealLinearIsometryEquiv_apply,
    coe_normedIsometryEquiv]

/-- The `InnerIsometryOnto` conclusion, recovered at this generality: an inner product space over
`ℝ` is a normed space, so §3 subsumes `InnerIsometryOnto.surjective`. **Stated so the subsumption
is a theorem rather than a remark** — and see the header for what it does NOT subsume. -/
theorem surjective_of_isometry_inner {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {g : F → F} (hg : Isometry g) :
    Function.Surjective g :=
  surjective_of_isometry hg

end Affine

end NormedIsometryOnto
