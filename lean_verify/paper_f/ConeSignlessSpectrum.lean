/-
  ConeSignlessSpectrum: the signless Laplacian of the CONE over a regular graph — a complete
  structural decomposition at every size, for an infinite family of NON-BIPARTITE graphs

  WHY THIS FILE EXISTS. `UNLOCK_WATCHLIST` L34948 clause (b), as `ERRATUM 506` corrected it and
  entry 177 narrowed it, asks for a non-bipartite graph that is neither a cycle, nor complete,
  nor complete multipartite. `PawSignlessSpectrum` supplied one — the paw — and that entry
  recorded exactly what was still missing: **the wheel and a general odd-cycle graph are
  untouched, and NOTHING GENERALISES OFF FOUR VERTICES, every proof being a `fin_cases` or a
  `decide`.** This file is the generalisation, and it is wider than the wheel.

  The wheel is the cone over a cycle. Nothing in the computation uses the cycle: what it uses is
  that the rim is REGULAR. So the object here is the cone over any `d`-regular graph — the wheel,
  `K_{n+1}` (the cone over `K_n`), the cone over any cubic graph, the cone over a torus — and the
  decomposition is at every `n` and `d` with no case analysis anywhere.

  WHAT IS PROVED.
  * **`coneGraph`** — one new vertex (`none`, the hub) joined to every vertex of `G`, with
    `cone_deg_hub` (`= card V`) and `cone_deg_rim` (`= G.degree i + 1`).
  * **`cone_signless_mulVec_hub` and `cone_signless_mulVec_rim`** — `Q = D + A` acting on a
    vector, at the hub and at a rim vertex. Everything below is these two lines of arithmetic.
  * **`cone_signless_rim_eigen` — THE RIM MODES, and this is the half that carries the
    multiplicity.** On the ZERO-SUM rim vectors the cone's `Q` acts as `(d + 1) + A_G`, so every
    zero-sum eigenvector of `G`'s adjacency matrix lifts to an eigenvector of the cone's signless
    Laplacian with `d + 1` added to its eigenvalue. **The zero-sum condition is a hypothesis, not
    a computation** — which is why no character sum, no root of unity and no trigonometric
    identity appears in this file. A caller who wants numbers supplies `G`'s adjacency spectrum;
    for the wheel that is the cycle's, which this estate already has.
  * **`cone_signless_hub_eigen` — THE HUB MODES.** On the two-dimensional span of the hub and
    the constant rim vector, `Q` is the matrix `[[n, n], [1, 2d+1]]`, whose characteristic
    polynomial is `λ² − (n + 2d + 1)λ + 2dn`. **For any real root of that quadratic**, the vector
    `λ − 2d − 1` at the hub and `1` on the rim is an eigenvector with eigenvalue `λ`.
    **No square root is taken**: the hypothesis IS the quadratic, so the statement is exact and
    carries no radical.
  * **`cone_disc_pos`** — and the discriminant is strictly positive at EVERY `n` and `d`, so the
    two hub eigenvalues are always real and always distinct. As a quadratic in `d` the
    discriminant has negative discriminant of its own, which is why this needs no hypothesis at
    all — not regularity, not `d ≤ n − 1`, not a size bound.
  * **`cone_not_colorable_two`** — **the family is non-bipartite the moment `G` has an edge**,
    because the hub closes that edge into a triangle. So this is an infinite family of
    non-bipartite graphs with a complete structural spectral decomposition, which is what clause
    (b) asked to generalise.
  * **`cone_block_complete` and `cone_rim_complete` — THE CROSS-CHECK, and it is the reason to
    believe the arithmetic.** At a complete rim (`n = m`, `d = m − 1`) the block's quadratic
    factors as `(λ − 2m)(λ − (m − 1))`, and the rim eigenvalue `d + 1 + μ` at `μ = −1` is
    `m − 1`. The cone over `K_m` is `K_{m+1}`, whose signless Laplacian eigenvalues are
    `2(m+1) − 2 = 2m` and `(m+1) − 2 = m − 1` — **proved independently in this estate by
    `CompleteSignlessSpectrum` and `CompleteSpectrumTwoPoints`.** Both halves agree, so a
    general computation reproduces a known family exactly.

  WHAT IS **NOT** CLAIMED.
  * ~~**EXHAUSTION IS NOT PROVED.** This exhibits eigenvectors; it does not show they span. The
    count is right — `n − 1` independent zero-sum rim modes plus 2 hub modes is
    `n + 1 = |V(cone)|` — but **independence of the rim modes is a property of `G`'s eigenvectors
    that this file does not assume and cannot supply**, and nothing here measures an
    eigenspace.~~ **PROVED THE NEXT UNIT (80),**
    `ConeSignlessExhaustion.eigenvalue_dichotomy`: every eigenvalue of the cone's `Q` is a root
    of the hub quadratic or `d + 1 + μ` for `μ` an adjacency eigenvalue on a nonzero zero-sum
    vector. **AND THIS BULLET'S REASON WAS WRONG, in the cheap direction.** Independence of the
    rim modes is what a MULTIPLICITY count needs; exhaustion needs only that the two summands are
    `Q`-invariant and that the decomposition is direct, and both are elementary — the projection
    onto the hub plane commutes with `Q`, so an eigenvector's two parts are separately
    eigenvectors by linearity alone, with no orthogonality, no self-adjointness and no basis.
    **So the obstacle named here was real but misidentified, and the C was one unit away.** What
    survives is the narrower statement the next unit inherits: **multiplicities are still not
    computed**, and THAT is where independence belongs. The fence moved from *which numbers* to
    *how many times*.
  * ~~**No eigenvalue is EVALUATED.** The rim modes take `G`'s adjacency spectrum as input and
    the hub modes take a root of a quadratic as input. **Nothing in this file computes a
    number**, and that is deliberate: it is what makes the result general.~~
    **FALSE IN ITS HUB HALF FROM 2026-09-16 (unit 83), AND BY THIS FILE'S OWN THEOREM.**
    `ConeMultiplicityExact` writes the two hub eigenvalues down — `hubRootPlus` and
    `hubRootMinus`, the quadratic formula applied to the discriminant `cone_disc_pos` proves
    positive here — and proves both are eigenvalues of the cone's `Q` at every regular rim. So
    *nothing in this file computes a number* was true of this file and became a false thing to
    say about the chain, **because the number it declined to compute was already determined by
    the theorem two lines above it**. The RIM half stands: `cone_signless_rim_eigen` takes `G`'s
    adjacency spectrum as input and no unit has computed it for any `G`. Original kept per
    `ERRATUM 94`.
  * **The wheel is not instantiated here**, and clause (b)'s *the wheel is untouched* is
    NARROWED by this file rather than closed by it. ~~The estate has the cycle's signless
    spectrum (`SignlessCycleSpectrum`), so the instance is one unit of bookkeeping.~~
    **CORRECTED BEFORE THE COMMIT by `estateclaim_scan`, which asked for the query: that
    sentence priced the instance too cheaply.** The estate's cycle eigenvector is
    `CycleLaplacianSpectrum.chi`, a **ℂ-valued character**, and the theorem is
    `cx (signlessLap (cycleGraph (n+3))) *ᵥ chi = … • chi` over `ℂ`. `cone_signless_rim_eigen`
    is over `ℝ` and wants `G.adjMatrix ℝ *ᵥ y = μ • y` with `∑ y = 0`. So the instance needs
    three things, not none: the passage from the signless Laplacian to the adjacency matrix
    (`Q = 2I + A` on a cycle, genuinely trivial); a REAL eigenvector where the estate has a
    complex character; and **`∑ chi = 0`, the character sum this file was designed to avoid.**
    **The design choice that makes this file general is exactly the cost the wheel instance
    will have to pay**, and saying otherwise would have been an estimate dressed as a fact.
  * **Nothing about the cascade, the spine, or any wall.** This is graph spectral theory on the
    `W3`/signless side, it moves no verdict, and `L34948` clause (c) is untouched.

  0 sorry. 0 new axioms. `#print axioms`, stated exactly rather than rounded up: `coneGraph`
  and its two adjacency lemmas depend on **NO axioms at all** — the cone is a `match` and its
  edges are `trivial` — and the other sixteen are on
  [propext, Classical.choice, Quot.sound].
-/

import LaplacianSignless

namespace ConeSignlessSpectrum

open SimpleGraph LaplacianSignless Matrix

/-! ## The cone -/

section Graph

variable {V : Type*}

/-- The CONE over `G`: one new vertex (`none`, the hub) joined to every vertex of `G`. -/
def coneGraph (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj a b := match a, b with
    | none, none => False
    | none, some _ => True
    | some _, none => True
    | some i, some j => G.Adj i j
  symm := by
    intro a b hab
    cases a with
    | none => cases b with
      | none => exact hab.elim
      | some j => trivial
    | some i => cases b with
      | none => trivial
      | some j => exact G.symm hab
  loopless := by
    refine ⟨fun a ha => ?_⟩
    cases a with
    | none => exact ha
    | some i => exact G.irrefl ha

instance (G : SimpleGraph V) [DecidableRel G.Adj] : DecidableRel (coneGraph G).Adj := by
  intro a b
  cases a <;> cases b <;> unfold coneGraph <;> simp only <;> infer_instance

/-- The hub is joined to every rim vertex. -/
theorem coneGraph_adj_hub (G : SimpleGraph V) (i : V) : (coneGraph G).Adj none (some i) := trivial

/-- Two rim vertices are joined exactly when they were. -/
theorem coneGraph_adj_rim (G : SimpleGraph V) (i j : V) :
    (coneGraph G).Adj (some i) (some j) ↔ G.Adj i j := Iff.rfl

/-- **THE FAMILY IS NON-BIPARTITE THE MOMENT `G` HAS AN EDGE**, because the hub closes that edge
into a triangle. -/
theorem cone_not_colorable_two (G : SimpleGraph V) {i j : V} (hij : G.Adj i j) :
    ¬ (coneGraph G).Colorable 2 := by
  rintro ⟨C⟩
  have h1 : C none ≠ C (some i) := C.valid (by trivial)
  have h2 : C none ≠ C (some j) := C.valid (by trivial)
  have h3 : C (some i) ≠ C (some j) := C.valid hij
  revert h1 h2 h3
  generalize C none = a
  generalize C (some i) = b
  generalize C (some j) = c
  revert a b c
  decide

end Graph

/-! ## Degrees -/

section Degrees

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem cone_nbf_hub [DecidableEq V] :
    (coneGraph G).neighborFinset none = Finset.univ.image some := by
  ext b
  cases b with
  | none => simp [coneGraph, mem_neighborFinset]
  | some j => simp [coneGraph, mem_neighborFinset]

/-- The hub sees everything. -/
theorem cone_deg_hub : (coneGraph G).degree none = Fintype.card V := by
  classical
  rw [degree, cone_nbf_hub,
    Finset.card_image_of_injective _ (Option.some_injective V), Finset.card_univ]

theorem cone_nbf_rim [DecidableEq V] (i : V) :
    (coneGraph G).neighborFinset (some i)
      = insert none ((G.neighborFinset i).image some) := by
  ext b
  cases b with
  | none => simp [coneGraph, mem_neighborFinset]
  | some j => simp [coneGraph, mem_neighborFinset]

/-- A rim vertex gains exactly the hub. -/
theorem cone_deg_rim (i : V) : (coneGraph G).degree (some i) = G.degree i + 1 := by
  classical
  rw [degree, cone_nbf_rim, Finset.card_insert_of_notMem (by simp),
    Finset.card_image_of_injective _ (Option.some_injective V), degree]

/-! ## `Q = D + A`, acting -/

/-- `Q` acting on a vector, at the hub. -/
theorem cone_signless_mulVec_hub [DecidableEq V] (x : Option V → ℝ) :
    (signlessLap (coneGraph G) *ᵥ x) none
      = (Fintype.card V : ℝ) * x none + ∑ j, x (some j) := by
  have hQ : signlessLap (coneGraph G) = (coneGraph G).degMatrix ℝ + (coneGraph G).adjMatrix ℝ :=
    rfl
  rw [hQ, Matrix.add_mulVec, Pi.add_apply, degMatrix_mulVec_apply, adjMatrix_mulVec_apply,
    cone_deg_hub, cone_nbf_hub,
    Finset.sum_image (by intro a _ b _ h; exact Option.some_injective V h)]

/-- `Q` acting on a vector, at a rim vertex. -/
theorem cone_signless_mulVec_rim [DecidableEq V] (x : Option V → ℝ) (i : V) :
    (signlessLap (coneGraph G) *ᵥ x) (some i)
      = ((G.degree i : ℝ) + 1) * x (some i) + x none
        + ∑ j ∈ G.neighborFinset i, x (some j) := by
  have hQ : signlessLap (coneGraph G) = (coneGraph G).degMatrix ℝ + (coneGraph G).adjMatrix ℝ :=
    rfl
  rw [hQ, Matrix.add_mulVec, Pi.add_apply, degMatrix_mulVec_apply, adjMatrix_mulVec_apply,
    cone_deg_rim, cone_nbf_rim, Finset.sum_insert (by simp),
    Finset.sum_image (by intro a _ b _ h; exact Option.some_injective V h)]
  push_cast
  ring

end Degrees

/-! ## The two families of vectors -/

section Vectors

variable {V : Type*}

/-- A rim vector: zero at the hub, `y` on the rim. -/
def liftRim (y : V → ℝ) : Option V → ℝ
  | none => 0
  | some i => y i

@[simp] theorem liftRim_none (y : V → ℝ) : liftRim y none = 0 := rfl

@[simp] theorem liftRim_some (y : V → ℝ) (i : V) : liftRim y (some i) = y i := rfl

theorem liftRim_ne_zero {y : V → ℝ} (hy : y ≠ 0) : liftRim y ≠ 0 := by
  intro hc
  apply hy
  funext i
  have := congrFun hc (some i)
  simpa using this

/-- The hub-plus-constant-rim vector attached to a root of the block's quadratic. -/
def hubVec (d : ℕ) (lam : ℝ) : Option V → ℝ
  | none => lam - 2 * d - 1
  | some _ => 1

theorem hubVec_ne_zero [Nonempty V] (d : ℕ) (lam : ℝ) : (hubVec (V := V) d lam) ≠ 0 := by
  intro hc
  have := congrFun hc (some (Classical.arbitrary V))
  simp only [hubVec, Pi.zero_apply] at this
  exact one_ne_zero this

end Vectors

/-! ## The decomposition -/

section Spectrum

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **THE RIM MODES.** On the zero-sum rim vectors the cone's `Q` acts as `(d + 1) + A_G`, so
every zero-sum eigenvector of `G`'s adjacency matrix lifts to an eigenvector of the cone's
signless Laplacian with `d + 1` added to its eigenvalue. The zero-sum condition is a hypothesis,
not a computation, which is why no character sum appears anywhere in this file. -/
theorem cone_signless_rim_eigen {d : ℕ} (hreg : ∀ i, G.degree i = d)
    (y : V → ℝ) (hsum : ∑ i, y i = 0) {μ : ℝ} (hy : G.adjMatrix ℝ *ᵥ y = μ • y) :
    signlessLap (coneGraph G) *ᵥ liftRim y = ((d : ℝ) + 1 + μ) • liftRim y := by
  funext a
  cases a with
  | none =>
      rw [cone_signless_mulVec_hub]
      simp only [liftRim_none, liftRim_some, mul_zero, zero_add]
      rw [hsum, Pi.smul_apply, liftRim_none, smul_zero]
  | some i =>
      rw [cone_signless_mulVec_rim, hreg i]
      have hA : (G.adjMatrix ℝ *ᵥ y) i = μ * y i := by rw [hy]; simp
      rw [adjMatrix_mulVec_apply] at hA
      simp only [liftRim_none, liftRim_some, add_zero]
      rw [hA, Pi.smul_apply, liftRim_some, smul_eq_mul]
      ring

/-- **THE HUB MODES.** For any real root of `λ² = (n + 2d + 1)λ − 2dn`, the vector that is
`λ − 2d − 1` at the hub and `1` on the rim is an eigenvector of the cone's signless Laplacian
with eigenvalue `λ`. **No square root is taken**: the hypothesis is the quadratic itself. -/
theorem cone_signless_hub_eigen {d : ℕ} (hreg : ∀ i, G.degree i = d) {lam : ℝ}
    (hlam : lam ^ 2 = ((Fintype.card V : ℝ) + 2 * d + 1) * lam - 2 * d * (Fintype.card V : ℝ)) :
    signlessLap (coneGraph G) *ᵥ hubVec d lam = lam • hubVec (V := V) d lam := by
  funext a
  cases a with
  | none =>
      rw [cone_signless_mulVec_hub]
      simp only [hubVec, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        Pi.smul_apply, smul_eq_mul]
      nlinarith [hlam]
  | some i =>
      rw [cone_signless_mulVec_rim, hreg i]
      simp only [hubVec, Finset.sum_const, nsmul_eq_mul, mul_one, Pi.smul_apply, smul_eq_mul]
      rw [show (G.neighborFinset i).card = G.degree i from rfl, hreg i]
      ring

end Spectrum

/-! ## The discriminant, and the cross-check -/

/-- **THE BLOCK'S DISCRIMINANT IS STRICTLY POSITIVE AT EVERY `n` AND `d`**, so the two hub
eigenvalues are always real and always distinct. As a quadratic in `d` the discriminant has
negative discriminant of its own, which is why no hypothesis is needed — not regularity, not
`d ≤ n − 1`, not a size bound. -/
theorem cone_disc_pos (n d : ℕ) :
    0 < ((n : ℝ) + 2 * d + 1) ^ 2 - 4 * (2 * d * (n : ℝ)) := by
  nlinarith [sq_nonneg ((n : ℝ) - 2 * d + 1), sq_nonneg ((n : ℝ) - 1), sq_nonneg ((d : ℝ)),
    Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) d]

/-- **THE CROSS-CHECK, hub half.** At a complete rim (`n = m`, `d = m − 1`) the block's quadratic
factors as `(λ − 2m)(λ − (m − 1))`. The cone over `K_m` is `K_{m+1}`, whose signless Laplacian
eigenvalues are `2(m+1) − 2 = 2m` and `(m+1) − 2 = m − 1` — proved independently in this estate
by `CompleteSignlessSpectrum` and `CompleteSpectrumTwoPoints`. -/
theorem cone_block_complete (m : ℕ) (lam : ℝ) :
    lam ^ 2 - ((m : ℝ) + 2 * ((m : ℝ) - 1) + 1) * lam + 2 * ((m : ℝ) - 1) * (m : ℝ)
      = (lam - 2 * m) * (lam - ((m : ℝ) - 1)) := by
  ring

/-- **THE CROSS-CHECK, rim half.** On a complete rim the adjacency matrix has eigenvalue `−1` on
zero-sum vectors, so this file's rim eigenvalue `d + 1 + μ` is `m − 1` — the same `K_{m+1}`
eigenvalue, now carrying the multiplicity the rim modes give it. -/
theorem cone_rim_complete (m : ℕ) : ((m : ℝ) - 1) + 1 + (-1) = (m : ℝ) - 1 := by ring

end ConeSignlessSpectrum
