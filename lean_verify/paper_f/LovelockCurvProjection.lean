import LovelockPairProjection

/-!
# The projection onto the algebraic curvature tensors

`LovelockPairProjection` built the first half of the object `WALLS` §W5.0 §5d names as what would
close both of the route's gaps, and said plainly what was missing: `pairProj` supplies three of
`IsAlgCurv`'s four clauses and **the first Bianchi identity is not imposed**. This file supplies
the fourth and composes them.

## The check §5d said had to come first, and it holds

That section recorded a design and one thing that had to be verified before the design was a plan:

> the estate's `IsAlgCurv.bianchi` is cyclic in the **first three** slots with `d` fixed
> (`R a b c d + R b c a d + R c a b d = 0`), while `b` above is cyclic in the **last three**. For an
> array with the pair symmetries the two are equivalent, and **that equivalence is a theorem nobody
> here has written.**

**`cyc_eq_zero_of_isAlgCurv` is that theorem**, and it costs three rewrites: each term of the
estate's clause, taken at `(b,c,d,a)`, becomes minus a term of the last-three cyclic sum by one
`pair_symm` and one `antisymm_left`. The two conventions agree, and the design is a plan.

## What is proved

* **`cyc`** — the cyclic sum over the last three slots, and `cyc_eq_zero_of_isAlgCurv`: it vanishes
  on algebraic curvature tensors;
* `cyc_cyc` — **`cyc ∘ cyc = 3 · cyc`, with no hypothesis at all**, which is what makes
  `bianchiProj` below a projection rather than merely a correction;
* **`bianchiProj A := A − ⅓ cyc A`**, with `cyc_bianchiProj` (the result satisfies the cyclic
  identity, again with no hypothesis) and `bianchiProj_eq_self`;
* **`ip_cyc_left`** — `⟨cyc A, B⟩ = ⟨A, cyc B⟩`, by two of the reindexings of the previous file, and
  hence **`ip_bianchiProj_left`**: `⟨bianchiProj A, B⟩ = ⟨A, B⟩` for every algebraic curvature `B`;
* `cyc_antisymm_left`, `cyc_antisymm_right`, `cyc_pair_symm` — **the cyclic sum keeps the three pair
  symmetries**, so the Bianchi step does not undo the first step;
* **`curvProj A := bianchiProj (pairProj A)`**, and the two theorems that make it the object §5d
  named:
  * **`isAlgCurv_curvProj`** — `curvProj A` is an algebraic curvature tensor, **for every array `A`,
    with no hypothesis whatever**;
  * **`ip_curvProj`** — `⟨curvProj A, B⟩ = ⟨A, B⟩` for every algebraic curvature tensor `B`. So
    against `Curv`, the projection is invisible.

## What this is and is not

**It is the object, and the object was the named gap-closer, and that is still not the same as
closing the gaps.** §5d's gaps (i) and (ii) are statements about `LovelockAdjoint.adjoint`
composed with this projection, and **that composition is not formed here** — no theorem in this
file mentions `T`. Two small lemmas are still missing before it can be: the 2-tensor twin of
`ip_act_transp`, and closure of `IsAlgCurv` under subtraction. **The watchlist item does not move**,
and `KillsWeyl` at `n ≥ 4` is exactly as open as it was.

**And this is not the `ip`-orthogonal projection in the bundled sense.** No submodule, no
`orthogonalProjection` instance, no uniqueness statement. What is proved is idempotence-on-the-image
(`bianchiProj_eq_self`, `pairProj_eq_self`), that the image lies in `Curv`, and that testing against
`Curv` cannot see it. Those three are what the route consumes; bundling is a separate decision, and
`LovelockReduction` §1's reason for not taking it stands.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockCurvProjection

open AlgebraicCurvature LovelockProjections LovelockOrthogonality LovelockPairProjection Finset

variable {n : ℕ}

/-! ## 1. The cyclic sum, and the convention check -/

def cyc (A : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) : ℝ :=
  A a b c d + A a c d b + A a d b c

theorem cyc_eq_zero_of_isAlgCurv {A : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hA : IsAlgCurv A) (a b c d : Fin n) : cyc A a b c d = 0 := by
  have hb := hA.bianchi b c d a
  have h1 : A b c d a = -A a d b c := (hA.pair_symm b c d a).trans (hA.antisymm_left d a b c)
  have h2 : A c d b a = -A a b c d := (hA.pair_symm c d b a).trans (hA.antisymm_left b a c d)
  have h3 : A d b c a = -A a c d b := (hA.pair_symm d b c a).trans (hA.antisymm_left c a d b)
  rw [h1, h2, h3] at hb
  simp only [cyc]
  linarith

/-! ## 2. The Bianchi projector -/

theorem cyc_cyc (A : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    cyc (cyc A) a b c d = 3 * cyc A a b c d := by
  simp only [cyc]; ring

noncomputable def bianchiProj (A : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) : ℝ :=
  A a b c d - (1/3 : ℝ) * cyc A a b c d

theorem cyc_bianchiProj (A : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    cyc (bianchiProj A) a b c d = 0 := by
  simp only [cyc, bianchiProj]; ring

theorem bianchiProj_eq_self {A : Fin n → Fin n → Fin n → Fin n → ℝ}
    (h : ∀ a b c d, cyc A a b c d = 0) (a b c d : Fin n) :
    bianchiProj A a b c d = A a b c d := by
  simp only [bianchiProj, h a b c d]; ring

theorem ip_cyc_left (A B : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip (cyc A) B = ip A (cyc B) := by
  have h1 : ∑ p : Fin n × Fin n × Fin n × Fin n,
      A p.1 p.2.2.1 p.2.2.2 p.2.1 * B p.1 p.2.1 p.2.2.1 p.2.2.2
      = ∑ p : Fin n × Fin n × Fin n × Fin n,
        A p.1 p.2.1 p.2.2.1 p.2.2.2 * B p.1 p.2.2.2 p.2.1 p.2.2.1 :=
    sum_reindex
      ⟨fun p => (p.1, p.2.2.1, p.2.2.2, p.2.1), fun p => (p.1, p.2.2.2, p.2.1, p.2.2.1),
       fun _ => rfl, fun _ => rfl⟩
      (fun q => A q.1 q.2.1 q.2.2.1 q.2.2.2 * B q.1 q.2.2.2 q.2.1 q.2.2.1)
  have h2 : ∑ p : Fin n × Fin n × Fin n × Fin n,
      A p.1 p.2.2.2 p.2.1 p.2.2.1 * B p.1 p.2.1 p.2.2.1 p.2.2.2
      = ∑ p : Fin n × Fin n × Fin n × Fin n,
        A p.1 p.2.1 p.2.2.1 p.2.2.2 * B p.1 p.2.2.1 p.2.2.2 p.2.1 :=
    sum_reindex
      ⟨fun p => (p.1, p.2.2.2, p.2.1, p.2.2.1), fun p => (p.1, p.2.2.1, p.2.2.2, p.2.1),
       fun _ => rfl, fun _ => rfl⟩
      (fun q => A q.1 q.2.1 q.2.2.1 q.2.2.2 * B q.1 q.2.2.1 q.2.2.2 q.2.1)
  rw [ip_eq_prod, ip_eq_prod]
  have hsplit : ∀ p : Fin n × Fin n × Fin n × Fin n,
      cyc A p.1 p.2.1 p.2.2.1 p.2.2.2 * B p.1 p.2.1 p.2.2.1 p.2.2.2
        = A p.1 p.2.1 p.2.2.1 p.2.2.2 * B p.1 p.2.1 p.2.2.1 p.2.2.2
          + A p.1 p.2.2.1 p.2.2.2 p.2.1 * B p.1 p.2.1 p.2.2.1 p.2.2.2
          + A p.1 p.2.2.2 p.2.1 p.2.2.1 * B p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    intro p; simp only [cyc]; ring
  have hjoin : ∀ p : Fin n × Fin n × Fin n × Fin n,
      A p.1 p.2.1 p.2.2.1 p.2.2.2 * cyc B p.1 p.2.1 p.2.2.1 p.2.2.2
        = A p.1 p.2.1 p.2.2.1 p.2.2.2 * B p.1 p.2.1 p.2.2.1 p.2.2.2
          + A p.1 p.2.1 p.2.2.1 p.2.2.2 * B p.1 p.2.2.2 p.2.1 p.2.2.1
          + A p.1 p.2.1 p.2.2.1 p.2.2.2 * B p.1 p.2.2.1 p.2.2.2 p.2.1 := by
    intro p; simp only [cyc]; ring
  rw [Finset.sum_congr rfl fun p _ => hsplit p, Finset.sum_congr rfl fun p _ => hjoin p]
  simp only [Finset.sum_add_distrib, h1, h2]

theorem ip_bianchiProj_left {B : Fin n → Fin n → Fin n → Fin n → ℝ} (hB : IsAlgCurv B)
    (A : Fin n → Fin n → Fin n → Fin n → ℝ) : ip (bianchiProj A) B = ip A B := by
  have hcyc : ip (cyc A) B = 0 := by
    rw [ip_cyc_left]
    have hz : cyc B = fun _ _ _ _ => (0 : ℝ) :=
      funext fun a => funext fun b => funext fun c => funext fun d =>
        cyc_eq_zero_of_isAlgCurv hB a b c d
    rw [hz]
    simp only [ip, mul_zero, Finset.sum_const_zero]
  have hsplit : ∀ p : Fin n × Fin n × Fin n × Fin n,
      bianchiProj A p.1 p.2.1 p.2.2.1 p.2.2.2 * B p.1 p.2.1 p.2.2.1 p.2.2.2
        = A p.1 p.2.1 p.2.2.1 p.2.2.2 * B p.1 p.2.1 p.2.2.1 p.2.2.2
          - (1/3 : ℝ) * (cyc A p.1 p.2.1 p.2.2.1 p.2.2.2 * B p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    intro p; simp only [bianchiProj]; ring
  rw [ip_eq_prod, Finset.sum_congr rfl fun p _ => hsplit p, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← ip_eq_prod, ← ip_eq_prod, hcyc]
  ring


/-! ## 3. The cyclic sum keeps the three pair symmetries -/

theorem cyc_antisymm_left {A : Fin n → Fin n → Fin n → Fin n → ℝ}
    (h1 : ∀ a b c d, A a b c d = -A b a c d) (h2 : ∀ a b c d, A a b c d = -A a b d c)
    (h3 : ∀ a b c d, A a b c d = A c d a b) (a b c d : Fin n) :
    cyc A a b c d = -cyc A b a c d := by
  have e1 : A b a c d = -A a b c d := by have := h1 a b c d; linarith
  have e2 : A b c d a = -A a d b c := (h3 b c d a).trans (h1 d a b c)
  have e3 : A b d a c = -A a c d b := (h3 b d a c).trans (h2 a c b d)
  simp only [cyc, e1, e2, e3]; ring

theorem cyc_antisymm_right {A : Fin n → Fin n → Fin n → Fin n → ℝ}
    (h2 : ∀ a b c d, A a b c d = -A a b d c) (a b c d : Fin n) :
    cyc A a b c d = -cyc A a b d c := by
  have e1 : A a b d c = -A a b c d := by have := h2 a b c d; linarith
  have e2 : A a d c b = -A a d b c := by have := h2 a d c b; linarith
  have e3 : A a c b d = -A a c d b := by have := h2 a c b d; linarith
  simp only [cyc, e1, e2, e3]; ring

theorem cyc_pair_symm {A : Fin n → Fin n → Fin n → Fin n → ℝ}
    (h1 : ∀ a b c d, A a b c d = -A b a c d) (h2 : ∀ a b c d, A a b c d = -A a b d c)
    (h3 : ∀ a b c d, A a b c d = A c d a b) (a b c d : Fin n) :
    cyc A a b c d = cyc A c d a b := by
  have e1 : A c d a b = A a b c d := h3 c d a b
  have e2 : A c a b d = A a c d b := by
    have s1 : A c a b d = A b d c a := h3 c a b d
    have s2 : A b d c a = -A b d a c := by have := h2 b d c a; linarith
    have s3 : A b d a c = A a c b d := h3 b d a c
    have s4 : A a c b d = -A a c d b := by have := h2 a c b d; linarith
    linarith
  have e3 : A c b d a = A a d b c := by
    have s1 : A c b d a = A d a c b := h3 c b d a
    have s2 : A d a c b = -A a d c b := by have := h1 d a c b; linarith
    have s3 : A a d c b = -A a d b c := by have := h2 a d c b; linarith
    linarith
  simp only [cyc, e1, e2, e3]

/-! ## 4. The projection -/

noncomputable def curvProj (A : Fin n → Fin n → Fin n → Fin n → ℝ) :
    Fin n → Fin n → Fin n → Fin n → ℝ := bianchiProj (pairProj A)

theorem ip_curvProj {B : Fin n → Fin n → Fin n → Fin n → ℝ} (hB : IsAlgCurv B)
    (A : Fin n → Fin n → Fin n → Fin n → ℝ) : ip (curvProj A) B = ip A B := by
  rw [curvProj, ip_bianchiProj_left hB, ip_pairProj_left hB.antisymm_left hB.antisymm_right
    hB.pair_symm]

theorem isAlgCurv_curvProj (A : Fin n → Fin n → Fin n → Fin n → ℝ) : IsAlgCurv (curvProj A) := by
  have p1 : ∀ a b c d : Fin n, pairProj A a b c d = -pairProj A b a c d :=
    pairProj_antisymm_left A
  have p2 : ∀ a b c d : Fin n, pairProj A a b c d = -pairProj A a b d c :=
    pairProj_antisymm_right A
  have p3 : ∀ a b c d : Fin n, pairProj A a b c d = pairProj A c d a b :=
    pairProj_pair_symm A
  have q1 : ∀ a b c d : Fin n, curvProj A a b c d = -curvProj A b a c d := by
    intro a b c d
    simp only [curvProj, bianchiProj]
    have := cyc_antisymm_left p1 p2 p3 a b c d
    have := p1 a b c d
    linarith
  have q2 : ∀ a b c d : Fin n, curvProj A a b c d = -curvProj A a b d c := by
    intro a b c d
    simp only [curvProj, bianchiProj]
    have := cyc_antisymm_right p2 a b c d
    have := p2 a b c d
    linarith
  have q3 : ∀ a b c d : Fin n, curvProj A a b c d = curvProj A c d a b := by
    intro a b c d
    simp only [curvProj, bianchiProj]
    have := cyc_pair_symm p1 p2 p3 a b c d
    have := p3 a b c d
    linarith
  refine ⟨q1, q2, q3, ?_⟩
  intro x y z w
  have hz : cyc (curvProj A) w x y z = 0 := cyc_bianchiProj (pairProj A) w x y z
  have h1 : curvProj A x y z w = -curvProj A w z x y := by
    have s1 := q3 x y z w
    have s2 := q1 z w x y
    linarith
  have h2 : curvProj A y z x w = -curvProj A w x y z := by
    have s1 := q3 y z x w
    have s2 := q1 x w y z
    linarith
  have h3 : curvProj A z x y w = -curvProj A w y z x := by
    have s1 := q3 z x y w
    have s2 := q1 y w z x
    linarith
  simp only [cyc] at hz
  linarith

end LovelockCurvProjection
