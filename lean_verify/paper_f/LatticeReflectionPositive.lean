/-
  LatticeReflectionPositive.lean — the estate's own statement of W1's failing
  step, proved.

  WHY. `GraphReflectionPositive` proved reflection positivity of the massive
  Green function for `boxGraph d n` with the reflection `revSite i`, and its
  own review section says plainly what was still missing:
  `LatticeReflection.ReflectionPositive` — **the `def` the estate wrote to
  name W1's failing step** — lives on `IsingFiniteVolume.Site n = Fin n × Fin n`
  with `refl n`, and the two boxes are the same box only through
  `BoxGraph.boxGraph_two_iso`. `GraphReflection.reflectionPositive_box`
  already identifies the general property at `(latticeGraph n, refl n)` WITH
  that `def`, by `Iff.rfl`, so the identification was never the gap. **The
  gap was the hypothesis**: the cross-coupling computation was done for the
  function encoding `Fin d → Fin n` and had not been re-run for pairs.

  The watchlist named two routes, and this file takes the one that leaves
  something behind: rather than redoing the arithmetic on pairs, transport
  the finished theorem along the isomorphism. That also discharges what
  `BoxGraph` claimed for `boxGraph_two_iso` — it was written so the `d = 2`
  case could be identified with the estate's box, and until now nothing used
  it for anything.

  WHAT THIS FILE PROVES:
  1. **§1, the transport.** For any bijection of vertex sets carrying one
     graph's adjacency to another's, the degree, the Laplacian, the massive
     operator and **the Green function all transport**
     (`green_congr`), and hence so does reflection positivity
     (`reflectionPositive_congr`) provided the bijection intertwines the two
     reflections. This is stated for two arbitrary finite graphs; nothing in
     it mentions a box. `GraphReflection.green_aut` is the special case of
     `green_congr` where the two graphs coincide.
  2. **§1 also: two structural lemmas about the property itself.**
     `ReflectionPositive.mono` — it is ANTITONE in the half, so shrinking the
     region is free. `ReflectionPositive.mirror` — it passes from a half to
     its mirror image, which is not free and is not symmetry-by-fiat: the
     estate's `def` reflects the FIRST argument only, so the two sides are
     different statements, and the proof reindexes both sums and uses that
     the Green function is `θ`-invariant.
  3. **§2, the two boxes agree.** `sitePair` intertwines `revSite 0` with
     `LatticeReflection.refl n` (`sitePair_revSite`), and carries
     `GraphHalfSpace.lowerHalf 0 n` onto `lowerHalfPair n`, the first-
     coordinate half of `Fin n × Fin n` (`map_lowerHalf`).
  4. **§3, THE DELIVERABLE.** `LatticeReflection.ReflectionPositive n m half`
     holds for even `n`, nonzero `m`, and every region contained in EITHER
     side of the cut — `half ⊆ lowerHalfPair n` or `half ⊆ (lowerHalfPair n)ᶜ`.
     The estate's named gap is a theorem.
  5. **§3 also, the non-degeneracy.** `LatticeReflection.reflectionPositive_empty`
     is recorded in that file as a WARNING: the `def` has a corner where it
     holds for nothing. So `lowerHalfPair` is shown to be a genuine half —
     `isHalf_lowerHalfPair`, and `card_lowerHalfPair`: it is exactly half the
     box, `2 · |H| = n²`.

  WHAT THIS DOES NOT DO.
  **It does not close W1.** All four non-closures recorded against
  `GraphReflectionPositive` stand, and only the fifth — the encoding gap —
  is removed here:
  * **Even side only.** `refl n` on a box of odd side fixes the middle row,
    and `GraphHalfSpace.not_isHalf_of_odd` says no half exists there. This is
    a site reflection, not a bond reflection, and the restriction is real.
  * **Not every half.** The estate's `def` takes `half` as a parameter. This
    proves it at every region lying wholly on one side of the
    first-coordinate cut. **A region STRADDLING the cut is not covered** and
    is not expected to be: reflection positivity is a statement about
    coefficients supported on one side, and a straddling support is a
    different — generally false — assertion. **Only the first coordinate is
    cut**: `LatticeReflection.refl n` reverses the first coordinate and the
    estate's `def` hardcodes it, so there is at present no second-coordinate
    statement in the estate — neither proved nor stated. Whether the same
    transport reaches one is not asserted here; it is seeded on the
    watchlist.
    **⚠ THE TRANSPORT REACHED IT FORTY-FOUR MINUTES LATER. Annotated
    2026-09-01** (`ERRATUM 94`, `ERRATUM 393`). This file was committed at
    **2026-08-09 19:51**; `LatticeReflectionTwo` at **20:35**, and its header
    quotes this very sentence — *"`LatticeReflectionPositive`'s header says
    plainly that the estate has no second-direction statement at all,
    'neither proved nor written down' … **It reaches it**, and the point of
    the file is that nothing new was needed."* **The caution above was
    correct and correctly hedged** — it said only that the transport's reach
    was not asserted here — and the answer came the same evening. What never
    happened is anyone returning to this bullet.
  * **Not measure-level OS2.** `LatticeField` established that the estate's
    OS2 packaging reaches the lattice covariance only as far as Gaussian
    moments. Nothing here is about a measure.
  * **No infinite-volume or continuum limit.** W2 is untouched: one box, one
    mass, one covariance.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import GraphReflectionPositive

namespace LatticeReflectionPositive

open Finset Matrix GraphLaplacian GraphReflection GraphHalfSpace

/-! ## 1. Transport along a graph isomorphism

Everything the Green function is built from is determined by adjacency, so a
bijection respecting adjacency carries all of it across. The proofs are the
`IsRefl` proofs of `GraphReflection` with the two vertex types allowed to
differ; that generalisation is the whole content, and it is what makes the
`d = 2` identification usable rather than decorative.
-/

section Transport

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {G' : SimpleGraph W} [DecidableRel G'.Adj]

omit [DecidableEq V] [DecidableEq W] in
/-- Degrees agree across an adjacency-preserving bijection. -/
theorem degree_congr (e : V ≃ W) (he : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q) (p : V) :
    G'.degree (e p) = G.degree p := by
  classical
  have himg : G'.neighborFinset (e p) = (G.neighborFinset p).image e := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image]
    constructor
    · intro hw
      refine ⟨e.symm w, ?_, by simp⟩
      have h := he p (e.symm w)
      rw [Equiv.apply_symm_apply] at h
      exact SimpleGraph.mem_neighborFinset _ _ _ |>.mp
        (by simpa [SimpleGraph.mem_neighborFinset] using h.mp hw)
    · rintro ⟨v, hv, rfl⟩
      exact (he p v).mpr (by simpa [SimpleGraph.mem_neighborFinset] using hv)
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
    himg, Finset.card_image_of_injective _ e.injective]

theorem lapMatrix_congr (e : V ≃ W) (he : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q) :
    (G'.lapMatrix ℝ).submatrix e e = G.lapMatrix ℝ := by
  classical
  ext p q
  simp only [Matrix.submatrix_apply, SimpleGraph.lapMatrix, Matrix.sub_apply,
    SimpleGraph.degMatrix, SimpleGraph.adjMatrix, Matrix.diagonal, Matrix.of_apply]
  have hd : (e p = e q) = (p = q) := propext ⟨fun hc => e.injective hc, fun hc => by rw [hc]⟩
  by_cases hpq : p = q
  · subst hpq; simp [degree_congr e he p]
  · simp only [hd, hpq, if_false]
    by_cases hadj : G.Adj p q
    · simp [(he p q).mpr hadj, hadj]
    · have hne : ¬ G'.Adj (e p) (e q) := fun hc => hadj ((he p q).mp hc)
      simp [hadj, hne]

theorem massive_congr (e : V ≃ W) (he : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q) (m : ℝ) :
    (GraphLaplacian.massive G' m).submatrix e e = GraphLaplacian.massive G m := by
  classical
  ext p q
  simp only [GraphLaplacian.massive, Matrix.submatrix_apply, Matrix.add_apply]
  have hlap := congrFun (congrFun (lapMatrix_congr e he) p) q
  simp only [Matrix.submatrix_apply] at hlap
  rw [hlap]
  congr 1
  simp only [Matrix.diagonal]
  have hd : (e p = e q) = (p = q) := propext ⟨fun hc => e.injective hc, fun hc => by rw [hc]⟩
  simp [hd]

/-- **THE GREEN FUNCTION TRANSPORTS.** `GraphReflection.green_aut` is this
    with `W = V` and `e` an involution; the point of separating the two
    vertex types is that a graph isomorphism between DIFFERENT encodings of
    the same box then carries theorems across. -/
theorem green_congr (e : V ≃ W) (he : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q) (m : ℝ) (p q : V) :
    GraphLaplacian.green G' m (e p) (e q) = GraphLaplacian.green G m p q := by
  have hg : (GraphLaplacian.green G' m).submatrix e e = GraphLaplacian.green G m := by
    rw [GraphLaplacian.green, GraphLaplacian.green, ← Matrix.inv_submatrix_equiv,
      massive_congr e he m]
  exact congrFun (congrFun hg p) q

/-- The reflected quadratic form transports, coefficient by coefficient. -/
theorem sum_green_congr (e : V ≃ W) (he : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q)
    {θ : V ≃ V} {θ' : W ≃ W} (hθ : ∀ p, e (θ p) = θ' (e p)) (m : ℝ) (c : W → ℝ) :
    ∑ p, ∑ q, c p * c q * GraphLaplacian.green G' m (θ' p) q
      = ∑ p, ∑ q, c (e p) * c (e q) * GraphLaplacian.green G m (θ p) q := by
  calc ∑ p, ∑ q, c p * c q * GraphLaplacian.green G' m (θ' p) q
      = ∑ p, ∑ q : V, c p * c (e q) * GraphLaplacian.green G' m (θ' p) (e q) :=
        Finset.sum_congr rfl fun p _ =>
          (Equiv.sum_comp e (fun q => c p * c q * GraphLaplacian.green G' m (θ' p) q)).symm
    _ = ∑ p : V, ∑ q : V, c (e p) * c (e q) * GraphLaplacian.green G' m (θ' (e p)) (e q) :=
        (Equiv.sum_comp e
          (fun p => ∑ q : V, c p * c (e q) * GraphLaplacian.green G' m (θ' p) (e q))).symm
    _ = ∑ p : V, ∑ q : V, c (e p) * c (e q) * GraphLaplacian.green G m (θ p) q := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        rw [← hθ p, green_congr e he]

/-- **REFLECTION POSITIVITY TRANSPORTS**, provided the bijection intertwines
    the two reflections. Both directions hold; §3 uses `mp`. -/
theorem reflectionPositive_congr (e : V ≃ W) (he : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q)
    {θ : V ≃ V} {θ' : W ≃ W} (hθ : ∀ p, e (θ p) = θ' (e p)) (m : ℝ) (H : Finset V) :
    GraphReflection.ReflectionPositive G m θ H
      ↔ GraphReflection.ReflectionPositive G' m θ' (H.map e.toEmbedding) := by
  classical
  constructor
  · intro hrp c hc
    rw [sum_green_congr e he hθ]
    refine hrp (fun p => c (e p)) fun p hp => hc (e p) ?_
    simp only [Finset.mem_map, Equiv.coe_toEmbedding]
    rintro ⟨k, hk, hke⟩
    exact hp (by rwa [e.injective hke] at hk)
  · intro hrp c hc
    have hsupp : ∀ w, w ∉ H.map e.toEmbedding → c (e.symm w) = 0 := by
      intro w hw
      refine hc _ fun hmem => hw ?_
      exact Finset.mem_map.mpr ⟨e.symm w, hmem, by simp⟩
    have h2 := hrp (fun w => c (e.symm w)) hsupp
    rw [sum_green_congr e he hθ] at h2
    simpa using h2

/-- **THE PROPERTY IS ANTITONE IN THE HALF.** A coefficient family supported
    in a smaller region is supported in the larger one, so nothing has to be
    reproved. This is why §3 states a family of halves rather than one. -/
theorem ReflectionPositive.mono {m : ℝ} {θ : V ≃ V} {H H' : Finset V} (hsub : H' ⊆ H)
    (h : GraphReflection.ReflectionPositive G m θ H) :
    GraphReflection.ReflectionPositive G m θ H' :=
  fun c hc => h c fun p hp => hc p fun hmem => hp (hsub hmem)

/-- **AND IT PASSES TO THE MIRROR HALF.** If the property holds for
    coefficients on one side of the reflection it holds for coefficients on
    the other, because the form is unchanged by reindexing both sums with `θ`
    and using that the Green function is `θ`-invariant and symmetric. Without
    this the estate's `def` would be proved on the lower half and silently
    unproved on the upper one, for no mathematical reason. -/
theorem ReflectionPositive.mirror {m : ℝ} {θ : V ≃ V} (h : GraphReflection.IsRefl G θ)
    {H : Finset V} (hrp : GraphReflection.ReflectionPositive G m θ H) :
    GraphReflection.ReflectionPositive G m θ (H.image θ) := by
  classical
  intro c hc
  have hc' : ∀ p, p ∉ H → c (θ p) = 0 := by
    intro p hp
    refine hc _ fun hmem => hp ?_
    obtain ⟨k, hk, hke⟩ := Finset.mem_image.mp hmem
    rwa [θ.injective hke] at hk
  have hK := hrp (fun p => c (θ p)) hc'
  have hS : ∑ p, ∑ q, c p * c q * GraphLaplacian.green G m (θ p) q
      = ∑ p, ∑ q, c (θ p) * c q * GraphLaplacian.green G m p q :=
    calc ∑ p, ∑ q, c p * c q * GraphLaplacian.green G m (θ p) q
        = ∑ p, ∑ q, c (θ p) * c q * GraphLaplacian.green G m (θ (θ p)) q :=
          (Equiv.sum_comp θ
            (fun p => ∑ q, c p * c q * GraphLaplacian.green G m (θ p) q)).symm
      _ = ∑ p, ∑ q, c (θ p) * c q * GraphLaplacian.green G m p q := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [h.invol p]
  have hKeq : ∑ p, ∑ q, c (θ p) * c (θ q) * GraphLaplacian.green G m (θ p) q
      = ∑ p, ∑ q, c (θ p) * c q * GraphLaplacian.green G m p q :=
    calc ∑ p, ∑ q, c (θ p) * c (θ q) * GraphLaplacian.green G m (θ p) q
        = ∑ p, ∑ q, c (θ p) * c (θ (θ q)) * GraphLaplacian.green G m (θ p) (θ q) :=
          Finset.sum_congr rfl fun p _ =>
            (Equiv.sum_comp θ
              (fun q => c (θ p) * c (θ q) * GraphLaplacian.green G m (θ p) q)).symm
      _ = ∑ p, ∑ q, c (θ p) * c q * GraphLaplacian.green G m p q := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
          rw [h.invol q, GraphReflection.green_aut h m]
  rw [hS, ← hKeq]
  exact hK

end Transport

/-! ## 2. The two encodings of the box

`BoxGraph.sitePair` is Mathlib's `finTwoArrowEquiv`, and `BoxGraph.adj_two_iff`
already says it respects adjacency. Two things are new here: it intertwines
the two reflections, and it carries one half onto the other.
-/

section Boxes

open BoxGraph

variable {n : ℕ}

/-- The first-coordinate half of the estate's box. -/
def lowerHalfPair (n : ℕ) : Finset (IsingFiniteVolume.Site n) :=
  Finset.univ.filter fun p => 2 * p.1.val < n

theorem mem_lowerHalfPair (p : IsingFiniteVolume.Site n) :
    p ∈ lowerHalfPair n ↔ 2 * p.1.val < n := by
  simp [lowerHalfPair]

/-- Adjacency corresponds, in the direction §1 wants it. -/
theorem adj_sitePair (p q : BoxGraph.Site 2 n) :
    (IsingContourSeparation.latticeGraph n).Adj (sitePair n p) (sitePair n q)
      ↔ (boxGraph 2 n).Adj p q := by
  simp only [IsingContourSeparation.latticeGraph_adj, boxGraph_adj]
  exact (adj_two_iff p q).symm

/-- **THE TWO REFLECTIONS AGREE.** Reversing coordinate `0` of a function on
    `Fin 2` is reversing the first entry of the corresponding pair. -/
theorem sitePair_revSite (p : BoxGraph.Site 2 n) :
    sitePair n (GraphReflection.revSite (n := n) (0 : Fin 2) p)
      = LatticeReflection.refl n (sitePair n p) := by
  have h0 : GraphReflection.revSite (n := n) (0 : Fin 2) p 0 = Fin.rev (p 0) :=
    GraphReflection.revSite_apply_self 0 p
  have h1 : GraphReflection.revSite (n := n) (0 : Fin 2) p 1 = p 1 :=
    GraphReflection.revSite_apply_ne (by decide) p
  simp [sitePair, h0, h1]

/-- **THE TWO HALVES AGREE.** -/
theorem map_lowerHalf (n : ℕ) :
    (GraphHalfSpace.lowerHalf (0 : Fin 2) n).map (sitePair n).toEmbedding = lowerHalfPair n := by
  classical
  ext q
  simp only [Finset.mem_map, Equiv.coe_toEmbedding, GraphHalfSpace.lowerHalf,
    lowerHalfPair, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa [sitePair] using hp
  · intro hq
    exact ⟨(sitePair n).symm q, by simpa [sitePair] using hq, by simp⟩

end Boxes

/-! ## 3. W1's failing step, in the estate's own words -/

section Deliverable

open BoxGraph

variable {n : ℕ}

/-- The half is a half: it and its mirror image partition the box. -/
theorem isHalf_lowerHalfPair (hn : Even n) :
    GraphHalfSpace.IsHalf (LatticeReflection.refl n) (lowerHalfPair n) := by
  intro p
  simp only [mem_lowerHalfPair, LatticeReflection.refl_apply]
  have hrev := Fin.val_rev p.1
  have hlt := p.1.isLt
  obtain ⟨k, hk⟩ := hn
  omega

/-- The transported theorem, at the graph level. Everything below is this
    plus `mono` and `mirror`. -/
theorem rp_lowerHalfPair (hn : Even n) {m : ℝ} (hm : m ≠ 0) :
    GraphReflection.ReflectionPositive (IsingContourSeparation.latticeGraph n) m
      (LatticeReflection.refl n) (lowerHalfPair n) := by
  rw [← map_lowerHalf n]
  exact (reflectionPositive_congr (sitePair n) adj_sitePair sitePair_revSite m _).mp
    (GraphReflectionPositive.reflectionPositive_box (0 : Fin 2) hn hm)

/-- **`LatticeReflection.ReflectionPositive` IS A THEOREM** — for a box of
    even side, a nonzero mass, and any region contained in the
    first-coordinate half.

    That `def` was written to name W1's failing step as an object, with the
    docstring "THIS IS A DEFINITION, NOT A THEOREM. Nothing in this estate
    proves it." Something in this estate now proves it. What has NOT changed
    is everything in the header's second half: this is one covariance on one
    finite box of even side, it is not measure-level OS2, and there is no
    limit of any kind. -/
theorem reflectionPositive_lattice (hn : Even n) {m : ℝ} (hm : m ≠ 0)
    {half : Finset (IsingFiniteVolume.Site n)} (hsub : half ⊆ lowerHalfPair n) :
    LatticeReflection.ReflectionPositive n m half :=
  (GraphReflection.reflectionPositive_box n m half).mp
    (ReflectionPositive.mono hsub (rp_lowerHalfPair hn hm))

/-- **AND ON THE OTHER SIDE OF THE CUT.** The two halves are not
    interchangeable by fiat — `refl n` is applied to the FIRST argument of
    the Green function in the estate's `def`, so the upper half is a separate
    statement — and `ReflectionPositive.mirror` is what makes it free. -/
theorem reflectionPositive_lattice_compl (hn : Even n) {m : ℝ} (hm : m ≠ 0)
    {half : Finset (IsingFiniteVolume.Site n)} (hsub : half ⊆ (lowerHalfPair n)ᶜ) :
    LatticeReflection.ReflectionPositive n m half := by
  refine (GraphReflection.reflectionPositive_box n m half).mp
    (ReflectionPositive.mono ?_ (ReflectionPositive.mirror
      (GraphReflection.isRefl_latticeGraph n) (rp_lowerHalfPair hn hm)))
  rw [(isHalf_lowerHalfPair hn).image_eq (LatticeReflection.refl_involutive n)]
  exact hsub

/-- **AND IT IS EXACTLY HALF**, `2·|H| = n²`, so §3's theorem is not the
    degenerate corner `LatticeReflection.reflectionPositive_empty` warns
    about. -/
theorem card_lowerHalfPair (hn : Even n) :
    2 * (lowerHalfPair n).card = n * n := by
  classical
  have himg := (isHalf_lowerHalfPair hn).image_eq (LatticeReflection.refl_involutive n)
  have hc : ((lowerHalfPair n).image (LatticeReflection.refl n)).card
      = (lowerHalfPair n).card :=
    Finset.card_image_of_injective _ (LatticeReflection.refl n).injective
  rw [himg, Finset.card_compl] at hc
  have hle : (lowerHalfPair n).card ≤ Fintype.card (IsingFiniteVolume.Site n) :=
    Finset.card_le_univ _
  have htot : Fintype.card (IsingFiniteVolume.Site n) = n * n := by simp
  rw [← htot]
  omega

/-- Non-vacuity at the level the theorem is used: the half is inhabited on
    every box of side at least one. -/
theorem lowerHalfPair_nonempty (hn : 0 < n) : (lowerHalfPair n).Nonempty :=
  ⟨(⟨0, hn⟩, ⟨0, hn⟩), by simpa [mem_lowerHalfPair] using hn⟩

end Deliverable

/-! ## 4. Review round 84 — the ways this could be hollow

**"Is this a real closure, or a renaming?"** It is a real closure of the item
the previous unit left open, and nothing more. The previous file's review
section named exactly one missing thing — "the HYPOTHESIS: §7's
cross-coupling computation is done for the `Fin d → Fin n` encoding and has
not been re-run for pairs" — and offered two routes. §1–§3 are the first
route, carried out. **The four OTHER non-closures that file recorded are
untouched and are restated in this header**, not quietly dropped.

**"Transport lemmas can be vacuous if the hypothesis is unsatisfiable."**
The hypothesis of `reflectionPositive_congr` is satisfied here by two
theorems, not by construction: `adj_sitePair`, which is `BoxGraph.adj_two_iff`
turned round, and `sitePair_revSite`, which is new and is the one place the
two encodings could have failed to agree — `revSite 0` acts by
`Function.update`, `refl n` acts on a pair, and the check that they match is
`revSite_apply_self` and `revSite_apply_ne` at the two coordinates of
`Fin 2`. Had they disagreed, the transport would have been unusable and route
(b) — redoing `BoxCrossCoupling` for pairs — would have been forced.

**"`green_congr` might just be `green_aut` with extra letters."** It is not
the same statement: `green_aut` is about one graph and an automorphism of it,
and cannot be applied when the vertex TYPES differ, which is precisely the
situation here (`Fin 2 → Fin n` against `Fin n × Fin n`). The proofs are
close because the content is the same — degree, Laplacian, mass term, inverse
— and the honest description is that §1 generalises FOUR of
`GraphReflection`'s lemmas by weakening `V ≃ V` to `V ≃ W`: `IsRefl.degree`,
`IsRefl.lapMatrix`, `IsRefl.massive` and `green_aut`. That each of the four
is recovered by feeding `IsRefl.adj` to its §1 counterpart was checked by
deriving it, not by inspection. **The generalisation is cheap and it is what
makes the identification usable**; that combination is worth having rather
than hiding.

**"Does this discharge `boxGraph_two_iso`?"** That definition was written
with the stated purpose of showing the `d = 2` case IS the estate's box, and
until now nothing consumed it. §2–§3 consume it — strictly, they consume its
two components, `sitePair` and `adj_two_iff`, since the transport wants the
equivalence and the adjacency correspondence separately rather than the
bundled `≃g`. **The bundled object is still unused**, and saying so is more
useful than routing the proof through it for appearances.

**"Even side again — is that hiding something?"** It is the same restriction
as the previous unit and it has the same cause, now visible in a second form:
`isHalf_lowerHalfPair` needs `Even n`, and `GraphHalfSpace.not_isHalf_of_odd`
shows no half exists for odd side. A box of odd side has a fixed row under
`refl n`, so a site reflection cannot split it. **This is not a limitation of
the method but a statement about which reflection is being used**, and the
bond reflection that avoids it is a different operator that this estate has
not defined.

**"Why state the theorem for a family of halves?"** Because the estate's
`def` takes `half` as a parameter, so proving it at one value would be a
weaker result than the `def` invites, and `ReflectionPositive.mono` makes the
stronger form free. It is still not every half: a region that `refl n` does
not carry into its complement is outside the scope, and no claim is made
there.

**"Why is the mirror half a separate theorem rather than a `simp`?"**
Because the estate's `def` is not symmetric in the two arguments of the Green
function: it reads `green n m (refl n p) q`, with the reflection on the left
only. Nothing about the shape of that expression makes the upper half
follow from the lower one; what makes it follow is that `green` is invariant
under `refl` and symmetric, and `ReflectionPositive.mirror` spends both
facts. Had it been symmetry-by-fiat the lemma would not have needed
`IsRefl`.

**"What did it cost?"** The seeded watchlist item guessed "under one unit"
and flagged the guess as a guess. It was one unit, so the guess was low. The
running tally of this project's estimates lives in the progress log, where it
can be counted rather than remembered. The route chosen was the one that
generalises rather than the one that repeats, which is why the file is longer
than the minimum: `reflectionPositive_congr`, `ReflectionPositive.mono` and
`ReflectionPositive.mirror` are statements about arbitrary finite graphs and
will outlive this application.
-/

end LatticeReflectionPositive
