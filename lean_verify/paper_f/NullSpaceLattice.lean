import NullSpaceBoxAny
import LatticeNotStrict
import OS2AnySide

/-!
# The estate's own lattice gets the null space the box just got

`CrossBlockStructure.all_three_thresholds` puts the box, the torus and the estate's own
`Fin n × Fin n` lattice in one statement, so all three have a sharpness threshold. Only two of the
three have a **null space**: `NullSpaceBoxAny` describes the box's at every side length and
`NullSpaceTorusAny` the torus's. The lattice has none, and it is the encoding the physics files
actually use.

It costs a transport rather than an argument, because
`LatticeNotStrict.reflectedForm_lattice_eq` already says the two reflected forms are **equal**
under `BoxGraph.sitePair`. What that equality does not carry is the massive operator, and the null
space is stated in terms of it — so §1 is the missing transport and everything after it is
substitution.

## What is proved

* `massive_mulVec_congr` — **on every pair of finite graphs joined by an adjacency-preserving
  equivalence**: the massive operator commutes with relabelling. `LatticeReflectionPositive`
  transports the matrix (`massive_congr`), the Green function and the quadratic form; it does not
  transport the operator's action on a vector, which is what a null-space statement needs.
* `innerLowerPair` and `map_innerLower` — the box's `innerLower` carried across, in the shape
  `LatticeReflectionPositive.map_lowerHalf` uses for the half.
* `nullSpace_lattice` — at **every** `n`, and this is the statement the file exists for: a family
  on `Fin n × Fin n` supported on the lower half is annihilated by the reflected form **iff** it is
  the massive image of something supported on `innerLowerPair`.
* `mem_nullSub_iff_lattice`, `finrank_nullSub_lattice`, `codim_lattice` — the dimension is
  `(innerLowerPair n).card` and the deficiency is exactly `n`: one line of the lattice, the sites
  with the first coordinate pinned.
* `exists_null_direction_lattice_any` and `not_strict_lattice_any` — **at every parity, from side
  three**, where `LatticeNotStrict.exists_null_direction_lattice` and `not_strict_lattice` carry
  `Even n` and `4 ≤ n`. Those two stay; they are pushed records and they are correct.
* `null_trivial_lattice_iff_side_le_two` and `strict_iff_innerLowerPair_empty`.

## THE THRESHOLD IS NOT NEW

`CrossBlockStructure.lattice_strict_iff_le_two` has had `n ≤ 2` for the lattice since 12 August
2026 (`fceefcc`), by transporting the box's, and it needs no parity and no size hypothesis. This
file does not discover that number, exactly as `NullSpaceBoxAny` does not discover the box's —
`ERRATUM 267` is the entry about the difference between a new number and a new route, and the route
here is the same one: the form is nondegenerate because there is nothing for a null family to be
built from.

## What is NOT here

The lattice's own combinatorics. `innerLowerPair` is defined by transporting the box's set and
`mem_innerLowerPair` states the resulting condition on `p.1`, so nothing below reasons about
`Fin n × Fin n` directly. That is deliberate: the two encodings are equivalent and the estate has
one file whose job is to say so.

## AND A SECTION THAT PROVED TWO THEOREMS THAT ALREADY EXIST

§6 records it rather than hiding it. The draft removed `Even n` from the lattice's reflection
positivity and presented that as work; `OS2AnySide` did it on **2026-08-10** and the watchlist
lists both names. The two duplicates were deleted, the `0 <` twin that motivated them stayed, and
the section now says what happened. `ERRATUM 267` is the entry about announcing an existing result
as new, and the cheap check it asks for — `grep` the NAME before writing it — is the one that was
skipped.

Reflection positivity itself is untouched here: `OS2AnySide.rp_lowerHalfPair_any` says the lattice
form is `≥ 0` at every side, and this file says by how much `≥` fails to be `>`.
-/

namespace NullSpaceLattice

open Finset BoxGraph GraphHalfSpace GraphReflection
open InnerLowerSupport LatticeReflectionPositive NullSpaceDimension

open scoped Matrix

variable {n : ℕ} {m : ℝ}

/-! ## 1. The massive operator commutes with relabelling

`LatticeReflectionPositive.massive_congr` says the matrices agree after `submatrix`. Turning that
into a statement about `*ᵥ` is a reindexing of one sum, and it is the piece the transport chain was
missing — every earlier transport there is about a form or a matrix entry, never about the
operator applied to a vector.
-/

/-- **THE MASSIVE OPERATOR TRANSPORTS.** If `e` matches the adjacencies then relabelling a vector
by `e` and applying `massive` on the target is applying `massive` on the source and relabelling. -/
theorem massive_mulVec_congr {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj] {G' : SimpleGraph W} [DecidableRel G'.Adj]
    (e : V ≃ W) (he : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q) (m : ℝ) (v : V → ℝ) (p : V) :
    (GraphLaplacian.massive G' m *ᵥ fun w => v (e.symm w)) (e p)
      = (GraphLaplacian.massive G m *ᵥ v) p := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp e fun w => GraphLaplacian.massive G' m (e p) w * v (e.symm w)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hmat := congrFun (congrFun (massive_congr (G := G) (G' := G') e he m) p) q
  simp only [Matrix.submatrix_apply] at hmat
  rw [Equiv.symm_apply_apply, hmat]

/-! ## 2. The set, carried across -/

/-- The box's `innerLower` in the lattice's own encoding. -/
def innerLowerPair (n : ℕ) : Finset (IsingFiniteVolume.Site n) :=
  Finset.univ.filter fun p => 2 * p.1.val + 2 < n

theorem mem_innerLowerPair (p : IsingFiniteVolume.Site n) :
    p ∈ innerLowerPair n ↔ 2 * p.1.val + 2 < n := by
  simp [innerLowerPair]

/-- **AND IT IS THE BOX'S SET**, in the shape `map_lowerHalf` uses for the half. -/
theorem map_innerLower (n : ℕ) :
    (innerLower (0 : Fin 2) n).map (sitePair n).toEmbedding = innerLowerPair n := by
  classical
  ext q
  simp only [Finset.mem_map, Equiv.coe_toEmbedding, mem_innerLowerPair]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [mem_innerLower] at hp
    simpa [sitePair] using hp
  · intro hq
    exact ⟨(sitePair n).symm q, mem_innerLower.mpr (by simpa [sitePair] using hq), by simp⟩

theorem innerLowerPair_subset_lowerHalfPair (n : ℕ) :
    innerLowerPair n ⊆ lowerHalfPair n := fun p hp =>
  (mem_lowerHalfPair p).mpr (by rw [mem_innerLowerPair] at hp; omega)

/-! ## 3. The null space -/

/-- **THE NULL SPACE OF THE REFLECTED FORM ON THE ESTATE'S LATTICE, AT EVERY SIDE LENGTH.**

The forms are equal (`LatticeNotStrict.reflectedForm_lattice_eq`), the halves correspond
(`map_lowerHalf`), the sets correspond (`map_innerLower`) and the operator transports (§1), so this
is `NullSpaceBoxAny.nullSpace_box_any` at `d = 2` and `i = 0`, read in the other encoding. -/
theorem nullSpace_lattice (n : ℕ) (hm : m ≠ 0)
    {c : IsingFiniteVolume.Site n → ℝ} (hc : ∀ q, q ∉ lowerHalfPair n → c q = 0) :
    reflectedForm (IsingContourSeparation.latticeGraph n) m (LatticeReflection.refl n) c = 0
      ↔ ∃ v : IsingFiniteVolume.Site n → ℝ, (∀ q, q ∉ innerLowerPair n → v q = 0)
          ∧ GraphLaplacian.massive (IsingContourSeparation.latticeGraph n) m *ᵥ v = c := by
  classical
  have hbox : ∀ p, p ∉ lowerHalf (0 : Fin 2) n → c (sitePair n p) = 0 := by
    intro p hp
    refine hc _ fun hmem => hp ?_
    rw [← map_lowerHalf n] at hmem
    obtain ⟨p', hp', hpe⟩ := Finset.mem_map.mp hmem
    simpa [(sitePair n).injective (by simpa using hpe)] using hp'
  rw [LatticeNotStrict.reflectedForm_lattice_eq (m := m) c,
    NullSpaceBoxAny.nullSpace_box_any (m := m) (0 : Fin 2) n hm hbox]
  constructor
  · rintro ⟨v, hvsupp, hvc⟩
    refine ⟨fun q => v ((sitePair n).symm q), ?_, ?_⟩
    · intro q hq
      refine hvsupp _ fun hmem => hq ?_
      rw [← map_innerLower n]
      exact Finset.mem_map.mpr ⟨(sitePair n).symm q, hmem, by simp⟩
    · funext q
      have := massive_mulVec_congr (sitePair n) (adj_sitePair (n := n)) m v
        ((sitePair n).symm q)
      rw [Equiv.apply_symm_apply] at this
      rw [this, congrFun hvc ((sitePair n).symm q), Equiv.apply_symm_apply]
  · rintro ⟨w, hwsupp, hwc⟩
    refine ⟨fun p => w (sitePair n p), ?_, ?_⟩
    · intro p hp
      refine hwsupp _ fun hmem => hp ?_
      rw [← map_innerLower n] at hmem
      obtain ⟨p', hp', hpe⟩ := Finset.mem_map.mp hmem
      simpa [(sitePair n).injective (by simpa using hpe)] using hp'
    · funext p
      have := massive_mulVec_congr (sitePair n) (adj_sitePair (n := n)) m
        (fun p' => w (sitePair n p')) p
      simp only [Equiv.apply_symm_apply] at this
      rw [← this]
      exact congrFun hwc (sitePair n p)

/-- **THE SAME, AS A DESCRIPTION OF THE SUBMODULE.** -/
theorem mem_nullSub_iff_lattice (n : ℕ) (hm : m ≠ 0) (c : IsingFiniteVolume.Site n → ℝ) :
    c ∈ nullSub (IsingContourSeparation.latticeGraph n) m (innerLowerPair n)
      ↔ (∀ q, q ∉ lowerHalfPair n → c q = 0)
        ∧ reflectedForm (IsingContourSeparation.latticeGraph n) m (LatticeReflection.refl n) c
            = 0 := by
  classical
  constructor
  · intro hcm
    obtain ⟨v, hvsupp, rfl⟩ := mem_nullSub.mp hcm
    have hboxsupp : ∀ p, p ∉ innerLower (0 : Fin 2) n → v (sitePair n p) = 0 := by
      intro p hp
      refine hvsupp _ fun hmem => hp ?_
      rw [← map_innerLower n] at hmem
      obtain ⟨p', hp', hpe⟩ := Finset.mem_map.mp hmem
      simpa [(sitePair n).injective (by simpa using hpe)] using hp'
    have hsupp : ∀ q, q ∉ lowerHalfPair n →
        (GraphLaplacian.massive (IsingContourSeparation.latticeGraph n) m *ᵥ v) q = 0 := by
      intro q hq
      have hb : ((sitePair n).symm q) ∉ lowerHalf (0 : Fin 2) n := by
        intro hmem
        refine hq ?_
        rw [← map_lowerHalf n]
        exact Finset.mem_map.mpr ⟨(sitePair n).symm q, hmem, by simp⟩
      have hz := massive_mulVec_supported (0 : Fin 2) m hboxsupp _ hb
      have ht := massive_mulVec_congr (sitePair n) (adj_sitePair (n := n)) m
        (fun p => v (sitePair n p)) ((sitePair n).symm q)
      simp only [Equiv.apply_symm_apply] at ht
      rw [← hz, ← ht]
    exact ⟨hsupp, (nullSpace_lattice n hm hsupp).mpr ⟨v, hvsupp, rfl⟩⟩
  · rintro ⟨hcsupp, hcnull⟩
    exact mem_nullSub.mpr ((nullSpace_lattice n hm hcsupp).mp hcnull)

/-! ## 4. The dimension and the deficiency -/

theorem finrank_nullSub_lattice (n : ℕ) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (IsingContourSeparation.latticeGraph n) m (innerLowerPair n))
      = (innerLowerPair n).card :=
  NullSpaceDimensionEven.finrank_nullSub hm _

/-- **THE DEFICIENCY IS ONE COLUMN**, which on a two-dimensional lattice of side `n` is `n` sites —
`NullSpaceBoxAny.card_lowerHalf_sdiff_innerLower` at `d = 2`, carried across. -/
theorem card_lowerHalfPair_sdiff_innerLowerPair (n : ℕ) (hn : 0 < n) :
    ((lowerHalfPair n) \ (innerLowerPair n)).card = n := by
  classical
  have h : (lowerHalfPair n) \ (innerLowerPair n)
      = ((lowerHalf (0 : Fin 2) n) \ (innerLower (0 : Fin 2) n)).map (sitePair n).toEmbedding := by
    ext q
    simp only [Finset.mem_sdiff, Finset.mem_map, Equiv.coe_toEmbedding, mem_lowerHalfPair,
      mem_innerLowerPair, lowerHalf, mem_innerLower, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(sitePair n).symm q, ⟨by simpa [sitePair] using h1, by
        intro hc; exact h2 (by simpa [sitePair] using hc)⟩, by simp⟩
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      exact ⟨by simpa [sitePair] using hp1, by
        intro hc; exact hp2 (by simpa [sitePair] using hc)⟩
  rw [h, Finset.card_map, NullSpaceBoxAny.card_lowerHalf_sdiff_innerLower (0 : Fin 2) hn]
  simp

theorem codim_lattice (n : ℕ) (hn : 0 < n) (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (IsingContourSeparation.latticeGraph n) m (innerLowerPair n)) + n
      = Module.finrank ℝ (supportedOn (lowerHalfPair n)) := by
  have h := NullSpaceCodimension.finrank_nullSub_add_card_sdiff (m := m)
    (IsingContourSeparation.latticeGraph n) hm (innerLowerPair_subset_lowerHalfPair n)
  rwa [card_lowerHalfPair_sdiff_innerLowerPair n hn] at h

/-! ## 5. Emptiness, and the threshold from the count -/

theorem innerLowerPair_eq_empty_of_le_two (n : ℕ) (hn : n ≤ 2) : innerLowerPair n = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
  rw [mem_innerLowerPair] at hp
  omega

theorem innerLowerPair_nonempty_iff (n : ℕ) : (innerLowerPair n).Nonempty ↔ 3 ≤ n := by
  classical
  constructor
  · rintro ⟨p, hp⟩
    rw [mem_innerLowerPair] at hp
    omega
  · intro h3
    exact ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), mem_innerLowerPair _ |>.mpr (by simpa using h3)⟩

/-- **A NONZERO NULL FAMILY ON THE LATTICE FROM SIDE THREE, AT EVERY PARITY.**
`LatticeNotStrict.exists_null_direction_lattice` carries `Even n` and `4 ≤ n` because it transports
`BoxNotStrict`'s explicit even-side family; this transports the count instead. -/
theorem exists_null_direction_lattice_any (n : ℕ) (h3 : 3 ≤ n) (hm : m ≠ 0) :
    ∃ c : IsingFiniteVolume.Site n → ℝ, c ≠ 0 ∧ (∀ q, q ∉ lowerHalfPair n → c q = 0)
      ∧ reflectedForm (IsingContourSeparation.latticeGraph n) m
          (LatticeReflection.refl n) c = 0 := by
  classical
  obtain ⟨p, hp⟩ := (innerLowerPair_nonempty_iff n).mpr h3
  have hne : Nontrivial (nullSub (IsingContourSeparation.latticeGraph n) m (innerLowerPair n)) :=
    Module.nontrivial_of_finrank_pos (by
      rw [finrank_nullSub_lattice (m := m) n hm]; exact Finset.card_pos.mpr ⟨p, hp⟩)
  obtain ⟨c, hc0⟩ := exists_ne (0 : nullSub (IsingContourSeparation.latticeGraph n) m
    (innerLowerPair n))
  obtain ⟨hcsupp, hcnull⟩ := (mem_nullSub_iff_lattice n hm _).mp c.2
  exact ⟨c.1, fun h => hc0 (Subtype.ext h), hcsupp, hcnull⟩

/-- **SO THE ESTATE'S OWN LATTICE IS NOT STRICT FROM SIDE THREE, AT EVERY PARITY.** -/
theorem not_strict_lattice_any (n : ℕ) (h3 : 3 ≤ n) (hm : m ≠ 0) :
    ¬ (∀ c : IsingFiniteVolume.Site n → ℝ, c ≠ 0 → (∀ q, q ∉ lowerHalfPair n → c q = 0) →
        0 < reflectedForm (IsingContourSeparation.latticeGraph n) m
              (LatticeReflection.refl n) c) := by
  intro hstrict
  obtain ⟨c, hc0, hcsupp, hcform⟩ := exists_null_direction_lattice_any (m := m) n h3 hm
  exact absurd hcform (ne_of_gt (hstrict c hc0 hcsupp))

/-- **NONDEGENERATE EXACTLY BELOW SIDE THREE.** The number is
`CrossBlockStructure.lattice_strict_iff_le_two`'s and has been since 12 August 2026; what this adds
is that it follows from the size of the null space. -/
theorem null_trivial_lattice_iff_side_le_two (n : ℕ) (hm : m ≠ 0) :
    (∀ c : IsingFiniteVolume.Site n → ℝ, (∀ q, q ∉ lowerHalfPair n → c q = 0) →
        reflectedForm (IsingContourSeparation.latticeGraph n) m (LatticeReflection.refl n) c = 0 →
        c = 0) ↔ n ≤ 2 := by
  classical
  constructor
  · intro h
    by_contra h2
    obtain ⟨c, hc0, hcsupp, hcnull⟩ := exists_null_direction_lattice_any (m := m) n (by omega) hm
    exact hc0 (h c hcsupp hcnull)
  · intro h2 c hcsupp hcnull
    obtain ⟨v, hvsupp, rfl⟩ := (nullSpace_lattice n hm hcsupp).mp hcnull
    have hv0 : v = 0 := funext fun q => hvsupp q (by
      rw [innerLowerPair_eq_empty_of_le_two n h2]; exact Finset.notMem_empty q)
    rw [hv0, Matrix.mulVec_zero]

/-- **STRICT EXACTLY WHEN THERE IS NOTHING TWO LINES IN.** No side length appears. -/
theorem strict_iff_innerLowerPair_empty (n : ℕ) (hm : m ≠ 0) :
    (∀ c : IsingFiniteVolume.Site n → ℝ, (∀ q, q ∉ lowerHalfPair n → c q = 0) →
        reflectedForm (IsingContourSeparation.latticeGraph n) m (LatticeReflection.refl n) c = 0 →
        c = 0)
      ↔ innerLowerPair n = ∅ := by
  classical
  rw [null_trivial_lattice_iff_side_le_two n hm, ← Finset.not_nonempty_iff_eq_empty,
    innerLowerPair_nonempty_iff n]
  omega

/-! ## 6. The `0 <` twin, on reflection positivity that was already there

**THE DRAFT OF THIS SECTION PROVED TWO THEOREMS THAT EXIST, AND THE REVIEW CAUGHT IT** — the
`ERRATUM 267` species, and the reason that entry exists. Writing §5 raised the question of what the
`0 <` form needs, which is reflection positivity at every side; the estate's
`LatticeReflectionPositive.rp_lowerHalfPair` carries `Even n`; and the draft concluded that
substituting `BoxOddReflection.reflectionPositive_box_any` for the even box theorem was work to be
done here. **`OS2AnySide.rp_lowerHalfPair_any` and `reflectionPositive_lattice_any` have been
exactly that substitution since 2026-08-10** (`2b8bbc1`, the day after
`BoxOddReflection.reflectionPositive_box_any` itself, `b01d715`), and `UNLOCK_WATCHLIST`'s `Even n`
block lists both by name under *"REMOVED, no parity hypothesis"*. The draft's two theorems were
deleted; only the twin below is new, and it cites the existing ones.

**The check that would have prevented it is one `grep` for the NAME I was about to write**, which
is cheaper than the paragraph explaining why I wrote it.
-/

/-- **STRICT ON THE HALF, IN THE `0 <` FORM.** Passing from `= 0 → c = 0` to `0 < …` is where
reflection positivity enters, and `OS2AnySide.rp_lowerHalfPair_any` supplies it at every side. -/
theorem strict_iff_innerLowerPair_empty' (n : ℕ) (hm : m ≠ 0) :
    (∀ c : IsingFiniteVolume.Site n → ℝ, c ≠ 0 → (∀ q, q ∉ lowerHalfPair n → c q = 0) →
        0 < reflectedForm (IsingContourSeparation.latticeGraph n) m (LatticeReflection.refl n) c)
      ↔ innerLowerPair n = ∅ := by
  rw [← strict_iff_innerLowerPair_empty n hm]
  constructor
  · intro hs c hcsupp hnull
    by_contra hc0
    exact absurd hnull (ne_of_gt (hs c hc0 hcsupp))
  · intro hs c hc0 hcsupp
    rcases lt_or_eq_of_le (OS2AnySide.rp_lowerHalfPair_any (m := m) n hm c hcsupp) with h | h
    · exact h
    · exact absurd (hs c hcsupp h.symm) hc0

end NullSpaceLattice
