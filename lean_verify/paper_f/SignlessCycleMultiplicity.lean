/-
  SignlessCycleMultiplicity.lean — the ring's signless eigenspaces, counted.

  WHY THIS FILE EXISTS, AND THE RECORD SAID SO. `UNLOCK_WATCHLIST`'s
  simplicity-transfer block, STATUS entry 29, records the odd cycle this way:

    ⚠ the reading is that `k ↦ N − k` collides in both of the estate's formulas,
      `2 ± 2cos(2πk/N)`, so both spectra are degenerate — **arithmetic about two
      proved formulas, not formalised as a multiplicity statement.**

  Half of that is now formalised on the Laplacian side and none of it on the
  signless side. `CycleMultiplicityCount.finrank_eigenspace_interior_eq_two`
  counts the massive Laplacian's interior fibres and gets `2`;
  `TorusRealMultiplicity.finrank_eigenspace_signless_real` reduces the signless
  multiplicity to a fibre cardinality in every dimension, **and no file counts a
  signless fibre**. The estate's exact signless multiplicities — 95 of them,
  counted for `ERRATUM 541` — cover the box, the complete graph, the multipartite
  family, the paw, several named small graphs, and the torus only at its
  EXTREMES (`TorusRealMultiplicity.signless_zero_simple_real`, the eigenvalue `0` at even
  side length). The interior of the ring is not among them. **That count is what
  chose this unit**, and running it before starting is the whole of what
  `ERRATUM 541` asks for.

  WHAT THIS FILE PROVES.

  1. `nuQR_eq_iff_one` — two frequencies of the ring share a signless eigenvalue
     exactly when they agree or reflect, `k' = k` or `k' + k = n`. **The same
     criterion the Laplacian has**, because both eigenvalue formulas depend on the
     frequency only through `cos(2πk/n)`; the proof is
     `CycleMultiplicity.cos_angle_eq_iff` — which mentions no operator — with the
     sign of the cosine flipped, and the flip is a `linarith`.
  2. `fibre_signless_eq_pair`, `ne_mirrorFreq_signless`,
     **`card_fibre_signless_eq_two`** — at an interior frequency (`0 < k` and
     `2k ≠ n`) the fibre is exactly `{k, n − k}`, a pair.
  3. **`finrank_eigenspace_signless_interior_eq_two`** — so the interior signless
     eigenspaces of the ring are two dimensional, in every side length.
  4. `card_fibre_signless_zero_eq_one`, **`finrank_eigenspace_signless_zero_eq_one`**
     — and at `k = 0` the fibre is a singleton, so `Q`'s largest eigenvalue on the
     ring, `4`, is simple. The frequency `0` is excluded from item 3 for a reason
     and this says what the reason costs.
  5. **`odd_cycle_signless_all_multiplicities`** — on an ODD cycle `2k = n` is
     impossible, so items 3 and 4 between them settle **every** frequency: the top
     is simple and everything else is a two-dimensional eigenspace. That is the
     ⚠ reading above, formalised.

  WHAT IS NOT CLAIMED. **Nothing about the EVEN cycle's half frequency.** At
  `2k = n` the fibre is a singleton too and the eigenvalue is `0`, but that case is
  `TorusRealMultiplicity.signless_zero_simple_real` and is not restated here — item 5 is
  stated for odd `n` precisely so that it does not overlap it. **No count of
  DISTINCT eigenvalues** is given, and item 5 is not "the spectrum of the odd
  cycle": it assigns a multiplicity to each frequency and does not say that
  distinct frequency-pairs give distinct eigenvalues — though `nuQR_eq_iff_one`
  is exactly the tool for that and the omission is bookkeeping nothing consumes
  (`ERRATUM 246`). **Nothing here is about `d ≥ 2`**; the reduction
  `finrank_eigenspace_signless_real` holds in every dimension and the counting
  does not, for the same reason the Laplacian counting does not.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import CycleMultiplicityCount
import SignlessTorusReal
import TorusRealMultiplicity

namespace SignlessCycleMultiplicity

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection LaplacianSignless
open MassiveTorusSpectrum TorusRealMultiplicity CycleMultiplicity
open SignlessTorusReal CycleMultiplicityCount

noncomputable section

/-! ## 1. The collision criterion, for `Q` -/

/-- **TWO FREQUENCIES SHARE A SIGNLESS EIGENVALUE ON THE RING EXACTLY WHEN THEY
AGREE OR REFLECT.** Identical to `CycleMultiplicity.nuR_eq_iff_one`'s conclusion,
and for a reason worth naming: `νR = 2 + m² − 2cos θ` and `νQR = 2 + 2cos θ` differ
in the sign of the cosine and in a constant, and neither of those can change when
two angles have equal cosines. `cos_angle_eq_iff` carries all of it. -/
theorem nuQR_eq_iff_one (N : ℕ) (k k' : Site 1 (N + 3)) :
    nuQR N k' = nuQR N k
      ↔ (k' 0).val = (k 0).val ∨ (k' 0).val + (k 0).val = N + 3 := by
  have hcast : ((N : ℝ) + 3) = ((N + 3 : ℕ) : ℝ) := by push_cast; ring
  have hpos : 0 < N + 3 := by omega
  have hexp : ∀ j : Site 1 (N + 3),
      nuQR N j = 2 * (1 : ℕ) + 2 * Real.cos (2 * Real.pi * (j 0).val / ((N : ℝ) + 3)) := by
    intro j
    rw [nuQR, Fin.sum_univ_one]
  rw [hexp k, hexp k']
  constructor
  · intro h
    have hc : Real.cos (2 * Real.pi * (k' 0).val / ((N + 3 : ℕ) : ℝ))
        = Real.cos (2 * Real.pi * (k 0).val / ((N + 3 : ℕ) : ℝ)) := by
      rw [← hcast]
      linarith
    exact (cos_angle_eq_iff hpos (k' 0).isLt (k 0).isLt).1 hc
  · intro h
    have hc : Real.cos (2 * Real.pi * (k' 0).val / ((N + 3 : ℕ) : ℝ))
        = Real.cos (2 * Real.pi * (k 0).val / ((N + 3 : ℕ) : ℝ)) :=
      (cos_angle_eq_iff hpos (k' 0).isLt (k 0).isLt).2 h
    rw [← hcast] at hc
    linarith

/-! ## 2. So an interior fibre is a pair -/

/-- The signless fibre at an interior frequency is `{k, n − k}`. `mirrorFreq` and
its arithmetic are `CycleMultiplicityCount`'s and are reused unchanged: they are
statements about frequencies and name no operator. -/
theorem fibre_signless_eq_pair (N : ℕ) (k : Site 1 (N + 3))
    (hk0 : 0 < (k 0).val) (hkhalf : 2 * (k 0).val ≠ N + 3) :
    {k' : Site 1 (N + 3) | nuQR N k' = nuQR N k} = {k, mirrorFreq k} := by
  ext k'
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [nuQR_eq_iff_one]
  constructor
  · rintro (h | h)
    · exact Or.inl (site_one_ext h)
    · refine Or.inr (site_one_ext ?_)
      rw [mirrorFreq_val k hk0]
      omega
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · right
      rw [mirrorFreq_val k hk0]
      omega

/-- **SO THE SIGNLESS FIBRE HAS TWO ELEMENTS.** -/
theorem card_fibre_signless_eq_two (N : ℕ) (k : Site 1 (N + 3))
    (hk0 : 0 < (k 0).val) (hkhalf : 2 * (k 0).val ≠ N + 3) :
    Nat.card {k' : Site 1 (N + 3) // nuQR N k' = nuQR N k} = 2 := by
  have hcoe : Nat.card {k' : Site 1 (N + 3) // nuQR N k' = nuQR N k}
      = Set.ncard {k' : Site 1 (N + 3) | nuQR N k' = nuQR N k} :=
    Nat.card_coe_set_eq _
  rw [hcoe, fibre_signless_eq_pair N k hk0 hkhalf,
    Set.ncard_pair (ne_mirrorFreq k hk0 hkhalf)]

/-- **THE INTERIOR SIGNLESS EIGENSPACES OF THE RING ARE TWO DIMENSIONAL.** The
reduction to a fibre count is `TorusRealMultiplicity`'s and holds in every
dimension; the count is this file's and holds at `d = 1`. -/
theorem finrank_eigenspace_signless_interior_eq_two (N : ℕ) (k : Site 1 (N + 3))
    (hk0 : 0 < (k 0).val) (hkhalf : 2 * (k 0).val ≠ N + 3) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap (torusGraph 1 (N + 3)))
          - (nuQR N k) • LinearMap.id)) = 2 := by
  rw [finrank_eigenspace_signless_real N (nuQR N k)]
  exact card_fibre_signless_eq_two N k hk0 hkhalf

/-! ## 3. And the frequency `0` is a singleton, which is why it is excluded above -/

/-- At `k = 0` the reflection clause `k' + 0 = n` cannot hold, every `k'` being
below `n`, so the fibre collapses to `{0}`. -/
theorem fibre_signless_zero_eq_singleton (N : ℕ) :
    {k' : Site 1 (N + 3) | nuQR N k' = nuQR N (0 : Site 1 (N + 3))} = {0} := by
  ext k'
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [nuQR_eq_iff_one]
  constructor
  · rintro (h | h)
    · refine site_one_ext (k := (0 : Site 1 (N + 3))) ?_ ▸ rfl
      simpa using h
    · exact absurd h (by have := (k' 0).isLt; simp; omega)
  · rintro rfl
    exact Or.inl rfl

theorem card_fibre_signless_zero_eq_one (N : ℕ) :
    Nat.card {k' : Site 1 (N + 3) // nuQR N k' = nuQR N (0 : Site 1 (N + 3))} = 1 := by
  have hcoe : Nat.card {k' : Site 1 (N + 3) // nuQR N k' = nuQR N (0 : Site 1 (N + 3))}
      = Set.ncard {k' : Site 1 (N + 3) | nuQR N k' = nuQR N (0 : Site 1 (N + 3))} :=
    Nat.card_coe_set_eq _
  rw [hcoe, fibre_signless_zero_eq_singleton N, Set.ncard_singleton]

/-- **`Q`'s LARGEST EIGENVALUE ON THE RING IS SIMPLE.** `TorusSpectrumExtremes`
gives `nuQR N 0 = 4` and `nuQR N k ≤ 4`; this gives its multiplicity. -/
theorem finrank_eigenspace_signless_zero_eq_one (N : ℕ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap (torusGraph 1 (N + 3)))
          - (nuQR N (0 : Site 1 (N + 3))) • LinearMap.id)) = 1 := by
  rw [finrank_eigenspace_signless_real N (nuQR N (0 : Site 1 (N + 3)))]
  exact card_fibre_signless_zero_eq_one N

/-! ## 4. On an odd cycle that is every frequency -/

/-- **THE ODD CYCLE'S SIGNLESS MULTIPLICITIES, ALL OF THEM.** When `n` is odd
`2k = n` is impossible, so `§2` covers every non-zero frequency and `§3` covers
the remaining one: the top is simple and every other eigenspace is a plane. This
is the `⚠` reading `UNLOCK_WATCHLIST` entry 29 recorded as *"arithmetic about two
proved formulas, not formalised as a multiplicity statement"*. -/
theorem odd_cycle_signless_all_multiplicities (M : ℕ) (k : Site 1 (2 * M + 3)) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap (torusGraph 1 (2 * M + 3)))
          - (nuQR (2 * M) k) • LinearMap.id))
      = if (k 0).val = 0 then 1 else 2 := by
  by_cases hk0 : (k 0).val = 0
  · rw [if_pos hk0]
    have hk : k = (0 : Site 1 (2 * M + 3)) := site_one_ext (by simpa using hk0)
    rw [hk]
    exact finrank_eigenspace_signless_zero_eq_one (2 * M)
  · rw [if_neg hk0]
    exact finrank_eigenspace_signless_interior_eq_two (2 * M) k
      (Nat.pos_of_ne_zero hk0) (by omega)

/-! ## 5. Review round 62 — the ways this could be hollow

**"§1 is `nuR_eq_iff_one` with a sign changed."** It is, and the docstring says so
rather than presenting the transcription as work. What is worth recording is WHY
the criterion survives the change: both eigenvalue functions factor through
`cos(2πk/n)`, and `cos_angle_eq_iff` — the file's only real content, and
`CycleMultiplicity`'s — mentions no operator at all. A sign and a constant cannot
disturb an equality of cosines.

**"§2 could be `CycleMultiplicityCount` with `nuR` replaced by `nuQR`."** §2 is;
`mirrorFreq`, `mirrorFreq_val`, `site_one_ext` and `ne_mirrorFreq` are imported and
not restated, for the same reason. The unit is §1 plus the observation that the
whole of `CycleMultiplicityCount` above `nuR_eq_iff_one` is operator-free — which
is a fact about that file, checked by reading it, not assumed.

**"The count might already exist."** It does not, and this was checked before the
file was written rather than after, which is `ERRATUM 541`'s rule: 95 exact
signless multiplicities across 30 files, none of them a torus interior. The torus
appears there only at its extremes.

**"§4 might overlap the even case."** It is stated at `2 * M + 3`, which is odd, so
it does not reach the half frequency at all — where the fibre is also a singleton
and the eigenvalue is `0`, and where `TorusRealMultiplicity.signless_zero_simple_real`
already answers. Stating §4 for all `n` would have duplicated that theorem, which
is the mistake `ERRATUM 541` is about.

**"§4 could be read as the spectrum of the odd cycle."** It cannot and the header
says so: it gives a multiplicity per FREQUENCY, and does not claim that different
frequency-pairs carry different eigenvalues. `nuQR_eq_iff_one` is exactly the tool
for that step and nothing here takes it.
-/

end

end SignlessCycleMultiplicity
