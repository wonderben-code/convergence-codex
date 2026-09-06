import TorusMultiplicity

/-!
# The top is simple too, and so is `Q`'s zero — the same frequency, counted

`TorusMultiplicity` turned every multiplicity on the periodic lattice into a **counting** question
about cosine sums, did that count at the bottom (`ground_state_simple`), and fenced the rest:

> **Nothing below computes a multiplicity at any eigenvalue other than the bottom.** Whether the top
> eigenvalue is simple at even side length is a different count … and **is not proved below**.

It is proved here, and the count at the top is the count at `Q`'s **bottom** — the same frequency
answers both, so one lemma serves twice (`ERRATUM 337`: extract, do not copy).

> **`cos_eq_neg_one_iff_half`** — at side length `2M`, a cosine `cos(2π a / n)` equals `−1` exactly
> at `a = M`. `Real.cos_eq_neg_one_iff` gives `π + 2πj = 2πa/n`; the range `0 ≤ a < 2M` pins the
> integer `j` to `0`. This is the **even** companion to `CycleSpectralBound.cos_ne_neg_one_of_odd`,
> which shows the equation has no solution at odd side length; together they settle the equation
> at every side length, which neither did alone.
>
> **`sum_cos_eq_neg_iff`** — hence the doubled cosine sum reaches its minimum `−2d` **only** at the
> all-halfway frequency. This is the shared lemma: it is what `νR = 4d + m²` says and what
> `νQ = 0` says, and neither operator appears in it.
>
> **`nuR_eq_top_iff` / `top_eigenvalue_simple`** — the greatest eigenvalue `4d + m²` of the massive
> Laplacian at even side length has multiplicity **one**.
>
> **`nuQR_eq_zero_iff` / `signless_zero_simple`** — and `Q = D + A`'s least eigenvalue `0` at even
> side length has multiplicity **one**.

## The second of those has an independent answer in this estate, and they agree

`LaplacianSignlessKernel.card_bipartiteComponent_eq_finrank_ker` says the dimension of `Q`'s kernel
is the number of **two-colourable connected components**, for every finite graph. The periodic
lattice at even side length is connected (`TorusDecay.torusGraph_connected`) and two-colourable
(`TorusBipartite.torusGraph_colorable_two`), so that count is **one** — the same answer
`signless_zero_simple` reaches from a basis of characters and a cosine sum.

**THE TWO ARE NOT DERIVED FROM EACH OTHER AND THIS FILE DOES NOT JOIN THEM.** That theorem computes
`finrank ℝ (ker (toLin' (signlessLap G)))`; `signless_zero_simple` computes
`finrank ℂ (ker (toLin' (cx (signlessLap G)) − 0))`. **Different fields**, and the transfer —
a real matrix's kernel has the same dimension over `ℝ` as its complexification's does over `ℂ` — is
**not proved anywhere in this estate** and is not proved below. `SignlessTorusReal.
real_eigenvalue_iff_cx` transfers *membership* in the spectrum, not the *dimension* of an
eigenspace, and `TorusMultiplicity` fenced exactly this. **So the agreement recorded above is a
consistency observation and not a theorem**, and it is written down because two independent routes
landing on the same number is worth knowing even when neither is a proof of the other.

⚠ **BOTH SENTENCES WENT FALSE ON 2026-08-30 AND ARE KEPT AS WRITTEN** (`ERRATUM 94`; annotated
2026-09-06 by `stalefence_scan`, `ERRATUM 466`, six days late). `RealComplexKernel.finrank_ker_cx`
proves the transfer for an **arbitrary** real matrix —
`finrank ℂ (ker (toLin' (cx A))) = finrank ℝ (ker (toLin' A))` — so it is not "not proved anywhere
in this estate"; and `RealComplexKernel.torus_card_bipComp_eq_one` **joins the two routes**, so the
agreement is a theorem and not only an observation. `RealComplexKernel` annotated its own stale
paragraphs the same day and missed this one, in the file its bridge was built for.

## What is NOT here

**No multiplicity is computed at any interior eigenvalue.** The counting question
`TorusMultiplicity` posed is answered here at the two extreme values and **nowhere else**; whether
frequencies collide in between is combinatorics of `Σᵢ cos(2π kᵢ / n)` and nothing here touches it.

**Nothing is said at odd side length beyond what is already known.** At odd `n` the top `4d + m²`
is not an eigenvalue at all (`TorusSpectrumExtremes.top_not_mem_spectrum_of_odd`) so its
multiplicity is zero and there is nothing to count; and `Q`'s least eigenvalue at odd side length
is **not identified here** — `nuQR` is positive there, but no closed form for its minimum is given,
which is the same fence `CycleSpectralBound` drew at `d = 1`.

**These are dimensions over `ℂ`, and geometric.** As in the previous unit: no claim about real
eigenspaces, no characteristic polynomial, no algebraic multiplicity.

**The box is not reached here.** A boundary and a non-constant degree, so no character family.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusTopSimple

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection LaplacianSignless
open TorusLaplacianSpectrum SignlessTorusSpectrum SignlessTorusComplete SignlessTorusReal
open CycleLaplacianSpectrum SignlessCycleSpectrum
open MassiveTorusSpectrum TorusSpectrumExtremes TorusMultiplicity

variable {d : ℕ}

/-! ## 1. Where a cosine equals `−1`, at even side length -/

/-- **AT SIDE LENGTH `2M` THE COSINE IS `−1` EXACTLY AT `M`.** `Real.cos_eq_neg_one_iff` supplies
an integer `j` with `π + 2πj = 2πa/n`; clearing `π` gives `M·(1 + 2j) = a`, and `0 ≤ a < 2M` forces
`1 + 2j = 1`. The **odd** companion is `CycleSpectralBound.cos_ne_neg_one_of_odd`, which shows the
equation has no solution at all; between them the equation is settled at every side length. -/
theorem cos_eq_neg_one_iff_half {M N : ℕ} (hN : N + 3 = 2 * M) (a : Fin (N + 3)) :
    Real.cos (2 * Real.pi * a.val / ((N : ℝ) + 3)) = -1 ↔ a.val = M := by
  have hM : 0 < M := by omega
  have hcast : ((N : ℝ) + 3) = 2 * M := cast_side hN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  constructor
  · intro hc
    obtain ⟨j, hj⟩ := Real.cos_eq_neg_one_iff.mp hc
    rw [hcast] at hj
    have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMR
    have hpine : Real.pi ≠ 0 := ne_of_gt hpi
    field_simp at hj
    have hreal : (M : ℝ) * (1 + 2 * (j : ℝ)) = (a.val : ℝ) := by linear_combination hj
    have hint : (M : ℤ) * (1 + 2 * j) = (a.val : ℤ) := by exact_mod_cast hreal
    have hMZ : (0 : ℤ) < M := by exact_mod_cast hM
    have hlt : (a.val : ℤ) < 2 * M := by
      have := a.isLt
      omega
    have hub : (M : ℤ) * (1 + 2 * j) < M * 2 := by omega
    have h2 : 1 + 2 * j < 2 := lt_of_mul_lt_mul_left hub (le_of_lt hMZ)
    have hlb : (M : ℤ) * 0 ≤ M * (1 + 2 * j) := by omega
    have h0 : (0 : ℤ) ≤ 1 + 2 * j := le_of_mul_le_mul_left hlb hMZ
    have hj0 : j = 0 := by omega
    rw [hj0] at hint
    omega
  · intro ha
    rw [ha, hcast, angle_at_half M hM, Real.cos_pi]

/-! ## 2. The shared lemma: where the cosine sum bottoms out -/

/-- **THE DOUBLED COSINE SUM REACHES `−2d` ONLY AT THE ALL-HALFWAY FREQUENCY.** Each term is at
least `−2`, so a sum equal to `−2d` forces every term to `−2`; the line above then pins every
coordinate. **Neither operator appears here**, which is why it serves both of them below. -/
theorem sum_cos_eq_neg_iff {M N : ℕ} (hN : N + 3 = 2 * M) (k : Site d (N + 3)) :
    (∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3))) = -(2 * d)
      ↔ k = halfFreq hN := by
  constructor
  · intro hsum
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        (-2 : ℝ) ≤ 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3)) := by
      intro i _
      have := Real.neg_one_le_cos (2 * Real.pi * ((k i).val : ℝ) / ((N : ℝ) + 3))
      linarith
    have hconst : (∑ _i : Fin d, (-2 : ℝ))
        = ∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum]
      ring
    have heach := (Finset.sum_eq_sum_iff_of_le hle).1 hconst
    funext i
    have hcos : Real.cos (2 * Real.pi * ((k i).val : ℝ) / ((N : ℝ) + 3)) = -1 := by
      have := heach i (Finset.mem_univ i)
      linarith
    exact Fin.ext ((cos_eq_neg_one_iff_half hN (k i)).1 hcos)
  · rintro rfl
    have hterm : ∀ i : Fin d,
        2 * Real.cos (2 * Real.pi * ((halfFreq (d := d) hN) i).val / ((N : ℝ) + 3)) = -2 := by
      intro i
      rw [cos_halfFreq hN i]
      ring
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

/-! ## 3. The top of the massive spectrum is simple -/

theorem nuR_eq_top_iff {M N : ℕ} (hN : N + 3 = 2 * M) (m : ℝ) (k : Site d (N + 3)) :
    nuR N m k = 4 * d + m ^ 2 ↔ k = halfFreq hN := by
  rw [← sum_cos_eq_neg_iff hN k, nuR]
  constructor <;> intro h <;> linarith

/-- **THE GREATEST EIGENVALUE IS SIMPLE AT EVEN SIDE LENGTH.** `4d + m²` is reached by the
alternating character and by nothing else, in every dimension. -/
theorem top_eigenvalue_simple {M N : ℕ} (hN : N + 3 = 2 * M) (m : ℝ) :
    Module.finrank ℂ (LinearMap.ker
        (Matrix.toLin' (MatrixLoewner.cx (massive (torusGraph d (N + 3)) m))
          - ((4 * d + m ^ 2 : ℝ) : ℂ) • LinearMap.id)) = 1 := by
  classical
  rw [finrank_eigenspace_massive N m ((4 * d + m ^ 2 : ℝ) : ℂ)]
  have hiff : ∀ k : Site d (N + 3),
      nu N m k = ((4 * d + m ^ 2 : ℝ) : ℂ) ↔ k = halfFreq hN := by
    intro k
    rw [nu_eq_ofReal_nuR, Complex.ofReal_inj]
    exact nuR_eq_top_iff hN m k
  haveI : Unique {k : Site d (N + 3) // nu N m k = ((4 * d + m ^ 2 : ℝ) : ℂ)} :=
    ⟨⟨⟨halfFreq hN, (hiff _).2 rfl⟩⟩, fun x => Subtype.ext ((hiff x.1).1 x.2)⟩
  exact Nat.card_unique

/-! ## 4. And `Q`'s zero is simple, by the same lemma -/

theorem nuQR_eq_zero_iff {M N : ℕ} (hN : N + 3 = 2 * M) (k : Site d (N + 3)) :
    nuQR N k = 0 ↔ k = halfFreq hN := by
  rw [← sum_cos_eq_neg_iff hN k, nuQR]
  constructor <;> intro h <;> linarith

/-- **`Q`'s LEAST EIGENVALUE IS SIMPLE AT EVEN SIDE LENGTH.** Its kernel over `ℂ` is one
dimensional — the alternating character, and nothing else. -/
theorem signless_zero_simple {M N : ℕ} (hN : N + 3 = 2 * M) :
    Module.finrank ℂ (LinearMap.ker
        (Matrix.toLin' (MatrixLoewner.cx (signlessLap (torusGraph d (N + 3))))
          - (0 : ℂ) • LinearMap.id)) = 1 := by
  classical
  rw [finrank_eigenspace_signless N (0 : ℂ)]
  have hiff : ∀ k : Site d (N + 3), nuQ N k = (0 : ℂ) ↔ k = halfFreq hN := by
    intro k
    rw [nuQ_eq_ofReal_nuQR]
    constructor
    · intro h
      exact (nuQR_eq_zero_iff hN k).1 (by exact_mod_cast h)
    · intro h
      rw [(nuQR_eq_zero_iff hN k).2 h]
      norm_num
  haveI : Unique {k : Site d (N + 3) // nuQ N k = (0 : ℂ)} :=
    ⟨⟨⟨halfFreq hN, (hiff _).2 rfl⟩⟩, fun x => Subtype.ext ((hiff x.1).1 x.2)⟩
  exact Nat.card_unique

end TorusTopSimple
