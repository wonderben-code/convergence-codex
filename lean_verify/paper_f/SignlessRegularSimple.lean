import SignlessSimpleFamilies

/-!
# On a regular graph too, and so where a separating graph would have to live

**ENTRY 178 PROVED THE TWO QUESTIONS COINCIDE ON A TWO-COLOURABLE GRAPH AND ASKED WHETHER THEY EVER
DIFFER.** They do not differ on a regular graph either, and the reason is already in this estate:
`LaplacianTopEigenspace.signlessLap_eq_of_regular` proves `Q = 2Δ • 1 − L` on a `Δ`-regular graph.
That file uses it **only at the top eigenvalue** — its whole subject is the multiplicity of `2Δ`,
which is `Q`'s kernel. **At every `μ` the same identity is a reindexing of the entire spectrum**,
and that had not been written.

## What is proved

**`ker_signless_eq_ker_lap_of_regular`, `finrank_signless_eq_finrank_lap_of_regular`** — on a
`Δ`-regular graph, `Q`'s eigenspace at `μ` **is** `L`'s eigenspace at `2Δ − μ`, the same subspace
and not merely the same dimension, because the two operators differ by a sign.

**`finrank_signless_le_one_iff_lap_of_regular`, `nodup_signless_iff_lap_of_regular`** — so on a
regular graph the signless simple-spectrum question and the Laplacian one are the same question,
**by a reindexing rather than by a conjugation, and with no two-colourability anywhere**.

**`nodup_signless_iff_lap_of_regular_or_colorable`** — the two halves in one statement, and what
they say together: **a graph on which the two questions have different answers is neither regular
nor two-colourable.** Entry 178 supplied the second half.

**`torusGraph_one_isRegular`, `not_finrank_signless_le_one_cycle`,
`not_nodup_roots_charpoly_signlessLap_cycle`** — **and the instance entry 178's transport could not
reach**: the cycle, at every length. It is `torusGraph 1 (N+3)`, two-regular, and its Laplacian
spectrum fails by `FieldSimpleConnected.not_finrank_lapMatrix_le_one_torus`; **at odd `N + 3` it is
not two-colourable**, so the conjugation says nothing and the reindexing settles it.

## What is NOT here

* **STILL NO SEPARATING GRAPH**, and the narrowing does not empty the search: *neither regular nor
  two-colourable* leaves plenty, and the two such graphs whose signless spectra this chain knows —
  the paw and `K_{1,3,3}` — do not separate the questions, the paw having a simple spectrum on both
  sides. **Whether the two can differ at all is exactly as open as it was.** Not attempted
  (`ERRATUM 246`).
* **NOTHING IS COMPUTED**, as in entry 178: both halves are transport, and the one new identity is
  four lines on top of a theorem that was already there.
* **`torusGraph_one_isRegular` DOES NOT DE-DUPLICATE ANYTHING.** Four files prove the `cycleGraph`
  form of this fact inline — `CycleNormFromColouring`, `LaplacianLoewnerConverse`,
  `LaplacianSharpEquality` and `RegularBipartiteSharp`, each as a local `have` with no shared
  lemma. That is the *six declarations of one fact* item's mechanism in a fourth chain, **and in a
  form its census cannot see**, because a `have` inside a proof is not a declaration. The four are
  upstream of this file and naming the fact here does not reach them; the de-duplication is still
  that item's, and still unstarted.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0`
  and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the estate's `Fintype`, `DecidableEq` and
`DecidableRel` instances; `G.IsRegularOfDegree Δ` on everything in §1, which is all the reindexing
needs; and on the cycle, nothing beyond the side length being at least three, which `torusGraph`'s
`N + 3` supplies. **No mass, no propagator, and no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessRegularSimple

open Matrix SimpleGraph LaplacianSignless

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **`Q`'s EIGENSPACE AT `μ` IS `L`'s AT `2Δ − μ`**, at every `μ` and not only at the top. -/
theorem ker_signless_eq_ker_lap_of_regular {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (μ : ℝ) :
    LinearMap.ker (Matrix.toLin' (signlessLap G) - μ • LinearMap.id)
      = LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - ((2 * Δ : ℝ) - μ) • LinearMap.id) := by
  have h : Matrix.toLin' (signlessLap G) - μ • LinearMap.id
      = -(Matrix.toLin' (G.lapMatrix ℝ) - ((2 * Δ : ℝ) - μ) • LinearMap.id) := by
    rw [LaplacianTopEigenspace.signlessLap_eq_of_regular G hreg, map_sub, map_smul,
      Matrix.toLin'_one]
    ext x i
    simp [sub_smul]
    ring
  rw [h]
  ext x
  simp only [LinearMap.mem_ker, LinearMap.neg_apply, neg_eq_zero]

theorem finrank_signless_eq_finrank_lap_of_regular {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G) - μ • LinearMap.id))
      = Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (G.lapMatrix ℝ) - ((2 * Δ : ℝ) - μ) • LinearMap.id)) := by
  rw [ker_signless_eq_ker_lap_of_regular G hreg μ]

/-- **SO ON A REGULAR GRAPH TOO THE TWO QUESTIONS ARE THE SAME QUESTION**, by a reindexing rather
than by a conjugation, and with no two-colourability anywhere. -/
theorem finrank_signless_le_one_iff_lap_of_regular {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) :
    (∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap G) - μ • LinearMap.id)) ≤ 1)
      ↔ (∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) := by
  constructor
  · intro h ν
    have hh := h ((2 * Δ : ℝ) - ν)
    rw [finrank_signless_eq_finrank_lap_of_regular G hreg,
      show (2 * (Δ : ℝ)) - ((2 * Δ : ℝ) - ν) = ν by ring] at hh
    exact hh
  · intro h μ
    rw [finrank_signless_eq_finrank_lap_of_regular G hreg]
    exact h _

theorem nodup_signless_iff_lap_of_regular {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) :
    (signlessLap G).charpoly.roots.Nodup ↔ (G.lapMatrix ℝ).charpoly.roots.Nodup := by
  rw [SimpleSpectrumCharpoly.nodup_roots_charpoly_signlessLap_iff,
    SimpleSpectrumCharpoly.nodup_roots_charpoly_lapMatrix_iff,
    ← FieldSimpleConverse.finrank_lapMatrix_le_one_iff_injective]
  exact finrank_signless_le_one_iff_lap_of_regular G hreg

/-- **SO A GRAPH SEPARATING THE TWO QUESTIONS IS NEITHER REGULAR NOR TWO-COLOURABLE.** Entry 178
did the two-colourable half by conjugation; this is the regular half by reindexing. -/
theorem nodup_signless_iff_lap_of_regular_or_colorable
    (h : (∃ Δ : ℕ, G.IsRegularOfDegree Δ) ∨ G.Colorable 2) :
    (signlessLap G).charpoly.roots.Nodup ↔ (G.lapMatrix ℝ).charpoly.roots.Nodup := by
  rcases h with ⟨Δ, hreg⟩ | hcol
  · exact nodup_signless_iff_lap_of_regular G hreg
  · exact SignlessSimpleFamilies.nodup_signless_iff_lap_of_colorable hcol

/-! ## 2. The instance the two-colourable transport cannot reach: the cycle at odd length -/

/-- **THE CYCLE'S SIGNLESS SPECTRUM IS NOT SIMPLE, AT EVERY LENGTH.** The cycle is
`torusGraph 1 (N+3)`, two-regular by `RegularSelfEmbedding.torusGraph_isRegularOfDegree`, and its
Laplacian spectrum fails by `FieldSimpleConnected.not_finrank_lapMatrix_le_one_torus`. **At odd
`N + 3` the graph is not two-colourable**, so entry 178's conjugation does not reach it and this
reindexing does. -/
theorem torusGraph_one_isRegular (N : ℕ) :
    (TorusReflection.torusGraph 1 (N + 3)).IsRegularOfDegree 2 := by
  simpa using RegularSelfEmbedding.torusGraph_isRegularOfDegree (d := 1) (n := N + 3) (by omega)

theorem not_finrank_signless_le_one_cycle (N : ℕ) :
    ¬ (∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap (TorusReflection.torusGraph 1 (N + 3)))
          - μ • LinearMap.id)) ≤ 1) := by
  intro h
  exact FieldSimpleConnected.not_finrank_lapMatrix_le_one_torus le_rfl N
    ((finrank_signless_le_one_iff_lap_of_regular _ (torusGraph_one_isRegular N)).mp h)

theorem not_nodup_roots_charpoly_signlessLap_cycle (N : ℕ) :
    ¬ (signlessLap (TorusReflection.torusGraph 1 (N + 3))).charpoly.roots.Nodup := by
  rw [SimpleSpectrumCharpoly.nodup_roots_charpoly_signlessLap_iff]
  exact not_finrank_signless_le_one_cycle N

end SignlessRegularSimple
