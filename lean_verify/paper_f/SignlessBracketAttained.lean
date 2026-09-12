import SignlessSpectrumTrichotomy
import GraphIsoSignlessSpectrum

/-!
# The bracket's upper bound is attained, at the smallest graph that could attain it

`SignlessSpectrumTrichotomy` proved that `Q`'s distinct eigenvalues on a complete multipartite graph
number between `s` and `3s`, with `s` the number of distinct part sizes, and fenced the obvious
question: *"**`3s` IS NOT CLAIMED TO BE ATTAINED.** No graph is exhibited where the eigenvalues
number `3s`, and the `K_{1,3,3}` of entry 173 has `s = 2` with three eigenvalues, comfortably inside
the bracket. Whether the upper bound is ever tight is open."* **It is tight, and the witness is
`K_{2,2}`.**

**Why that graph and why it is not a coincidence.** The factor of three in the bracket is the
trichotomy: every eigenvalue is a part value, a pole, or a secular root. Tightness needs all three
families non-empty **and disjoint**. At `K_{2,2}` — `N = 4`, one distinct part size, so `s = 1` and
`3s = 3` — the part value is `N − n = 2`, the pole is `N − 2n = 0`, and `4` is neither, so it is a
secular root; and `0 ≠ 2 ≠ 4`. Three families, one eigenvalue each, nothing shared. **The smallest
balanced graph is the tight one**, which is worth saying because the chain's earlier witnesses were
all unbalanced and all slack.

## What is proved

> **`signlessLap_mulVec_one_of_regular`** — on a `k`-regular graph the all-ones vector is an
> eigenvector of `Q` at `2k`, from `GraphIsoSignlessSpectrum.signlessLap_mulVec_apply`: the diagonal
> contributes `deg v` and the neighbour sum contributes `deg v` again. **General, and the estate did
> not have it** — `SignlessRegularSimple` relates `Q`'s kernel to the Laplacian's on a regular graph
> and says nothing about the top of the spectrum.
>
> **`isEigen_four`** — hence `4` at `K_{2,2}`, which is `2 · 2`.
>
> **`isEigen_zero`** — `0`, from `SecularPoleNotPartValue.finrank_signless_balanced_two_zero` at
> `t = 2` (the kernel is a line, both parts being half-sized) through
> `UnbalancedMultipartiteSecularEquation.isEigenvector_iff_finrank_pos`, whose generalisation from
> `ℝ` to an arbitrary field earlier the same day is what lets it be used as a bridge here.
>
> **`isEigen_two`** — `2`, from `UnbalancedMultipartiteSecular.finrank_signless_size_eq`: the part
> value `N − n` at `n = 2` has multiplicity `k₂·(n − 1) + …` with `k₂ = 2`, so at least two, so
> positive. **No eigenvector is written down for it**; the multiplicity theorem supplies one.
>
> **`bracket_attained`** — so `S.card = 3 = 3s`. The proof needs no computation of the spectrum:
> the bracket gives `S.card ≤ 3`, the three eigenvalues give `3 ≤ S.card`, and that is the whole
> argument.
>
> **`spectrum_B22`** — and therefore the spectrum **is** `{0, 2, 4}` exactly, by cardinality against
> the inclusion. `Q` on `K_{2,2}` has three distinct eigenvalues and this names them.

## What is NOT here

* **NO CLAIM THAT `3s` IS ATTAINED FOR ANY OTHER `s`.** One witness at `s = 1`. Whether every `s`
  admits a tight graph — the natural guess being a balanced graph with `s` distinct sizes — is
  **open, not attempted, no cost claimed** (`ERRATUM 246`). The fence in
  `SignlessSpectrumTrichotomy` is closed for the question it asks (*"whether the upper bound is ever
  tight"*) and not for the stronger one.
* **NO MULTIPLICITIES HERE, AND THE POLYNOMIAL IS ALREADY IN THE ESTATE ONE ISOMORPHISM AWAY.**
  `bracket_attained` and `spectrum_B22` count **distinct** eigenvalues.
  `MultipartiteSignlessCharpoly.charpoly_signlessLap_multi` gives `Q`'s characteristic polynomial on
  the equipartite family, and at `r = t = 2` it reads `(X − 4)·X·(X − 2)²` — the same three values
  with multiplicities `1, 1, 2`. **It is stated for `completeEquipartiteGraph r t`, which lives on
  `Fin r × Fin t`, while this file's graph is indexed by a sigma type**, so carrying it across needs
  `GraphIsoSignlessSpectrum.charpoly_signlessLap_iso` against
  `completeEquipartiteGraph.completeMultipartiteGraph`. That is a transport and not a computation,
  and it is **not done here** (`ERRATUM 246`). Nothing above depends on it: the bracket argument
  never touches a polynomial.
* **NO GENERAL CHARACTERISATION OF TIGHTNESS.** What makes the three families disjoint here is
  arithmetic at one graph; the fence's other clause — *what the overlaps are in general* — is
  untouched, and `SignlessSpectrumTrichotomy`'s `pole_isEigen_iff` and entry 157's criterion still
  decide the cases one at a time without being assembled.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is `OS0`, `OS1`
  and `OS4` in their continuum senses, and `OS4`'s finite-volume shadow is empty on the box.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances; `signlessLap_mulVec_one_of_regular` takes a graph, a `DecidableRel` and
`IsRegularOfDegree k` and **nothing else** — no connectivity, no multipartiteness; the three
eigenvalue statements are about one concrete graph and take nothing. **No mass, no propagator, no
metric.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace BracketAttained

open Matrix Finset SimpleGraph LaplacianSignless SignlessSpectrumTrichotomy

/-- `K_{2,2}`: two parts of two. -/
abbrev B22 : Fin 2 → Type := fun _ => Fin 2

theorem card_B22 : Fintype.card (Σ i, B22 i) = 4 := by decide

theorem regular_B22 : (completeMultipartiteGraph B22).IsRegularOfDegree 2 := by
  intro v
  revert v
  decide

/-! ## 1. The all-ones vector: `2k` is an eigenvalue of a regular graph's `Q` -/

theorem signlessLap_mulVec_one_of_regular {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph W} [DecidableRel G.Adj] {k : ℕ} (hk : G.IsRegularOfDegree k) :
    signlessLap G *ᵥ (fun _ => (1 : ℝ)) = (2 * k : ℝ) • (fun _ => (1 : ℝ)) := by
  funext v
  rw [GraphIsoSignlessSpectrum.signlessLap_mulVec_apply]
  simp [hk v, SimpleGraph.card_neighborFinset_eq_degree]
  ring

open UnbalancedMultipartite UnbalancedMultipartiteSecular

/-! ## 2. Three eigenvalues of `K_{2,2}` -/

theorem isEigen_four : IsEigen B22 4 := by
  refine ⟨fun _ => (1 : ℝ), ?_, ?_⟩
  · intro h
    have := congrFun h ⟨0, 0⟩
    norm_num at this
  · rw [signlessLap_mulVec_one_of_regular regular_B22]
    norm_num

theorem isEigen_zero : IsEigen B22 0 := by
  rw [IsEigen, UnbalancedMultipartiteSecularEquation.isEigenvector_iff_finrank_pos]
  rw [SecularPoleNotPartValue.finrank_signless_balanced_two_zero (t := 2) (by norm_num)]
  norm_num

theorem isEigen_two : IsEigen B22 2 := by
  rw [IsEigen, UnbalancedMultipartiteSecularEquation.isEigenvector_iff_finrank_pos]
  have hcard : ((Fintype.card (Σ i, B22 i) : ℝ) - (2 : ℕ)) = 2 := by
    rw [card_B22]; norm_num
  rw [← hcard, finrank_signless_size_eq (V := B22) (n := 2) (by norm_num)
    (by rw [card_B22]; norm_num) (fun _ => ⟨0⟩)]
  have h2 : Fintype.card {i : Fin 2 // Fintype.card (B22 i) = 2} = 2 := by decide
  rw [h2]
  norm_num

/-! ## 3. So the upper bound of the bracket is attained -/

theorem sizes_card_one :
    (Finset.univ.image (fun i : Fin 2 => Fintype.card (B22 i))).card = 1 := by decide

theorem bracket_attained :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen B22 μ)
      ∧ S.card = 3 * (Finset.univ.image (fun i : Fin 2 => Fintype.card (B22 i))).card := by
  classical
  obtain ⟨S, hS, _, hhigh⟩ := exists_spectrum_bracket (V := B22) (fun _ => ⟨0⟩) ⟨0⟩
  refine ⟨S, hS, ?_⟩
  rw [sizes_card_one] at hhigh ⊢
  have hsub : ({0, 2, 4} : Finset ℝ) ⊆ S := by
    intro μ hμ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hμ
    rcases hμ with rfl | rfl | rfl
    · exact (hS 0).mpr isEigen_zero
    · exact (hS 2).mpr isEigen_two
    · exact (hS 4).mpr isEigen_four
  have hthree : ({0, 2, 4} : Finset ℝ).card = 3 := by norm_num
  have := Finset.card_le_card hsub
  omega

/-- **AND SO THE SPECTRUM IS EXACTLY `{0, 2, 4}`**, by cardinality against the inclusion. -/
theorem spectrum_B22 (μ : ℝ) : IsEigen B22 μ ↔ μ = 0 ∨ μ = 2 ∨ μ = 4 := by
  classical
  obtain ⟨S, hS, hcard⟩ := bracket_attained
  rw [sizes_card_one] at hcard
  have hsub : ({0, 2, 4} : Finset ℝ) ⊆ S := by
    intro ν hν
    simp only [Finset.mem_insert, Finset.mem_singleton] at hν
    rcases hν with rfl | rfl | rfl
    · exact (hS 0).mpr isEigen_zero
    · exact (hS 2).mpr isEigen_two
    · exact (hS 4).mpr isEigen_four
  have hthree : ({0, 2, 4} : Finset ℝ).card = 3 := by norm_num
  have heq : S = ({0, 2, 4} : Finset ℝ) :=
    (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  rw [← hS, heq]
  simp

end BracketAttained
