/-
  GraphReflection.lean — reflection positivity for an arbitrary graph with an
  arbitrary involutive automorphism, and the four-dimensional reflection this
  campaign twice declared easy and did not write.

  WHY. Two things at once, and they are the same thing.

  **One.** `LatticeReflectionSplit` proved, an hour ago, that reflection
  positivity is a comparison of two ordinary energies. It is stated for
  `Site n = Fin n × Fin n` and `LatticeReflection.refl`, and **no step of it
  uses either** — the inputs are that the reflection is an involutive graph
  automorphism and that `green` is symmetric. `PROOF_STRATEGY` §7 rule 3 says
  remove the fence.

  **Two, and it is the check ERRATUM 48 asks for.** `BoxGraph` says of the
  four-dimensional box: *"the analogue on `Fin d → Fin n` is easy to write
  and this file does not write it — a statement about what was done, not
  about difficulty."* A claim that something is easy is a claim, and the
  check is to do it. §5 does it.

  WHAT THIS FILE PROVES:
  1. **`green_aut`** — for any involutive automorphism `θ` of any finite
     simple graph, the massive Green function satisfies
     `green (θ p) (θ q) = green p q`. Generalises
     `LatticeReflection.green_refl`, whose proof needed the box only for its
     degree lemma.
  2. **`reflectedForm_eq`** — `4·R(c) = Q(sym c) − Q(anti c)` over an
     arbitrary graph and automorphism.
  3. **`ReflectionPositive`, `reflectionPositive_iff_energy_le`** — the
     property and the energy comparison, now sayable for any graph.
  4. **`reflectionPositive_box`** — the box case is an instance: the general
     property at `(latticeGraph n, refl n)` is `LatticeReflection`'s, by
     `Iff.rfl`.
  5. **`revSite`, `boxGraph_revSite_aut`** — **the reflection in ANY
     coordinate of the `d`-dimensional box, proved to be an involutive
     automorphism.** Hence `ReflectionPositive` is stateable in four
     dimensions — `RP4` — for the first time. The claim that this was easy
     was correct: `adj_revSite` is the same coordinate-exchange argument as
     `LatticeReflection.adj_refl`, and no new idea appears.

  WHAT THIS DOES NOT DO. **Nothing here proves reflection positivity, in any
  dimension, for any half bigger than a singleton.** §3 is an equivalence,
  §5 supplies an object. W1's ladder still reads R1a done, R1b open, R2 done
  (`MatrixLoewner`), R3 open, R4 open — and R1b, the eigenspace
  identification, is untouched. **A wall does not move because its statement
  acquired a second dimension.**

  `LatticeReflectionSplit` is not deleted and is not edited. It is the box
  instance of §2–§3 and it landed first; the estate's practice is that a
  working proof stays. §6 records that this is the SECOND time today the
  box-first habit produced a file that a general one immediately subsumed.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import BoxGraph
import LatticeReflectionSplit

namespace GraphReflection

open Finset GraphLaplacian

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. An involutive automorphism leaves the Green function alone -/

/-- What we need of a reflection: an involutive bijection of the vertices
    preserving adjacency. Nothing else about `LatticeReflection.refl` was
    ever used. -/
structure IsRefl (θ : V ≃ V) : Prop where
  invol : Function.Involutive θ
  adj : ∀ p q, G.Adj (θ p) (θ q) ↔ G.Adj p q

variable {G}

theorem IsRefl.degree {θ : V ≃ V} (h : IsRefl G θ) (p : V) :
    G.degree (θ p) = G.degree p := by
  classical
  have himg : (G.neighborFinset (θ p)) = (G.neighborFinset p).image θ := by
    ext u
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image]
    constructor
    · intro hu
      refine ⟨θ u, ?_, by simp [h.invol u]⟩
      have hiff := h.adj p (θ u)
      rw [h.invol u] at hiff
      exact hiff.mp hu
    · rintro ⟨v, hv, rfl⟩
      exact (h.adj p v).mpr hv
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
    himg, Finset.card_image_of_injective _ θ.injective]

theorem IsRefl.lapMatrix {θ : V ≃ V} (h : IsRefl G θ) :
    (G.lapMatrix ℝ).submatrix θ θ = G.lapMatrix ℝ := by
  classical
  ext p q
  simp only [Matrix.submatrix_apply, SimpleGraph.lapMatrix, Matrix.sub_apply,
    SimpleGraph.degMatrix, SimpleGraph.adjMatrix, Matrix.diagonal, Matrix.of_apply]
  have hd : (θ p = θ q) = (p = q) := propext ⟨fun hc => θ.injective hc, fun hc => by rw [hc]⟩
  by_cases hpq : p = q
  · subst hpq; simp [h.degree p]
  · simp only [hd, hpq, if_false]
    by_cases hadj : G.Adj p q
    · simp [(h.adj p q).mpr hadj, hadj]
    · have hne : ¬ G.Adj (θ p) (θ q) := fun hc => hadj ((h.adj p q).mp hc)
      simp [hadj, hne]

theorem IsRefl.massive {θ : V ≃ V} (h : IsRefl G θ) (m : ℝ) :
    (GraphLaplacian.massive G m).submatrix θ θ = GraphLaplacian.massive G m := by
  classical
  ext p q
  simp only [GraphLaplacian.massive, Matrix.submatrix_apply, Matrix.add_apply]
  have hlap := congrFun (congrFun h.lapMatrix p) q
  simp only [Matrix.submatrix_apply] at hlap
  rw [hlap]
  congr 1
  simp only [Matrix.diagonal]
  have hd : (θ p = θ q) = (p = q) := propext ⟨fun hc => θ.injective hc, fun hc => by rw [hc]⟩
  simp [hd]

/-- **THE GREEN FUNCTION IS INVARIANT UNDER ANY INVOLUTIVE AUTOMORPHISM.**
    `LatticeReflection.green_refl` is this at the box; the box entered its
    proof only through a degree lemma, which `IsRefl.degree` supplies in
    general. -/
theorem green_aut {θ : V ≃ V} (h : IsRefl G θ) (m : ℝ) (p q : V) :
    GraphLaplacian.green G m (θ p) (θ q) = GraphLaplacian.green G m p q := by
  have hg : (GraphLaplacian.green G m).submatrix θ θ = GraphLaplacian.green G m := by
    rw [GraphLaplacian.green, ← Matrix.inv_submatrix_equiv, h.massive m]
  exact congrFun (congrFun hg p) q

theorem green_symm (m : ℝ) (p q : V) :
    GraphLaplacian.green G m p q = GraphLaplacian.green G m q p := by
  have hsym : (GraphLaplacian.massive G m).IsSymm := GraphLaplacian.massive_isSymm G m
  have hs : (GraphLaplacian.green G m).IsSymm := by
    unfold Matrix.IsSymm GraphLaplacian.green
    rw [Matrix.transpose_nonsing_inv]
    exact congrArg (fun M => M⁻¹) hsym
  exact (hs.apply p q).symm

/-! ## 2. The bilinear form and the identity -/

noncomputable def bil (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (c d : V → ℝ) : ℝ :=
  ∑ p, ∑ q, c p * d q * GraphLaplacian.green G m p q

noncomputable def energy (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (c : V → ℝ) : ℝ :=
  bil G m c c

noncomputable def reflectedForm (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ)
    (θ : V ≃ V) (c : V → ℝ) : ℝ :=
  ∑ p, ∑ q, c p * c q * GraphLaplacian.green G m (θ p) q

def sym (θ : V ≃ V) (c : V → ℝ) : V → ℝ := fun p => c p + c (θ p)
def anti (θ : V ≃ V) (c : V → ℝ) : V → ℝ := fun p => c p - c (θ p)
def mir (θ : V ≃ V) (c : V → ℝ) : V → ℝ := fun p => c (θ p)

variable {m : ℝ}

theorem bil_add_left (c d e : V → ℝ) :
    bil G m (fun p => c p + d p) e = bil G m c e + bil G m d e := by
  simp only [bil, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

theorem bil_sub_left (c d e : V → ℝ) :
    bil G m (fun p => c p - d p) e = bil G m c e - bil G m d e := by
  simp only [bil, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

theorem bil_add_right (c d e : V → ℝ) :
    bil G m c (fun q => d q + e q) = bil G m c d + bil G m c e := by
  simp only [bil, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

theorem bil_sub_right (c d e : V → ℝ) :
    bil G m c (fun q => d q - e q) = bil G m c d - bil G m c e := by
  simp only [bil, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

theorem bil_comm (c d : V → ℝ) : bil G m c d = bil G m d c := by
  rw [bil, bil, Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    rw [green_symm (G := G) m y x]; ring

theorem bil_mir_mir {θ : V ≃ V} (h : IsRefl G θ) (c d : V → ℝ) :
    bil G m (mir θ c) (mir θ d) = bil G m c d := by
  have hsum : ∀ f : V → ℝ, ∑ p, f (θ p) = ∑ p, f p :=
    fun f => Fintype.sum_equiv θ _ _ (fun _ => rfl)
  rw [bil, bil, ← hsum (fun p => ∑ q, c p * d q * GraphLaplacian.green G m p q)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← hsum (fun q => c (θ p) * d q * GraphLaplacian.green G m (θ p) q)]
  exact Finset.sum_congr rfl fun q _ => by simp only [mir]; rw [green_aut h m p q]

theorem reflectedForm_eq_bil {θ : V ≃ V} (h : IsRefl G θ) (c : V → ℝ) :
    reflectedForm G m θ c = bil G m (mir θ c) c := by
  have hsum : ∀ f : V → ℝ, ∑ p, f (θ p) = ∑ p, f p :=
    fun f => Fintype.sum_equiv θ _ _ (fun _ => rfl)
  rw [reflectedForm, bil, ← hsum (fun p => ∑ q, mir θ c p * c q * GraphLaplacian.green G m p q)]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [mir]
  rw [h.invol p]

/-- **THE REFLECTED FORM IS THE DIFFERENCE OF TWO ORDINARY ENERGIES**, over
    an arbitrary graph and an arbitrary involutive automorphism. -/
theorem reflectedForm_eq {θ : V ≃ V} (h : IsRefl G θ) (c : V → ℝ) :
    4 * reflectedForm G m θ c = energy G m (sym θ c) - energy G m (anti θ c) := by
  have hs : sym θ c = fun p => c p + mir θ c p := rfl
  have ha : anti θ c = fun p => c p - mir θ c p := rfl
  rw [energy, energy, hs, ha, bil_add_left, bil_add_right, bil_add_right,
    bil_sub_left, bil_sub_right, bil_sub_right, bil_mir_mir h,
    reflectedForm_eq_bil h, bil_comm (G := G) (m := m) c (mir θ c)]
  ring

/-! ## 3. Reflection positivity over an arbitrary graph -/

/-- **W1's failing step, for any graph and any reflection.**
    `LatticeReflection.ReflectionPositive` is this at the box; §4 proves it. -/
def ReflectionPositive (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (θ : V ≃ V)
    (half : Finset V) : Prop :=
  ∀ c : V → ℝ, (∀ p, p ∉ half → c p = 0) →
    0 ≤ ∑ p, ∑ q, c p * c q * GraphLaplacian.green G m (θ p) q

/-- **REFLECTION POSITIVITY IS AN ENERGY COMPARISON**, on any graph:
    symmetrising costs at least as much as antisymmetrising. -/
theorem reflectionPositive_iff_energy_le {θ : V ≃ V} (h : IsRefl G θ) (half : Finset V) :
    ReflectionPositive G m θ half
      ↔ ∀ c : V → ℝ, (∀ p, p ∉ half → c p = 0) →
          energy G m (anti θ c) ≤ energy G m (sym θ c) := by
  constructor
  · intro hrp c hc
    have h1 : 0 ≤ reflectedForm G m θ c := hrp c hc
    have h4 := reflectedForm_eq (m := m) h c
    linarith
  · intro hle c hc
    have h1 := hle c hc
    have h4 := reflectedForm_eq (m := m) h c
    have : (0:ℝ) ≤ reflectedForm G m θ c := by linarith
    exact this

/-! ## 4. The box is an instance -/

section Box

open IsingFiniteVolume IsingContourSeparation LatticeReflection

theorem isRefl_latticeGraph (n : ℕ) : IsRefl (latticeGraph n) (refl n) where
  invol := refl_involutive n
  adj := fun p q => adj_refl p q

/-- The general property at `(latticeGraph n, refl n)` IS
    `LatticeReflection.ReflectionPositive`, definitionally. -/
theorem reflectionPositive_box (n : ℕ) (m : ℝ) (half : Finset (Site n)) :
    ReflectionPositive (latticeGraph n) m (refl n) half
      ↔ LatticeReflection.ReflectionPositive n m half := Iff.rfl

end Box

/-! ## 5. The reflection in four dimensions

`BoxGraph` said the analogue on `Fin d → Fin n` was easy and did not write
it. It is, and here it is: reverse one coordinate. The only step with
content is `adj_revSite`, and it is the same exchange
`LatticeReflection.adj_refl` found — a step UP in the reversed coordinate
becomes a step DOWN, so the two disjuncts swap.
-/

section Box4

open BoxGraph

variable {d n : ℕ}

/-- Reflection of the `d`-dimensional box in coordinate `i`. -/
def revSite (i : Fin d) : BoxGraph.Site d n ≃ BoxGraph.Site d n where
  toFun p := Function.update p i (Fin.rev (p i))
  invFun p := Function.update p i (Fin.rev (p i))
  left_inv p := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  right_inv p := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]

@[simp] theorem revSite_apply_self (i : Fin d) (p : BoxGraph.Site d n) :
    revSite (n := n) i p i = Fin.rev (p i) := by simp [revSite]

@[simp] theorem revSite_apply_ne {i j : Fin d} (hj : j ≠ i) (p : BoxGraph.Site d n) :
    revSite (n := n) i p j = p j := by simp [revSite, Function.update_of_ne hj]

theorem revSite_involutive (i : Fin d) :
    Function.Involutive (revSite (n := n) i) := fun p => (revSite i).left_inv p

/-- **THE REFLECTION IS A GRAPH AUTOMORPHISM.** Reversing coordinate `i`
    leaves every other coordinate's steps alone and exchanges the two
    directions of a step in coordinate `i`. -/
theorem adj_revSite (i : Fin d) (p q : BoxGraph.Site d n) :
    BoxGraph.adj (revSite (n := n) i p) (revSite (n := n) i q) ↔ BoxGraph.adj p q := by
  constructor
  · rintro ⟨k, h1, h2⟩
    refine ⟨k, fun j hj => ?_, ?_⟩
    · by_cases hji : j = i
      · subst hji
        by_cases hik : j = k
        · exact absurd hik hj
        · have := h1 j hj
          simpa using Fin.rev_injective (by simpa using this)
      · simpa [revSite_apply_ne hji] using h1 j hj
    · by_cases hki : k = i
      · subst hki
        simp only [revSite_apply_self] at h2
        have hp := Fin.val_rev (p k)
        have hq := Fin.val_rev (q k)
        have hpk := (p k).isLt
        have hqk := (q k).isLt
        omega
      · simpa [revSite_apply_ne hki] using h2
  · rintro ⟨k, h1, h2⟩
    refine ⟨k, fun j hj => ?_, ?_⟩
    · by_cases hji : j = i
      · subst hji
        by_cases hik : j = k
        · exact absurd hik hj
        · simp only [revSite_apply_self]
          rw [h1 j hj]
      · simpa [revSite_apply_ne hji] using h1 j hj
    · by_cases hki : k = i
      · subst hki
        simp only [revSite_apply_self]
        have hp := Fin.val_rev (p k)
        have hq := Fin.val_rev (q k)
        have hpk := (p k).isLt
        have hqk := (q k).isLt
        omega
      · simpa [revSite_apply_ne hki] using h2

theorem boxGraph_revSite_aut (i : Fin d) :
    IsRefl (boxGraph d n) (revSite (n := n) i) where
  invol := revSite_involutive i
  adj := fun p q => adj_revSite i p q

/-- **REFLECTION POSITIVITY IN FOUR DIMENSIONS**, stateable for the first
    time. Nothing proves it; §6 says so. -/
def RP4 (n : ℕ) (m : ℝ) (i : Fin 4) (half : Finset (BoxGraph.Site 4 n)) : Prop :=
  ReflectionPositive (boxGraph 4 n) m (revSite (n := n) i) half

theorem rp4_iff_energy_le (n : ℕ) (m : ℝ) (i : Fin 4) (half : Finset (BoxGraph.Site 4 n)) :
    RP4 n m i half
      ↔ ∀ c : BoxGraph.Site 4 n → ℝ, (∀ p, p ∉ half → c p = 0) →
          energy (boxGraph 4 n) m (anti (revSite i) c)
            ≤ energy (boxGraph 4 n) m (sym (revSite i) c) :=
  reflectionPositive_iff_energy_le (boxGraph_revSite_aut i) half

/-- The four-dimensional Green function is invariant under the reflection —
    the `d = 4` twin of `LatticeReflection.green_refl`. -/
theorem green4_revSite (n : ℕ) (m : ℝ) (i : Fin 4) (p q : BoxGraph.Site 4 n) :
    BoxGraph.green4 n m (revSite (n := n) i p) (revSite (n := n) i q)
      = BoxGraph.green4 n m p q :=
  green_aut (boxGraph_revSite_aut i) m p q

end Box4

/-! ## 6. Review round 80 — the ways this could be hollow

**"§5 could be claimed as progress on W1."** It is not, and the distinction
is exact. §5 supplies an OBJECT — a reflection in four dimensions — and an
equivalence. **`RP4` is a `def` and nothing in this estate proves it for any
half with more than one element.** The ladder is unchanged: R1a done, R1b
open, R2 done, R3 open, R4 open. What §5 removes is the position
`LatticeField` §3 found the estate in once before, where a wall's statement
needed an object nobody had built.

**"So was `BoxGraph`'s 'this is easy' claim right?"** Yes, and that is the
finding, because it could have gone the other way. `adj_revSite` is two
`by_cases` and an `omega` against `Fin.val_rev`, with no new idea, exactly as
predicted. ERRATUM 48 says a claim that X is possible is checked by
attempting X — this attempt confirms rather than refutes, and confirming is
also a result. Had it been hard, the claim would have been a second instance
of "done and waiting".

**"This duplicates `LatticeReflectionSplit`, which landed an hour ago."** It
does, and §2–§3 here subsume it. That file is not deleted and not edited: a
working proof stays, and the box instance is what §4 checks the general
statement against. **But the duplication is the point of a note rather than
something to pass over** — this is the SECOND time today the box-first habit
produced a file immediately subsumed by a general one, the first being
`LatticeLaplacian` → `GraphLaplacian`. Both times the box was chosen because
W3 had built it, and both times no proof used it. The pattern is now named:
**when the estate's only instance of a structure is a special case someone
else built, write the general statement first and instantiate.**

**"`IsRefl` could be too weak, so §1 could be about nothing."** It has two
fields and both are used: `invol` in `reflectedForm_eq_bil` and
`revSite_involutive`, `adj` in `IsRefl.degree`, which is what
`IsRefl.lapMatrix` needs. Dropping either breaks §1. It is also exactly the
hypothesis `LatticeReflection` established for `refl n` and no more — §4
constructs `isRefl_latticeGraph` from `refl_involutive` and `adj_refl` and
nothing else.

**"§4 could be papering over a mismatch."** It is `Iff.rfl`, which is the
strongest evidence available that the general definition at the box IS the
box definition rather than an analogue of it. Had `GraphLaplacian.green_box`
not been `rfl`, this would have failed rather than silently compared two
different properties.

**"`green_symm` here duplicates the one in `LatticeReflectionSplit`."** It
does, at the general graph, and both are unconditional in `m` — neither
needs the `m ≠ 0` that `LatticeLaplacian.green_isSymm` carries, because
`Matrix.transpose_nonsing_inv` and `massive_isSymm` are unconditional. The
duplication is the same one the paragraph above records.
-/

end GraphReflection
