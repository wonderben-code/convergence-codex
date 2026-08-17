import TorusBlockCount

/-!
# The block hypothesis was buying a count, not a dimension

`ReachKernelDimension` proved `finrank (reachKer) + blockCount = |H|` **on a block cut**, and read
the block hypothesis as what makes the identity true. It is not. `CrossBlockStructure`'s
`inReachKernel_iff_rows` needs only the mirror reflection, and it says the reach kernel is the
kernel of **the cut matrix acting on the half** — one linear equation per half-site, blocks or no
blocks. Rank–nullity then gives the identity on every graph:

> **`finrank_reachKer_add_rank`** — for any graph with an involutive automorphism and a mirror
> half, **`finrank (reachKer) + rank (cutRows) = |H|`**. No `IsCrossBlock`, no `hcross`, and no
> assumption that the coupling is even semidefinite.

**What the block hypothesis buys is `finrank_range_cutRows_eq_card_blockClasses`**: on a block cut
the rank *equals the number of blocks*, so a rank becomes a count. That is a real service — a count
is decidable and a rank is not obviously so — but it is a service to the *computation*, not to the
identity, and the two had been conflated.

## What comes free once the hypothesis is gone

* **`reachKer_eq_of_mass_general`** — the reach kernel does not move with the mass on **any** graph
  with a mirror reflection. `ReachKernelDimension.reachKer_eq_of_mass` proved this on a block cut;
  `cutRows` has no `m` in it at all, so the block cut was never involved.
* **`not_strict_of_rank_lt` — A NON-STRICTNESS CERTIFICATE FOR AN ARBITRARY CUT.** If the cut
  matrix on the half is rank-deficient, the reflected form is not strict. `strict_iff_cut_perfect`
  is sharper but only on a block cut; **this needs no block structure at all**, and it is the first
  statement in the estate that rules out strictness on a cut the block criterion cannot see.

The forward half of `StrictBiconditional`'s biconditional is what makes that possible:
`not_strict_of_supportedIsotropic` never used `hcross`, and that file said so. The consequence went
unwritten because until `ReachKernelDimension` there was no rank on the other side of it.

## What still needs the block hypothesis, and why

`strict ↔ reachKer = ⊥` does **not** survive. Only one direction is hypothesis-free — a nonzero
reach-kernel vector kills strictness always — and the converse is
`CrossBlockStructure.strict_iff_reachKernel_trivial`, which consumes `hcross` because without a
semidefinite coupling the reflected form is not controlled by the reach kernel. **Nothing here
weakens that**; `rank = |H|` is a *necessary* condition for strictness in general and a sufficient
one only where the estate already had sufficiency.

**No published tag moves**, `OS4` does not move, and no spectral gap is claimed.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CutRank

open SimpleGraph GraphReflection GraphMirrorReflection CrossFormMatrix CrossBlockStructure
open CrossPosSemidef BlockCount BlockDimension NullSpaceDimension ReachKernelDimension

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {θ : V ≃ V} {H Mir : Finset V} {m : ℝ}

/-! ## 1. The cut matrix, as a map on the half -/

/-- **THE CUT MATRIX ACTING ON THE HALF.** A supported family goes to its tuple of cut-matrix rows.
The mass is absent — `crossMatrix` never had one. -/
noncomputable def cutRows (G : SimpleGraph V) [DecidableRel G.Adj] (θ : V ≃ V) (H : Finset V) :
    supportedOn H →ₗ[ℝ] (H → ℝ) where
  toFun w := fun s => ∑ q ∈ H, crossMatrix G θ H (s : V) q * (w : V → ℝ) q
  map_add' u v := by
    funext s
    simp only [Submodule.coe_add, Pi.add_apply, mul_add]
    exact Finset.sum_add_distrib
  map_smul' c v := by
    funext s
    simp only [RingHom.id_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring

omit [Fintype V] in
@[simp] theorem cutRows_apply (w : supportedOn H) (s : H) :
    cutRows G θ H w s = ∑ q ∈ H, crossMatrix G θ H (s : V) q * (w : V → ℝ) q := rfl

/-! ## 2. Its kernel is the reach kernel, on any cut -/

/-- **THE REACH KERNEL IS THE CUT MATRIX'S KERNEL.** `CrossBlockStructure.inReachKernel_iff_rows`
read as a statement about a linear map. **No block hypothesis**: the rows are linear whether or not
they are block sums. -/
theorem ker_cutRows (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (m : ℝ) :
    Submodule.comap (supportedOn H).subtype (reachKer G m H Mir)
      = LinearMap.ker (cutRows G θ H) := by
  ext w
  rw [Submodule.mem_comap, LinearMap.mem_ker]
  simp only [Submodule.subtype_apply]
  rw [mem_reachKer, inReachKernel_iff_rows hM h m (w : V → ℝ)]
  constructor
  · rintro ⟨-, hrows⟩
    funext s
    simpa using hrows (s : V) s.2
  · intro hk
    refine ⟨w.2, fun s hs => ?_⟩
    have := congrFun hk ⟨s, hs⟩
    simpa using this

/-- **AND SO THE REACH KERNEL DOES NOT MOVE WITH THE MASS, ON ANY CUT.**
`ReachKernelDimension.reachKer_eq_of_mass` proved this on a block cut and read the block hypothesis
as the reason. The reason is that `cutRows` has no mass in it. -/
theorem reachKer_eq_of_mass_general (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (m₁ m₂ : ℝ) :
    reachKer G m₁ H Mir = reachKer G m₂ H Mir := by
  have h₁ := ker_cutRows hM h m₁
  have h₂ := ker_cutRows hM h m₂
  have hcomap : Submodule.comap (supportedOn H).subtype (reachKer G m₁ H Mir)
      = Submodule.comap (supportedOn H).subtype (reachKer G m₂ H Mir) := by rw [h₁, h₂]
  refine le_antisymm (fun v hv => ?_) (fun v hv => ?_)
  · have hmem : (⟨v, hv.1⟩ : supportedOn H)
        ∈ Submodule.comap (supportedOn H).subtype (reachKer G m₁ H Mir) := hv
    rw [hcomap] at hmem
    exact hmem
  · have hmem : (⟨v, hv.1⟩ : supportedOn H)
        ∈ Submodule.comap (supportedOn H).subtype (reachKer G m₂ H Mir) := hv
    rw [← hcomap] at hmem
    exact hmem

/-! ## 3. Rank–nullity, with the block hypothesis gone -/

/-- **THE IDENTITY, ON EVERY GRAPH WITH A MIRROR REFLECTION.** `ReachKernelDimension` proved this
with `blockCount` on the left and `IsCrossBlock` in the hypotheses; neither is needed. What sits
opposite the degeneracy is the **rank of the cut**, and on a block cut §4 says that rank is the
block count. -/
theorem finrank_reachKer_add_rank (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (m : ℝ) :
    Module.finrank ℝ (reachKer G m H Mir)
        + Module.finrank ℝ (LinearMap.range (cutRows G θ H)) = H.card := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (cutRows G θ H)
  rw [finrank_supportedOn] at hrn
  have he := (Submodule.comapSubtypeEquivOfLe
    (reachKer_le_supported (G := G) (m := m) (H := H) (Mir := Mir))).finrank_eq
  rw [ker_cutRows hM h m] at he
  omega

/-! ## 4. What the block hypothesis was actually buying -/

omit [Fintype V] in
/-- **ON A BLOCK CUT THE RANK IS THE NUMBER OF BLOCKS.** Two identities with the same left summand;
subtract. **This is the whole content of the block hypothesis in this chain** — it does not make the
dimension exist, it makes the rank countable.

**`[Finite V]` replaces the section's `[Fintype V]`**: the statement needs neither, the proof needs
the ambient space finite-dimensional, and the linter's own suggestion is taken rather than the
omission being forced. -/
theorem finrank_range_cutRows_eq_card_blockClasses [Finite V] (hM : IsMirrorHalf θ H Mir)
    (h : IsRefl G θ) (hC : IsCrossBlock G θ H) :
    Module.finrank ℝ (LinearMap.range (cutRows G θ H)) = (blockClasses G θ H).card := by
  have : Fintype V := Fintype.ofFinite V
  have h1 := finrank_reachKer_add_rank (Mir := Mir) hM h (0 : ℝ)
  have h2 := finrank_reachKer_add (m := (0 : ℝ)) hM h hC
  omega

/-! ## 5. A non-strictness certificate that needs no block structure -/

/-- **A NONZERO REACH-KERNEL VECTOR KILLS STRICTNESS, ALWAYS.**
`StrictBiconditional.not_strict_of_supportedIsotropic` does not use `hcross`, and that file says so;
`CrossBlockStructure.supportedIsotropic_iff_reachKernel_ne_zero` does not either. -/
theorem reachKer_eq_bot_of_strict (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hstrict : ∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c) :
    reachKer G m H Mir = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  by_contra hv0
  exact StrictBiconditional.not_strict_of_supportedIsotropic hM h hm
    ((supportedIsotropic_iff_reachKernel_ne_zero hM h m).mpr ⟨v, hv0, hv⟩) hstrict

/-- **AND SO STRICTNESS FORCES THE CUT TO HAVE FULL RANK ON THE HALF.** A necessary condition, on an
arbitrary cut. -/
theorem rank_cutRows_eq_card_of_strict (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hstrict : ∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c) :
    Module.finrank ℝ (LinearMap.range (cutRows G θ H)) = H.card := by
  have hid := finrank_reachKer_add_rank (Mir := Mir) hM h m
  rw [reachKer_eq_bot_of_strict hM h hm hstrict, finrank_bot] at hid
  omega

/-- **THE CERTIFICATE.** A rank-deficient cut is not strict — **on any graph with an involutive
automorphism and a mirror half**, with no block hypothesis and no semidefiniteness.

`CrossBlockStructure.strict_iff_cut_perfect` is sharper where it applies, and it applies only on a
block cut. This is the statement for the cuts it cannot see. -/
theorem not_strict_of_rank_lt (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hlt : Module.finrank ℝ (LinearMap.range (cutRows G θ H)) < H.card) :
    ¬ (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c) := by
  intro hstrict
  exact absurd (rank_cutRows_eq_card_of_strict hM h hm hstrict) (Nat.ne_of_lt hlt)


/-- **AN ISOLATED HALF-SITE PUTS ITS INDICATOR IN THE REACH KERNEL.** A site with no cross-neighbour
anywhere in the half contributes a zero column to the cut, so the family that is `1` there and `0`
elsewhere solves every row. -/
theorem indicator_mem_reachKer (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (m : ℝ) {s : V}
    (hs : s ∈ H) (hiso : ∀ q ∈ H, ¬ G.Adj q (θ s)) :
    (fun p => if p = s then (1 : ℝ) else 0) ∈ reachKer G m H Mir := by
  classical
  rw [mem_reachKer, inReachKernel_iff_rows hM h m]
  refine ⟨fun i hi => if_neg (fun hc => hi (by rw [hc]; exact hs)), fun t ht => ?_⟩
  have hrow : ∀ q ∈ H, crossMatrix G θ H t q * (if q = s then (1 : ℝ) else 0)
      = if q = s then crossMatrix G θ H t s else 0 := by
    intro q _
    by_cases hq : q = s
    · rw [if_pos hq, if_pos hq, hq, mul_one]
    · rw [if_neg hq, if_neg hq, mul_zero]
  rw [Finset.sum_congr rfl hrow, Finset.sum_ite_eq' H s (fun _ => crossMatrix G θ H t s),
    if_pos hs]
  rcases crossMatrix_entries (G := G) (θ := θ) (H := H) t s with h0 | h1
  · exact h0
  · exact absurd ((crossMatrix_eq_one_iff t s).mp h1).2.2 (hiso t ht)

omit [Fintype V] in
/-- **AND SO AN ISOLATED SITE MAKES THE CUT RANK-DEFICIENT.**

**`[Finite V]` replaces the section's `[Fintype V]`** for the reason recorded at
`finrank_range_cutRows_eq_card_blockClasses`: the statement needs neither and the proof needs the
ambient space finite-dimensional. -/
theorem rank_lt_of_isolated [Finite V] (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) {s : V}
    (hs : s ∈ H) (hiso : ∀ q ∈ H, ¬ G.Adj q (θ s)) :
    Module.finrank ℝ (LinearMap.range (cutRows G θ H)) < H.card := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hne : reachKer G (0 : ℝ) H Mir ≠ ⊥ := by
    intro hbot
    have hmem := indicator_mem_reachKer (Mir := Mir) hM h (0 : ℝ) hs hiso
    rw [hbot, Submodule.mem_bot] at hmem
    have := congrFun hmem s
    rw [if_pos rfl] at this
    exact one_ne_zero this
  have hpos : 0 < Module.finrank ℝ (reachKer G (0 : ℝ) H Mir) :=
    Nat.pos_of_ne_zero fun hz => hne (Submodule.finrank_eq_zero.mp hz)
  have hid := finrank_reachKer_add_rank (Mir := Mir) hM h (0 : ℝ)
  omega

/-- **A NON-STRICTNESS CERTIFICATE WITH NO DIAGONALITY AND NO BLOCKS.** -/
theorem not_strict_of_isolated (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0) {s : V}
    (hs : s ∈ H) (hiso : ∀ q ∈ H, ¬ G.Adj q (θ s)) :
    ¬ (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c) :=
  not_strict_of_rank_lt hM h hm (rank_lt_of_isolated (Mir := Mir) hM h hs hiso)

/-- **AND `HalfBlockStructure.not_strict_of_untouched` IS THE DIAGONAL CASE OF IT**, so the
generalisation is proved rather than asserted (`ERRATUM 48`). That theorem assumes the cut is
diagonal and the site misses its own mirror; under diagonality those two together say the site has
no cross-neighbour at all, which is this file's hypothesis and all of it. **Stated as an `example`
because the conclusion is already the estate's** — what is new is the hypothesis it is reached
from. -/
example (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hdiag : ∀ p ∈ H, ∀ q ∈ H, G.Adj p (θ q) → p = q) {s : V} (hs : s ∈ H)
    (hns : ¬ G.Adj s (θ s)) :
    ¬ (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c) := by
  refine not_strict_of_isolated hM h hm hs fun q hq hadj => hns ?_
  have hqs : q = s := hdiag q hq s hs hadj
  subst hqs
  exact hadj

/-! ## 6. The two halves, read as ranks -/

open ReflectedFormCongr HalfBlockStructure TorusReflection TorusBlockCount

/-- **RANK TWO AGAINST RANK ONE**, on a half of size two. The contiguous cut has full rank on its
half and the antipodal cut is one short — and by §5 that shortfall alone rules out strictness,
without appealing to the block structure that §4 used to count it. -/
theorem rank_two_halves :
    Module.finrank ℝ (LinearMap.range (cutRows (torusGraph 1 4) torusRho rotHalf)) = 2
      ∧ Module.finrank ℝ (LinearMap.range (cutRows (torusGraph 1 4) torusRho torusHalf)) = 1 := by
  refine ⟨?_, ?_⟩
  · rw [finrank_range_cutRows_eq_card_blockClasses isMirrorHalf_rotHalf isRefl_torusRho
      (isCrossBlock_of_cross_diag crossDiag_rotHalf), card_blockClasses_rotHalf]
  · rw [finrank_range_cutRows_eq_card_blockClasses isMirrorHalf_torusHalf isRefl_torusRho
      isCrossBlock_torusHalf, card_blockClasses_torusHalf]

end CutRank
