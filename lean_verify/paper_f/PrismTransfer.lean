/-
  PrismTransfer.lean — integrating out one layer returns the graph you started
  from.

  WHY. `PrismReflection` proved reflection positivity over an arbitrary finite
  graph and ended with a paragraph saying that a two-layer stack is the
  geometry a transfer operator lives on, that the estate has `TransferMatrix`
  and `TransferGap`, and that **nothing there connected them and the
  connection was not claimed.** ERRATUM 48's rule is that when a unit's
  contribution is "this makes X possible", the check is to attempt X. This
  attempts it, and reports how far it actually gets — which is further than a
  bridge to those two files and short of what their names suggest.

  WHAT THIS FILE PROVES:
  1. **`prism_degree`** — a vertex of the stack has its base degree plus one,
     the rung.
  2. **`massive_apply`** — the massive operator entrywise, for any graph. A
     small lemma the estate did not have and every computation below wants.
  3. **`massive_prism_layer`, `crossOp_prism`** — the two blocks. Within a
     layer the stack's operator is the base operator plus the identity (the
     rung's contribution to the degree); across the layers it is minus the
     identity (the rung itself).
  4. **`plusOp_entry` — THE IDENTIFICATION, and it is exact:
     `A + B = massive K m`.** The `+1` from the rung's degree and the `−1`
     from the rung's edge cancel, so **the even sector of a two-layer stack is
     the base graph's own massive operator at the same mass.** Physically:
     integrating out the odd combination of the two layers returns the field
     you started with, unshifted.
  5. **`minusOp_entry`, `minusOp_eq_massive_shift`** — the odd sector is the
     base operator with the mass shifted, `m² ↦ m² + 2`; stated both additively
     and as `massive K (√(m² + 2))`.
  6. **`blocks_eq`** — both sectors in one statement, and **`mass_shift_gt`**,
     that the shifted mass is genuinely larger.

  **A HEADER OVERCLAIM, CAUGHT IN REVIEW AND RECORDED RATHER THAN QUIETLY
  DROPPED.** The draft of this list promised two further theorems —
  `reflectedForm_prism_eq`, evaluating the reflected quadratic form as half
  the difference of two base-graph Green functions, and
  `reflectionPositive_prism_strict`, upgrading the criterion's inequality to a
  strict one. **Neither exists and neither is proved here.** They follow from
  §3 but not formally: both need `plusOp` and `minusOp` as matrices over `V`
  rather than over the subtype `↥(lower V)`, and hence a transport along
  `↥(lower V) ≃ V` that this file does not build. The route is short and
  written down on `UNLOCK_WATCHLIST.md`: the equivalence, `Matrix.submatrix`,
  `Matrix.inv_submatrix_equiv`, and one reindexing of a dot product. **This is
  the fifth header overclaim of this campaign and the fifth caught by review
  rather than by the compiler**, which is what a docstring's inability to fail
  typechecking guarantees.

  WHAT THIS DOES NOT DO, and the first item is the honest answer to the
  question the previous file raised.
  * **THIS IS NOT A BRIDGE TO `TransferMatrix` OR `TransferGap`, and it does
    not import them.** Those files are about the Ising transfer matrix — a
    statistical-mechanical object on spin configurations — and the operator
    identified here is a Gaussian covariance. **The geometry coincides and the
    objects do not.** The previous file's paragraph said the connection was
    not claimed; this one says, having looked, that the connection is not
    there to be made without a further construction nobody has written.
  * **No spectral statement.** `minusOp_eq_massive_shift` says the odd sector
    is a massive operator at a larger mass, which is the shape a mass gap
    argument would consume. **It is not a gap theorem**, there is no
    eigenvalue anywhere in this file, and the estate's gap files are
    untouched.
  * **Two layers only**, inherited verbatim; three layers have a middle and
    are outside all of this.
  * **No bundled matrix identity and no inverse.** §3 is entrywise. Turning it
    into `plusOp = (massive K m).submatrix e e` and then into a statement
    about `green` requires the subtype transport described above, and until
    that exists a downstream user cannot invert either block.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import PrismReflection

namespace PrismTransfer

open Finset GraphLaplacian GraphReflection GraphHalfSpace PrismReflection

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (K : SimpleGraph V) [DecidableRel K.Adj] {m : ℝ}

/-! ## 1. The massive operator, entrywise

Every computation below is a case split on `p = q` and on adjacency, so the
entrywise form is written once.
-/

theorem massive_apply {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (m : ℝ) (p q : W) :
    massive G m p q
      = (if p = q then (G.degree p : ℝ) + m ^ 2 else 0) - (if G.Adj p q then 1 else 0) := by
  classical
  simp only [massive, Matrix.add_apply, SimpleGraph.lapMatrix, Matrix.sub_apply,
    SimpleGraph.degMatrix, SimpleGraph.adjMatrix, Matrix.diagonal_apply, Matrix.of_apply]
  by_cases h : p = q
  · subst h; simp
  · simp [h]

/-! ## 2. The two blocks of the stack -/

theorem prism_degree (p : V) (a : Bool) : (prism K).degree (p, a) = K.degree p + 1 := by
  classical
  have himg : (prism K).neighborFinset (p, a)
      = insert (p, !a) ((K.neighborFinset p).image fun q => (q, a)) := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_image,
      prism_adj, prismAdj]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inr ⟨y.1, by simpa [SimpleGraph.mem_neighborFinset] using h2,
          Prod.ext rfl h1⟩
      · refine Or.inl ?_
        have hy2 : y.2 = !a := by cases a <;> cases hy : y.2 <;> simp_all
        exact Prod.ext h1.symm hy2
    · rintro (rfl | ⟨q, hq, rfl⟩)
      · exact Or.inr ⟨rfl, by cases a <;> simp⟩
      · exact Or.inl ⟨rfl, by simpa [SimpleGraph.mem_neighborFinset] using hq⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree, himg]
  rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ (fun x y h => by
    simpa using congrArg Prod.fst h), SimpleGraph.card_neighborFinset_eq_degree]
  simp only [Finset.mem_image, not_exists]
  rintro q ⟨-, hq⟩
  exact absurd (congrArg Prod.snd hq) (by cases a <;> simp)

/-- **WITHIN A LAYER**: the stack's operator is the base operator plus the
    identity — the rung's contribution to the degree, and nothing else. -/
theorem massive_prism_layer (p q : V) (a : Bool) :
    massive (prism K) m (p, a) (q, a)
      = massive K m p q + (if p = q then 1 else 0) := by
  classical
  have hadj : prismAdj K (p, a) (q, a) ↔ K.Adj p q := by
    simp only [prismAdj]
    constructor
    · rintro (⟨-, h⟩ | ⟨rfl, h⟩)
      · exact h
      · exact absurd rfl h
    · exact fun h => Or.inl ⟨trivial, h⟩
  have hpq : ((p, a) : V × Bool) = (q, a) ↔ p = q := by simp [Prod.ext_iff]
  rw [massive_apply, massive_apply, prism_degree]
  simp only [prism_adj, hadj, hpq]
  split_ifs <;> push_cast <;> ring

/-- **ACROSS THE LAYERS**: the coupling is minus the identity — the rung
    itself, and nothing else, because two vertices in opposite layers are
    adjacent exactly when they are the same base vertex. -/
theorem crossOp_prism (p q : V) :
    crossOp (prism K) m (swap (V := V)) (p, false) (q, false)
      = if p = q then -1 else 0 := by
  classical
  rw [TorusReflection.crossOp_eq_neg_adj isHalf_lower (by simp) (by simp)]
  by_cases h : p = q
  · subst h
    rw [if_pos (by simpa using prism_adj_rung K p), if_pos rfl]
  · rw [if_neg h, if_neg]
    rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact absurd h1 (by simp)
    · exact h (by simpa using h1)

/-! ## 3. The identification -/

/-- **THE EVEN SECTOR OF A TWO-LAYER STACK IS THE BASE GRAPH'S OWN MASSIVE
    OPERATOR, AT THE SAME MASS.** The `+1` the rung adds to the degree and the
    `−1` the rung contributes as an edge cancel exactly. -/
theorem plusOp_entry (p q : V) :
    massive (prism K) m (p, false) (q, false)
        + crossOp (prism K) m (swap (V := V)) (p, false) (q, false)
      = massive K m p q := by
  rw [massive_prism_layer, crossOp_prism]
  by_cases h : p = q <;> simp [h]

/-- **THE ODD SECTOR IS THE SAME OPERATOR WITH THE MASS SHIFTED.** -/
theorem minusOp_entry (p q : V) :
    massive (prism K) m (p, false) (q, false)
        - crossOp (prism K) m (swap (V := V)) (p, false) (q, false)
      = massive K m p q + 2 * (if p = q then 1 else 0) := by
  rw [massive_prism_layer, crossOp_prism]
  rcases eq_or_ne p q with rfl | h
  · simp; ring
  · simp [h]

/-- The shift, named: `m² ↦ m² + 2`. -/
theorem minusOp_eq_massive_shift (p q : V) :
    massive (prism K) m (p, false) (q, false)
        - crossOp (prism K) m (swap (V := V)) (p, false) (q, false)
      = massive K (Real.sqrt (m ^ 2 + 2)) p q := by
  classical
  rw [minusOp_entry, massive_apply, massive_apply,
    Real.sq_sqrt (by positivity : (0:ℝ) ≤ m ^ 2 + 2)]
  rcases eq_or_ne p q with rfl | h
  · simp; ring
  · simp [h]

/-! ## 4. What the identification is, and what it is not

The two blocks are base-graph operators at two masses. That is a statement
about matrices and it is exact. It is NOT a statement about the estate's
transfer matrix, and §5 says why in more detail than a docstring can.
-/

/-- Both sectors at once, as the sentence a reader should take away: the
    stack's `A ± B` are the base graph's massive operators at masses `m` and
    `√(m² + 2)`. -/
theorem blocks_eq (p q : V) :
    (massive (prism K) m (p, false) (q, false)
        + crossOp (prism K) m (swap (V := V)) (p, false) (q, false) = massive K m p q)
    ∧ (massive (prism K) m (p, false) (q, false)
        - crossOp (prism K) m (swap (V := V)) (p, false) (q, false)
        = massive K (Real.sqrt (m ^ 2 + 2)) p q) :=
  ⟨plusOp_entry K p q, minusOp_eq_massive_shift K p q⟩

/-- The shifted mass is genuinely larger, which is the direction any spectral
    reading would need — and is as far as this file goes in that direction. -/
theorem mass_shift_gt (hm : 0 ≤ m) : m < Real.sqrt (m ^ 2 + 2) := by
  have h1 : m ^ 2 < m ^ 2 + 2 := by linarith
  calc m = Real.sqrt (m ^ 2) := (Real.sqrt_sq hm).symm
    _ < Real.sqrt (m ^ 2 + 2) := by
        exact Real.sqrt_lt_sqrt (by positivity) h1

/-! ## 5. Review round 90 — the ways this could be hollow

**"`PrismReflection` said the transfer connection was not claimed. Is it
claimed now?"** No, and this is the file that looked. What was found is an
exact identification of the stack's two sectors with base-graph operators, and
what was NOT found is any relation to `TransferMatrix` or `TransferGap`.
**Those files are about the Ising transfer matrix, an operator on spin
configurations; the object here is a Gaussian covariance.** The geometry
coincides — two layers, a reflection between them — and the objects do not.
The honest report is therefore: ERRATUM 48's check was run, the answer is
negative, and the negative answer is written down instead of a bridge that
would have to be faked.

**"Is the cancellation in `plusOp_entry` a coincidence?"** It is exactly the
structure of the construction: the rung contributes `+1` to the degree of
every vertex, hence `+1` to the diagonal of the stack's operator, and `−1` as
an edge to the cross-block. Those are the same rung counted twice with
opposite signs, so `A + B` loses it entirely. **That is why the even sector is
the base operator at the SAME mass and not a shifted one** — and it is a fact
about the prism, not about graphs generally: on the box the corresponding
cancellation does not happen, because a box's cut-crossing bonds are not
present at every vertex.

**"§3 gives entries, not matrices. Is that a dodge?"** It became one the
moment the draft header promised two theorems that need the bundled form, and
that is why the header now says so in the list rather than only in the
caveats. On its own terms the entries ARE the definition:
`GraphReflectionPositive.plusOp` is `Matrix.of fun p q => massive … + crossOp …`
on the subtype of the half, so an entrywise identity at every `(p, false)`,
`(q, false)` is that matrix, read through the obvious bijection between the
lower layer and `V`. Stating it entrywise avoids constructing and transporting
along that bijection for no gain. **What is genuinely not here is a bundled
`Matrix V V ℝ` equality**, and a downstream user wanting `plusOp⁻¹` as a
matrix over `V` would have to build the transport.

**"`mass_shift_gt` looks like the start of a gap argument."** It is the
direction such an argument would need and it is not one. **There is no
eigenvalue in this file, no spectrum, and no operator norm**, and the estate's
gap files are neither imported nor mentioned. Recorded because "the odd sector
has a larger mass" is exactly the sentence that invites the inference, and the
inference is not licensed by anything proved here.
-/

end PrismTransfer
