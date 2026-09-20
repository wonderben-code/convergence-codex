import SignlessRegularConverse
import HermitianTracePower

/-!
# The second eigenvalue, which six units have fenced as absent, and a floor under it

Every unit of this chain since `SignlessPerronSimple` has closed with the same sentence — *no
second eigenvalue and no gap* — and the sentence was accurate: **the estate defines no second
eigenvalue for any operator.** `PerronGap` proves a qualitative gap for a strictly positive matrix
(`abs_eigenvalues_lt_of_ne`: every eigenvalue but the top is strictly smaller in modulus) and stops
there; `RayleighVariational.topEigen` is a `Finset.sup'` over all of `univ` and has no sibling.
Grepped before writing, and this time the grep was run (`ERRATUM 535`).

## What is proved

**`topIdx`, `secondEigen`** — an index attaining the top, and the largest eigenvalue **off that
index**. This is `λ₂` in the multiset convention: when the top has multiplicity two or more,
`secondEigen = topEigen`, which is what a sorted-with-multiplicity list gives and is the reading
every bound below is stated against.
⚠ **THAT SENTENCE WAS AN ASSERTION FOR THE WHOLE LIFE OF THIS FILE AND IS NOW A THEOREM**
(2026-09-19, unit 140, `ERRATUM 94` — kept because it was right). `secondEigen_eq_topEigen_iff`
proves it **as an iff and in both directions**: `secondEigen = topEigen` exactly when some index
other than `topIdx` also attains the top, and `secondEigen_lt_topEigen_iff` reads the strict
inequality off as simplicity of the top **as a value**. The `UNLOCK_WATCHLIST` item for the
quantitative gap named the same gap in its own words — *`secondEigen` is connected only to its
own definition, not to any multiset notion of second largest* — and this is that connection.

**`secondEigen_le_topEigen`** — the obvious half: on any Hermitian matrix with two or more indices,
and nothing else. (An earlier draft said *the only one that needs no hypothesis*, which
`uncondclaim_scan` refused — it takes `hA` and `Nontrivial V` like everything here, and what was
meant was *no bound on the trace and no connectedness*.)

**`trace_le`** — `tr A ≤ topEigen + (|V| − 1)·secondEigen`. The trace is the sum of the eigenvalues
(`HermitianTracePower.real_trace_pow_eq_sum_eigenvalues_pow` at `k = 1`), one term is the top and
the other `|V| − 1` are each at most the second.

**`le_secondEigen`** — hence **a floor**: `secondEigen ≥ (tr A − topEigen)/(|V| − 1)`, for every
real symmetric matrix on two or more points. **This is the file's general content** and it is
where the quantitative part comes from: an upper bound on `topEigen` becomes a *lower* bound on
`secondEigen`, because the trace is fixed.

**`trace_signlessLap`** — `tr Q = ∑ᵥ deg(v)`, the adjacency matrix contributing nothing to the
diagonal.

**`le_secondEigen_signlessLap`** — so on any graph on two or more vertices,

```
(∑ᵥ deg v − 2Δ) / (|V| − 1)  ≤  secondEigen (signlessLap G)
```

with `SignlessTopDegreeBounds.topEigen_le_two_maxDegree` supplying the `2Δ`.
**`le_secondEigen_regular`** reads it on a `k`-regular graph, where it is `k(|V| − 2)/(|V| − 1)` —
so on a large regular graph the second eigenvalue is nearly `k`, which is half the top.

**`secondEigen_lt_topEigen`** — and on a **connected** graph the gap is strict. This is the first
statement in the estate that separates the top of a spectrum from the rest of it in the `topEigen`
vocabulary, and it comes from joining two things proved earlier this week:
`SignlessPerronSimple.top_simple_connected` says the top eigenspace has dimension at most one, and
`HermitianFibreCount.finrank_eigenspace_hermitian_eq_card_fibre` says that dimension **is the number
of indices carrying that eigenvalue**. One index, so every other index is strictly below.

## What is NOT here

* **NO QUANTITATIVE GAP.** `secondEigen < topEigen` is proved on a connected graph; **how far
  below** is not, and no bound of the form `topEigen − secondEigen ≥ f(G)` appears (`ERRATUM 246`).
  The floor above is a bound on `secondEigen` from below, which is the opposite direction: together
  they trap it, they do not separate it.
* **NO CEILING ON `secondEigen` BEYOND THE TOP.** The classical bounds — Das, Merris, and the
  interlacing that would come from edge deletion — are each a different argument and none is
  attempted.
* **NOTHING ABOUT EIGENVALUES BELOW THE SECOND.** `topIdx` picks one index; a genuine sorted
  spectrum is not built and `secondEigen` is not shown to be the second element of one.
* **NOTHING ABOUT THE ORDINARY LAPLACIAN'S ALGEBRAIC CONNECTIVITY**, which is the *smallest*
  nonzero eigenvalue and a different object entirely; nothing here bears on it.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a finite vertex type with decidable
equality, and `Nontrivial V` wherever `secondEigen` appears — the definition needs a second index
to range over. The graph statements add decidable adjacency, and the strict gap adds `G.Connected`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessSecondEigen

open Matrix Finset SimpleGraph LaplacianSignless RayleighVariational

/-! ## 1. The second eigenvalue -/

section Defn
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An index attaining the top of the spectrum. -/
noncomputable def topIdx {A : Matrix V V ℝ} (hA : A.IsHermitian) [Nonempty V] : V :=
  (SignlessPerronSimple.exists_topEigen hA).choose

theorem eigenvalues_topIdx {A : Matrix V V ℝ} (hA : A.IsHermitian) [Nonempty V] :
    hA.eigenvalues (topIdx hA) = topEigen hA :=
  (SignlessPerronSimple.exists_topEigen hA).choose_spec

theorem erase_nonempty [Nontrivial V] (i : V) : (Finset.univ.erase i).Nonempty := by
  rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  have := Fintype.one_lt_card (α := V)
  omega

/-- **THE SECOND EIGENVALUE**: the largest one carried by an index other than `topIdx`. When the
top has multiplicity two or more this equals the top, which is the multiset convention.
⚠ **THE SECOND SENTENCE WAS AN ASSERTION UNTIL 2026-09-19 AND IS NOW A THEOREM**
(`secondEigen_eq_topEigen_iff`, unit 140), as an **iff** and in both directions. It is kept as
written because it was right; what changed is that it is checked. -/
noncomputable def secondEigen {A : Matrix V V ℝ} (hA : A.IsHermitian) [Nontrivial V] : ℝ :=
  (Finset.univ.erase (topIdx hA)).sup' (erase_nonempty _) hA.eigenvalues

theorem le_secondEigen_of_ne {A : Matrix V V ℝ} (hA : A.IsHermitian) [Nontrivial V] {i : V}
    (hi : i ≠ topIdx hA) : hA.eigenvalues i ≤ secondEigen hA :=
  Finset.le_sup' _ (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)

theorem secondEigen_le_topEigen {A : Matrix V V ℝ} (hA : A.IsHermitian) [Nontrivial V] :
    secondEigen hA ≤ topEigen hA :=
  Finset.sup'_le _ _ fun i _ => SignlessPerronSimple.le_topEigen hA i

/-- **THE MULTISET CONVENTION, PROVED RATHER THAN ASSERTED.** `secondEigen`'s own docstring and
this file's header have said since they were written that *when the top has multiplicity two or
more this equals the top, which is the multiset convention*. Nothing proved it, and the
`UNLOCK_WATCHLIST` item for the quantitative gap names the same gap in its own words —
*`secondEigen` is connected only to its own definition, not to any multiset notion of second
largest*. This is that connection, as an **iff**: the second eigenvalue equals the top exactly
when some index other than `topIdx` also attains the top. -/
theorem secondEigen_eq_topEigen_iff {A : Matrix V V ℝ} (hA : A.IsHermitian) [Nontrivial V] :
    secondEigen hA = topEigen hA ↔ ∃ j, j ≠ topIdx hA ∧ hA.eigenvalues j = topEigen hA := by
  constructor
  · intro h
    obtain ⟨j, hj, hval⟩ :=
      Finset.exists_mem_eq_sup' (erase_nonempty (topIdx hA)) hA.eigenvalues
    exact ⟨j, (Finset.mem_erase.1 hj).1, by rw [← h, secondEigen, hval]⟩
  · rintro ⟨j, hj, hval⟩
    exact le_antisymm (secondEigen_le_topEigen hA) (hval ▸ le_secondEigen_of_ne hA hj)

/-- **AND SO THE STRICT INEQUALITY IS EXACTLY SIMPLICITY OF THE TOP AS A VALUE** — no index but
`topIdx` attains it. `secondEigen_lt_topEigen` below derives this from connectedness; this says
what the strict inequality MEANS, at any Hermitian matrix and with no graph in sight. -/
theorem secondEigen_lt_topEigen_iff {A : Matrix V V ℝ} (hA : A.IsHermitian) [Nontrivial V] :
    secondEigen hA < topEigen hA ↔ ∀ j, j ≠ topIdx hA → hA.eigenvalues j ≠ topEigen hA := by
  rw [lt_iff_le_and_ne, and_iff_right (secondEigen_le_topEigen hA), ne_eq,
    secondEigen_eq_topEigen_iff]
  simp only [not_exists, not_and]

/-- **AND WITHOUT THE CHOSEN INDEX.** `topIdx` is a `choose`; a statement mentioning it is a
statement about that choice. This says the same thing about the matrix alone: the second
eigenvalue equals the top exactly when **two distinct indices** attain the top. -/
theorem secondEigen_eq_topEigen_iff_exists_pair {A : Matrix V V ℝ} (hA : A.IsHermitian)
    [Nontrivial V] :
    secondEigen hA = topEigen hA
      ↔ ∃ i j, i ≠ j ∧ hA.eigenvalues i = topEigen hA ∧ hA.eigenvalues j = topEigen hA := by
  rw [secondEigen_eq_topEigen_iff]
  constructor
  · rintro ⟨j, hj, hval⟩
    exact ⟨topIdx hA, j, Ne.symm hj, eigenvalues_topIdx hA, hval⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    rcases eq_or_ne i (topIdx hA) with rfl | hne
    · exact ⟨j, Ne.symm hij, hj⟩
    · exact ⟨i, hne, hi⟩

/-- **THE FIBRE OVER THE TOP IS A SINGLETON EXACTLY WHEN THE GAP IS STRICT.** Still no `topIdx`
in the statement. -/
theorem card_fibre_topEigen_eq_one_iff {A : Matrix V V ℝ} (hA : A.IsHermitian) [Nontrivial V] :
    Fintype.card {i : V // hA.eigenvalues i = topEigen hA} = 1
      ↔ secondEigen hA < topEigen hA := by
  rw [Fintype.card_eq_one_iff, secondEigen_lt_topEigen_iff]
  constructor
  · rintro ⟨x, hx⟩ j hj hval
    exact hj (congrArg Subtype.val
      ((hx ⟨j, hval⟩).trans (hx ⟨topIdx hA, eigenvalues_topIdx hA⟩).symm))
  · intro h
    refine ⟨⟨topIdx hA, eigenvalues_topIdx hA⟩, fun y => ?_⟩
    ext
    by_contra hne
    exact h y.1 hne y.2

/-- **AND SO THE STRICT GAP IS ONE-DIMENSIONALITY OF THE TOP EIGENSPACE** — the form a consumer
wants, and the one the `UNLOCK_WATCHLIST` item's *multiset notion of second largest* was asking
for. Through `HermitianFibreCount.finrank_eigenspace_hermitian_eq_card_fibre`, which was already
below this file in the import order. -/
theorem finrank_eigenspace_topEigen_eq_one_iff {A : Matrix V V ℝ} (hA : A.IsHermitian)
    [Nontrivial V] :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A - topEigen hA • LinearMap.id)) = 1
      ↔ secondEigen hA < topEigen hA := by
  rw [HermitianFibreCount.finrank_eigenspace_hermitian_eq_card_fibre hA (topEigen hA)]
  exact card_fibre_topEigen_eq_one_iff hA

/-! ## 2. The trace pins it from below -/

/-- The trace is the sum of the eigenvalues. -/
theorem trace_eq_sum {A : Matrix V V ℝ} (hA : A.IsHermitian) :
    A.trace = ∑ i, hA.eigenvalues i := by
  have := TransferPowerSum.real_trace_pow_eq_sum_eigenvalues_pow hA 1
  simpa using this

/-- **ONE TOP AND `|V| − 1` SECONDS.** -/
theorem trace_le {A : Matrix V V ℝ} (hA : A.IsHermitian) [Nontrivial V] :
    A.trace ≤ topEigen hA + (Fintype.card V - 1 : ℕ) * secondEigen hA := by
  classical
  have hrest : ∑ i ∈ Finset.univ.erase (topIdx hA), hA.eigenvalues i
      ≤ (Fintype.card V - 1 : ℕ) * secondEigen hA := by
    calc ∑ i ∈ Finset.univ.erase (topIdx hA), hA.eigenvalues i
        ≤ ∑ _i ∈ Finset.univ.erase (topIdx hA), secondEigen hA :=
          Finset.sum_le_sum fun i hi => le_secondEigen_of_ne hA (Finset.mem_erase.mp hi).1
      _ = (Fintype.card V - 1 : ℕ) * secondEigen hA := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            nsmul_eq_mul]
  rw [trace_eq_sum hA, ← Finset.add_sum_erase _ _ (Finset.mem_univ (topIdx hA)),
    eigenvalues_topIdx hA]
  linarith

/-- **THE FLOOR.** An upper bound on the top is a lower bound on the second, the trace being
fixed. -/
theorem le_secondEigen {A : Matrix V V ℝ} (hA : A.IsHermitian) [Nontrivial V] :
    (A.trace - topEigen hA) / (Fintype.card V - 1 : ℕ) ≤ secondEigen hA := by
  have hcard : (0 : ℝ) < (Fintype.card V - 1 : ℕ) := by
    have := Fintype.one_lt_card (α := V)
    have h1 : 1 ≤ Fintype.card V - 1 := by omega
    exact_mod_cast lt_of_lt_of_le zero_lt_one h1
  rw [div_le_iff₀ hcard]
  linarith [trace_le hA]

end Defn

/-! ## 3. On a graph -/

section Graph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **`tr Q = ∑ deg`.** The adjacency matrix has zero diagonal. -/
theorem trace_signlessLap : (signlessLap G).trace = ∑ v, (G.degree v : ℝ) := by
  simp [signlessLap, Matrix.trace_add, SimpleGraph.degMatrix, Matrix.trace_diagonal]

/-- **A FLOOR UNDER THE SECOND EIGENVALUE OF EVERY GRAPH ON TWO OR MORE VERTICES.** -/
theorem le_secondEigen_signlessLap [Nontrivial V] :
    ((∑ v, (G.degree v : ℝ)) - 2 * (G.maxDegree : ℝ)) / (Fintype.card V - 1 : ℕ)
      ≤ secondEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G) := by
  have hcard : (0 : ℝ) < (Fintype.card V - 1 : ℕ) := by
    have := Fintype.one_lt_card (α := V)
    have h1 : 1 ≤ Fintype.card V - 1 := by omega
    exact_mod_cast lt_of_lt_of_le zero_lt_one h1
  have hfloor := le_secondEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G)
  rw [trace_signlessLap G] at hfloor
  refine le_trans ?_ hfloor
  have hstep : (∑ v, (G.degree v : ℝ)) - 2 * (G.maxDegree : ℝ)
      ≤ (∑ v, (G.degree v : ℝ))
        - topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G) := by
    linarith [SignlessTopDegreeBounds.topEigen_le_two_maxDegree G]
  gcongr

/-- **ON A `k`-REGULAR GRAPH THE FLOOR IS `k(|V| − 2)/(|V| − 1)`**, so on a large regular graph the
second eigenvalue is nearly `k` — half the top, which is `2k`. -/
theorem le_secondEigen_regular [Nontrivial V] {k : ℕ} (hreg : G.IsRegularOfDegree k) :
    ((Fintype.card V : ℝ) * k - 2 * k) / (Fintype.card V - 1 : ℕ)
      ≤ secondEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G) := by
  have hΔ : (G.maxDegree : ℝ) = k := by
    rw [SignlessStarExact.maxDegree_of_regular G hreg]
  have hsum : ∑ v, (G.degree v : ℝ) = (Fintype.card V : ℝ) * k := by
    rw [Finset.sum_congr rfl fun v _ => by rw [hreg v], Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have := le_secondEigen_signlessLap G
  rwa [hsum, hΔ] at this

/-! ## 4. And on a connected graph the gap is strict -/

/-- **EXACTLY ONE INDEX CARRIES THE TOP**, on a connected graph: the top eigenspace has dimension
at most one and that dimension *is* the number of such indices. -/
theorem eigenvalues_ne_topEigen [Nontrivial V] (hconn : G.Connected) {i : V}
    (hi : i ≠ topIdx (LaplacianSignlessDefinite.signlessLap_isHermitian G)) :
    (LaplacianSignlessDefinite.signlessLap_isHermitian G).eigenvalues i
      ≠ topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G) := by
  classical
  set hQ := LaplacianSignlessDefinite.signlessLap_isHermitian G with hQdef
  intro hEq
  have hsimple := SignlessPerronSimple.top_simple_connected G hconn
  rw [HermitianFibreCount.finrank_eigenspace_hermitian_eq_card_fibre hQ (topEigen hQ)] at hsimple
  have h1 : (⟨topIdx hQ, eigenvalues_topIdx hQ⟩ :
      {j : V // hQ.eigenvalues j = topEigen hQ}) ≠ ⟨i, hEq⟩ := by
    simp only [ne_eq, Subtype.mk.injEq]
    exact fun h => hi h.symm
  have h2 : 1 < Fintype.card {j : V // hQ.eigenvalues j = topEigen hQ} :=
    Fintype.one_lt_card_iff_nontrivial.mpr ⟨_, _, h1⟩
  omega

/-- **THE STRICT GAP.** -/
theorem secondEigen_lt_topEigen [Nontrivial V] (hconn : G.Connected) :
    secondEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G)
      < topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G) := by
  classical
  set hQ := LaplacianSignlessDefinite.signlessLap_isHermitian G with hQdef
  rw [secondEigen, Finset.sup'_lt_iff]
  intro i hi
  exact lt_of_le_of_ne (SignlessPerronSimple.le_topEigen hQ i)
    (eigenvalues_ne_topEigen G hconn (Finset.mem_erase.mp hi).1)

/-! ## 5. And so the top eigenspace is a LINE, at every connected graph -/

/-- **THE TOP EIGENSPACE OF `Q` IS EXACTLY ONE-DIMENSIONAL ON ANY CONNECTED GRAPH.**
`SignlessPerronSimple.top_simple_connected` has bounded this dimension by `1` since the Perron
work; what it does not give is that the bound is ATTAINED, and the estate's `= 1` statements for a
top eigenvalue all name a smaller class — `LaplacianTopEigenspace.finrank_top_eigenspace_eq_one`
and `ReflectionGeneral.finrank_lap_top_eq_one` are the Laplacian's and take **regular** and
**bipartite**, and `SignlessFlatConnected.forall_finrank_le_one_of_flat_connected` takes bipartite
and a flatness hypothesis. Here there is no regularity, no colouring and no flatness: connected is
the whole hypothesis. -/
theorem finrank_eigenspace_topEigen_signlessLap_eq_one [Nontrivial V] (hconn : G.Connected) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G)
        - topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G) • LinearMap.id))
      = 1 :=
  (finrank_eigenspace_topEigen_eq_one_iff _).2 (secondEigen_lt_topEigen G hconn)

/-- The same read on Mathlib's enumeration: **exactly one index carries the top**.
`eigenvalues_ne_topEigen` says no index other than the chosen one does; this says it as a count,
with no chosen index in the statement. -/
theorem card_fibre_topEigen_signlessLap_eq_one [Nontrivial V] (hconn : G.Connected) :
    Fintype.card {i : V // (LaplacianSignlessDefinite.signlessLap_isHermitian G).eigenvalues i
        = topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G)} = 1 :=
  (card_fibre_topEigen_eq_one_iff _).2 (secondEigen_lt_topEigen G hconn)

/-- **AND SO THE TOP EIGENVECTOR IS UNIQUE UP TO SCALE**, which is the form a consumer holding a
vector can use: on a connected graph, any top eigenvector of `Q` is a multiple of any nonzero one.
A dimension is a number; this is the sentence the number is for. Note the hypothesis on `y` is the
eigenvector equation alone — `y = 0` is allowed and is the `c = 0` case. -/
theorem exists_smul_of_mulVec_eq_topEigen [Nontrivial V] (hconn : G.Connected)
    {x y : V → ℝ}
    (hx : (signlessLap G).mulVec x
      = topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G) • x) (hx0 : x ≠ 0)
    (hy : (signlessLap G).mulVec y
      = topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G) • y) :
    ∃ c : ℝ, c • x = y := by
  classical
  set t := topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G) with ht
  set W := LinearMap.ker (Matrix.toLin' (signlessLap G) - t • LinearMap.id) with hW
  have hxW : x ∈ W := (RealComplexKernel.mem_ker_sub_smul (signlessLap G) t x).2 hx
  have hyW : y ∈ W := (RealComplexKernel.mem_ker_sub_smul (signlessLap G) t y).2 hy
  have hx0' : (⟨x, hxW⟩ : W) ≠ 0 := by
    simpa [Submodule.mk_eq_zero] using hx0
  have h1 : Module.finrank ℝ W = 1 :=
    finrank_eigenspace_topEigen_signlessLap_eq_one G hconn
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨x, hxW⟩ : W) hx0').1 h1 ⟨y, hyW⟩
  exact ⟨c, congrArg Subtype.val hc⟩

end Graph

end SignlessSecondEigen
