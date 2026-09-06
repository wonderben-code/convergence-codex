import RayCircuitSurrounding

/-!
# How far the enclosure step off `+` actually reaches: the even-degree condition, read on the box

`RayCircuitSurrounding.exists_circuit_surrounding_leftRay` replaced `PlusBoundary` by
**`EvenDegrees (dualGraph σ)`** in Peierls' enclosure step. That is a hypothesis about the dual
graph, and *"no boundary condition"* is an easy thing to read into it. This file says what it is.

> **`evenDegrees_congr_boundary`** — it is a condition on the **boundary spins and nothing else**.
> Two configurations agreeing at every boundary site satisfy it together or not at all, however
> much they differ inside.

> **`left_rim_const`, `top_rim_const`, `right_rim_const`, `bottom_rim_const`** — and on the
> boundary it is severe: **no bond along the interior of a rim may be broken.**

> **`corner_bl_coupling`** and its three partners — **and the two rim neighbours of each corner
> must agree**, whatever the corner itself does.

So the class the enclosure step now reaches is: **the interior free, the four rims each constant
away from their corners, and the corner neighbourhoods glued.** It is strictly larger than `+`,
which fixes every boundary spin and every corner, and it is **not** all configurations — one
broken bond along the interior of a rim excludes a configuration outright. **No count and no
proportion is offered** (`ERRATUM 477`): how many configurations satisfy the condition is not
computed here, and neither comparison above is a statement about sizes.

## What is proved

**`notMem_of_unique_outward`, `mem_iff_of_two_outward`** — the two local facts, stated once
instead of eight times. A plaquette with exactly one outward direction has that side unbroken; one
with exactly two has them broken together or not at all. Both are `DualDegreeExact`'s
`evenDegrees_dualGraph_iff` plus the observation that the filter is then a singleton, and `1` is
odd.

**`unique_outward_left`, `unique_outward_up`, `unique_outward_right`, `unique_outward_down`** —
which directions of a rim plaquette face out. Each is four `fin_cases` against the matching
`*_eq_self_iff`.

**`sideL_notMem_of_evenDegrees`** and its three partners — so those sides are unbroken.

**`left_rim_const`, `right_rim_const`, `bottom_rim_const`, `top_rim_const`** — read on the
configuration: consecutive sites along the interior of a rim carry the same spin.

**`two_outward_corner_bl`** and its three partners, then **`corner_bl_coupling`** and its three —
at a corner plaquette exactly two directions face out, and `EvenDegrees` forces the two bonds to
be broken together, which says the corner's two rim neighbours agree.

**`all_outward_two`** — and the trichotomy *interior, one rim, or corner* genuinely needs
`2 < n`: in a `2 × 2` box the one plaquette has all four directions facing out.

**`no_outward_interior`** — an interior plaquette has no outward side at all, so the condition is
silent there; **`evenDegrees_congr_boundary`** is the sharp form of that, and it is the theorem
this file is for.

## What is NOT here

**THE GLOBAL STATEMENT IS NOT ASSEMBLED.** The rim constancies and the corner couplings together
say *every boundary site other than the four corners carries the same spin*, and **that sentence
is not a theorem here.** Chaining them needs a **ranged** variant of the
`Fin n` induction `NoBrokenOutwardCharacterised.const_of_step` does over the full range — here the
steps exist only for `1 ≤ j ≤ n - 3` — and then four corner glue steps. **Not attempted, no cost
claimed** (`ERRATUM 246`) — and the cost, unusually, is visible: it is the shape of that file's
§3 with shifted ranges.

**THE CONVERSE IS NOT PROVED.** Nothing here says a configuration constant on the boundary away
from the corners **satisfies** `EvenDegrees (dualGraph σ)`. That direction needs the trichotomy
*every plaquette is interior, one-rim or corner*, which is **not proved** either — and at `n =
2` it is false: `all_outward_two` exhibits the single plaquette of a `2 × 2` box with **all
four** directions facing out. Every corner theorem here carries `2 < n` for that reason.

**NO COUNT, NO PROPORTION, NO COMPARISON OF SIZES.** How many configurations satisfy the condition
is not computed. The two comparisons above are **containments read off the theorems** — `+`
implies the condition and a broken rim-interior bond refutes it — and neither is a statement about
how many configurations are involved.

**NOTHING IS REPAIRED AND NO HYPOTHESIS IS REMOVED.** This file adds no theorem to the Peierls
chain; it describes a hypothesis that chain already carries. `ExtendedDual`'s four-rim
construction is still the repair and is still untouched. **W3 does not move.**

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): the two local facts and
`evenDegrees_congr_boundary` take **nothing** about `n`; the four `unique_outward_*` and the four
`*_notMem_*` take the plaquette's position and the plaquette's own bounds; the four `*_rim_const`
take the same in index form, two of them with `1 < n` to name the far rim; every corner theorem
takes **`2 < n`**. No `PlusBoundary` anywhere in this file.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace EvenDegreesReach

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette PlaquetteLattice
open IsingBoundaryField DualObstruction DualGraph ExtendedDual DualDegreeExact
open RimBoundary SimpleGraph

/- `Outward` is a `def`, so instance search cannot see the `DecidableEq (Plaq n)` behind it and
the predicate below has no inferrable instance. `DualDegreeExact` opens the classical one for the
same predicate; this file must open the same one or `evenDegrees_dualGraph_iff`'s filter and this
file's will carry different instances and no rewrite between them will fire. -/
set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The two local facts, once each rather than eight times -/

/-- **A PLAQUETTE WITH EXACTLY ONE OUTWARD SIDE HAS THAT SIDE UNBROKEN.** Its outward-broken count
is `0` or `1`, and `EvenDegrees` forbids `1`. -/
theorem notMem_of_unique_outward {σ : Config n} (hev : EvenDegrees (dualGraph σ)) {P : Plaq n}
    {d : Fin 4} (hout : Outward P d) (huniq : ∀ e : Fin 4, Outward P e → e = d) :
    sideOf P d ∉ contour σ := by
  intro hmem
  have hfilter : (Finset.univ.filter fun e : Fin 4 => sideOf P e ∈ contour σ ∧ Outward P e)
      = {d} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => huniq e h.2, by rintro rfl; exact ⟨hmem, hout⟩⟩
  have hcount := (evenDegrees_dualGraph_iff σ).mp hev P
  rw [Finset.filter_congr_decidable] at hcount
  rw [hfilter, Finset.card_singleton] at hcount
  simp at hcount

/-- **A PLAQUETTE WITH EXACTLY TWO OUTWARD SIDES HAS THEM BROKEN TOGETHER OR NOT AT ALL.** -/
theorem mem_iff_of_two_outward {σ : Config n} (hev : EvenDegrees (dualGraph σ)) {P : Plaq n}
    {d e : Fin 4} (hd : Outward P d) (he : Outward P e)
    (huniq : ∀ f : Fin 4, Outward P f → f = d ∨ f = e) :
    sideOf P d ∈ contour σ ↔ sideOf P e ∈ contour σ := by
  have key : ∀ {a b : Fin 4}, Outward P a → Outward P b →
      (∀ f : Fin 4, Outward P f → f = a ∨ f = b) →
      sideOf P a ∈ contour σ → sideOf P b ∉ contour σ → False := by
    intro a b ha _ hu hma hmb
    have hfilter : (Finset.univ.filter fun f : Fin 4 => sideOf P f ∈ contour σ ∧ Outward P f)
        = {a} := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hm, ho⟩
        rcases hu f ho with rfl | rfl
        · rfl
        · exact absurd hm hmb
      · rintro rfl; exact ⟨hma, ha⟩
    have hcount := (evenDegrees_dualGraph_iff σ).mp hev P
    rw [Finset.filter_congr_decidable] at hcount
    rw [hfilter, Finset.card_singleton] at hcount
    simp at hcount
  constructor
  · intro hma
    by_contra hmb
    exact key hd he huniq hma hmb
  · intro hmb
    by_contra hma
    exact key he hd (fun f hf => (huniq f hf).symm) hmb hma

/-! ## 2. Which directions of a rim plaquette face out -/

theorem unique_outward_left {P : Plaq n} (hi : P.i = 0) (hj0 : 0 < P.j) (hj1 : P.j + 2 < n) :
    ∀ e : Fin 4, Outward P e → e = 0 := by
  have h1 := P.hi
  have h2 := P.hj
  intro e he
  fin_cases e
  · rfl
  · exact absurd ((upP_eq_self_iff P).mp he) (by omega)
  · exact absurd ((rightP_eq_self_iff P).mp he) (by omega)
  · exact absurd ((downP_eq_self_iff P).mp he) (by omega)

theorem unique_outward_right {P : Plaq n} (hi : P.i + 2 = n) (hj0 : 0 < P.j) (hj1 : P.j + 2 < n) :
    ∀ e : Fin 4, Outward P e → e = 2 := by
  have h1 := P.hi
  have h2 := P.hj
  intro e he
  fin_cases e
  · exact absurd ((leftP_eq_self_iff P).mp he) (by omega)
  · exact absurd ((upP_eq_self_iff P).mp he) (by omega)
  · rfl
  · exact absurd ((downP_eq_self_iff P).mp he) (by omega)

theorem unique_outward_down {P : Plaq n} (hj : P.j = 0) (hi0 : 0 < P.i) (hi1 : P.i + 2 < n) :
    ∀ e : Fin 4, Outward P e → e = 3 := by
  have h1 := P.hi
  have h2 := P.hj
  intro e he
  fin_cases e
  · exact absurd ((leftP_eq_self_iff P).mp he) (by omega)
  · exact absurd ((upP_eq_self_iff P).mp he) (by omega)
  · exact absurd ((rightP_eq_self_iff P).mp he) (by omega)
  · rfl

theorem unique_outward_up {P : Plaq n} (hj : P.j + 2 = n) (hi0 : 0 < P.i) (hi1 : P.i + 2 < n) :
    ∀ e : Fin 4, Outward P e → e = 1 := by
  have h1 := P.hi
  have h2 := P.hj
  intro e he
  fin_cases e
  · exact absurd ((leftP_eq_self_iff P).mp he) (by omega)
  · rfl
  · exact absurd ((rightP_eq_self_iff P).mp he) (by omega)
  · exact absurd ((downP_eq_self_iff P).mp he) (by omega)

/-! ## 3. So no bond along the interior of a rim is broken -/

theorem sideL_notMem_of_evenDegrees {σ : Config n} (hev : EvenDegrees (dualGraph σ)) {P : Plaq n}
    (hi : P.i = 0) (hj0 : 0 < P.j) (hj1 : P.j + 2 < n) : sideL P ∉ contour σ :=
  notMem_of_unique_outward (d := 0) hev ((leftP_eq_self_iff P).mpr hi)
    (unique_outward_left hi hj0 hj1)

theorem sideR_notMem_of_evenDegrees {σ : Config n} (hev : EvenDegrees (dualGraph σ)) {P : Plaq n}
    (hi : P.i + 2 = n) (hj0 : 0 < P.j) (hj1 : P.j + 2 < n) : sideR P ∉ contour σ :=
  notMem_of_unique_outward (d := 2) hev ((rightP_eq_self_iff P).mpr hi)
    (unique_outward_right hi hj0 hj1)

theorem sideD_notMem_of_evenDegrees {σ : Config n} (hev : EvenDegrees (dualGraph σ)) {P : Plaq n}
    (hj : P.j = 0) (hi0 : 0 < P.i) (hi1 : P.i + 2 < n) : sideD P ∉ contour σ :=
  notMem_of_unique_outward (d := 3) hev ((downP_eq_self_iff P).mpr hj)
    (unique_outward_down hj hi0 hi1)

theorem sideU_notMem_of_evenDegrees {σ : Config n} (hev : EvenDegrees (dualGraph σ)) {P : Plaq n}
    (hj : P.j + 2 = n) (hi0 : 0 < P.i) (hi1 : P.i + 2 < n) : sideU P ∉ contour σ :=
  notMem_of_unique_outward (d := 1) hev ((upP_eq_self_iff P).mpr hj)
    (unique_outward_up hj hi0 hi1)

/-! ## 4. Read on the configuration -/

theorem left_rim_const {σ : Config n} (hev : EvenDegrees (dualGraph σ)) {j : ℕ}
    (hj0 : 0 < j) (hj1 : j + 2 < n) :
    σ ((⟨0, by omega⟩ : Fin n), (⟨j, by omega⟩ : Fin n))
      = σ ((⟨0, by omega⟩ : Fin n), (⟨j + 1, by omega⟩ : Fin n)) := by
  have hP : (0 : ℕ) + 1 < n := by omega
  have hQ : j + 1 < n := by omega
  have h := sideL_notMem_of_evenDegrees hev (P := (⟨0, j, hP, hQ⟩ : Plaq n)) rfl hj0 hj1
  rw [sideL, mem_contour] at h
  push Not at h
  exact h (adj_sideL _)

theorem right_rim_const {σ : Config n} (hev : EvenDegrees (dualGraph σ)) {j : ℕ}
    (hj0 : 0 < j) (hj1 : j + 2 < n) (hn : 1 < n) :
    σ ((⟨n - 2 + 1, by omega⟩ : Fin n), (⟨j, by omega⟩ : Fin n))
      = σ ((⟨n - 2 + 1, by omega⟩ : Fin n), (⟨j + 1, by omega⟩ : Fin n)) := by
  have hP : n - 2 + 1 < n := by omega
  have hQ : j + 1 < n := by omega
  have h := sideR_notMem_of_evenDegrees hev (P := (⟨n - 2, j, hP, hQ⟩ : Plaq n))
    (show n - 2 + 2 = n by omega) hj0 hj1
  rw [sideR, mem_contour] at h
  push Not at h
  exact (h (adj_sideR _)).symm

theorem bottom_rim_const {σ : Config n} (hev : EvenDegrees (dualGraph σ)) {i : ℕ}
    (hi0 : 0 < i) (hi1 : i + 2 < n) :
    σ ((⟨i, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin n))
      = σ ((⟨i + 1, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin n)) := by
  have hP : i + 1 < n := by omega
  have hQ : (0 : ℕ) + 1 < n := by omega
  have h := sideD_notMem_of_evenDegrees hev (P := (⟨i, 0, hP, hQ⟩ : Plaq n)) rfl hi0 hi1
  rw [sideD, mem_contour] at h
  push Not at h
  exact (h (adj_sideD _)).symm

theorem top_rim_const {σ : Config n} (hev : EvenDegrees (dualGraph σ)) {i : ℕ}
    (hi0 : 0 < i) (hi1 : i + 2 < n) (hn : 1 < n) :
    σ ((⟨i, by omega⟩ : Fin n), (⟨n - 2 + 1, by omega⟩ : Fin n))
      = σ ((⟨i + 1, by omega⟩ : Fin n), (⟨n - 2 + 1, by omega⟩ : Fin n)) := by
  have hP : i + 1 < n := by omega
  have hQ : n - 2 + 1 < n := by omega
  have h := sideU_notMem_of_evenDegrees hev (P := (⟨i, n - 2, hP, hQ⟩ : Plaq n))
    (show n - 2 + 2 = n by omega) hi0 hi1
  rw [sideU, mem_contour] at h
  push Not at h
  exact h (adj_sideU _)

/-! ## 5. And at a corner plaquette the two outward sides are broken together or not at all -/

theorem two_outward_corner_bl {P : Plaq n} (hi : P.i = 0) (hj : P.j = 0) (hn : 2 < n) :
    ∀ f : Fin 4, Outward P f → f = 0 ∨ f = 3 := by
  have h1 := P.hi
  have h2 := P.hj
  intro f hf
  fin_cases f
  · exact Or.inl rfl
  · exact absurd ((upP_eq_self_iff P).mp hf) (by omega)
  · exact absurd ((rightP_eq_self_iff P).mp hf) (by omega)
  · exact Or.inr rfl

theorem two_outward_corner_tl {P : Plaq n} (hi : P.i = 0) (hj : P.j + 2 = n) (hn : 2 < n) :
    ∀ f : Fin 4, Outward P f → f = 0 ∨ f = 1 := by
  have h1 := P.hi
  have h2 := P.hj
  intro f hf
  fin_cases f
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd ((rightP_eq_self_iff P).mp hf) (by omega)
  · exact absurd ((downP_eq_self_iff P).mp hf) (by omega)

theorem two_outward_corner_br {P : Plaq n} (hi : P.i + 2 = n) (hj : P.j = 0) (hn : 2 < n) :
    ∀ f : Fin 4, Outward P f → f = 2 ∨ f = 3 := by
  have h1 := P.hi
  have h2 := P.hj
  intro f hf
  fin_cases f
  · exact absurd ((leftP_eq_self_iff P).mp hf) (by omega)
  · exact absurd ((upP_eq_self_iff P).mp hf) (by omega)
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem two_outward_corner_tr {P : Plaq n} (hi : P.i + 2 = n) (hj : P.j + 2 = n) (hn : 2 < n) :
    ∀ f : Fin 4, Outward P f → f = 2 ∨ f = 1 := by
  have h1 := P.hi
  have h2 := P.hj
  intro f hf
  fin_cases f
  · exact absurd ((leftP_eq_self_iff P).mp hf) (by omega)
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact absurd ((downP_eq_self_iff P).mp hf) (by omega)

/-! ## 6. Read on the configuration: the two rim neighbours of a corner agree

At the bottom-left corner the two outward sides are `sideL` and `sideD` of the plaquette `⟨0,0⟩`,
which share the corner site. Broken together or not at all is exactly *the two other endpoints
agree*, whatever the corner itself does. -/

theorem corner_bl_coupling {σ : Config n} (hev : EvenDegrees (dualGraph σ)) (hn : 2 < n) :
    σ (tl 0 0 (by omega) (by omega) : Site n) = σ (br 0 0 (by omega) (by omega) : Site n) := by
  have hP : (0 : ℕ) + 1 < n := by omega
  have ha1 : adj (bl 0 0 hP hP : Site n) (tl 0 0 hP hP) := adj_bl_tl 0 0 hP hP
  have ha2 : adj (br 0 0 hP hP : Site n) (bl 0 0 hP hP) := adj_br_bl 0 0 hP hP
  have h := mem_iff_of_two_outward (d := 0) (e := 3) hev
    ((leftP_eq_self_iff (⟨0, 0, hP, hP⟩ : Plaq n)).mpr rfl)
    ((downP_eq_self_iff (⟨0, 0, hP, hP⟩ : Plaq n)).mpr rfl)
    (two_outward_corner_bl rfl rfl hn)
  rw [show sideOf (⟨0, 0, hP, hP⟩ : Plaq n) 0 = sideL (⟨0, 0, hP, hP⟩ : Plaq n) from rfl,
    show sideOf (⟨0, 0, hP, hP⟩ : Plaq n) 3 = sideD (⟨0, 0, hP, hP⟩ : Plaq n) from rfl,
    sideL, sideD, mem_contour, mem_contour] at h
  rcases Bool.eq_false_or_eq_true (σ (bl 0 0 hP hP)) with hb | hb <;>
    rcases Bool.eq_false_or_eq_true (σ (tl 0 0 hP hP)) with ht | ht <;>
      rcases Bool.eq_false_or_eq_true (σ (br 0 0 hP hP)) with hr | hr <;>
        simp_all

theorem corner_tl_coupling {σ : Config n} (hev : EvenDegrees (dualGraph σ)) (hn : 2 < n) :
    σ (bl 0 (n - 2) (by omega) (by omega) : Site n)
      = σ (tr 0 (n - 2) (by omega) (by omega) : Site n) := by
  have hP : (0 : ℕ) + 1 < n := by omega
  have hQ : n - 2 + 1 < n := by omega
  have ha1 : adj (bl 0 (n - 2) hP hQ : Site n) (tl 0 (n - 2) hP hQ) := adj_bl_tl 0 (n - 2) hP hQ
  have ha2 : adj (tl 0 (n - 2) hP hQ : Site n) (tr 0 (n - 2) hP hQ) := adj_tl_tr 0 (n - 2) hP hQ
  have h := mem_iff_of_two_outward (d := 0) (e := 1) hev
    ((leftP_eq_self_iff (⟨0, n - 2, hP, hQ⟩ : Plaq n)).mpr rfl)
    ((upP_eq_self_iff (⟨0, n - 2, hP, hQ⟩ : Plaq n)).mpr (show n - 2 + 2 = n by omega))
    (two_outward_corner_tl rfl (show n - 2 + 2 = n by omega) hn)
  rw [show sideOf (⟨0, n - 2, hP, hQ⟩ : Plaq n) 0 = sideL (⟨0, n - 2, hP, hQ⟩ : Plaq n) from rfl,
    show sideOf (⟨0, n - 2, hP, hQ⟩ : Plaq n) 1 = sideU (⟨0, n - 2, hP, hQ⟩ : Plaq n) from rfl,
    sideL, sideU, mem_contour, mem_contour] at h
  rcases Bool.eq_false_or_eq_true (σ (bl 0 (n - 2) hP hQ)) with hb | hb <;>
    rcases Bool.eq_false_or_eq_true (σ (tl 0 (n - 2) hP hQ)) with ht | ht <;>
      rcases Bool.eq_false_or_eq_true (σ (tr 0 (n - 2) hP hQ)) with hr | hr <;>
        simp_all

theorem corner_br_coupling {σ : Config n} (hev : EvenDegrees (dualGraph σ)) (hn : 2 < n) :
    σ (tr (n - 2) 0 (by omega) (by omega) : Site n)
      = σ (bl (n - 2) 0 (by omega) (by omega) : Site n) := by
  have hP : n - 2 + 1 < n := by omega
  have hQ : (0 : ℕ) + 1 < n := by omega
  have ha1 : adj (tr (n - 2) 0 hP hQ : Site n) (br (n - 2) 0 hP hQ) := adj_tr_br (n - 2) 0 hP hQ
  have ha2 : adj (br (n - 2) 0 hP hQ : Site n) (bl (n - 2) 0 hP hQ) := adj_br_bl (n - 2) 0 hP hQ
  have h := mem_iff_of_two_outward (d := 2) (e := 3) hev
    ((rightP_eq_self_iff (⟨n - 2, 0, hP, hQ⟩ : Plaq n)).mpr (show n - 2 + 2 = n by omega))
    ((downP_eq_self_iff (⟨n - 2, 0, hP, hQ⟩ : Plaq n)).mpr rfl)
    (two_outward_corner_br (show n - 2 + 2 = n by omega) rfl hn)
  rw [show sideOf (⟨n - 2, 0, hP, hQ⟩ : Plaq n) 2 = sideR (⟨n - 2, 0, hP, hQ⟩ : Plaq n) from rfl,
    show sideOf (⟨n - 2, 0, hP, hQ⟩ : Plaq n) 3 = sideD (⟨n - 2, 0, hP, hQ⟩ : Plaq n) from rfl,
    sideR, sideD, mem_contour, mem_contour] at h
  rcases Bool.eq_false_or_eq_true (σ (tr (n - 2) 0 hP hQ)) with hb | hb <;>
    rcases Bool.eq_false_or_eq_true (σ (br (n - 2) 0 hP hQ)) with ht | ht <;>
      rcases Bool.eq_false_or_eq_true (σ (bl (n - 2) 0 hP hQ)) with hr | hr <;>
        simp_all

theorem corner_tr_coupling {σ : Config n} (hev : EvenDegrees (dualGraph σ)) (hn : 2 < n) :
    σ (br (n - 2) (n - 2) (by omega) (by omega) : Site n)
      = σ (tl (n - 2) (n - 2) (by omega) (by omega) : Site n) := by
  have hP : n - 2 + 1 < n := by omega
  have ha1 : adj (tr (n - 2) (n - 2) hP hP : Site n) (br (n - 2) (n - 2) hP hP) :=
    adj_tr_br (n - 2) (n - 2) hP hP
  have ha2 : adj (tl (n - 2) (n - 2) hP hP : Site n) (tr (n - 2) (n - 2) hP hP) :=
    adj_tl_tr (n - 2) (n - 2) hP hP
  have h := mem_iff_of_two_outward (d := 2) (e := 1) hev
    ((rightP_eq_self_iff (⟨n - 2, n - 2, hP, hP⟩ : Plaq n)).mpr (show n - 2 + 2 = n by omega))
    ((upP_eq_self_iff (⟨n - 2, n - 2, hP, hP⟩ : Plaq n)).mpr (show n - 2 + 2 = n by omega))
    (two_outward_corner_tr (show n - 2 + 2 = n by omega) (show n - 2 + 2 = n by omega) hn)
  rw [show sideOf (⟨n - 2, n - 2, hP, hP⟩ : Plaq n) 2
        = sideR (⟨n - 2, n - 2, hP, hP⟩ : Plaq n) from rfl,
    show sideOf (⟨n - 2, n - 2, hP, hP⟩ : Plaq n) 1
        = sideU (⟨n - 2, n - 2, hP, hP⟩ : Plaq n) from rfl,
    sideR, sideU, mem_contour, mem_contour] at h
  rcases Bool.eq_false_or_eq_true (σ (tr (n - 2) (n - 2) hP hP)) with hb | hb <;>
    rcases Bool.eq_false_or_eq_true (σ (br (n - 2) (n - 2) hP hP)) with ht | ht <;>
      rcases Bool.eq_false_or_eq_true (σ (tl (n - 2) (n - 2) hP hP)) with hr | hr <;>
        simp_all

/-! ## 7. And the condition says nothing about the interior

An interior plaquette has no outward side at all, so its count is `0` whatever the configuration
does; and more than that, the whole condition depends only on the spins along the edge of the
box. -/

theorem no_outward_interior {P : Plaq n} (hi0 : 0 < P.i) (hi1 : P.i + 2 < n)
    (hj0 : 0 < P.j) (hj1 : P.j + 2 < n) : ∀ e : Fin 4, ¬ Outward P e := by
  intro e he
  fin_cases e
  · exact absurd ((leftP_eq_self_iff P).mp he) (by omega)
  · exact absurd ((upP_eq_self_iff P).mp he) (by omega)
  · exact absurd ((rightP_eq_self_iff P).mp he) (by omega)
  · exact absurd ((downP_eq_self_iff P).mp he) (by omega)

/-- **AND AT `n = 2` THERE IS NO TRICHOTOMY**: the single plaquette of a `2 × 2` box faces out in
all four directions, which is why every corner theorem above carries `2 < n`. -/
theorem all_outward_two (d : Fin 4) : Outward (⟨0, 0, by omega, by omega⟩ : Plaq 2) d := by
  fin_cases d
  · exact (leftP_eq_self_iff _).mpr rfl
  · exact (upP_eq_self_iff _).mpr rfl
  · exact (rightP_eq_self_iff _).mpr rfl
  · exact (downP_eq_self_iff _).mpr rfl

/-- **THE EVEN-DEGREE CONDITION IS A CONDITION ON THE BOUNDARY SPINS AND NOTHING ELSE.** Two
configurations agreeing at every boundary site satisfy it together or not at all, however
much they differ inside. -/
theorem evenDegrees_congr_boundary {σ τ : Config n}
    (h : ∀ p : Site n, isBoundary p = true → σ p = τ p) :
    EvenDegrees (dualGraph σ) ↔ EvenDegrees (dualGraph τ) := by
  have key : ∀ (P : Plaq n) (d : Fin 4), Outward P d →
      (sideOf P d ∈ contour σ ↔ sideOf P d ∈ contour τ) := by
    intro P d hout
    have hb := RimBoundary.outward_side_isBoundary hout
    revert hb
    refine Sym2.ind (fun a b hb => ?_) (sideOf P d)
    rw [mem_contour, mem_contour, h a (hb a (Sym2.mem_mk_left a b)),
      h b (hb b (Sym2.mem_mk_right a b))]
  have hfil : ∀ P : Plaq n,
      (Finset.univ.filter fun d : Fin 4 => sideOf P d ∈ contour σ ∧ Outward P d)
        = (Finset.univ.filter fun d : Fin 4 => sideOf P d ∈ contour τ ∧ Outward P d) := by
    intro P
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hm => ⟨(key P d hm.2).mp hm.1, hm.2⟩, fun hm => ⟨(key P d hm.2).mpr hm.1, hm.2⟩⟩
  constructor
  · intro hev
    refine (evenDegrees_dualGraph_iff τ).mpr fun P => ?_
    have h1 := (evenDegrees_dualGraph_iff σ).mp hev P
    rw [Finset.filter_congr_decidable, hfil P] at h1
    rw [Finset.filter_congr_decidable]
    exact h1
  · intro hev
    refine (evenDegrees_dualGraph_iff σ).mpr fun P => ?_
    have h1 := (evenDegrees_dualGraph_iff τ).mp hev P
    rw [Finset.filter_congr_decidable, ← hfil P] at h1
    rw [Finset.filter_congr_decidable]
    exact h1

end EvenDegreesReach
