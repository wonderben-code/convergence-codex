import LovelockReflections
import RicciFlatSharp

/-!
# Coordinate reflections on a four-index array, and the normal form they force

`LovelockReflections` did this one slot-pair at a time, on 2-tensors: `act2 (reflect k) S b c` is
`S b c` times `(1 − 2δ_{bk})(1 − 2δ_{ck})`, the sign is `−1` at exactly the entries the reflection
moves, and a real number equal to its own negative is zero. That was step 1 of the three-step route
to `RicciProportional`, and `LovelockDiagonalise` finished the route.

**The same computation has never been run on `act`**, where the array has four slots and the sign is
a product of four factors. This file runs it, and then says what the resulting support condition
costs an algebraic curvature tensor.

## What is proved

* **`act_reflect_four`** — `act (reflect k) R a b c d = (1−2δ_{ak})(1−2δ_{bk})(1−2δ_{ck})(1−2δ_{dk})
  · R a b c d`, the four-index twin of `AlgebraicCurvature.act2_reflect`. No hypotheses: not
  `IsAlgCurv`, not symmetry, nothing;
* `reflect_factor_pair_eq` — **which generalises `LovelockReflections.reflect_factor_self`**: that
  lemma is the `b = c` case, and what the sign actually depends on is only whether the two slots
  agree *about `k`*. One restrictive hypothesis removed, in passing;
* `sign_quad_left`, `sign_quad_right` — the sign is `−1` when an odd number of the four slots hold
  `k`; and `sign_quad_agree`, `sign_quad_cross` — it is `+1` when an even number do. **The second
  pair is not used by anything below**, and it is proved because the word *exactly* in the sentence
  above is otherwise half a theorem. All four are stated as two pairings rather than as a parity
  predicate, because that is the form the corollaries consume and it needs no counting gadget;
* **`eq_zero_of_sign_neg`** and the four slot lemmas `eq_zero_of_fst_ne` …
  `eq_zero_of_fth_ne` — **an array fixed by every coordinate reflection vanishes at every entry
  where some slot holds a value no other slot holds**;
* `exists_eq_of_ne_zero` — the same as one statement, and **it needs no curvature symmetries at
  all**;
* **`eq_zero_of_ne_pattern`** — and *with* the two antisymmetries, the support collapses much
  further: a reflection-invariant algebraic curvature tensor vanishes unless `(c,d)` is `(a,b)` or
  `(b,a)`;
* **`eq_of_diag_eq`** — so such a tensor is **determined by the numbers `R a b a b`**. Two
  reflection-invariant algebraic curvature tensors agreeing there are equal.

## The class is not empty, and it is not empty of the interesting case either

`WeylNonzeroFour` exists because a statement about a class nobody has shown inhabited is worth
nothing, and the same test applies to `eq_of_diag_eq`. It is applied twice here, because passing it
once would have been misleading:

* `act_reflect_knSquare_diagonal` says `knSquare h` is reflection-invariant for **every** diagonal
  `h` — an `n`-parameter family — and **`exists_ne_zero_reflect_invariant`** picks `h = δ`, where
  `knSquare δ` is `constCurv n` (`knSquare_delta`) and `constCurv_ne_zero` keeps it off the floor
  for `n ≥ 2`. **But `constCurv` is pure scalar curvature and carries no Weyl at all**, so on its
  own that witness leaves open whether §4 ever meets the tensors `KillsWeyl` is about;
* **`exists_ricciFlat_reflect_invariant`** closes that: at every `n ≥ 4`, `RicciFlatSharp`'s
  witness — non-zero, Ricci-flat, hence its own Weyl part — **is reflection-invariant too**. The
  only new step is `act_weylPart` moving the frame change inside the projection.

`symm_of_diagonal` is the half-line that lets `isAlgCurv_knSquare` accept a diagonal `h`, and
`diagonal_twoProj` is the same service for `WeylNonzeroGeneral.twoProj`.

## What this is for, and what it is not

**It is the first rung of a candidate elementary route to `KillsWeyl`**, and naming that is a
correction rather than a claim. `WALLS` §W5.0 §5c point 7 says of the missing complete-reducibility
step that there is *"an elementary substitute, of which nobody has exhibited even a candidate"*.
**That sentence is now false**, and `WALLS` §W5.0 §5d states the candidate and the two places it is
still open. Standing orders say findings are folded back by proving more, so the rung it needs
first is proved here rather than the sentence being edited into vagueness.

**It is not progress on `KillsWeyl`, and the watchlist item does not move.** A candidate route with
named gaps is not a proof, and this one's gaps are real. It runs through the adjoint of `T` against
`LovelockOrthogonality.ip`, and (i) the estate's equivariance hypothesis is assumed only at
algebraic curvature tensors, which is exactly where the adjoint would need it unconditionally, and
(ii) nothing says the adjoint lands in the algebraic curvature tensors at all. Nothing in this file
closes either, and nothing in this file should be read as narrowing them.

**And it says nothing about what an equivariant `T` does to the Weyl summand.** `weylPart` appears
in exactly one place — §6's witness, where it builds a tensor satisfying §4's hypotheses. No
theorem here has `T` in it.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockReflectionFour

open AlgebraicCurvature LovelockProjections LovelockEquivariance LovelockReflections Finset

variable {n : ℕ}

/-! ## 1. The sign a reflection puts on a four-index entry

`AlgebraicCurvature.act2_reflect` is the two-slot statement. This is the four-slot one, and the
proof is the same shape as `act_delta`'s: `reflect` is diagonal, so exactly one term of the
quadruple product index survives.
-/

/-- **A COORDINATE REFLECTION MULTIPLIES A FOUR-INDEX ENTRY BY FOUR SIGNS.** The four-index twin of
`AlgebraicCurvature.act2_reflect`, with no hypothesis on `R` whatever. -/
theorem act_reflect_four (k : Fin n) (R : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    act (reflect k) R a b c d
      = (1 - 2 * delta a k) * (1 - 2 * delta b k) * (1 - 2 * delta c k) * (1 - 2 * delta d k)
        * R a b c d := by
  simp only [act, reflect_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single c]
      · rw [Finset.sum_eq_single d]
        · simp [delta_self]
        · intro x _ hx; simp [delta, Ne.symm hx]
        · intro h; exact absurd (Finset.mem_univ d) h
      · intro x _ hx
        refine Finset.sum_eq_zero fun y _ => ?_
        simp [delta, Ne.symm hx]
      · intro h; exact absurd (Finset.mem_univ c) h
    · intro x _ hx
      refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun z _ => ?_
      simp [delta, Ne.symm hx]
    · intro h; exact absurd (Finset.mem_univ b) h
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun z _ =>
      Finset.sum_eq_zero fun w _ => ?_
    simp [delta, Ne.symm hx]
  · intro h; exact absurd (Finset.mem_univ a) h

/-! ## 2. When the four signs multiply to `−1`

`LovelockReflections` needed two facts about the factor: that it squares to one, and that a pair of
slots disagreeing about `k` contributes `−1`. The first of those turns out to be a special case of
a lemma about *pairs*, which is what §1's four factors want.
-/

/-- **THE SIGN OF A PAIR THAT AGREES ABOUT `k` IS `+1`**, whether both slots hold `k` or neither
does. **This generalises `LovelockReflections.reflect_factor_self`**, which is the `b = c` case: the
hypothesis that lemma really needs is not that the two slots are the same slot, only that they
answer the same way. -/
theorem reflect_factor_pair_eq {k b c : Fin n} (hbc : (b = k) = (c = k)) :
    (1 - 2 * delta b k) * (1 - 2 * delta c k) = (1 : ℝ) := by
  by_cases hb : b = k
  · have hc : c = k := by rw [← hbc]; exact hb
    norm_num [delta, hb, hc]
  · have hc : ¬ c = k := by rw [← hbc]; exact hb
    norm_num [delta, hb, hc]

/-- The four-factor sign is `−1` when the first pair disagrees about `k` and the second agrees.
Together with `sign_quad_right` this covers **every odd number of slots holding `k`**: one slot in
the first pair, or three with the odd one out in the first pair. -/
theorem sign_quad_left {k a b c d : Fin n} (hab : (a = k) ≠ (b = k)) (hcd : (c = k) = (d = k)) :
    (1 - 2 * delta a k) * (1 - 2 * delta b k) * (1 - 2 * delta c k) * (1 - 2 * delta d k)
      = (-1 : ℝ) := by
  have h1 := reflect_factor_pair hab
  have h2 := reflect_factor_pair_eq hcd
  linear_combination ((1 - 2 * delta c k) * (1 - 2 * delta d k)) * h1 - h2

/-- And with the roles of the two pairs exchanged. -/
theorem sign_quad_right {k a b c d : Fin n} (hab : (a = k) = (b = k)) (hcd : (c = k) ≠ (d = k)) :
    (1 - 2 * delta a k) * (1 - 2 * delta b k) * (1 - 2 * delta c k) * (1 - 2 * delta d k)
      = (-1 : ℝ) := by
  have h1 := reflect_factor_pair_eq hab
  have h2 := reflect_factor_pair hcd
  linear_combination ((1 - 2 * delta c k) * (1 - 2 * delta d k)) * h1 + h2

/-- The other half of the dichotomy: **both pairs agreeing about `k` gives `+1`.** Nothing below
consumes it, and it is here because without it the word *exactly* in this section's claim would be
half a theorem. -/
theorem sign_quad_agree {k a b c d : Fin n} (hab : (a = k) = (b = k)) (hcd : (c = k) = (d = k)) :
    (1 - 2 * delta a k) * (1 - 2 * delta b k) * (1 - 2 * delta c k) * (1 - 2 * delta d k)
      = (1 : ℝ) := by
  have h1 := reflect_factor_pair_eq hab
  have h2 := reflect_factor_pair_eq hcd
  linear_combination ((1 - 2 * delta c k) * (1 - 2 * delta d k)) * h1 + h2

/-- And **both pairs disagreeing also gives `+1`** — two slots holding `k`, one in each pair. With
`sign_quad_agree` this exhausts the even cases, so `sign_quad_left` and `sign_quad_right` really do
cover exactly the odd ones. -/
theorem sign_quad_cross {k a b c d : Fin n} (hab : (a = k) ≠ (b = k)) (hcd : (c = k) ≠ (d = k)) :
    (1 - 2 * delta a k) * (1 - 2 * delta b k) * (1 - 2 * delta c k) * (1 - 2 * delta d k)
      = (1 : ℝ) := by
  have h1 := reflect_factor_pair hab
  have h2 := reflect_factor_pair hcd
  linear_combination ((1 - 2 * delta c k) * (1 - 2 * delta d k)) * h1 - h2

/-! ## 3. What invariance under every reflection forces

The whole content is `LovelockReflections`' again: a real number equal to its own negative is zero.
-/

variable {R : Fin n → Fin n → Fin n → Fin n → ℝ}

/-- **AN ENTRY THE REFLECTION NEGATES IS ZERO**, for an array fixed by that reflection. -/
theorem eq_zero_of_sign_neg
    (hfix : ∀ k a b c d, act (reflect k) R a b c d = R a b c d) (k a b c d : Fin n)
    (hsign : (1 - 2 * delta a k) * (1 - 2 * delta b k) * (1 - 2 * delta c k) * (1 - 2 * delta d k)
      = (-1 : ℝ)) :
    R a b c d = 0 := by
  have h := hfix k a b c d
  rw [act_reflect_four, hsign] at h
  linarith

/-- **A VALUE HELD BY THE FIRST SLOT ALONE KILLS THE ENTRY.** Reflect in that value. -/
theorem eq_zero_of_fst_ne (hfix : ∀ k a b c d, act (reflect k) R a b c d = R a b c d)
    {a b c d : Fin n} (hb : b ≠ a) (hc : c ≠ a) (hd : d ≠ a) : R a b c d = 0 := by
  refine eq_zero_of_sign_neg hfix a a b c d (sign_quad_left ?_ ?_)
  · simp [hb]
  · simp [hc, hd]

/-- The same for the second slot. -/
theorem eq_zero_of_snd_ne (hfix : ∀ k a b c d, act (reflect k) R a b c d = R a b c d)
    {a b c d : Fin n} (ha : a ≠ b) (hc : c ≠ b) (hd : d ≠ b) : R a b c d = 0 := by
  refine eq_zero_of_sign_neg hfix b a b c d (sign_quad_left ?_ ?_)
  · simp [ha]
  · simp [hc, hd]

/-- The third. -/
theorem eq_zero_of_thd_ne (hfix : ∀ k a b c d, act (reflect k) R a b c d = R a b c d)
    {a b c d : Fin n} (ha : a ≠ c) (hb : b ≠ c) (hd : d ≠ c) : R a b c d = 0 := by
  refine eq_zero_of_sign_neg hfix c a b c d (sign_quad_right ?_ ?_)
  · simp [ha, hb]
  · simp [hd]

/-- The fourth. -/
theorem eq_zero_of_fth_ne (hfix : ∀ k a b c d, act (reflect k) R a b c d = R a b c d)
    {a b c d : Fin n} (ha : a ≠ d) (hb : b ≠ d) (hc : c ≠ d) : R a b c d = 0 := by
  refine eq_zero_of_sign_neg hfix d a b c d (sign_quad_right ?_ ?_)
  · simp [ha, hb]
  · simp [hc]

/-- **THE SUPPORT CONDITION IN ONE STATEMENT**: at a non-zero entry, every slot's value is held by
some other slot as well. **No curvature symmetries are used**, so this is a fact about arbitrary
four-index arrays fixed by the coordinate reflections. -/
theorem exists_eq_of_ne_zero (hfix : ∀ k a b c d, act (reflect k) R a b c d = R a b c d)
    {a b c d : Fin n} (h : R a b c d ≠ 0) :
    (b = a ∨ c = a ∨ d = a) ∧ (a = b ∨ c = b ∨ d = b) ∧ (a = c ∨ b = c ∨ d = c)
      ∧ (a = d ∨ b = d ∨ c = d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hcon
    exact h (eq_zero_of_fst_ne hfix (fun e => hcon (Or.inl e))
      (fun e => hcon (Or.inr (Or.inl e))) (fun e => hcon (Or.inr (Or.inr e))))
  · by_contra hcon
    exact h (eq_zero_of_snd_ne hfix (fun e => hcon (Or.inl e))
      (fun e => hcon (Or.inr (Or.inl e))) (fun e => hcon (Or.inr (Or.inr e))))
  · by_contra hcon
    exact h (eq_zero_of_thd_ne hfix (fun e => hcon (Or.inl e))
      (fun e => hcon (Or.inr (Or.inl e))) (fun e => hcon (Or.inr (Or.inr e))))
  · by_contra hcon
    exact h (eq_zero_of_fth_ne hfix (fun e => hcon (Or.inl e))
      (fun e => hcon (Or.inr (Or.inl e))) (fun e => hcon (Or.inr (Or.inr e))))

/-! ## 4. And with the curvature symmetries, a normal form

Two antisymmetries kill the entries where a slot pair repeats a value, and §3 kills the entries
where a value appears once. What is left is `R_{abab}` and `R_{abba}`, and the second is minus the
first.
-/

/-- **A REFLECTION-INVARIANT ALGEBRAIC CURVATURE TENSOR IS SUPPORTED ON `R_{abab}` AND
`R_{abba}`.** Only `antisymm_left` and `antisymm_right` are used — not the pair symmetry, not
Bianchi. -/
theorem eq_zero_of_ne_pattern (hR : IsAlgCurv R)
    (hfix : ∀ k a b c d, act (reflect k) R a b c d = R a b c d) {a b c d : Fin n}
    (hne : ¬ ((c = a ∧ d = b) ∨ (c = b ∧ d = a))) : R a b c d = 0 := by
  by_cases hab : a = b
  · subst hab
    have h := hR.antisymm_left a a c d
    linarith
  by_cases hcd : c = d
  · subst hcd
    have h := hR.antisymm_right a b c c
    linarith
  by_cases hca : c = a
  · have hdb : d ≠ b := fun e => hne (Or.inl ⟨hca, e⟩)
    have hda : d ≠ a := fun e => hcd (hca.trans e.symm)
    exact eq_zero_of_fth_ne hfix (Ne.symm hda) (Ne.symm hdb) hcd
  by_cases hcb : c = b
  · have hda : d ≠ a := fun e => hne (Or.inr ⟨hcb, e⟩)
    have hdb : d ≠ b := fun e => hcd (hcb.trans e.symm)
    exact eq_zero_of_fth_ne hfix (Ne.symm hda) (Ne.symm hdb) hcd
  · exact eq_zero_of_thd_ne hfix (Ne.symm hca) (Ne.symm hcb) (Ne.symm hcd)

/-- **SO SUCH A TENSOR IS DETERMINED BY THE NUMBERS `R a b a b`.** Off the pattern both sides
vanish; on it they agree by hypothesis or by one antisymmetry. -/
theorem eq_of_diag_eq {R S : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hR : IsAlgCurv R) (hS : IsAlgCurv S)
    (hfixR : ∀ k a b c d, act (reflect k) R a b c d = R a b c d)
    (hfixS : ∀ k a b c d, act (reflect k) S a b c d = S a b c d)
    (hdiag : ∀ a b, R a b a b = S a b a b) (a b c d : Fin n) : R a b c d = S a b c d := by
  by_cases hp : (c = a ∧ d = b) ∨ (c = b ∧ d = a)
  · rcases hp with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · rw [hc, hd]; exact hdiag a b
    · have h1 : R a b b a = - R a b a b := by rw [hR.antisymm_right a b a b]; ring
      have h2 : S a b b a = - S a b a b := by rw [hS.antisymm_right a b a b]; ring
      rw [hc, hd, h1, h2, hdiag a b]
  · rw [eq_zero_of_ne_pattern hR hfixR hp, eq_zero_of_ne_pattern hS hfixS hp]

/-! ## 5. The class is inhabited, and by more than one tensor

`WeylNonzeroFour`'s standard: a normal-form theorem about a class nobody has shown inhabited says
nothing. Every diagonal `h` gives one, by `act2_reflect_of_diagonal` and `act_kn`.
-/

/-- A diagonal array is symmetric, because both off-diagonal entries are zero. What
`isAlgCurv_knSquare` needs, from what §5 has. -/
theorem symm_of_diagonal {h : Fin n → Fin n → ℝ} (hh : ∀ b c, b ≠ c → h b c = 0) (a b : Fin n) :
    h a b = h b a := by
  by_cases hab : a = b
  · rw [hab]
  · rw [hh a b hab, hh b a (Ne.symm hab)]

/-- **AN `n`-PARAMETER FAMILY OF REFLECTION-INVARIANT CURVATURE TENSORS.** `act_kn` passes the
frame change through the Kulkarni–Nomizu product, and `act2_reflect_of_diagonal` says a reflection
fixes a diagonal 2-tensor. -/
theorem act_reflect_knSquare_diagonal {h : Fin n → Fin n → ℝ}
    (hh : ∀ b c, b ≠ c → h b c = 0) (m a b c d : Fin n) :
    act (reflect m) (knSquare h) a b c d = knSquare h a b c d := by
  have hfun : (fun x y z w => (2 : ℝ) * knSquare h x y z w) = kn h h := by
    funext x y z w
    show (2 : ℝ) * knSquare h x y z w = kn h h x y z w
    rw [kn_self]
  have key : act (reflect m) (fun x y z w => (2 : ℝ) * knSquare h x y z w) a b c d
      = 2 * knSquare h a b c d := by
    rw [hfun, act_kn, act2_reflect_of_diagonal hh, kn_self]
  rw [act_smul] at key
  linarith

/-- **AND ONE OF THEM IS NOT ZERO**, so §4 is not a statement about the zero tensor alone.
`knSquare δ` is `constCurv n`, which `constCurv_ne_zero` keeps off the floor for `n ≥ 2`. -/
theorem exists_ne_zero_reflect_invariant (hn : 2 ≤ n) :
    ∃ R : Fin n → Fin n → Fin n → Fin n → ℝ, IsAlgCurv R
      ∧ (∀ m a b c d, act (reflect m) R a b c d = R a b c d)
      ∧ R ≠ fun _ _ _ _ => (0 : ℝ) := by
  have hdiag : ∀ b c : Fin n, b ≠ c → (delta : Fin n → Fin n → ℝ) b c = 0 := by
    intro b c hbc; simp [delta, hbc]
  refine ⟨knSquare delta, isAlgCurv_knSquare (symm_of_diagonal hdiag),
    fun m a b c d => act_reflect_knSquare_diagonal hdiag m a b c d, ?_⟩
  rw [knSquare_delta]
  exact constCurv_ne_zero hn

/-- `WeylNonzeroGeneral.twoProj` is diagonal — a sum of two rank-one projectors onto coordinate
axes. What §5's witness machinery needs from it. -/
theorem diagonal_twoProj (i j : Fin n) {b c : Fin n} (hbc : b ≠ c) :
    WeylNonzeroGeneral.twoProj i j b c = 0 := by
  have h1 : delta b i * delta c i = (0 : ℝ) := by
    by_cases hbi : b = i
    · have hci : ¬ c = i := fun e => hbc (hbi.trans e.symm)
      simp [delta, hci]
    · simp [delta, hbi]
  have h2 : delta b j * delta c j = (0 : ℝ) := by
    by_cases hbj : b = j
    · have hcj : ¬ c = j := fun e => hbc (hbj.trans e.symm)
      simp [delta, hcj]
    · simp [delta, hbj]
  simp only [WeylNonzeroGeneral.twoProj, h1, h2, add_zero]

/-! ## 6. And the class contains a tensor that is pure Weyl

The witness of §5 is `constCurv`, which is all scalar curvature and no Weyl at all — so on its own
it leaves open whether §4's normal form ever meets the tensors `KillsWeyl` is a statement about.
It does. `RicciFlatSharp`'s witness is reflection-invariant too, and it is Ricci-flat and non-zero
at every `n ≥ 4`, hence **all Weyl**.
-/

/-- **A NON-ZERO RICCI-FLAT REFLECTION-INVARIANT ALGEBRAIC CURVATURE TENSOR**, at every `n ≥ 4`.
Ricci-flat and algebraic-curvature means it is its own Weyl part, so §4's normal form is a
statement about Weyl-carrying tensors and not only about the Kulkarni–Nomizu family. The witness
is `RicciFlatSharp`'s, and the only new step is that a reflection fixes it: `act_weylPart` moves
the frame change inside the projection, and §5 fixes what is left. -/
theorem exists_ricciFlat_reflect_invariant (hn : 4 ≤ n) :
    ∃ R : Fin n → Fin n → Fin n → Fin n → ℝ, IsAlgCurv R
      ∧ (∀ m a b c d, act (reflect m) R a b c d = R a b c d)
      ∧ (∀ b c, ricci R b c = 0) ∧ R ≠ fun _ _ _ _ => (0 : ℝ) := by
  have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
  have hij : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by norm_num)
  set i : Fin n := ⟨0, by omega⟩ with hi
  set j : Fin n := ⟨1, by omega⟩ with hj
  have hbase : IsAlgCurv (knSquare (WeylNonzeroGeneral.twoProj i j)) :=
    WeylNonzeroGeneral.isAlgCurv_twoProjCurv i j
  refine ⟨weylPart (knSquare (WeylNonzeroGeneral.twoProj i j)), isAlgCurv_weylPart hbase, ?_,
    fun b c => ricci_weylPart hn1 hn2 _ b c,
    WeylNonzeroGeneral.weylPart_ne_zero_of_four_le hn hij⟩
  intro m a b c d
  have hfix : act (reflect m) (knSquare (WeylNonzeroGeneral.twoProj i j))
      = knSquare (WeylNonzeroGeneral.twoProj i j) :=
    funext fun x => funext fun y => funext fun z => funext fun w =>
      act_reflect_knSquare_diagonal (fun p q hpq => diagonal_twoProj i j hpq) m x y z w
  rw [act_weylPart (isOrth_reflect m), hfix]

end LovelockReflectionFour
