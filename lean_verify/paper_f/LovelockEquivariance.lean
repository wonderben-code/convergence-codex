import LovelockProjections

/-!
# The three projections are `O(n)`-equivariant

`LovelockProjections` ends by naming its own remaining leg, per `PROOF_STRATEGY` §3:

> making the three projections equivariant needs one more lemma,
> `act Q (kn h k) = kn (act2 Q h) (act2 Q k)`, which is the factorisation of a quadruple sum into
> two double sums. **That is the remaining leg and it is written down here rather than left
> implicit.**

**This is that leg, taken immediately** — §6's third question, *"if the unit I just finished WAS a
B: retry B → C right now, before touching the queue"*.

## What is delivered

`act_weylPart`, `act_ricciPart`, `act_scalPart`: for every orthogonal `Q`,

    act Q (weylPart R)  =  weylPart (act Q R)

and the same for the other two. So the splitting of `LovelockProjections` is not merely an
algebraic identity that happens to hold in one frame — **it commutes with every change of
orthonormal frame**, which is what makes the three pieces *representations* rather than
coordinates, and is the form the classification would consume.

The route is four steps and only the first is work:

* `act_factor` / `act_factor'` — the quadruple sum defining `act` factorises into the two double
  sums defining `act2`, in the two index pairings a Kulkarni–Nomizu product uses. Modelled on
  `AlgebraicCurvature.sum_act_delta_pair`, which does the same collapse for `δ ⊗ δ`; the second
  pairing is reduced to the first by the same `Fintype.sum_equiv` re-indexing `act_constCurv` uses.
* `act_kn` — assembles them. **Orthogonality is not needed here**, and that is worth naming: the
  factorisation is multilinearity of `act`, nothing else. `IsOrth` enters only later, through
  `act2_delta`, `scal_act` and `act_constCurv`.
* `act2_tracefreeRicci` — the trace-free Ricci tensor transports, which is `ricci_act` and
  `scal_act` from `AlgebraicCurvature` §12 plus linearity of `act2`.
* the three conclusions, one line each.

## The hypothesis audit, continued from `LovelockProjections`

That file recorded two hypotheses it had written down and never used. The same audit is run here
and its result is stated rather than left for a reader to infer:

* **`act_factor`, `act_factor'`, `act_kn`, `act_smul`, `act_sub`, `act2_smul`, `act2_sub` carry no
  `IsOrth`** — **seven of the thirteen** declarations here are pure multilinearity (count from
  `check_ledger.py --decls`, not from the list).
* **`IsOrth` is genuinely needed by the other six** — `act2_tracefreeRicci` and its function-level
  form, `act2_delta_fun`, and the three projection statements. `ricci_act` and `scal_act` both take
  it and `act2_delta` is false without it. So the hypothesis is not decorative and is not
  removable: an arbitrary linear frame change does *not* preserve this splitting, because the
  splitting is defined through traces taken against `δ`.

**One honest note about §2.** `act_smul`, `act_sub`, `act2_smul` and `act2_sub` are stated because
they are the general linearity facts and nothing in the estate had them — but **the assembly in
§§3–4 does not call them**, and that is deliberate rather than an oversight. `rw` cannot see
through an unapplied function argument: the goal carries `act Q (scalPart R)` with `scalPart R` as
a *function*, so a rewrite keyed on `act Q (fun x y z w => …)` never fires. Each assembly step
therefore repeats the one-line `simp only [act, …]` computation inline. The lemmas are kept as
vocabulary for a consumer that has the applied form, and this paragraph exists so that a reader
does not mistake them for load-bearing steps.

## What this is NOT

**It is still not Lovelock.** Equivariance of the projections is a property of three particular
maps; the classification asserts that *every* equivariant map into symmetric 2-tensors lies in the
span of `ricci` and `scal • δ`. That is an **exhaustion** statement, nothing here bears on it, and
`UNLOCK_WATCHLIST` keeps the item open for the reason it already gives — no decomposition into
irreducibles over `ℝ` without compactness of `O(n)` and Haar averaging.

**And `act` is still not known to be an action.** `AlgebraicCurvature`'s own §12 header says so:
`act (Q · Q') = act Q ∘ act Q'` is not proved there and is not proved here, and every theorem below
quantifies over a single `Q`. "Equivariant" is used below in exactly the sense the estate can
support: one frame change at a time.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockEquivariance

open AlgebraicCurvature LovelockProjections Finset

variable {n : ℕ} {Q : Fin n → Fin n → ℝ}

/-! ## 1. The quadruple sum factorises

`AlgebraicCurvature.sum_act_delta_pair` does this for `δ ⊗ δ` and then collapses the deltas and
spends orthogonality. Here nothing collapses and nothing is spent: the four `Q` factors are simply
regrouped into the two pairs the summand already pairs.
-/

/-- **THE `(a,d) | (b,c)` PAIRING.** -/
theorem act_factor (Q u v : Fin n → Fin n → ℝ) (a b c d : Fin n) :
    (∑ p : Fin n × Fin n × Fin n × Fin n,
      Q a p.1 * Q b p.2.1 * Q c p.2.2.1 * Q d p.2.2.2 * (u p.1 p.2.2.2 * v p.2.1 p.2.2.1))
      = act2 Q u a d * act2 Q v b c := by
  simp only [Fintype.sum_prod_type, act2]
  have step : ∀ x : Fin n,
      ∑ y, ∑ z, ∑ w, Q a x * Q b y * Q c z * Q d w * (u x w * v y z)
        = (∑ w, Q a x * Q d w * u x w) * ∑ y, ∑ z, Q b y * Q c z * v y z := by
    intro x
    have inner : ∀ y : Fin n,
        ∑ z, ∑ w, Q a x * Q b y * Q c z * Q d w * (u x w * v y z)
          = (∑ w, Q a x * Q d w * u x w) * ∑ z, Q b y * Q c z * v y z := by
      intro y
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [Finset.sum_congr rfl fun y _ => inner y, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x _ => step x, ← Finset.sum_mul]

/-- **THE `(a,c) | (b,d)` PAIRING**, by the re-indexing `AlgebraicCurvature.act_constCurv` uses for
the same purpose. -/
theorem act_factor' (Q u v : Fin n → Fin n → ℝ) (a b c d : Fin n) :
    (∑ p : Fin n × Fin n × Fin n × Fin n,
      Q a p.1 * Q b p.2.1 * Q c p.2.2.1 * Q d p.2.2.2 * (u p.1 p.2.2.1 * v p.2.1 p.2.2.2))
      = act2 Q u a c * act2 Q v b d := by
  rw [Fintype.sum_equiv
    ⟨fun p => (p.1, p.2.1, p.2.2.2, p.2.2.1), fun p => (p.1, p.2.1, p.2.2.2, p.2.2.1),
      fun _ => rfl, fun _ => rfl⟩ _
    (fun p : Fin n × Fin n × Fin n × Fin n =>
      Q a p.1 * Q b p.2.1 * Q d p.2.2.1 * Q c p.2.2.2 * (u p.1 p.2.2.2 * v p.2.1 p.2.2.1))
    fun p => by simp only [Equiv.coe_fn_mk]; ring]
  exact act_factor Q u v a b d c

/-- **THE FRAME CHANGE PASSES THROUGH A KULKARNI–NOMIZU PRODUCT.** No orthogonality: this is
multilinearity of `act` and nothing more. -/
theorem act_kn (Q h k : Fin n → Fin n → ℝ) (a b c d : Fin n) :
    act Q (kn h k) a b c d = kn (act2 Q h) (act2 Q k) a b c d := by
  have split : ∀ p : Fin n × Fin n × Fin n × Fin n,
      Q a p.1 * Q b p.2.1 * Q c p.2.2.1 * Q d p.2.2.2 * kn h k p.1 p.2.1 p.2.2.1 p.2.2.2
        = Q a p.1 * Q b p.2.1 * Q c p.2.2.1 * Q d p.2.2.2 * (h p.1 p.2.2.2 * k p.2.1 p.2.2.1)
          + Q a p.1 * Q b p.2.1 * Q c p.2.2.1 * Q d p.2.2.2 * (k p.1 p.2.2.2 * h p.2.1 p.2.2.1)
          - Q a p.1 * Q b p.2.1 * Q c p.2.2.1 * Q d p.2.2.2 * (h p.1 p.2.2.1 * k p.2.1 p.2.2.2)
          - Q a p.1 * Q b p.2.1 * Q c p.2.2.1 * Q d p.2.2.2
              * (k p.1 p.2.2.1 * h p.2.1 p.2.2.2) := by
    intro p; simp only [kn]; ring
  simp only [act]
  rw [Finset.sum_congr rfl fun p _ => split p, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, act_factor Q h k a b c d, act_factor Q k h a b c d,
    act_factor' Q h k a b c d, act_factor' Q k h a b c d]
  simp only [kn]

/-! ## 2. `act` and `act2` are linear -/

theorem act_smul (Q : Fin n → Fin n → ℝ) (lam : ℝ) (R : Fin n → Fin n → Fin n → Fin n → ℝ)
    (a b c d : Fin n) :
    act Q (fun x y z w => lam * R x y z w) a b c d = lam * act Q R a b c d := by
  simp only [act, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem act_sub (Q : Fin n → Fin n → ℝ) (R S : Fin n → Fin n → Fin n → Fin n → ℝ)
    (a b c d : Fin n) :
    act Q (fun x y z w => R x y z w - S x y z w) a b c d
      = act Q R a b c d - act Q S a b c d := by
  simp only [act, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem act2_smul (Q : Fin n → Fin n → ℝ) (lam : ℝ) (S : Fin n → Fin n → ℝ) (b c : Fin n) :
    act2 Q (fun x y => lam * S x y) b c = lam * act2 Q S b c := by
  simp only [act2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem act2_sub (Q : Fin n → Fin n → ℝ) (S T : Fin n → Fin n → ℝ) (b c : Fin n) :
    act2 Q (fun x y => S x y - T x y) b c = act2 Q S b c - act2 Q T b c := by
  simp only [act2, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-! ## 3. The trace-free Ricci tensor transports

This is where `IsOrth` enters and it enters three times: `ricci_act`, `scal_act`, `act2_delta`.
-/

theorem act2_tracefreeRicci (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ) (b c : Fin n) :
    act2 Q (tracefreeRicci R) b c = tracefreeRicci (act Q R) b c := by
  have key : act2 Q (tracefreeRicci R) b c
      = act2 Q (ricci R) b c - (scal R / (n : ℝ)) * act2 Q delta b c := by
    simp only [act2, tracefreeRicci, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [key, act2_delta hQ, ← ricci_act hQ, tracefreeRicci, scal_act hQ]

/-- The two function-level identities the assembly rewrites with. -/
theorem act2_tracefreeRicci_fun (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    act2 Q (tracefreeRicci R) = tracefreeRicci (act Q R) := by
  funext x y; exact act2_tracefreeRicci hQ R x y

theorem act2_delta_fun (hQ : IsOrth Q) : act2 Q (delta : Fin n → Fin n → ℝ) = delta := by
  funext x y; exact act2_delta hQ x y

/-! ## 4. The three projections commute with the frame change -/

/-- **THE SCALAR PIECE IS EQUIVARIANT.** -/
theorem act_scalPart (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    act Q (scalPart R) a b c d = scalPart (act Q R) a b c d := by
  have key : act Q (scalPart R) a b c d
      = (scal R / ((n : ℝ) * ((n : ℝ) - 1))) * act Q (constCurv n) a b c d := by
    simp only [act, scalPart, knSquare_delta, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [key, act_constCurv hQ, scalPart, knSquare_delta, scal_act hQ]

/-- **THE TRACELESS-RICCI PIECE IS EQUIVARIANT.** -/
theorem act_ricciPart (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    act Q (ricciPart R) a b c d = ricciPart (act Q R) a b c d := by
  have key : act Q (ricciPart R) a b c d
      = (1 / ((n : ℝ) - 2)) * act Q (kn (tracefreeRicci R) delta) a b c d := by
    simp only [act, ricciPart, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [key, act_kn, act2_tracefreeRicci_fun hQ, act2_delta_fun hQ, ricciPart]

/-- **AND THEREFORE SO IS THE WEYL PIECE**, which is the statement that makes the splitting a
splitting of representations rather than of coordinates. -/
theorem act_weylPart (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ) (a b c d : Fin n) :
    act Q (weylPart R) a b c d = weylPart (act Q R) a b c d := by
  have key : act Q (weylPart R) a b c d
      = act Q R a b c d - act Q (ricciPart R) a b c d - act Q (scalPart R) a b c d := by
    simp only [act, weylPart, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [key, act_ricciPart hQ, act_scalPart hQ, weylPart]

end LovelockEquivariance
