import LovelockReduction

/-!
# The three summands are mutually orthogonal

`LovelockProjections` had to disclaim one word of the `UNLOCK_WATCHLIST` item's own prediction:

> LIKELY OUTCOME: **the projections and their orthogonality** …

and that file's header says exactly why it could not honour it — *"that the three summands are
mutually orthogonal for the natural inner product on four-index arrays is **not proved here**, and
this estate has no inner product on that space to state it against."* **This supplies the form and
proves the orthogonality**, which closes the last unmet clause of that prediction.

**A SECOND JUSTIFICATION WAS DRAFTED HERE AND IS FALSE; IT IS KEPT WITH ITS CORRECTION BECAUSE THE
ERROR IS INSTRUCTIVE.** The draft said this supplies the vocabulary the `a₂` coefficient needs,
because `a₂` is a combination of `|Riem|²`, `|Ric|²` and `R²`. **`WALLS` §W5.0 §1 says otherwise,
in the estate's own words:** *"`a₂`, the second heat-kernel coefficient, **whose integrand is a
multiple of the scalar curvature**"*. So `a₂` needs `scal`, which `AlgebraicCurvature` has had all
along, and needs nothing from this file. The quadratic invariants belong to the **next**
coefficient. The claim was asserted from memory of the literature rather than checked against the
wall document that states it, which is exactly what `ERRATUM 159`'s rule is about.

**What is true, and is narrower:** the full contraction of two four-index arrays did not exist in
this estate, so the quadratic curvature invariants could not be *written* — grepped before
claiming, `paper_f` contains no four-fold contraction of two curvature tensors and no norm on them.
That is worth having on its own, and the orthogonality above is what it was built for.

## What is delivered

`ip R S = ∑_{abcd} R_{abcd} S_{abcd}`, with bilinearity and symmetry, and then two contraction
identities that do all the work:

* **`ip_kn_delta`**: `⟨R, h ⊙ δ⟩ = 4 · ∑_{bc} Ric(R)_{bc} · h_{bc}`, for every algebraic curvature
  tensor `R` and **every** `h`;
* **`ip_knSquare_delta`**: `⟨R, δ ⊙ δ⟩ = 2 · scal R`, which falls straight out of the first at
  `h = δ`.

Both constants were computed by exact rational arithmetic on **generic** algebraic curvature
tensors at `n = 3, 4, 5` before being written — the same check `LovelockProjections` used. **It
earned its keep**: working the four terms out by hand produced `2` on the first pass and `4` on the
second, from a sign slip in one of the three contractions, and the numerics decided between them
before either reached a statement.

The two identities say one thing: **contracting a curvature tensor against a Kulkarni–Nomizu
product with the metric sees only its traces.** So a tensor whose Ricci trace vanishes is
orthogonal to both of the other summands, and that is the entire proof:

* `ip_weylPart_ricciPart`, `ip_weylPart_scalPart` — immediate from `ricci_weylPart`;
* `ip_ricciPart_scalPart` — from `scal_kn_delta`: `scal (h ⊙ δ) = (2n − 2)·tr h`, which vanishes
  because the middle summand is built from the **trace-free** part of the Ricci tensor;
* `ip_self_eq` — hence Pythagoras: `⟨R,R⟩` is the sum of the three squared lengths.

## Where the hypotheses sit, audited as in the three previous files

* **`IsAlgCurv R` is load-bearing in the computation here**, for the first time in this group:
  `sum_mid` spends `pair_symm` and `ricci_symm`, `sum_13` and `sum_24` spend `antisymm_right`.
  In `LovelockProjections` the same hypothesis turned out to be decorative on every trace identity;
  here it is not, and the difference is that these statements are about a *contraction of two*
  tensors rather than a trace of one.
* **Neither contraction identity needs `n ≥ 3`, and neither needs `h` symmetric.** A textbook
  statement of the Kulkarni–Nomizu product carries symmetry of both arguments. **Unlike the three
  previous cases in this group, that hypothesis was never written down here in the first place** —
  `LovelockProjections` had already found the same one decorative in `ricci_kn_delta`, so this file
  was drafted without it. Recorded as a habit that transferred rather than as a fourth removal,
  because it is not a removal.
* **The three orthogonality statements do need `n ≥ 3`** — but only because `ricci_weylPart` and
  `trace_tracefreeRicci` do. `ip_eq_zero_of_ricci_eq_zero` is the dimension-free form and is the
  theorem actually doing the work.

## What this is NOT

**It is not progress on Lovelock.** Orthogonality is a property of three particular summands; the
classification is an exhaustion statement about *all* equivariant maps, and `LovelockReduction`
names the two `Prop`s that remain. Nothing here bears on either. The watchlist item stays open on
its recorded blocker.

**It is not `a₂`.** What exists now is the form that `|Riem|²`, `|Ric|²` and `R²` are written with.
`a₂` is a specific combination of them with specific coefficients coming out of a heat-kernel
expansion this estate does not have — `WALLS` W5 fails at the differential geometry, `HeatKernel`
is zero files, and nothing here changes that. **No theorem in this file should be recorded as an
`a₂` computation.**

**And `ip` is not proved to be an inner product in Mathlib's sense**: no `InnerProductSpace`
instance, no positive-definiteness, no completeness. It is a symmetric bilinear form, and
positivity is not proved because nothing below needs it. Said so that "orthogonality" is read as
*"this bilinear form vanishes on these pairs"* and not as more.

**SUPERSEDED IN PART — `LovelockInnerPositive` PROVES THE POSITIVITY.** `ip_self_nonneg`,
`ip_self_pos` and `eq_zero_of_ip_self_eq_zero` are there, and that file's §2 is titled *"The
consumer that made it worth proving"* — so *"nothing below needs it"* was true of this file and
stopped being true of the estate. The paragraph is kept per `ERRATUM 94`; **what still stands is
the rest of it**, and it is the part that matters: there is still no `InnerProductSpace` instance
and no completeness, so "orthogonality" should still be read as *"this bilinear form vanishes on
these pairs"*. Found by `--gapmarks`, `ERRATUM 226`.

**AND NOW THAT LAST CLAUSE HAS GONE THE SAME WAY, WHICH IS WHY IT IS BEING CORRECTED THE SAME
DAY.** `LovelockInnerSpace.arrEquiv` is an explicit linear equivalence onto
`EuclideanSpace ℝ (Fin n × Fin n × Fin n × Fin n)` and `inner_arrEquiv` proves it carries `ip` to
that space's inner product, so **"orthogonality" in this file now means orthogonality in a
genuine inner-product space** — `inner_weylPart_ricciPart` and its two companions restate §6's
theorems there, and `norm_sq_eq` is §6's Pythagoras on norms. What is *still* true of the sentence
above: **no instance is placed on `Fin n → Fin n → Fin n → Fin n → ℝ`**, so every statement in
this file remains one about the bare form, and completeness is neither claimed nor used.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockOrthogonality

open AlgebraicCurvature LovelockProjections Finset

variable {n : ℕ} {R : Fin n → Fin n → Fin n → Fin n → ℝ}

/-! ## 1. The full contraction, and its bilinearity -/

/-- **THE FULL CONTRACTION OF TWO FOUR-INDEX ARRAYS.** -/
def ip (R S : Fin n → Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * S a b c d

theorem ip_comm (R S : Fin n → Fin n → Fin n → Fin n → ℝ) : ip R S = ip S R := by
  simp only [ip]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => mul_comm _ _

theorem ip_smul_right (lam : ℝ) (R S : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip R (fun a b c d => lam * S a b c d) = lam * ip R S := by
  simp only [ip, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

theorem ip_smul_left (lam : ℝ) (R S : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip (fun a b c d => lam * R a b c d) S = lam * ip R S := by
  rw [ip_comm, ip_smul_right, ip_comm S R]

/-- Splitting the **second** argument along the decomposition, which is the only shape the
Pythagoras assembly needs. Stated directly rather than via a general `ip_add_right`, because a
rewrite keyed on a lambda does not fire against `ip X R` with `R` a bare variable. -/
theorem ip_decomp_right (X R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip X R = ip X (weylPart R) + ip X (ricciPart R) + ip X (scalPart R) := by
  simp only [ip, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by
      rw [decomposition R a b c d]; ring

theorem ip_decomp_left (R X : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ip R X = ip (weylPart R) X + ip (ricciPart R) X + ip (scalPart R) X := by
  rw [ip_comm, ip_decomp_right X R, ip_comm X (weylPart R), ip_comm X (ricciPart R),
    ip_comm X (scalPart R)]

/-! ## 2. The three ways a repeated index contracts

Each is one structure field, and together they are why all four terms of a Kulkarni–Nomizu product
with `δ` contribute the same thing rather than cancelling in pairs.
-/

/-- Contracting slots 2 and 3 gives the Ricci trace: `pair_symm` renames the sum into the
definition of `ricci`, and `ricci_symm` puts the arguments in the caller's order. -/
theorem sum_mid (hR : IsAlgCurv R) (a c : Fin n) : ∑ b, R a b b c = ricci R a c := by
  have hstep : ∀ b : Fin n, R a b b c = R b c a b := fun b => hR.pair_symm a b b c
  simp only [hstep]
  exact ricci_symm hR c a

/-- Contracting slots 1 and 3 gives **minus** the Ricci trace. -/
theorem sum_13 (hR : IsAlgCurv R) (b d : Fin n) : ∑ a, R a b a d = -ricci R b d := by
  have hstep : ∀ a : Fin n, R a b a d = -R a b d a := fun a => hR.antisymm_right a b a d
  simp only [hstep, Finset.sum_neg_distrib]
  rfl

/-- Contracting slots 2 and 4 gives minus the Ricci trace as well. -/
theorem sum_24 (hR : IsAlgCurv R) (a c : Fin n) : ∑ b, R a b c b = -ricci R a c := by
  have hstep : ∀ b : Fin n, R a b c b = -R a b b c := fun b => by
    rw [hR.antisymm_right a b b c]; ring
  simp only [hstep, Finset.sum_neg_distrib, sum_mid hR]

/-- A `δ` inside a sum collapses it, in the argument order the four terms produce. -/
theorem sum_delta_swap (b : Fin n) (g : Fin n → ℝ) : ∑ c, delta b c * g c = g b := by
  have hstep : ∀ c : Fin n, delta b c * g c = delta c b * g c := fun c => by rw [delta_symm b c]
  simp only [hstep]
  exact sum_delta_left b g

/-! ## 3. The two contraction identities -/

/-- **CONTRACTING AGAINST A KULKARNI–NOMIZU PRODUCT WITH THE METRIC SEES ONLY THE RICCI TRACE.**
The constant is `4` — one from each term of the product, all four agreeing after the three
contraction lemmas above. **No symmetry of `h`, and no `n ≥ 3`.** -/
theorem ip_kn_delta (hR : IsAlgCurv R) (h : Fin n → Fin n → ℝ) :
    ip R (kn h delta) = 4 * ∑ b, ∑ c, ricci R b c * h b c := by
  have hA1 : ip R (fun a b c d => h a d * delta b c) = ∑ b, ∑ c, ricci R b c * h b c := by
    simp only [ip]
    have outer : ∀ a : Fin n, ∑ b, ∑ c, ∑ d, R a b c d * (h a d * delta b c)
        = ∑ b, ∑ d, R a b b d * h a d := by
      intro a
      refine Finset.sum_congr rfl fun b _ => ?_
      have step : ∀ c : Fin n, ∑ d, R a b c d * (h a d * delta b c)
          = delta b c * ∑ d, R a b c d * h a d := by
        intro c
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => by ring
      rw [Finset.sum_congr rfl fun c _ => step c,
        sum_delta_swap b fun c => ∑ d, R a b c d * h a d]
    rw [Finset.sum_congr rfl fun a _ => outer a]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => by rw [← Finset.sum_mul, sum_mid hR]
  have hA2 : ip R (fun a b c d => delta a d * h b c) = ∑ b, ∑ c, ricci R b c * h b c := by
    simp only [ip]
    have outer : ∀ a : Fin n, ∑ b, ∑ c, ∑ d, R a b c d * (delta a d * h b c)
        = ∑ b, ∑ c, R a b c a * h b c := by
      intro a
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
      have step : ∀ d : Fin n, R a b c d * (delta a d * h b c)
          = delta a d * (R a b c d * h b c) := fun d => by ring
      rw [Finset.sum_congr rfl fun d _ => step d,
        sum_delta_swap a fun d => R a b c d * h b c]
    rw [Finset.sum_congr rfl fun a _ => outer a, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => by rw [← Finset.sum_mul]; rfl
  have hA3 : ip R (fun a b c d => h a c * delta b d) = -∑ b, ∑ c, ricci R b c * h b c := by
    simp only [ip]
    have outer : ∀ a : Fin n, ∑ b, ∑ c, ∑ d, R a b c d * (h a c * delta b d)
        = ∑ b, ∑ c, R a b c b * h a c := by
      intro a
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
      have step : ∀ d : Fin n, R a b c d * (h a c * delta b d)
          = delta b d * (R a b c d * h a c) := fun d => by ring
      rw [Finset.sum_congr rfl fun d _ => step d,
        sum_delta_swap b fun d => R a b c d * h a c]
    rw [Finset.sum_congr rfl fun a _ => outer a]
    have inner : ∀ a : Fin n, ∑ b, ∑ c, R a b c b * h a c
        = ∑ c, -(ricci R a c * h a c) := by
      intro a
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c _ => by rw [← Finset.sum_mul, sum_24 hR]; ring
    rw [Finset.sum_congr rfl fun a _ => inner a]
    simp only [Finset.sum_neg_distrib]
  have hA4 : ip R (fun a b c d => delta a c * h b d) = -∑ b, ∑ c, ricci R b c * h b c := by
    simp only [ip]
    have outer : ∀ a : Fin n, ∀ b : Fin n, ∑ c, ∑ d, R a b c d * (delta a c * h b d)
        = ∑ d, R a b a d * h b d := by
      intro a b
      have step : ∀ c : Fin n, ∑ d, R a b c d * (delta a c * h b d)
          = delta a c * ∑ d, R a b c d * h b d := by
        intro c
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => by ring
      rw [Finset.sum_congr rfl fun c _ => step c,
        sum_delta_swap a fun c => ∑ d, R a b c d * h b d]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => outer a b,
      Finset.sum_comm]
    have inner : ∀ b : Fin n, ∑ a, ∑ d, R a b a d * h b d
        = ∑ d, -(ricci R b d * h b d) := by
      intro b
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun d _ => by rw [← Finset.sum_mul, sum_13 hR]; ring
    rw [Finset.sum_congr rfl fun b _ => inner b]
    simp only [Finset.sum_neg_distrib]
  have hsplit : ip R (kn h delta)
      = ip R (fun a b c d => h a d * delta b c) + ip R (fun a b c d => delta a d * h b c)
        - ip R (fun a b c d => h a c * delta b d) - ip R (fun a b c d => delta a c * h b d) := by
    simp only [ip, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by
        simp only [kn]; ring
  rw [hsplit, hA1, hA2, hA3, hA4]
  ring

/-- **AND AT `h = δ` IT IS TWICE THE SCALAR CURVATURE.** -/
theorem ip_knSquare_delta (hR : IsAlgCurv R) :
    ip R (knSquare (delta : Fin n → Fin n → ℝ)) = 2 * scal R := by
  have hself : ip R (kn (delta : Fin n → Fin n → ℝ) delta)
      = 2 * ip R (knSquare (delta : Fin n → Fin n → ℝ)) := by
    have hfun : kn (delta : Fin n → Fin n → ℝ) delta
        = fun a b c d => 2 * knSquare (delta : Fin n → Fin n → ℝ) a b c d := by
      funext a b c d; exact kn_self delta a b c d
    rw [hfun, ip_smul_right]
  have hcollapse : ∀ b : Fin n, ∑ c, ricci R b c * delta b c = ricci R b b := by
    intro b
    have hstep : ∀ c : Fin n, ricci R b c * delta b c = delta b c * ricci R b c :=
      fun c => mul_comm _ _
    rw [Finset.sum_congr rfl fun c _ => hstep c, sum_delta_swap b fun c => ricci R b c]
  have h4 := ip_kn_delta hR (delta : Fin n → Fin n → ℝ)
  rw [hself, Finset.sum_congr rfl fun b _ => hcollapse b] at h4
  have hscal : ∑ b, ricci R b b = scal R := rfl
  rw [hscal] at h4
  linarith

/-- **THE SCALAR CURVATURE OF A KULKARNI–NOMIZU PRODUCT WITH THE METRIC**, from
`ricci_kn_delta`. This is where the middle summand's orthogonality to the scalar one comes from. -/
theorem scal_kn_delta (h : Fin n → Fin n → ℝ) :
    scal (kn h delta) = (2 * (n : ℝ) - 2) * ∑ a, h a a := by
  have e1 : ∑ b : Fin n, (delta b b : ℝ) = (n : ℝ) := by simp [delta]
  simp only [scal, ricci_kn_delta, Finset.sum_add_distrib, ← Finset.mul_sum, e1]
  ring

/-! ## 4. Orthogonality -/

/-- **THE DIMENSION-FREE STATEMENT, WHICH IS THE ONE DOING THE WORK.** A curvature tensor with
vanishing Ricci trace is orthogonal to every Kulkarni–Nomizu product with the metric. -/
theorem ip_eq_zero_of_ricci_eq_zero (hR : IsAlgCurv R) (h0 : ∀ b c, ricci R b c = 0)
    (h : Fin n → Fin n → ℝ) : ip R (kn h delta) = 0 := by
  rw [ip_kn_delta hR h]
  have : ∀ b : Fin n, ∑ c, ricci R b c * h b c = 0 := by
    intro b
    rw [Finset.sum_congr rfl fun c _ => by rw [h0 b c, zero_mul]]
    simp
  rw [Finset.sum_congr rfl fun b _ => this b]
  simp

/-- **THE WEYL PIECE IS ORTHOGONAL TO THE TRACELESS-RICCI PIECE.** -/
theorem ip_weylPart_ricciPart (hn1 : (n : ℝ) - 1 ≠ 0) (hn2 : (n : ℝ) - 2 ≠ 0)
    (hR : IsAlgCurv R) : ip (weylPart R) (ricciPart R) = 0 := by
  have hfun : ricciPart R
      = fun a b c d => (1 / ((n : ℝ) - 2)) * kn (tracefreeRicci R) delta a b c d := by
    funext a b c d; rfl
  rw [hfun, ip_smul_right,
    ip_eq_zero_of_ricci_eq_zero (isAlgCurv_weylPart hR)
      (fun b c => ricci_weylPart hn1 hn2 R b c) (tracefreeRicci R), mul_zero]

/-- **AND TO THE SCALAR PIECE.** -/
theorem ip_weylPart_scalPart (hn1 : (n : ℝ) - 1 ≠ 0) (hn2 : (n : ℝ) - 2 ≠ 0)
    (hR : IsAlgCurv R) : ip (weylPart R) (scalPart R) = 0 := by
  have hfun : scalPart R
      = fun a b c d => (scal R / ((n : ℝ) * ((n : ℝ) - 1)))
          * knSquare (delta : Fin n → Fin n → ℝ) a b c d := by
    funext a b c d; rfl
  rw [hfun, ip_smul_right, ip_knSquare_delta (isAlgCurv_weylPart hR),
    scal_weylPart hn1 hn2 R]
  ring

/-- **AND THE OTHER TWO ARE ORTHOGONAL TO EACH OTHER**, because the middle summand is built from
the **trace-free** part of the Ricci tensor and `scal_kn_delta` sees only the trace. -/
theorem ip_ricciPart_scalPart (hn0 : (n : ℝ) ≠ 0) (hR : IsAlgCurv R) :
    ip (ricciPart R) (scalPart R) = 0 := by
  have hfunR : ricciPart R
      = fun a b c d => (1 / ((n : ℝ) - 2)) * kn (tracefreeRicci R) delta a b c d := by
    funext a b c d; rfl
  have hfunS : scalPart R
      = fun a b c d => (scal R / ((n : ℝ) * ((n : ℝ) - 1)))
          * knSquare (delta : Fin n → Fin n → ℝ) a b c d := by
    funext a b c d; rfl
  rw [hfunR, hfunS, ip_smul_left, ip_smul_right,
    ip_knSquare_delta (isAlgCurv_kn (tracefreeRicci_symm hR) delta_symm),
    scal_kn_delta (tracefreeRicci R), trace_tracefreeRicci hn0 R]
  ring

/-- **PYTHAGORAS.** `⟨R,R⟩` is the sum of the three squared lengths, so the decomposition is
orthogonal in the strongest sense the estate can state. -/
theorem ip_self_eq (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0) (hn2 : (n : ℝ) - 2 ≠ 0)
    (hR : IsAlgCurv R) :
    ip R R = ip (weylPart R) (weylPart R) + ip (ricciPart R) (ricciPart R)
      + ip (scalPart R) (scalPart R) := by
  have hWR := ip_weylPart_ricciPart hn1 hn2 hR
  have hWS := ip_weylPart_scalPart hn1 hn2 hR
  have hRS := ip_ricciPart_scalPart hn0 hR
  have eW : ip (weylPart R) R = ip (weylPart R) (weylPart R) := by
    rw [ip_decomp_right (weylPart R) R, hWR, hWS]; ring
  have eR : ip (ricciPart R) R = ip (ricciPart R) (ricciPart R) := by
    rw [ip_decomp_right (ricciPart R) R, ip_comm (ricciPart R) (weylPart R), hWR, hRS]; ring
  have eS : ip (scalPart R) R = ip (scalPart R) (scalPart R) := by
    rw [ip_decomp_right (scalPart R) R, ip_comm (scalPart R) (weylPart R),
      ip_comm (scalPart R) (ricciPart R), hWS, hRS]; ring
  rw [ip_decomp_left R R, eW, eR, eS]

end LovelockOrthogonality
