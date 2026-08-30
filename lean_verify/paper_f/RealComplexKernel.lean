import TorusTopSimple

/-!
# The transfer the spectrum chain never made: a real kernel and its complexification have the
same dimension

`TorusTopSimple` ended with a coincidence it refused to dress as a theorem. Two files compute the
dimension of `Q = D + A`'s kernel on the even periodic lattice, by wholly different routes, and get
`1` both times — `LaplacianSignlessKernel.card_bipartiteComponent_eq_finrank_ker` by counting
two-colourable components, and `TorusTopSimple.signless_zero_simple` by counting frequencies. **They
could not be compared**: the first is `finrank ℝ` of the real matrix's kernel and the second is
`finrank ℂ` of its complexification's, and this estate had no bridge between the two. Its only
real/complex bridge, `SignlessTorusReal.real_eigenvalue_iff_cx`, transfers **membership** in the
spectrum and says nothing about dimension.

**THE BRIDGE IS BUILT HERE, AND THE ROUTE IS NOT THE ONE THE ITEM SKETCHED.** That block guessed at
base-change invariance of `Matrix.rank`. **The search it declined to do was done, and it is reported
as a search and not as an absence** — refuting an absence claim is cheap and confirming one is not
(`PROGRESS_LOG` entry 42). What the search found, exactly: `Mathlib/LinearAlgebra/Matrix/Rank.lean`
contains **no** occurrence of `RingHom` or `algebraMap` and **one** of `Submodule.map`, inside
another proof; there is no `Matrix.rank` statement under `Matrix.map` and no minor-determinant
characterisation to run the usual argument through. `Module.finrank_baseChange` **does** exist —
`finrank R (R ⊗[S] M') = finrank S M'` — but it is about a tensor product, and identifying
`ker (cx A)` with `ℂ ⊗[ℝ] ker A` is the same work as the equivalence below, done less directly.

What works instead needs no rank and no tensor product: **count real dimensions on both sides.**

> **`mem_ker_cx_iff`** — `z` is in the complexified kernel **iff** its real and imaginary parts are
> both in the real one. This is `cx_mulVec_re` and `cx_mulVec_im` read at eigenvalue zero, and they
> were proved for the membership transfer three units ago.
>
> **`kerEquivProd`** — hence `z ↦ (re z, im z)` is an **`ℝ`-linear equivalence** from the
> complexified kernel to two copies of the real one.
>
> **`finrank_ker_cx`** — so `2·finrank ℂ (ker (cx A)) = finrank ℝ (ker (cx A)) = 2·finrank ℝ (ker
> A)`, the first step being the tower law with `finrank ℝ ℂ = 2` and the second the equivalence.
> **For an arbitrary real square matrix**, nothing about graphs in it.
>
> **`card_bipComp_eq_finrank_ker_cx`** — the component count, now on the complex side, for **every
> finite graph**.

## The coincidence is now a derivation, and what that is worth is stated exactly

`torus_card_bipComp_eq_one` reads off that the even periodic lattice has exactly one two-colourable
component. **THAT FACT IS NOT NEW AND IS NOT INTERESTING**: the graph is connected
(`TorusDecay.torusGraph_connected`) and two-colourable (`TorusBipartite.torusGraph_colorable_two`),
so it has one component and that component is two-colourable, in two lines and with no spectrum
anywhere. **The point is the direction of the arrow.** Before this file the two computations agreed
and could not be compared; now the comparison is a theorem, and had they *disagreed* the
disagreement would have been visible. A consistency check that cannot fail is not a check, and
until today this one could not fail because it could not be run.

## What is NOT here

**No statement about `Matrix.rank` under base change.** `finrank_ker_cx` is about kernels. The rank
statement follows from it and `LaplacianRank.rank_add_finrank_ker` **only after that lemma is
generalised from `ℝ` to an arbitrary field**, which it is not, and **that generalisation is not
done here**.

**No eigenspace version.** `finrank_ker_cx` is stated at eigenvalue zero. For a real `μ` the same
argument applies to `A − μ`, and **the general statement is not made below** — it needs the
subtraction pushed through `cx`, which is true and unproved here.

**Nothing about complex eigenvalues.** A real matrix can have non-real eigenvalues whose eigenspaces
have no real counterpart at all; this file says nothing about them and its statement does not
mention them.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RealComplexKernel

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection LaplacianSignless
open SignlessTorusReal TorusTopSimple

/-! ## 1. Membership: real and imaginary parts, separately -/

/-- Building a complex vector from two real ones recovers the first as its real part. -/
theorem re_add_mul_I {V : Type*} (x y : V → ℝ) :
    (fun v => (((x v : ℂ) + (y v : ℂ) * Complex.I)).re) = x := by
  funext v; simp

/-- And the second as its imaginary part. -/
theorem im_add_mul_I {V : Type*} (x y : V → ℝ) :
    (fun v => (((x v : ℂ) + (y v : ℂ) * Complex.I)).im) = y := by
  funext v; simp

section Transfer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **A VECTOR IS IN THE COMPLEXIFIED KERNEL IFF BOTH ITS PARTS ARE IN THE REAL ONE.**
`cx_mulVec_re` and `cx_mulVec_im` at eigenvalue zero. -/
theorem mem_ker_cx_iff (A : Matrix V V ℝ) (z : V → ℂ) :
    z ∈ LinearMap.ker (Matrix.toLin' (MatrixLoewner.cx A))
      ↔ (fun v => (z v).re) ∈ LinearMap.ker (Matrix.toLin' A) ∧
        (fun v => (z v).im) ∈ LinearMap.ker (Matrix.toLin' A) := by
  simp only [LinearMap.mem_ker, Matrix.toLin'_apply]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · funext v
      rw [← cx_mulVec_re A z v, h]
      simp
    · funext v
      rw [← cx_mulVec_im A z v, h]
      simp
  · rintro ⟨hr, hi⟩
    have hr' := congrFun hr
    have hi' := congrFun hi
    simp only [Pi.zero_apply] at hr' hi'
    funext v
    apply Complex.ext
    · rw [cx_mulVec_re A z v, hr' v]
      simp
    · rw [cx_mulVec_im A z v, hi' v]
      simp

/-- **THE COMPLEXIFIED KERNEL IS TWO COPIES OF THE REAL ONE, `ℝ`-LINEARLY.** Real and imaginary
parts one way, `x + iy` the other. -/
noncomputable def kerEquivProd (A : Matrix V V ℝ) :
    LinearMap.ker (Matrix.toLin' (MatrixLoewner.cx A)) ≃ₗ[ℝ]
      (LinearMap.ker (Matrix.toLin' A) × LinearMap.ker (Matrix.toLin' A)) where
  toFun z := (⟨fun v => ((z : V → ℂ) v).re, ((mem_ker_cx_iff A _).1 z.2).1⟩,
              ⟨fun v => ((z : V → ℂ) v).im, ((mem_ker_cx_iff A _).1 z.2).2⟩)
  map_add' z w := by
    refine Prod.ext ?_ ?_ <;> · apply Subtype.ext; funext v; simp
  map_smul' r z := by
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      funext v
      change ((r • (z : V → ℂ)) v).re = r * ((z : V → ℂ) v).re
      simp
    · apply Subtype.ext
      funext v
      change ((r • (z : V → ℂ)) v).im = r * ((z : V → ℂ) v).im
      simp
  invFun p := ⟨fun v => (((p.1 : V → ℝ) v : ℂ) + (((p.2 : V → ℝ) v : ℂ) * Complex.I)),
    (mem_ker_cx_iff A _).2
      ⟨by rw [re_add_mul_I]; exact p.1.2, by rw [im_add_mul_I]; exact p.2.2⟩⟩
  left_inv z := by
    apply Subtype.ext
    funext v
    simp
  right_inv p := by
    refine Prod.ext ?_ ?_ <;> · apply Subtype.ext; funext v; simp

/-- **THE TRANSFER.** A real square matrix's kernel has the same dimension over `ℝ` as its
complexification's kernel has over `ℂ`. Both sides are counted in **real** dimensions and compared:
the tower law gives `finrank ℝ = 2 · finrank ℂ` on the left, and `kerEquivProd` gives
`finrank ℝ = 2 · finrank ℝ (ker A)` on the right. **No rank, and no base-change lemma** — the
pinned Mathlib has none for `Matrix.rank`. -/
theorem finrank_ker_cx (A : Matrix V V ℝ) :
    Module.finrank ℂ (LinearMap.ker (Matrix.toLin' (MatrixLoewner.cx A)))
      = Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A)) := by
  have htower : Module.finrank ℝ ℂ *
      Module.finrank ℂ (LinearMap.ker (Matrix.toLin' (MatrixLoewner.cx A)))
      = Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (MatrixLoewner.cx A))) :=
    Module.finrank_mul_finrank ℝ ℂ _
  rw [Complex.finrank_real_complex] at htower
  have hprod : Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (MatrixLoewner.cx A)))
      = 2 * Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A)) := by
    rw [(kerEquivProd A).finrank_eq, Module.finrank_prod]
    ring
  omega

end Transfer

/-! ## 2. The component count, on the complex side -/

/-- **THE NUMBER OF TWO-COLOURABLE COMPONENTS IS THE COMPLEXIFIED KERNEL'S DIMENSION**, for every
finite graph. `LaplacianSignlessKernel.card_bipartiteComponent_eq_finrank_ker` carried it over `ℝ`;
the transfer moves it. -/
theorem card_bipComp_eq_finrank_ker_cx {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card (LaplacianSignlessKernel.BipComp G)
      = Module.finrank ℂ (LinearMap.ker
          (Matrix.toLin' (MatrixLoewner.cx (signlessLap G)))) := by
  rw [finrank_ker_cx]
  exact LaplacianSignlessKernel.card_bipartiteComponent_eq_finrank_ker G

/-- **THE CONSISTENCY CHECK, NOW RUNNABLE.** On the even periodic lattice the two-colourable
component count is `1`. **The fact is not new** — the graph is connected and two-colourable, which
gives it in two lines with no spectrum — but until the transfer above existed the two computations
of that number could not be compared, and a check that cannot fail is not a check. -/
theorem torus_card_bipComp_eq_one {d M N : ℕ} (hN : N + 3 = 2 * M) :
    Fintype.card (LaplacianSignlessKernel.BipComp (torusGraph d (N + 3))) = 1 := by
  rw [card_bipComp_eq_finrank_ker_cx]
  have h := signless_zero_simple (d := d) hN
  rw [zero_smul, sub_zero] at h
  exact h

end RealComplexKernel
