# WALLS — where the formalisation stops, and exactly why

**A stop-point deliverable, written 26 September 2026 on the author's stand-down order, after
hardening unit 243.** It summarises `codex-internal/formalisation/WALLS.md`, which holds each wall's
full staircase, every dated amendment and the probes behind each claim. Where this file and that one
ever differ, that one is right.

## The nine walls at a glance

| Wall | What it is | State | Exact failing step, today |
|---|---|---|---|
| **W1** | Reflection positivity and the OS axioms for the massive lattice field | **Open in its OS0/OS1/OS4 part**; the step it was named for is proved | The infinite-volume limit |
| **W2** | The continuum field and Osterwalder–Schrader reconstruction | **OPEN** | Step 2b: a self-adjoint, unbounded Hamiltonian generating the evolution |
| **W3** | Symmetry breaking for a given model (the Peierls argument) | **OPEN** | The comparison that bounds the magnetisation; the estate's own route is proved insufficient |
| **W4** | The mass gap | **OPEN** | A uniform bound on the transfer operator's sub-top eigenvalue ratio as the cross-section grows |
| **W5** | The Einstein equations from the spectral action (`a₂`) | **OPEN** | Rung 4: the heat-kernel expansion of the spectral action |
| **W6** | The Stein class against the `Cc^∞`-defined Sobolev space `W^{1,2}(γ)` | **CLOSED** 9 August, every dimension | — |
| **W7** | Real Clifford classification and the spin identification | **CLOSED** 8 August; the mod-8 table proved 18 August | No mathematics: a presentation decision, and one narrow separation |
| **W8** | The non-trivial reflexive domain `D∞` | **CLOSED** 12 August | — |
| **W9** | The Chamseddine–Connes–Marcolli classification: from the spectral-triple axioms to the finite algebra | **OPEN**; rung 1 climbed, rung 2 half climbed | Rung 2's second half: what the order-one condition forces across the isotypic pieces of CCM's `H_F` |

Six walls are open and three are closed (W6, W7, W8). Of the six, W1 is open with the step it was
named for proved, and W9 has one of its five rungs climbed and half of the second; W2, W3, W4 and W5
are open at the steps named below. **W4 and W5 are the spine's two OPEN links** — L23 (the mass
gap, behind W1–W4) and L22 (the Einstein equations, W5) — and W9 is what keeps L6 PARTIAL.

**One missing subject stands behind two walls.** W2's step 2b and W5's rung 4 both need unbounded
self-adjoint operators — densely defined operators, their adjoints and closures, discrete spectrum,
heat semigroups. Neither this estate nor the pinned Mathlib has any unbounded operator theory. Every
generator the estate handles is bounded (`ASSUMPTIONS_LEDGER` 32).

---

## W1 — reflection positivity and the OS axioms for the massive lattice field

**What it is.** The Osterwalder–Schrader axioms for the lattice field whose covariance is the massive
lattice Green function `(−Δ + m²)⁻¹`, the field the physics wants.

**Staircase climbed.**
* The complete finite-site OS2 programme for the Ornstein–Uhlenbeck-product covariance, in every
  dimension including 4, at the measure level.
* **The step this wall was named for is proved** (9 August):
  `LatticeReflectionPositive.reflectionPositive_lattice` for the estate's own definition,
  `GraphReflectionPositive.reflectionPositive_box` in general, on either side of the first-coordinate
  cut. It came by a route neither named in advance: a symmetric/antisymmetric split and the
  antitonicity of matrix inversion.
* Lifted to the measure (`GraphOS2.os2_lattice`) and to the exponential algebra
  (`GraphOS2Exponential.os2_exponential_lattice`). Sharpness is settled by a biconditional
  (`StrictBiconditional.strict_iff_not_supportedIsotropic`).
* OS1 stated and proved in finite volume (`LatticeOS1.gaussianField_euclideanCovariantFinVol`, 28
  August). OS0 and OS4 have finite-volume content, which is not the axioms
  (`LatticeGeneratingFunctional`; `LatticeFieldFactorises.generatingFunctional_add_of_separated`).

**Exact failing step: the infinite-volume limit.** It is not a missing estimate: there is no
projective system to take a limit along. The finite-volume measures live on a different space for
each box, and they are not consistent: restricting a box's Gaussian to a smaller box gives the
submatrix of the Green function, which is not the smaller box's Green function. So no
Kolmogorov-style construction applies.

**What would have to exist.** Either uniform-in-volume correlation bounds with a tightness argument,
or an independent construction of the infinite-volume Gaussian and a proof that the finite-volume
ones converge to it. Neither is in Mathlib, and neither is packaging. **Kind (c): research.** The
continuum axioms are W2.

## W2 — the continuum field and OS reconstruction

**What it is.** A measure for the continuum field, and from its reflection-positive pairing a
Hilbert space, a vacuum and a Hamiltonian (Osterwalder–Schrader reconstruction).

**Staircase: four steps, two of them hard.**

| step | what it is | where it stops |
|---|---|---|
| 1a | a measure on an infinite-dimensional carrier | **an author's decision** (`ASSUMPTIONS_LEDGER` 47, which carrier), then arithmetic |
| 1b | that measure is the `ℤ^d` free field | **a convergence theorem** — a real unit of analysis |
| 2a | the reflection-positive pairing → a Hilbert space and a vacuum | **done** — Mathlib's GNS construction, consumed by `CascadeGNS` |
| 2b | → a self-adjoint Hamiltonian generating the evolution | **the wall** |

The bounded prototype of leg 2 is large: `FiniteStone`, and Stone's converse for norm-continuous
one-parameter unitary groups in any C⋆-algebra (`StoneConverseLocal.exists_unique_global_generator`),
at five named carriers, under strong, weak and expectation-value continuity (15–16 September).

**Exact failing step: 2b.** The reconstruction's Hamiltonian is unbounded and self-adjoint, on an
infinite-dimensional Hilbert space. Mathlib has no unbounded operators at all (re-probed: no
unbounded-operator constant, no spectral measure, no Borel functional calculus), and every file of
the prototype is bounded by construction. **So 2b is not blocked on a theorem; the objects the
theorem is about do not exist.**

**What would have to exist.** Densely defined unbounded operators, adjoints, closures and essential
self-adjointness, then the semigroup-to-generator step — a Mathlib-scale project. Step 1a waits on the
author; 1b is analysis.

## W3 — symmetry breaking for a given model (the Peierls argument)

**What it is.** A proof that a specific lattice model breaks its symmetry at low temperature — the
magnetisation stays bounded away from zero as the volume grows.

**Staircase climbed.**
* The formulation is well-posed (9 August): ten contour files.
* The gate to the circuit half: a finite graph with all degrees even and an edge contains a cycle
  (`SimpleGraph.exists_isCycle_of_forall_even_degree`), and all degrees are even exactly when the
  edges are an edge-disjoint union of cycles (`SimpleGraph.evenDegrees_iff_exists_cycle_decomposition`).
* **The Peierls step itself**, on the dual lattice: under `+` boundary conditions the contour is an
  edge-disjoint union of circuits (`DualGraph.exists_dual_cycle_decomposition`). The `+` condition is
  a hypothesis on the configuration (`ASSUMPTIONS_LEDGER` 46).
* The enclosure step: *surrounds*, defined by crossing parity; the number of circuits surrounding a
  site is odd exactly when the site is down (`DualUnique.odd_count_circuits_iff_down`).

**Exact failing step — on this arm, a proof of impossibility rather than a missing estimate.** The
comparison the estate built delivers `O(n)` against a target of `O(n²)`
(`IsingBoundaryRouteCeiling.route_insufficient`). Its output is computed exactly, not just bounded
(`IsingSiteFieldBound.sum_tanh_of_indicator`), so the route succeeds exactly when the field's support
is a positive fraction of the box, and a boundary is not. Chain refinements fail the same way
(`IsingChainRouteCeiling.chain_route_insufficient`). **The gap is a theorem that this method cannot
close it.**

**What would have to exist.** First, two author's decisions: the early-August DECISIONS 1–2, now
DECISIONS NEEDED items 16–17 (the logos statement and its `GibbsMeasure` axiom). Then the S3b repair,
which needs a configuration hypothesis with a positive radius (`S3bLocalObstruction`). Then a
comparison model of a genuinely different shape, whose magnetisation the estate can compute and whose
output is not sublinear. None is recorded. **Not claimed:** whether the magnetisation bound is
*true*; every result above is about a method.

## W4 — the mass gap

**What it is.** A gap above the ground state that stays open as the system grows — here, for
transfer operators of lattice models; the Yang–Mills mass gap is behind it (spine L23).

**Staircase climbed.** §6's three items: **1 done** (`IsingTransfer2D`); **2 open**; **3 discharged
for the chain**, and untouched in dimension ≥ 2. Separately, the one-dimensional Ising chain's whole
spectrum and its gap `2e^{−|β|}` are derived from the transfer matrix itself (`IsingTransferMatrix`).
The second route to item 2 has its first rung: any real eigenvalue of a nonnegative matrix is bounded
by any uniform row-sum bound (`PerronBound`).

**Exact failing step.** §6 item 3: that the sub-top eigenvalue ratio stays below one **uniformly** as
the cross-section grows (`IsingTopRatio.UniformSubTopRatio β`, and its three-dimensional and
anisotropic siblings). They are proved at `β = 0` and nowhere else. **And the target is false as stated
above the critical point — measured, not proved** (`ERRATUM 395`). Diagonalising the estate's own
transfer matrices, the ratio climbs towards 1 above `β_c` (0.99990 at width 13 and `β = 0.60` in two
dimensions), so no uniform `δ > 0` can exist there. The two routes recorded as dead were not lossy:
they were reporting that the thing to be bounded does not exist.

**What would have to exist.** First, **the author's decision** whether §6 item 3 is restricted to `β`
below a threshold (DECISIONS NEEDED 10). Then, for the restricted statement, an estimate that sees the
matrix's structure — Dobrushin uniqueness or a high-temperature cluster expansion. Mathlib has
neither. **Kind (c).**

## W5 — the Einstein equations from the spectral action (`a₂`)

**What it is.** The Einstein equations as the `a₂` term of a heat-kernel expansion of the spectral
action — a statement about a Riemannian manifold, a Dirac operator and an asymptotic expansion of an
operator trace.

**Staircase.** Rungs 1–3 are differential geometry, and they are climbed:
* Riemannian metrics exist in Mathlib as a developed API.
* Connections do too (`CovariantDerivative`) — this ledger said otherwise until `ERRATUM 359` and
  `ERRATUM 411` corrected it.
* The algebraic Lovelock stair is climbed: every additive, homogeneous, `O(n)`-equivariant map on
  curvature tensors is `α·Ric + β·S·δ` at every `n ≥ 3` (`LovelockKillsWeyl`, `LovelockClassified`).
* 7–12 September: the geometric chain to rung 3 built in the estate — Levi-Civita, curvature and its
  symmetries, scalar curvature, the volume density. Curvature itself is absent from Mathlib. How its
  components and contractions are read is `ASSUMPTIONS_LEDGER` 54 and 56.

**Exact failing step: rung 4.** An asymptotic expansion of `Tr f(D/Λ)` in powers of `Λ`, with `a₂`
identified as a curvature integral. It needs the Dirac operator as an unbounded self-adjoint operator
with discrete spectrum, its heat semigroup, the local parametrix construction and the identification
of the coefficients. **No part of that exists here or in Mathlib.** This is W2's missing subject seen
from another wall. And no curved example exists anywhere in the estate, so the curvature definitions
have never been tested against a case that could tell a right one from a wrong one.

**What would have to exist.** Unbounded operator theory, then a research-grade formalisation of the
heat-kernel expansion. **Three rungs of standard geometry, then one research project**; the two should
not be costed together.

## W6 — the Stein class against the `Cc^∞`-defined `W^{1,2}(γ)` — CLOSED

Closed on 9 August in one dimension, and the same day in every dimension
(`SteinSmoothPi.w6_answered_pi`): the Hermite pairing, the `Cc^∞` pairing and the Lebesgue weak
derivative are three descriptions of one class, for every `n`. Nothing is outstanding.

## W7 — real Clifford classification and the spin identification — CLOSED

Closed on 8 August, with the mod-8 periodicity table proved on 18 August for every nondegenerate real
form (`CliffordPeriodicityQuantified.clifford_periodicity_eight`). The clause *except the mod-8
table* was false from that day and is corrected in place (`ERRATUM 428`).

**What remains is not mathematics.** No Lean statement is quantified over the signature `(p, q)`,
because the eight target algebras are different types. Whether to write eight theorems or one
type-valued statement is a presentation decision for the author (`ASSUMPTIONS_LEDGER` 49, DECISIONS
NEEDED). One narrow item is genuinely unproved: **separating mixed signatures**, where the estate
separates exactly two pairs, both from `Cl(1,3;ℝ)`. The identification of mixed signatures is proved.
The complex-side clause once listed here has been proved since 29 August.

## W8 — the non-trivial reflexive domain `D∞` — CLOSED

Closed on 12 August: `CanonicalTower.dInfExists_holds` gives a **non-trivial** `D` with an ω-CPO
structure and `D ≃ (D →𝒄 D)` — the estate's own statement of the target. Over sets the same equation
has only one-point solutions (`ReflexiveDomainObstruction.isSetReflexive_iff`). That is why spine L2
stays PARTIAL on its published wording (DECISIONS NEEDED 6).

## W9 — the CCM classification: from the spectral-triple axioms to the finite algebra

**What it is.** Chamseddine–Connes–Marcolli's derivation of the finite algebra `ℂ ⊕ ℍ ⊕ M₃(ℂ)` from
the axioms of a real spectral triple. It is spine L6's clause (b), and what would select `n = 4` by
theorem rather than by criterion.

**The staircase.**

| rung | statement | status |
|---|---|---|
| 1 | a finite-dimensional ⋆-algebra with a faithful ⋆-representation is semisimple — a product of matrix algebras over `ℝ`, `ℂ`, `ℍ` | **CLIMBED** 14 September (`StarRepSemisimple.isSemisimpleRing_of_faithful_star_rep`) |
| 2 | which ⋆-structures that product admits, and what the ORDER-ONE condition does to the algebra and its opposite acting on `H` | **the failing step** — first half climbed, second half climbed on model bimodules only |
| 3 | Poincaré duality on `K`-theory as a constraint on the factor list | not begun; `K`-theory of a finite algebra is absent from the estate and from Mathlib |
| 4 | `k = 2a` from the irreducibility and symplectic-unitary condition, then `a = 2`: `M₂(ℍ) ⊕ M₄(ℂ)` | not begun |
| 5 | the Standard Model sub-algebra `ℂ ⊕ ℍ ⊕ M₃(ℂ)` and its 96-dimensional representation | not begun; no declaration of that algebra exists |

**Rung 2, first half — climbed for complex matrix factors** (15–16 September):
* Every ⋆-structure on `Mₙ(ℂ)` is the conjugate transpose twisted by an inner automorphism
  (`StarStructureMatrix.exists_inner_conjTranspose`).
* A ⋆-structure on a finite product permutes its factors by an involution
  (`StarStructurePi.exists_factorPerm`, `factorPerm_involutive`).
* Up to conjugacy there are exactly `n/2 + 1` ⋆-structures on `Mₙ(ℂ)`
  (`HermitianSignatureClassification.card_achievable`).
* A faithful ⋆-representation selects the conjugate transpose's class (`StarStructureFromRep`,
  `TripleSelectsStar`).
* Real and quaternionic factors are not covered.

**Rung 2, second half — solved on the estate's model bimodules, not on CCM's.**
* On the regular bimodule of `Mₙ(ℂ)`, order-one forces `D = C ⊗ 1 + 1 ⊗ B` (unit 168). With the real
  structure, `B = C̄` (unit 169). With the grading, one real scale is left: `D = t • Dccm` (unit 170).
* On a product of matrix algebras with every pair of factors once, order-one forces `blockKron`, with
  and without `J` (units 228, 230).
* With a multiplicity (generations), order-one is the sum of two commutants (unit 232). With `J` it is
  `genPart A + 1 ⊗ Ā` (unit 234); with the grading, `Dsym ⊗ R` for a real `R` (unit 236).
* The quaternions as test algebra give the same answers (unit 237). The self-adjoint solutions are
  counted and classified (unit 241).
* **The tensor-sum shape** the spectral-action factorisation needs is decided exactly on these
  models: forced for every operator exactly for one full matrix algebra at multiplicity one, the
  trivial `M₁` aside (`KronSumCriterion`, `ProductKronSum`; units 242–243).

**Exact failing step: what order-one forces across the isotypic pieces of CCM's `H_F`.**
* `H_F` is a sub-bimodule of a product with three generations. It contains some pairs of factors and
  not others, and it has `ℍ` as a factor.
* The isotypic decomposition is not built as an object.
* One route is closed by theorem (§W9.4, 14 September): the doubled-algebra argument cannot run
  through a regular bimodule. The real regular bimodule of `M₂(ℂ)` is not faithful
  (`CentralBimoduleKernel.regAction_not_injective_M2C_over_R`), and CCM's algebra has a commutative
  factor, so the route fails over any base field. A rung-2 proof may not go through faithfulness of
  the regular bimodule.
* No Dirac operator on `H_F` is constructed, so none is shown to anticommute with its grading.

**What would have to exist.** The isotypic decomposition of a finite-dimensional bimodule over a
product of real, complex and quaternionic matrix algebras, as an object. Then order-one computed on
it, with `J` and the grading. Then `K`-theory for rung 3.

---

## How to read an open wall's status

Each wall above names the step that fails, *why*, and *what would have to exist*. The *kind* labels
follow the source ledger's taxonomy of why the walls stop: **(a)** missing library infrastructure at
community scale — W2, W5, W8, and the residue of W7; **(b)** elementary but voluminous combinatorics —
W3; **(c)** genuinely open mathematics — W4, and W1 in its physical form; **(d)** a question that
could not be settled either way — W6, which has since closed.

A wall's *failing step* is a claim about the route space, and the source ledger records failing
steps that fell by routes its own document had not listed — W1's, above, is one. So a failing step
here is where the known routes stop. It is not a proof that no route exists.
