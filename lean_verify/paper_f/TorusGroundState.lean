import TorusRealMultiplicity

/-!
# The ground state is the constant field, not merely something unique up to scale

`TorusRealMultiplicity` proved the real eigenspace of `massive (torusGraph d (N+3)) m` at its least
eigenvalue `m²` is **one dimensional**, and fenced what that does not say:

> **No eigenvector is exhibited over `ℝ`.** The dimensions transfer; the *bases* do not, and nothing
> below names a real eigenvector. The constant vector is the obvious one at `m²` and **it is not
> identified as spanning that eigenspace here**.

It is identified here, and the identification is short for a reason worth stating: **a
one-dimensional space containing a non-zero vector is that vector's span**, so the only new inputs
are that the constant field is an eigenvector and that it is non-zero.

> **`const_mem_ground_eigenspace`** — the constant field is an eigenvector at `m²`. This is
> `GreenExpansion.massive_mulVec_one` read as a membership: the Laplacian kills constants and only
> the mass survives.
>
> **`ground_eigenspace_eq_span_const`** — so the eigenspace **is** `span ℝ {1}`, in every dimension
> and at every side length at least three.
>
> **`eigenvector_at_least_is_const`** — hence, in the form a reader wants: **every real eigenvector
> of the massive Laplacian at `m²` is a constant field.** No other configuration sounds the lowest
> frequency.

## What is NOT here

**No claim about any other eigenvalue's eigenvectors.** The characters are eigenvectors over `ℂ` and
their real and imaginary parts are eigenvectors over `ℝ`, but **nothing below says those span an
eigenspace** at any frequency other than the zero one, and `TorusRealMultiplicity`'s counting
result gives dimensions rather than bases.

**Nothing about the top.** `TorusTopSimple` makes the top simple at even side length; the
alternating character's real part is the obvious spanning vector there and **is not identified as
one below**. The argument would be the same and it is not made.

**No physics is claimed.** *Ground state* is used here as a name for the eigenspace at the least
eigenvalue of a finite matrix. The passage from that to a statement about a field theory needs the
Gaussian measure and a limit, neither of which appears in this file.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusGroundState

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection
open MassiveTorusSpectrum TorusRealMultiplicity RealComplexKernel

variable {d : ℕ}

/-- **THE CONSTANT FIELD IS AN EIGENVECTOR AT `m²`.** `GreenExpansion.massive_mulVec_one` says the
Laplacian kills constants so only the mass survives; this is that fact as a membership. -/
theorem const_mem_ground_eigenspace (N : ℕ) (m : ℝ) :
    (fun _ => (1 : ℝ)) ∈ LinearMap.ker
      (Matrix.toLin' (massive (torusGraph d (N + 3)) m) - (m ^ 2) • LinearMap.id) := by
  rw [mem_ker_sub_smul]
  rw [GreenExpansion.massive_mulVec_one]
  funext p
  simp

/-- **THE GROUND EIGENSPACE IS THE CONSTANTS.** One dimensional by
`TorusRealMultiplicity.ground_state_simple_real`, and containing the non-zero constant field, so it
is that field's span — in every dimension and at every side length at least three. -/
theorem ground_eigenspace_eq_span_const (N : ℕ) (m : ℝ) :
    LinearMap.ker (Matrix.toLin' (massive (torusGraph d (N + 3)) m) - (m ^ 2) • LinearMap.id)
      = Submodule.span ℝ {(fun _ => (1 : ℝ) : Site d (N + 3) → ℝ)} := by
  haveI : Nonempty (Site d (N + 3)) := TorusRegular.nonempty_site (by omega)
  obtain ⟨p⟩ : Nonempty (Site d (N + 3)) := inferInstance
  have hne : (fun _ => (1 : ℝ) : Site d (N + 3) → ℝ) ≠ 0 := by
    intro h
    have := congrFun h p
    simp at this
  refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact const_mem_ground_eigenspace N m
  · rw [ground_state_simple_real N m, finrank_span_singleton hne]

/-- **SO EVERY REAL EIGENVECTOR AT THE LEAST EIGENVALUE IS CONSTANT.** No other configuration of the
lattice field sounds its lowest frequency. -/
theorem eigenvector_at_least_is_const (N : ℕ) (m : ℝ) (x : Site d (N + 3) → ℝ)
    (hx : massive (torusGraph d (N + 3)) m *ᵥ x = (m ^ 2) • x) :
    ∃ c : ℝ, x = fun _ => c := by
  have hmem : x ∈ LinearMap.ker
      (Matrix.toLin' (massive (torusGraph d (N + 3)) m) - (m ^ 2) • LinearMap.id) :=
    (mem_ker_sub_smul _ _ _).2 hx
  rw [ground_eigenspace_eq_span_const N m, Submodule.mem_span_singleton] at hmem
  obtain ⟨a, ha⟩ := hmem
  refine ⟨a, ?_⟩
  funext p
  have := congrFun ha p
  simpa using this.symm

end TorusGroundState
