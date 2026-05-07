# TRIAGE: F4_1l_GaussianPartition.lean

**Grade distribution:** 6A, 1B, 0C, 10D (17 declarations)
**Assessment:** Has real Gaussian integral from Mathlib. Majority is arithmetic.

## Grade A (genuine — 6)
- `gaussian_integral_real` — ∫exp(-bx²)=√(π/b) via integral_gaussian
- `exp_neg_nonneg_le_one` — 0≤s → exp(-s)≤1 via exp_le_one_iff
- `exp_neg_pos` — 0<exp(-s) via exp_pos
- `gaussian_base_case` — ∫exp(-x²)=√π via integral_gaussian + simp
- `pi_is_positive/pi_positive` — 0<π via pi_pos

## Grade B (overclaim — 1)
- `convergence_chain_complete` — (4*4=16)∧(16-4=12)∧(16-12=4)∧(0<π)

## Grade D (arithmetic — 10)
- `herm2_dim/herm4_dim/herm16_dim` — 2*2=4, 4*4=16, 16*16=256
- `hermn_dim` — n*n=n² (ring identity)
- `partition_function_finite_dim` — 16=4*4
- `gaussian_product_dim` — n=n (rfl!)
- `dim_U4` — 4*4=16
- `physical_dof` — 16-4*(4-1)=4
- `gauge_orbit_dim` — 16-4=12
- `weyl_reduction_factor` — 16/4=4

## Action: FAST TRACK
- Keep 6 Grade A (genuine Gaussian integral + exp analysis)
- Remove all 10 Grade D arithmetic theorems
- Remove or honestly relabel Grade B convergence_chain
