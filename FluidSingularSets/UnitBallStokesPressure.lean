-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.BallDivergenceInverse
public import FluidSingularSets.StokesPressureRecovery

/-!
# Genuine bounded mean-zero Stokes pressure on the unit ball

The actual divergence right inverse constructs a continuous pressure functional
from the actual variational residual. Negative Riesz representation gives the
usual Stokes sign: gradient energy minus the pressure-divergence pairing equals
the force. The pressure has literal zero ball integral and a uniform norm bound.
-/

@[expose] public section

open MeasureTheory Set CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The genuine mean-zero pressure obtained from the constructed divergence inverse. -/
def unitBallStokesPressure (F : StokesEnergyForce (vec3Ball 0 1)) : unitBallMeanZeroL2 :=
  -((InnerProductSpace.toDual ℝ unitBallMeanZeroL2).symm
    ((stokesEnergyResidual F).comp unitBallEnergyDivergenceRightInverse))

/-- The pressure is genuinely bounded in the spatial L² norm. -/
theorem unitBallStokesPressure_norm (F : StokesEnergyForce (vec3Ball 0 1)) :
    ‖unitBallStokesPressure F‖ ≤ 4 * ‖F‖ := by
  rw [unitBallStokesPressure, norm_neg,
    (InnerProductSpace.toDual ℝ unitBallMeanZeroL2).symm.norm_map]
  calc
    _ ≤ ‖stokesEnergyResidual F‖ * ‖unitBallEnergyDivergenceRightInverse‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (2 * ‖F‖) * 2 := mul_le_mul (stokesEnergyResidual_norm_le F)
      unitBallEnergyDivergenceRightInverse_norm
      (norm_nonneg unitBallEnergyDivergenceRightInverse) (by positivity)
    _ = _ := by ring

/-- The actual pressure has literal zero mean on the actual ball. -/
theorem unitBallStokesPressure_integral_zero (F : StokesEnergyForce (vec3Ball 0 1)) :
    (∫ x in vec3Ball 0 1, (unitBallStokesPressure F :
      Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x) = 0 :=
  (unitBallMeanZeroL2_mem_iff _).mp (unitBallStokesPressure F).property

/-- The genuine pressure gradient is exactly the actual variational residual. -/
theorem unitBallStokesPressure_pairing (F : StokesEnergyForce (vec3Ball 0 1))
    (v : stokesGradientEnergySpace (vec3Ball 0 1)) :
    -(inner ℝ (unitBallStokesPressure F : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))
      (stokesEnergyDivergence (vec3Ball 0 1) v)) = stokesEnergyResidual F v := by
  have hcod := unitBallEnergyDivergenceRightInverse_apply (unitBallMeanZeroDivergence v)
  have hraw : stokesEnergyDivergence (vec3Ball 0 1)
      (unitBallEnergyDivergenceRightInverse (unitBallMeanZeroDivergence v) - v) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val hcod)
  have hres := stokesEnergyResidual_eq_zero_of_divergence_eq_zero F
    (unitBallEnergyDivergenceRightInverse (unitBallMeanZeroDivergence v) - v) hraw
  rw [map_sub] at hres
  change -(inner ℝ (unitBallStokesPressure F) (unitBallMeanZeroDivergence v)) = _
  rw [unitBallStokesPressure, inner_neg_left, neg_neg, InnerProductSpace.toDual_symm_apply]
  exact sub_eq_zero.mp hres

/-- The recovered pressure solves the actual weak Stokes equation against every
compact smooth vector test, with a genuine integrable pressure pairing. -/
theorem unitBallStokesPressure_test (F : StokesEnergyForce (vec3Ball 0 1))
    (φ : StokesVectorTest (vec3Ball 0 1)) :
    Integrable (fun x ↦ (unitBallStokesPressure F :
      Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x * ∑ i : Fin 3, (φ i).partialDeriv i x)
      (volume.restrict (vec3Ball 0 1)) ∧
    inner ℝ (stokesEnergySolution F : stokesGradientEnergySpace (vec3Ball 0 1))
      (stokesEnergyTest φ) -
        (∫ x in vec3Ball 0 1, (unitBallStokesPressure F :
          Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x * ∑ i : Fin 3, (φ i).partialDeriv i x) =
            F (stokesEnergyTest φ) := by
  let p : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)) := unitBallStokesPressure F
  have hprod : (fun x ↦ inner ℝ (p x)
      (stokesEnergyDivergence (vec3Ball 0 1) (stokesEnergyTest φ) x))
        =ᵐ[volume.restrict (vec3Ball 0 1)]
          (fun x ↦ p x * ∑ i : Fin 3, (φ i).partialDeriv i x) := by
    filter_upwards [stokesEnergyDivergence_test_ae φ] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  refine ⟨(L2.integrable_inner (𝕜 := ℝ) p
    (stokesEnergyDivergence (vec3Ball 0 1) (stokesEnergyTest φ))).congr hprod, ?_⟩
  have hpair := unitBallStokesPressure_pairing F (stokesEnergyTest φ)
  rw [L2.inner_def, integral_congr_ae hprod] at hpair
  change -(∫ x in vec3Ball 0 1, p x * ∑ i : Fin 3, (φ i).partialDeriv i x) =
    F (stokesEnergyTest φ) -
      inner ℝ (stokesEnergySolution F : stokesGradientEnergySpace (vec3Ball 0 1))
        (stokesEnergyTest φ) at hpair
  linarith

end FluidSingularSets
