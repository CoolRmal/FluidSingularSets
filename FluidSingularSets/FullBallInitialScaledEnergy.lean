-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallInitialProjectedEnergy
public import FluidSingularSets.FullBallRadiusCaccioppoli

/-!
# Genuine initial projected energy from the original velocity moment

At the actual physical projection radius three quarters, the proved endpoint
gradient estimate controls the rescaled full gradient energy. Exact scaling
and monotonicity control the rescaled velocity source as well. Consequently
the initial normalized projected energy depends only on the original velocity
mixed moment, with no outer energy hypothesis.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A finite actual coefficient for initial energy after radius-three-quarter scaling. -/
def fullBallScaledInitialEnergyConstant : ℝ :=
  6 * (projectedUnitCaccioppoliConstant32 * physicalCylinderEndpointForcingConstant +
    16 * fullCylinderEndpointForcingConstant / (1 - (3 / 4 : ℝ)) ^ 12)

theorem fullBallScaledInitialEnergyConstant_nonneg :
    0 ≤ fullBallScaledInitialEnergyConstant := by
  unfold fullBallScaledInitialEnergyConstant
  exact mul_nonneg (by norm_num) (add_nonneg
    (mul_nonneg projectedUnitCaccioppoliConstant32_nonneg
      physicalCylinderEndpointForcingConstant_nonneg)
    (div_nonneg (mul_nonneg (by norm_num) fullCylinderEndpointForcingConstant_nonneg)
      (by positivity)))

/-- Actual suitable data alone bound the genuine initial energy of the radius-scaled projection. -/
theorem suitable_fullBall_scaled_initial_projected_energy_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0)) :
    let X := (velocityCylinderSixMoment u 1).toReal
    fullBallNormalizedProjectedIterationEnergy
      (rescaleVelocity (3 / 4) (0, 0) u) (rescaleGradient (3 / 4) (0, 0) D)
      (rescalePressure (3 / 4) (0, 0) p) (-1) 0 (-(1 / 2)) (1 / 4) 0 ≤
        ENNReal.ofReal (fullBallScaledInitialEnergyConstant * (X + X ^ 2 + X ^ 4)) := by
  let X := (velocityCylinderSixMoment u 1).toReal
  let us := rescaleVelocity (3 / 4) (0, 0) u
  let Ds := rescaleGradient (3 / 4) (0, 0) D
  let ps := rescalePressure (3 / 4) (0, 0) p
  let x := (velocityCylinderSixMoment us 1).toReal
  have hμ : (0 : ℝ) < 3 / 4 := by norm_num
  have hs := suitable_unforced_rescale hsol (0, 0) hμ
  have hb := localBox_rescaled_subunit_backwardCylinder hbox hμ (by norm_num)
  have hinitial := suitable_fullBall_initial_normalized_projected_energy_bound hs hb
  have hgrad := suitable_fullBall_endpoint_coordinate_energy_bound hsol hbox
  have hscale : (coordinateCylinderMass Ds 1).toReal =
      (4 / 3) * (coordinateCylinderMass D (3 / 4)).toReal := by
    simpa only [show (3 / 4 : ℝ) / (3 / 4) = 1 by norm_num,
      show (3 / 4 : ℝ)⁻¹ = 4 / 3 by norm_num] using
      coordinateCylinderMass_rescale_toReal hμ D (3 / 4)
  have hxX : x ≤ 2 * X := velocityCylinderSixMoment_rescale_toReal_le_two u
    le_rfl (by norm_num) (suitable_velocityCylinderSixMoment_unit_lt_top hsol hbox)
  have hpoly := endpoint_source_polynomial_le_sixteen
    (show 0 ≤ x from ENNReal.toReal_nonneg) (show 0 ≤ X from ENNReal.toReal_nonneg) hxX
  have hbudget : fullBallInitialProjectedBudget us Ds ≤
      (projectedUnitCaccioppoliConstant32 * physicalCylinderEndpointForcingConstant +
        16 * fullCylinderEndpointForcingConstant / (1 - (3 / 4 : ℝ)) ^ 12) *
          (X + X ^ 2 + X ^ 4) := by
    unfold fullBallInitialProjectedBudget
    rw [hscale]
    change (3 / 4) * ((4 / 3) * (coordinateCylinderMass D (3 / 4)).toReal) +
      fullCylinderEndpointForcingConstant / (1 - (3 / 4 : ℝ)) ^ 12 *
        (x + x ^ 2 + x ^ 4) ≤ _
    calc
      _ ≤ (3 / 4) * ((4 / 3) * (projectedUnitCaccioppoliConstant32 *
          physicalCylinderEndpointForcingConstant * (X + X ^ 2 + X ^ 4))) +
          fullCylinderEndpointForcingConstant / (1 - (3 / 4 : ℝ)) ^ 12 *
            (16 * (X + X ^ 2 + X ^ 4)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hgrad (by norm_num)) (by norm_num))
          (mul_le_mul_of_nonneg_left hpoly
            (div_nonneg fullCylinderEndpointForcingConstant_nonneg (by positivity)))
      _ = _ := by ring
  calc
    _ ≤ ENNReal.ofReal (6 * fullBallInitialProjectedBudget us Ds) := hinitial
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      unfold fullBallScaledInitialEnergyConstant
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbudget (by norm_num : (0 : ℝ) ≤ 6))

end FluidSingularSets
