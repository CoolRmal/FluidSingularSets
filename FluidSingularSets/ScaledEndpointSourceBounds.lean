-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallInitialScaledEnergy

/-!
# Genuine source bounds for the scaled endpoint recurrence

The actual radius-three-quarter solution has a full coordinate dissipation
bound from the proved physical radius iteration. Its velocity source is
bounded by the original source as well. These estimates remove the full
native gradient term from the nonlinear iteration forcing.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The finite native full-gradient coefficient from the genuine physical radius iteration. -/
def fullBallScaledDissipationSourceConstant : ℝ :=
  (4 / 3) * projectedUnitCaccioppoliConstant32 * physicalCylinderEndpointForcingConstant

theorem fullBallScaledDissipationSourceConstant_nonneg :
    0 ≤ fullBallScaledDissipationSourceConstant :=
  mul_nonneg (mul_nonneg (by norm_num) projectedUnitCaccioppoliConstant32_nonneg)
    physicalCylinderEndpointForcingConstant_nonneg

/-- The genuine scaled full gradient has a source-only real bound. -/
theorem suitable_fullBall_scaled_full_coordinate_gradient_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0)) :
    let X := (velocityCylinderSixMoment u 1).toReal
    (coordinateCylinderMass (rescaleGradient (3 / 4) (0, 0) D) 1).toReal ≤
      fullBallScaledDissipationSourceConstant * (X + X ^ 2 + X ^ 4) := by
  have hscale : (coordinateCylinderMass (rescaleGradient (3 / 4) (0, 0) D) 1).toReal =
      (4 / 3) * (coordinateCylinderMass D (3 / 4)).toReal := by
    simpa only [show (3 / 4 : ℝ) / (3 / 4) = 1 by norm_num,
      show (3 / 4 : ℝ)⁻¹ = 4 / 3 by norm_num] using
        coordinateCylinderMass_rescale_toReal (by norm_num : (0 : ℝ) < 3 / 4) D (3 / 4)
  rw [hscale]
  exact (mul_le_mul_of_nonneg_left
    (suitable_fullBall_endpoint_coordinate_energy_bound hsol hbox)
      (by norm_num : (0 : ℝ) ≤ 4 / 3)).trans_eq (by
        unfold fullBallScaledDissipationSourceConstant
        ring)

/-- Genuine finiteness upgrades the scaled real velocity bound to an extended-real bound. -/
theorem suitable_fullBall_scaled_velocity_six_moment_le_source
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0)) :
    let X := (velocityCylinderSixMoment u 1).toReal
    velocityCylinderSixMoment (rescaleVelocity (3 / 4) (0, 0) u) 1 ≤
      ENNReal.ofReal (2 * X) := by
  have hs := suitable_unforced_rescale hsol (0, 0) (by norm_num : (0 : ℝ) < 3 / 4)
  have hb := localBox_rescaled_subunit_backwardCylinder hbox
    (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num)
  have hfin := suitable_velocityCylinderSixMoment_unit_lt_top hs hb
  calc
    _ = ENNReal.ofReal
        (velocityCylinderSixMoment (rescaleVelocity (3 / 4) (0, 0) u) 1).toReal :=
      (ENNReal.ofReal_toReal hfin.ne).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (velocityCylinderSixMoment_rescale_toReal_le_two u
      le_rfl (by norm_num) (suitable_velocityCylinderSixMoment_unit_lt_top hsol hbox))

end FluidSingularSets
