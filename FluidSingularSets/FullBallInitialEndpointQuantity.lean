-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallInitialScaledEnergy
public import FluidSingularSets.FullBallNonlinearPressureDecay

/-!
# A genuine initial endpoint iteration bound from the original velocity source

The actual radius-three-quarter rescaling has an initial projected energy
bound from the original velocity mixed moment. Its actual centered convective
pressure has the same source bound. Their literal sum therefore starts the
nonlinear iteration without an additional energy or pressure hypothesis.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A finite real source coefficient for the actual initial projected iteration quantity. -/
def fullBallScaledInitialIterationConstant : ℝ :=
  fullBallScaledInitialEnergyConstant +
    (2 * fullBallInitialConvectiveOscillationConstant.toReal) ^ (3 / 2 : ℝ)

theorem fullBallScaledInitialIterationConstant_nonneg :
    0 ≤ fullBallScaledInitialIterationConstant :=
  add_nonneg fullBallScaledInitialEnergyConstant_nonneg
    (Real.rpow_nonneg (by positivity) _)

/-- Genuine suitable data bound the initial literal energy-plus-pressure iteration quantity. -/
theorem suitable_fullBall_scaled_initial_endpoint_iteration_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0)) :
    let X := (velocityCylinderSixMoment u 1).toReal
    fullBallEndpointIterationQuantity
      (rescaleVelocity (3 / 4) (0, 0) u) (rescaleGradient (3 / 4) (0, 0) D)
      (rescalePressure (3 / 4) (0, 0) p) (-1) 0 (-(1 / 2)) (1 / 4) 0 ≤
        ENNReal.ofReal (fullBallScaledInitialIterationConstant *
          (X + X ^ 2 + X ^ 4 + X ^ (3 / 2 : ℝ))) := by
  let X := (velocityCylinderSixMoment u 1).toReal
  let us := rescaleVelocity (3 / 4) (0, 0) u
  let Ds := rescaleGradient (3 / 4) (0, 0) D
  let ps := rescalePressure (3 / 4) (0, 0) p
  let x := (velocityCylinderSixMoment us 1).toReal
  let Cp := fullBallInitialConvectiveOscillationConstant.toReal
  have hX : 0 ≤ X := ENNReal.toReal_nonneg
  have hCp : 0 ≤ Cp := ENNReal.toReal_nonneg
  have hμ : (0 : ℝ) < 3 / 4 := by norm_num
  have hs := suitable_unforced_rescale hsol (0, 0) hμ
  have hb := localBox_rescaled_subunit_backwardCylinder hbox hμ (by norm_num)
  have henergy := suitable_fullBall_scaled_initial_projected_energy_bound hsol hbox
  have hpressure := suitable_fullBall_initial_convective_oscillation_le_source hs hb
  have hsource : fullBallOriginalEndpointSixSquareMoment us = ENNReal.ofReal x := by
    have hf := suitable_velocityCylinderSixMoment_unit_lt_top hs hb
    simpa only [fullBallOriginalEndpointSixSquareMoment, velocityCylinderSixMoment, one_pow,
      x, us]
      using (ENNReal.ofReal_toReal hf.ne).symm
  have hxX : x ≤ 2 * X := velocityCylinderSixMoment_rescale_toReal_le_two u
    le_rfl (by norm_num) (suitable_velocityCylinderSixMoment_unit_lt_top hsol hbox)
  have hconst : fullBallInitialConvectiveOscillationConstant = ENNReal.ofReal Cp :=
    (ENNReal.ofReal_toReal fullBallInitialConvectiveOscillationConstant_ne_top).symm
  have hp : fullBallNormalizedConvectiveOscillation us (1 / 4) 0 ≤
      ENNReal.ofReal (2 * Cp * X) := by
    rw [hsource, hconst, ← ENNReal.ofReal_mul hCp] at hpressure
    apply hpressure.trans (ENNReal.ofReal_le_ofReal ?_)
    have hh := mul_le_mul_of_nonneg_left hxX hCp
    nlinarith
  have hpp := ENNReal.rpow_le_rpow hp (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ 2 * Cp * X) (by norm_num),
    Real.mul_rpow (mul_nonneg (by norm_num) hCp) hX] at hpp
  have hpoly : 0 ≤ X + X ^ 2 + X ^ 4 := by positivity
  have hy : 0 ≤ X ^ (3 / 2 : ℝ) := Real.rpow_nonneg hX _
  have hCPow : 0 ≤ (2 * Cp) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg (by norm_num) hCp) _
  have hCE := fullBallScaledInitialEnergyConstant_nonneg
  calc
    _ ≤ ENNReal.ofReal (fullBallScaledInitialEnergyConstant * (X + X ^ 2 + X ^ 4)) +
        ENNReal.ofReal ((2 * Cp) ^ (3 / 2 : ℝ) * X ^ (3 / 2 : ℝ)) :=
      add_le_add henergy hpp
    _ = ENNReal.ofReal (fullBallScaledInitialEnergyConstant * (X + X ^ 2 + X ^ 4) +
        (2 * Cp) ^ (3 / 2 : ℝ) * X ^ (3 / 2 : ℝ)) :=
      (ENNReal.ofReal_add (mul_nonneg hCE hpoly) (mul_nonneg hCPow hy)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      change fullBallScaledInitialEnergyConstant * (X + X ^ 2 + X ^ 4) +
        (2 * Cp) ^ (3 / 2 : ℝ) * X ^ (3 / 2 : ℝ) ≤
          (fullBallScaledInitialEnergyConstant + (2 * Cp) ^ (3 / 2 : ℝ)) *
            (X + X ^ 2 + X ^ 4 + X ^ (3 / 2 : ℝ))
      nlinarith [mul_nonneg hCE hy, mul_nonneg hCPow hpoly])

end FluidSingularSets
