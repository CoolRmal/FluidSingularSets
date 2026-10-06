-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallEndpointIterationStep
public import FluidSingularSets.FullBallInitialEndpointQuantity
public import FluidSingularSets.ScaledEndpointSourceBounds

/-!
# The actual suitable-solution shrinking-scale endpoint sequence

The literal iteration quantity of the radius-three-quarter rescaled solution
has a genuine source-only initial bound and recurrence. Its geometric radii
stay in the native interior range. No energy or pressure bound is assumed.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The real literal energy-plus-pressure sequence of the true scaled solution. -/
def fullBallScaledEndpointSequence (u : ParabolicPoint → Vec3)
    (D : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ) (θ : ℝ) (n : ℕ) : ℝ :=
  (fullBallEndpointIterationQuantity
    (rescaleVelocity (3 / 4) (0, 0) u) (rescaleGradient (3 / 4) (0, 0) D)
    (rescalePressure (3 / 4) (0, 0) p) (-1) 0 (-(1 / 2)) ((1 / 4) * θ ^ n) 0).toReal

/-- Every member of the literal scaled endpoint sequence is nonnegative. -/
theorem fullBallScaledEndpointSequence_nonneg
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (θ : ℝ) (n : ℕ) :
    0 ≤ fullBallScaledEndpointSequence u D p θ n := ENNReal.toReal_nonneg

/-- Genuine positive geometric radii stay in the exact native quarter-ball range. -/
theorem fullBall_scaled_endpoint_radius_bounds {θ : ℝ}
    (hθ : 0 < θ) (hθquarter : θ < 1 / 4) (n : ℕ) :
    0 < (1 / 4 : ℝ) * θ ^ n ∧ (1 / 4 : ℝ) * θ ^ n ≤ 1 / 4 := by
  refine ⟨mul_pos (by norm_num) (pow_pos hθ n), ?_⟩
  have hpow : θ ^ n ≤ 1 := pow_le_one₀ hθ.le (by linarith)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow
    (by norm_num : (0 : ℝ) ≤ 1 / 4)

section Suitable

variable {Ω : Set Vec3} {I : Set ℝ} {q θ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

/-- The genuine extended iteration quantity is finite at every actual geometric scale. -/
theorem suitable_fullBall_scaled_endpoint_sequence_quantity_lt_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0))
    (hθ : 0 < θ) (hθquarter : θ < 1 / 4) (n : ℕ) :
    fullBallEndpointIterationQuantity
      (rescaleVelocity (3 / 4) (0, 0) u) (rescaleGradient (3 / 4) (0, 0) D)
      (rescalePressure (3 / 4) (0, 0) p) (-1) 0 (-(1 / 2)) ((1 / 4) * θ ^ n) 0 < ⊤ := by
  have hs := suitable_unforced_rescale hsol (0, 0) (by norm_num : (0 : ℝ) < 3 / 4)
  have hb := localBox_rescaled_subunit_backwardCylinder hbox
    (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num)
  have hr := fullBall_scaled_endpoint_radius_bounds hθ hθquarter n
  exact suitable_fullBall_endpoint_iteration_quantity_lt_top hs hb
    (by norm_num : (-(1 / 2 : ℝ)) ∈ Ioo (-1) 0) hr.1 (hr.2.trans_lt (by norm_num))

/-- The actual extended normalized energy is controlled by the literal real sequence value. -/
theorem suitable_fullBall_scaled_endpoint_sequence_energy_le
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0))
    (hθ : 0 < θ) (hθquarter : θ < 1 / 4) (n : ℕ) :
    fullBallNormalizedProjectedIterationEnergy
      (rescaleVelocity (3 / 4) (0, 0) u) (rescaleGradient (3 / 4) (0, 0) D)
      (rescalePressure (3 / 4) (0, 0) p) (-1) 0 (-(1 / 2)) ((1 / 4) * θ ^ n) 0 ≤
        ENNReal.ofReal (fullBallScaledEndpointSequence u D p θ n) := by
  have ht := suitable_fullBall_scaled_endpoint_sequence_quantity_lt_top
    hsol hbox hθ hθquarter n
  change _ ≤ ENNReal.ofReal
    (fullBallEndpointIterationQuantity
      (rescaleVelocity (3 / 4) (0, 0) u) (rescaleGradient (3 / 4) (0, 0) D)
      (rescalePressure (3 / 4) (0, 0) p) (-1) 0 (-(1 / 2)) ((1 / 4) * θ ^ n) 0).toReal
  rw [ENNReal.ofReal_toReal ht.ne]
  exact le_self_add

/-- The actual shrinking-scale sequence starts with the original velocity source alone. -/
theorem suitable_fullBall_scaled_endpoint_sequence_initial
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) :
    let x := (velocityCylinderSixMoment u 1).toReal
    fullBallScaledEndpointSequence u D p θ 0 ≤
      fullBallScaledInitialIterationConstant * (x + x ^ 2 + x ^ 4 + x ^ (3 / 2 : ℝ)) := by
  have hx : 0 ≤ (velocityCylinderSixMoment u 1).toReal := ENNReal.toReal_nonneg
  have hA : 0 ≤ fullBallScaledInitialIterationConstant *
      ((velocityCylinderSixMoment u 1).toReal + (velocityCylinderSixMoment u 1).toReal ^ 2 +
        (velocityCylinderSixMoment u 1).toReal ^ 4 +
          (velocityCylinderSixMoment u 1).toReal ^ (3 / 2 : ℝ)) := by
    exact mul_nonneg fullBallScaledInitialIterationConstant_nonneg (by positivity)
  have hb := ENNReal.toReal_le_of_le_ofReal hA
    (suitable_fullBall_scaled_initial_endpoint_iteration_bound hsol hbox)
  simpa only [fullBallScaledEndpointSequence, pow_zero, mul_one] using hb

/-- Every actual sequence step has only the original velocity source as forcing. -/
theorem suitable_fullBall_scaled_endpoint_sequence_step
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0))
    (hθ : 0 < θ) (hθquarter : θ < 1 / 4) (n : ℕ) :
    let x := (velocityCylinderSixMoment u 1).toReal
    let F := fullBallScaledEndpointSequence u D p θ
    F (n + 1) ≤
      (1 / 8 + projectedGaussianRecurrenceUniversalConstant * θ ^ (3 / 2 : ℝ) +
        projectedGaussianRecurrenceUniversalConstant * Real.sqrt (2 * x) * (θ⁻¹) ^ 2) * F n +
      projectedGaussianRecurrenceUniversalConstant * (θ⁻¹) ^ 6 *
        (F n ^ (3 / 2 : ℝ) + (2 * x) ^ (3 / 2 : ℝ) + (2 * x) ^ 2 +
          fullBallScaledDissipationSourceConstant * (x + x ^ 2 + x ^ 4)) := by
  let x := (velocityCylinderSixMoment u 1).toReal
  let us := rescaleVelocity (3 / 4) (0, 0) u
  let Ds := rescaleGradient (3 / 4) (0, 0) D
  let ps := rescalePressure (3 / 4) (0, 0) p
  let xs := (fullBallOriginalEndpointSixSquareMoment us).toReal
  let ρ : ℝ := (1 / 4) * θ ^ n
  let r : ℝ := (1 / 4) * θ ^ (n + 1)
  have hs := suitable_unforced_rescale hsol (0, 0) (by norm_num : (0 : ℝ) < 3 / 4)
  have hb := localBox_rescaled_subunit_backwardCylinder hbox
    (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num)
  have hρbounds := fullBall_scaled_endpoint_radius_bounds hθ hθquarter n
  have hrbounds := fullBall_scaled_endpoint_radius_bounds hθ hθquarter (n + 1)
  have hρ : 0 < ρ := hρbounds.1
  have hr : 0 < r := hrbounds.1
  have hρhalf : ρ < 1 / 2 := lt_of_le_of_lt hρbounds.2 (by norm_num)
  have hrρ : r = ρ * θ := by dsimp [r, ρ]; rw [pow_succ]; ring
  have hscale : r < ρ / 4 := by
    rw [hrρ]
    nlinarith [mul_lt_mul_of_pos_left hθquarter hρ]
  have hRatio : r / ρ = θ := by rw [hrρ]; field_simp [hρ.ne']
  have hInverse : ρ / r = θ⁻¹ := by rw [hrρ]; field_simp [hρ.ne', hθ.ne']
  have hsource : xs ≤ 2 * x := by
    have he := suitable_fullBall_scaled_velocity_six_moment_le_source hsol hbox
    have hh := ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ENNReal.toReal_nonneg) he
    simpa only [xs, us, x, fullBallOriginalEndpointSixSquareMoment,
      velocityCylinderSixMoment, one_pow] using hh
  have hDsource := suitable_fullBall_scaled_full_coordinate_gradient_bound hsol hbox
  have hxs : 0 ≤ xs := ENNReal.toReal_nonneg
  have hx : 0 ≤ x := ENNReal.toReal_nonneg
  have hhalf : xs ^ (1 / 2 : ℝ) ≤ Real.sqrt (2 * x) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow hxs hsource (by norm_num)
  have hC : 0 ≤ projectedGaussianRecurrenceUniversalConstant :=
    (by norm_num : (0 : ℝ) ≤ 1).trans projectedGaussianRecurrenceUniversalConstant_ge_one
  have hF : 0 ≤ fullBallScaledEndpointSequence u D p θ n :=
    fullBallScaledEndpointSequence_nonneg u D p θ n
  have hstep := suitable_fullBall_endpoint_iteration_step hs hb
    (by norm_num : (-(1 / 2 : ℝ)) ∈ Ioo (-1) 0) hr hρ hρhalf hscale
  change fullBallScaledEndpointSequence u D p θ (n + 1) ≤
    (1 / 8 + projectedGaussianRecurrenceUniversalConstant * (r / ρ) ^ (3 / 2 : ℝ) +
      projectedGaussianRecurrenceUniversalConstant * xs ^ (1 / 2 : ℝ) * (ρ / r) ^ 2) *
        fullBallScaledEndpointSequence u D p θ n +
      projectedGaussianRecurrenceUniversalConstant * (ρ / r) ^ 6 *
        (fullBallScaledEndpointSequence u D p θ n ^ (3 / 2 : ℝ) + xs ^ (3 / 2 : ℝ) +
          xs ^ 2 + (coordinateCylinderMass Ds 1).toReal) at hstep
  rw [hRatio, hInverse] at hstep
  dsimp only
  apply hstep.trans
  gcongr

end Suitable

end FluidSingularSets
