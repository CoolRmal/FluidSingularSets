-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.SuitableProjectedLocalEnergy
public import FluidSingularSets.MixedQuadraticSources

/-!
# Actual harmonic correction bounds by the original velocity

The actual continuous harmonic correction and its literal Hessian are bounded
on a common full time set by the original spatial L² velocity class. These
quantitative bounds follow from the actual averaged-force identity and the
proved Stokes and harmonic derivative bounds.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

local instance projectedHarmonicSourceForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The literal canonical compact Hessian component has the true force bound. -/
theorem harmonicCompactHessianOperator_component_norm_le
    (F : StokesEnergyForce (vec3Ball 0 1)) (x : unitBallPressureCompactInterior)
    (i j : Fin 3) :
    ‖harmonicCompactHessianOperator F x (i, j)‖ ≤
      3 * unitBallPressureHessianConstant * ‖F‖ := by
  change ‖unitBallHarmonicForceHessianExtended F (pressureCompactHessianInclusion x) (i, j)‖ ≤ _
  exact (PiLp.norm_apply_le _ (i, j)).trans
    (((unitBallHarmonicForceHessianExtended F).norm_coe_le_norm
      (pressureCompactHessianInclusion x)).trans
        (unitBallHarmonicForceHessianExtended_norm_le F))

/-- The literal completed velocity force is bounded by its actual spatial L² class. -/
theorem unitBallVelocityForceCurve_norm_le_actual_class
    (u : ParabolicPoint → Vec3) (t : ℝ) :
    ‖unitBallVelocityForceCurve u t‖ ≤
      3 * (stokesTestPoincareConstant (vec3Ball (0 : Vec3) 1)).toReal *
        ‖unitBallVelocityCurve u t‖ := by
  rw [unitBallVelocityForceCurve, stokesVectorForceL_apply]
  exact stokesVectorForce_norm_le (isOpen_vec3Ball 0 1).measurableSet
    volume_vec3Ball_lt_top.ne _

/-- The actual harmonic Hessian-to-original-velocity constant. -/
def projectedHarmonicHessianVelocityConstant : ℝ :=
  9 * unitBallPressureHessianConstant *
    (stokesTestPoincareConstant (vec3Ball (0 : Vec3) 1)).toReal

theorem projectedHarmonicHessianVelocityConstant_nonneg :
    0 ≤ projectedHarmonicHessianVelocityConstant := by
  unfold projectedHarmonicHessianVelocityConstant
  positivity [unitBallPressureHessianConstant_nonneg]

/-- The genuine suitable harmonic Hessian is bounded by the original L² slice class. -/
theorem suitable_projected_harmonic_hessian_velocity_bound_ae
    {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      ∀ x : unitBallPressureCompactInterior, ∀ i j : Fin 3,
        ‖suitableProjectedHarmonicDerivative u Du p t₀ (x, t) i j‖ ≤
          projectedHarmonicHessianVelocityConstant * ‖unitBallVelocityCurve u t‖ := by
  filter_upwards [suitable_unitBall_velocityForce_ae_primitive hsol hdom] with t ht
  intro x i j
  unfold suitableProjectedHarmonicDerivative
  rw [← ht]
  have hb := harmonicCompactHessianOperator_component_norm_le
    (-unitBallVelocityForceCurve u t) x j i
  rw [norm_neg] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left
    (unitBallVelocityForceCurve_norm_le_actual_class u t)
    (by positivity [unitBallPressureHessianConstant_nonneg])).trans_eq
      (by unfold projectedHarmonicHessianVelocityConstant; ring))

/-- The true harmonic correction-to-original-velocity constant. -/
def projectedHarmonicGradientVelocityConstant : ℝ :=
  3 * unitBallPressureGradientConstant *
    (stokesTestPoincareConstant (vec3Ball (0 : Vec3) 1)).toReal

theorem projectedHarmonicGradientVelocityConstant_nonneg :
    0 ≤ projectedHarmonicGradientVelocityConstant := by
  unfold projectedHarmonicGradientVelocityConstant
  positivity [unitBallPressureGradientConstant_nonneg]

/-- The genuine suitable continuous harmonic correction has the true original-velocity bound. -/
theorem suitable_projected_harmonic_gradient_velocity_bound_ae
    {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      ∀ x : unitBallPressureCompactInterior,
        ‖suitableProjectedHarmonicGradient u Du p t₀ (x, t)‖ ≤
          projectedHarmonicGradientVelocityConstant * ‖unitBallVelocityCurve u t‖ := by
  filter_upwards [suitable_unitBall_velocityForce_ae_primitive hsol hdom] with t ht
  intro x
  unfold suitableProjectedHarmonicGradient unitBallHarmonicTimePrimitive
  rw [← ht]
  change ‖-unitBallHarmonicForceGradientExtended (unitBallVelocityForceCurve u t) x‖ ≤ _
  rw [norm_neg]
  exact ((unitBallHarmonicForceGradientExtended (unitBallVelocityForceCurve u t)).norm_coe_le_norm x
    |>.trans (unitBallHarmonicForceGradientExtended_norm_le _)).trans
      ((mul_le_mul_of_nonneg_left (unitBallVelocityForceCurve_norm_le_actual_class u t)
        unitBallPressureGradientConstant_nonneg).trans_eq
          (by unfold projectedHarmonicGradientVelocityConstant; ring))

end FluidSingularSets
