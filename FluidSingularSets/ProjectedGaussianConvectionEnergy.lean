-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedGaussianSourceEnergy
public import FluidSingularSets.FullBallProjectedPressureSource

/-!
# Actual normalized Gaussian convection costs

The genuine same-cylinder Sobolev interpolation bounds the literal Euclidean
cubic moment. The actual full-ball harmonic source supplies the quadratic term.
Both terms retain the exact squared radius ratio of the Gaussian derivative.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- The finite literal Gaussian convection cost in actual normalized energy and endpoint moment. -/
def projectedGaussianConvectionEnergyCost (r ρ : ℝ) (E X : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (3 * projectedGaussianGradientConstant * (ρ / r) ^ 2) *
    (27 * ballH1ParabolicInterpolationConstant * E ^ (3 / 2 : ℝ) +
      ENNReal.ofReal (fullBallProjectedHarmonicVelocityConstant (1 / 2)) *
        volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ) * E * X ^ (1 / 2 : ℝ))

section Suitable

variable {Ω : Set Vec3} {I : Set ℝ} {q c ρ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

/-- Genuine suitability yields the actual normalized Gaussian convection estimate. -/
theorem suitable_fullBall_projected_gaussian_convection_energy_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    {r δ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r ≤ ρ)
    (hδ : 0 < δ) {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    ‖∫ z : ParabolicPoint, fullBallJointConvectionError u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ z‖ₑ ≤
      projectedGaussianConvectionEnergyCost r ρ
        (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0)
          (projectedGaussianOriginalSixMoment u) := by
  have hh := suitable_fullBall_projected_gaussian_convection_moment_bound
    hsol hbox hc hr hρ hρhalf hscale hδ hχ hbχ
  refine hh.trans ((mul_le_mul' le_rfl (add_le_add
    (suitable_fullBall_projected_iteration_euclidean_cubic_le_normalized_energy
      hsol hbox hc hρ hρhalf)
    (mul_le_mul' le_rfl
      (suitable_fullBall_projected_iteration_source_square_le_normalized_energy
        hsol hbox hc hρ hρhalf)))).trans_eq ?_)
  unfold projectedGaussianConvectionEnergyCost
  have hCG : 0 ≤ projectedGaussianGradientConstant := by
    unfold projectedGaussianGradientConstant
    have hC := CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
    positivity
  have hC : 0 ≤ 3 * projectedGaussianGradientConstant / r ^ 2 := by positivity
  have he : ENNReal.ofReal (3 * projectedGaussianGradientConstant * (ρ / r) ^ 2) =
      ENNReal.ofReal (3 * projectedGaussianGradientConstant / r ^ 2) *
        ENNReal.ofReal ρ ^ 2 := by
    rw [← ENNReal.ofReal_pow hρ.le, ← ENNReal.ofReal_mul hC]
    congr 1
    rw [div_pow]
    ring
  rw [he]
  ring

/-- The actual normalized Gaussian convection cost is genuinely finite. -/
theorem suitable_projectedGaussianConvectionEnergyCost_lt_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (r : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    projectedGaussianConvectionEnergyCost r ρ
      (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0)
        (projectedGaussianOriginalSixMoment u) < ⊤ := by
  have hE := (suitable_fullBall_normalized_projected_iteration_energy_lt_top
    hsol hbox hc hρ hρhalf).ne
  have hX := (suitable_projectedGaussianOriginalSixMoment_lt_top hsol hbox).ne
  unfold projectedGaussianConvectionEnergyCost
  have hW : volume (vec3Ball (0 : Vec3) 1) ≠ ⊤ := volume_vec3Ball_lt_top.ne
  finiteness [hE, hX, hW,
    ballH1ParabolicInterpolationConstant_ne_top]

/-- The literal true Gaussian convection integral obeys the finite normalized real cost. -/
theorem suitable_fullBall_projected_gaussian_convection_energy_bound_real
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    {r δ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r ≤ ρ)
    (hδ : 0 < δ) {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    ‖∫ z : ParabolicPoint, fullBallJointConvectionError u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ z‖ ≤
      (projectedGaussianConvectionEnergyCost r ρ
        (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0)
          (projectedGaussianOriginalSixMoment u)).toReal := by
  have hh := ENNReal.toReal_mono
    (suitable_projectedGaussianConvectionEnergyCost_lt_top hsol hbox hc r hρ hρhalf).ne
    (suitable_fullBall_projected_gaussian_convection_energy_bound
      hsol hbox hc hr hρ hρhalf hscale hδ hχ hbχ)
  simpa only [toReal_enorm] using hh

end Suitable

end FluidSingularSets
