-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedGaussianConvectionEnergy
public import FluidSingularSets.ProjectedGaussianHarmonicYoung

/-!
# Genuine Gaussian heat, convection, and harmonic RHS assembly

Actual derivative support identifies each cylinder integral with its global
integral. The signed heat estimate and the two genuine flux estimates then give
a universal real cost for the three pressure-free families of the projected RHS.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- The actual Gaussian spatial derivative coefficient is nonnegative. -/
theorem projectedGaussianGradientConstant_nonneg : 0 ≤ projectedGaussianGradientConstant := by
  unfold projectedGaussianGradientConstant
  have hC := CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
  positivity

/-- The universal coefficient of the normalized projected cubic energy. -/
def projectedGaussianNonpressureCubicConstant : ℝ :=
  81 * projectedGaussianGradientConstant * ballH1ParabolicInterpolationConstant.toReal

/-- The universal coefficient of the quadratic energy times the original endpoint norm. -/
def projectedGaussianNonpressureMixedConstant : ℝ :=
  3 * projectedGaussianGradientConstant * fullBallProjectedHarmonicVelocityConstant (1 / 2) *
    (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 3 : ℝ) +
      2 * projectedGaussianHarmonicQuadraticConstant

theorem projectedGaussianNonpressureCubicConstant_nonneg :
    0 ≤ projectedGaussianNonpressureCubicConstant := by
  unfold projectedGaussianNonpressureCubicConstant
  exact mul_nonneg (mul_nonneg (by norm_num) projectedGaussianGradientConstant_nonneg)
    ENNReal.toReal_nonneg

theorem projectedGaussianNonpressureMixedConstant_nonneg :
    0 ≤ projectedGaussianNonpressureMixedConstant := by
  unfold projectedGaussianNonpressureMixedConstant
  exact add_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      projectedGaussianGradientConstant_nonneg)
        (fullBallProjectedHarmonicVelocityConstant_nonneg (by norm_num)))
          (Real.rpow_nonneg ENNReal.toReal_nonneg _))
    (mul_nonneg (by norm_num) projectedGaussianHarmonicQuadraticConstant_nonneg)

/-- The actual finite extended-real convection cost has its literal real formula. -/
theorem projectedGaussianConvectionEnergyCost_toReal
    {r ρ : ℝ} {E X : ℝ≥0∞} (hE : E ≠ ⊤) (hX : X ≠ ⊤) :
    (projectedGaussianConvectionEnergyCost r ρ E X).toReal =
      3 * projectedGaussianGradientConstant * (ρ / r) ^ 2 *
        (27 * ballH1ParabolicInterpolationConstant.toReal * E.toReal ^ (3 / 2 : ℝ) +
          fullBallProjectedHarmonicVelocityConstant (1 / 2) *
            (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 3 : ℝ) * E.toReal *
              X.toReal ^ (1 / 2 : ℝ)) := by
  have hW : volume (vec3Ball (0 : Vec3) 1) ≠ ⊤ := volume_vec3Ball_lt_top.ne
  have hCH : 0 ≤ fullBallProjectedHarmonicVelocityConstant (1 / 2) :=
    fullBallProjectedHarmonicVelocityConstant_nonneg (by norm_num)
  have hC : 0 ≤ 3 * projectedGaussianGradientConstant * (ρ / r) ^ 2 := by
    exact mul_nonneg (mul_nonneg (by norm_num) projectedGaussianGradientConstant_nonneg)
      (sq_nonneg _)
  have hA : 27 * ballH1ParabolicInterpolationConstant * E ^ (3 / 2 : ℝ) ≠ ⊤ := by
    finiteness [ballH1ParabolicInterpolationConstant_ne_top, hE]
  have hB : ENNReal.ofReal (fullBallProjectedHarmonicVelocityConstant (1 / 2)) *
      volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ) * E * X ^ (1 / 2 : ℝ) ≠ ⊤ := by
    finiteness [hW, hE, hX]
  unfold projectedGaussianConvectionEnergyCost
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, ENNReal.toReal_add hA hB]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hCH]

/-- Genuine Gaussian support localizes each of the three actual error integrals. -/
theorem projectedGaussian_nonpressure_integrals_eq_global
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (c r ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ)
    (χ : ℝ → ℝ) :
    let ψ := projectedGaussianTest r ρ δ hρ
    (∫ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
      fullBallJointHeatError u D p (-1) 0 c ψ χ z) =
        (∫ z : ParabolicPoint, fullBallJointHeatError u D p (-1) 0 c ψ χ z) ∧
    (∫ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
      fullBallJointConvectionError u D p (-1) 0 c ψ χ z) =
        (∫ z : ParabolicPoint, fullBallJointConvectionError u D p (-1) 0 c ψ χ z) ∧
    (∫ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
      fullBallJointHarmonicError u D p (-1) 0 c ψ χ z) =
        (∫ z : ParabolicPoint, fullBallJointHarmonicError u D p (-1) 0 c ψ χ z) := by
  dsimp only
  have hs := projectedGaussianTest_tsupport_cylinder (r := r) hρ hδ
  have hz (z : ParabolicPoint) (hz : z ∉ vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0) :
      z ∉ tsupport (projectedGaussianTest r ρ δ hρ) := fun h ↦ hz (hs h)
  exact ⟨setIntegral_eq_integral_of_forall_compl_eq_zero (fun z h ↦
    (fullBallJointEnergyErrors_zero_off_tsupport u D p (-1) 0 c _ χ z (hz z h)).1),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z h ↦
      (fullBallJointEnergyErrors_zero_off_tsupport u D p (-1) 0 c _ χ z (hz z h)).2.1),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z h ↦
      (fullBallJointEnergyErrors_zero_off_tsupport u D p (-1) 0 c _ χ z (hz z h)).2.2.2)⟩

/-- The universal real cost of the three pressure-free genuine Gaussian RHS families. -/
def projectedGaussianNonpressureEnergyCost (r ρ η E X : ℝ) : ℝ :=
  projectedGaussianHeatConstant * (r / ρ) ^ 2 * E +
    projectedGaussianNonpressureCubicConstant * (ρ / r) ^ 2 * E ^ (3 / 2 : ℝ) +
    projectedGaussianNonpressureMixedConstant * (ρ / r) ^ 2 * E * X ^ (1 / 2 : ℝ) +
    2 * η * E + 2 * (projectedGaussianHarmonicLinearConstant ^ 2 / (4 * η)) *
      (ρ / r) ^ 2 * X ^ 2

/-- Actual suitability gives the uniform true heat, convection, and harmonic RHS upper bound. -/
theorem suitable_fullBall_projected_gaussian_nonpressure_bound
    {Ω : Set Vec3} {I : Set ℝ} {q c r ρ δ η : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r ≤ ρ / 2)
    (hδ : 0 < δ) (hη : 0 < η) {χ : ℝ → ℝ} (hχ : Continuous χ)
    (hbχ : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) :
    let ψ := projectedGaussianTest r ρ δ hρ
    (∫ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
      fullBallJointHeatError u D p (-1) 0 c ψ χ z) +
    (∫ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
      fullBallJointConvectionError u D p (-1) 0 c ψ χ z) +
    2 * (∫ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
      fullBallJointHarmonicError u D p (-1) 0 c ψ χ z) ≤
      projectedGaussianNonpressureEnergyCost r ρ η
        (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0).toReal
          (projectedGaussianOriginalSixMoment u).toReal := by
  dsimp only
  obtain ⟨he, hce, hbe⟩ :=
    projectedGaussian_nonpressure_integrals_eq_global u D p c r ρ δ hρ hδ χ
  rw [he, hce, hbe]
  have hb (t : ℝ) : ‖χ t‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hbχ t).1]
    exact (hbχ t).2
  have hrρ : r ≤ ρ := hscale.trans (by linarith)
  have hE := (suitable_fullBall_normalized_projected_iteration_energy_lt_top
    hsol hbox hc hρ hρhalf).ne
  have hX := (suitable_projectedGaussianOriginalSixMoment_lt_top hsol hbox).ne
  have hh := suitable_fullBall_projected_gaussian_heat_bound
    hsol hbox hc hr hρ hρhalf hscale hδ hχ hbχ
  have hcNorm := suitable_fullBall_projected_gaussian_convection_energy_bound_real
    hsol hbox hc hr hρ hρhalf hrρ hδ hχ hb
  rw [projectedGaussianConvectionEnergyCost_toReal hE hX] at hcNorm
  have hbNorm := suitable_fullBall_projected_gaussian_harmonic_young_bound
    hsol hbox hc hr hρ hρhalf hrρ hδ hη hχ hb
  have hcUpper := (Real.le_norm_self _).trans hcNorm
  have hbUpper := (Real.le_norm_self _).trans hbNorm
  refine (add_le_add (add_le_add hh hcUpper)
    (mul_le_mul_of_nonneg_left hbUpper (by norm_num))).trans_eq ?_
  unfold projectedGaussianNonpressureEnergyCost projectedGaussianNonpressureCubicConstant
    projectedGaussianNonpressureMixedConstant
  ring

end FluidSingularSets
