-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallIterationPressureAlgebra
public import FluidSingularSets.ProjectedGaussianPressurePairings
public import FluidSingularSets.ProjectedPressureIterationAbsorption

/-!
# Actual normalized nonlinear Gaussian pressure absorption

The literal centered pressure flux is bounded by the actual iteration quantity
to power seven sixths and the square radius ratio. Genuine Young absorption
then gives a small linear term and a three-halves remainder with ratio power six.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The literal finite normalized Gaussian pressure coefficient. -/
def projectedGaussianConvectivePressureConstant : ℝ := 9 * projectedGaussianGradientConstant

/-- The actual pressure coefficient is nonnegative. -/
theorem projectedGaussianConvectivePressureConstant_nonneg :
    0 ≤ projectedGaussianConvectivePressureConstant := by
  have hC := CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
  unfold projectedGaussianConvectivePressureConstant projectedGaussianGradientConstant
  positivity

section Suitable

variable {Ω : Set Vec3} {I : Set ℝ} {q c r ρ δ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

/-- The true nonlinear Gaussian flux has the exact normalized seven-sixths energy bound. -/
theorem suitable_fullBall_gaussian_convective_pressure_iteration_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r ≤ ρ) (hδ : 0 < δ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    let G := fullBallJointProjectedPressureTest u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ
    ‖∫ t in Ioo (-ρ ^ 2) 0, ∫ x in vec3Ball 0 ρ,
      ((unitBallConvectivePressureCurve u t).val x -
        average (volume.restrict (vec3Ball 0 ρ)) (unitBallConvectivePressureCurve u t).val) *
          G (x, t)‖ₑ ≤
      ENNReal.ofReal (projectedGaussianConvectivePressureConstant * (ρ / r) ^ 2) *
        fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0 ^ (7 / 6 : ℝ) := by
  dsimp only
  have hb := (suitable_fullBall_projected_gaussian_convective_pressure_pairing
    hsol hbox hc hr hρ hρhalf hscale hδ hχ hbχ).2
  have hprod := fullBall_pressure_oscillation_energy_product_le_iteration u D p (-1) 0 c 0 hρ
  simp only [zero_sub] at hprod
  have hC : 0 ≤ projectedGaussianPressureFluxConstant r := by
    have hK := projectedGaussianConvectivePressureConstant_nonneg
    change 0 ≤ projectedGaussianConvectivePressureConstant / r ^ 2
    positivity
  have he : ENNReal.ofReal (projectedGaussianPressureFluxConstant r) * ENNReal.ofReal ρ ^ 2 =
      ENNReal.ofReal (projectedGaussianConvectivePressureConstant * (ρ / r) ^ 2) := by
    rw [← ENNReal.ofReal_pow hρ.le, ← ENNReal.ofReal_mul hC]
    congr 1
    unfold projectedGaussianPressureFluxConstant projectedGaussianConvectivePressureConstant
    field_simp [hr.ne']
  apply hb.trans
  calc
    _ = ENNReal.ofReal (projectedGaussianPressureFluxConstant r) *
        (unitBallConvectiveOscillationMoment u ρ (Ioo (-ρ ^ 2) 0) *
          fullBallProjectedIterationSliceEnergy u D p (-1) 0 c ρ 0 ^ (1 / 2 : ℝ)) := by ring
    _ ≤ _ := (mul_le_mul' le_rfl hprod).trans_eq (by rw [← mul_assoc, he])

/-- The true nonlinear Gaussian pressure is absorbed into a small linear energy term. -/
theorem suitable_fullBall_gaussian_convective_pressure_iteration_absorption
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r ≤ ρ) (hδ : 0 < δ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1)
    {κ : ℝ} (hκ : 0 < κ) :
    let G := fullBallJointProjectedPressureTest u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ
    ‖∫ t in Ioo (-ρ ^ 2) 0, ∫ x in vec3Ball 0 ρ,
      ((unitBallConvectivePressureCurve u t).val x -
        average (volume.restrict (vec3Ball 0 ρ)) (unitBallConvectivePressureCurve u t).val) *
          G (x, t)‖ ≤
      κ * (fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0).toReal +
        projectedGaussianConvectivePressureConstant ^ 3 * (ρ / r) ^ 6 / κ ^ 2 *
          (fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0).toReal ^ (3 / 2 : ℝ) := by
  dsimp only
  have hK := projectedGaussianConvectivePressureConstant_nonneg
  have hC : 0 ≤ projectedGaussianConvectivePressureConstant * (ρ / r) ^ 2 := by positivity
  have hI := suitable_fullBall_endpoint_iteration_quantity_lt_top hsol hbox hc hρ hρhalf
  have he := suitable_fullBall_gaussian_convective_pressure_iteration_bound
    hsol hbox hc hr hρ hρhalf hscale hδ hχ hbχ
  have hh := ENNReal.toReal_mono (by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hI.ne)) he
  simp only [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
    ← ENNReal.toReal_rpow] at hh
  have hy := sevenSixths_pressure_iteration_absorption hC
    (ENNReal.toReal_nonneg : 0 ≤
      (fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0).toReal) hκ
  apply hh.trans (hy.trans_eq ?_)
  rw [mul_pow, ← pow_mul]

end Suitable

end FluidSingularSets
