-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedGaussianNonpressureRhs
public import FluidSingularSets.ProjectedGaussianConvectivePressureAbsorption
public import FluidSingularSets.ProjectedGaussianViscousPressureAbsorption
public import FluidSingularSets.FullBallNonlinearPressureDecay

/-!
# Universal coefficients of the genuine Gaussian iteration

The pressure cost is the literal sum of the two proved Gaussian Young costs.
A fixed absorption choice makes the total linear absorption exactly one eighth.
Every coefficient below is independent of the solution and both radii.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The one fixed absorption parameter used for all Gaussian error families. -/
def projectedGaussianAbsorptionParameter : ℝ := 1 / 144000

theorem projectedGaussianAbsorptionParameter_pos : 0 < projectedGaussianAbsorptionParameter := by
  norm_num [projectedGaussianAbsorptionParameter]

/-- The exact total absorption after the genuine Gaussian energy extraction factor. -/
theorem projectedGaussianAbsorptionParameter_identity :
    3000 * (2 * projectedGaussianAbsorptionParameter +
      4 * projectedGaussianAbsorptionParameter) = (1 / 8 : ℝ) := by
  norm_num [projectedGaussianAbsorptionParameter]

/-- The genuine backward heat collar coefficient is nonnegative. -/
theorem projectedGaussianHeatConstant_nonneg : 0 ≤ projectedGaussianHeatConstant := by
  unfold projectedGaussianHeatConstant
  have hG := CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
  have hD := CKN.Foundation.Heat.cutoffSecondDerivativeConstant_nonneg_global
  positivity

/-- The literal real cost of the actual convective and viscous pressure Young bounds. -/
def projectedGaussianPressureYoungCost (r ρ κ Y D : ℝ) : ℝ :=
  2 * κ * Y + projectedGaussianConvectivePressureConstant ^ 3 * (ρ / r) ^ 6 / κ ^ 2 *
    Y ^ (3 / 2 : ℝ) + projectedGaussianViscousPressureConstant ^ 2 * (ρ / r) ^ 4 / κ * D

theorem projectedGaussianPressureYoungCost_nonneg
    {r ρ κ Y D : ℝ} (hκ : 0 < κ) (hY : 0 ≤ Y) (hD : 0 ≤ D) :
    0 ≤ projectedGaussianPressureYoungCost r ρ κ Y D := by
  have hC := projectedGaussianConvectivePressureConstant_nonneg
  unfold projectedGaussianPressureYoungCost
  positivity

theorem projectedGaussianNonpressureEnergyCost_nonneg
    {r ρ η E X : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hX : 0 ≤ X) :
    0 ≤ projectedGaussianNonpressureEnergyCost r ρ η E X := by
  have hH := projectedGaussianHeatConstant_nonneg
  have hC := projectedGaussianNonpressureCubicConstant_nonneg
  have hM := projectedGaussianNonpressureMixedConstant_nonneg
  unfold projectedGaussianNonpressureEnergyCost
  positivity

/-- One genuine universal coefficient dominates every real Gaussian recurrence coefficient. -/
def projectedGaussianRecurrenceUniversalConstant : ℝ :=
  1 +
    (3000 * projectedGaussianHeatConstant +
      fullBallNonlinearPressurePowerContractionConstant.toReal) +
    3000 * projectedGaussianNonpressureMixedConstant +
    (3000 * projectedGaussianNonpressureCubicConstant +
      6000 * projectedGaussianConvectivePressureConstant ^ 3 /
        projectedGaussianAbsorptionParameter ^ 2) +
    1500 * projectedGaussianHarmonicLinearConstant ^ 2 / projectedGaussianAbsorptionParameter +
    6000 * projectedGaussianViscousPressureConstant ^ 2 / projectedGaussianAbsorptionParameter +
    fullBallNonlinearPressurePowerSourceConstant.toReal

theorem projectedGaussianRecurrenceUniversalConstant_ge_one :
    1 ≤ projectedGaussianRecurrenceUniversalConstant := by
  have hH := projectedGaussianHeatConstant_nonneg
  have hC := projectedGaussianNonpressureCubicConstant_nonneg
  have hM := projectedGaussianNonpressureMixedConstant_nonneg
  have hP := projectedGaussianConvectivePressureConstant_nonneg
  have hκ := projectedGaussianAbsorptionParameter_pos
  unfold projectedGaussianRecurrenceUniversalConstant
  have hA : 0 ≤ 3000 * projectedGaussianHeatConstant +
      fullBallNonlinearPressurePowerContractionConstant.toReal := by positivity
  have hB : 0 ≤ 3000 * projectedGaussianNonpressureMixedConstant := by positivity
  have hC' : 0 ≤ 3000 * projectedGaussianNonpressureCubicConstant +
      6000 * projectedGaussianConvectivePressureConstant ^ 3 /
        projectedGaussianAbsorptionParameter ^ 2 := by positivity
  have hD : 0 ≤ 1500 * projectedGaussianHarmonicLinearConstant ^ 2 /
      projectedGaussianAbsorptionParameter := by positivity
  have hE : 0 ≤ 6000 * projectedGaussianViscousPressureConstant ^ 2 /
      projectedGaussianAbsorptionParameter := by positivity
  have hF : 0 ≤ fullBallNonlinearPressurePowerSourceConstant.toReal := ENNReal.toReal_nonneg
  linarith

end FluidSingularSets
