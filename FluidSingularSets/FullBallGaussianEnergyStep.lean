-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedGaussianRecurrenceCoefficients
public import FluidSingularSets.ProjectedGaussianPressureRhs
public import FluidSingularSets.ProjectedGaussianEnergyExtraction

/-!
# Actual one-step Gaussian projected-energy estimate

The true four-error RHS is bounded uniformly for every actual backward ramp.
Genuine Gaussian inner-energy extraction then gives the normalized smaller
energy solely from the actual outer energy, nonlinear pressure, original
endpoint velocity and full coordinate-gradient sources.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

section Suitable

variable {Ω : Set Vec3} {I : Set ℝ} {q c r ρ δ η κ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

/-- All four actual Gaussian RHS errors obey the genuine uniform iteration/source bound. -/
theorem suitable_fullBall_gaussian_rhs_iteration_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r ≤ ρ / 2)
    (hδ : 0 < δ) (hη : 0 < η) (hκ : 0 < κ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) :
    (∫ z, fullBallProjectedRhsDensity ρ u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) z * χ z.2
        ∂(fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo (-1) 0))) ≤
      projectedGaussianNonpressureEnergyCost r ρ η
        (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0).toReal
        (projectedGaussianOriginalSixMoment u).toReal +
      2 * projectedGaussianPressureYoungCost r ρ κ
        (fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0).toReal
        (coordinateCylinderMass D 1).toReal := by
  have hb (t : ℝ) : ‖χ t‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hbχ t).1]
    exact (hbχ t).2
  rw [suitable_fullBall_projected_gaussian_rhs_eq_errors
    hsol hbox hc hr hρ hρhalf hδ hχ hb]
  have hn := suitable_fullBall_projected_gaussian_nonpressure_bound
    hsol hbox hc hr hρ hρhalf hscale hδ hη hχ hbχ
  have hp := suitable_fullBall_projected_gaussian_pressure_error_young_bound
    hsol hbox hc hr hρ hρhalf (by linarith) hδ hκ hχ hb
  have hpu := (Real.le_norm_self _).trans hp
  change _ ≤ projectedGaussianPressureYoungCost r ρ κ
    (fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0).toReal
    (coordinateCylinderMass D 1).toReal at hpu
  convert add_le_add hn (mul_le_mul_of_nonneg_left hpu (by norm_num : (0 : ℝ) ≤ 2))
    using 1
  ring

/-- The actual normalized inner projected energy obeys the genuine Gaussian one-step bound. -/
theorem suitable_fullBall_gaussian_projected_energy_step
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r < ρ / 4)
    (hη : 0 < η) (hκ : 0 < κ) :
    fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c r 0 ≤
      ENNReal.ofReal (3000 *
        (projectedGaussianNonpressureEnergyCost r ρ η
          (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0).toReal
          (projectedGaussianOriginalSixMoment u).toReal +
        2 * projectedGaussianPressureYoungCost r ρ κ
          (fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0).toReal
          (coordinateCylinderMass D 1).toReal)) := by
  let A := projectedGaussianNonpressureEnergyCost r ρ η
      (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0).toReal
      (projectedGaussianOriginalSixMoment u).toReal +
    2 * projectedGaussianPressureYoungCost r ρ κ
      (fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0).toReal
      (coordinateCylinderMass D 1).toReal
  have hA : 0 ≤ A := add_nonneg
    (projectedGaussianNonpressureEnergyCost_nonneg hη ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (mul_nonneg (by norm_num)
      (projectedGaussianPressureYoungCost_nonneg hκ ENNReal.toReal_nonneg ENNReal.toReal_nonneg))
  have hb := suitable_fullBall_gaussian_energy_bound_of_rhs
    hsol hbox hc hr hρ hρhalf hscale hA (by
      intro δ hδ _ t h _
      exact suitable_fullBall_gaussian_rhs_iteration_bound hsol hbox hc hr hρ hρhalf
        (by linarith) hδ hη hκ backwardTimeCutoff_smooth.continuous
          (fun _ ↦ ⟨backwardTimeCutoff_nonneg, backwardTimeCutoff_le_one⟩))
  exact hb.2.2

/-- The literal normalized projected-energy step holds also as a finite real inequality. -/
theorem suitable_fullBall_gaussian_projected_energy_step_toReal
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r < ρ / 4)
    (hη : 0 < η) (hκ : 0 < κ) :
    (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c r 0).toReal ≤
      3000 *
        (projectedGaussianNonpressureEnergyCost r ρ η
          (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0).toReal
          (projectedGaussianOriginalSixMoment u).toReal +
        2 * projectedGaussianPressureYoungCost r ρ κ
          (fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0).toReal
          (coordinateCylinderMass D 1).toReal) := by
  have hA : 0 ≤ projectedGaussianNonpressureEnergyCost r ρ η
      (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0).toReal
      (projectedGaussianOriginalSixMoment u).toReal +
      2 * projectedGaussianPressureYoungCost r ρ κ
        (fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0).toReal
        (coordinateCylinderMass D 1).toReal := add_nonneg
    (projectedGaussianNonpressureEnergyCost_nonneg hη ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (mul_nonneg (by norm_num)
      (projectedGaussianPressureYoungCost_nonneg hκ ENNReal.toReal_nonneg ENNReal.toReal_nonneg))
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (suitable_fullBall_gaussian_projected_energy_step hsol hbox hc hr hρ hρhalf hscale hη hκ)
  simpa only [ENNReal.toReal_ofReal (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3000) hA)] using hh

end Suitable

end FluidSingularSets
