-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallJointPressureEnergy
public import FluidSingularSets.ProjectedGaussianHeatError

/-!
# Genuine Gaussian pressure-flux energy classes

The actual Gaussian gradient budget and suitable projected energy give the
literal pressure flux its time L∞ spatial L² class, with the precise inverse
square inner-radius coefficient and the true outer-cylinder slice supremum.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The literal finite inverse-square Gaussian pressure flux coefficient. -/
def projectedGaussianPressureFluxConstant (r : ℝ) : ℝ :=
  9 * projectedGaussianGradientConstant / r ^ 2

/-- The actual Gaussian pressure flux is controlled by the genuine outer slice energy. -/
theorem suitable_fullBall_projected_gaussian_pressure_flux_data
    {Ω : Set Vec3} {I : Set ℝ} {q c r ρ δ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r ≤ ρ) (hδ : 0 < δ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    ProjectedEnergySliceData (volume.restrict (vec3Ball 0 ρ))
        (volume.restrict (Ioo (-ρ ^ 2) 0)) ⊤
        (fullBallJointProjectedPressureTest u D p (-1) 0 c
          (projectedGaussianTest r ρ δ hρ) χ) ∧
      eLpNorm (actualSliceLp (μ := volume.restrict (vec3Ball 0 ρ)) (p := 2)
        (fullBallJointProjectedPressureTest u D p (-1) 0 c
          (projectedGaussianTest r ρ δ hρ) χ)) ⊤ (volume.restrict (Ioo (-ρ ^ 2) 0)) ≤
        ENNReal.ofReal (projectedGaussianPressureFluxConstant r) *
          fullBallProjectedIterationSliceEnergy u D p (-1) 0 c ρ 0 ^ (1 / 2 : ℝ) := by
  have ht : Ioo (-ρ ^ 2) 0 ⊆ Ioo (-1) 0 := by
    intro t h
    have hs : ρ ^ 2 < 1 / 4 := by nlinarith
    exact ⟨by linarith only [h.1, hs], h.2⟩
  have hψ := (projectedGaussianTest_admissible hr hρ hρhalf hδ).1.1
  have hM := suitable_fullBall_projected_iteration_sliceEnergy_lt_top hsol hbox hc hρ hρhalf
  have hb := suitable_fullBall_joint_pressure_test_energy_data
    (L := 3 * projectedGaussianGradientConstant / r ^ 2)
    hsol hbox (by norm_num) hc hρ (by linarith) (isOpen_vec3Ball 0 ρ)
    subset_closure measurableSet_Ioo ht hψ hχ hbχ
    (fun x _ t ht ↦ (norm_le_vec3EuclideanNorm _).trans
      (projectedGaussianTest_gradient_bound hr hρ hscale ht.2.le))
    (by simpa only [fullBallProjectedIterationSliceEnergy, zero_sub] using hM)
  have he : 3 * (3 * projectedGaussianGradientConstant / r ^ 2) =
      projectedGaussianPressureFluxConstant r := by
    unfold projectedGaussianPressureFluxConstant
    ring
  simpa only [he, fullBallProjectedIterationSliceEnergy, zero_sub] using hb

end FluidSingularSets
