-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedGaussianPressureEnergy
public import FluidSingularSets.CenteredPressureEnergyPairing
public import FluidSingularSets.FullBallNativePressureClasses
public import FluidSingularSets.FullBallViscousOscillationMoment

/-!
# Actual centered Gaussian pressure flux bounds

Genuine native pressure classes and the actual Gaussian energy class give
literal nonlinear and viscous oscillation bounds on the smaller cylinder.
Every class and integrability input is derived from the suitable solution.
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

variable {Ω : Set Vec3} {I : Set ℝ} {q c r ρ δ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

private theorem gaussian_pressure_time_subset (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    Ioo (-ρ ^ 2) 0 ⊆ Ioo (-1) 0 := by
  intro t ht
  have hs : ρ ^ 2 < 1 / 4 := by nlinarith
  exact ⟨by linarith only [ht.1, hs], ht.2⟩

/-- The actual centered nonlinear Gaussian flux has its genuine oscillation-energy bound. -/
theorem suitable_fullBall_projected_gaussian_convective_pressure_pairing
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r ≤ ρ) (hδ : 0 < δ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    let G := fullBallJointProjectedPressureTest u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ
    let F := fun t ↦ ∫ x in vec3Ball 0 ρ,
      ((unitBallConvectivePressureCurve u t).val x -
        average (volume.restrict (vec3Ball 0 ρ)) (unitBallConvectivePressureCurve u t).val) *
          G (x, t)
    Integrable F (volume.restrict (Ioo (-ρ ^ 2) 0)) ∧
      ‖∫ t in Ioo (-ρ ^ 2) 0, F t‖ₑ ≤
        unitBallConvectiveOscillationMoment u ρ (Ioo (-ρ ^ 2) 0) *
          (ENNReal.ofReal (projectedGaussianPressureFluxConstant r) *
            fullBallProjectedIterationSliceEnergy u D p (-1) 0 c ρ 0 ^ (1 / 2 : ℝ)) := by
  dsimp only
  have hn := suitable_fullBall_native_convective_pressure_memLp_one hsol hbox
  have hP : MemLp (fun t ↦ (unitBallConvectivePressureCurve u t).val) 1
      (volume.restrict (Ioo (-ρ ^ 2) 0)) :=
    (hn.continuousLinearMap_comp unitBallMeanZeroL2.toSubmodule.subtypeL).mono_measure
        (Measure.restrict_mono (gaussian_pressure_time_subset hρ hρhalf) le_rfl)
  have hd := suitable_fullBall_projected_gaussian_pressure_flux_data
    hsol hbox hc hr hρ hρhalf hscale hδ hχ hbχ
  have hb := pressureCurve_centered_pairing_one_top_integrable_and_bound
    (x := 0) (by linarith : ρ ≤ 1) hP hd.1.slices hd.1.classMemLp
  refine ⟨hb.1, hb.2.trans ?_⟩
  exact mul_le_mul' le_rfl hd.2

/-- The actual centered viscous Gaussian flux retains the true time-measure square root. -/
theorem suitable_fullBall_projected_gaussian_viscous_pressure_pairing
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r ≤ ρ) (hδ : 0 < δ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    let G := fullBallJointProjectedPressureTest u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ
    let F := fun t ↦ ∫ x in vec3Ball 0 ρ,
      ((unitBallViscousPressureCurve D t).val x -
        average (volume.restrict (vec3Ball 0 ρ)) (unitBallViscousPressureCurve D t).val) *
          G (x, t)
    Integrable F (volume.restrict (Ioo (-ρ ^ 2) 0)) ∧
      ‖∫ t in Ioo (-ρ ^ 2) 0, F t‖ₑ ≤
        unitBallViscousOscillationTwoMoment D ρ (Ioo (-ρ ^ 2) 0) *
          volume (Ioo (-ρ ^ 2) 0) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal (projectedGaussianPressureFluxConstant r) *
            fullBallProjectedIterationSliceEnergy u D p (-1) 0 c ρ 0 ^ (1 / 2 : ℝ)) := by
  dsimp only
  let : IsFiniteMeasure (volume.restrict (Ioo (-ρ ^ 2) 0)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hn := suitable_fullBall_native_viscous_pressure_memLp_two hsol hbox
  have hP : MemLp (fun t ↦ (unitBallViscousPressureCurve D t).val) 2
      (volume.restrict (Ioo (-ρ ^ 2) 0)) :=
    (hn.continuousLinearMap_comp unitBallMeanZeroL2.toSubmodule.subtypeL).mono_measure
        (Measure.restrict_mono (gaussian_pressure_time_subset hρ hρhalf) le_rfl)
  have hd := suitable_fullBall_projected_gaussian_pressure_flux_data
    hsol hbox hc hr hρ hρhalf hscale hδ hχ hbχ
  have hb := pressureCurve_centered_pairing_two_top_integrable_and_bound
    (x := 0) (by linarith : ρ ≤ 1) hP hd.1.slices hd.1.classMemLp
  rw [Measure.restrict_apply_univ] at hb
  refine ⟨hb.1, hb.2.trans ?_⟩
  exact mul_le_mul' le_rfl hd.2

end Suitable

end FluidSingularSets
