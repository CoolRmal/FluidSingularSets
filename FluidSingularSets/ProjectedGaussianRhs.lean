-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallJointPatchRhs
public import FluidSingularSets.ProjectedGaussianPressurePairings

/-!
# Actual Gaussian RHS and centered pressure error

The original native projected RHS is exactly its four genuine smaller-cylinder
errors. Actual divergence cancels the pressure means on that cylinder, and the
literal nonlinear and viscous oscillation moments bound the true pressure flux.
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

/-- Genuine Gaussian support localizes the literal original RHS to its four cylinder errors. -/
theorem suitable_fullBall_projected_gaussian_rhs_eq_errors
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hδ : 0 < δ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    let ψ := projectedGaussianTest r ρ δ hρ
    (∫ z, fullBallProjectedRhsDensity ρ u D p (-1) 0 c ψ z * χ z.2
      ∂(fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo (-1) 0))) =
      (∫ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
        fullBallJointHeatError u D p (-1) 0 c ψ χ z) +
      (∫ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
        fullBallJointConvectionError u D p (-1) 0 c ψ χ z) +
      2 * (∫ t in Ioo (-ρ ^ 2) 0, ∫ x in vec3Ball 0 ρ,
        fullBallJointPressureError u D p (-1) 0 c ψ χ (x, t)) +
      2 * (∫ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
        fullBallJointHarmonicError u D p (-1) 0 c ψ χ z) := by
  dsimp only
  obtain ⟨hψ, hnψ, hsupp⟩ := projectedGaussianTest_admissible hr hρ hρhalf hδ
  have hψ' : projectedGaussianTest r ρ δ hρ ∈ spaceTimeTestFunction (V := ℝ) Ω I := by
    refine ⟨hψ.1, hψ.2.1, hψ.2.2.trans ?_⟩
    exact Set.prod_mono (subset_closure.trans hbox.2.2.1)
      (subset_closure.trans hbox.2.2.2.2.2)
  exact suitable_fullBall_joint_rhs_integral_eq_patch_errors
    hsol hbox (by norm_num) hc hρ (by linarith) hψ' hnψ hsupp
    (projectedGaussianTest_tsupport_cylinder hρ hδ) hχ hbχ

/-- Actual mean cancellation and both genuine pressure classes bound the literal Gaussian error. -/
theorem suitable_fullBall_projected_gaussian_pressure_error_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r ≤ ρ) (hδ : 0 < δ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    let ψ := projectedGaussianTest r ρ δ hρ
    Integrable (fun t ↦ ∫ x in vec3Ball 0 ρ,
      fullBallJointPressureError u D p (-1) 0 c ψ χ (x, t))
        (volume.restrict (Ioo (-ρ ^ 2) 0)) ∧
      ‖∫ t in Ioo (-ρ ^ 2) 0, ∫ x in vec3Ball 0 ρ,
        fullBallJointPressureError u D p (-1) 0 c ψ χ (x, t)‖ₑ ≤
        (unitBallConvectiveOscillationMoment u ρ (Ioo (-ρ ^ 2) 0) +
          unitBallViscousOscillationTwoMoment D ρ (Ioo (-ρ ^ 2) 0) *
            volume (Ioo (-ρ ^ 2) 0) ^ (1 / 2 : ℝ)) *
          (ENNReal.ofReal (projectedGaussianPressureFluxConstant r) *
            fullBallProjectedIterationSliceEnergy u D p (-1) 0 c ρ 0 ^ (1 / 2 : ℝ)) := by
  dsimp only
  let ψ := projectedGaussianTest r ρ δ hρ
  let G := fullBallJointProjectedPressureTest u D p (-1) 0 c ψ χ
  let m₁ : ℝ → ℝ := fun t ↦ average (volume.restrict (vec3Ball 0 ρ))
    (unitBallConvectivePressureCurve u t).val
  let m₂ : ℝ → ℝ := fun t ↦ average (volume.restrict (vec3Ball 0 ρ))
    (unitBallViscousPressureCurve D t).val
  let F₁ : ℝ → ℝ := fun t ↦ ∫ x in vec3Ball 0 ρ,
    ((unitBallConvectivePressureCurve u t).val x - m₁ t) * G (x, t)
  let F₂ : ℝ → ℝ := fun t ↦ ∫ x in vec3Ball 0 ρ,
    ((unitBallViscousPressureCurve D t).val x - m₂ t) * G (x, t)
  obtain ⟨hψ, _, _⟩ := projectedGaussianTest_admissible hr hρ hρhalf hδ
  have hs : ∀ z ∈ tsupport ψ, z.1 ∈ vec3Ball 0 ρ :=
    fun z hz ↦ (projectedGaussianTest_tsupport_cylinder hρ hδ hz).1
  have ht : Ioo (-ρ ^ 2) 0 ⊆ Ioo (-1) 0 := by
    intro t htt
    have hs : ρ ^ 2 < 1 / 4 := by nlinarith
    exact ⟨by linarith only [htt.1, hs], htt.2⟩
  have he : (fun t ↦ ∫ x in vec3Ball 0 ρ,
      fullBallJointPressureError u D p (-1) 0 c ψ χ (x, t)) =ᵐ[
        volume.restrict (Ioo (-ρ ^ 2) 0)] fun t ↦ F₁ t + F₂ t :=
    (suitable_fullBall_joint_pressure_pairing_eq_centered_stokes_ae
      hsol hbox hρ (by linarith) (isOpen_vec3Ball 0 ρ) subset_closure
      hψ.1 hψ.2.1 hs χ m₁ m₂).filter_mono
        (ae_mono (Measure.restrict_mono ht le_rfl))
  have h₁ := suitable_fullBall_projected_gaussian_convective_pressure_pairing
    hsol hbox hc hr hρ hρhalf hscale hδ hχ hbχ
  have h₂ := suitable_fullBall_projected_gaussian_viscous_pressure_pairing
    hsol hbox hc hr hρ hρhalf hscale hδ hχ hbχ
  refine ⟨(h₁.1.add h₂.1).congr he.symm, ?_⟩
  rw [integral_congr_ae he, integral_add h₁.1 h₂.1]
  apply ((enorm_add_le _ _).trans (add_le_add h₁.2 h₂.2)).trans_eq
  ring

end Suitable

end FluidSingularSets
