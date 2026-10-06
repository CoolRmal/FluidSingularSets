-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedGaussianRhs
public import FluidSingularSets.ProjectedGaussianViscousPressureAbsorption

/-!
# Actual Gaussian pressure RHS absorption

Literal native mean cancellation splits the actual pressure error into its
convective and viscous pairings. The proved true flux estimates then absorb
both into a chosen small multiple of the actual iteration quantity.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The literal actual Gaussian pressure error has its true absorbed iteration/source cost. -/
theorem suitable_fullBall_projected_gaussian_pressure_error_young_bound
    {Ω : Set Vec3} {I : Set ℝ} {q c r ρ δ κ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r ≤ ρ)
    (hδ : 0 < δ) (hκ : 0 < κ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    let ψ := projectedGaussianTest r ρ δ hρ
    ‖∫ t in Ioo (-ρ ^ 2) 0, ∫ x in vec3Ball 0 ρ,
      fullBallJointPressureError u D p (-1) 0 c ψ χ (x, t)‖ ≤
      2 * κ * (fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0).toReal +
        projectedGaussianConvectivePressureConstant ^ 3 * (ρ / r) ^ 6 / κ ^ 2 *
          (fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0).toReal ^ (3 / 2 : ℝ) +
        projectedGaussianViscousPressureConstant ^ 2 * (ρ / r) ^ 4 / κ *
          (coordinateCylinderMass D 1).toReal := by
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
  have hb₁ := suitable_fullBall_gaussian_convective_pressure_iteration_absorption
    hsol hbox hc hr hρ hρhalf hscale hδ hχ hbχ hκ
  have hb₂ := suitable_fullBall_gaussian_viscous_pressure_iteration_absorption
    hsol hbox hc hr hρ hρhalf hscale hδ hχ hbχ hκ
  change ‖∫ t in Ioo (-ρ ^ 2) 0, F₁ t‖ ≤ _ at hb₁
  change ‖∫ t in Ioo (-ρ ^ 2) 0, F₂ t‖ ≤ _ at hb₂
  rw [integral_congr_ae he, integral_add h₁.1 h₂.1]
  apply (norm_add_le _ _).trans
  exact (add_le_add hb₁ hb₂).trans_eq (by ring)

end FluidSingularSets
