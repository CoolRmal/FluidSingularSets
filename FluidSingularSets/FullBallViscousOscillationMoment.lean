-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallPressureMixedBounds
public import FluidSingularSets.SuitableViscousPressureHarmonic
public import FluidSingularSets.HarmonicPressureOscillation
public import FluidSingularSets.FullBallGradientMomentFinite

/-!
# Actual centered viscous-pressure time L² decay

Suitable weak gradients and the genuine slice divergence equation make the
native viscous Stokes pressure harmonic. Its actual centered spatial L² norm
therefore decays by the factor r^(5/2), and its actual time L² norm is bounded
by the full original coordinate-gradient energy with the same radius factor.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The literal centered viscous-pressure L²-time/L²-space moment. -/
def unitBallViscousOscillationTwoMoment
    (D : ParabolicPoint → Fin 3 → Vec3) (r : ℝ) (J : Set ℝ) : ℝ≥0∞ :=
  (∫⁻ t in J, eLpNorm
    (fun x ↦ (unitBallViscousPressureCurve D t :
      Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x -
      average (volume.restrict (vec3Ball 0 r))
        (unitBallViscousPressureCurve D t : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))) 2
    (volume.restrict (vec3Ball 0 r)) ^ 2) ^ (1 / 2 : ℝ)

/-- Actual suitability gives the genuine centered spatial harmonic decay at almost every time. -/
theorem suitable_unitBallViscousPressureCurve_centered_decay_ae_localBox
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J)
    {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hρone : ρ < 1) :
    ∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x ↦ (unitBallViscousPressureCurve D t :
          Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x -
        average (volume.restrict (vec3Ball 0 r))
          (unitBallViscousPressureCurve D t : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))) 2
        (volume.restrict (vec3Ball 0 r)) ≤
      fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal r ^ (5 / 2 : ℝ) *
        ‖unitBallViscousPressureCurve D t‖ₑ := by
  filter_upwards [suitable_unitBall_viscousPressureCurve_weaklyHarmonic_ae hsol hbox]
    with t ht
  have h := fullBallHarmonic_centered_eLpNorm_two_decay
    (Lp.memLp (unitBallViscousPressureCurve D t).val) ht hr hrρ hρone
  rw [← Lp.enorm_def] at h
  exact h

/-- The true centered harmonic decay persists in the actual time L² seminorm. -/
theorem suitable_unitBallViscousOscillationTwoMoment_le_pressure_time_two
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J)
    {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hρone : ρ < 1) :
    unitBallViscousOscillationTwoMoment D r J ≤
      fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal r ^ (5 / 2 : ℝ) *
        eLpNorm (unitBallViscousPressureCurve D) 2 (volume.restrict J) := by
  have hr1 : r ≤ 1 := hrρ.trans hρone.le
  have hD : AEStronglyMeasurable D
      ((volume.restrict (vec3Ball 0 1)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hsol.toData.aestronglyMeasurable_gradient hbox
  have hP : AEStronglyMeasurable
      (fun t ↦ (unitBallViscousPressureCurve D t).val) (volume.restrict J) :=
    unitBallMeanZeroL2.toSubmodule.subtypeL.continuous.comp_aestronglyMeasurable
      (unitBallViscousPressureCurve_aestronglyMeasurable hD)
  have hC := ballCenteredPressureL_aestronglyMeasurable 0 hr1 hP
  have hp := (suitable_unitBallViscousPressureCurve_centered_decay_ae_localBox
    hsol hbox hr hrρ hρone).mono fun t ht ↦ by
      rw [← ballCenteredPressureL_enorm 0 hr1] at ht
      exact ht
  have hb := eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' 2 hC hp
  rw [ballCenteredPressureL_eLpNorm_two_eq 0 hr1 hP] at hb
  exact hb

/-- Actual full-box coordinate-gradient energy controls centered viscous oscillation,
retaining the essential r^(5/2) spatial factor. -/
theorem suitable_unitBallViscousOscillationTwoMoment_le_coordinate_energy
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J)
    {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hρone : ρ < 1) :
    unitBallViscousOscillationTwoMoment D r J ≤
      12 * fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal r ^ (5 / 2 : ℝ) *
        (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ J,
          ENNReal.ofReal (projectedGradientSquare (D z))) ^ (1 / 2 : ℝ) := by
  have hD : AEStronglyMeasurable D
      ((volume.restrict (vec3Ball 0 1)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hsol.toData.aestronglyMeasurable_gradient hbox
  have hs := (slice_memLp_ae_of_sws hsol hbox).mono fun _ ht ↦ ht.2
  have hsource := unitBallViscousPressureCurve_eLpNorm_two_le_gradient_moment hD hs
  rw [lintegral_spatial_two_sq_eq (hsol.toData.aestronglyMeasurable_gradient hbox)] at hsource
  have hm : (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ J, ‖D z‖ₑ ^ (2 : ℝ)) ≤
      ∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ J,
        ENNReal.ofReal (projectedGradientSquare (D z)) :=
    lintegral_mono fun z ↦ gradient_enorm_square_le_coordinate (D z)
  calc
    _ ≤ fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal r ^ (5 / 2 : ℝ) *
        eLpNorm (unitBallViscousPressureCurve D) 2 (volume.restrict J) :=
      suitable_unitBallViscousOscillationTwoMoment_le_pressure_time_two hsol hbox hr hrρ hρone
    _ ≤ fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal r ^ (5 / 2 : ℝ) *
        (12 * (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ J,
          ENNReal.ofReal (projectedGradientSquare (D z))) ^ (1 / 2 : ℝ)) := by
      exact mul_le_mul' le_rfl (hsource.trans (mul_le_mul' le_rfl
        (ENNReal.rpow_le_rpow hm (by norm_num))))
    _ = _ := by ring

/-- A smaller actual time window preserves the same harmonic radius gain. -/
theorem suitable_unitBallViscousOscillationTwoMoment_subset_le_coordinate_energy
    {Ω : Set Vec3} {I J J' : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) (hJ : J' ⊆ J)
    {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hρone : ρ < 1) :
    unitBallViscousOscillationTwoMoment D r J' ≤
      12 * fullBallHarmonicOscillationConstant ρ * ENNReal.ofReal r ^ (5 / 2 : ℝ) *
        (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ J,
          ENNReal.ofReal (projectedGradientSquare (D z))) ^ (1 / 2 : ℝ) := by
  apply (show unitBallViscousOscillationTwoMoment D r J' ≤
    unitBallViscousOscillationTwoMoment D r J from
      ENNReal.rpow_le_rpow (lintegral_mono_set hJ) (by norm_num)).trans
  exact suitable_unitBallViscousOscillationTwoMoment_le_coordinate_energy
    hsol hbox hr hrρ hρone

end FluidSingularSets
