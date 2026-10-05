-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.SuitableProjectedWeakGradient
public import FluidSingularSets.ProjectedHarmonicSourceBounds

/-!
# Genuine projected velocity slice energy

The actual harmonic correction is bounded by the original velocity's spatial
L² class. This gives an explicit uniform bound for the corrected slice energy,
and hence its genuine spatial L² class belongs to time L∞ from suitable S1 data.
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

local instance projectedVelocityEnergySpaceSecondCountable : SecondCountableTopology Vec3 :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → ℝ))

/-- The explicit correction factor relative to the original full-ball L² slice. -/
def projectedVelocitySliceCoefficient : ℝ≥0∞ :=
  1 + ENNReal.ofReal projectedHarmonicGradientVelocityConstant *
    volume unitBallPressureCompactInterior ^ (1 / 2 : ℝ)

/-- The actual source-bound coefficient is finite. -/
theorem projectedVelocitySliceCoefficient_ne_top : projectedVelocitySliceCoefficient ≠ ∞ := by
  have hv : volume unitBallPressureCompactInterior < ∞ :=
    (isCompact_closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 16)).measure_lt_top
  exact ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hv.ne).ne⟩

/-- The genuine conditional corrected velocity spatial class on an actual inner set. -/
def suitableProjectedVelocityCurve
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t₀ : ℝ) (B : Set Vec3) (t : ℝ) :
    Lp Vec3 2 (volume.restrict B) :=
  actualSliceLp (μ := volume.restrict B) (p := 2)
    (suitableProjectedVelocityAmbient u D p t₀) t

variable {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

/-- On one common full time set, the actual projected spatial norm has a true source bound. -/
theorem suitableProjectedVelocityAmbient_slice_norm_le_source_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior) :
    ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      eLpNorm (fun x ↦ suitableProjectedVelocityAmbient u D p t₀ (x, t)) 2
        (volume.restrict B) ≤
        projectedVelocitySliceCoefficient * ‖unitBallVelocityCurve u t‖ₑ := by
  have hB1 : B ⊆ vec3Ball 0 1 := fun x hx ↦
    vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1)
      (unitBallPressureCompactInterior_subset_eighth (hBK hx))
  have hbox := suitableProjected_unitBall_localBox hdom
  filter_upwards [slice_memLp_ae_of_sws hsol hbox,
    suitable_projected_harmonic_gradient_velocity_bound_ae hsol hdom] with t hu hb
  have hmH := (suitableProjectedHarmonicGradientAmbient_memLp_two u D p t₀ t).mono_measure
    (Measure.restrict_mono_set volume hBK)
  have hHbound : ∀ᵐ x ∂volume.restrict B,
      ‖suitableProjectedHarmonicGradientAmbient u D p t₀ (x, t)‖ ≤
        projectedHarmonicGradientVelocityConstant * ‖unitBallVelocityCurve u t‖ := by
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    rw [suitableProjectedHarmonicGradientAmbient_eq_compact u D p t₀ ⟨x, hBK hx⟩ t]
    exact hb ⟨x, hBK hx⟩
  have hHnorm := eLpNorm_le_of_ae_bound (p := 2) hmH.aestronglyMeasurable hHbound
  simp only [ENNReal.toReal_ofNat, inv_eq_one_div, Measure.restrict_apply_univ,
    ENNReal.ofReal_mul projectedHarmonicGradientVelocityConstant_nonneg, ofReal_norm] at hHnorm
  have hU : eLpNorm (fun x ↦ u (x, t)) 2 (volume.restrict B) ≤
      ‖unitBallVelocityCurve u t‖ₑ := by
    rw [unitBallVelocityCurve, actualSliceLp_enorm u t hu.1]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hB1)
  have hH : eLpNorm (fun x ↦ suitableProjectedHarmonicGradientAmbient u D p t₀ (x, t)) 2
      (volume.restrict B) ≤
      ENNReal.ofReal projectedHarmonicGradientVelocityConstant *
        volume unitBallPressureCompactInterior ^ (1 / 2 : ℝ) *
          ‖unitBallVelocityCurve u t‖ₑ := by
    apply hHnorm.trans
    calc
      _ = ENNReal.ofReal projectedHarmonicGradientVelocityConstant *
          volume B ^ (1 / 2 : ℝ) * ‖unitBallVelocityCurve u t‖ₑ := by ring
      _ ≤ _ := by
        gcongr
  have hsum := eLpNorm_add_le (f := fun x ↦ u (x, t))
    (g := fun x ↦ suitableProjectedHarmonicGradientAmbient u D p t₀ (x, t))
    (μ := volume.restrict B) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  calc
    _ ≤ eLpNorm (fun x ↦ u (x, t)) 2 (volume.restrict B) +
        eLpNorm (fun x ↦ suitableProjectedHarmonicGradientAmbient u D p t₀ (x, t)) 2
          (volume.restrict B) := hsum
    _ ≤ ‖unitBallVelocityCurve u t‖ₑ +
        ENNReal.ofReal projectedHarmonicGradientVelocityConstant *
          volume unitBallPressureCompactInterior ^ (1 / 2 : ℝ) *
            ‖unitBallVelocityCurve u t‖ₑ := add_le_add hU hH
    _ = _ := by unfold projectedVelocitySliceCoefficient; ring

/-- The true projected spatial class curve is genuinely strongly measurable in time. -/
theorem suitableProjectedVelocityCurve_aestronglyMeasurable
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {B : Set Vec3} (hBK : B ⊆ unitBallPressureCompactInterior) :
    AEStronglyMeasurable (suitableProjectedVelocityCurve u D p t₀ B)
      (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) := by
  have hprod : AEStronglyMeasurable (suitableProjectedVelocityAmbient u D p t₀)
      ((volume.restrict B).prod (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    have hm := (suitableProjectedVelocityAmbient_joint_memLp_two u D p t₀ hsol hdom hBK).1
    exact hm.aestronglyMeasurable
  exact aestronglyMeasurable_actualSliceLp hprod (by norm_num)

/-- The actual projected spatial class has an explicit uniform time norm bound by source S1. -/
theorem suitableProjectedVelocityCurve_eLpNorm_top_le_source_energy
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior) :
    eLpNorm (suitableProjectedVelocityCurve u D p t₀ B) ⊤
        (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ≤
      projectedVelocitySliceCoefficient *
        (essSup (fun t ↦ ∫⁻ x in vec3Ball 0 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
          (volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_exponent_top
    (suitableProjectedVelocityCurve_aestronglyMeasurable hsol hdom hBK)]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  filter_upwards [suitableProjectedVelocityAmbient_slice_norm_le_source_ae hsol hdom hB hBK,
    ENNReal.ae_le_essSup (μ := volume.restrict (Ioo (t₀ - 4) (t₀ + 4)))
      (fun t ↦ ∫⁻ x in vec3Ball 0 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))] with t hv ht
  have hclass : ‖unitBallVelocityCurve u t‖ₑ ≤
      (∫⁻ x in vec3Ball 0 1, ‖u (x, t)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    actualSliceLp_enorm_two_le_sliceEnergy u t
  exact ((actualSliceLp_enorm_le (μ := volume.restrict B) (p := 2)
    (suitableProjectedVelocityAmbient u D p t₀) t).trans hv).trans
    (mul_le_mul' (le_refl _) (hclass.trans (ENNReal.rpow_le_rpow ht (by norm_num))))

/-- Actual suitable S1 gives the genuine projected spatial L² class in time L∞. -/
theorem suitableProjectedVelocityCurve_memLp_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior) :
    MemLp (suitableProjectedVelocityCurve u D p t₀ B) ⊤
      (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) := by
  have hE := hsol.toData.essSup_sliceEnergy_lt_top (suitableProjected_unitBall_localBox hdom)
  exact (suitableProjectedVelocityCurve_eLpNorm_top_le_source_energy hsol hdom hB hBK).trans_lt
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr projectedVelocitySliceCoefficient_ne_top)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hE.ne))

/-- The genuine corrected slice energy has the explicit squared source coefficient. -/
theorem suitableProjectedVelocityAmbient_slice_energy_le_source_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior) :
    ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      (∫⁻ x in B, ‖suitableProjectedVelocityAmbient u D p t₀ (x, t)‖ₑ ^ (2 : ℝ)) ≤
        projectedVelocitySliceCoefficient ^ 2 *
          ∫⁻ x in vec3Ball 0 1, ‖u (x, t)‖ₑ ^ (2 : ℝ) := by
  filter_upwards [suitableProjectedVelocityAmbient_slice_norm_le_source_ae hsol hdom hB hBK,
    suitableProjectedVelocityAmbient_weak_gradient_slices_ae u D p t₀ hsol hdom hB hBK,
    slice_memLp_ae_of_sws hsol (suitableProjected_unitBall_localBox hdom)] with t hb hv hu
  have hVEq := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    hv.1.aestronglyMeasurable
  have hUEq := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    hu.1.aestronglyMeasurable
  norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at hVEq hUEq
  have hs : ‖unitBallVelocityCurve u t‖ₑ ^ 2 =
      ∫⁻ x in vec3Ball 0 1, ‖u (x, t)‖ₑ ^ (2 : ℝ) := by
    rw [unitBallVelocityCurve, actualSliceLp_enorm u t hu.1]
    simpa only [ENNReal.rpow_ofNat] using hUEq
  have hsq := pow_le_pow_left' hb 2
  rw [mul_pow, hVEq, hs] at hsq
  simpa only [ENNReal.rpow_ofNat] using hsq

/-- The actual corrected energy supremum is bounded by the original full-ball S1 supremum. -/
theorem suitableProjectedVelocityAmbient_essSup_energy_le_source
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior) :
    essSup (fun t ↦ ∫⁻ x in B,
      ‖suitableProjectedVelocityAmbient u D p t₀ (x, t)‖ₑ ^ (2 : ℝ))
        (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ≤
      projectedVelocitySliceCoefficient ^ 2 *
        essSup (fun t ↦ ∫⁻ x in vec3Ball 0 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
          (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) :=
  (essSup_mono_ae (suitableProjectedVelocityAmbient_slice_energy_le_source_ae
    hsol hdom hB hBK)).trans_eq ENNReal.essSup_const_mul

/-- The literal corrected slice energy supremum is genuinely finite from suitable S1. -/
theorem suitableProjectedVelocityAmbient_essSup_energy_lt_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior) :
    essSup (fun t ↦ ∫⁻ x in B,
      ‖suitableProjectedVelocityAmbient u D p t₀ (x, t)‖ₑ ^ (2 : ℝ))
        (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) < ∞ := by
  apply (suitableProjectedVelocityAmbient_essSup_energy_le_source hsol hdom hB hBK).trans_lt
  exact ENNReal.mul_lt_top (by finiteness [projectedVelocitySliceCoefficient_ne_top])
    (hsol.toData.essSup_sliceEnergy_lt_top (suitableProjected_unitBall_localBox hdom))

/-- The genuine corrected spatial class represents the actual velocity on good time slices. -/
theorem suitableProjectedVelocityCurve_ae_actual
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ unitBallPressureCompactInterior) :
    ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      (suitableProjectedVelocityCurve u D p t₀ B t : Vec3 → Vec3) =ᵐ[volume.restrict B]
        (fun x ↦ suitableProjectedVelocityAmbient u D p t₀ (x, t)) := by
  filter_upwards [suitableProjectedVelocityAmbient_weak_gradient_slices_ae
    u D p t₀ hsol hdom hB hBK] with t ht
  exact actualSliceLp_ae (suitableProjectedVelocityAmbient u D p t₀) t ht.1

end FluidSingularSets
