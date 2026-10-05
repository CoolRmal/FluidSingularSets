-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallHarmonicValues
public import FluidSingularSets.FullBallProjectedWeakGradient
public import FluidSingularSets.FullBallProjectedData
public import FluidSingularSets.ProjectedHarmonicSourceBounds
public import FluidSingularSets.WeightedProjectedSobolev

/-!
# Actual projected energy controlled by the original endpoint mixed norm

On every compact interior radius, the true harmonic correction has a quantitative
bound by the actual full-ball velocity class. Spatial finite-volume Hölder then
bounds the corrected square integral by the original L²-time/L⁶-space moment.
The time interval is the original suitable local interval.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

local instance fullBallSixControlForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The actual harmonic correction coefficient with its genuine boundary margin. -/
def fullBallProjectedHarmonicVelocityConstant (ρ : ℝ) : ℝ :=
  fullBallHarmonicForceGradientCoefficient ((ρ + 1) / 2) *
    (3 * (stokesTestPoincareConstant (vec3Ball (0 : Vec3) 1)).toReal)

/-- Every strictly interior radius gives a nonnegative actual correction coefficient. -/
theorem fullBallProjectedHarmonicVelocityConstant_nonneg {ρ : ℝ} (hρone : ρ < 1) :
    0 ≤ fullBallProjectedHarmonicVelocityConstant ρ := by
  unfold fullBallProjectedHarmonicVelocityConstant
  exact mul_nonneg (fullBallHarmonicForceGradientCoefficient_nonneg (by linarith))
    (by positivity)

/-- The actual corrected spatial L² coefficient relative to the genuine full source. -/
def fullBallProjectedVelocitySliceCoefficient (ρ : ℝ) : ℝ≥0∞ :=
  1 + ENNReal.ofReal (fullBallProjectedHarmonicVelocityConstant ρ) *
    volume (vec3Ball (0 : Vec3) 1) ^ (1 / 2 : ℝ)

/-- The true corrected spatial coefficient is finite at every radius. -/
theorem fullBallProjectedVelocitySliceCoefficient_ne_top (ρ : ℝ) :
    fullBallProjectedVelocitySliceCoefficient ρ ≠ ⊤ := by
  unfold fullBallProjectedVelocitySliceCoefficient
  exact ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (volume_vec3Ball_lt_top (x := 0) (r := 1)).ne).ne⟩

/-- Original suitable momentum controls the full-ball correction on the original interval. -/
theorem fullBall_projected_harmonic_gradient_velocity_bound_ae
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ x : fullBallCompactInterior ρ,
      ‖fullBallProjectedHarmonicGradientAmbient u D p a b c (x.1, t)‖ ≤
        fullBallProjectedHarmonicVelocityConstant ρ * ‖unitBallVelocityCurve u t‖ := by
  let H := fullBallHarmonicGradientExtended (fullBallCompactInterior ρ)
    (fullBallCompactInterior_subset_unit hρ hρone)
    (show (ρ + 1) / 2 < 1 by linarith)
    (fullBallCompactInterior_subset hρ (show ρ < (ρ + 1) / 2 by linarith))
  filter_upwards [suitable_unitBall_velocityForce_ae_primitive_localBox hsol hbox hab hc]
    with t ht
  intro x
  change ‖H (-localBoxForcePrimitive u D p a b c t) x‖ ≤ _
  rw [← ht]
  have hb := fullBallHarmonicGradientExtended_norm_le (fullBallCompactInterior ρ)
    (fullBallCompactInterior_subset_unit hρ hρone)
    (show (ρ + 1) / 2 < 1 by linarith)
    (fullBallCompactInterior_subset hρ (show ρ < (ρ + 1) / 2 by linarith))
    (-unitBallVelocityForceCurve u t)
  rw [norm_neg] at hb
  exact ((H (-unitBallVelocityForceCurve u t)).norm_coe_le_norm x |>.trans hb).trans
    ((mul_le_mul_of_nonneg_left (unitBallVelocityForceCurve_norm_le_actual_class u t)
      (fullBallHarmonicForceGradientCoefficient_nonneg (by linarith))).trans_eq
        (by unfold fullBallProjectedHarmonicVelocityConstant; ring))

/-- The genuine corrected L² slices have an actual full-source bound at every inner radius. -/
theorem fullBallProjectedVelocityAmbient_slice_norm_le_source_ae
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      eLpNorm (fun x ↦ fullBallProjectedVelocityAmbient u D p a b c (x, t)) 2
        (volume.restrict B) ≤
        fullBallProjectedVelocitySliceCoefficient ρ * ‖unitBallVelocityCurve u t‖ₑ := by
  have hB1 := hBK.trans (fullBallCompactInterior_subset_unit hρ hρone)
  filter_upwards [slice_memLp_ae_of_sws hsol hbox,
    fullBall_projected_harmonic_gradient_velocity_bound_ae hsol hbox hab hc hρ hρone]
    with t hu hb
  have hmH := (fullBallProjectedHarmonicGradientAmbient_memLp_two u D p a b c hρ hρone t
    ).mono_measure (Measure.restrict_mono_set volume hBK)
  have hHbound : ∀ᵐ x ∂volume.restrict B,
      ‖fullBallProjectedHarmonicGradientAmbient u D p a b c (x, t)‖ ≤
        fullBallProjectedHarmonicVelocityConstant ρ * ‖unitBallVelocityCurve u t‖ := by
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    exact hb ⟨x, hBK hx⟩
  have hHnorm := eLpNorm_le_of_ae_bound (p := 2) hmH.aestronglyMeasurable hHbound
  simp only [ENNReal.toReal_ofNat, inv_eq_one_div, Measure.restrict_apply_univ,
    ENNReal.ofReal_mul (fullBallProjectedHarmonicVelocityConstant_nonneg hρone), ofReal_norm]
    at hHnorm
  have hU : eLpNorm (fun x ↦ u (x, t)) 2 (volume.restrict B) ≤
      ‖unitBallVelocityCurve u t‖ₑ := by
    rw [unitBallVelocityCurve, actualSliceLp_enorm u t hu.1]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hB1)
  have hH : eLpNorm (fun x ↦ fullBallProjectedHarmonicGradientAmbient u D p a b c (x, t)) 2
      (volume.restrict B) ≤
      ENNReal.ofReal (fullBallProjectedHarmonicVelocityConstant ρ) *
        volume (vec3Ball (0 : Vec3) 1) ^ (1 / 2 : ℝ) * ‖unitBallVelocityCurve u t‖ₑ := by
    apply hHnorm.trans
    calc
      _ = ENNReal.ofReal (fullBallProjectedHarmonicVelocityConstant ρ) *
          volume B ^ (1 / 2 : ℝ) * ‖unitBallVelocityCurve u t‖ₑ := by ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ eLpNorm (fun x ↦ u (x, t)) 2 (volume.restrict B) +
        eLpNorm (fun x ↦ fullBallProjectedHarmonicGradientAmbient u D p a b c (x, t)) 2
          (volume.restrict B) := eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ ≤ ‖unitBallVelocityCurve u t‖ₑ +
        ENNReal.ofReal (fullBallProjectedHarmonicVelocityConstant ρ) *
          volume (vec3Ball (0 : Vec3) 1) ^ (1 / 2 : ℝ) * ‖unitBallVelocityCurve u t‖ₑ :=
      add_le_add hU hH
    _ = _ := by unfold fullBallProjectedVelocitySliceCoefficient; ring

/-- Genuine full-ball finite-volume Hölder controls the actual source L² slice by L⁶. -/
theorem fullBall_velocityCurve_two_le_six_ae
    {Ω : Set Vec3} {I : Set ℝ} {q a b : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), ‖unitBallVelocityCurve u t‖ₑ ≤
      eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) *
        volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ) := by
  let : IsFiniteMeasure (volume.restrict (vec3Ball (0 : Vec3) 1)) :=
    isFiniteMeasure_restrict.mpr (volume_vec3Ball_lt_top (x := 0) (r := 1)).ne
  filter_upwards [slice_memLp_ae_of_sws hsol hbox] with t ht
  rw [unitBallVelocityCurve, actualSliceLp_enorm u t ht.1]
  have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 2) (q := 6)
    (by norm_num) ht.1.aestronglyMeasurable
  norm_num only [ENNReal.toReal_ofNat, Measure.restrict_apply_univ] at hh
  exact hh

/-- The actual unweighted projected L⁶ slice is controlled by the original full-ball source. -/
theorem fullBallProjectedVelocityAmbient_six_norm_le_source_ae
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      eLpNorm (fun x ↦ fullBallProjectedVelocityAmbient u D p a b c (x, t)) 6
        (volume.restrict B) ≤ fullBallProjectedVelocitySliceCoefficient ρ *
          eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) := by
  have hB1 := hBK.trans (fullBallCompactInterior_subset_unit hρ hρone)
  filter_upwards [fullBall_velocityCurve_two_le_six_ae hsol hbox,
    fullBall_projected_harmonic_gradient_velocity_bound_ae hsol hbox hab hc hρ hρone]
    with t hu hb
  have hmH := (fullBallProjectedHarmonicGradientAmbient_memLp_two u D p a b c hρ hρone t
    ).mono_measure (Measure.restrict_mono_set volume hBK)
  have hHbound : ∀ᵐ x ∂volume.restrict B,
      ‖fullBallProjectedHarmonicGradientAmbient u D p a b c (x, t)‖ ≤
        fullBallProjectedHarmonicVelocityConstant ρ * ‖unitBallVelocityCurve u t‖ := by
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    exact hb ⟨x, hBK hx⟩
  have hh := eLpNorm_le_of_ae_bound (p := 6) hmH.aestronglyMeasurable hHbound
  simp only [ENNReal.toReal_ofNat, inv_eq_one_div, Measure.restrict_apply_univ,
    ENNReal.ofReal_mul (fullBallProjectedHarmonicVelocityConstant_nonneg hρone), ofReal_norm]
    at hh
  have hH : eLpNorm (fun x ↦ fullBallProjectedHarmonicGradientAmbient u D p a b c (x, t)) 6
      (volume.restrict B) ≤ ENNReal.ofReal (fullBallProjectedHarmonicVelocityConstant ρ) *
        volume (vec3Ball (0 : Vec3) 1) ^ (1 / 2 : ℝ) *
          eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) := by
    apply hh.trans
    calc
      _ ≤ volume (vec3Ball (0 : Vec3) 1) ^ (1 / 6 : ℝ) *
          (ENNReal.ofReal (fullBallProjectedHarmonicVelocityConstant ρ) *
          (eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) *
            volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ))) :=
        mul_le_mul' (ENNReal.rpow_le_rpow (measure_mono hB1) (by norm_num))
          (mul_le_mul' le_rfl hu)
      _ = _ := by
        rw [show (1 / 2 : ℝ) = 1 / 3 + 1 / 6 by norm_num,
          ENNReal.rpow_add_of_nonneg (1 / 3 : ℝ) (1 / 6 : ℝ) (by norm_num) (by norm_num)]
        ring
  calc
    _ ≤ eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict B) +
        eLpNorm (fun x ↦ fullBallProjectedHarmonicGradientAmbient u D p a b c (x, t)) 6
          (volume.restrict B) := eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 6)
    _ ≤ eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) +
        ENNReal.ofReal (fullBallProjectedHarmonicVelocityConstant ρ) *
          volume (vec3Ball (0 : Vec3) 1) ^ (1 / 2 : ℝ) *
            eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) :=
      add_le_add (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hB1)) hH
    _ = _ := by unfold fullBallProjectedVelocitySliceCoefficient; ring

/-- The genuine projected endpoint mixed cost is bounded by the original endpoint moment. -/
theorem fullBallProjectedVelocityAmbient_six_square_moment_le
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ) :
    (∫⁻ t in Ioo a b, eLpNorm
      (fun x ↦ fullBallProjectedVelocityAmbient u D p a b c (x, t)) 6
      (volume.restrict B) ^ 2) ≤ fullBallProjectedVelocitySliceCoefficient ρ ^ 2 *
        ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2 := by
  have hp := fullBallProjectedVelocityAmbient_six_norm_le_source_ae
    hsol hbox hab hc hρ hρone hB hBK
  calc
    _ ≤ ∫⁻ t in Ioo a b, fullBallProjectedVelocitySliceCoefficient ρ ^ 2 *
        eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) ^ 2 := by
      apply lintegral_mono_ae
      filter_upwards [hp] with t ht
      simpa only [mul_pow] using pow_le_pow_left' ht 2
    _ = _ := lintegral_const_mul' _ _
      (ENNReal.pow_ne_top (fullBallProjectedVelocitySliceCoefficient_ne_top ρ))

/-- The true projected joint-square coefficient relative to the original endpoint moment. -/
def fullBallProjectedVelocitySquareCoefficient (ρ : ℝ) : ℝ≥0∞ :=
  fullBallProjectedVelocitySliceCoefficient ρ ^ 2 *
    volume (vec3Ball (0 : Vec3) 1) ^ (2 / 3 : ℝ)

/-- The actual projected joint-square coefficient is finite. -/
theorem fullBallProjectedVelocitySquareCoefficient_ne_top (ρ : ℝ) :
    fullBallProjectedVelocitySquareCoefficient ρ ≠ ⊤ := by
  exact ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (fullBallProjectedVelocitySliceCoefficient_ne_top ρ))
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (volume_vec3Ball_lt_top (x := 0) (r := 1)).ne).ne

/-- The actual projected square integral is controlled by the original L²/L⁶ moment. -/
theorem fullBallProjectedVelocityAmbient_joint_square_le_six_moment
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ) :
    (∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
      ‖fullBallProjectedVelocityAmbient u D p a b c z‖ₑ ^ (2 : ℝ)) ≤
        fullBallProjectedVelocitySquareCoefficient ρ *
          ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
            (volume.restrict (vec3Ball 0 1)) ^ 2 := by
  obtain ⟨hV, _hD⟩ :=
    fullBallProjectedVelocityAmbient_joint_memLp_two hsol hbox hab hc hρ hρone hBK
  have heq : (∫⁻ t in Ioo a b, eLpNorm
      (fun x ↦ fullBallProjectedVelocityAmbient u D p a b c (x, t)) 2
      (volume.restrict B) ^ 2) =
      ∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
        ‖fullBallProjectedVelocityAmbient u D p a b c z‖ₑ ^ (2 : ℝ) :=
    lintegral_spatial_two_sq_eq hV.aestronglyMeasurable
  rw [← heq]
  have hp := fullBallProjectedVelocityAmbient_slice_norm_le_source_ae
    hsol hbox hab hc hρ hρone hB hBK
  have hu := fullBall_velocityCurve_two_le_six_ae hsol hbox
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioo a b),
      eLpNorm (fun x ↦ fullBallProjectedVelocityAmbient u D p a b c (x, t)) 2
        (volume.restrict B) ^ 2 ≤ fullBallProjectedVelocitySquareCoefficient ρ *
          eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) ^ 2 := by
    filter_upwards [hp, hu] with t ht hut
    have hv := pow_le_pow_left' ht 2
    rw [mul_pow] at hv
    have hs := pow_le_pow_left' hut 2
    rw [mul_pow, ← ENNReal.rpow_natCast (volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ)) 2,
      ← ENNReal.rpow_mul] at hs
    norm_num only [show (1 / 3 : ℝ) * 2 = 2 / 3 by norm_num] at hs
    exact (hv.trans (mul_le_mul' le_rfl hs)).trans_eq
      (by unfold fullBallProjectedVelocitySquareCoefficient; ring)
  exact (lintegral_mono_ae hpoint).trans_eq
    (lintegral_const_mul' _ _ (fullBallProjectedVelocitySquareCoefficient_ne_top ρ))

/-- Actual full-ball projected weak gradients give weighted energy with the original source. -/
theorem fullBallProjectedVelocityAmbient_weighted_sobolev_le_source
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcompact : HasCompactSupport φ)
    (hs : tsupport φ ⊆ B) (hunit : tsupport φ ⊆ euclideanBall 0 1)
    (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 1 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L) :
    (∫⁻ t in Ioo a b, eLpNorm
      (fun x ↦ φ x ^ 3 • fullBallProjectedVelocityAmbient u D p a b c (x, t)) 6
        (volume.restrict B) ^ (2 : ℝ)) ≤ 2 * (3 * localSobolevConstant) ^ 2 *
          ((∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
              ‖φ z.1 ^ 3 • fullBallProjectedVelocityDerivativeAmbient u D p a b c z‖ₑ ^
                (2 : ℝ)) +
            1225 * ENNReal.ofReal L ^ 2 * fullBallProjectedVelocitySquareCoefficient ρ *
              ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
                (volume.restrict (vec3Ball 0 1)) ^ 2) := by
  obtain ⟨hV, hD⟩ :=
    fullBallProjectedVelocityAmbient_joint_memLp_two hsol hbox hab hc hρ hρone hBK
  have hslices := fullBallProjectedVelocityAmbient_weak_gradient_slices_ae
    u D p a b c hsol hbox hρ hρone hB hBK
  have hh := integrated_cutoff_cube_sobolev_quadratic_error hB
    hV.aestronglyMeasurable hD.aestronglyMeasurable hslices
    hφ hcompact hs hunit hb hL hgrad
  have hsource := fullBallProjectedVelocityAmbient_joint_square_le_six_moment
    hsol hbox hab hc hρ hρone hB hBK
  apply hh.trans
  apply mul_le_mul' le_rfl
  apply add_le_add le_rfl
  calc
    _ ≤ (1225 * ENNReal.ofReal L ^ 2) *
        (fullBallProjectedVelocitySquareCoefficient ρ *
          ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
            (volume.restrict (vec3Ball 0 1)) ^ 2) :=
      mul_le_mul' (le_refl (1225 * ENNReal.ofReal L ^ 2)) hsource
    _ = _ := by ring

end FluidSingularSets
