-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallProjectedPressureSource
public import CKN.Foundation.Parabolic.Doubling

/-!
# Actual original velocity quartic source for projected nonlinear pressure decay

The literal velocity is the projected field minus its true harmonic correction.
The former is controlled by actual projected energy and dissipation. The latter
is controlled by the genuine original endpoint velocity moment, with the spatial
volume factor retained. No pressure-decay or regularity criterion is assumed.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The literal original unit-cylinder squared endpoint mixed cost. -/
def fullBallOriginalEndpointSixSquareMoment (u : ParabolicPoint → Vec3) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (-1 : ℝ) 0, eLpNorm (fun x ↦ u (x, t)) 6
    (volume.restrict (vec3Ball 0 1)) ^ 2

/-- The actual fixed interior harmonic coefficient for original quartic pressure sources. -/
def fullBallHarmonicQuarticSourceCoefficient : ℝ≥0∞ :=
  ENNReal.ofReal (fullBallProjectedHarmonicVelocityConstant (1 / 2)) ^ 2 *
    volume (vec3Ball (0 : Vec3) 1) ^ (7 / 6 : ℝ)

theorem fullBallHarmonicQuarticSourceCoefficient_ne_top :
    fullBallHarmonicQuarticSourceCoefficient ≠ ∞ := by
  unfold fullBallHarmonicQuarticSourceCoefficient
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) volume_vec3Ball_lt_top.ne).ne

private theorem uniform_spatial_four_square_le
    {μ : Measure Vec3} {H : Vec3 → Vec3} {K : ℝ}
    (hH : AEStronglyMeasurable H μ) (hK : 0 ≤ K)
    (hb : ∀ᵐ x ∂μ, ‖H x‖ ≤ K) :
    eLpNorm H 4 μ ^ 2 ≤ ENNReal.ofReal K ^ 2 * (μ univ) ^ (1 / 2 : ℝ) := by
  have h : eLpNorm H 4 μ ≤ eLpNorm (fun _ : Vec3 ↦ K) 4 μ :=
    eLpNorm_mono_ae_real hH hb
  rw [eLpNorm_const' _ (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num),
    ENNReal.toReal_ofNat, Real.enorm_eq_ofReal hK] at h
  have hs := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul] at hs
  norm_num only [show (1 / 4 : ℝ) * 2 = 1 / 2 by norm_num] at hs
  simp only [ENNReal.rpow_ofNat] at hs
  exact hs

private theorem aemeasurable_spatial_four_square
    {B : Set Vec3} {J : Set ℝ} {H : ParabolicPoint → Vec3}
    (hH : AEStronglyMeasurable H (volume.restrict (B ×ˢ J))) :
    AEMeasurable (fun t ↦ eLpNorm (fun x ↦ H (x, t)) 4
      (volume.restrict B) ^ 2) (volume.restrict J) := by
  have hp : AEStronglyMeasurable H ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hH
  apply (((hp.enorm.pow_const (4 : ℝ)).lintegral_prod_left').pow_const (1 / 2 : ℝ)).congr
  filter_upwards [hp.prodMk_right] with t ht
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) ht]
  norm_num only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_ofNat, ← ENNReal.rpow_mul]
  norm_num

section Suitable

variable {Ω : Set Vec3} {I : Set ℝ} {q c r : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

private theorem nonlinear_source_time_subset (hr : 0 < r) (hrhalf : r < 1 / 2) :
    Ioo (-r ^ 2) 0 ⊆ Ioo (-1) 0 := by
  intro t ht
  have hh : r ^ 2 < 1 / 4 := by nlinarith
  exact ⟨by linarith [ht.1], ht.2⟩

/-- Actual suitable energy makes the literal original endpoint moment finite. -/
theorem suitable_fullBall_original_endpoint_six_square_moment_lt_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) :
    fullBallOriginalEndpointSixSquareMoment u < ⊤ := by
  simpa only [fullBallOriginalEndpointSixSquareMoment, ENNReal.rpow_ofNat] using
    suitable_fullBall_velocity_six_moment_lt_top hsol hbox

/-- Genuine suitable momentum bounds harmonic quartic slices by the original endpoint cost. -/
theorem suitable_fullBall_harmonic_four_square_source_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0))
    (hc : c ∈ Ioo (-1) 0) (_hr : 0 < r) (hrhalf : r < 1 / 2) :
    ∀ᵐ t ∂volume.restrict (Ioo (-1) 0),
      eLpNorm (fun x ↦ fullBallProjectedHarmonicGradientAmbient u D p (-1) 0 c (x, t)) 4
        (volume.restrict (vec3Ball 0 r)) ^ 2 ≤
      ENNReal.ofReal (fullBallProjectedHarmonicVelocityConstant (1 / 2)) ^ 2 *
        volume (vec3Ball 0 r) ^ (1 / 2 : ℝ) *
        volume (vec3Ball 0 1) ^ (2 / 3 : ℝ) *
        eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) ^ 2 := by
  have hBK : vec3Ball (0 : Vec3) r ⊆ fullBallCompactInterior (1 / 2) :=
    (vec3Ball_mono hrhalf.le).trans subset_closure
  have hj := (fullBallProjected_correction_ambient_joint_memLp_top
    (ρ := 1 / 2) hsol hbox (by norm_num) hc (by norm_num) (by norm_num)).1
  have hH : AEStronglyMeasurable
      (fullBallProjectedHarmonicGradientAmbient u D p (-1) 0 c)
      ((volume.restrict (vec3Ball 0 r)).prod (volume.restrict (Ioo (-1) 0))) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hj.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono (Set.prod_mono hBK Subset.rfl) le_rfl)
  have hC : 0 ≤ fullBallProjectedHarmonicVelocityConstant (1 / 2) :=
    fullBallProjectedHarmonicVelocityConstant_nonneg (by norm_num)
  filter_upwards [hH.prodMk_right,
    fullBall_projected_harmonic_gradient_velocity_bound_ae
      (ρ := 1 / 2) hsol hbox (by norm_num) hc (by norm_num) (by norm_num),
    fullBall_velocityCurve_two_le_six_ae hsol hbox] with t ht hb hu
  have hpoint : ∀ᵐ x ∂volume.restrict (vec3Ball 0 r),
      ‖fullBallProjectedHarmonicGradientAmbient u D p (-1) 0 c (x, t)‖ ≤
        fullBallProjectedHarmonicVelocityConstant (1 / 2) * ‖unitBallVelocityCurve u t‖ := by
    filter_upwards [ae_restrict_mem (isOpen_vec3Ball 0 r).measurableSet] with x hx
    exact hb ⟨x, hBK hx⟩
  have hs := uniform_spatial_four_square_le ht
    (mul_nonneg hC (norm_nonneg _)) hpoint
  rw [ENNReal.ofReal_mul hC, ofReal_norm, mul_pow] at hs
  have hu2 := ENNReal.rpow_le_rpow hu (by norm_num : (0 : ℝ) ≤ 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul] at hu2
  norm_num only [show (1 / 3 : ℝ) * 2 = 2 / 3 by norm_num] at hu2
  simp only [ENNReal.rpow_ofNat] at hu2
  simp only [Measure.restrict_apply_univ] at hs
  exact (hs.trans (mul_le_mul' (mul_le_mul' le_rfl hu2) le_rfl)).trans_eq (by ring)

/-- Actual harmonic quartic sources retain their parabolic spatial-volume gain. -/
theorem suitable_fullBall_harmonic_four_square_moment_source
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0))
    (hc : c ∈ Ioo (-1) 0) (hr : 0 < r) (hrhalf : r < 1 / 2) :
    (∫⁻ t in Ioo (-r ^ 2) 0, eLpNorm
      (fun x ↦ fullBallProjectedHarmonicGradientAmbient u D p (-1) 0 c (x, t)) 4
        (volume.restrict (vec3Ball 0 r)) ^ 2) ≤
      fullBallHarmonicQuarticSourceCoefficient * ENNReal.ofReal r ^ (3 / 2 : ℝ) *
        fullBallOriginalEndpointSixSquareMoment u := by
  let A := ENNReal.ofReal (fullBallProjectedHarmonicVelocityConstant (1 / 2)) ^ 2 *
    volume (vec3Ball (0 : Vec3) r) ^ (1 / 2 : ℝ) *
      volume (vec3Ball (0 : Vec3) 1) ^ (2 / 3 : ℝ)
  have hA : A ≠ ⊤ := by
    dsimp [A]
    finiteness [(volume_vec3Ball_lt_top (x := 0) (r := r)).ne,
      (volume_vec3Ball_lt_top (x := 0) (r := 1)).ne]
  have hJ := nonlinear_source_time_subset hr hrhalf
  have hp := (suitable_fullBall_harmonic_four_square_source_ae
    hsol hbox hc hr hrhalf).filter_mono (ae_mono (Measure.restrict_mono hJ le_rfl))
  have hv : volume (vec3Ball (0 : Vec3) r) =
      ENNReal.ofReal r ^ 3 * volume (vec3Ball (0 : Vec3) 1) := by
    simpa only [mul_one, ENNReal.ofReal_pow hr.le] using
      (volume_vec3Ball_scale (r := 1) hr)
  have hcoeff : A = fullBallHarmonicQuarticSourceCoefficient *
      ENNReal.ofReal r ^ (3 / 2 : ℝ) := by
    unfold A fullBallHarmonicQuarticSourceCoefficient
    rw [hv, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ← ENNReal.rpow_natCast_mul (ENNReal.ofReal r) 3 (1 / 2)]
    norm_num only [show (3 : ℝ) * (1 / 2) = 3 / 2 by norm_num]
    rw [show (volume (vec3Ball (0 : Vec3) 1)) ^ (7 / 6 : ℝ) =
        (volume (vec3Ball (0 : Vec3) 1)) ^ (1 / 2 : ℝ) *
          (volume (vec3Ball (0 : Vec3) 1)) ^ (2 / 3 : ℝ) by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num]
    ring
  calc
    _ ≤ ∫⁻ t in Ioo (-r ^ 2) 0, A *
        eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) ^ 2 :=
      lintegral_mono_ae hp
    _ = A * ∫⁻ t in Ioo (-r ^ 2) 0,
        eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) ^ 2 :=
      lintegral_const_mul' _ _ hA
    _ ≤ A * fullBallOriginalEndpointSixSquareMoment u :=
      mul_le_mul' le_rfl (lintegral_mono_set hJ)
    _ = _ := by rw [hcoeff]

/-- The original velocity splits literally into its projected field and harmonic correction. -/
theorem fullBall_original_four_square_le_projected_harmonic
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c r t : ℝ) :
    eLpNorm (fun x ↦ u (x, t)) 4 (volume.restrict (vec3Ball 0 r)) ^ 2 ≤
      2 * (eLpNorm (fun x ↦ fullBallProjectedVelocityAmbient u D p a b c (x, t)) 4
          (volume.restrict (vec3Ball 0 r)) ^ 2 +
        eLpNorm (fun x ↦ fullBallProjectedHarmonicGradientAmbient u D p a b c (x, t)) 4
          (volume.restrict (vec3Ball 0 r)) ^ 2) := by
  have hid : (fun x ↦ u (x, t)) =
      (fun x ↦ fullBallProjectedVelocityAmbient u D p a b c (x, t)) -
        (fun x ↦ fullBallProjectedHarmonicGradientAmbient u D p a b c (x, t)) := by
    funext x
    simp only [Pi.sub_apply, fullBallProjectedVelocityAmbient, add_sub_cancel_right]
  have h := eLpNorm_sub_le
    (f := fun x ↦ fullBallProjectedVelocityAmbient u D p a b c (x, t))
    (g := fun x ↦ fullBallProjectedHarmonicGradientAmbient u D p a b c (x, t))
    (by norm_num : (1 : ℝ≥0∞) ≤ 4) (μ := volume.restrict (vec3Ball 0 r))
  rw [← hid] at h
  have hs := pow_le_pow_left' h 2
  have ha := ENNReal.rpow_add_le_mul_rpow_add_rpow
    (eLpNorm (fun x ↦ fullBallProjectedVelocityAmbient u D p a b c (x, t)) 4
      (volume.restrict (vec3Ball 0 r)))
    (eLpNorm (fun x ↦ fullBallProjectedHarmonicGradientAmbient u D p a b c (x, t)) 4
      (volume.restrict (vec3Ball 0 r))) (by norm_num : (1 : ℝ) ≤ 2)
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.rpow_ofNat] at ha
  exact hs.trans ha

/-- Actual original quartic pressure sources use projected energy and original endpoint cost. -/
theorem suitable_fullBall_original_four_square_moment_le_projected_energy_source
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0))
    (hc : c ∈ Ioo (-1) 0) (hr : 0 < r) (hrhalf : r < 1 / 2) :
    unitBallVelocityFourSquareMoment u r (Ioo (-r ^ 2) 0) ≤
      2 * ENNReal.ofReal r ^ (3 / 2 : ℝ) *
        (ballH1ParabolicInterpolationConstant *
            fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c r 0 +
          fullBallHarmonicQuarticSourceCoefficient *
            fullBallOriginalEndpointSixSquareMoment u) := by
  have hBK : vec3Ball (0 : Vec3) r ⊆ fullBallCompactInterior (1 / 2) :=
    (vec3Ball_mono hrhalf.le).trans subset_closure
  have hHj := (fullBallProjected_correction_ambient_joint_memLp_top
    (ρ := 1 / 2) hsol hbox (by norm_num) hc (by norm_num) (by norm_num)).1
  have hm := aemeasurable_spatial_four_square
    (hHj.aestronglyMeasurable.mono_measure (Measure.restrict_mono
      (Set.prod_mono hBK (nonlinear_source_time_subset hr hrhalf)) le_rfl))

  calc
    _ ≤ ∫⁻ t in Ioo (-r ^ 2) 0, 2 *
        (eLpNorm (fun x ↦ fullBallProjectedVelocityAmbient u D p (-1) 0 c (x, t)) 4
            (volume.restrict (vec3Ball 0 r)) ^ 2 +
          eLpNorm (fun x ↦ fullBallProjectedHarmonicGradientAmbient u D p (-1) 0 c (x, t)) 4
            (volume.restrict (vec3Ball 0 r)) ^ 2) :=
      lintegral_mono fun t ↦ fullBall_original_four_square_le_projected_harmonic
        u D p (-1) 0 c r t
    _ ≤ 2 * ((∫⁻ t in Ioo (-r ^ 2) 0, eLpNorm
          (fun x ↦ fullBallProjectedVelocityAmbient u D p (-1) 0 c (x, t)) 4
            (volume.restrict (vec3Ball 0 r)) ^ 2) +
        ∫⁻ t in Ioo (-r ^ 2) 0, eLpNorm
          (fun x ↦ fullBallProjectedHarmonicGradientAmbient u D p (-1) 0 c (x, t)) 4
            (volume.restrict (vec3Ball 0 r)) ^ 2) := by
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_right' _ hm]
    _ ≤ _ := (mul_le_mul' le_rfl (add_le_add
      (suitable_fullBall_projected_iteration_four_square_le_normalized_energy
        hsol hbox hc hr hrhalf)
      (suitable_fullBall_harmonic_four_square_moment_source hsol hbox hc hr hrhalf))).trans_eq
        (by ring)

end Suitable

end FluidSingularSets
