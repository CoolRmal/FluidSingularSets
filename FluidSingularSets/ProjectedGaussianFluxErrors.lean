-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedGaussianHeatError
public import FluidSingularSets.FullBallHarmonicCutoffErrors

/-!
# Genuine Gaussian convection and harmonic source moments

Tonelli, the actual projected slice energy and spatial Hölder control the
quadratic and linear moments of the full-ball velocity source. Gaussian tests
then bound the literal convection and Hessian errors without a regularity premise.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

section Moments

variable {A T E : Type*} [MeasurableSpace A] [MeasurableSpace T]
  [NormedAddCommGroup E] {μ : Measure A} [SFinite μ] {ν : Measure T} [SFinite ν]
  {V : A × T → Vec3} {S : T → E} {M : ℝ≥0∞}

/-- A genuine time source weights the square mass by its true essential supremum. -/
theorem lintegral_source_mul_euclidean_square_le
    (hV : AEStronglyMeasurable V (μ.prod ν)) (hS : AEStronglyMeasurable S ν)
    (hM : ∀ᵐ t ∂ν, (∫⁻ x, ENNReal.ofReal (vec3EuclideanNorm (V (x, t)) ^ 2) ∂μ) ≤ M) :
    (∫⁻ z, ‖S z.2‖ₑ * ENNReal.ofReal (vec3EuclideanNorm (V z) ^ 2) ∂μ.prod ν) ≤
      M * ν univ ^ (1 / 2 : ℝ) * eLpNorm S 2 ν := by
  have hN := ((CKN.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hV).pow 2)
  have hU := ENNReal.continuous_ofReal.comp_aestronglyMeasurable hN
  have hA : AEMeasurable (fun z ↦ ‖S z.2‖ₑ *
      ENNReal.ofReal (vec3EuclideanNorm (V z) ^ 2)) (μ.prod ν) :=
    hS.enorm.comp_snd.mul hU.aemeasurable
  have hp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
    (by norm_num) hS
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, one_div_one,
    show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num] at hp
  calc
    _ = ∫⁻ t, ‖S t‖ₑ * (∫⁻ x, ENNReal.ofReal
        (vec3EuclideanNorm (V (x, t)) ^ 2) ∂μ) ∂ν := by
      rw [lintegral_prod_symm _ hA]
      apply lintegral_congr
      intro t
      exact lintegral_const_mul' (‖S t‖ₑ) _ (by simp)
    _ ≤ ∫⁻ t, ‖S t‖ₑ * M ∂ν :=
      lintegral_mono_ae (hM.mono fun t ht ↦ mul_le_mul' le_rfl ht)
    _ = M * ∫⁻ t, ‖S t‖ₑ ∂ν := by
      simp_rw [mul_comm _ M]
      exact lintegral_const_mul'' _ hS.enorm
    _ ≤ M * (eLpNorm S 2 ν * ν univ ^ (1 / 2 : ℝ)) :=
      mul_le_mul' le_rfl (lintegral_enorm_le_eLpNorm_one.trans hp)
    _ = _ := by ring

/-- A genuine squared time source weights the linear mass by finite-volume Hölder. -/
theorem lintegral_source_square_mul_euclidean_le
    (hV : AEStronglyMeasurable V (μ.prod ν)) (hS : AEStronglyMeasurable S ν)
    (hM : ∀ᵐ t ∂ν, (∫⁻ x, ENNReal.ofReal (vec3EuclideanNorm (V (x, t)) ^ 2) ∂μ) ≤ M) :
    (∫⁻ z, ‖S z.2‖ₑ ^ 2 * ENNReal.ofReal (vec3EuclideanNorm (V z)) ∂μ.prod ν) ≤
      μ univ ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) * eLpNorm S 2 ν ^ 2 := by
  have hN := CKN.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hV
  have hU := ENNReal.continuous_ofReal.comp_aestronglyMeasurable hN
  have hA : AEMeasurable (fun z ↦ ‖S z.2‖ₑ ^ 2 *
      ENNReal.ofReal (vec3EuclideanNorm (V z))) (μ.prod ν) :=
    (hS.enorm.pow_const 2).comp_snd.mul hU.aemeasurable
  have hL : ∀ᵐ t ∂ν, (∫⁻ x, ENNReal.ofReal (vec3EuclideanNorm (V (x, t))) ∂μ) ≤
      μ univ ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) := by
    filter_upwards [hN.prodMk_right, hM] with t hnt hmt
    have hp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
      (by norm_num) hnt
    norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, one_div_one,
      show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num] at hp
    rw [eLpNorm_one_eq_lintegral_enorm hnt,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hnt] at hp
    simp_rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _),
      ENNReal.toReal_ofNat, ENNReal.rpow_ofNat,
      ← ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _)] at hp
    exact hp.trans ((mul_le_mul'
      (ENNReal.rpow_le_rpow hmt (by norm_num)) le_rfl).trans_eq (mul_comm _ _))
  have hsq : (∫⁻ t, ‖S t‖ₑ ^ 2 ∂ν) = eLpNorm S 2 ν ^ 2 := by
    simpa only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] using
      (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hS).symm
  calc
    _ = ∫⁻ t, ‖S t‖ₑ ^ 2 * (∫⁻ x,
        ENNReal.ofReal (vec3EuclideanNorm (V (x, t))) ∂μ) ∂ν := by
      rw [lintegral_prod_symm _ hA]
      apply lintegral_congr
      intro t
      exact lintegral_const_mul' (‖S t‖ₑ ^ 2) _ (by simp)
    _ ≤ ∫⁻ t, ‖S t‖ₑ ^ 2 * (μ univ ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ)) ∂ν :=
      lintegral_mono_ae (hL.mono fun t ht ↦ mul_le_mul' le_rfl ht)
    _ = _ := by
      simp_rw [mul_comm _ (μ univ ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ))]
      rw [lintegral_const_mul'' _ (hS.enorm.pow_const 2), hsq]

end Moments

section Suitable

variable {Ω : Set Vec3} {I : Set ℝ} {q c ρ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

/-- The literal full-ball velocity source weighted by the true projected square mass. -/
def fullBallProjectedIterationSourceSquareMoment
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c r τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (τ - r ^ 2) τ,
    ‖unitBallVelocityCurve u z.2‖ₑ *
      ENNReal.ofReal (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z) ^ 2)

/-- The literal squared full-ball velocity source weighted by the true projected linear mass. -/
def fullBallProjectedIterationSourceLinearMoment
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c r τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (τ - r ^ 2) τ,
    ‖unitBallVelocityCurve u z.2‖ₑ ^ 2 *
      ENNReal.ofReal (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z))

private theorem gaussianFlux_time_subset (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    Ioo (-ρ ^ 2) 0 ⊆ Ioo (-1) 0 := by
  intro t ht
  have hsq : ρ ^ 2 < 1 / 4 := by nlinarith
  exact ⟨by linarith only [ht.1, hsq], ht.2⟩

private theorem gaussianFlux_projected_measurable
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    AEStronglyMeasurable (fullBallProjectedVelocityAmbient u D p (-1) 0 c)
      ((volume.restrict (vec3Ball 0 ρ)).prod (volume.restrict (Ioo (-ρ ^ 2) 0))) := by
  rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
  have hi := (fullBallProjectedVelocityAmbient_joint_memLp_two
    (B := vec3Ball 0 ρ) hsol hbox (by norm_num) hc hρ (by linarith) subset_closure).1
  exact hi.aestronglyMeasurable.mono_measure (Measure.restrict_mono_set volume
        (Set.prod_mono Subset.rfl (gaussianFlux_time_subset hρ hρhalf)))

/-- Genuine suitable source data give the exact source-times-square moment bound. -/
theorem suitable_fullBall_projected_iteration_source_square_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    fullBallProjectedIterationSourceSquareMoment u D p (-1) 0 c ρ 0 ≤
      ENNReal.ofReal ρ * fullBallProjectedIterationSliceEnergy u D p (-1) 0 c ρ 0 *
        eLpNorm (unitBallVelocityCurve u) 2 (volume.restrict (Ioo (-ρ ^ 2) 0)) := by
  have hS0 := (suitable_velocityCurve_memLp_localBox hsol hbox).aestronglyMeasurable
  have hS := hS0.mono_measure
    (Measure.restrict_mono_set volume (gaussianFlux_time_subset hρ hρhalf))
  have hh := lintegral_source_mul_euclidean_square_le
    (gaussianFlux_projected_measurable hsol hbox hc hρ hρhalf) hS
    (by simpa only [zero_sub] using
      fullBallProjectedIteration_euclidean_square_le_sliceEnergy_ae u D p (-1) 0 c ρ 0)
  have ht : (volume.restrict (Ioo (-ρ ^ 2) 0)) univ ^ (1 / 2 : ℝ) =
      ENNReal.ofReal ρ := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
    simp only [zero_sub, neg_neg]
    rw [ENNReal.ofReal_pow hρ.le, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  unfold fullBallProjectedIterationSourceSquareMoment
  simp only [zero_sub]
  rw [show (volume : Measure ParabolicPoint).restrict
      (vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0) =
      (volume.restrict (vec3Ball 0 ρ)).prod (volume.restrict (Ioo (-ρ ^ 2) 0)) by
    rw [Measure.prod_restrict, volume_parabolicPoint_eq_prod]]
  exact hh.trans_eq (by rw [ht]; ring)

/-- Genuine suitable source data give the source-square-times-linear moment bound. -/
theorem suitable_fullBall_projected_iteration_source_linear_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    fullBallProjectedIterationSourceLinearMoment u D p (-1) 0 c ρ 0 ≤
      volume (vec3Ball (0 : Vec3) ρ) ^ (1 / 2 : ℝ) *
        fullBallProjectedIterationSliceEnergy u D p (-1) 0 c ρ 0 ^ (1 / 2 : ℝ) *
          eLpNorm (unitBallVelocityCurve u) 2 (volume.restrict (Ioo (-ρ ^ 2) 0)) ^ 2 := by
  have hS0 := (suitable_velocityCurve_memLp_localBox hsol hbox).aestronglyMeasurable
  have hS := hS0.mono_measure
    (Measure.restrict_mono_set volume (gaussianFlux_time_subset hρ hρhalf))
  have hh := lintegral_source_square_mul_euclidean_le
    (gaussianFlux_projected_measurable hsol hbox hc hρ hρhalf) hS
    (by simpa only [zero_sub] using
      fullBallProjectedIteration_euclidean_square_le_sliceEnergy_ae u D p (-1) 0 c ρ 0)
  unfold fullBallProjectedIterationSourceLinearMoment
  simp only [zero_sub]
  rw [show (volume : Measure ParabolicPoint).restrict
      (vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0) =
      (volume.restrict (vec3Ball 0 ρ)).prod (volume.restrict (Ioo (-ρ ^ 2) 0)) by
    rw [Measure.prod_restrict, volume_parabolicPoint_eq_prod]]
  exact hh.trans_eq (by rw [Measure.restrict_apply_univ])

/-- The true advecting velocity is controlled by the actual corrected velocity and correction. -/
theorem fullBallProjectedVelocityAmbient_original_norm_le
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (z : ParabolicPoint) :
    ‖u z‖ ≤ vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z) +
      ‖fullBallProjectedHarmonicGradientAmbient u D p a b c z‖ := by
  have he : u z - fullBallProjectedVelocityAmbient u D p a b c z =
      -fullBallProjectedHarmonicGradientAmbient u D p a b c z := by
    simp only [fullBallProjectedVelocityAmbient]
    abel
  calc
    _ ≤ ‖fullBallProjectedVelocityAmbient u D p a b c z‖ +
        ‖u z - fullBallProjectedVelocityAmbient u D p a b c z‖ := norm_le_insert' _ _
    _ = ‖fullBallProjectedVelocityAmbient u D p a b c z‖ +
        ‖fullBallProjectedHarmonicGradientAmbient u D p a b c z‖ := by rw [he, norm_neg]
    _ ≤ _ := add_le_add (norm_le_vec3EuclideanNorm
      (fullBallProjectedVelocityAmbient u D p a b c z)) le_rfl

/-- Genuine suitability on the original interval makes both literal Gaussian fluxes integrable. -/
theorem suitable_fullBall_projected_gaussian_flux_integrable
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    {r δ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hδ : 0 < δ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    Integrable (fullBallJointConvectionError u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ) volume ∧
    Integrable (fullBallJointHarmonicError u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ) volume := by
  obtain ⟨htest, hn, hs⟩ := projectedGaussianTest_admissible hr hρ hρhalf hδ
  have ht : projectedGaussianTest r ρ δ hρ ∈ spaceTimeTestFunction (V := ℝ) Ω I :=
    ⟨htest.1, htest.2.1, htest.2.2.trans
      (Set.prod_mono (subset_closure.trans hbox.2.2.1)
        (subset_closure.trans hbox.2.2.2.2.2))⟩
  have hf := suitable_fullBall_joint_errors_integrable hsol hbox (by norm_num) hc hρ
    (by linarith) ht hn hs hχ hbχ
  exact ⟨hf.2.1, hf.2.2.2⟩

/-- Actual harmonic source bounds split Gaussian convection into cubic and quadratic masses. -/
theorem suitable_fullBall_projected_gaussian_convection_pointwise_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    {r δ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r ≤ ρ)
    {χ : ℝ → ℝ} (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    ∀ᵐ t ∂volume.restrict (Ioo (-ρ ^ 2) 0), ∀ x ∈ vec3Ball 0 ρ,
      ‖fullBallJointConvectionError u D p (-1) 0 c
        (projectedGaussianTest r ρ δ hρ) χ (x, t)‖ ≤
      (3 * projectedGaussianGradientConstant / r ^ 2) *
        (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p (-1) 0 c (x, t)) ^ 3 +
          fullBallProjectedHarmonicVelocityConstant (1 / 2) * ‖unitBallVelocityCurve u t‖ *
            vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p (-1) 0 c (x, t)) ^ 2) := by
  have hH := fullBall_projected_harmonic_gradient_velocity_bound_ae
    hsol hbox (by norm_num) hc (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hHρ := hH.filter_mono
    (ae_mono (Measure.restrict_mono (gaussianFlux_time_subset hρ hρhalf) le_rfl))
  filter_upwards [hHρ, ae_restrict_mem measurableSet_Ioo] with t ht htt
  intro x hx
  have hχ := hbχ t
  let z : ParabolicPoint := (x, t)
  let V := vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p (-1) 0 c z)
  let S := ‖unitBallVelocityCurve u t‖
  let CH := fullBallProjectedHarmonicVelocityConstant (1 / 2)
  let CG := projectedGaussianGradientConstant / r ^ 2
  have hv : 0 ≤ V := vec3EuclideanNorm_nonneg _
  have hs : 0 ≤ S := norm_nonneg _
  have hch : 0 ≤ CH := fullBallProjectedHarmonicVelocityConstant_nonneg (by norm_num)
  have hcg : 0 ≤ CG := by
    dsimp [CG, projectedGaussianGradientConstant]
    have hC := CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
    positivity
  have hu : ‖u z‖ ≤ V + CH * S :=
    (fullBallProjectedVelocityAmbient_original_norm_le u D p (-1) 0 c z).trans
      (add_le_add le_rfl (ht ⟨x, subset_closure ((vec3Ball_mono hρhalf.le) hx)⟩))
  have hterm (j : Fin 3) : ‖u z j * spatialPartial
      (projectedGaussianTest r ρ δ hρ) j z‖ ≤ (V + CH * S) * CG := by
    rw [norm_mul]
    exact mul_le_mul ((norm_le_pi_norm _ j).trans hu)
      (by simpa only [Real.norm_eq_abs, z, CG] using
        projectedGaussianTest_spatialPartial_bound hr hρ hscale htt.2.le j)
      (norm_nonneg _) (by positivity)
  have hsum : ‖∑ j : Fin 3, u z j * spatialPartial
      (projectedGaussianTest r ρ δ hρ) j z‖ ≤ 3 * ((V + CH * S) * CG) :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ ↦ hterm j).trans_eq (by simp))
  calc
    _ = V ^ 2 * ‖∑ j : Fin 3, u z j * spatialPartial
        (projectedGaussianTest r ρ δ hρ) j z‖ * ‖χ t‖ := by
      simp only [fullBallJointConvectionError, z, V, norm_mul,
        Real.norm_of_nonneg (sq_nonneg _)]
    _ ≤ V ^ 2 * (3 * ((V + CH * S) * CG)) * 1 := by gcongr
    _ = _ := by dsimp [V, CH, S, CG, z]; ring

/-- Actual Hessian source bounds split the Gaussian harmonic error into two true source moments. -/
theorem suitable_fullBall_projected_gaussian_harmonic_pointwise_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    {r δ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hδ : 0 < δ)
    {χ : ℝ → ℝ} (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    ∀ᵐ t ∂volume.restrict (Ioo (-ρ ^ 2) 0), ∀ x ∈ vec3Ball 0 ρ,
      ‖fullBallJointHarmonicError u D p (-1) 0 c
        (projectedGaussianTest r ρ δ hρ) χ (x, t)‖ ≤
      (9000 * fullBallProjectedHarmonicHessianVelocityConstant (1 / 2) / r) *
        (‖unitBallVelocityCurve u t‖ *
          vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p (-1) 0 c (x, t)) ^ 2 +
        fullBallProjectedHarmonicVelocityConstant (1 / 2) * ‖unitBallVelocityCurve u t‖ ^ 2 *
          vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p (-1) 0 c (x, t))) := by
  have hH := fullBall_projected_harmonic_gradient_velocity_bound_ae
    hsol hbox (by norm_num) hc (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hDH := fullBall_projected_harmonic_hessian_velocity_bound_ae
    hsol hbox (by norm_num) hc (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hmeasure : volume.restrict (Ioo (-ρ ^ 2) 0) ≤ volume.restrict (Ioo (-1) 0) :=
    Measure.restrict_mono (gaussianFlux_time_subset hρ hρhalf) le_rfl
  filter_upwards [hH.filter_mono (ae_mono hmeasure), hDH.filter_mono (ae_mono hmeasure),
    ae_restrict_mem measurableSet_Ioo] with t ht hdt htt
  intro x hx
  have hχ := hbχ t
  let z : ParabolicPoint := (x, t)
  let V := vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p (-1) 0 c z)
  let S := ‖unitBallVelocityCurve u t‖
  let CH := fullBallProjectedHarmonicVelocityConstant (1 / 2)
  let CD := fullBallProjectedHarmonicHessianVelocityConstant (1 / 2)
  have hv : 0 ≤ V := vec3EuclideanNorm_nonneg _
  have hs : 0 ≤ S := norm_nonneg _
  have hch : 0 ≤ CH := fullBallProjectedHarmonicVelocityConstant_nonneg (by norm_num)
  have hcd : 0 ≤ CD := fullBallProjectedHarmonicHessianVelocityConstant_nonneg (by norm_num)
  have hK : x ∈ fullBallCompactInterior (1 / 2) :=
    subset_closure ((vec3Ball_mono hρhalf.le) hx)
  have hu : ‖u z‖ ≤ V + CH * S :=
    (fullBallProjectedVelocityAmbient_original_norm_le u D p (-1) 0 c z).trans
      (add_le_add le_rfl (ht ⟨x, hK⟩))
  have hterm (i j : Fin 3) : ‖u z j *
      fullBallProjectedHarmonicDerivativeAmbient u D p (-1) 0 c z i j *
        fullBallProjectedVelocityAmbient u D p (-1) 0 c z i‖ ≤
      (V + CH * S) * (CD * S) * V := by
    simp only [norm_mul]
    gcongr
    · exact (norm_le_pi_norm _ j).trans hu
    · exact hdt ⟨x, hK⟩ i j
    · exact (norm_le_pi_norm _ i).trans (norm_le_vec3EuclideanNorm _)
  have hsum : ‖∑ i : Fin 3, ∑ j : Fin 3, u z j *
      fullBallProjectedHarmonicDerivativeAmbient u D p (-1) 0 c z i j *
        fullBallProjectedVelocityAmbient u D p (-1) 0 c z i‖ ≤
      9 * ((V + CH * S) * (CD * S) * V) := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _i : Fin 3, 3 * ((V + CH * S) * (CD * S) * V) :=
        Finset.sum_le_sum fun i _ ↦ (norm_sum_le _ _).trans
          ((Finset.sum_le_sum fun j _ ↦ hterm i j).trans_eq (by simp))
      _ = _ := by simp; ring
  have hψ : ‖projectedGaussianTest r ρ δ hρ z‖ ≤ 1000 / r := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      ((projectedGaussianTest_admissible hr hρ hρhalf hδ).2.1 z)]
    exact projectedGaussianTest_upper hr hρ htt.2.le
  calc
    _ = ‖∑ i : Fin 3, ∑ j : Fin 3, u z j *
        fullBallProjectedHarmonicDerivativeAmbient u D p (-1) 0 c z i j *
        fullBallProjectedVelocityAmbient u D p (-1) 0 c z i‖ *
      ‖projectedGaussianTest r ρ δ hρ z‖ * ‖χ t‖ := by
        simp only [fullBallJointHarmonicError, z, norm_mul]
    _ ≤ (9 * ((V + CH * S) * (CD * S) * V)) * (1000 / r) * 1 := by gcongr
    _ = _ := by dsimp [V, CH, CD, S, z]; ring

private theorem gaussianFlux_ae_on_cylinder {P : ParabolicPoint → Prop}
    (hP : ∀ᵐ t ∂volume.restrict (Ioo (-ρ ^ 2) 0), ∀ x ∈ vec3Ball 0 ρ, P (x, t)) :
    ∀ᵐ z ∂(volume : Measure ParabolicPoint).restrict (vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0),
      P z := by
  rw [show (volume : Measure ParabolicPoint).restrict
      (vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0) =
      (volume.restrict (vec3Ball 0 ρ)).prod (volume.restrict (Ioo (-ρ ^ 2) 0)) by
    rw [Measure.prod_restrict, volume_parabolicPoint_eq_prod]]
  filter_upwards [(Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (vec3Ball 0 ρ))
      (ν := volume.restrict (Ioo (-ρ ^ 2) 0))).ae hP,
    (Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict (vec3Ball 0 ρ))
      (ν := volume.restrict (Ioo (-ρ ^ 2) 0))).ae
        (ae_restrict_mem (isOpen_vec3Ball 0 ρ).measurableSet)] with z ht hx
  exact ht z.1 hx

private theorem gaussianFlux_integral_bound {F : ParabolicPoint → ℝ}
    (hF : Integrable F volume)
    (hz : ∀ z, z ∉ vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0 → F z = 0) :
    ‖∫ z, F z‖ₑ ≤ ∫⁻ z in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0, ‖F z‖ₑ := by
  have he : (∫ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0, F z) =
      ∫ z : ParabolicPoint, F z := setIntegral_eq_integral_of_forall_compl_eq_zero hz
  calc
    _ = ‖∫ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0, F z‖ₑ :=
      congrArg (fun x : ℝ ↦ ‖x‖ₑ) he.symm
    _ = ENNReal.ofReal ‖∫ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0, F z‖ :=
      (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (∫ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0, ‖F z‖) :=
      ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm F)
    _ = _ := ofReal_integral_norm_eq_lintegral_enorm
      (hF.mono_measure Measure.restrict_le_self)

/-- The actual cubic and source-square moments bound the true global Gaussian convection. -/
theorem suitable_fullBall_projected_gaussian_convection_moment_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    {r δ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r ≤ ρ)
    (hδ : 0 < δ) {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    ‖∫ z : ParabolicPoint, fullBallJointConvectionError u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ z‖ₑ ≤
      ENNReal.ofReal (3 * projectedGaussianGradientConstant / r ^ 2) *
        ((∫⁻ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0, ENNReal.ofReal
          (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p (-1) 0 c z) ^ 3)) +
          ENNReal.ofReal (fullBallProjectedHarmonicVelocityConstant (1 / 2)) *
            fullBallProjectedIterationSourceSquareMoment u D p (-1) 0 c ρ 0) := by
  let V := fullBallProjectedVelocityAmbient u D p (-1) 0 c
  let F := fullBallJointConvectionError u D p (-1) 0 c
    (projectedGaussianTest r ρ δ hρ) χ
  let K := 3 * projectedGaussianGradientConstant / r ^ 2
  let CH := fullBallProjectedHarmonicVelocityConstant (1 / 2)
  have hK : 0 ≤ K := by
    dsimp [K, projectedGaussianGradientConstant]
    have hC := CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
    positivity
  have hCH : 0 ≤ CH := fullBallProjectedHarmonicVelocityConstant_nonneg (by norm_num)
  have hF := (suitable_fullBall_projected_gaussian_flux_integrable
    hsol hbox hc hr hρ hρhalf hδ hχ hbχ).1
  have hz : ∀ z : ParabolicPoint, z ∉ vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0 → F z = 0 := by
    intro z hn
    exact (fullBallJointEnergyErrors_zero_off_tsupport u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ (z.1, z.2)
        (fun hs ↦ hn (projectedGaussianTest_tsupport_cylinder hρ hδ hs))).2.1
  have hp0 := gaussianFlux_ae_on_cylinder (ρ := ρ)
    (P := fun z ↦ ‖F z‖ ≤ K * (vec3EuclideanNorm (V z) ^ 3 +
      CH * ‖unitBallVelocityCurve u z.2‖ * vec3EuclideanNorm (V z) ^ 2))
    (suitable_fullBall_projected_gaussian_convection_pointwise_bound
      (δ := δ) hsol hbox hc hr hρ hρhalf hscale hbχ)
  have hp : ∀ᵐ z ∂volume.restrict (vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0), ‖F z‖ₑ ≤
      ENNReal.ofReal K * (ENNReal.ofReal (vec3EuclideanNorm (V z) ^ 3) +
        ENNReal.ofReal CH * ‖unitBallVelocityCurve u z.2‖ₑ *
          ENNReal.ofReal (vec3EuclideanNorm (V z) ^ 2)) := by
    filter_upwards [hp0] with z hzp
    have hv : 0 ≤ vec3EuclideanNorm (V z) := vec3EuclideanNorm_nonneg _
    calc
      _ = ENNReal.ofReal ‖F z‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (K * (vec3EuclideanNorm (V z) ^ 3 +
          CH * ‖unitBallVelocityCurve u z.2‖ * vec3EuclideanNorm (V z) ^ 2)) :=
        ENNReal.ofReal_le_ofReal hzp
      _ = _ := by
        rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_add
          (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul hCH, ofReal_norm]
  have hV := gaussianFlux_projected_measurable hsol hbox hc hρ hρhalf
  have hVN : AEStronglyMeasurable V
      ((volume : Measure ParabolicPoint).restrict (vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0)) := by
    rw [volume_parabolicPoint_eq_prod, ← Measure.prod_restrict]
    exact hV
  have hQ3 : AEMeasurable (fun z : ParabolicPoint ↦
      ENNReal.ofReal (vec3EuclideanNorm (V z) ^ 3))
      (volume.restrict (vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0)) :=
    (ENNReal.continuous_ofReal.comp_aestronglyMeasurable
      ((CKN.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hVN).pow 3)).aemeasurable
  calc
    _ ≤ ∫⁻ z in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0, ‖F z‖ₑ :=
      gaussianFlux_integral_bound hF hz
    _ ≤ ∫⁻ z in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
        ENNReal.ofReal K * (ENNReal.ofReal (vec3EuclideanNorm (V z) ^ 3) +
          ENNReal.ofReal CH * ‖unitBallVelocityCurve u z.2‖ₑ *
            ENNReal.ofReal (vec3EuclideanNorm (V z) ^ 2)) := lintegral_mono_ae hp
    _ = _ := by
      have he : (∫⁻ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
          ENNReal.ofReal CH * ‖unitBallVelocityCurve u z.2‖ₑ *
            ENNReal.ofReal (vec3EuclideanNorm (V z) ^ 2)) =
          ENNReal.ofReal CH *
            fullBallProjectedIterationSourceSquareMoment u D p (-1) 0 c ρ 0 := by
        simp only [fullBallProjectedIterationSourceSquareMoment, zero_sub, mul_assoc]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      have hadd : (∫⁻ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
          ENNReal.ofReal (vec3EuclideanNorm (V z) ^ 3) +
            ENNReal.ofReal CH * ‖unitBallVelocityCurve u z.2‖ₑ *
              ENNReal.ofReal (vec3EuclideanNorm (V z) ^ 2)) =
          (∫⁻ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
            ENNReal.ofReal (vec3EuclideanNorm (V z) ^ 3)) +
          (∫⁻ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
            ENNReal.ofReal CH * ‖unitBallVelocityCurve u z.2‖ₑ *
              ENNReal.ofReal (vec3EuclideanNorm (V z) ^ 2)) := lintegral_add_left' hQ3 _
      exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans
        ((congrArg (fun x : ℝ≥0∞ ↦ ENNReal.ofReal K * x) hadd).trans
          (congrArg (fun x : ℝ≥0∞ ↦ ENNReal.ofReal K *
            ((∫⁻ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
              ENNReal.ofReal (vec3EuclideanNorm (V z) ^ 3)) + x)) he))

/-- The true global Gaussian Hessian error is bounded by two actual full-source moments. -/
theorem suitable_fullBall_projected_gaussian_harmonic_moment_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    {r δ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hδ : 0 < δ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    ‖∫ z : ParabolicPoint, fullBallJointHarmonicError u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ z‖ₑ ≤
      ENNReal.ofReal (9000 * fullBallProjectedHarmonicHessianVelocityConstant (1 / 2) / r) *
        (fullBallProjectedIterationSourceSquareMoment u D p (-1) 0 c ρ 0 +
          ENNReal.ofReal (fullBallProjectedHarmonicVelocityConstant (1 / 2)) *
            fullBallProjectedIterationSourceLinearMoment u D p (-1) 0 c ρ 0) := by
  let V := fullBallProjectedVelocityAmbient u D p (-1) 0 c
  let F := fullBallJointHarmonicError u D p (-1) 0 c (projectedGaussianTest r ρ δ hρ) χ
  let K := 9000 * fullBallProjectedHarmonicHessianVelocityConstant (1 / 2) / r
  let CH := fullBallProjectedHarmonicVelocityConstant (1 / 2)
  have hCH : 0 ≤ CH := fullBallProjectedHarmonicVelocityConstant_nonneg (by norm_num)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact div_nonneg (mul_nonneg (by norm_num)
      (fullBallProjectedHarmonicHessianVelocityConstant_nonneg (by norm_num))) hr.le
  have hF := (suitable_fullBall_projected_gaussian_flux_integrable
    hsol hbox hc hr hρ hρhalf hδ hχ hbχ).2
  have hz : ∀ z : ParabolicPoint, z ∉ vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0 → F z = 0 := by
    intro z hn
    exact (fullBallJointEnergyErrors_zero_off_tsupport u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ (z.1, z.2)
        (fun hs ↦ hn (projectedGaussianTest_tsupport_cylinder hρ hδ hs))).2.2.2
  have hp0 := gaussianFlux_ae_on_cylinder (ρ := ρ)
    (P := fun z ↦ ‖F z‖ ≤ K * (‖unitBallVelocityCurve u z.2‖ *
      vec3EuclideanNorm (V z) ^ 2 + CH * ‖unitBallVelocityCurve u z.2‖ ^ 2 *
        vec3EuclideanNorm (V z)))
    (suitable_fullBall_projected_gaussian_harmonic_pointwise_bound
      hsol hbox hc hr hρ hρhalf hδ hbχ)
  have hp : ∀ᵐ z ∂volume.restrict (vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0), ‖F z‖ₑ ≤
      ENNReal.ofReal K * (‖unitBallVelocityCurve u z.2‖ₑ *
        ENNReal.ofReal (vec3EuclideanNorm (V z) ^ 2) +
          ENNReal.ofReal CH * ‖unitBallVelocityCurve u z.2‖ₑ ^ 2 *
            ENNReal.ofReal (vec3EuclideanNorm (V z))) := by
    filter_upwards [hp0] with z hzp
    have hv : 0 ≤ vec3EuclideanNorm (V z) := vec3EuclideanNorm_nonneg _
    calc
      _ = ENNReal.ofReal ‖F z‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (K * (‖unitBallVelocityCurve u z.2‖ * vec3EuclideanNorm (V z) ^ 2 +
          CH * ‖unitBallVelocityCurve u z.2‖ ^ 2 * vec3EuclideanNorm (V z))) :=
        ENNReal.ofReal_le_ofReal hzp
      _ = _ := by
        rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hCH,
          ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hV := gaussianFlux_projected_measurable hsol hbox hc hρ hρhalf
  have hS0 := (suitable_velocityCurve_memLp_localBox hsol hbox).aestronglyMeasurable
  have hS1 := hS0.mono_measure
    (Measure.restrict_mono_set volume (gaussianFlux_time_subset hρ hρhalf))
  have hS : AEMeasurable (fun z : Vec3 × ℝ ↦ ‖unitBallVelocityCurve u z.2‖ₑ)
      ((volume.restrict (vec3Ball 0 ρ)).prod (volume.restrict (Ioo (-ρ ^ 2) 0))) :=
    hS1.enorm.comp_snd
  have hSQ : AEMeasurable (fun z : ParabolicPoint ↦ ‖unitBallVelocityCurve u z.2‖ₑ *
      ENNReal.ofReal (vec3EuclideanNorm (V z) ^ 2))
      (volume.restrict (vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0)) := by
    rw [volume_parabolicPoint_eq_prod, ← Measure.prod_restrict]
    exact hS.mul (ENNReal.continuous_ofReal.comp_aestronglyMeasurable
      ((CKN.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hV).pow 2)).aemeasurable
  calc
    _ ≤ ∫⁻ z in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0, ‖F z‖ₑ :=
      gaussianFlux_integral_bound hF hz
    _ ≤ ∫⁻ z in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
        ENNReal.ofReal K * (‖unitBallVelocityCurve u z.2‖ₑ *
          ENNReal.ofReal (vec3EuclideanNorm (V z) ^ 2) +
            ENNReal.ofReal CH * ‖unitBallVelocityCurve u z.2‖ₑ ^ 2 *
              ENNReal.ofReal (vec3EuclideanNorm (V z))) := lintegral_mono_ae hp
    _ = _ := by
      have he : (∫⁻ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
          ENNReal.ofReal CH * ‖unitBallVelocityCurve u z.2‖ₑ ^ 2 *
            ENNReal.ofReal (vec3EuclideanNorm (V z))) =
          ENNReal.ofReal CH *
            fullBallProjectedIterationSourceLinearMoment u D p (-1) 0 c ρ 0 := by
        simp only [fullBallProjectedIterationSourceLinearMoment, zero_sub, mul_assoc]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      have hadd : (∫⁻ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
          ‖unitBallVelocityCurve u z.2‖ₑ * ENNReal.ofReal (vec3EuclideanNorm (V z) ^ 2) +
            ENNReal.ofReal CH * ‖unitBallVelocityCurve u z.2‖ₑ ^ 2 *
              ENNReal.ofReal (vec3EuclideanNorm (V z))) =
          fullBallProjectedIterationSourceSquareMoment u D p (-1) 0 c ρ 0 +
          (∫⁻ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
            ENNReal.ofReal CH * ‖unitBallVelocityCurve u z.2‖ₑ ^ 2 *
              ENNReal.ofReal (vec3EuclideanNorm (V z))) := by
        simpa only [fullBallProjectedIterationSourceSquareMoment, zero_sub] using
          lintegral_add_left' hSQ (fun z : ParabolicPoint ↦ ENNReal.ofReal CH *
            ‖unitBallVelocityCurve u z.2‖ₑ ^ 2 * ENNReal.ofReal (vec3EuclideanNorm (V z)))
      exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans
        ((congrArg (fun x : ℝ≥0∞ ↦ ENNReal.ofReal K * x) hadd).trans
          (congrArg (fun x : ℝ≥0∞ ↦ ENNReal.ofReal K *
            (fullBallProjectedIterationSourceSquareMoment u D p (-1) 0 c ρ 0 + x)) he))

end Suitable

end FluidSingularSets
