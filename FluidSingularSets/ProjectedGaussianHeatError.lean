-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedGaussianCutoff
public import FluidSingularSets.FullBallJointErrorIntegrability
public import FluidSingularSets.FullBallPressureOscillationDecay
public import FluidSingularSets.FullBallTimeWeightedEnergy

/-!
# Actual Gaussian heat errors and projected iteration energy

Genuine suitable slice bounds make the fixed-projection energy finite. Tonelli
and the actual essential supremum control the cylinder square moment. The
Gaussian heat estimate remains signed and independent of the terminal ramp.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Heat
open scoped ENNReal NNReal Topology BigOperators ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- The literal Euclidean spatial square moment is bounded by its genuine essential supremum. -/
theorem fullBallProjectedIteration_euclidean_square_le_sliceEnergy_ae
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c r τ : ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioo (τ - r ^ 2) τ),
      (∫⁻ x in vec3Ball 0 r, ENNReal.ofReal
        (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c (x, t)) ^ 2)) ≤
          fullBallProjectedIterationSliceEnergy u D p a b c r τ :=
  ENNReal.ae_le_essSup _

/-- The native spatial square moment is bounded by the genuine Euclidean slice energy. -/
theorem fullBallProjectedIteration_native_square_le_sliceEnergy_ae
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c r τ : ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioo (τ - r ^ 2) τ),
      (∫⁻ x in vec3Ball 0 r,
        ‖fullBallProjectedVelocityAmbient u D p a b c (x, t)‖ₑ ^ (2 : ℝ)) ≤
          fullBallProjectedIterationSliceEnergy u D p a b c r τ := by
  filter_upwards [fullBallProjectedIteration_euclidean_square_le_sliceEnergy_ae
    u D p a b c r τ] with t ht
  refine (lintegral_mono fun x ↦ ?_).trans ht
  rw [ENNReal.rpow_ofNat, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal
    ((sq_le_sq₀ (norm_nonneg _) (vec3EuclideanNorm_nonneg _)).2
      (norm_le_vec3EuclideanNorm _))

section Suitable

variable {Ω : Set Vec3} {I : Set ℝ} {q c ρ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

private theorem gaussian_iteration_time_subset (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    Ioo (-ρ ^ 2) 0 ⊆ Ioo (-1) 0 := by
  intro t ht
  have hsq : ρ ^ 2 < 1 / 4 := by nlinarith
  exact ⟨by linarith only [ht.1, hsq], ht.2⟩

/-- Actual suitable data make the genuine Euclidean iteration slice energy finite. -/
theorem suitable_fullBall_projected_iteration_sliceEnergy_lt_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    fullBallProjectedIterationSliceEnergy u D p (-1) 0 c ρ 0 < ⊤ := by
  have hf := fullBallTimeWeightedProjectedEnergySup_lt_top
    (B := vec3Ball 0 ρ) (φ := fun _ ↦ 1) (θ := fun _ ↦ 1)
    hsol hbox (by norm_num) hc hρ (by linarith) (isOpen_vec3Ball 0 ρ)
    subset_closure contDiff_const (fun _ ↦ by norm_num) (fun _ ↦ by norm_num)
  have heq : fullBallTimeWeightedProjectedEnergySup u D p (-1) 0 c
      (vec3Ball 0 ρ) (fun _ ↦ 1) (fun _ ↦ 1) =
      essSup (fun t ↦ ∫⁻ x in vec3Ball 0 ρ, ENNReal.ofReal
        (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p (-1) 0 c (x, t)) ^ 2))
          (volume.restrict (Ioo (-1) 0)) := by
    unfold fullBallTimeWeightedProjectedEnergySup
    apply congrArg (fun f : ℝ → ℝ≥0∞ ↦ essSup f (volume.restrict (Ioo (-1) 0)))
    funext t
    apply lintegral_congr
    intro x
    simp only [fullBallTimeWeightedProjectedVelocity, fullBallProjectedCutoffVelocity,
      Real.sqrt_one, one_pow, one_smul]
    rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _), ENNReal.rpow_ofNat,
      ← ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _)]
  have hm := essSup_mono_measure'
    (μ := volume.restrict (Ioo (-1) 0)) (ν := volume.restrict (Ioo (-ρ ^ 2) 0))
    (f := fun t ↦ ∫⁻ x in vec3Ball 0 ρ, ENNReal.ofReal
      (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p (-1) 0 c (x, t)) ^ 2))
    (Measure.restrict_mono (gaussian_iteration_time_subset hρ hρhalf) le_rfl)
  change essSup _ (volume.restrict (Ioo (0 - ρ ^ 2) 0)) < ⊤
  simpa only [zero_sub] using hm.trans_lt (heq ▸ hf)

/-- Actual projected weak H¹ data make the coordinate iteration dissipation finite. -/
theorem suitable_fullBall_projected_iteration_dissipation_lt_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    fullBallProjectedIterationDissipation u D p (-1) 0 c ρ 0 < ⊤ := by
  have hd := (fullBallProjectedVelocityAmbient_joint_memLp_two
    (B := vec3Ball 0 ρ) hsol hbox (by norm_num) hc hρ (by linarith) subset_closure).2
  have hj : MemLp (fullBallProjectedVelocityDerivativeAmbient u D p (-1) 0 c) 2
      (volume.restrict (vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0)) :=
    hd.mono_measure (Measure.restrict_mono
      (Set.prod_mono Subset.rfl (gaussian_iteration_time_subset hρ hρhalf)) le_rfl)
  have he : (∫⁻ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
      ‖fullBallProjectedVelocityDerivativeAmbient u D p (-1) 0 c z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    simpa only [ENNReal.toReal_ofNat] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2)
        (by norm_num) (by norm_num) hj
  unfold fullBallProjectedIterationDissipation
  simp only [zero_sub]
  calc
    _ ≤ ∫⁻ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
        9 * ‖fullBallProjectedVelocityDerivativeAmbient u D p (-1) 0 c z‖ₑ ^ (2 : ℝ) :=
      lintegral_mono fun z ↦ projectedGradientSquare_enorm_le_nine _
    _ = 9 * ∫⁻ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
        ‖fullBallProjectedVelocityDerivativeAmbient u D p (-1) 0 c z‖ₑ ^ (2 : ℝ) :=
      lintegral_const_mul' _ _ (by norm_num)
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num) he

/-- Genuine suitable data make the actual normalized projected energy finite. -/
theorem suitable_fullBall_normalized_projected_iteration_energy_lt_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0 < ⊤ :=
  ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr
    ⟨suitable_fullBall_projected_iteration_sliceEnergy_lt_top hsol hbox hc hρ hρhalf,
      suitable_fullBall_projected_iteration_dissipation_lt_top hsol hbox hc hρ hρhalf⟩)

/-- Actual suitable data give true square integrability on every smaller backward cylinder. -/
theorem suitable_fullBall_projected_iteration_square_integrable
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    Integrable (fun z : ParabolicPoint ↦
      vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p (-1) 0 c z) ^ 2)
        (volume.restrict (vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0)) := by
  have hi := fullBallProjectedVelocityAmbient_euclidean_square_integrable
    (B := vec3Ball 0 ρ) hsol hbox (by norm_num) hc hρ (by linarith) subset_closure
  exact hi.mono_measure (Measure.restrict_mono
      (Set.prod_mono Subset.rfl (gaussian_iteration_time_subset hρ hρhalf)) le_rfl)

/-- Genuine Tonelli and the actual essential supremum bound the cylinder square moment. -/
theorem suitable_fullBall_projected_iteration_square_lintegral_le
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    (∫⁻ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0, ENNReal.ofReal
      (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p (-1) 0 c z) ^ 2)) ≤
        ENNReal.ofReal (ρ ^ 2) * fullBallProjectedIterationSliceEnergy u D p (-1) 0 c ρ 0 := by
  let V := fullBallProjectedVelocityAmbient u D p (-1) 0 c
  let J := Ioo (-ρ ^ 2) 0
  have hi := suitable_fullBall_projected_iteration_square_integrable hsol hbox hc hρ hρhalf
  have hm : AEMeasurable (fun z : ParabolicPoint ↦ ENNReal.ofReal
      (vec3EuclideanNorm (V z) ^ 2)) (volume.restrict (vec3Ball 0 ρ ×ˢ J)) :=
    (ENNReal.continuous_ofReal.comp_aestronglyMeasurable hi.aestronglyMeasurable).aemeasurable
  have hp : AEMeasurable (fun z : Vec3 × ℝ ↦ ENNReal.ofReal
      (vec3EuclideanNorm (V z) ^ 2)) ((volume.restrict (vec3Ball 0 ρ)).prod
        (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hm
  have hs : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in vec3Ball 0 ρ, ENNReal.ofReal (vec3EuclideanNorm (V (x, t)) ^ 2)) ≤
        fullBallProjectedIterationSliceEnergy u D p (-1) 0 c ρ 0 := by
    simpa only [fullBallProjectedIterationSliceEnergy, zero_sub] using
      ENNReal.ae_le_essSup (fun t ↦ ∫⁻ x in vec3Ball 0 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (V (x, t)) ^ 2)) (μ := volume.restrict J)
  calc
    _ = ∫⁻ z : Vec3 × ℝ, ENNReal.ofReal (vec3EuclideanNorm (V z) ^ 2)
        ∂(volume.restrict (vec3Ball 0 ρ)).prod (volume.restrict J) := by
      rw [show (volume : Measure ParabolicPoint).restrict (vec3Ball 0 ρ ×ˢ J) =
          (volume.restrict (vec3Ball 0 ρ)).prod (volume.restrict J) by
        rw [Measure.prod_restrict, volume_parabolicPoint_eq_prod]]
      rfl
    _ = ∫⁻ t in J, ∫⁻ x in vec3Ball 0 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (V (x, t)) ^ 2) := lintegral_prod_symm _ hp
    _ ≤ ∫⁻ _t in J, fullBallProjectedIterationSliceEnergy u D p (-1) 0 c ρ 0 :=
      lintegral_mono_ae hs
    _ = ENNReal.ofReal (ρ ^ 2) * fullBallProjectedIterationSliceEnergy u D p (-1) 0 c ρ 0 := by
      simp only [lintegral_const, Measure.restrict_apply_univ, J, Real.volume_Ioo,
        zero_sub, neg_neg]
      ring

/-- Actual finite slice energy converts the genuine cylinder square bound to real numbers. -/
theorem suitable_fullBall_projected_iteration_square_integral_le
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    (∫ z : ParabolicPoint in vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0,
      vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p (-1) 0 c z) ^ 2) ≤
        ρ ^ 2 * (fullBallProjectedIterationSliceEnergy u D p (-1) 0 c ρ 0).toReal := by
  have hi := suitable_fullBall_projected_iteration_square_integrable hsol hbox hc hρ hρhalf
  have hM := suitable_fullBall_projected_iteration_sliceEnergy_lt_top hsol hbox hc hρ hρhalf
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM.ne)
    (suitable_fullBall_projected_iteration_square_lintegral_le hsol hbox hc hρ hρhalf)
  rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ sq_nonneg _)
    hi.aestronglyMeasurable, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg ρ)] at hh
  exact hh

/-- The actual Gaussian heat error is globally integrable for every genuine backward weight. -/
theorem suitable_fullBall_projected_gaussian_heat_integrable
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    {r δ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hδ : 0 < δ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) :
    Integrable (fullBallJointHeatError u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ) volume := by
  obtain ⟨htest, hn, hs⟩ := projectedGaussianTest_admissible hr hρ hρhalf hδ
  have ht : projectedGaussianTest r ρ δ hρ ∈ spaceTimeTestFunction (V := ℝ) Ω I :=
    ⟨htest.1, htest.2.1, htest.2.2.trans
      (Set.prod_mono (subset_closure.trans hbox.2.2.1)
        (subset_closure.trans hbox.2.2.2.2.2))⟩
  exact (suitable_fullBall_joint_errors_integrable hsol hbox (by norm_num) hc hρ
    (by linarith) ht hn hs hχ (fun t ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbχ t).1]
      exact (hbχ t).2)).1

/-- The actual Gaussian heat error is controlled by the genuine normalized outer energy. -/
theorem suitable_fullBall_projected_gaussian_heat_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    {r δ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (hscale : r ≤ ρ / 2) (hδ : 0 < δ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) :
    (∫ z : ParabolicPoint, fullBallJointHeatError u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ z) ≤
        projectedGaussianHeatConstant * (r / ρ) ^ 2 *
          (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0).toReal := by
  let V := fullBallProjectedVelocityAmbient u D p (-1) 0 c
  let A : Set ParabolicPoint := vec3Ball 0 ρ ×ˢ Ioo (-ρ ^ 2) 0
  let ψ := projectedGaussianTest r ρ δ hρ
  let F := fullBallJointHeatError u D p (-1) 0 c ψ χ
  let K := projectedGaussianHeatConstant * r ^ 2 / ρ ^ 5
  have hCG : 0 ≤ cutoffGradientConstant := cutoffGradientConstant_nonneg_global
  have hCS : 0 ≤ cutoffSecondDerivativeConstant := cutoffSecondDerivativeConstant_nonneg_global
  have hC : 0 ≤ projectedGaussianHeatConstant := by
    unfold projectedGaussianHeatConstant
    positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hi := suitable_fullBall_projected_iteration_square_integrable hsol hbox hc hρ hρhalf
  have hF : Integrable F volume :=
    suitable_fullBall_projected_gaussian_heat_integrable hsol hbox hc hr hρ hρhalf hδ hχ hbχ
  have hz : ∀ z : ParabolicPoint, z ∉ A → F z = 0 := by
    intro z hn
    have hnψ : (z.1, z.2) ∉ tsupport ψ := fun hs ↦
      hn (projectedGaussianTest_tsupport_cylinder hρ hδ hs)
    exact (fullBallJointEnergyErrors_zero_off_tsupport
      u D p (-1) 0 c ψ χ (z.1, z.2) hnψ).1
  have hp (z : ParabolicPoint) : F z ≤ K * vec3EuclideanNorm (V z) ^ 2 := by
    have hH := projectedGaussianTest_heat_upper_global hr hρ hscale hδ z
    have hm : (timePartial ψ z + ∑ j, spatialSecondPartial ψ j j z) * χ z.2 ≤ K :=
      ((mul_le_mul_of_nonneg_right hH (hbχ z.2).1).trans
        (mul_le_mul_of_nonneg_left (hbχ z.2).2 hK)).trans_eq (mul_one K)
    calc
      _ = vec3EuclideanNorm (V z) ^ 2 *
          ((timePartial ψ z + ∑ j, spatialSecondPartial ψ j j z) * χ z.2) := mul_assoc _ _ _
      _ ≤ vec3EuclideanNorm (V z) ^ 2 * K :=
        mul_le_mul_of_nonneg_left hm (sq_nonneg _)
      _ = K * vec3EuclideanNorm (V z) ^ 2 := mul_comm _ _
  have hME : ρ⁻¹ * (fullBallProjectedIterationSliceEnergy u D p (-1) 0 c ρ 0).toReal ≤
      (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0).toReal := by
    have he := suitable_fullBall_normalized_projected_iteration_energy_lt_top
      hsol hbox hc hρ hρhalf
    have hm : ENNReal.ofReal ρ⁻¹ * fullBallProjectedIterationSliceEnergy u D p (-1) 0 c ρ 0 ≤
        fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0 :=
      mul_le_mul' le_rfl le_self_add
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hρ.le)] using
      ENNReal.toReal_mono he.ne hm
  calc
    _ = ∫ z : ParabolicPoint in A, F z :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm
    _ ≤ ∫ z : ParabolicPoint in A, K * vec3EuclideanNorm (V z) ^ 2 :=
      integral_mono_ae (hF.mono_measure Measure.restrict_le_self) (hi.const_mul K)
        (ae_of_all _ hp)
    _ = K * ∫ z : ParabolicPoint in A, vec3EuclideanNorm (V z) ^ 2 :=
      integral_const_mul _ _
    _ ≤ K * (ρ ^ 2 * (fullBallProjectedIterationSliceEnergy u D p (-1) 0 c ρ 0).toReal) :=
      mul_le_mul_of_nonneg_left
        (suitable_fullBall_projected_iteration_square_integral_le hsol hbox hc hρ hρhalf) hK
    _ = projectedGaussianHeatConstant * (r / ρ) ^ 2 *
        (ρ⁻¹ * (fullBallProjectedIterationSliceEnergy u D p (-1) 0 c ρ 0).toReal) := by
      dsimp [K]
      field_simp [hρ.ne']
    _ ≤ projectedGaussianHeatConstant * (r / ρ) ^ 2 *
        (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0).toReal :=
      mul_le_mul_of_nonneg_left hME (mul_nonneg hC (sq_nonneg _))

end Suitable

end FluidSingularSets
