-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedGaussianFluxErrors

/-!
# Actual normalized Gaussian harmonic source costs

The original endpoint mixed moment bounds the real full-ball source curve.
The genuine projected slice energy then gives the exact squared-radius source
moments. The Hessian error retains the sharper radius factor before Young absorption.
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

/-- The literal original full-ball endpoint mixed square moment on the original interval. -/
def projectedGaussianOriginalSixMoment (u : ParabolicPoint → Vec3) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (-1) 0, eLpNorm (fun x ↦ u (x, t)) 6
    (volume.restrict (vec3Ball 0 1)) ^ 2

/-- The genuine slice energy is bounded by radius times the actual normalized energy. -/
theorem fullBallProjectedIterationSliceEnergy_le_radius_energy
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c τ : ℝ) {r : ℝ} (hr : 0 < r) :
    fullBallProjectedIterationSliceEnergy u D p a b c r τ ≤
      ENNReal.ofReal r * fullBallNormalizedProjectedIterationEnergy u D p a b c r τ := by
  have hi : ENNReal.ofReal r * ENNReal.ofReal r⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hr.le, mul_inv_cancel₀ hr.ne', ENNReal.ofReal_one]
  calc
    _ ≤ fullBallProjectedIterationSliceEnergy u D p a b c r τ +
        fullBallProjectedIterationDissipation u D p a b c r τ := le_self_add
    _ = _ := by
      unfold fullBallNormalizedProjectedIterationEnergy
      rw [← mul_assoc, hi, one_mul]

private theorem gaussianSource_time_subset {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    Ioo (-ρ ^ 2) 0 ⊆ Ioo (-1) 0 := by
  intro t ht
  have hsq : ρ ^ 2 < 1 / 4 := by nlinarith
  exact ⟨by linarith only [ht.1, hsq], ht.2⟩

section Suitable

variable {Ω : Set Vec3} {I : Set ℝ} {q c ρ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

/-- Genuine finite energy makes the literal original endpoint moment finite. -/
theorem suitable_projectedGaussianOriginalSixMoment_lt_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) :
    projectedGaussianOriginalSixMoment u < ⊤ := by
  simpa only [projectedGaussianOriginalSixMoment, ENNReal.rpow_ofNat] using
    suitable_fullBall_velocity_six_moment_lt_top hsol hbox

/-- The genuine original endpoint moment controls the actual source curve on the small window. -/
theorem suitable_projectedGaussian_source_two_le_endpoint
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0))
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    eLpNorm (unitBallVelocityCurve u) 2 (volume.restrict (Ioo (-ρ ^ 2) 0)) ≤
      volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ) *
        projectedGaussianOriginalSixMoment u ^ (1 / 2 : ℝ) :=
  (eLpNorm_mono_measure _ (Measure.restrict_mono
    (gaussianSource_time_subset hρ hρhalf) le_rfl)).trans
      (localBox_velocityCurve_two_le_six_moment_sqrt hsol hbox)

/-- The literal quadratic Gaussian source moment has the exact normalized squared-radius bound. -/
theorem suitable_fullBall_projected_iteration_source_square_le_normalized_energy
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    fullBallProjectedIterationSourceSquareMoment u D p (-1) 0 c ρ 0 ≤
      volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ) * ENNReal.ofReal ρ ^ 2 *
        fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0 *
          projectedGaussianOriginalSixMoment u ^ (1 / 2 : ℝ) := by
  have hh := suitable_fullBall_projected_iteration_source_square_bound hsol hbox hc hρ hρhalf
  exact hh.trans ((mul_le_mul'
    (mul_le_mul' le_rfl
      (fullBallProjectedIterationSliceEnergy_le_radius_energy u D p (-1) 0 c 0 hρ))
    (suitable_projectedGaussian_source_two_le_endpoint hsol hbox hρ hρhalf)).trans_eq
      (by ring))

/-- The literal linear Gaussian source moment has the exact normalized squared-radius bound. -/
theorem suitable_fullBall_projected_iteration_source_linear_le_normalized_energy
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    fullBallProjectedIterationSourceLinearMoment u D p (-1) 0 c ρ 0 ≤
      volume (vec3Ball (0 : Vec3) 1) ^ (7 / 6 : ℝ) * ENNReal.ofReal ρ ^ 2 *
        fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0 ^ (1 / 2 : ℝ) *
          projectedGaussianOriginalSixMoment u := by
  let W := volume (vec3Ball (0 : Vec3) 1)
  let E := fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0
  let X := projectedGaussianOriginalSixMoment u
  have hW0 : W ≠ 0 := (volume_vec3Ball_pos (by norm_num : (0 : ℝ) < 1)).ne'
  have hWtop : W ≠ ⊤ := volume_vec3Ball_lt_top.ne
  have hρ0 : ENNReal.ofReal ρ ≠ 0 := (ENNReal.ofReal_pos.mpr hρ).ne'
  have hVol : volume (vec3Ball (0 : Vec3) ρ) ^ (1 / 2 : ℝ) =
      W ^ (1 / 2 : ℝ) * ENNReal.ofReal ρ ^ (3 / 2 : ℝ) := by
    rw [volume_vec3Ball_eq, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ← ENNReal.rpow_natCast _ 3, ← ENNReal.rpow_mul]
    norm_num only [show (3 : ℝ) * (1 / 2) = 3 / 2 by norm_num]
    dsimp [W]
    rw [volume_vec3Ball_eq]
    simp only [ENNReal.ofReal_one, one_pow, one_mul]
    exact mul_comm _ _
  have hM := ENNReal.rpow_le_rpow
    (fullBallProjectedIterationSliceEnergy_le_radius_energy u D p (-1) 0 c 0 hρ)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at hM
  have hS := ENNReal.rpow_le_rpow
    (suitable_projectedGaussian_source_two_le_endpoint hsol hbox hρ hρhalf)
      (by norm_num : (0 : ℝ) ≤ 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hS
  norm_num only [show (1 / 3 : ℝ) * 2 = 2 / 3 by norm_num,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_ofNat] at hS
  have hh := suitable_fullBall_projected_iteration_source_linear_bound hsol hbox hc hρ hρhalf
  refine hh.trans ((mul_le_mul' (mul_le_mul' le_rfl hM) hS).trans_eq ?_)
  rw [hVol]
  change W ^ (1 / 2 : ℝ) * ENNReal.ofReal ρ ^ (3 / 2 : ℝ) *
    (ENNReal.ofReal ρ ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ)) *
    (W ^ (2 / 3 : ℝ) * X) = W ^ (7 / 6 : ℝ) * ENNReal.ofReal ρ ^ 2 * E ^ (1 / 2 : ℝ) * X
  have hR : ENNReal.ofReal ρ ^ (3 / 2 : ℝ) * ENNReal.ofReal ρ ^ (1 / 2 : ℝ) =
      ENNReal.ofReal ρ ^ 2 := by
    rw [← ENNReal.rpow_add _ _ hρ0 ENNReal.ofReal_ne_top]
    norm_num
  have hW : W ^ (1 / 2 : ℝ) * W ^ (2 / 3 : ℝ) = W ^ (7 / 6 : ℝ) := by
    rw [← ENNReal.rpow_add _ _ hW0 hWtop]
    norm_num
  calc
    _ = (W ^ (1 / 2 : ℝ) * W ^ (2 / 3 : ℝ)) *
        (ENNReal.ofReal ρ ^ (3 / 2 : ℝ) * ENNReal.ofReal ρ ^ (1 / 2 : ℝ)) *
          E ^ (1 / 2 : ℝ) * X := by ring
    _ = _ := by rw [hR, hW]

/-- The exact finite harmonic Gaussian cost, retaining its radius factor before absorption. -/
def projectedGaussianHarmonicEnergyCost (r ρ : ℝ) (E X : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (9000 * fullBallProjectedHarmonicHessianVelocityConstant (1 / 2) * ρ ^ 2 / r) *
    (volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ) * E * X ^ (1 / 2 : ℝ) +
      ENNReal.ofReal (fullBallProjectedHarmonicVelocityConstant (1 / 2)) *
        volume (vec3Ball (0 : Vec3) 1) ^ (7 / 6 : ℝ) * E ^ (1 / 2 : ℝ) * X)

/-- The genuine Gaussian Hessian error has the exact normalized energy and source cost. -/
theorem suitable_fullBall_projected_gaussian_harmonic_energy_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    {r δ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hδ : 0 < δ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    ‖∫ z : ParabolicPoint, fullBallJointHarmonicError u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ z‖ₑ ≤
      projectedGaussianHarmonicEnergyCost r ρ
        (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0)
          (projectedGaussianOriginalSixMoment u) := by
  have hh := suitable_fullBall_projected_gaussian_harmonic_moment_bound
    hsol hbox hc hr hρ hρhalf hδ hχ hbχ
  refine hh.trans ((mul_le_mul' le_rfl (add_le_add
    (suitable_fullBall_projected_iteration_source_square_le_normalized_energy
      hsol hbox hc hρ hρhalf)
    (mul_le_mul' le_rfl
      (suitable_fullBall_projected_iteration_source_linear_le_normalized_energy
        hsol hbox hc hρ hρhalf)))).trans_eq ?_)
  unfold projectedGaussianHarmonicEnergyCost
  have hC : 0 ≤ 9000 * fullBallProjectedHarmonicHessianVelocityConstant (1 / 2) / r :=
    div_nonneg (mul_nonneg (by norm_num)
      (fullBallProjectedHarmonicHessianVelocityConstant_nonneg (by norm_num))) hr.le
  have he : ENNReal.ofReal
      (9000 * fullBallProjectedHarmonicHessianVelocityConstant (1 / 2) * ρ ^ 2 / r) =
      ENNReal.ofReal (9000 * fullBallProjectedHarmonicHessianVelocityConstant (1 / 2) / r) *
        ENNReal.ofReal ρ ^ 2 := by
    rw [← ENNReal.ofReal_pow hρ.le, ← ENNReal.ofReal_mul hC]
    congr 1
    ring
  rw [he]
  ring

/-- The normalized actual harmonic error cost is genuinely finite. -/
theorem suitable_projectedGaussianHarmonicEnergyCost_lt_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (r : ℝ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    projectedGaussianHarmonicEnergyCost r ρ
      (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0)
        (projectedGaussianOriginalSixMoment u) < ⊤ := by
  have hE := (suitable_fullBall_normalized_projected_iteration_energy_lt_top
    hsol hbox hc hρ hρhalf).ne
  have hX := (suitable_projectedGaussianOriginalSixMoment_lt_top hsol hbox).ne
  unfold projectedGaussianHarmonicEnergyCost
  have hW : volume (vec3Ball (0 : Vec3) 1) ≠ ⊤ := volume_vec3Ball_lt_top.ne
  finiteness [hE, hX, hW]

/-- The true harmonic integral obeys the finite normalized real energy cost. -/
theorem suitable_fullBall_projected_gaussian_harmonic_energy_bound_real
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    {r δ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hδ : 0 < δ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    ‖∫ z : ParabolicPoint, fullBallJointHarmonicError u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ z‖ ≤
      (projectedGaussianHarmonicEnergyCost r ρ
        (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0)
          (projectedGaussianOriginalSixMoment u)).toReal := by
  have hh := ENNReal.toReal_mono
    (suitable_projectedGaussianHarmonicEnergyCost_lt_top hsol hbox hc r hρ hρhalf).ne
    (suitable_fullBall_projected_gaussian_harmonic_energy_bound
      hsol hbox hc hr hρ hρhalf hδ hχ hbχ)
  simpa only [toReal_enorm] using hh

end Suitable

end FluidSingularSets
