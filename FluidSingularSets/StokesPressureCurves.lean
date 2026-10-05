-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StokesPressureTimeIntegrability

/-!
# Genuine anisotropic Stokes pressure curves

The actual conditional spatial L² classes of `u ⊗ u` and of the transposed
velocity gradient are mapped by the constructed continuous Stokes pressure
operator. Genuine joint measurability proves measurability of these pressure
curves. The suitable solution's actual energy data give time L^{4/3} for the
convective pressure and time L² for the viscous pressure.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

private theorem pressureCurve_ball_eq {r : ℝ} (hr : 0 < r) :
    euclideanBall (0 : Vec3) r = vec3Ball 0 r := by
  ext x
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr, mem_vec3Ball]
  simp only [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]

/-- The actual tensor-to-force operation is a continuous linear map. -/
def stokesTensorForceL (U : Set Vec3) : StokesGradientL2 U →L[ℝ] StokesEnergyForce U :=
  (realDualPrecompose (E := StokesGradientL2 U) (K := stokesGradientEnergySpace U)
    (stokesGradientEnergySpace U).toSubmodule.subtypeL).comp (innerSL ℝ)

@[simp]
theorem stokesTensorForceL_apply {U : Set Vec3} (T : StokesGradientL2 U) :
    stokesTensorForceL U T = stokesTensorForce T := rfl

/-- The genuine continuous tensor pressure operator on the unit ball. -/
def unitBallTensorPressureL : StokesGradientL2 (vec3Ball 0 1) →L[ℝ] unitBallMeanZeroL2 :=
  unitBallStokesPressureL.comp (stokesTensorForceL (vec3Ball 0 1))

@[simp]
theorem unitBallTensorPressureL_apply (T : StokesGradientL2 (vec3Ball 0 1)) :
    unitBallTensorPressureL T = unitBallStokesPressure (stokesTensorForce T) := rfl

/-- The pressure of the true convective tensor slice, zero at the non-L² times. -/
def unitBallConvectivePressureCurve (u : ParabolicPoint → Vec3) (t : ℝ) :
    unitBallMeanZeroL2 :=
  unitBallTensorPressureL (actualSliceLp (μ := volume.restrict (vec3Ball 0 1)) (p := 2)
    (fun z : Vec3 × ℝ ↦ stokesOuterProduct (u z) (u z)) t)

/-- The pressure of the actual negative derivative array, with the physical viscous sign. -/
def unitBallViscousPressureCurve (D : ParabolicPoint → Fin 3 → Vec3) (t : ℝ) :
    unitBallMeanZeroL2 :=
  unitBallTensorPressureL (-actualSliceLp (μ := volume.restrict (vec3Ball 0 1)) (p := 2)
    (fun z : Vec3 × ℝ ↦ stokesRawGradientMatrix (fun x ↦ D (x, z.2)) z.1) t)

/-- At every genuine L⁴ velocity slice this curve is exactly its nonlinear pressure. -/
theorem unitBallConvectivePressureCurve_eq (u : ParabolicPoint → Vec3) (t : ℝ)
    (ht : MemLp (fun x ↦ u (x, t)) 4 (volume.restrict (vec3Ball 0 1))) :
    unitBallConvectivePressureCurve u t = unitBallNonlinearPressure (fun x ↦ u (x, t)) ht := by
  unfold unitBallConvectivePressureCurve actualSliceLp
  rw [dite_eq_left (stokesConvectiveTensor_memLp (fun x ↦ u (x, t)) ht)]
  rfl

/-- At every genuine L² derivative slice this curve is exactly its viscous pressure. -/
theorem unitBallViscousPressureCurve_eq (D : ParabolicPoint → Fin 3 → Vec3) (t : ℝ)
    (ht : MemLp (fun x ↦ D (x, t)) 2 (volume.restrict (vec3Ball 0 1))) :
    unitBallViscousPressureCurve D t = unitBallRawViscousPressure (fun x ↦ D (x, t)) ht := by
  unfold unitBallViscousPressureCurve actualSliceLp
  rw [dite_eq_left (stokesRawGradientMatrix_memLp (fun x ↦ D (x, t)) ht)]
  rfl

/-- Genuine joint velocity measurability gives the actual pressure curve's measurability. -/
theorem unitBallConvectivePressureCurve_aestronglyMeasurable {ν : Measure ℝ} [SFinite ν]
    {u : ParabolicPoint → Vec3}
    (hu : AEStronglyMeasurable u ((volume.restrict (vec3Ball 0 1)).prod ν)) :
    AEStronglyMeasurable (unitBallConvectivePressureCurve u) ν := by
  have hT : AEStronglyMeasurable (fun z : Vec3 × ℝ ↦ stokesOuterProduct (u z) (u z))
      ((volume.restrict (vec3Ball 0 1)).prod ν) :=
    stokesOuterProduct_continuous.comp_aestronglyMeasurable (hu.prodMk hu)
  exact unitBallTensorPressureL.continuous.comp_aestronglyMeasurable
    (aestronglyMeasurable_actualSliceLp hT (by norm_num))

/-- Genuine joint derivative measurability gives the actual viscous curve's measurability. -/
theorem unitBallViscousPressureCurve_aestronglyMeasurable {ν : Measure ℝ} [SFinite ν]
    {D : ParabolicPoint → Fin 3 → Vec3}
    (hD : AEStronglyMeasurable D ((volume.restrict (vec3Ball 0 1)).prod ν)) :
    AEStronglyMeasurable (unitBallViscousPressureCurve D) ν := by
  have hmap : Continuous (fun A : Fin 3 → Vec3 ↦
      WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 ↦ A ij.2 ij.1)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 × Fin 3 ↦ ℝ)).comp
    exact continuous_pi (fun ij ↦ (continuous_apply ij.1).comp (continuous_apply ij.2))
  have hT : AEStronglyMeasurable
      (fun z : Vec3 × ℝ ↦ stokesRawGradientMatrix (fun x ↦ D (x, z.2)) z.1)
      ((volume.restrict (vec3Ball 0 1)).prod ν) :=
    hmap.comp_aestronglyMeasurable hD
  exact unitBallTensorPressureL.continuous.comp_aestronglyMeasurable
    (aestronglyMeasurable_actualSliceLp hT (by norm_num)).neg

/-- The exact actual spatial convective pressure bound in extended norms. -/
theorem unitBallConvectivePressureCurve_enorm_le (u : ParabolicPoint → Vec3) (t : ℝ)
    (ht : MemLp (fun x ↦ u (x, t)) 4 (volume.restrict (vec3Ball 0 1))) :
    ‖unitBallConvectivePressureCurve u t‖ₑ ≤
      12 * eLpNorm (fun x ↦ u (x, t)) 4 (volume.restrict (vec3Ball 0 1)) ^ 2 := by
  rw [unitBallConvectivePressureCurve_eq u t ht, ← ofReal_norm]
  have h := ENNReal.ofReal_le_ofReal (unitBallNonlinearPressure_norm (fun x ↦ u (x, t)) ht)
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ht.eLpNorm_lt_top.ne] using h

/-- The exact actual spatial viscous pressure bound in extended norms. -/
theorem unitBallViscousPressureCurve_enorm_le (D : ParabolicPoint → Fin 3 → Vec3) (t : ℝ)
    (ht : MemLp (fun x ↦ D (x, t)) 2 (volume.restrict (vec3Ball 0 1))) :
    ‖unitBallViscousPressureCurve D t‖ₑ ≤
      12 * eLpNorm (fun x ↦ D (x, t)) 2 (volume.restrict (vec3Ball 0 1)) := by
  rw [unitBallViscousPressureCurve_eq D t ht, ← ofReal_norm]
  have h := ENNReal.ofReal_le_ofReal (unitBallRawViscousPressure_norm (fun x ↦ D (x, t)) ht)
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_toReal ht.eLpNorm_lt_top.ne] using h

section Suitable

variable {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
  {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

private theorem pressureCurve_joint_restrict {E : Type*} [TopologicalSpace E]
    {F : ParabolicPoint → E}
    (hF : AEStronglyMeasurable F (volume.restrict (euclideanBall 0 2 ×ˢ J))) :
    AEStronglyMeasurable F ((volume.restrict (vec3Ball 0 1)).prod (volume.restrict J)) := by
  rw [Measure.prod_restrict, ← CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
  apply hF.mono_measure
  apply Measure.restrict_mono _ le_rfl
  exact Set.prod_mono
    (by rw [pressureCurve_ball_eq (by norm_num : (0 : ℝ) < 2)]; exact vec3Ball_mono (by norm_num))
    Subset.rfl

/-- Actual suitable data, without a slice-measurability premise, give convective pressure
time measurability. -/
theorem suitable_convectivePressureCurve_aestronglyMeasurable
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    AEStronglyMeasurable (unitBallConvectivePressureCurve u) (volume.restrict J) :=
  unitBallConvectivePressureCurve_aestronglyMeasurable
    (pressureCurve_joint_restrict (hsol.toData.aestronglyMeasurable_velocity hbox))

/-- Actual suitable data give viscous pressure time measurability. -/
theorem suitable_viscousPressureCurve_aestronglyMeasurable
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    AEStronglyMeasurable (unitBallViscousPressureCurve Du) (volume.restrict J) :=
  unitBallViscousPressureCurve_aestronglyMeasurable
    (pressureCurve_joint_restrict (hsol.toData.aestronglyMeasurable_gradient hbox))

/-- The genuine convective pressure moment is controlled by the actual velocity moment. -/
theorem suitable_convectivePressureCurve_time_moment
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    (∫⁻ t in J, ‖unitBallConvectivePressureCurve u t‖ₑ ^ (4 / 3 : ℝ)) ≤
      (12 : ℝ≥0∞) ^ (4 / 3 : ℝ) *
        ∫⁻ t in J, eLpNorm (fun x ↦ u (x, t)) 4
          (volume.restrict (euclideanBall 0 1)) ^ (8 / 3 : ℝ) := by
  have hpoint : ∀ᵐ t ∂volume.restrict J,
      ‖unitBallConvectivePressureCurve u t‖ₑ ^ (4 / 3 : ℝ) ≤
        (12 : ℝ≥0∞) ^ (4 / 3 : ℝ) * eLpNorm (fun x ↦ u (x, t)) 4
          (volume.restrict (euclideanBall 0 1)) ^ (8 / 3 : ℝ) := by
    filter_upwards [suitable_unitBall_memLp_four_ae hsol hbox] with t ht
    rw [pressureCurve_ball_eq (by norm_num : (0 : ℝ) < 1)] at ht ⊢
    have h := ENNReal.rpow_le_rpow (unitBallConvectivePressureCurve_enorm_le u t ht)
      (by norm_num : (0 : ℝ) ≤ 4 / 3)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_ofNat,
      ← ENNReal.rpow_mul] at h
    norm_num only [show (2 : ℝ) * (4 / 3) = 8 / 3 by norm_num] at h
    exact h
  calc
    _ ≤ ∫⁻ t in J, (12 : ℝ≥0∞) ^ (4 / 3 : ℝ) * eLpNorm (fun x ↦ u (x, t)) 4
        (volume.restrict (euclideanBall 0 1)) ^ (8 / 3 : ℝ) := lintegral_mono_ae hpoint
    _ = _ := lintegral_const_mul' _ _
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by norm_num)).ne

/-- Actual suitable energy data give genuine time L^{4/3} of the nonlinear spatial L² pressure. -/
theorem suitable_convectivePressureCurve_memLp
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    MemLp (unitBallConvectivePressureCurve u) (ENNReal.ofReal (4 / 3 : ℝ))
      (volume.restrict J) := by
  apply memLp_iff.mpr
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ENNReal.ofReal_pos.mpr (by norm_num)).ne' ENNReal.ofReal_ne_top
    (suitable_convectivePressureCurve_aestronglyMeasurable hsol hbox)).mpr
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4 / 3)]
  exact (suitable_convectivePressureCurve_time_moment hsol hbox).trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by norm_num))
      (suitable_unitBall_four_time_moment_lt_top hsol hbox))

/-- The genuine viscous pressure time-square moment is controlled by the actual gradient energy. -/
theorem suitable_viscousPressureCurve_time_moment
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    (∫⁻ t in J, ‖unitBallViscousPressureCurve Du t‖ₑ ^ (2 : ℝ)) ≤
      144 * ∫⁻ z in euclideanBall 0 2 ×ˢ J, ‖Du z‖ₑ ^ (2 : ℝ) := by
  have hsub : vec3Ball (0 : Vec3) 1 ⊆ euclideanBall 0 2 := by
    rw [pressureCurve_ball_eq (by norm_num : (0 : ℝ) < 2)]
    exact vec3Ball_mono (by norm_num)
  have hpoint : ∀ᵐ t ∂volume.restrict J,
      ‖unitBallViscousPressureCurve Du t‖ₑ ^ (2 : ℝ) ≤
        144 * eLpNorm (fun x ↦ Du (x, t)) 2
          (volume.restrict (euclideanBall 0 2)) ^ 2 := by
    filter_upwards [slice_memLp_ae_of_sws hsol hbox] with t ht
    have h := (unitBallViscousPressureCurve_enorm_le Du t
      (ht.2.mono_measure (Measure.restrict_mono hsub le_rfl))).trans
      (mul_le_mul_right (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)) 12)
    have hsq := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
    norm_num only [ENNReal.rpow_ofNat, mul_pow,
      show (12 : ℝ≥0∞) ^ 2 = 144 by norm_num] at hsq
    simpa only [ENNReal.rpow_ofNat] using hsq
  calc
    _ ≤ ∫⁻ t in J, 144 * eLpNorm (fun x ↦ Du (x, t)) 2
        (volume.restrict (euclideanBall 0 2)) ^ 2 := lintegral_mono_ae hpoint
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by norm_num),
        lintegral_spatial_two_sq_eq (hsol.toData.aestronglyMeasurable_gradient hbox)]

/-- Actual suitable gradient energy gives genuine time L² of the viscous spatial L² pressure. -/
theorem suitable_viscousPressureCurve_memLp
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    MemLp (unitBallViscousPressureCurve Du) 2 (volume.restrict J) := by
  apply memLp_iff.mpr
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
    (suitable_viscousPressureCurve_aestronglyMeasurable hsol hbox)).mpr
  rw [ENNReal.toReal_ofNat]
  apply (suitable_viscousPressureCurve_time_moment hsol hbox).trans_lt
  exact ENNReal.mul_lt_top (by norm_num)
    ((lintegral_mono (fun _ ↦ le_add_left le_rfl)).trans_lt
      (hsol.toData.energy_lintegral_lt_top hbox))

end Suitable

end FluidSingularSets
