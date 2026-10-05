-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.BallStokesPressureSources
public import FluidSingularSets.EndpointVelocityInterpolation
public import FluidSingularSets.SliceLpMoments

/-!
# Actual physical-ball pressure curves and endpoint mixed bounds

These are the true Stokes projections of the conditional actual tensor and
weak-gradient slices. Genuine good slices identify them with the physical
nonlinear and viscous pressures. Their time L¹ and L² bounds follow from the
actual velocity L² L⁶ moment and weak-gradient square energy.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual nonlinear Stokes pressure curve on the physical ball. -/
def ballConvectivePressureCurve (x : Vec3) {r : ℝ} (hr : 0 < r)
    (u : ParabolicPoint → Vec3) (t : ℝ) : Lp ℝ 2 (volume.restrict (vec3Ball x r)) :=
  ballTensorPressureL x hr (actualSliceLp (μ := volume.restrict (vec3Ball x r)) (p := 2)
    (fun z : Vec3 × ℝ ↦ stokesOuterProduct (u z) (u z)) t)

/-- The true viscous Stokes pressure curve with its physical momentum sign. -/
def ballViscousPressureCurve (x : Vec3) {r : ℝ} (hr : 0 < r)
    (D : ParabolicPoint → Fin 3 → Vec3) (t : ℝ) :
    Lp ℝ 2 (volume.restrict (vec3Ball x r)) :=
  ballTensorPressureL x hr (-actualSliceLp (μ := volume.restrict (vec3Ball x r)) (p := 2)
    (fun z : Vec3 × ℝ ↦ stokesRawGradientMatrix (fun y ↦ D (y, z.2)) z.1) t)

/-- Every genuine spatial L⁴ slice has exactly its physical nonlinear pressure. -/
theorem ballConvectivePressureCurve_eq (x : Vec3) {r : ℝ} (hr : 0 < r)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : MemLp (fun y ↦ u (y, t)) 4 (volume.restrict (vec3Ball x r))) :
    ballConvectivePressureCurve x hr u t = ballNonlinearPressure x hr (fun y ↦ u (y, t)) hu := by
  unfold ballConvectivePressureCurve actualSliceLp
  rw [dite_eq_left (stokesConvectiveTensor_memLp (fun y ↦ u (y, t)) hu)]
  rfl

/-- Every genuine spatial weak-gradient slice has exactly its physical viscous pressure. -/
theorem ballViscousPressureCurve_eq (x : Vec3) {r : ℝ} (hr : 0 < r)
    (D : ParabolicPoint → Fin 3 → Vec3) (t : ℝ)
    (hD : MemLp (fun y ↦ D (y, t)) 2 (volume.restrict (vec3Ball x r))) :
    ballViscousPressureCurve x hr D t = ballRawViscousPressure x hr (fun y ↦ D (y, t)) hD := by
  unfold ballViscousPressureCurve actualSliceLp
  rw [dite_eq_left (stokesRawGradientMatrix_memLp (fun y ↦ D (y, t)) hD)]
  rfl

/-- Genuine joint velocity measurability gives the actual pressure curve measurability. -/
theorem ballConvectivePressureCurve_aestronglyMeasurable (x : Vec3) {r : ℝ} (hr : 0 < r)
    {ν : Measure ℝ} [SFinite ν] {u : ParabolicPoint → Vec3}
    (hu : AEStronglyMeasurable u ((volume.restrict (vec3Ball x r)).prod ν)) :
    AEStronglyMeasurable (ballConvectivePressureCurve x hr u) ν := by
  have hT : AEStronglyMeasurable (fun z : Vec3 × ℝ ↦ stokesOuterProduct (u z) (u z))
      ((volume.restrict (vec3Ball x r)).prod ν) :=
    stokesOuterProduct_continuous.comp_aestronglyMeasurable (hu.prodMk hu)
  exact (ballTensorPressureL x hr).continuous.comp_aestronglyMeasurable
    (aestronglyMeasurable_actualSliceLp hT (by norm_num))

/-- Genuine joint weak-gradient measurability gives the actual viscous curve measurability. -/
theorem ballViscousPressureCurve_aestronglyMeasurable (x : Vec3) {r : ℝ} (hr : 0 < r)
    {ν : Measure ℝ} [SFinite ν] {D : ParabolicPoint → Fin 3 → Vec3}
    (hD : AEStronglyMeasurable D ((volume.restrict (vec3Ball x r)).prod ν)) :
    AEStronglyMeasurable (ballViscousPressureCurve x hr D) ν := by
  have hmap : Continuous (fun A : Fin 3 → Vec3 ↦
      WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 ↦ A ij.2 ij.1)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 × Fin 3 ↦ ℝ)).comp
    exact continuous_pi (fun ij ↦ (continuous_apply ij.1).comp (continuous_apply ij.2))
  have hT : AEStronglyMeasurable
      (fun z : Vec3 × ℝ ↦ stokesRawGradientMatrix (fun y ↦ D (y, z.2)) z.1)
      ((volume.restrict (vec3Ball x r)).prod ν) := hmap.comp_aestronglyMeasurable hD
  exact (ballTensorPressureL x hr).continuous.comp_aestronglyMeasurable
    (aestronglyMeasurable_actualSliceLp hT (by norm_num)).neg

/-- The actual nonlinear curve has the genuine spatial L⁴ bound with constant twelve. -/
theorem ballConvectivePressureCurve_enorm_le_four (x : Vec3) {r : ℝ} (hr : 0 < r)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : MemLp (fun y ↦ u (y, t)) 4 (volume.restrict (vec3Ball x r))) :
    ‖ballConvectivePressureCurve x hr u t‖ₑ ≤
      12 * eLpNorm (fun y ↦ u (y, t)) 4 (volume.restrict (vec3Ball x r)) ^ 2 := by
  rw [ballConvectivePressureCurve_eq x hr u t hu, ← ofReal_norm]
  have hb := ENNReal.ofReal_le_ofReal (ballNonlinearPressure_norm_le x hr (fun y ↦ u (y, t)) hu)
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hu.eLpNorm_ne_top] using hb

/-- Actual finite-volume interpolation gives the genuine endpoint spatial pressure bound. -/
theorem ballConvectivePressureCurve_enorm_le_six (x : Vec3) {r : ℝ} (hr : 0 < r)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : MemLp (fun y ↦ u (y, t)) 6 (volume.restrict (vec3Ball x r))) :
    ‖ballConvectivePressureCurve x hr u t‖ₑ ≤
      12 * volume (vec3Ball x r) ^ (1 / 6 : ℝ) *
        eLpNorm (fun y ↦ u (y, t)) 6 (volume.restrict (vec3Ball x r)) ^ 2 := by
  let : IsFiniteMeasure (volume.restrict (vec3Ball x r)) :=
    isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  have hb := ballConvectivePressureCurve_enorm_le_four x hr u t
    (hu.mono_exponent (by norm_num))
  have hc := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 4) (q := 6)
    (by norm_num) hu.aestronglyMeasurable
  norm_num only [ENNReal.toReal_ofNat, Measure.restrict_apply_univ] at hc
  have hs := pow_le_pow_left' hc 2
  rw [mul_pow, ← ENNReal.rpow_natCast (volume (vec3Ball x r) ^ (1 / 12 : ℝ)) 2,
    ← ENNReal.rpow_mul] at hs
  norm_num only [show (1 / 12 : ℝ) * 2 = 1 / 6 by norm_num] at hs
  exact hb.trans ((mul_le_mul' le_rfl hs).trans_eq (by ring))

/-- The genuine nonlinear time L¹ norm is bounded by the actual endpoint mixed moment. -/
theorem ballConvectivePressureCurve_eLpNorm_one_le_six_moment
    (x : Vec3) {r : ℝ} (hr : 0 < r) {ν : Measure ℝ} [SFinite ν]
    {u : ParabolicPoint → Vec3}
    (hu : AEStronglyMeasurable u ((volume.restrict (vec3Ball x r)).prod ν))
    (hus : ∀ᵐ t ∂ν, MemLp (fun y ↦ u (y, t)) 6 (volume.restrict (vec3Ball x r))) :
    eLpNorm (ballConvectivePressureCurve x hr u) 1 ν ≤
      12 * volume (vec3Ball x r) ^ (1 / 6 : ℝ) *
        ∫⁻ t, eLpNorm (fun y ↦ u (y, t)) 6 (volume.restrict (vec3Ball x r)) ^ 2 ∂ν := by
  rw [eLpNorm_one_eq_lintegral_enorm (ballConvectivePressureCurve_aestronglyMeasurable x hr hu)]
  calc
    _ ≤ ∫⁻ t, 12 * volume (vec3Ball x r) ^ (1 / 6 : ℝ) *
        eLpNorm (fun y ↦ u (y, t)) 6 (volume.restrict (vec3Ball x r)) ^ 2 ∂ν :=
      lintegral_mono_ae (hus.mono fun t ht ↦ ballConvectivePressureCurve_enorm_le_six x hr u t ht)
    _ = _ := lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) volume_vec3Ball_lt_top.ne).ne)

/-- Genuine finite endpoint velocity cost gives the actual nonlinear pressure L¹ class. -/
theorem ballConvectivePressureCurve_memLp_one_of_six_moment
    (x : Vec3) {r : ℝ} (hr : 0 < r) {ν : Measure ℝ} [SFinite ν]
    {u : ParabolicPoint → Vec3}
    (hu : AEStronglyMeasurable u ((volume.restrict (vec3Ball x r)).prod ν))
    (hus : ∀ᵐ t ∂ν, MemLp (fun y ↦ u (y, t)) 6 (volume.restrict (vec3Ball x r)))
    (hfin : (∫⁻ t, eLpNorm (fun y ↦ u (y, t)) 6 (volume.restrict (vec3Ball x r)) ^ 2 ∂ν) < ⊤) :
    MemLp (ballConvectivePressureCurve x hr u) 1 ν := by
  exact (ballConvectivePressureCurve_eLpNorm_one_le_six_moment x hr hu hus).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) volume_vec3Ball_lt_top.ne)) hfin)

/-- The actual viscous curve has the genuine spatial weak-gradient bound with constant twelve. -/
theorem ballViscousPressureCurve_enorm_le_two (x : Vec3) {r : ℝ} (hr : 0 < r)
    (D : ParabolicPoint → Fin 3 → Vec3) (t : ℝ)
    (hD : MemLp (fun y ↦ D (y, t)) 2 (volume.restrict (vec3Ball x r))) :
    ‖ballViscousPressureCurve x hr D t‖ₑ ≤
      12 * eLpNorm (fun y ↦ D (y, t)) 2 (volume.restrict (vec3Ball x r)) := by
  rw [ballViscousPressureCurve_eq x hr D t hD, ← ofReal_norm]
  have hb := ENNReal.ofReal_le_ofReal (ballRawViscousPressure_norm_le x hr (fun y ↦ D (y, t)) hD)
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_toReal hD.eLpNorm_ne_top] using hb

/-- The actual viscous time L² norm is bounded by the literal gradient energy moment. -/
theorem ballViscousPressureCurve_eLpNorm_two_le_gradient_moment
    (x : Vec3) {r : ℝ} (hr : 0 < r) {ν : Measure ℝ} [SFinite ν]
    {D : ParabolicPoint → Fin 3 → Vec3}
    (hD : AEStronglyMeasurable D ((volume.restrict (vec3Ball x r)).prod ν))
    (hDs : ∀ᵐ t ∂ν, MemLp (fun y ↦ D (y, t)) 2 (volume.restrict (vec3Ball x r))) :
    eLpNorm (ballViscousPressureCurve x hr D) 2 ν ≤
      12 * (∫⁻ t, eLpNorm (fun y ↦ D (y, t)) 2 (volume.restrict (vec3Ball x r)) ^ 2 ∂ν)
        ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (ballViscousPressureCurve_aestronglyMeasurable x hr hD)]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  have hb : (∫⁻ t, ‖ballViscousPressureCurve x hr D t‖ₑ ^ 2 ∂ν) ≤
      12 ^ 2 * ∫⁻ t, eLpNorm (fun y ↦ D (y, t)) 2 (volume.restrict (vec3Ball x r)) ^ 2 ∂ν := by
    calc
      _ ≤ ∫⁻ t, (12 * eLpNorm (fun y ↦ D (y, t)) 2
          (volume.restrict (vec3Ball x r))) ^ 2 ∂ν :=
        lintegral_mono_ae (hDs.mono fun t ht ↦
          pow_le_pow_left' (ballViscousPressureCurve_enorm_le_two x hr D t ht) 2)
      _ = _ := by
        simp only [mul_pow]
        exact lintegral_const_mul' _ _ (by norm_num)
  have hs := ENNReal.rpow_le_rpow hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast _ 2,
    ← ENNReal.rpow_mul] at hs
  norm_num only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one] at hs
  exact hs

end FluidSingularSets
