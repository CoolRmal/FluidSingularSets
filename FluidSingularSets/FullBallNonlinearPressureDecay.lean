-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallNonlinearPressureSource

/-!
# Actual normalized nonlinear-pressure contraction with projected energy sources

Genuine local Stokes pressure decay and the actual velocity decomposition give
an all-scale centered nonlinear-pressure contraction. Every analytic source is
proved from actual suitable weak data; the scale normalization is literal.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The finite source coefficient in actual normalized nonlinear-pressure decay. -/
def fullBallNonlinearPressureSourceConstant : ℝ≥0∞ :=
  2 * (24 + 12 * fullBallHarmonicOscillationConstant (1 / 2)) *
    (ballH1ParabolicInterpolationConstant + fullBallHarmonicQuarticSourceCoefficient)

theorem fullBallNonlinearPressureSourceConstant_ne_top :
    fullBallNonlinearPressureSourceConstant ≠ ⊤ := by
  unfold fullBallNonlinearPressureSourceConstant fullBallHarmonicOscillationConstant
  finiteness [(volume_vec3Ball_lt_top (x := 0) (r := 1)).ne,
    ballH1ParabolicInterpolationConstant_ne_top,
    fullBallHarmonicQuarticSourceCoefficient_ne_top]

private theorem normalized_pressure_decay_algebra
    {a b P Q A C Z : ℝ≥0∞} (ha : a ≠ 0) (hat : a ≠ ⊤)
    (hb : b ≠ 0) (hbt : b ≠ ⊤)
    (h : Q ≤ A * a ^ (3 / 2 : ℝ) * Z + C * b ^ (5 / 2 : ℝ) * P) :
    (a * b) ^ (-3 / 2 : ℝ) * Q ≤
      A * b ^ (-3 / 2 : ℝ) * Z + C * b * (a ^ (-3 / 2 : ℝ) * P) := by
  have ha1 : a ^ (-3 / 2 : ℝ) * a ^ (3 / 2 : ℝ) = 1 := by
    rw [← ENNReal.rpow_add (-3 / 2) (3 / 2) ha hat]
    norm_num
  have hb1 : b ^ (-3 / 2 : ℝ) * b ^ (5 / 2 : ℝ) = b := by
    rw [← ENNReal.rpow_add (-3 / 2) (5 / 2) hb hbt]
    norm_num
  calc
    _ ≤ (a * b) ^ (-3 / 2 : ℝ) *
        (A * a ^ (3 / 2 : ℝ) * Z + C * b ^ (5 / 2 : ℝ) * P) :=
      mul_le_mul' le_rfl h
    _ = _ := by
      rw [ENNReal.mul_rpow_of_ne_top hat hbt, mul_add]
      calc
        _ = A * b ^ (-3 / 2 : ℝ) *
            (a ^ (-3 / 2 : ℝ) * a ^ (3 / 2 : ℝ)) * Z +
            C * (b ^ (-3 / 2 : ℝ) * b ^ (5 / 2 : ℝ)) *
              (a ^ (-3 / 2 : ℝ) * P) := by ring
        _ = _ := by rw [ha1, hb1, mul_one]

/-- The finite source coefficient after raising actual pressure oscillation to power 3/2. -/
def fullBallNonlinearPressurePowerSourceConstant : ℝ≥0∞ :=
  2 * fullBallNonlinearPressureSourceConstant ^ (3 / 2 : ℝ)

/-- The genuine centered harmonic contraction coefficient at pressure energy exponent 3/2. -/
def fullBallNonlinearPressurePowerContractionConstant : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
    fullBallHarmonicOscillationConstant (1 / 2) ^ (3 / 2 : ℝ)

/-- The genuine nonlinear-pressure energy source coefficient is finite. -/
theorem fullBallNonlinearPressurePowerSourceConstant_ne_top :
    fullBallNonlinearPressurePowerSourceConstant ≠ ⊤ := by
  unfold fullBallNonlinearPressurePowerSourceConstant
  exact ENNReal.mul_ne_top (by norm_num)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      fullBallNonlinearPressureSourceConstant_ne_top).ne

/-- The genuine centered harmonic pressure-energy contraction coefficient is finite. -/
theorem fullBallNonlinearPressurePowerContractionConstant_ne_top :
    fullBallNonlinearPressurePowerContractionConstant ≠ ⊤ := by
  unfold fullBallNonlinearPressurePowerContractionConstant fullBallHarmonicOscillationConstant
  finiteness [(volume_vec3Ball_lt_top (x := 0) (r := 1)).ne]

private theorem pressure_power_decay_algebra {P Q E X A C b : ℝ≥0∞}
    (h : Q ≤ A * b ^ (-3 / 2 : ℝ) * (E + X) + C * b * P) :
    Q ^ (3 / 2 : ℝ) ≤
      2 * A ^ (3 / 2 : ℝ) * b ^ (-9 / 4 : ℝ) *
        (E ^ (3 / 2 : ℝ) + X ^ (3 / 2 : ℝ)) +
      (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * C ^ (3 / 2 : ℝ) *
        b ^ (3 / 2 : ℝ) * P ^ (3 / 2 : ℝ) := by
  have hp := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 3 / 2)
  simp only [neg_div] at hp
  have hadd := ENNReal.rpow_add_le_mul_rpow_add_rpow
    (A * b ^ (-3 / 2 : ℝ) * (E + X)) (C * b * P)
      (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have hsource := ENNReal.rpow_add_le_mul_rpow_add_rpow E X
    (by norm_num : (1 : ℝ) ≤ 3 / 2)
  norm_num only [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] at hadd hsource
  have hsqrt : (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 2 := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  calc
    _ ≤ (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        ((A * b ^ (-3 / 2 : ℝ) * (E + X)) ^ (3 / 2 : ℝ) +
          (C * b * P) ^ (3 / 2 : ℝ)) := by
      simpa only [neg_div] using hp.trans hadd
    _ = (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        (A ^ (3 / 2 : ℝ) * b ^ (-9 / 4 : ℝ) * (E + X) ^ (3 / 2 : ℝ) +
          C ^ (3 / 2 : ℝ) * b ^ (3 / 2 : ℝ) * P ^ (3 / 2 : ℝ)) := by
      simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 2),
        ← ENNReal.rpow_mul]
      norm_num
    _ ≤ (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        (A ^ (3 / 2 : ℝ) * b ^ (-9 / 4 : ℝ) *
          ((2 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
            (E ^ (3 / 2 : ℝ) + X ^ (3 / 2 : ℝ))) +
          C ^ (3 / 2 : ℝ) * b ^ (3 / 2 : ℝ) * P ^ (3 / 2 : ℝ)) :=
      mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl hsource) le_rfl)
    _ = _ := by
      rw [mul_add]
      calc
        _ = ((2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (2 : ℝ≥0∞) ^ (1 / 2 : ℝ)) *
            A ^ (3 / 2 : ℝ) * b ^ (-9 / 4 : ℝ) *
              (E ^ (3 / 2 : ℝ) + X ^ (3 / 2 : ℝ)) +
            (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * C ^ (3 / 2 : ℝ) *
              b ^ (3 / 2 : ℝ) * P ^ (3 / 2 : ℝ) := by ring
        _ = _ := by rw [hsqrt]

section Suitable

variable {Ω : Set Vec3} {I : Set ℝ} {q c r s : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

/-- Actual nonlinear pressure decay has a linear contraction factor after scale normalization. -/
theorem suitable_fullBall_normalized_convective_oscillation_decay
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0))
    (hc : c ∈ Ioo (-1) 0) (hr : 0 < r) (hrhalf : r < 1 / 2)
    (hs : 0 < s) (hshalf : s ≤ 1 / 2) :
    fullBallNormalizedConvectiveOscillation u (r * s) 0 ≤
      fullBallNonlinearPressureSourceConstant * ENNReal.ofReal s ^ (-3 / 2 : ℝ) *
        (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c r 0 +
          fullBallOriginalEndpointSixSquareMoment u) +
      fullBallHarmonicOscillationConstant (1 / 2) * ENNReal.ofReal s *
        fullBallNormalizedConvectiveOscillation u r 0 := by
  let E := fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c r 0
  let X := fullBallOriginalEndpointSixSquareMoment u
  let C := fullBallHarmonicOscillationConstant (1 / 2)
  let γ := C * ENNReal.ofReal s ^ (5 / 2 : ℝ)
  have hJ : Ioo (-r ^ 2) 0 ⊆ Ioo (-1) 0 := by
    intro t ht
    have hh : r ^ 2 < 1 / 4 := by nlinarith
    exact ⟨by linarith [ht.1], ht.2⟩
  have hJr : -r ^ 2 < (0 : ℝ) := by nlinarith [sq_pos_of_pos hr]
  have hboxr : localBox Ω I (vec3Ball 0 1) (Ioo (-r ^ 2) 0) := by
    refine ⟨hbox.1, hbox.2.1, hbox.2.2.1, ordConnected_Ioo, ?_,
      (closure_mono hJ).trans hbox.2.2.2.2.2⟩
    rw [closure_Ioo hJr.ne]
    exact isCompact_Icc
  have hp := suitable_unitBallConvectiveOscillationMoment_backward_decay_localBox
    (τ := 0) hsol hr (by linarith) hs hshalf (by norm_num)
      (by simpa only [zero_sub] using hboxr)
  have hf := suitable_fullBall_original_four_square_moment_le_projected_energy_source
    hsol hbox hc hr hrhalf
  have hsone : ENNReal.ofReal s ≤ 1 := by
    exact (ENNReal.ofReal_le_ofReal (show s ≤ (1 : ℝ) by linarith)).trans_eq
      ENNReal.ofReal_one
  have hγ : γ ≤ C := by
    apply (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hsone (by norm_num))).trans_eq
    simp
  have hf' : unitBallVelocityFourSquareMoment u r (Ioo (-r ^ 2) 0) ≤
      2 * (ballH1ParabolicInterpolationConstant + fullBallHarmonicQuarticSourceCoefficient) *
        ENNReal.ofReal r ^ (3 / 2 : ℝ) * (E + X) := by
    apply hf.trans
    calc
      _ ≤ 2 * ENNReal.ofReal r ^ (3 / 2 : ℝ) *
          ((ballH1ParabolicInterpolationConstant + fullBallHarmonicQuarticSourceCoefficient) *
            E + (ballH1ParabolicInterpolationConstant + fullBallHarmonicQuarticSourceCoefficient) *
            X) := by
        gcongr
        · exact le_self_add
        · exact le_add_self
      _ = _ := by ring
  have hraw : unitBallConvectiveOscillationMoment u (r * s) (Ioo (-(r * s) ^ 2) 0) ≤
      fullBallNonlinearPressureSourceConstant * ENNReal.ofReal r ^ (3 / 2 : ℝ) * (E + X) +
        C * ENNReal.ofReal s ^ (5 / 2 : ℝ) *
          unitBallConvectiveOscillationMoment u r (Ioo (-r ^ 2) 0) := by
    have hp' : unitBallConvectiveOscillationMoment u (r * s) (Ioo (-(r * s) ^ 2) 0) ≤
        (24 + 12 * γ) * unitBallVelocityFourSquareMoment u r (Ioo (-r ^ 2) 0) +
          γ * unitBallConvectiveOscillationMoment u r (Ioo (-r ^ 2) 0) := by
      simpa only [zero_sub, γ, C] using hp
    apply hp'.trans
    apply (add_le_add (mul_le_mul'
      (add_le_add le_rfl (mul_le_mul' le_rfl hγ)) hf') le_rfl).trans_eq
    unfold fullBallNonlinearPressureSourceConstant
    dsimp [γ, C]
    ring
  have hn := normalized_pressure_decay_algebra
    (a := ENNReal.ofReal r) (b := ENNReal.ofReal s)
    (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top
    (ENNReal.ofReal_pos.mpr hs).ne' ENNReal.ofReal_ne_top hraw
  unfold fullBallNormalizedConvectiveOscillation
  simp only [zero_sub]
  rw [← ENNReal.ofReal_rpow_of_pos (mul_pos hr hs), ENNReal.ofReal_mul hr.le,
    ← ENNReal.ofReal_rpow_of_pos hr]
  exact hn

/-- Actual normalized nonlinear-pressure energy has its genuine all-scale contraction. -/
theorem suitable_fullBall_normalized_convective_oscillation_power_decay
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0))
    (hc : c ∈ Ioo (-1) 0) (hr : 0 < r) (hrhalf : r < 1 / 2)
    (hs : 0 < s) (hshalf : s ≤ 1 / 2) :
    fullBallNormalizedConvectiveOscillation u (r * s) 0 ^ (3 / 2 : ℝ) ≤
      fullBallNonlinearPressurePowerSourceConstant * ENNReal.ofReal s ^ (-9 / 4 : ℝ) *
        (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c r 0 ^ (3 / 2 : ℝ) +
          fullBallOriginalEndpointSixSquareMoment u ^ (3 / 2 : ℝ)) +
      fullBallNonlinearPressurePowerContractionConstant * ENNReal.ofReal s ^ (3 / 2 : ℝ) *
        fullBallNormalizedConvectiveOscillation u r 0 ^ (3 / 2 : ℝ) :=
  pressure_power_decay_algebra
    (suitable_fullBall_normalized_convective_oscillation_decay hsol hbox hc hr hrhalf hs hshalf)

/-- The exact actual iteration quantity controls every projected nonlinear-pressure source. -/
theorem suitable_fullBall_normalized_convective_oscillation_power_decay_iteration
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0))
    (hc : c ∈ Ioo (-1) 0) (hr : 0 < r) (hrhalf : r < 1 / 2)
    (hs : 0 < s) (hshalf : s ≤ 1 / 2) :
    fullBallNormalizedConvectiveOscillation u (r * s) 0 ^ (3 / 2 : ℝ) ≤
      fullBallNonlinearPressurePowerSourceConstant * ENNReal.ofReal s ^ (-9 / 4 : ℝ) *
        (fullBallEndpointIterationQuantity u D p (-1) 0 c r 0 ^ (3 / 2 : ℝ) +
          fullBallOriginalEndpointSixSquareMoment u ^ (3 / 2 : ℝ)) +
      fullBallNonlinearPressurePowerContractionConstant * ENNReal.ofReal s ^ (3 / 2 : ℝ) *
        fullBallEndpointIterationQuantity u D p (-1) 0 c r 0 := by
  apply (suitable_fullBall_normalized_convective_oscillation_power_decay
    hsol hbox hc hr hrhalf hs hshalf).trans
  apply add_le_add
  · exact mul_le_mul' le_rfl (add_le_add
      (ENNReal.rpow_le_rpow le_self_add (by norm_num)) le_rfl)
  · exact mul_le_mul' le_rfl le_add_self

/-- A finite actual fixed-quarter centered-pressure source coefficient. -/
def fullBallInitialConvectiveOscillationConstant : ℝ≥0∞ :=
  24 * ENNReal.ofReal ((1 / 4 : ℝ) ^ (-3 / 2 : ℝ)) *
    volume (vec3Ball (0 : Vec3) 1) ^ (1 / 6 : ℝ)

theorem fullBallInitialConvectiveOscillationConstant_ne_top :
    fullBallInitialConvectiveOscillationConstant ≠ ⊤ := by
  unfold fullBallInitialConvectiveOscillationConstant
  finiteness [(volume_vec3Ball_lt_top (x := 0) (r := 1)).ne]

/-- Actual suitable data bound every normalized centered nonlinear-pressure moment. -/
theorem suitable_fullBall_convective_oscillation_le_source
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hr : 0 < r)
    (hrhalf : r < 1 / 2) :
    fullBallNormalizedConvectiveOscillation u r 0 ≤
      24 * ENNReal.ofReal (r ^ (-3 / 2 : ℝ)) *
        volume (vec3Ball (0 : Vec3) 1) ^ (1 / 6 : ℝ) *
          fullBallOriginalEndpointSixSquareMoment u := by
  have hu : AEStronglyMeasurable u
      ((volume.restrict (vec3Ball 0 1)).prod (volume.restrict (Ioo (-1) 0))) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hsol.toData.aestronglyMeasurable_velocity hbox
  have hP : AEStronglyMeasurable
      (fun t ↦ (unitBallConvectivePressureCurve u t).val) (volume.restrict (Ioo (-1) 0)) :=
    unitBallMeanZeroL2.toSubmodule.subtypeL.continuous.comp_aestronglyMeasurable
      (unitBallConvectivePressureCurve_aestronglyMeasurable hu)
  have hw := ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)
  have hsix : ∀ᵐ t ∂volume.restrict (Ioo (-1) 0), MemLp (fun x ↦ u (x, t)) 6
      (volume.restrict (vec3Ball 0 1)) := by
    filter_upwards [slice_memLp_ae_of_sws hsol hbox, hw] with t ht htW
    exact fullUnitBallH1Vector_memLp_six ht.1 ht.2 htW
  have hcent := ballCenteredPressureL_eLpNorm_le_two 0
    hr (show r ≤ 1 by linarith) 1 hP
  rw [ballCenteredPressureL_eLpNorm_one_eq 0 (show r ≤ 1 by linarith) hP] at hcent
  have hsource := unitBallConvectivePressureCurve_eLpNorm_one_le_six_moment hu hsix
  have hnorm := eLpNorm_congr_enorm_ae
    (unitBallConvectivePressureCurve_aestronglyMeasurable hu) hP
    (.of_forall fun _ ↦ rfl) (p := 1)
  rw [← hnorm] at hcent
  have hJ : Ioo (-r ^ 2) 0 ⊆ Ioo (-1) 0 := by
    intro t ht
    have hh : r ^ 2 < 1 / 4 := by nlinarith
    exact ⟨by linarith [ht.1], ht.2⟩
  unfold fullBallNormalizedConvectiveOscillation
  simp only [zero_sub]
  calc
    _ ≤ ENNReal.ofReal (r ^ (-3 / 2 : ℝ)) *
        unitBallConvectiveOscillationMoment u r (Ioo (-1) 0) :=
      mul_le_mul' le_rfl (lintegral_mono_set hJ)
    _ ≤ ENNReal.ofReal (r ^ (-3 / 2 : ℝ)) *
        (2 * eLpNorm (unitBallConvectivePressureCurve u) 1 (volume.restrict (Ioo (-1) 0))) :=
      mul_le_mul' le_rfl hcent
    _ ≤ ENNReal.ofReal (r ^ (-3 / 2 : ℝ)) *
        (2 * (12 * volume (vec3Ball (0 : Vec3) 1) ^ (1 / 6 : ℝ) *
          fullBallOriginalEndpointSixSquareMoment u)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hsource)
    _ = _ := by ring

/-- Actual suitable data give the initial normalized centered nonlinear-pressure bound. -/
theorem suitable_fullBall_initial_convective_oscillation_le_source
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) :
    fullBallNormalizedConvectiveOscillation u (1 / 4) 0 ≤
      fullBallInitialConvectiveOscillationConstant * fullBallOriginalEndpointSixSquareMoment u :=
  suitable_fullBall_convective_oscillation_le_source hsol hbox (by norm_num) (by norm_num)

/-- The literal normalized nonlinear-pressure moment is finite at every actual inner scale. -/
theorem suitable_fullBall_convective_oscillation_lt_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hr : 0 < r)
    (hrhalf : r < 1 / 2) :
    fullBallNormalizedConvectiveOscillation u r 0 < ⊤ := by
  apply (suitable_fullBall_convective_oscillation_le_source hsol hbox hr hrhalf).trans_lt
  apply ENNReal.mul_lt_top
  · finiteness [(volume_vec3Ball_lt_top (x := 0) (r := 1)).ne]
  · exact suitable_fullBall_original_endpoint_six_square_moment_lt_top hsol hbox


end Suitable

end FluidSingularSets
