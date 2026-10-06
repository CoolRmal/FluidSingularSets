-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallNativePressureClasses
public import FluidSingularSets.ProjectedGaussianSourceEnergy

/-!
# Actual iteration finiteness and nonlinear pressure energy algebra

The genuine native time L¹ pressure class gives finite centered oscillation.
The literal iteration quantity controls its two-thirds pressure power and the
square root of slice energy, yielding the exact seven-sixths flux exponent.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual native centered pressure and suitable energy make the iteration quantity finite. -/
theorem suitable_fullBall_endpoint_iteration_quantity_lt_top
    {Ω : Set Vec3} {I : Set ℝ} {q c r : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hrhalf : r < 1 / 2) :
    fullBallEndpointIterationQuantity u D p (-1) 0 c r 0 < ⊤ := by
  have ht : Ioo (-r ^ 2) 0 ⊆ Ioo (-1) 0 := by
    intro t htt
    have hs : r ^ 2 < 1 / 4 := by nlinarith
    exact ⟨by linarith only [htt.1, hs], htt.2⟩
  have hn := suitable_fullBall_native_convective_pressure_memLp_one hsol hbox
  have hP : MemLp (fun t ↦ (unitBallConvectivePressureCurve u t).val) 1
      (volume.restrict (Ioo (-r ^ 2) 0)) :=
    (hn.continuousLinearMap_comp unitBallMeanZeroL2.toSubmodule.subtypeL).mono_measure
      (Measure.restrict_mono ht le_rfl)
  have hm : unitBallConvectiveOscillationMoment u r (Ioo (-r ^ 2) 0) < ⊤ := by
    have hb := ballCenteredPressureL_memLp 0 (by linarith : r ≤ 1) hP
    have hf := hb.eLpNorm_lt_top
    rw [ballCenteredPressureL_eLpNorm_one_eq 0 (by linarith : r ≤ 1)
      hP.aestronglyMeasurable] at hf
    exact hf
  have hPf : fullBallNormalizedConvectiveOscillation u r 0 < ⊤ := by
    unfold fullBallNormalizedConvectiveOscillation
    simpa only [zero_sub] using ENNReal.mul_lt_top ENNReal.ofReal_lt_top hm
  unfold fullBallEndpointIterationQuantity
  exact ENNReal.add_lt_top.mpr
    ⟨suitable_fullBall_normalized_projected_iteration_energy_lt_top hsol hbox hc hr hrhalf,
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hPf.ne⟩

/-- The literal normalized pressure is bounded by the iteration quantity to power two thirds. -/
theorem fullBallNormalizedConvectiveOscillation_le_iteration_twoThirds
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c r τ : ℝ) :
    fullBallNormalizedConvectiveOscillation u r τ ≤
      fullBallEndpointIterationQuantity u D p a b c r τ ^ (2 / 3 : ℝ) := by
  calc
    _ = (fullBallNormalizedConvectiveOscillation u r τ ^ (3 / 2 : ℝ)) ^
        (2 / 3 : ℝ) := by
      rw [← ENNReal.rpow_mul]
      norm_num
    _ ≤ _ := ENNReal.rpow_le_rpow le_add_self (by norm_num)

/-- The true unnormalized pressure moment has exactly the radius factor three halves. -/
theorem unitBallConvectiveOscillationMoment_eq_radius_normalized
    (u : ParabolicPoint → Vec3) {r : ℝ} (hr : 0 < r) (τ : ℝ) :
    unitBallConvectiveOscillationMoment u r (Ioo (τ - r ^ 2) τ) =
      ENNReal.ofReal r ^ (3 / 2 : ℝ) * fullBallNormalizedConvectiveOscillation u r τ := by
  have h0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  unfold fullBallNormalizedConvectiveOscillation
  rw [← ENNReal.ofReal_rpow_of_pos hr, ← mul_assoc,
    ← ENNReal.rpow_add (3 / 2) (-3 / 2) h0 ENNReal.ofReal_ne_top]
  norm_num

/-- The actual pressure moment times slice square root has the exact radius-square energy budget. -/
theorem fullBall_pressure_oscillation_energy_product_le_iteration
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c τ : ℝ) {r : ℝ} (hr : 0 < r) :
    unitBallConvectiveOscillationMoment u r (Ioo (τ - r ^ 2) τ) *
      fullBallProjectedIterationSliceEnergy u D p a b c r τ ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal r ^ 2 * fullBallEndpointIterationQuantity u D p a b c r τ ^
          (7 / 6 : ℝ) := by
  let Q := fullBallEndpointIterationQuantity u D p a b c r τ
  have hM : fullBallProjectedIterationSliceEnergy u D p a b c r τ ≤
      ENNReal.ofReal r * Q :=
    (fullBallProjectedIterationSliceEnergy_le_radius_energy u D p a b c τ hr).trans
      (mul_le_mul' le_rfl le_self_add)
  have hMr := ENNReal.rpow_le_rpow hM (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at hMr
  rw [unitBallConvectiveOscillationMoment_eq_radius_normalized u hr τ]
  calc
    _ ≤ (ENNReal.ofReal r ^ (3 / 2 : ℝ) * Q ^ (2 / 3 : ℝ)) *
        (ENNReal.ofReal r ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ)) :=
      mul_le_mul' (mul_le_mul' le_rfl
        (fullBallNormalizedConvectiveOscillation_le_iteration_twoThirds u D p a b c r τ)) hMr
    _ = _ := by
      have hR := ENNReal.rpow_add_of_nonneg (x := ENNReal.ofReal r)
        (3 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num)
      have hQ := ENNReal.rpow_add_of_nonneg (x := Q)
        (2 / 3 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num)
      norm_num only [show (3 / 2 + 1 / 2 : ℝ) = 2 by norm_num,
        show (2 / 3 + 1 / 2 : ℝ) = 7 / 6 by norm_num, ENNReal.rpow_ofNat] at hR hQ
      rw [hR, hQ]
      ring

end FluidSingularSets
