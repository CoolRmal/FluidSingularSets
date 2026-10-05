-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.Specification
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The mixed gradient cost of a suitable weak solution

Spatial Hölder bounds the squared spatial `L^(12/7)` norm by the spatial dissipation,
with the factor `volume(U)^(1/6)`. Tonelli then gives the corresponding bound integrated
in time. This proves that the mixed gradient cost is finite on compact product sets for
the actual energy class in the suitable weak solution interface.

Here the gradient uses the operator norm of the derivative, as in that energy class.
The critical Sobolev estimate, pressure decay, and local energy recurrence require
additional arguments and are not conclusions of this file.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

section Holder

variable {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup F] {μ : Measure α} {ν : Measure β}

/-- The mixed spatial exponent gives a sixth-root volume factor in the dissipation bound. -/
theorem mixedGradientSlice_le_dissipation {f : α → F}
    (hf : AEStronglyMeasurable f μ) :
    (∫⁻ x, ‖f x‖ₑ ^ (12 / 7 : ℝ) ∂μ) ^ (7 / 6 : ℝ) ≤
      μ univ ^ (1 / 6 : ℝ) * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  have h := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ
    (p := (12 / 7 : ℝ)) (q := (2 : ℝ)) (by norm_num) (by norm_num) hf
  have h₂ := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  simp only [eLpNorm'_eq_lintegral_enorm] at h₂
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)] at h₂
  simp only [← ENNReal.rpow_mul] at h₂
  norm_num at h₂
  simpa only [mul_comm, ENNReal.rpow_ofNat] using h₂

/-- Joint almost everywhere strong measurability implies spatial slice measurability
for almost every time. -/
theorem aestronglyMeasurable_spatial_slice_ae [SFinite μ] [SFinite ν]
    {f : α × β → F} (hf : AEStronglyMeasurable f (μ.prod ν)) :
    ∀ᵐ t ∂ν, AEStronglyMeasurable (fun x ↦ f (x, t)) μ := by
  have hs := hf.prod_swap
  filter_upwards [Measure.ae_ae_of_ae_prod hs.ae_eq_mk] with t ht
  exact (aestronglyMeasurable_congr ht).2
    (hs.stronglyMeasurable_mk.comp_measurable measurable_prodMk_left).aestronglyMeasurable

/-- The spatial Hölder bound integrated in time, for any jointly measurable field. -/
theorem mixedGradientIntegral_le_dissipation [SFinite μ] [SFinite ν]
    {f : α × β → F} (hf : AEStronglyMeasurable f (μ.prod ν)) :
    (∫⁻ t, (∫⁻ x, ‖f (x, t)‖ₑ ^ (12 / 7 : ℝ) ∂μ) ^ (7 / 6 : ℝ) ∂ν) ≤
      μ univ ^ (1 / 6 : ℝ) * ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂μ.prod ν := by
  have hnorm : AEMeasurable (fun z ↦ ‖f z‖ₑ ^ (2 : ℝ)) (μ.prod ν) :=
    hf.enorm.pow_const _
  rw [lintegral_prod_symm _ hnorm,
    ← lintegral_const_mul'' _ hnorm.lintegral_prod_left']
  refine lintegral_mono_ae ?_
  filter_upwards [aestronglyMeasurable_spatial_slice_ae hf] with t ht
  exact mixedGradientSlice_le_dissipation ht

end Holder

/-- Time integral of the squared spatial `L^(12/7)` norm of the gradient. -/
def mixedGradientIntegral (D : SpaceTime → (Space →L[ℝ] Space))
    (U : Set Space) (J : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ t in J, (∫⁻ x in U, ‖D (x, t)‖ₑ ^ (12 / 7 : ℝ)) ^ (7 / 6 : ℝ)

/-- Suitable weak solutions satisfy the spatial Hölder dissipation bound on every
product set where their local energy class applies. -/
theorem suitableWeakSolution_mixedGradientIntegral_le
    {Ω : Set Space} {I : Set ℝ} {q : ℝ≥0}
    (sol : CKNChallenge.LocalWeakNSESolution Ω I q)
    (U : Set Space) (J : Set ℝ)
    (hUJ : IsOpen U ∧ CKNChallenge.IsCompactlyContained U Ω ∧
      OrdConnected J ∧ CKNChallenge.IsCompactlyContained J I) :
    mixedGradientIntegral sol.Dxu U J ≤
      volume U ^ (1 / 6 : ℝ) * ∫⁻ z in U ×ˢ J, ‖sol.Dxu z‖ₑ ^ (2 : ℝ) := by
  have hf := (sol.energyRegularity U J hUJ).gradientMemLp.aestronglyMeasurable
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hf
  simpa only [mixedGradientIntegral, Measure.restrict_apply_univ, Measure.prod_restrict,
    ← Measure.volume_eq_prod]
    using mixedGradientIntegral_le_dissipation hf

/-- The mixed gradient cost is finite on every compact product set of an actual
suitable weak solution. No regularity or mixed-gradient estimate is assumed. -/
theorem suitableWeakSolution_mixedGradientIntegral_lt_top
    {Ω : Set Space} {I : Set ℝ} {q : ℝ≥0}
    (sol : CKNChallenge.LocalWeakNSESolution Ω I q)
    (U : Set Space) (J : Set ℝ)
    (hUJ : IsOpen U ∧ CKNChallenge.IsCompactlyContained U Ω ∧
      OrdConnected J ∧ CKNChallenge.IsCompactlyContained J I) :
    mixedGradientIntegral sol.Dxu U J < ∞ := by
  apply lt_of_le_of_lt (suitableWeakSolution_mixedGradientIntegral_le sol U J hUJ)
  apply ENNReal.mul_lt_top
  · apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    exact (lt_of_le_of_lt (measure_mono subset_closure) hUJ.2.1.1.measure_lt_top).ne
  · exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (sol.energyRegularity U J hUJ).gradientMemLp.eLpNorm_lt_top

/-- In three spatial dimensions the Hölder volume factor scales as the square root
of the radius. -/
theorem volume_ball_rpow_one_sixth (x : Space) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball x r) ^ (1 / 6 : ℝ) =
      ENNReal.ofReal r ^ (1 / 2 : ℝ) *
        volume (Metric.ball (0 : Space) 1) ^ (1 / 6 : ℝ) := by
  rw [Measure.addHaar_ball volume x hr, finrank_euclideanSpace]
  simp only [Fintype.card_fin]
  rw [ENNReal.ofReal_pow hr,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 6),
    ← ENNReal.rpow_ofNat, ← ENNReal.rpow_mul]
  norm_num

/-- The normalized mixed gradient cost is bounded by a universal constant times
normalized dissipation, for actual suitable weak solutions. -/
theorem suitableWeakSolution_scaledMixedGradient_le_dissipation
    {Ω : Set Space} {I : Set ℝ} {q : ℝ≥0}
    (sol : CKNChallenge.LocalWeakNSESolution Ω I q)
    (x : Space) {r : ℝ} (hr : 0 < r) (J : Set ℝ)
    (hball : CKNChallenge.IsCompactlyContained (Metric.ball x r) Ω)
    (hJ : OrdConnected J ∧ CKNChallenge.IsCompactlyContained J I) :
    ENNReal.ofReal r ^ (-3 / 2 : ℝ) * mixedGradientIntegral sol.Dxu (Metric.ball x r) J ≤
      volume (Metric.ball (0 : Space) 1) ^ (1 / 6 : ℝ) *
        (ENNReal.ofReal r ^ (-1 : ℝ) *
          ∫⁻ z in Metric.ball x r ×ˢ J, ‖sol.Dxu z‖ₑ ^ (2 : ℝ)) := by
  have h := suitableWeakSolution_mixedGradientIntegral_le sol (Metric.ball x r) J
    ⟨Metric.isOpen_ball, hball, hJ⟩
  have hscale : ENNReal.ofReal r ^ (-3 / 2 : ℝ) * ENNReal.ofReal r ^ (1 / 2 : ℝ) =
      ENNReal.ofReal r ^ (-1 : ℝ) := by
    rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_ne_zero_iff.mpr hr)
      ENNReal.ofReal_ne_top]
    norm_num
  calc
    _ ≤ ENNReal.ofReal r ^ (-3 / 2 : ℝ) *
        (volume (Metric.ball x r) ^ (1 / 6 : ℝ) *
          ∫⁻ z in Metric.ball x r ×ˢ J, ‖sol.Dxu z‖ₑ ^ (2 : ℝ)) :=
      by gcongr
    _ = _ := by
      rw [volume_ball_rpow_one_sixth x hr.le]
      calc
        _ = (ENNReal.ofReal r ^ (-3 / 2 : ℝ) * ENNReal.ofReal r ^ (1 / 2 : ℝ)) *
            (volume (Metric.ball (0 : Space) 1) ^ (1 / 6 : ℝ) *
              ∫⁻ z in Metric.ball x r ×ˢ J, ‖sol.Dxu z‖ₑ ^ (2 : ℝ)) := by ac_rfl
        _ = _ := by rw [hscale]; ac_rfl

end FluidSingularSets
