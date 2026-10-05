-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UniformMixedSlices

/-!
# Actual bounded joint fields and spatial L² classes

On a finite spatial measure, a truly essentially bounded jointly measurable
field has genuine good spatial L² slices and an essentially bounded curve of
those actual classes. The good-slice conclusion is proved separately, so an
exceptional zero branch cannot substitute for actual spatial integrability.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- A joint essential bound gives genuine spatial L² slices on a common time set. -/
theorem actualSlice_memLp_two_of_joint_uniform_bound
    {A T E : Type*} [MeasurableSpace A] [MeasurableSpace T] [NormedAddCommGroup E]
    {μ : Measure A} [IsFiniteMeasure μ] {ν : Measure T} [SFinite ν]
    {F : A × T → E} (hF : AEStronglyMeasurable F (μ.prod ν)) {C : ℝ}
    (hbound : ∀ᵐ z ∂μ.prod ν, ‖F z‖ ≤ C) :
    ∀ᵐ t ∂ν, MemLp (fun x ↦ F (x, t)) 2 μ := by
  have hb := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae hbound)
  filter_upwards [hF.prodMk_right, hb] with t ht hbt
  exact MemLp.of_bound ht C hbt

/-- The genuine spatial L² curve satisfies its true uniform radius-volume bound. -/
theorem actualSliceLp_eLpNorm_top_le_of_joint_uniform_bound
    {A T E : Type*} [MeasurableSpace A] [MeasurableSpace T]
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure A} [IsFiniteMeasure μ] [IsSeparable μ] {ν : Measure T} [SFinite ν]
    {F : A × T → E} (hF : AEStronglyMeasurable F (μ.prod ν)) {C : ℝ}
    (hbound : ∀ᵐ z ∂μ.prod ν, ‖F z‖ ≤ C) :
    eLpNorm (actualSliceLp (μ := μ) (p := 2) F) ⊤ ν ≤
      ENNReal.ofReal C * μ univ ^ (1 / 2 : ℝ) := by
  have hb := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae hbound)
  have hg := actualSlice_memLp_two_of_joint_uniform_bound hF hbound
  rw [eLpNorm_exponent_top (aestronglyMeasurable_actualSliceLp hF (by norm_num))]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  filter_upwards [hF.prodMk_right, hb, hg] with t ht hbt hgt
  rw [actualSliceLp_enorm F t hgt]
  have he := eLpNorm_le_of_ae_bound (p := 2) ht hbt
  simpa only [ENNReal.toReal_ofNat, one_div, mul_comm] using he

/-- True joint L∞ data yield genuine spatial L² slices and actual time L∞ classes. -/
theorem actualSliceLp_memLp_top_of_joint_memLp_top
    {A T E : Type*} [MeasurableSpace A] [MeasurableSpace T]
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure A} [IsFiniteMeasure μ] [IsSeparable μ] {ν : Measure T} [SFinite ν]
    {F : A × T → E} (hF : MemLp F ⊤ (μ.prod ν)) :
    (∀ᵐ t ∂ν, MemLp (fun x ↦ F (x, t)) 2 μ) ∧
      MemLp (actualSliceLp (μ := μ) (p := 2) F) ⊤ ν := by
  have he : eLpNormEssSup F (μ.prod ν) < ⊤ := by
    simpa only [eLpNorm_exponent_top hF.aestronglyMeasurable] using hF.eLpNorm_lt_top
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp he
  change ∀ᵐ z ∂μ.prod ν, ‖F z‖₊ ≤ C at hC
  have hb : ∀ᵐ z ∂μ.prod ν, ‖F z‖ ≤ (C : ℝ) := hC.mono fun _ hx ↦ by exact_mod_cast hx
  refine ⟨actualSlice_memLp_two_of_joint_uniform_bound hF.aestronglyMeasurable hb, ?_⟩
  apply memLp_iff.mpr
  exact (actualSliceLp_eLpNorm_top_le_of_joint_uniform_bound
    hF.aestronglyMeasurable hb).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top μ univ)))

end FluidSingularSets
