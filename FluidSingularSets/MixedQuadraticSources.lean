-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.MixedWeightedVelocity

/-!
# Genuine quadratic mixed source bounds

An actual source dominated by the spatial velocity times its true L² slice
norm has time L¹ spatial L² control quadratic in the velocity's time L²
spatial L² norm. This is the mixed estimate used for the harmonic Hessian and
nonlinear pressure terms of the projected energy inequality.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- A true quadratic velocity domination bounds the actual source class time L¹ norm. -/
theorem actualSliceLp_one_le_of_quadratic_velocity_bound
    {A T E : Type*} [MeasurableSpace A] [MeasurableSpace T]
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure A} [SFinite μ] [IsSeparable μ] {ν : Measure T} [SFinite ν]
    {U : A × T → E} {F : A × T → ℝ}
    (hF : AEStronglyMeasurable F (μ.prod ν))
    (hUs : ∀ᵐ t ∂ν, MemLp (fun x ↦ U (x, t)) 2 μ)
    (hUc : MemLp (actualSliceLp (μ := μ) (p := 2) U) 2 ν)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, ‖F (x, t)‖ ≤
      (C * ‖actualSliceLp (μ := μ) (p := 2) U t‖) * ‖U (x, t)‖) :
    (∀ᵐ t ∂ν, MemLp (fun x ↦ F (x, t)) 2 μ) ∧
      eLpNorm (actualSliceLp (μ := μ) (p := 2) F) 1 ν ≤
        ENNReal.ofReal C * eLpNorm (actualSliceLp (μ := μ) (p := 2) U) 2 ν ^ 2 := by
  have hgood : ∀ᵐ t ∂ν, MemLp (fun x ↦ F (x, t)) 2 μ := by
    filter_upwards [hF.prodMk_right, hUs, hbound] with t hft hut hbt
    exact hut.of_le_mul hft hbt
  have hFc := aestronglyMeasurable_actualSliceLp hF (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have hnorm : ∀ᵐ t ∂ν, ‖actualSliceLp (μ := μ) (p := 2) F t‖ₑ ≤
      ENNReal.ofReal C * ‖(‖actualSliceLp (μ := μ) (p := 2) U t‖ *
        ‖actualSliceLp (μ := μ) (p := 2) U t‖ : ℝ)‖ₑ := by
    filter_upwards [hgood, hUs, hbound] with t hft hut hbt
    rw [actualSliceLp_enorm F t hft]
    have hb := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hft.aestronglyMeasurable hbt 2
    rw [ENNReal.ofReal_mul hC, ofReal_norm,
      ← actualSliceLp_enorm U t hut] at hb
    simpa only [enorm_mul, enorm_norm, mul_assoc] using hb
  have hsq : eLpNorm (fun t ↦ ‖actualSliceLp (μ := μ) (p := 2) U t‖ *
      ‖actualSliceLp (μ := μ) (p := 2) U t‖) 1 ν ≤
        eLpNorm (actualSliceLp (μ := μ) (p := 2) U) 2 ν ^ 2 := by
    have hb := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 2) (q := 2) (r := 1)
      (fun a b : ℝ ↦ a * b) 1 continuous_mul
      hUc.norm.aestronglyMeasurable hUc.norm.aestronglyMeasurable
      (ae_of_all _ fun _ ↦ by simp only [NNReal.coe_one, one_mul, norm_mul]; rfl)
    simpa only [ENNReal.coe_one, one_mul, eLpNorm_norm _ hUc.aestronglyMeasurable,
      pow_two] using hb
  exact ⟨hgood, (eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' 1 hFc hnorm).trans
    (mul_le_mul' le_rfl hsq)⟩

/-- Genuine quadratic mixed sources have actual time L¹ spatial L² classes. -/
theorem projectedEnergySliceData_one_of_quadratic_velocity_bound
    {A T E : Type*} [MeasurableSpace A] [MeasurableSpace T]
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure A} [SFinite μ] [IsSeparable μ] {ν : Measure T} [SFinite ν]
    {U : A × T → E} {F : A × T → ℝ}
    (hF : AEStronglyMeasurable F (μ.prod ν))
    (hUs : ∀ᵐ t ∂ν, MemLp (fun x ↦ U (x, t)) 2 μ)
    (hUc : MemLp (actualSliceLp (μ := μ) (p := 2) U) 2 ν)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, ‖F (x, t)‖ ≤
      (C * ‖actualSliceLp (μ := μ) (p := 2) U t‖) * ‖U (x, t)‖) :
    ProjectedEnergySliceData μ ν 1 F := by
  have hb := actualSliceLp_one_le_of_quadratic_velocity_bound hF hUs hUc hC hbound
  refine ⟨hF, hb.1, hb.2.trans_lt ?_⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top hUc.eLpNorm_lt_top)

/-- Actual quadratic sources paired with a genuine bounded mixed velocity are integrable,
with the true quadratic source times square-root-energy bound. -/
theorem integrable_product_and_bound_of_quadratic_velocity_source
    {A T E : Type*} [MeasurableSpace A] [MeasurableSpace T]
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure A} [SFinite μ] [IsSeparable μ] {ν : Measure T} [SFinite ν]
    {U : A × T → E} {F G : A × T → ℝ}
    (hF : AEStronglyMeasurable F (μ.prod ν)) (hG : AEStronglyMeasurable G (μ.prod ν))
    (hUs : ∀ᵐ t ∂ν, MemLp (fun x ↦ U (x, t)) 2 μ)
    (hUc : MemLp (actualSliceLp (μ := μ) (p := 2) U) 2 ν)
    (hGs : ∀ᵐ t ∂ν, MemLp (fun x ↦ G (x, t)) 2 μ)
    (hGc : MemLp (actualSliceLp (μ := μ) (p := 2) G) ⊤ ν)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, ‖F (x, t)‖ ≤
      (C * ‖actualSliceLp (μ := μ) (p := 2) U t‖) * ‖U (x, t)‖) :
    Integrable (fun z ↦ F z * G z) (μ.prod ν) ∧
      ‖∫ z, F z * G z ∂μ.prod ν‖ₑ ≤
        ENNReal.ofReal C * eLpNorm (actualSliceLp (μ := μ) (p := 2) U) 2 ν ^ 2 *
          eLpNorm (actualSliceLp (μ := μ) (p := 2) G) ⊤ ν := by
  have hb := actualSliceLp_one_le_of_quadratic_velocity_bound hF hUs hUc hC hbound
  have hd := projectedEnergySliceData_one_of_quadratic_velocity_bound hF hUs hUc hC hbound
  refine ⟨integrable_mul_of_actualSliceLp_one_top hF hG hb.1 hGs hd.classMemLp hGc, ?_⟩
  rw [integral_mul_eq_integral_actualSliceLp_inner hF hG hb.1 hGs hd.classMemLp hGc]
  exact ((enorm_integral_le_lintegral_enorm _).trans
    lintegral_enorm_le_eLpNorm_one).trans
      ((eLpNorm_real_inner_le (p := 1) (q := ⊤) (r := 1)
        hd.classMemLp.aestronglyMeasurable hGc.aestronglyMeasurable).trans
        (mul_le_mul' hb.2 le_rfl))

end FluidSingularSets
