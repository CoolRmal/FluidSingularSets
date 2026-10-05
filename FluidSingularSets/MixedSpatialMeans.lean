-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.MixedWeightedVelocity
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Actual spatial means in mixed pressure pairings

A genuine integrable time coefficient gives actual time L¹ spatial L²
constant classes on finite spatial measure. Its pairing with a true bounded
mixed velocity is integrable, and vanishes if the literal spatial integral
of that tested velocity vanishes. This removes the actual pressure mean.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The actual spatial mean of a true integrable joint field is integrable in time. -/
theorem integrable_spatial_average_of_joint_integrable
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    {μ : Measure A} [SFinite μ] {ν : Measure T} [SFinite ν]
    {F : A × T → ℝ} (hF : Integrable F (μ.prod ν)) :
    Integrable (fun t ↦ average μ (fun x ↦ F (x, t))) ν := by
  have hi := hF.integral_prod_right.const_mul ((μ.real univ)⁻¹)
  convert hi using 1
  funext t
  rw [average_eq, smul_eq_mul]

/-- A genuine integrable time coefficient gives actual L¹ spatial L² constant classes. -/
theorem projectedEnergySliceData_one_spatial_constant
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    {μ : Measure A} [IsFiniteMeasure μ] [IsSeparable μ] {ν : Measure T} [SFinite ν]
    {c : T → ℝ} (hc : Integrable c ν) :
    ProjectedEnergySliceData μ ν 1 (fun z : A × T ↦ c z.2) := by
  let F : A × T → ℝ := fun z ↦ c z.2
  have hF : AEStronglyMeasurable F (μ.prod ν) :=
    hc.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := μ))
  have hgood : ∀ᵐ t ∂ν, MemLp (fun x ↦ F (x, t)) 2 μ :=
    ae_of_all _ fun t ↦ memLp_const (c t)
  have hm := aestronglyMeasurable_actualSliceLp hF (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have hb : ∀ᵐ t ∂ν, ‖actualSliceLp (μ := μ) (p := 2) F t‖ₑ ≤
      μ univ ^ (1 / 2 : ℝ) * ‖c t‖ₑ := by
    filter_upwards [] with t
    rw [actualSliceLp_enorm F t (memLp_const (c t))]
    have he := eLpNorm_const' (μ := μ) (c t)
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    simpa only [F, ENNReal.toReal_ofNat, one_div, mul_comm] using he.le
  refine ⟨hF, hgood, (eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' 1 hm hb).trans_lt ?_⟩
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top μ univ))
    (memLp_one_iff_integrable.mpr hc).eLpNorm_lt_top

/-- The actual mean-pressure pairing with genuine divergence tests is integrable and zero. -/
theorem integrable_spatial_constant_product_and_integral_zero
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    {μ : Measure A} [IsFiniteMeasure μ] [IsSeparable μ] {ν : Measure T} [SFinite ν]
    {c : T → ℝ} {G : A × T → ℝ} (hc : Integrable c ν)
    (hG : AEStronglyMeasurable G (μ.prod ν))
    (hGs : ∀ᵐ t ∂ν, MemLp (fun x ↦ G (x, t)) 2 μ)
    (hGc : MemLp (actualSliceLp (μ := μ) (p := 2) G) ⊤ ν)
    (hzero : ∀ᵐ t ∂ν, (∫ x, G (x, t) ∂μ) = 0) :
    Integrable (fun z : A × T ↦ c z.2 * G z) (μ.prod ν) ∧
      (∫ z : A × T, c z.2 * G z ∂μ.prod ν) = 0 := by
  have hd := projectedEnergySliceData_one_spatial_constant (μ := μ) hc
  have hi := integrable_mul_of_actualSliceLp_one_top hd.joint hG hd.slices hGs hd.classMemLp hGc
  refine ⟨hi, ?_⟩
  rw [integral_prod_symm _ hi]
  apply integral_eq_zero_of_ae
  filter_upwards [hzero] with t ht
  rw [integral_const_mul, ht, mul_zero]
  rfl

end FluidSingularSets
