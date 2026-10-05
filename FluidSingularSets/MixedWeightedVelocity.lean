-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedEnergyStrongLimit
public import FluidSingularSets.UniformMixedSlices

/-!
# Actual tested velocity class bounds

A genuine bounded test coefficient transports the suitable velocity's actual
time L∞ spatial L² class to the tested scalar velocity. Uniform approximation
of the harmonic correction gives the true strong time L∞ class limit used in
the projected pressure pairing.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The literal coordinate pairing has the true finite-dimensional norm bound. -/
theorem vec3_coordinate_pairing_norm_le (V G : Vec3) :
    ‖∑ i : Fin 3, V i * G i‖ ≤ 3 * ‖V‖ * ‖G‖ := by
  calc
    _ ≤ ∑ i : Fin 3, ‖V i * G i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖V‖ * ‖G‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul (norm_le_pi_norm V i) (norm_le_pi_norm G i)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Genuine pointwise domination transports the true spatial-class time bound. -/
theorem projectedEnergySliceData_top_of_velocity_bound
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    {μ : Measure A} [SFinite μ] [IsSeparable μ] {ν : Measure T} [SFinite ν]
    {V : A × T → Vec3} {F : A × T → ℝ}
    (hF : AEStronglyMeasurable F (μ.prod ν))
    (hVs : ∀ᵐ t ∂ν, MemLp (fun x ↦ V (x, t)) 2 μ)
    (hVc : MemLp (actualSliceLp (μ := μ) (p := 2) V) ⊤ ν)
    {C : ℝ} (hbound : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, ‖F (x, t)‖ ≤ C * ‖V (x, t)‖) :
    ProjectedEnergySliceData μ ν ⊤ F := by
  have hgood : ∀ᵐ t ∂ν, MemLp (fun x ↦ F (x, t)) 2 μ := by
    filter_upwards [hF.prodMk_right, hVs, hbound] with t hft hvt hbt
    exact hvt.of_le_mul hft hbt
  have hFc := aestronglyMeasurable_actualSliceLp hF (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have hnorm : ∀ᵐ t ∂ν, ‖actualSliceLp (μ := μ) (p := 2) F t‖ₑ ≤
      ENNReal.ofReal C * ‖actualSliceLp (μ := μ) (p := 2) V t‖ₑ := by
    filter_upwards [hgood, hVs, hbound] with t hft hvt hbt
    rw [actualSliceLp_enorm F t hft, actualSliceLp_enorm V t hvt]
    exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul hft.aestronglyMeasurable hbt 2
  refine ⟨hF, hgood, ?_⟩
  exact (eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' ⊤ hFc hnorm).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hVc)

/-- A bounded actual coefficient gives the true time L∞ tested-velocity class. -/
theorem projectedEnergySliceData_top_tested_velocity
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    {μ : Measure A} [SFinite μ] [IsSeparable μ] {ν : Measure T} [SFinite ν]
    {V G : A × T → Vec3}
    (hV : AEStronglyMeasurable V (μ.prod ν)) (hG : AEStronglyMeasurable G (μ.prod ν))
    (hVs : ∀ᵐ t ∂ν, MemLp (fun x ↦ V (x, t)) 2 μ)
    (hVc : MemLp (actualSliceLp (μ := μ) (p := 2) V) ⊤ ν)
    {M : ℝ} (hbound : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, ‖G (x, t)‖ ≤ M) :
    ProjectedEnergySliceData μ ν ⊤ (fun z ↦ ∑ i : Fin 3, V z i * G z i) := by
  have hmeas : AEStronglyMeasurable (fun z ↦ ∑ i : Fin 3, V z i * G z i) (μ.prod ν) := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro i _
    exact (((continuous_apply i).comp_aestronglyMeasurable hV).mul
      ((continuous_apply i).comp_aestronglyMeasurable hG))
  apply projectedEnergySliceData_top_of_velocity_bound hmeas hVs hVc
  filter_upwards [hbound] with t ht
  filter_upwards [ht] with x hx
  exact (vec3_coordinate_pairing_norm_le (V (x, t)) (G (x, t))).trans
    ((mul_le_mul_of_nonneg_left hx (mul_nonneg (by norm_num) (norm_nonneg _))).trans_eq
      (by ring : 3 * ‖V (x, t)‖ * M = (3 * M) * ‖V (x, t)‖))

/-- True uniform field differences give the structured strong mixed class limit. -/
theorem projectedEnergySliceStrong_top_of_uniform_bound
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    {μ : Measure A} [IsFiniteMeasure μ] [IsSeparable μ] {ν : Measure T} [SFinite ν]
    {F : A × T → ℝ} {Fs : ℕ → A × T → ℝ}
    (hF : ProjectedEnergySliceData μ ν ⊤ F)
    (hFs : ∀ n, ProjectedEnergySliceData μ ν ⊤ (Fs n))
    {C : ℕ → ℝ} (hC : ∀ n, 0 ≤ C n) (hzero : Tendsto C atTop (𝓝 0))
    (hbound : ∀ n, ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, ‖Fs n (x, t) - F (x, t)‖ ≤ C n) :
    ProjectedEnergySliceStrong μ ν ⊤ F Fs :=
  ⟨hF, hFs, tendsto_actualSliceLp_top_sub_of_uniform_bound hF.joint
    (fun n ↦ (hFs n).joint) hF.slices hC hzero hbound⟩

end FluidSingularSets
