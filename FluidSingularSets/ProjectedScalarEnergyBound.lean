-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.MixedWeightedVelocity
public import FluidSingularSets.SliceLpMoments
public import FluidSingularSets.SuitableVelocityTimeBound

/-!
# True scalar mixed classes controlled by Euclidean slice energy

Pointwise domination by a genuine vector field controls the scalar spatial L²
class in time L∞ by the square root of the literal Euclidean slice supremum.
The estimate applies to pressure fluxes with joint space-time coefficients.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Actual scalar domination gives the genuine mixed class and Euclidean energy bound. -/
theorem projectedEnergySliceData_top_bound_of_euclidean_energy
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    {μ : Measure A} [SFinite μ] [IsSeparable μ] {ν : Measure T} [SFinite ν]
    {V : A × T → Vec3} {F : A × T → ℝ}
    (hV : AEStronglyMeasurable V (μ.prod ν))
    (hF : AEStronglyMeasurable F (μ.prod ν))
    (hVs : ∀ᵐ t ∂ν, MemLp (fun x ↦ V (x, t)) 2 μ)
    (hM : essSup (fun t ↦ ∫⁻ x, ENNReal.ofReal (vec3EuclideanNorm (V (x, t)) ^ 2) ∂μ) ν < ⊤)
    {C : ℝ} (hbound : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, ‖F (x, t)‖ ≤ C * ‖V (x, t)‖) :
    ProjectedEnergySliceData μ ν ⊤ F ∧
      eLpNorm (actualSliceLp (μ := μ) (p := 2) F) ⊤ ν ≤ ENNReal.ofReal C *
        essSup (fun t ↦ ∫⁻ x, ENNReal.ofReal (vec3EuclideanNorm (V (x, t)) ^ 2) ∂μ) ν ^
          (1 / 2 : ℝ) := by
  have henergy : essSup (fun t ↦ ∫⁻ x, ‖V (x, t)‖ₑ ^ (2 : ℝ) ∂μ) ν ≤
      essSup (fun t ↦ ∫⁻ x, ENNReal.ofReal (vec3EuclideanNorm (V (x, t)) ^ 2) ∂μ) ν := by
    refine essSup_mono_ae (ae_of_all _ fun t ↦ lintegral_mono fun x ↦ ?_)
    rw [ENNReal.rpow_ofNat, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (norm_nonneg _) (norm_le_vec3EuclideanNorm _) 2)
  have hVc : MemLp (actualSliceLp (μ := μ) (p := 2) V) ⊤ ν :=
    actualSliceLp_memLp_top_of_sliceEnergy hV (henergy.trans_lt hM)
  have hVnorm : eLpNorm (actualSliceLp (μ := μ) (p := 2) V) ⊤ ν ≤
      essSup (fun t ↦ ∫⁻ x, ENNReal.ofReal (vec3EuclideanNorm (V (x, t)) ^ 2) ∂μ) ν ^
        (1 / 2 : ℝ) :=
    (actualSliceLp_eLpNorm_top_le_sliceEnergy hV).trans
      (ENNReal.rpow_le_rpow henergy (by norm_num))
  have hd := projectedEnergySliceData_top_of_velocity_bound hF hVs hVc hbound
  have hn : ∀ᵐ t ∂ν, ‖actualSliceLp (μ := μ) (p := 2) F t‖ₑ ≤
      ENNReal.ofReal C * ‖actualSliceLp (μ := μ) (p := 2) V t‖ₑ := by
    filter_upwards [hd.slices, hVs, hbound] with t hft hvt hbt
    rw [actualSliceLp_enorm F t hft, actualSliceLp_enorm V t hvt]
    exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul hft.aestronglyMeasurable hbt 2
  exact ⟨hd, (eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' ⊤
    hd.classMemLp.aestronglyMeasurable hn).trans (mul_le_mul' le_rfl hVnorm)⟩

end FluidSingularSets
