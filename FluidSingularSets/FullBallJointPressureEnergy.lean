-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallJointPressureTest
public import FluidSingularSets.FullBallProjectedData
public import FluidSingularSets.ProjectedScalarEnergyBound

/-!
# Actual pressure-flux classes controlled by projected energy

The genuine projected field supplies all joint measurability and good spatial
slices. Its actual Euclidean slice supremum bounds every joint pressure test
whose literal spatial gradient has a finite uniform budget.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual joint-test pressure flux has a true time L∞ spatial L² energy bound. -/
theorem suitable_fullBall_joint_pressure_test_energy_data
    {Ω : Set Vec3} {I J : Set ℝ} {q a b c ρ L : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {B : Set Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (hJ : MeasurableSet J) (hJsub : J ⊆ Ioo a b)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1)
    (hL : ∀ x ∈ B, ∀ t ∈ J, ‖fun i ↦ spatialPartial ψ i (x, t)‖ ≤ L)
    (hM : essSup (fun t ↦ ∫⁻ x in B, ENNReal.ofReal
      (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c (x, t)) ^ 2))
        (volume.restrict J) < ⊤) :
    ProjectedEnergySliceData (volume.restrict B) (volume.restrict J) ⊤
        (fullBallJointProjectedPressureTest u D p a b c ψ χ) ∧
      eLpNorm (actualSliceLp (μ := volume.restrict B) (p := 2)
        (fullBallJointProjectedPressureTest u D p a b c ψ χ)) ⊤ (volume.restrict J) ≤
        ENNReal.ofReal (3 * L) * essSup (fun t ↦ ∫⁻ x in B, ENNReal.ofReal
          (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c (x, t)) ^ 2))
            (volume.restrict J) ^ (1 / 2 : ℝ) := by
  let V := fullBallProjectedVelocityAmbient u D p a b c
  let G := fullBallJointProjectedPressureTest u D p a b c ψ χ
  let μ := volume.restrict B
  let ν := volume.restrict J
  have hV : AEStronglyMeasurable V (μ.prod ν) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact (fullBallProjectedVelocityAmbient_joint_memLp_two
      hsol hbox hab hc hρ hρone hBK).1.aestronglyMeasurable.mono_measure
        (Measure.restrict_mono (Set.prod_mono Subset.rfl hJsub) le_rfl)
  have hVs : ∀ᵐ t ∂ν, MemLp (fun x ↦ V (x, t)) 2 μ := by
    have hs := (fullBallProjectedVelocityAmbient_weak_gradient_slices_ae
      u D p a b c hsol hbox hρ hρone hB hBK).mono fun _ ht ↦ ht.1
    exact hs.filter_mono (ae_mono (Measure.restrict_mono hJsub le_rfl))
  have hG : AEStronglyMeasurable G (μ.prod ν) := by
    apply (hχ.comp continuous_snd).aestronglyMeasurable.mul
    apply Finset.aestronglyMeasurable_fun_sum
    intro i _
    exact ((continuous_apply i).comp_aestronglyMeasurable hV).mul
      (spatialPartial_contDiff hψ i).continuous.aestronglyMeasurable
  have hb : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, ‖G (x, t)‖ ≤ (3 * L) * ‖V (x, t)‖ := by
    filter_upwards [ae_restrict_mem hJ] with t ht
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    change ‖χ t * ∑ i : Fin 3, V (x, t) i * spatialPartial ψ i (x, t)‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ 1 * ‖∑ i : Fin 3, V (x, t) i * spatialPartial ψ i (x, t)‖ :=
        mul_le_mul_of_nonneg_right (hbχ t) (norm_nonneg _)
      _ ≤ 3 * ‖V (x, t)‖ * ‖fun i ↦ spatialPartial ψ i (x, t)‖ := by
        simpa only [one_mul] using vec3_coordinate_pairing_norm_le
          (V (x, t)) (fun i ↦ spatialPartial ψ i (x, t))
      _ ≤ 3 * ‖V (x, t)‖ * L :=
        mul_le_mul_of_nonneg_left (hL x hx t ht) (by positivity)
      _ = _ := by ring
  exact projectedEnergySliceData_top_bound_of_euclidean_energy hV hG hVs hM hb

end FluidSingularSets
