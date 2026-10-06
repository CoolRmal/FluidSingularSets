-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallRadiusCaccioppoli
public import FluidSingularSets.BoxChargeReduction

/-!
# Physical endpoint velocity costs and native source bounds

Closed-cylinder containment gives the actual compact local box. Exact mixed
norm scaling and the Euclidean norm comparison bound the native velocity
source by the physical velocity-only cost, at every positive radius.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Actual closed-cylinder containment supplies the physical compact local box. -/
theorem localBox_endpoint_physical
    {Ω : Set Vec3} {I : Set ℝ} {t r : ℝ} (hr : 0 < r)
    (hdom : closure (parabolicCylinder 0 t r) ⊆ spaceTimeSet Ω I) :
    localBox Ω I (vec3Ball 0 r) (Ioo (t - r ^ 2) t) := by
  have htime : t - r ^ 2 < t := by nlinarith [sq_pos_of_pos hr]
  rw [closure_parabolicCylinder hr] at hdom
  refine ⟨isOpen_vec3Ball _ _, isCompact_closure_vec3Ball hr, ?_,
    ordConnected_Ioo, ?_, ?_⟩
  · intro x hx
    rw [closure_vec3Ball hr] at hx
    have hh : (x, t) ∈ spaceTimeSet Ω I := hdom
      (show (x, t) ∈ {y | vec3EuclideanNorm (y - 0) ≤ r} ×ˢ Icc (t - r ^ 2) t
        from ⟨hx, htime.le, le_rfl⟩)
    exact hh.1
  · rw [closure_Ioo htime.ne]
    exact isCompact_Icc
  · intro s hs
    rw [closure_Ioo htime.ne] at hs
    have hzero : vec3EuclideanNorm ((0 : Vec3) - 0) ≤ r := by
      simpa only [sub_zero, vec3EuclideanNorm_zero] using hr.le
    have hh : ((0 : Vec3), s) ∈ spaceTimeSet Ω I := hdom
      (show ((0 : Vec3), s) ∈ {y | vec3EuclideanNorm (y - 0) ≤ r} ×ˢ Icc (t - r ^ 2) t
        from ⟨hzero, hs⟩)
    exact hh.2

/-- The physical closed-cylinder box rescales to the exact native unit local box. -/
theorem localBox_endpoint_unit_rescaled
    {Ω : Set Vec3} {I : Set ℝ} {t r : ℝ} (hr : 0 < r)
    (hdom : closure (parabolicCylinder 0 t r) ⊆ spaceTimeSet Ω I) :
    localBox (rescaledSpace r 0 Ω) (rescaledTime r t I)
      (vec3Ball 0 1) (Ioo (-1 : ℝ) 0) := by
  have hb := localBox_rescaled_projectionBall hr (0, t)
    (localBox_endpoint_physical hr hdom)
  have hlo : (t - r ^ 2 - t) / r ^ 2 = -1 := by
    field_simp [hr.ne']
    ring
  simpa only [hlo, sub_self, zero_div] using hb

/-- Genuine suitable slice measurability and scaling bound the true native source. -/
theorem suitable_endpoint_rescaled_six_moment_le_velocity_cost
    {Ω : Set Vec3} {I : Set ℝ} {q t r : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hr : 0 < r)
    (hdom : closure (parabolicCylinder 0 t r) ⊆ spaceTimeSet Ω I) :
    velocityCylinderSixMoment (rescaleVelocity r (0, t) u) 1 ≤
      velocityOnlyMixedCost u t r := by
  have hbox := localBox_endpoint_physical hr hdom
  have hm := hsol.toData.aestronglyMeasurable_velocity hbox
  have hp : AEStronglyMeasurable u
      ((volume.restrict (vec3Ball 0 r)).prod
        (volume.restrict (Ioo (t - r ^ 2) t))) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hm
  have hlo : (t - r ^ 2 - t) / r ^ 2 = -1 := by
    field_simp [hr.ne']
    ring
  have hscale := rescaleVelocity_mixed_two_six_projectionBall hr (0, t) u
    (t - r ^ 2) t
  simp only [hlo, sub_self, zero_div] at hscale
  simp only [velocityCylinderSixMoment, one_pow]
  rw [hscale, velocityOnlyMixedCost, ENNReal.ofReal_inv_of_pos hr]
  refine mul_le_mul' le_rfl ?_
  apply lintegral_mono_ae
  filter_upwards [hp.prodMk_right] with s hs
  rw [ENNReal.rpow_ofNat]
  apply pow_le_pow_left' _ 2
  exact eLpNorm_mono_real hs (fun x ↦ norm_le_vec3EuclideanNorm _)

end FluidSingularSets
