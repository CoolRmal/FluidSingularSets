-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallRadiusCaccioppoli
public import FluidSingularSets.ScaleRegularity
public import CKN.Foundation.Parabolic.Vec3Norm

/-!
# Fixed interior boxes for an actual endpoint regularity theorem

Every point of the closed radius-one-eighth cylinder has a radius-one-quarter
backward box contained in the original unit box. Genuine parabolic rescaling
retains its localBox geometry, and its original velocity mixed source is
bounded by four times the original unit source. All constants are independent
of a future terminal margin.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Literal closed-inner-cylinder membership gives the genuine space and time bounds. -/
theorem endpoint_closed_inner_point_bounds {z : ParabolicPoint}
    (hz : z ∈ closure (parabolicCylinder 0 0 (1 / 8))) :
    vec3EuclideanNorm z.1 ≤ 1 / 8 ∧ -(1 / 64 : ℝ) ≤ z.2 ∧ z.2 ≤ 0 := by
  rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < 1 / 8)] at hz
  refine ⟨?_, ?_, hz.2.2⟩
  · have hs := hz.1
    change vec3EuclideanNorm (z.1 - 0) ≤ 1 / 8 at hs
    simpa only [sub_zero] using hs
  · simpa only [zero_sub, show (1 / 8 : ℝ) ^ 2 = 1 / 64 by norm_num] using hz.2.1

/-- The true closed quarter-ball about every such interior point lies in the open unit ball. -/
theorem endpoint_interior_closed_quarterBall_subset_unit {z : ParabolicPoint}
    (hz : z ∈ closure (parabolicCylinder 0 0 (1 / 8))) :
    closure (vec3Ball z.1 (1 / 4)) ⊆ vec3Ball 0 1 := by
  intro x hx
  rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 4)] at hx
  change vec3EuclideanNorm (x - z.1) ≤ 1 / 4 at hx
  have hzx := (endpoint_closed_inner_point_bounds hz).1
  have ht := vec3EuclideanNorm_add_le (x - z.1) z.1
  rw [sub_add_cancel] at ht
  apply mem_vec3Ball.mpr
  simp only [sub_zero]
  linarith

/-- Every fixed interior quarter-box is genuinely compactly contained in the source carrier. -/
theorem localBox_endpoint_interior_quarter
    {Ω : Set Vec3} {I : Set ℝ}
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0))
    {z : ParabolicPoint} (hz : z ∈ closure (parabolicCylinder 0 0 (1 / 8))) :
    localBox Ω I (vec3Ball z.1 (1 / 4)) (Ioo (z.2 - (1 / 4 : ℝ) ^ 2) z.2) := by
  obtain ⟨_, hzlo, hzhi⟩ := endpoint_closed_inner_point_bounds hz
  have he : closure (Ioo (z.2 - (1 / 4 : ℝ) ^ 2) z.2) =
      Icc (z.2 - (1 / 4 : ℝ) ^ 2) z.2 := closure_Ioo (by linarith)
  refine ⟨isOpen_vec3Ball _ _, isCompact_closure_vec3Ball (by norm_num), ?_,
    ordConnected_Ioo, ?_, ?_⟩
  · intro x hx
    exact hbox.2.2.1 (subset_closure (endpoint_interior_closed_quarterBall_subset_unit hz hx))
  · rw [he]
    exact isCompact_Icc
  · intro t ht
    rw [he] at ht
    apply hbox.2.2.2.2.2
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)]
    exact ⟨by linarith [ht.1], ht.2.trans hzhi⟩

/-- The actual interior physical quarter-box rescales to the exact native unit local box. -/
theorem localBox_endpoint_interior_quarter_rescaled
    {Ω : Set Vec3} {I : Set ℝ}
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0))
    {z : ParabolicPoint} (hz : z ∈ closure (parabolicCylinder 0 0 (1 / 8))) :
    localBox (rescaledSpace (1 / 4) z.1 Ω) (rescaledTime (1 / 4) z.2 I)
      (vec3Ball 0 1) (Ioo (-1 : ℝ) 0) := by
  have hh := localBox_rescaled_projectionBall (by norm_num : (0 : ℝ) < 1 / 4) z
    (localBox_endpoint_interior_quarter hbox hz)
  have hlo : (z.2 - (1 / 4 : ℝ) ^ 2 - z.2) / (1 / 4 : ℝ) ^ 2 = -1 := by ring
  have hhi : (z.2 - z.2) / (1 / 4 : ℝ) ^ 2 = 0 := by ring
  simpa only [hlo, hhi] using hh

/-- Genuine mixed-norm scaling and containment bound every interior source by four unit sources. -/
theorem endpoint_interior_rescaled_six_moment_le_four
    (u : ParabolicPoint → Vec3) {z : ParabolicPoint}
    (hz : z ∈ closure (parabolicCylinder 0 0 (1 / 8))) :
    velocityCylinderSixMoment (rescaleVelocity (1 / 4) z u) 1 ≤
      4 * velocityCylinderSixMoment u 1 := by
  obtain ⟨_, hzlo, hzhi⟩ := endpoint_closed_inner_point_bounds hz
  have hball : vec3Ball z.1 (1 / 4) ⊆ vec3Ball 0 1 :=
    subset_closure.trans (endpoint_interior_closed_quarterBall_subset_unit hz)
  have htime : Ioo (z.2 - (1 / 4 : ℝ) ^ 2) z.2 ⊆ Ioo (-1 : ℝ) 0 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2.trans_le hzhi⟩
  have hlo : (z.2 - (1 / 4 : ℝ) ^ 2 - z.2) / (1 / 4 : ℝ) ^ 2 = -1 := by ring
  have hhi : (z.2 - z.2) / (1 / 4 : ℝ) ^ 2 = 0 := by ring
  have hscale := rescaleVelocity_mixed_two_six_projectionBall
    (by norm_num : (0 : ℝ) < 1 / 4) z u (z.2 - (1 / 4 : ℝ) ^ 2) z.2
  simp only [hlo, hhi, show (1 / 4 : ℝ)⁻¹ = 4 by norm_num,
    ENNReal.ofReal_ofNat] at hscale
  simp only [velocityCylinderSixMoment, one_pow]
  rw [hscale]
  apply mul_le_mul' le_rfl
  calc
    _ ≤ ∫⁻ t in Ioo (z.2 - (1 / 4 : ℝ) ^ 2) z.2,
        eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) ^ 2 := by
      apply lintegral_mono
      intro t
      exact pow_le_pow_left' (eLpNorm_mono_measure _
        (Measure.restrict_mono_set volume hball)) 2
    _ ≤ _ := lintegral_mono_set htime

end FluidSingularSets
