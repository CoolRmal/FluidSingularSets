-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedBallMixedRescaling
public import CKN.Foundation.Parabolic.BallBasics

/-!
# Actual nested cylinders inside a physical projection ball

The restricted scaling measure transports an arbitrary inner radius, not only
the projection ball itself. Genuine compact local boxes on smaller cylinders
are derived from the original unit local box.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- Any smaller physical cylinder is a genuine compact local box. -/
theorem localBox_subunit_backwardCylinder
    {Ω : Set Vec3} {I : Set ℝ}
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0))
    {μ : ℝ} (hμ : 0 < μ) (hμone : μ ≤ 1) :
    localBox Ω I (vec3Ball 0 μ) (Ioo (-(μ ^ 2)) 0) := by
  rcases hbox with ⟨_, _, hBΩ, _, _, hJI⟩
  have hsq : μ ^ 2 ≤ 1 := by nlinarith
  have ht : Ioo (-(μ ^ 2)) 0 ⊆ Ioo (-1 : ℝ) 0 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  refine ⟨isOpen_vec3Ball 0 μ, isCompact_closure_vec3Ball hμ,
    (closure_mono (vec3Ball_mono hμone)).trans hBΩ, ordConnected_Ioo, ?_,
    (closure_mono ht).trans hJI⟩
  rw [closure_Ioo (by nlinarith [sq_pos_of_pos hμ] : -(μ ^ 2) ≠ (0 : ℝ))]
  exact isCompact_Icc

/-- Scaling the genuine smaller cylinder gives the original native unit time interval. -/
theorem localBox_rescaled_subunit_backwardCylinder
    {Ω : Set Vec3} {I : Set ℝ}
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0))
    {μ : ℝ} (hμ : 0 < μ) (hμone : μ ≤ 1) :
    localBox (rescaledSpace μ 0 Ω) (rescaledTime μ 0 I)
      (vec3Ball 0 1) (Ioo (-1 : ℝ) 0) := by
  have h := localBox_rescaled_projectionBall hμ (0, 0)
    (localBox_subunit_backwardCylinder hbox hμ hμone)
  simpa only [sub_zero, zero_div, neg_div, div_self (pow_ne_zero 2 hμ.ne')] using h

/-- Degree-four densities have their exact restricted scaling on every inner ball. -/
theorem lintegral_projectedScaling_four_innerBall {μ : ℝ} (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (R a b : ℝ) (F : ParabolicPoint → ℝ≥0∞) :
    (∫⁻ w : ParabolicPoint in vec3Ball 0 (R / μ) ×ˢ
        Ioo ((a - z₀.2) / μ ^ 2) ((b - z₀.2) / μ ^ 2),
      ENNReal.ofReal (μ ^ 4) * F (scalingParabolic μ z₀ w)) =
      ENNReal.ofReal μ⁻¹ * ∫⁻ z : ParabolicPoint in vec3Ball z₀.1 R ×ˢ Ioo a b, F z := by
  have hm := map_scalingParabolic_restrict hμ z₀
    (vec3Ball_measurable z₀.1 R) (I := Ioo a b) measurableSet_Ioo
  rw [rescaledSpace_vec3Ball μ hμ z₀.1 R, rescaledTime_Ioo μ hμ z₀.2 a b] at hm
  have hc : ENNReal.ofReal (μ ^ 4) * ENNReal.ofReal (μ⁻¹ ^ 5) =
      ENNReal.ofReal μ⁻¹ := by
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ μ ^ 4)]
    congr 1
    field_simp [hμ.ne']
  calc
    _ = ENNReal.ofReal (μ ^ 4) * ∫⁻ w : ParabolicPoint in vec3Ball 0 (R / μ) ×ˢ
        Ioo ((a - z₀.2) / μ ^ 2) ((b - z₀.2) / μ ^ 2), F (scalingParabolic μ z₀ w) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (μ ^ 4) * ∫⁻ z, F z ∂Measure.map (scalingParabolic μ z₀)
        (volume.restrict (vec3Ball 0 (R / μ) ×ˢ
          Ioo ((a - z₀.2) / μ ^ 2) ((b - z₀.2) / μ ^ 2))) :=
      congrArg (fun r : ℝ≥0∞ ↦ ENNReal.ofReal (μ ^ 4) * r)
        ((projectedScalingParabolic_measurableEmbedding hμ z₀).lintegral_map F).symm
    _ = ENNReal.ofReal (μ ^ 4) * (ENNReal.ofReal (μ⁻¹ ^ 5) *
        ∫⁻ z : ParabolicPoint in vec3Ball z₀.1 R ×ˢ Ioo a b, F z) := by
      calc
        _ = ENNReal.ofReal (μ ^ 4) * ∫⁻ z, F z
            ∂(ENNReal.ofReal (μ⁻¹ ^ 5) •
              volume.restrict (spaceTimeSet (vec3Ball z₀.1 R) (Ioo a b))) :=
          congrArg (fun ν : Measure ParabolicPoint ↦
            ENNReal.ofReal (μ ^ 4) * ∫⁻ z, F z ∂ν) hm
        _ = _ := by
          rw [lintegral_smul_measure]
          rfl
    _ = _ := by rw [← mul_assoc, hc]

/-- Literal coordinate-gradient energy rescales correctly on every nested inner cylinder. -/
theorem rescaleGradient_coordinate_energy_innerBall {μ : ℝ} (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (D : ParabolicPoint → Fin 3 → Vec3) (R a b : ℝ) :
    (∫⁻ w : ParabolicPoint in vec3Ball 0 (R / μ) ×ˢ
        Ioo ((a - z₀.2) / μ ^ 2) ((b - z₀.2) / μ ^ 2),
      ENNReal.ofReal (projectedGradientSquare (rescaleGradient μ z₀ D w))) =
      ENNReal.ofReal μ⁻¹ * ∫⁻ z : ParabolicPoint in vec3Ball z₀.1 R ×ˢ Ioo a b,
        ENNReal.ofReal (projectedGradientSquare (D z)) := by
  have hg (w : ParabolicPoint) : rescaleGradient μ z₀ D w =
      μ ^ 2 • D (scalingParabolic μ z₀ w) := rfl
  have hp (w : ParabolicPoint) :
      ENNReal.ofReal (projectedGradientSquare (rescaleGradient μ z₀ D w)) =
      ENNReal.ofReal (μ ^ 4) *
        ENNReal.ofReal (projectedGradientSquare (D (scalingParabolic μ z₀ w))) := by
    rw [hg, projectedGradientSquare_smul, ← pow_mul,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ μ ^ (2 * 2))]
  exact (lintegral_congr hp).trans
    (lintegral_projectedScaling_four_innerBall hμ z₀ R a b
      (fun z ↦ ENNReal.ofReal (projectedGradientSquare (D z))))

end FluidSingularSets
