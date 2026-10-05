-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedBallRescaling
public import FluidSingularSets.ProjectedEnergyAlgebra

/-!
# Genuine endpoint mixed norms under physical projection-ball rescaling

The actual spatial and time affine homeomorphisms supply their true restricted
Jacobian measures. The L²-time/L⁶-space velocity moment on a native unit ball
therefore equals the physical moment divided by the projection radius. The
identities use extended nonnegative values and retain infinite moments.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- The true positive spatial scaling is a measurable embedding. -/
theorem projectedScalingSpace_measurableEmbedding {μ : ℝ} (hμ : 0 < μ) (x₀ : Vec3) :
    MeasurableEmbedding (scalingSpace μ x₀) := by
  have he : scalingSpace μ x₀ = scalingSpaceHomeomorph μ hμ x₀ := by
    funext y
    simp [scalingSpace, scalingSpaceHomeomorph]
  rw [he]
  exact (scalingSpaceHomeomorph μ hμ x₀).measurableEmbedding

/-- The true positive time scaling is a measurable embedding. -/
theorem projectedScalingTime_measurableEmbedding {μ : ℝ} (hμ : 0 < μ) (t₀ : ℝ) :
    MeasurableEmbedding (scalingTime μ t₀) := by
  have he : scalingTime μ t₀ = scalingTimeHomeomorph μ hμ t₀ := by
    funext s
    simp [scalingTime, scalingTimeHomeomorph, smul_eq_mul]
  rw [he]
  exact (scalingTimeHomeomorph μ hμ t₀).measurableEmbedding

/-- The actual parabolic scaling is the product of the two genuine embeddings. -/
theorem projectedScalingParabolic_measurableEmbedding {μ : ℝ} (hμ : 0 < μ)
    (z₀ : ParabolicPoint) : MeasurableEmbedding (scalingParabolic μ z₀) := by
  rw [scalingParabolic_eq]
  exact (projectedScalingSpace_measurableEmbedding hμ z₀.1).prodMap
    (projectedScalingTime_measurableEmbedding hμ z₀.2)

/-- Restricted physical spatial norms have the true dimensional Jacobian factor. -/
theorem eLpNorm_scalingSpace_projectionBall {μ : ℝ} (hμ : 0 < μ) (x₀ : Vec3)
    {E : Type*} [NormedAddCommGroup E] (f : Vec3 → E) :
    eLpNorm (fun y ↦ f (scalingSpace μ x₀ y)) 6 (volume.restrict (vec3Ball 0 1)) =
      ENNReal.ofReal (μ⁻¹ ^ 3) ^ (1 / 6 : ℝ) *
        eLpNorm f 6 (volume.restrict (vec3Ball x₀ μ)) := by
  have hm := map_scalingSpace_restrict hμ x₀ (vec3Ball_measurable x₀ μ)
  rw [rescaledSpace_projectionBall hμ x₀] at hm
  calc
    _ = eLpNorm f 6 (Measure.map (scalingSpace μ x₀)
        (volume.restrict (vec3Ball 0 1))) :=
      (projectedScalingSpace_measurableEmbedding hμ x₀).eLpNorm_map_measure.symm
    _ = _ := by
      rw [hm, eLpNorm_smul_measure_of_ne_zero_of_ne_top
        (by norm_num : (6 : ℝ≥0∞) ≠ 0) (by norm_num : (6 : ℝ≥0∞) ≠ ⊤)]
      norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
        smul_eq_mul]

/-- The two spatial scaling factors have exactly the critical endpoint square coefficient. -/
theorem projectedScaling_six_square_coefficient {μ : ℝ} (hμ : 0 < μ) :
    (ENNReal.ofReal μ * ENNReal.ofReal (μ⁻¹ ^ 3) ^ (1 / 6 : ℝ)) ^ 2 =
      ENNReal.ofReal μ := by
  rw [mul_pow, ← ENNReal.rpow_natCast
    (ENNReal.ofReal (μ⁻¹ ^ 3) ^ (1 / 6 : ℝ)) 2, ← ENNReal.rpow_mul]
  norm_num only [show (1 / 6 : ℝ) * 2 = 1 / 3 by norm_num, Nat.cast_ofNat]
  rw [ENNReal.ofReal_pow (inv_nonneg.mpr hμ.le), ← ENNReal.rpow_natCast _ 3,
    ← ENNReal.rpow_mul]
  norm_num only [show (3 : ℝ) * (1 / 3) = 1 by norm_num, Nat.cast_ofNat,
    ENNReal.rpow_one]
  rw [ENNReal.ofReal_inv_of_pos hμ, pow_two, mul_assoc,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hμ).ne' ENNReal.ofReal_ne_top, mul_one]

/-- Every literal rescaled velocity slice has its true endpoint square scaling. -/
theorem rescaleVelocity_six_square_projectionBall {μ : ℝ} (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (u : ParabolicPoint → Vec3) (s : ℝ) :
    eLpNorm (fun y ↦ rescaleVelocity μ z₀ u (y, s)) 6
      (volume.restrict (vec3Ball 0 1)) ^ 2 =
    ENNReal.ofReal μ * eLpNorm (fun x ↦ u (x, scalingTime μ z₀.2 s)) 6
      (volume.restrict (vec3Ball z₀.1 μ)) ^ 2 := by
  have he : (fun y ↦ rescaleVelocity μ z₀ u (y, s)) =
      μ • (fun y ↦ u (scalingSpace μ z₀.1 y, scalingTime μ z₀.2 s)) := rfl
  rw [he, eLpNorm_const_smul,
    eLpNorm_scalingSpace_projectionBall hμ z₀.1 (fun x ↦ u (x, scalingTime μ z₀.2 s)),
    ← ofReal_norm, Real.norm_eq_abs, abs_of_pos hμ, ← mul_assoc, mul_pow,
    projectedScaling_six_square_coefficient hμ]

/-- The true original time interval transforms with its exact restricted time Jacobian. -/
theorem lintegral_scalingTime_Ioo {μ : ℝ} (hμ : 0 < μ) (t₀ a b : ℝ)
    (F : ℝ → ℝ≥0∞) :
    (∫⁻ s in Ioo ((a - t₀) / μ ^ 2) ((b - t₀) / μ ^ 2),
      F (scalingTime μ t₀ s)) = ENNReal.ofReal ((μ ^ 2)⁻¹) * ∫⁻ t in Ioo a b, F t := by
  have hm := map_scalingTime_restrict hμ t₀ (I := Ioo a b) measurableSet_Ioo
  rw [rescaledTime_Ioo μ hμ t₀ a b] at hm
  rw [← (projectedScalingTime_measurableEmbedding hμ t₀).lintegral_map, hm,
    lintegral_smul_measure]
  rfl

/-- The endpoint velocity mixed moment rescales by the inverse physical projection radius. -/
theorem rescaleVelocity_mixed_two_six_projectionBall {μ : ℝ} (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (u : ParabolicPoint → Vec3) (a b : ℝ) :
    (∫⁻ s in Ioo ((a - z₀.2) / μ ^ 2) ((b - z₀.2) / μ ^ 2),
      eLpNorm (fun y ↦ rescaleVelocity μ z₀ u (y, s)) 6
        (volume.restrict (vec3Ball 0 1)) ^ 2) =
      ENNReal.ofReal μ⁻¹ * ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
        (volume.restrict (vec3Ball z₀.1 μ)) ^ 2 := by
  let F : ℝ → ℝ≥0∞ := fun t ↦ eLpNorm (fun x ↦ u (x, t)) 6
    (volume.restrict (vec3Ball z₀.1 μ)) ^ 2
  have hp (s : ℝ) := rescaleVelocity_six_square_projectionBall hμ z₀ u s
  have hc : ENNReal.ofReal μ * ENNReal.ofReal ((μ ^ 2)⁻¹) = ENNReal.ofReal μ⁻¹ := by
    rw [← ENNReal.ofReal_mul hμ.le]
    congr 1
    field_simp [hμ.ne']
  calc
    _ = ∫⁻ s in Ioo ((a - z₀.2) / μ ^ 2) ((b - z₀.2) / μ ^ 2),
        ENNReal.ofReal μ * F (scalingTime μ z₀.2 s) := lintegral_congr hp
    _ = ENNReal.ofReal μ * ∫⁻ s in
        Ioo ((a - z₀.2) / μ ^ 2) ((b - z₀.2) / μ ^ 2), F (scalingTime μ z₀.2 s) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal μ * (ENNReal.ofReal ((μ ^ 2)⁻¹) * ∫⁻ t in Ioo a b, F t) :=
      congrArg (fun r : ℝ≥0∞ ↦ ENNReal.ofReal μ * r)
        (lintegral_scalingTime_Ioo hμ z₀.2 a b F)
    _ = _ := by rw [← mul_assoc, hc]

/-- A degree-four density has the exact inverse-radius parabolic scaling on the physical box. -/
theorem lintegral_projectedScaling_four_projectionBall {μ : ℝ} (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (a b : ℝ) (F : ParabolicPoint → ℝ≥0∞) :
    (∫⁻ w : ParabolicPoint in vec3Ball 0 1 ×ˢ
        Ioo ((a - z₀.2) / μ ^ 2) ((b - z₀.2) / μ ^ 2),
      ENNReal.ofReal (μ ^ 4) * F (scalingParabolic μ z₀ w)) =
      ENNReal.ofReal μ⁻¹ * ∫⁻ z : ParabolicPoint in vec3Ball z₀.1 μ ×ˢ Ioo a b, F z := by
  have hm := map_scalingParabolic_restrict hμ z₀
    (vec3Ball_measurable z₀.1 μ) (I := Ioo a b) measurableSet_Ioo
  rw [rescaledSpace_projectionBall hμ z₀.1, rescaledTime_Ioo μ hμ z₀.2 a b] at hm
  have hc : ENNReal.ofReal (μ ^ 4) * ENNReal.ofReal (μ⁻¹ ^ 5) =
      ENNReal.ofReal μ⁻¹ := by
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ μ ^ 4)]
    congr 1
    field_simp [hμ.ne']
  calc
    _ = ENNReal.ofReal (μ ^ 4) * ∫⁻ w : ParabolicPoint in vec3Ball 0 1 ×ˢ
        Ioo ((a - z₀.2) / μ ^ 2) ((b - z₀.2) / μ ^ 2), F (scalingParabolic μ z₀ w) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (μ ^ 4) * ∫⁻ z, F z ∂Measure.map (scalingParabolic μ z₀)
        (volume.restrict (vec3Ball 0 1 ×ˢ
          Ioo ((a - z₀.2) / μ ^ 2) ((b - z₀.2) / μ ^ 2))) :=
      congrArg (fun r : ℝ≥0∞ ↦ ENNReal.ofReal (μ ^ 4) * r)
        ((projectedScalingParabolic_measurableEmbedding hμ z₀).lintegral_map F).symm
    _ = ENNReal.ofReal (μ ^ 4) * (ENNReal.ofReal (μ⁻¹ ^ 5) *
        ∫⁻ z : ParabolicPoint in vec3Ball z₀.1 μ ×ˢ Ioo a b, F z) := by
      calc
        _ = ENNReal.ofReal (μ ^ 4) * ∫⁻ z, F z
            ∂(ENNReal.ofReal (μ⁻¹ ^ 5) •
              volume.restrict (spaceTimeSet (vec3Ball z₀.1 μ) (Ioo a b))) :=
          congrArg (fun ν : Measure ParabolicPoint ↦
            ENNReal.ofReal (μ ^ 4) * ∫⁻ z, F z ∂ν) hm
        _ = _ := by
          rw [lintegral_smul_measure]
          rfl
    _ = _ := by rw [← mul_assoc, hc]

/-- The actual raw gradient's joint energy has the exact inverse physical radius scaling. -/
theorem rescaleGradient_raw_energy_projectionBall {μ : ℝ} (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (D : ParabolicPoint → Fin 3 → Vec3) (a b : ℝ) :
    (∫⁻ w : ParabolicPoint in vec3Ball 0 1 ×ˢ
        Ioo ((a - z₀.2) / μ ^ 2) ((b - z₀.2) / μ ^ 2),
      ‖rescaleGradient μ z₀ D w‖ₑ ^ (2 : ℝ)) =
      ENNReal.ofReal μ⁻¹ * ∫⁻ z : ParabolicPoint in vec3Ball z₀.1 μ ×ˢ Ioo a b,
        ‖D z‖ₑ ^ (2 : ℝ) := by
  have hg (w : ParabolicPoint) : rescaleGradient μ z₀ D w =
      μ ^ 2 • D (scalingParabolic μ z₀ w) := rfl
  have hp (w : ParabolicPoint) : ‖rescaleGradient μ z₀ D w‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (μ ^ 4) * ‖D (scalingParabolic μ z₀ w)‖ₑ ^ (2 : ℝ) := by
    rw [hg, enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg μ)]
    norm_num only [ENNReal.rpow_ofNat, ← ENNReal.ofReal_pow (sq_nonneg μ), ← pow_mul,
      Nat.reduceMul]
  exact (lintegral_congr hp).trans
    (lintegral_projectedScaling_four_projectionBall hμ z₀ a b (fun z ↦ ‖D z‖ₑ ^ (2 : ℝ)))

/-- The literal coordinate square gradient density is genuinely homogeneous of degree two. -/
theorem projectedGradientSquare_smul (c : ℝ) (D : Fin 3 → Vec3) :
    projectedGradientSquare (c • D) = c ^ 2 * projectedGradientSquare D := by
  simp only [projectedGradientSquare, Pi.smul_apply, smul_eq_mul, mul_pow,
    ← Finset.mul_sum]

/-- The actual coordinate square energy has the same true inverse-radius physical scaling. -/
theorem rescaleGradient_coordinate_energy_projectionBall {μ : ℝ} (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (D : ParabolicPoint → Fin 3 → Vec3) (a b : ℝ) :
    (∫⁻ w : ParabolicPoint in vec3Ball 0 1 ×ˢ
        Ioo ((a - z₀.2) / μ ^ 2) ((b - z₀.2) / μ ^ 2),
      ENNReal.ofReal (projectedGradientSquare (rescaleGradient μ z₀ D w))) =
      ENNReal.ofReal μ⁻¹ * ∫⁻ z : ParabolicPoint in vec3Ball z₀.1 μ ×ˢ Ioo a b,
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
    (lintegral_projectedScaling_four_projectionBall hμ z₀ a b
      (fun z ↦ ENNReal.ofReal (projectedGradientSquare (D z))))

end FluidSingularSets
