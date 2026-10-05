-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FixedScaleRecurrence
public import FluidSingularSets.ConcreteTraceCarleson

/-!
# Comparison of the actual symmetric mixed cost with adjacent cells

The nonlinear recurrence uses a symmetric cylinder, whereas the trace embedding
uses half-open shifted dyadic cells. Containment and the precise spatial scale
normalization compare these actual quantities with one universal coefficient.
-/

@[expose] public section

open MeasureTheory Set CKN
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The symmetric Euclidean cylinder is contained in the closed ball for the
actual snowflaked parabolic metric. -/
theorem rawSymmetricL3Cylinder_subset_closedBall
    (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ) :
    rawSymmetricL3Cylinder z ρ ⊆ Metric.closedBall z ρ := by
  rintro a ⟨hx, hlow, hhigh⟩
  rw [Metric.mem_closedBall, dist_eq_parabolicDist, parabolicDist, max_le_iff]
  constructor
  · exact hx.le
  · apply Real.sqrt_le_iff.mpr
    refine ⟨hρ.le, abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith only [hlow, hhigh]

/-- Spatial side at most sixty-four radii changes the mixed normalization by
at most five hundred and twelve. -/
theorem mixedNormalization_le_of_side_le {ρ ℓ : ℝ}
    (hρ : 0 < ρ) (hℓ : 0 < ℓ) (hside : ℓ ≤ 64 * ρ) :
    ρ ^ (-(3 / 2 : ℝ)) ≤ 512 * ℓ ^ (-(3 / 2 : ℝ)) := by
  have h64 : (64 : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / 512 := by
    norm_num
  have h := Real.rpow_le_rpow_of_nonpos hℓ hside (by norm_num : -(3 / 2 : ℝ) ≤ 0)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 64) hρ.le, h64] at h
  linarith only [h]

/-- The literal mixed gradient integral of a contained symmetric cylinder is
dominated by the literal mixed integral of the spatial and temporal cell factors. -/
theorem arrayMixedGradientIntegral_le_containingCell
    (Du : ParabolicPoint → Fin 3 → Vec3) (g : ParabolicGridShift)
    (Q : ParabolicDyadicIndex) (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : rawSymmetricL3Cylinder z ρ ⊆ shiftedParabolicDyadicCell g Q) :
    arrayMixedGradientIntegral Du (vec3Ball z.1 ρ)
        (Ioo (z.2 - ρ ^ 2) (z.2 + ρ ^ 2)) ≤
      ∫⁻ t in shiftedParabolicDyadicTime g Q.scale Q.timeCorner,
        (∫⁻ x in parabolicSpatialCube g Q,
          ‖Du (x, t)‖ₑ ^ (12 / 7 : ℝ)) ^ (7 / 6 : ℝ) := by
  have hx : z.1 ∈ vec3Ball z.1 ρ := by
    simpa only [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero] using hρ
  have ht : z.2 ∈ Ioo (z.2 - ρ ^ 2) (z.2 + ρ ^ 2) := by
    constructor <;> nlinarith only [sq_pos_of_pos hρ]
  have hspatial : vec3Ball z.1 ρ ⊆ parabolicSpatialCube g Q := by
    intro x hx
    exact (hsub (show (x, z.2) ∈ rawSymmetricL3Cylinder z ρ from ⟨hx, ht⟩)).1
  have htime : Ioo (z.2 - ρ ^ 2) (z.2 + ρ ^ 2) ⊆
      shiftedParabolicDyadicTime g Q.scale Q.timeCorner := by
    intro t ht
    exact (hsub (show (z.1, t) ∈ rawSymmetricL3Cylinder z ρ from ⟨hx, ht⟩)).2
  calc
    _ ≤ ∫⁻ t in Ioo (z.2 - ρ ^ 2) (z.2 + ρ ^ 2),
        (∫⁻ x in parabolicSpatialCube g Q,
          ‖Du (x, t)‖ₑ ^ (12 / 7 : ℝ)) ^ (7 / 6 : ℝ) :=
      lintegral_mono (fun _ ↦ ENNReal.rpow_le_rpow (lintegral_mono_set hspatial)
        (by norm_num : (0 : ℝ) ≤ 7 / 6))
    _ ≤ _ := lintegral_mono_set htime

/-- The actual symmetric mixed cost is bounded by five hundred and twelve
times the actual shifted-cell activity. The statement remains valid for infinite
cell mass, so the trace coefficient needs no hidden finiteness premise. -/
theorem rawSymmetricMixedGradientActivity_le_containingCell
    (Du : ParabolicPoint → Fin 3 → Vec3) (g : ParabolicGridShift)
    (Q : ParabolicDyadicIndex) (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : rawSymmetricL3Cylinder z ρ ⊆ shiftedParabolicDyadicCell g Q)
    (hside : dyadicScale Q.scale ≤ 64 * ρ) :
    ENNReal.ofReal (rawSymmetricMixedGradientActivity Du z ρ) ≤
      512 * dyadicMixedGradientActivity g Du Q := by
  have hmass := arrayMixedGradientIntegral_le_containingCell Du g Q z hρ hsub
  have hnorm := ENNReal.ofReal_le_ofReal
    (mixedNormalization_le_of_side_le hρ (dyadicScale_pos _) hside)
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 512)] at hnorm
  unfold rawSymmetricMixedGradientActivity
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _)]
  calc
    _ ≤ ENNReal.ofReal (ρ ^ (-(3 / 2 : ℝ))) *
        arrayMixedGradientIntegral Du (vec3Ball z.1 ρ)
          (Ioo (z.2 - ρ ^ 2) (z.2 + ρ ^ 2)) :=
      mul_le_mul' le_rfl ENNReal.ofReal_toReal_le
    _ ≤ _ := by
      unfold dyadicMixedGradientActivity dyadicMixedActivity
      exact (mul_le_mul' hnorm hmass).trans_eq (by norm_num; ring)

/-- Adjacency supplies one of the sixteen grids with side between `r/32` and
`r/16`, containing the actual recurrence cost cylinder of radius `r/512`. -/
theorem exists_adjacent_cell_mixedGradient_comparison
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    ∃ (g : ParabolicGridShift) (Q : ParabolicDyadicIndex),
      r / 32 ≤ dyadicScale Q.scale ∧ dyadicScale Q.scale < r / 16 ∧
        z ∈ shiftedParabolicDyadicCell g Q ∧
        rawSymmetricL3Cylinder z (r / 512) ⊆ shiftedParabolicDyadicCell g Q ∧
        ENNReal.ofReal (rawSymmetricMixedGradientActivity Du z (r / 512)) ≤
          512 * dyadicMixedGradientActivity g Du Q := by
  obtain ⟨g, Q, hlo, hhi, hball⟩ := exists_adjacent_parabolic_cell z
    (by positivity : 0 < r / 512)
  have hsub := (rawSymmetricL3Cylinder_subset_closedBall z (by positivity)).trans hball
  refine ⟨g, Q, ?_, ?_, hball (Metric.mem_closedBall_self (by positivity)), hsub, ?_⟩
  · linarith only [hlo]
  · linarith only [hhi]
  · exact rawSymmetricMixedGradientActivity_le_containingCell Du g Q z
      (by positivity) hsub (by linarith only [hhi, hr])

end FluidSingularSets
