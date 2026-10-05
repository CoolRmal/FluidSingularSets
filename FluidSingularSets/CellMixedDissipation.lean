-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ConcreteTraceCarleson
public import FluidSingularSets.ActivityMeasurability

/-!
# The actual cell mixed integral is controlled by cell dissipation

Spatial Hölder gives the factor one over the cell side after applying the
normalization in the trace activity. Finite energy therefore gives finite cell
activity, and zero dissipation forces zero mixed activity without division.
-/

@[expose] public section

open MeasureTheory Set CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The sixth-root spatial volume and the three-halves mixed normalization
leave precisely the inverse side length. -/
theorem cellMixedNormalization_volume_identity
    (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) :
    ENNReal.ofReal (dyadicScale Q.scale ^ (-3 / 2 : ℝ)) *
        volume (parabolicSpatialCube g Q) ^ (1 / 6 : ℝ) =
      ENNReal.ofReal ((dyadicScale Q.scale)⁻¹) := by
  have hℓ := dyadicScale_pos Q.scale
  unfold parabolicSpatialCube
  rw [volume_shiftedDyadicCube, ← ENNReal.ofReal_pow hℓ.le,
    ENNReal.ofReal_rpow_of_pos (pow_pos hℓ 3),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hℓ.le _)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ.le, ← Real.rpow_add hℓ]
  norm_num
  exact Real.rpow_neg_one _

/-- Actual almost everywhere measurable gradient data give the cell mixed
bound by normalized quadratic dissipation. No finiteness hypothesis is needed. -/
theorem dyadicMixedGradientActivity_le_normalizedDissipation
    (D : ParabolicPoint → Fin 3 → Vec3) (hD : AEStronglyMeasurable D volume)
    (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) :
    dyadicMixedGradientActivity g D Q ≤ ENNReal.ofReal ((dyadicScale Q.scale)⁻¹) *
      ∫⁻ a in shiftedParabolicDyadicCell g Q, ‖D a‖ₑ ^ (2 : ℕ) := by
  have hDc : AEStronglyMeasurable D
      (volume.restrict (shiftedParabolicDyadicCell g Q)) :=
    hD.mono_measure Measure.restrict_le_self
  have h := arrayMixedGradientIntegral_le_dissipation D (parabolicSpatialCube g Q)
    (shiftedParabolicDyadicTime g Q.scale Q.timeCorner) hDc
  simp only [ENNReal.rpow_ofNat] at h
  unfold dyadicMixedGradientActivity dyadicMixedActivity
  calc
    _ ≤ ENNReal.ofReal (dyadicScale Q.scale ^ (-3 / 2 : ℝ)) *
        (volume (parabolicSpatialCube g Q) ^ (1 / 6 : ℝ) *
          ∫⁻ a in shiftedParabolicDyadicCell g Q, ‖D a‖ₑ ^ (2 : ℕ)) :=
      mul_le_mul' le_rfl h
    _ = _ := by rw [← mul_assoc, cellMixedNormalization_volume_identity]

/-- Finite global quadratic energy makes every literal shifted-cell mixed
gradient activity finite. -/
theorem dyadicMixedGradientActivity_lt_top
    (D : ParabolicPoint → Fin 3 → Vec3) (hD : AEStronglyMeasurable D volume)
    (henergy : (∫⁻ a, ‖D a‖ₑ ^ (2 : ℕ)) < ⊤)
    (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) :
    dyadicMixedGradientActivity g D Q < ⊤ := by
  apply (dyadicMixedGradientActivity_le_normalizedDissipation D hD g Q).trans_lt
  apply ENNReal.mul_lt_top
  · exact ENNReal.ofReal_lt_top
  · exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt henergy

/-- A zero dissipation cell has zero actual mixed activity. This also covers
the zero-denominator case in square-root charge comparisons. -/
theorem dyadicMixedGradientActivity_eq_zero_of_dissipation_eq_zero
    (D : ParabolicPoint → Fin 3 → Vec3) (hD : AEStronglyMeasurable D volume)
    (g : ParabolicGridShift) (Q : ParabolicDyadicIndex)
    (hzero : (∫⁻ a in shiftedParabolicDyadicCell g Q, ‖D a‖ₑ ^ (2 : ℕ)) = 0) :
    dyadicMixedGradientActivity g D Q = 0 := by
  have hle : dyadicMixedGradientActivity g D Q ≤ 0 := by
    simpa only [hzero, mul_zero] using
      dyadicMixedGradientActivity_le_normalizedDissipation D hD g Q
  exact le_antisymm hle bot_le

end FluidSingularSets
