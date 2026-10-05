-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallMarginCoefficients

/-!
# True endpoint coefficients in the nested cutoff gap

The actual projected joint-square and harmonic Hessian-square coefficients
have fixed reciprocal sixth and twelfth boundary-gap bounds. The midpoint
margin is at least half the nested radius gap, yielding genuine uniform
coefficients for the actual endpoint energy estimates.
-/

@[expose] public section

open CKN MeasureTheory Set
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A genuine fixed coefficient for the corrected velocity joint-square source bound. -/
def fullBallFixedProjectedSquareConstant : ℝ :=
  fullBallFixedProjectedSliceConstant ^ 2 *
    (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (2 / 3 : ℝ)

theorem fullBallFixedProjectedSquareConstant_nonneg :
    0 ≤ fullBallFixedProjectedSquareConstant := by
  unfold fullBallFixedProjectedSquareConstant
  positivity

/-- A genuine fixed coefficient for the harmonic derivative joint-square source bound. -/
def fullBallFixedHarmonicSquareConstant : ℝ :=
  fullBallFixedHarmonicHessianConstant ^ 2 *
    (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (5 / 3 : ℝ)

theorem fullBallFixedHarmonicSquareConstant_nonneg :
    0 ≤ fullBallFixedHarmonicSquareConstant := by
  unfold fullBallFixedHarmonicSquareConstant
  positivity

/-- The actual native corrected joint-square coefficient has its literal real value. -/
theorem fullBallProjectedVelocitySquareCoefficient_toReal (ρ : ℝ) :
    (fullBallProjectedVelocitySquareCoefficient ρ).toReal =
      (fullBallProjectedVelocitySliceCoefficient ρ).toReal ^ 2 *
        (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (2 / 3 : ℝ) := by
  rw [fullBallProjectedVelocitySquareCoefficient, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_rpow]

/-- The actual native harmonic joint-square coefficient has its literal real value. -/
theorem fullBallProjectedHarmonicSquareCoefficient_toReal {ρ : ℝ} (hρone : ρ < 1) :
    (fullBallProjectedHarmonicSquareCoefficient ρ).toReal =
      fullBallProjectedHarmonicHessianVelocityConstant ρ ^ 2 *
        (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (5 / 3 : ℝ) := by
  rw [fullBallProjectedHarmonicSquareCoefficient, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (fullBallProjectedHarmonicHessianVelocityConstant_nonneg hρone),
    ENNReal.toReal_rpow]

/-- Genuine corrected velocity source control costs the reciprocal sixth margin power. -/
theorem fullBallProjectedVelocitySquareCoefficient_toReal_le_gap {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρone : ρ < 1) :
    (fullBallProjectedVelocitySquareCoefficient ρ).toReal ≤
      fullBallFixedProjectedSquareConstant / (1 - ρ) ^ 6 := by
  rw [fullBallProjectedVelocitySquareCoefficient_toReal]
  have hh := pow_le_pow_left₀ ENNReal.toReal_nonneg
    (fullBallProjectedVelocitySliceCoefficient_toReal_le_gap hρ hρone) 2
  calc
    _ ≤ (fullBallFixedProjectedSliceConstant / (1 - ρ) ^ 3) ^ 2 *
        (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    _ = _ := by
      unfold fullBallFixedProjectedSquareConstant
      rw [div_pow, ← pow_mul]
      norm_num only [show (3 : ℕ) * 2 = 6 by norm_num]
      ring

/-- Genuine harmonic derivative source control costs the reciprocal twelfth margin power. -/
theorem fullBallProjectedHarmonicSquareCoefficient_toReal_le_gap {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρone : ρ < 1) :
    (fullBallProjectedHarmonicSquareCoefficient ρ).toReal ≤
      fullBallFixedHarmonicSquareConstant / (1 - ρ) ^ 12 := by
  rw [fullBallProjectedHarmonicSquareCoefficient_toReal hρone]
  have hh := pow_le_pow_left₀
    (fullBallProjectedHarmonicHessianVelocityConstant_nonneg hρone)
    (fullBallProjectedHarmonicHessianVelocityConstant_le_gap hρ hρone) 2
  calc
    _ ≤ (fullBallFixedHarmonicHessianConstant / (1 - ρ) ^ 6) ^ 2 *
        (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (5 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    _ = _ := by
      unfold fullBallFixedHarmonicSquareConstant
      rw [div_pow, ← pow_mul]
      norm_num only [show (6 : ℕ) * 2 = 12 by norm_num]
      ring

/-- A midpoint's genuine projection margin is at least half the nested radius gap. -/
theorem fullBall_midpoint_margin_lower {r R : ℝ} (hR : R ≤ 1) :
    (R - r) / 2 ≤ 1 - (r + R) / 2 := by linarith

/-- A genuine fixed reciprocal midpoint margin bound gives a uniform radius-gap bound. -/
theorem reciprocal_midpoint_margin_le_gap {r R K : ℝ} (hrR : r < R) (hR : R ≤ 1)
    (hK : 0 ≤ K) (n : ℕ) :
    K / (1 - (r + R) / 2) ^ n ≤ (2 : ℝ) ^ n * K / (R - r) ^ n := by
  have hd : 0 < (R - r) / 2 := by linarith
  have hm := fullBall_midpoint_margin_lower (r := r) hR
  calc
    _ ≤ K / ((R - r) / 2) ^ n :=
      div_le_div_of_nonneg_left hK (pow_pos hd _) (pow_le_pow_left₀ hd.le hm _)
    _ = _ := by rw [div_pow, div_div_eq_mul_div]; ring

/-- The actual corrected slice coefficient at the midpoint costs the reciprocal cubed gap. -/
theorem fullBallProjectedVelocitySliceCoefficient_midpoint_le_gap {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hR : R ≤ 1) :
    (fullBallProjectedVelocitySliceCoefficient ((r + R) / 2)).toReal ≤
      8 * fullBallFixedProjectedSliceConstant / (R - r) ^ 3 := by
  have hρ : 0 ≤ (r + R) / 2 := by linarith
  have hρone : (r + R) / 2 < 1 := by linarith
  exact (fullBallProjectedVelocitySliceCoefficient_toReal_le_gap hρ hρone).trans
    (by simpa only [show (2 : ℝ) ^ (3 : ℕ) = 8 by norm_num] using
      reciprocal_midpoint_margin_le_gap hrR hR fullBallFixedProjectedSliceConstant_nonneg 3)

/-- The true corrected joint-square coefficient at the midpoint has a sixth radius-gap bound. -/
theorem fullBallProjectedVelocitySquareCoefficient_midpoint_le_gap {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hR : R ≤ 1) :
    (fullBallProjectedVelocitySquareCoefficient ((r + R) / 2)).toReal ≤
      64 * fullBallFixedProjectedSquareConstant / (R - r) ^ 6 := by
  have hρ : 0 ≤ (r + R) / 2 := by linarith
  have hρone : (r + R) / 2 < 1 := by linarith
  exact (fullBallProjectedVelocitySquareCoefficient_toReal_le_gap hρ hρone).trans
    (by simpa only [show (2 : ℝ) ^ (6 : ℕ) = 64 by norm_num] using
      reciprocal_midpoint_margin_le_gap hrR hR fullBallFixedProjectedSquareConstant_nonneg 6)

/-- The true harmonic joint-square coefficient at the midpoint has a twelfth radius-gap bound. -/
theorem fullBallProjectedHarmonicSquareCoefficient_midpoint_le_gap {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hR : R ≤ 1) :
    (fullBallProjectedHarmonicSquareCoefficient ((r + R) / 2)).toReal ≤
      4096 * fullBallFixedHarmonicSquareConstant / (R - r) ^ 12 := by
  have hρ : 0 ≤ (r + R) / 2 := by linarith
  have hρone : (r + R) / 2 < 1 := by linarith
  exact (fullBallProjectedHarmonicSquareCoefficient_toReal_le_gap hρ hρone).trans
    (by simpa only [show (2 : ℝ) ^ (12 : ℕ) = 4096 by norm_num] using
      reciprocal_midpoint_margin_le_gap hrR hR fullBallFixedHarmonicSquareConstant_nonneg 12)

/-- The true cube-root slice factor in convection costs just one reciprocal radius gap. -/
theorem fullBallProjectedVelocitySliceCoefficient_cuberoot_midpoint_le_gap {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hR : R ≤ 1) :
    (fullBallProjectedVelocitySliceCoefficient ((r + R) / 2)).toReal ^ (1 / 3 : ℝ) ≤
      (8 * fullBallFixedProjectedSliceConstant) ^ (1 / 3 : ℝ) / (R - r) := by
  have hd : 0 < R - r := sub_pos.mpr hrR
  have hK : 0 ≤ 8 * fullBallFixedProjectedSliceConstant :=
    mul_nonneg (by norm_num) fullBallFixedProjectedSliceConstant_nonneg
  have hh := Real.rpow_le_rpow ENNReal.toReal_nonneg
    (fullBallProjectedVelocitySliceCoefficient_midpoint_le_gap hr hrR hR)
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  apply hh.trans_eq
  have he : ((R - r) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) = R - r := by
    convert Real.pow_rpow_inv_natCast hd.le (by norm_num : (3 : ℕ) ≠ 0) using 1
    norm_num
  rw [Real.div_rpow hK (pow_nonneg hd.le _), he]

/-- The literal sixth-cutoff convection coefficient has a true reciprocal squared gap bound. -/
theorem fullBall_endpoint_convectionCoefficient_midpoint_le_gap {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hR : R ≤ 1) :
    162 * (32 / (R - r)) *
      (fullBallProjectedVelocitySliceCoefficient ((r + R) / 2)).toReal ^ (1 / 3 : ℝ) ≤
      5184 * (8 * fullBallFixedProjectedSliceConstant) ^ (1 / 3 : ℝ) / (R - r) ^ 2 := by
  have hd : 0 < R - r := sub_pos.mpr hrR
  apply (mul_le_mul_of_nonneg_left
    (fullBallProjectedVelocitySliceCoefficient_cuberoot_midpoint_le_gap hr hrR hR)
    (by positivity : 0 ≤ 162 * (32 / (R - r)))).trans_eq
  field_simp
  ring

/-- The actual harmonic source Hessian at the midpoint has a sixth radius-gap bound. -/
theorem fullBallProjectedHarmonicHessianVelocityConstant_midpoint_le_gap {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hR : R ≤ 1) :
    fullBallProjectedHarmonicHessianVelocityConstant ((r + R) / 2) ≤
      64 * fullBallFixedHarmonicHessianConstant / (R - r) ^ 6 := by
  have hρ : 0 ≤ (r + R) / 2 := by linarith
  have hρone : (r + R) / 2 < 1 := by linarith
  exact (fullBallProjectedHarmonicHessianVelocityConstant_le_gap hρ hρone).trans
    (by simpa only [show (2 : ℝ) ^ (6 : ℕ) = 64 by norm_num] using
      reciprocal_midpoint_margin_le_gap hrR hR fullBallFixedHarmonicHessianConstant_nonneg 6)

/-- The actual cutoff Sobolev error has a true reciprocal eighth radius-gap source bound. -/
theorem fullBall_endpoint_sobolevErrorCoefficient_midpoint_le_gap {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hR : R ≤ 1) :
    1225 * (32 / (R - r)) ^ 2 *
      (fullBallProjectedVelocitySquareCoefficient ((r + R) / 2)).toReal ≤
      80281600 * fullBallFixedProjectedSquareConstant / (R - r) ^ 8 := by
  have hd : 0 < R - r := sub_pos.mpr hrR
  apply (mul_le_mul_of_nonneg_left
    (fullBallProjectedVelocitySquareCoefficient_midpoint_le_gap hr hrR hR)
    (by positivity : 0 ≤ 1225 * (32 / (R - r)) ^ 2)).trans_eq
  field_simp
  ring

end FluidSingularSets
