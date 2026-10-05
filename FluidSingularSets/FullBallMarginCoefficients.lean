-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallProjectedGradientControl

/-!
# Genuine uniform coefficients in the actual projection boundary margin

The true gradient and Hessian operators have explicit finite bounds in the
boundary gap. Bounding the Hessian's smaller-ball volume by the actual unit
volume gives a reciprocal sixth power, sufficient for the proved scalar
iteration with forcing powers up to thirty-two.
-/

@[expose] public section

open CKN MeasureTheory Set
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A true fixed coefficient for the harmonic velocity boundary-gap estimate. -/
def fullBallFixedHarmonicVelocityConstant : ℝ :=
  96 * (1728 * harmonicInteriorGradientSupConstant) *
    (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ) *
      (stokesTestPoincareConstant (vec3Ball (0 : Vec3) 1)).toReal

theorem fullBallFixedHarmonicVelocityConstant_nonneg :
    0 ≤ fullBallFixedHarmonicVelocityConstant := by
  unfold fullBallFixedHarmonicVelocityConstant
  positivity [harmonicInteriorGradientSupConstant_nonneg]

/-- The actual harmonic velocity coefficient is exactly its reciprocal cubed gap. -/
theorem fullBallProjectedHarmonicVelocityConstant_eq_gap {ρ : ℝ} (hρ : ρ < 1) :
    fullBallProjectedHarmonicVelocityConstant ρ =
      fullBallFixedHarmonicVelocityConstant / (1 - ρ) ^ 3 := by
  unfold fullBallProjectedHarmonicVelocityConstant fullBallHarmonicForceGradientCoefficient
    fullBallHarmonicGradientConstant fullBallFixedHarmonicVelocityConstant
  have hd : 1 - ρ ≠ 0 := (sub_pos.mpr hρ).ne'
  have he : 1 - (ρ + 1) / 2 = (1 - ρ) / 2 := by ring
  rw [he]
  field_simp
  ring

/-- A genuine fixed coefficient for the full-ball Hessian's reciprocal sixth gap power. -/
def fullBallFixedHarmonicHessianConstant : ℝ :=
  18432 * (1728 * harmonicInteriorGradientSupConstant) ^ 2 *
    (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (2 / 3 : ℝ) *
      (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ) *
        (stokesTestPoincareConstant (vec3Ball (0 : Vec3) 1)).toReal

theorem fullBallFixedHarmonicHessianConstant_nonneg :
    0 ≤ fullBallFixedHarmonicHessianConstant := by
  unfold fullBallFixedHarmonicHessianConstant
  positivity

/-- The actual source-derived Hessian coefficient has a genuine uniform sixth-gap bound. -/
theorem fullBallProjectedHarmonicHessianVelocityConstant_le_gap {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρone : ρ < 1) :
    fullBallProjectedHarmonicHessianVelocityConstant ρ ≤
      fullBallFixedHarmonicHessianConstant / (1 - ρ) ^ 6 := by
  let β := (ρ + 1) / 2
  have hβ : β < 1 := by dsimp [β]; linarith
  have hd : 0 < 1 - β := sub_pos.mpr hβ
  have hR : (1 - β) / 2 ≤ 1 := by dsimp [β]; linarith
  have hv : (volume (vec3Ball (0 : Vec3) ((1 - β) / 2))).toReal ≤
      (volume (vec3Ball (0 : Vec3) 1)).toReal :=
    ENNReal.toReal_mono (volume_vec3Ball_lt_top (x := 0) (r := 1)).ne
      (measure_mono (vec3Ball_mono hR))
  have hvp := Real.rpow_le_rpow ENNReal.toReal_nonneg hv (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hK := harmonicInteriorGradientSupConstant_nonneg
  have hG := fullBallHarmonicGradientConstant_nonneg hβ
  unfold fullBallProjectedHarmonicHessianVelocityConstant fullBallHarmonicForceHessianCoefficient
    fullBallHarmonicHessianConstant
  change 3 * (1728 * harmonicInteriorGradientSupConstant * (((1 - β) / 2) ^ 3)⁻¹ *
      fullBallHarmonicGradientConstant β *
        (volume (vec3Ball (0 : Vec3) ((1 - β) / 2))).toReal ^ (2 / 3 : ℝ)) *
      (4 * (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ)) *
      (3 * (stokesTestPoincareConstant (vec3Ball (0 : Vec3) 1)).toReal) ≤ _
  calc
    _ ≤ 3 * (1728 * harmonicInteriorGradientSupConstant * (((1 - β) / 2) ^ 3)⁻¹ *
        fullBallHarmonicGradientConstant β *
          (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (2 / 3 : ℝ)) *
        (4 * (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ)) *
        (3 * (stokesTestPoincareConstant (vec3Ball (0 : Vec3) 1)).toReal) := by
      gcongr
    _ = _ := by
      unfold fullBallHarmonicGradientConstant fullBallFixedHarmonicHessianConstant
      have he : 1 - β = (1 - ρ) / 2 := by dsimp [β]; ring
      rw [he]
      field_simp
      ring

/-- The actual corrected slice coefficient has a fixed reciprocal cubed-gap coefficient. -/
def fullBallFixedProjectedSliceConstant : ℝ :=
  1 + fullBallFixedHarmonicVelocityConstant *
    (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 2 : ℝ)

theorem fullBallFixedProjectedSliceConstant_nonneg :
    0 ≤ fullBallFixedProjectedSliceConstant := by
  unfold fullBallFixedProjectedSliceConstant
  positivity [fullBallFixedHarmonicVelocityConstant_nonneg]

/-- Literal conversion of the finite native slice coefficient to its actual real value. -/
theorem fullBallProjectedVelocitySliceCoefficient_toReal {ρ : ℝ} (hρone : ρ < 1) :
    (fullBallProjectedVelocitySliceCoefficient ρ).toReal =
      1 + fullBallProjectedHarmonicVelocityConstant ρ *
        (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 2 : ℝ) := by
  have hp : ENNReal.ofReal (fullBallProjectedHarmonicVelocityConstant ρ) *
      volume (vec3Ball (0 : Vec3) 1) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (volume_vec3Ball_lt_top (x := 0) (r := 1)).ne).ne
  rw [fullBallProjectedVelocitySliceCoefficient,
    ENNReal.toReal_add (by simp) hp, ENNReal.toReal_one,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (fullBallProjectedHarmonicVelocityConstant_nonneg hρone), ENNReal.toReal_rpow]

/-- The genuine corrected spatial slice coefficient has the uniform actual gap bound. -/
theorem fullBallProjectedVelocitySliceCoefficient_toReal_le_gap {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρone : ρ < 1) :
    (fullBallProjectedVelocitySliceCoefficient ρ).toReal ≤
      fullBallFixedProjectedSliceConstant / (1 - ρ) ^ 3 := by
  rw [fullBallProjectedVelocitySliceCoefficient_toReal hρone,
    fullBallProjectedHarmonicVelocityConstant_eq_gap hρone]
  have hd : 0 < 1 - ρ := sub_pos.mpr hρone
  have hdone : 1 - ρ ≤ 1 := by linarith
  have hp : (1 - ρ) ^ 3 ≤ 1 := pow_le_one₀ hd.le hdone
  apply (le_div_iff₀ (pow_pos hd 3)).mpr
  unfold fullBallFixedProjectedSliceConstant
  field_simp
  nlinarith

end FluidSingularSets
