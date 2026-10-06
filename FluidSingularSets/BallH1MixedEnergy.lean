-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.BallH1Vector
public import FluidSingularSets.EndpointVelocityInterpolation

/-!
# Genuine same-ball parabolic Sobolev and cubic/quartic energy bounds

Actual weak gradients and literal slice square energy control the mixed L²-L⁶
moment on the same cylinder. Spatial interpolation and time Hölder then give
cubic and quartic source estimates, with their precise parabolic radius factors.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Genuine weak Sobolev integrates against the actual slice-energy bound. -/
theorem ballH1Vector_mixed_six_square_le
    {r : ℝ} (hr : 0 < r) {J : Set ℝ}
    {V : ParabolicPoint → Vec3} {G : ParabolicPoint → Fin 3 → Vec3} {M : ℝ≥0∞}
    (hG : AEStronglyMeasurable G (volume.restrict (vec3Ball 0 r ×ˢ J)))
    (hw : ∀ᵐ t ∂volume.restrict J,
      MemLp (fun x ↦ V (x, t)) 2 (volume.restrict (vec3Ball 0 r)) ∧
      MemLp (fun x ↦ G (x, t)) 2 (volume.restrict (vec3Ball 0 r)) ∧
      ∀ j : Fin 3, HasWeakGradientOn (vec3Ball 0 r)
        (fun x ↦ V (x, t) j) (fun x ↦ G (x, t) j))
    (hM : ∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x ↦ V (x, t)) 2 (volume.restrict (vec3Ball 0 r)) ^ 2 ≤ M) :
    (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6
      (volume.restrict (vec3Ball 0 r)) ^ 2) ≤
      2 * fullUnitBallH1Coefficient ^ 2 *
        ((∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ J, ‖G z‖ₑ ^ (2 : ℝ)) +
          ENNReal.ofReal r⁻¹ ^ 2 * M * volume J) := by
  have hpoint : ∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict (vec3Ball 0 r)) ^ 2 ≤
        2 * fullUnitBallH1Coefficient ^ 2 *
          (eLpNorm (fun x ↦ G (x, t)) 2 (volume.restrict (vec3Ball 0 r)) ^ 2 +
            ENNReal.ofReal r⁻¹ ^ 2 * M) := by
    filter_upwards [hw, hM] with t ht hMt
    exact (ballH1Vector_sobolev_square hr ht.1 ht.2.1 ht.2.2).trans
      (mul_le_mul' le_rfl (add_le_add le_rfl (mul_le_mul' le_rfl hMt)))
  calc
    _ ≤ ∫⁻ t in J, 2 * fullUnitBallH1Coefficient ^ 2 *
        (eLpNorm (fun x ↦ G (x, t)) 2 (volume.restrict (vec3Ball 0 r)) ^ 2 +
          ENNReal.ofReal r⁻¹ ^ 2 * M) := lintegral_mono_ae hpoint
    _ = _ := by
      rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top fullUnitBallH1Coefficient_ne_top)),
        lintegral_add_right _ measurable_const, lintegral_const,
        Measure.restrict_apply_univ, lintegral_spatial_two_sq_eq hG]
      rfl

private theorem backward_volume_reciprocal_square {r τ : ℝ} (hr : 0 < r) :
    ENNReal.ofReal r⁻¹ ^ 2 * volume (Ioo (τ - r ^ 2) τ) = 1 := by
  rw [Real.volume_Ioo, show τ - (τ - r ^ 2) = r ^ 2 by ring,
    ← ENNReal.ofReal_pow (inv_nonneg.mpr hr.le),
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  have h : r⁻¹ ^ 2 * r ^ 2 = 1 := by field_simp
  rw [h, ENNReal.ofReal_one]

/-- On a genuine backward cylinder the lower-order radius term is exactly slice energy. -/
theorem ballH1Vector_backward_six_square_le
    {r τ : ℝ} (hr : 0 < r)
    {V : ParabolicPoint → Vec3} {G : ParabolicPoint → Fin 3 → Vec3} {M : ℝ≥0∞}
    (hG : AEStronglyMeasurable G
      (volume.restrict (vec3Ball 0 r ×ˢ Ioo (τ - r ^ 2) τ)))
    (hw : ∀ᵐ t ∂volume.restrict (Ioo (τ - r ^ 2) τ),
      MemLp (fun x ↦ V (x, t)) 2 (volume.restrict (vec3Ball 0 r)) ∧
      MemLp (fun x ↦ G (x, t)) 2 (volume.restrict (vec3Ball 0 r)) ∧
      ∀ j : Fin 3, HasWeakGradientOn (vec3Ball 0 r)
        (fun x ↦ V (x, t) j) (fun x ↦ G (x, t) j))
    (hM : ∀ᵐ t ∂volume.restrict (Ioo (τ - r ^ 2) τ),
      eLpNorm (fun x ↦ V (x, t)) 2 (volume.restrict (vec3Ball 0 r)) ^ 2 ≤ M) :
    (∫⁻ t in Ioo (τ - r ^ 2) τ, eLpNorm (fun x ↦ V (x, t)) 6
      (volume.restrict (vec3Ball 0 r)) ^ 2) ≤
      2 * fullUnitBallH1Coefficient ^ 2 *
        ((∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (τ - r ^ 2) τ,
          ‖G z‖ₑ ^ (2 : ℝ)) + M) := by
  convert ballH1Vector_mixed_six_square_le hr hG hw hM using 1
  rw [mul_right_comm (ENNReal.ofReal r⁻¹ ^ 2) M,
    backward_volume_reciprocal_square hr, one_mul]

/-- The genuine quartic square moment follows from literal slice energy and mixed endpoint cost. -/
theorem velocity_four_square_moment_le_energy_six
    {B : Set Vec3} {J : Set ℝ} {V : ParabolicPoint → Vec3} {M : ℝ≥0∞}
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J))) (hMfin : M < ∞)
    (hM : ∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x ↦ V (x, t)) 2 (volume.restrict B) ^ 2 ≤ M) :
    (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 4 (volume.restrict B) ^ 2) ≤
      M ^ (1 / 4 : ℝ) * volume J ^ (1 / 4 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6
          (volume.restrict B) ^ (2 : ℝ)) ^ (3 / 4 : ℝ) := by
  have hprod : AEStronglyMeasurable V ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hV
  have hp : ∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x ↦ V (x, t)) 4 (volume.restrict B) ^ 2 ≤
        M ^ (1 / 4 : ℝ) * eLpNorm (fun x ↦ V (x, t)) 6
          (volume.restrict B) ^ (3 / 2 : ℝ) := by
    filter_upwards [hprod.prodMk_right, hM] with t ht hMt
    have h := ENNReal.rpow_le_rpow (eLpNorm_interpolate_four ht)
      (by norm_num : (0 : ℝ) ≤ 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h
    norm_num only [show (1 / 4 : ℝ) * 2 = 1 / 2 by norm_num,
      show (3 / 4 : ℝ) * 2 = 3 / 2 by norm_num] at h
    rw [ENNReal.rpow_ofNat] at h
    have h2 := ENNReal.rpow_le_rpow hMt (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← ENNReal.rpow_ofNat, ← ENNReal.rpow_mul] at h2
    norm_num only [show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num] at h2
    exact h.trans (mul_le_mul' h2 le_rfl)
  calc
    _ ≤ ∫⁻ t in J, M ^ (1 / 4 : ℝ) * eLpNorm (fun x ↦ V (x, t)) 6
        (volume.restrict B) ^ (3 / 2 : ℝ) := lintegral_mono_ae hp
    _ = M ^ (1 / 4 : ℝ) * ∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6
        (volume.restrict B) ^ (3 / 2 : ℝ) :=
      lintegral_const_mul' _ _ (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hMfin.ne).ne
    _ ≤ M ^ (1 / 4 : ℝ) *
        ((∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6
          (volume.restrict B) ^ (2 : ℝ)) ^ (3 / 4 : ℝ) * volume J ^ (1 / 4 : ℝ)) :=
      mul_le_mul' le_rfl (lintegral_spatial_six_threeHalves_le hV)
    _ = _ := by ring

/-- A finite universal coefficient for parabolic energy interpolation on a ball. -/
def ballH1ParabolicInterpolationConstant : ℝ≥0∞ :=
  (2 * fullUnitBallH1Coefficient ^ 2) ^ (3 / 4 : ℝ)

theorem ballH1ParabolicInterpolationConstant_ne_top :
    ballH1ParabolicInterpolationConstant ≠ ∞ := by
  unfold ballH1ParabolicInterpolationConstant
  exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top fullUnitBallH1Coefficient_ne_top))).ne

private theorem backward_volume_quarter {r τ : ℝ} (hr : 0 < r) :
    volume (Ioo (τ - r ^ 2) τ) ^ (1 / 4 : ℝ) =
      ENNReal.ofReal r ^ (1 / 2 : ℝ) := by
  rw [Real.volume_Ioo, show τ - (τ - r ^ 2) = r ^ 2 by ring,
    ENNReal.ofReal_pow hr.le, ← ENNReal.rpow_ofNat, ← ENNReal.rpow_mul]
  norm_num

/-- Genuine projected quartic sources have the exact parabolic energy scaling. -/
theorem ballH1Vector_backward_four_square_le_energy
    {r τ : ℝ} (hr : 0 < r)
    {V : ParabolicPoint → Vec3} {G : ParabolicPoint → Fin 3 → Vec3} {M : ℝ≥0∞}
    (hV : AEStronglyMeasurable V
      (volume.restrict (vec3Ball 0 r ×ˢ Ioo (τ - r ^ 2) τ)))
    (hG : AEStronglyMeasurable G
      (volume.restrict (vec3Ball 0 r ×ˢ Ioo (τ - r ^ 2) τ)))
    (hw : ∀ᵐ t ∂volume.restrict (Ioo (τ - r ^ 2) τ),
      MemLp (fun x ↦ V (x, t)) 2 (volume.restrict (vec3Ball 0 r)) ∧
      MemLp (fun x ↦ G (x, t)) 2 (volume.restrict (vec3Ball 0 r)) ∧
      ∀ j : Fin 3, HasWeakGradientOn (vec3Ball 0 r)
        (fun x ↦ V (x, t) j) (fun x ↦ G (x, t) j))
    (hMfin : M < ∞)
    (hM : ∀ᵐ t ∂volume.restrict (Ioo (τ - r ^ 2) τ),
      eLpNorm (fun x ↦ V (x, t)) 2 (volume.restrict (vec3Ball 0 r)) ^ 2 ≤ M) :
    (∫⁻ t in Ioo (τ - r ^ 2) τ, eLpNorm (fun x ↦ V (x, t)) 4
      (volume.restrict (vec3Ball 0 r)) ^ 2) ≤
      ballH1ParabolicInterpolationConstant * ENNReal.ofReal r ^ (1 / 2 : ℝ) *
        (M + ∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (τ - r ^ 2) τ,
          ‖G z‖ₑ ^ (2 : ℝ)) := by
  let E := M + ∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (τ - r ^ 2) τ,
    ‖G z‖ₑ ^ (2 : ℝ)
  have hs := ballH1Vector_backward_six_square_le hr hG hw hM
  have hs' : (∫⁻ t in Ioo (τ - r ^ 2) τ, eLpNorm (fun x ↦ V (x, t)) 6
      (volume.restrict (vec3Ball 0 r)) ^ (2 : ℝ)) ≤
      2 * fullUnitBallH1Coefficient ^ 2 * E := by
    simpa only [ENNReal.rpow_ofNat, E, add_comm] using hs
  calc
    _ ≤ M ^ (1 / 4 : ℝ) * volume (Ioo (τ - r ^ 2) τ) ^ (1 / 4 : ℝ) *
        (∫⁻ t in Ioo (τ - r ^ 2) τ, eLpNorm (fun x ↦ V (x, t)) 6
          (volume.restrict (vec3Ball 0 r)) ^ (2 : ℝ)) ^ (3 / 4 : ℝ) :=
      velocity_four_square_moment_le_energy_six hV hMfin hM
    _ ≤ E ^ (1 / 4 : ℝ) * ENNReal.ofReal r ^ (1 / 2 : ℝ) *
        (2 * fullUnitBallH1Coefficient ^ 2 * E) ^ (3 / 4 : ℝ) := by
      rw [backward_volume_quarter hr]
      gcongr
      exact le_self_add
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      change _ = ballH1ParabolicInterpolationConstant *
        ENNReal.ofReal r ^ (1 / 2 : ℝ) * E
      conv_rhs =>
        rw [show E = E ^ (1 / 4 : ℝ) * E ^ (3 / 4 : ℝ) by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
          norm_num]
      unfold ballH1ParabolicInterpolationConstant
      ring

/-- Genuine projected cubic sources have the exact parabolic energy scaling. -/
theorem ballH1Vector_backward_cubic_le_energy
    {r τ : ℝ} (hr : 0 < r)
    {V : ParabolicPoint → Vec3} {G : ParabolicPoint → Fin 3 → Vec3} {M : ℝ≥0∞}
    (hV : AEStronglyMeasurable V
      (volume.restrict (vec3Ball 0 r ×ˢ Ioo (τ - r ^ 2) τ)))
    (hG : AEStronglyMeasurable G
      (volume.restrict (vec3Ball 0 r ×ˢ Ioo (τ - r ^ 2) τ)))
    (hw : ∀ᵐ t ∂volume.restrict (Ioo (τ - r ^ 2) τ),
      MemLp (fun x ↦ V (x, t)) 2 (volume.restrict (vec3Ball 0 r)) ∧
      MemLp (fun x ↦ G (x, t)) 2 (volume.restrict (vec3Ball 0 r)) ∧
      ∀ j : Fin 3, HasWeakGradientOn (vec3Ball 0 r)
        (fun x ↦ V (x, t) j) (fun x ↦ G (x, t) j))
    (hMfin : M < ∞)
    (hM : ∀ᵐ t ∂volume.restrict (Ioo (τ - r ^ 2) τ),
      eLpNorm (fun x ↦ V (x, t)) 2 (volume.restrict (vec3Ball 0 r)) ^ 2 ≤ M) :
    (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (τ - r ^ 2) τ,
      ‖V z‖ₑ ^ (3 : ℝ)) ≤
      ballH1ParabolicInterpolationConstant * ENNReal.ofReal r ^ (1 / 2 : ℝ) *
        (M + ∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (τ - r ^ 2) τ,
          ‖G z‖ₑ ^ (2 : ℝ)) ^ (3 / 2 : ℝ) := by
  let E := M + ∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (τ - r ^ 2) τ,
    ‖G z‖ₑ ^ (2 : ℝ)
  have hs := ballH1Vector_backward_six_square_le hr hG hw hM
  have hs' : (∫⁻ t in Ioo (τ - r ^ 2) τ, eLpNorm (fun x ↦ V (x, t)) 6
      (volume.restrict (vec3Ball 0 r)) ^ (2 : ℝ)) ≤
      2 * fullUnitBallH1Coefficient ^ 2 * E := by
    simpa only [ENNReal.rpow_ofNat, E, add_comm] using hs
  have hprod : AEStronglyMeasurable V ((volume.restrict (vec3Ball 0 r)).prod
      (volume.restrict (Ioo (τ - r ^ 2) τ))) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hV
  have he : ∀ᵐ t ∂volume.restrict (Ioo (τ - r ^ 2) τ),
      (∫⁻ x in vec3Ball 0 r, ‖V (x, t)‖ₑ ^ (2 : ℝ)) ≤ M := by
    filter_upwards [hprod.prodMk_right, hM] with t ht hMt
    have heq := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) ht
    norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at heq
    simpa only [ENNReal.rpow_ofNat] using heq.symm.trans_le hMt
  calc
    _ ≤ M ^ (3 / 4 : ℝ) * volume (Ioo (τ - r ^ 2) τ) ^ (1 / 4 : ℝ) *
        (∫⁻ t in Ioo (τ - r ^ 2) τ, eLpNorm (fun x ↦ V (x, t)) 6
          (volume.restrict (vec3Ball 0 r)) ^ (2 : ℝ)) ^ (3 / 4 : ℝ) :=
      endpoint_velocity_cubic_lintegral_le hV hMfin he
    _ ≤ E ^ (3 / 4 : ℝ) * ENNReal.ofReal r ^ (1 / 2 : ℝ) *
        (2 * fullUnitBallH1Coefficient ^ 2 * E) ^ (3 / 4 : ℝ) := by
      rw [backward_volume_quarter hr]
      gcongr
      exact le_self_add
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      change _ = ballH1ParabolicInterpolationConstant *
        ENNReal.ofReal r ^ (1 / 2 : ℝ) * E ^ (3 / 2 : ℝ)
      rw [show E ^ (3 / 2 : ℝ) = E ^ (3 / 4 : ℝ) * E ^ (3 / 4 : ℝ) by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
        norm_num]
      unfold ballH1ParabolicInterpolationConstant
      ring

end FluidSingularSets
