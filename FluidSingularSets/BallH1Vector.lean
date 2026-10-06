-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.LocalBoxEnergyForces
public import CKN.Foundation.Parabolic.Doubling

/-!
# Genuine same-ball weak vector Sobolev with radius-explicit mean

The weak scalar Sobolev-Poincare theorem controls oscillation on the same ball.
The true spatial mean has reciprocal-radius scaling, giving a uniform vector
H¹-to-L⁶ estimate with the correct lower-order radius factor.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual coefficient controlling a spatial mean on a ball. -/
def ballH1MeanCoefficient (r : ℝ) : ℝ≥0∞ :=
  (volume (vec3Ball (0 : Vec3) r))⁻¹ *
    volume (vec3Ball (0 : Vec3) r) ^ (1 / 2 : ℝ) *
      volume (vec3Ball (0 : Vec3) r) ^ (1 / 6 : ℝ)

private theorem ballH1MeanCoefficient_eq_volume_power {r : ℝ} (hr : 0 < r) :
    ballH1MeanCoefficient r = volume (vec3Ball (0 : Vec3) r) ^ (-1 / 3 : ℝ) := by
  have h0 : volume (vec3Ball (0 : Vec3) r) ≠ 0 := (volume_vec3Ball_pos hr).ne'
  have ht : volume (vec3Ball (0 : Vec3) r) ≠ ∞ := volume_vec3Ball_lt_top.ne
  unfold ballH1MeanCoefficient
  rw [← ENNReal.rpow_neg_one,
    ← ENNReal.rpow_add (-1) (1 / 2) h0 ht,
    ← ENNReal.rpow_add (-1 + 1 / 2) (1 / 6) h0 ht]
  norm_num

/-- The actual spatial-mean coefficient scales by exactly the reciprocal radius. -/
theorem ballH1MeanCoefficient_scale {r : ℝ} (hr : 0 < r) :
    ballH1MeanCoefficient r = ENNReal.ofReal r⁻¹ * fullUnitBallMeanCoefficient := by
  rw [ballH1MeanCoefficient_eq_volume_power hr]
  have hv : volume (vec3Ball (0 : Vec3) r) =
      ENNReal.ofReal r ^ 3 * volume (vec3Ball (0 : Vec3) 1) := by
    simpa only [mul_one, ENNReal.ofReal_pow hr.le] using
      (volume_vec3Ball_scale (r := 1) hr)
  rw [hv, ENNReal.mul_rpow_of_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    volume_vec3Ball_lt_top.ne, ← ENNReal.rpow_ofNat, ← ENNReal.rpow_mul]
  norm_num only [show (3 : ℝ) * (-1 / 3) = -1 by norm_num]
  rw [ENNReal.rpow_neg_one, ← ENNReal.ofReal_inv_of_pos hr]
  change _ = _ * ballH1MeanCoefficient 1
  rw [ballH1MeanCoefficient_eq_volume_power zero_lt_one]
  norm_num

private theorem fullBall_eLpNorm_vector_six_le_sum {μ : Measure Vec3}
    {u : Vec3 → Vec3} (hu : AEStronglyMeasurable u μ) :
    eLpNorm u 6 μ ≤ ∑ j : Fin 3, eLpNorm (fun x ↦ u x j) 6 μ := by
  calc
    _ ≤ eLpNorm (fun x ↦ ∑ j : Fin 3, ‖u x j‖) 6 μ := by
      apply eLpNorm_mono_ae hu
      exact ae_of_all _ (fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))]
        apply (pi_norm_le_iff_of_nonneg
          (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))).mpr
        intro j
        exact Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ j))
    _ = eLpNorm (∑ j : Fin 3, fun x ↦ ‖u x j‖) 6 μ := rfl
    _ ≤ ∑ j : Fin 3, eLpNorm (fun x ↦ ‖u x j‖) 6 μ :=
      eLpNorm_sum_le (by norm_num)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact eLpNorm_norm _ ((continuous_apply j).comp_aestronglyMeasurable hu)

/-- Genuine same-ball weak gradients give the scale-uniform vector Sobolev estimate. -/
theorem ballH1Vector_sobolev
    {r : ℝ} (hr : 0 < r) {u : Vec3 → Vec3} {D : Vec3 → Fin 3 → Vec3}
    (hu : MemLp u 2 (volume.restrict (vec3Ball 0 r)))
    (hD : MemLp D 2 (volume.restrict (vec3Ball 0 r)))
    (hw : ∀ j : Fin 3, HasWeakGradientOn (vec3Ball 0 r)
      (fun x ↦ u x j) (fun x ↦ D x j)) :
    eLpNorm u 6 (volume.restrict (vec3Ball 0 r)) ≤ fullUnitBallH1Coefficient *
      (eLpNorm D 2 (volume.restrict (vec3Ball 0 r)) +
        ENNReal.ofReal r⁻¹ * eLpNorm u 2 (volume.restrict (vec3Ball 0 r))) := by
  let μ : Measure Vec3 := volume.restrict (vec3Ball 0 r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  have hμ : μ univ ≠ 0 := by
    simp only [μ, Measure.restrict_apply_univ]
    exact (volume_vec3Ball_pos hr).ne'
  have hcomp (j : Fin 3) : eLpNorm (fun x ↦ u x j) 6 μ ≤
      (sobolevPoincareL6Constant + fullUnitBallMeanCoefficient) *
        (eLpNorm D 2 μ + ENNReal.ofReal r⁻¹ * eLpNorm u 2 μ) := by
    have hB : euclideanBall (0 : Vec3) r = vec3Ball 0 r :=
      euclideanBall_eq_vec3Ball hr
    let v : H1Function (euclideanBall 0 r) :=
      { toFun := fun x ↦ u x j
        grad := fun x ↦ D x j
        memL2 := by simpa only [MemL2On, MemLpOn, hB] using hu.eval j
        gradMemL2 := fun i ↦ by
          simpa only [MemLpOn, hB] using (hD.eval j).eval i
        hasWeakGradient := by
          simpa only [hB] using hw j }
    have hs := sobolevPoincare_L6_ball_weak (0 : Vec3) hr v
    simp only [lpNormOn, weakGradientLpNormOn, hB] at hs
    change eLpNorm (fun x ↦ u x j - average μ (fun y ↦ u y j)) 6 μ ≤
      sobolevPoincareL6Constant * eLpNorm (fun x ↦ D x j) 2 μ at hs
    have hg : eLpNorm (fun x ↦ D x j) 2 μ ≤ eLpNorm D 2 μ :=
      eLpNorm_mono_ae ((hD.eval j).aestronglyMeasurable)
        (ae_of_all _ (fun x ↦ norm_le_pi_norm (D x) j))
    have hv : eLpNorm (fun x ↦ u x j) 2 μ ≤ eLpNorm u 2 μ :=
      eLpNorm_mono_ae ((hu.eval j).aestronglyMeasurable)
        (ae_of_all _ (fun x ↦ norm_le_pi_norm (u x) j))
    have hmean : eLpNorm (fun _ : Vec3 ↦ average μ (fun y ↦ u y j)) 6 μ ≤
        ballH1MeanCoefficient r * eLpNorm u 2 μ := by
      rw [eLpNorm_const' _ (by norm_num : (6 : ℝ≥0∞) ≠ 0) (by norm_num),
        ENNReal.toReal_ofNat]
      have ha := enorm_average_le_energy hμ (hu.eval j).aestronglyMeasurable
      apply (mul_le_mul_left ha _).trans
      calc
        _ ≤ ((μ univ)⁻¹ * (eLpNorm u 2 μ * (μ univ) ^ (1 / 2 : ℝ))) *
            (μ univ) ^ (1 / 6 : ℝ) := by gcongr
        _ = _ := by
          simp only [μ, Measure.restrict_apply_univ, ballH1MeanCoefficient]
          ring
    have hid : (fun x ↦ u x j) =
        (fun x ↦ u x j - average μ (fun y ↦ u y j)) +
          (fun _ ↦ average μ (fun y ↦ u y j)) := by
      funext x
      simp only [Pi.add_apply, sub_add_cancel]
    calc
      _ ≤ eLpNorm (fun x ↦ u x j - average μ (fun y ↦ u y j)) 6 μ +
          eLpNorm (fun _ : Vec3 ↦ average μ (fun y ↦ u y j)) 6 μ := by
        conv_lhs => rw [hid]
        exact eLpNorm_add_le (by norm_num)
      _ ≤ sobolevPoincareL6Constant * eLpNorm D 2 μ +
          ballH1MeanCoefficient r * eLpNorm u 2 μ :=
        add_le_add (hs.trans (mul_le_mul_right hg _)) hmean
      _ ≤ _ := by
        rw [ballH1MeanCoefficient_scale hr]
        calc
          _ ≤ sobolevPoincareL6Constant *
              (eLpNorm D 2 μ + ENNReal.ofReal r⁻¹ * eLpNorm u 2 μ) +
              fullUnitBallMeanCoefficient *
              (eLpNorm D 2 μ + ENNReal.ofReal r⁻¹ * eLpNorm u 2 μ) := by
            apply add_le_add
            · exact mul_le_mul' le_rfl le_self_add
            · calc
                _ = fullUnitBallMeanCoefficient *
                    (ENNReal.ofReal r⁻¹ * eLpNorm u 2 μ) := by ring
                _ ≤ _ := mul_le_mul' le_rfl le_add_self
          _ = _ := by ring
  calc
    _ ≤ ∑ j : Fin 3, eLpNorm (fun x ↦ u x j) 6 μ :=
      fullBall_eLpNorm_vector_six_le_sum hu.aestronglyMeasurable
    _ ≤ ∑ _j : Fin 3, (sobolevPoincareL6Constant + fullUnitBallMeanCoefficient) *
        (eLpNorm D 2 μ + ENNReal.ofReal r⁻¹ * eLpNorm u 2 μ) := Finset.sum_le_sum fun j _ ↦ hcomp j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_ofNat, fullUnitBallH1Coefficient, μ, mul_assoc]


/-- Genuine same-ball weak Sobolev retains the square energy and reciprocal-square factor. -/
theorem ballH1Vector_sobolev_square
    {r : ℝ} (hr : 0 < r) {u : Vec3 → Vec3} {D : Vec3 → Fin 3 → Vec3}
    (hu : MemLp u 2 (volume.restrict (vec3Ball 0 r)))
    (hD : MemLp D 2 (volume.restrict (vec3Ball 0 r)))
    (hw : ∀ j : Fin 3, HasWeakGradientOn (vec3Ball 0 r)
      (fun x ↦ u x j) (fun x ↦ D x j)) :
    eLpNorm u 6 (volume.restrict (vec3Ball 0 r)) ^ 2 ≤
      2 * fullUnitBallH1Coefficient ^ 2 *
        (eLpNorm D 2 (volume.restrict (vec3Ball 0 r)) ^ 2 +
          ENNReal.ofReal r⁻¹ ^ 2 * eLpNorm u 2 (volume.restrict (vec3Ball 0 r)) ^ 2) := by
  have h := pow_le_pow_left' (ballH1Vector_sobolev hr hu hD hw) 2
  rw [mul_pow] at h
  have ha := ENNReal.rpow_add_le_mul_rpow_add_rpow
    (eLpNorm D 2 (volume.restrict (vec3Ball 0 r)))
    (ENNReal.ofReal r⁻¹ * eLpNorm u 2 (volume.restrict (vec3Ball 0 r)))
    (by norm_num : (1 : ℝ) ≤ 2)
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.rpow_ofNat, mul_pow] at ha
  exact (h.trans (mul_le_mul' le_rfl ha)).trans_eq (by ring)

/-- Genuine weak Sobolev gives the spatial L⁶ class on the same ball. -/
theorem ballH1Vector_memLp_six_sameBall
    {r : ℝ} (hr : 0 < r) {u : Vec3 → Vec3} {D : Vec3 → Fin 3 → Vec3}
    (hu : MemLp u 2 (volume.restrict (vec3Ball 0 r)))
    (hD : MemLp D 2 (volume.restrict (vec3Ball 0 r)))
    (hw : ∀ j : Fin 3, HasWeakGradientOn (vec3Ball 0 r)
      (fun x ↦ u x j) (fun x ↦ D x j)) :
    MemLp u 6 (volume.restrict (vec3Ball 0 r)) :=
  (ballH1Vector_sobolev hr hu hD hw).trans_lt (ENNReal.mul_lt_top
    fullUnitBallH1Coefficient_ne_top.lt_top (ENNReal.add_lt_top.mpr
      ⟨hD.eLpNorm_lt_top, ENNReal.mul_lt_top ENNReal.ofReal_ne_top.lt_top
        hu.eLpNorm_lt_top⟩))

end FluidSingularSets
