-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallProjectedSixControl

/-!
# Actual full-ball endpoint velocity moment is finite

The genuine local suitable energy and weak spatial slices imply the actual
full-ball L²-time/L⁶-space moment is finite. This is derived from the proved
nonzero-boundary H¹ Sobolev estimate, with no additional mixed-norm hypothesis.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

private theorem aemeasurable_spatial_two_square {E : Type*} [NormedAddCommGroup E]
    {B : Set Vec3} {J : Set ℝ} {F : ParabolicPoint → E}
    (hF : AEStronglyMeasurable F (volume.restrict (B ×ˢ J))) :
    AEMeasurable (fun t ↦ eLpNorm (fun x ↦ F (x, t)) 2
      (volume.restrict B) ^ (2 : ℝ)) (volume.restrict J) := by
  have hp : AEStronglyMeasurable F ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hF
  apply ((hp.enorm.pow_const (2 : ℝ)).lintegral_prod_left').congr
  filter_upwards [hp.prodMk_right] with t ht
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) ht]
  norm_num only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_mul]
  norm_num

/-- The genuine full-ball H¹ Sobolev bound has a literal quadratic energy estimate. -/
theorem fullUnitBallH1Vector_six_square_energy {v : Vec3 → Vec3}
    {D : Vec3 → Fin 3 → Vec3}
    (hv : MemLp v 2 (volume.restrict (vec3Ball 0 1)))
    (hD : MemLp D 2 (volume.restrict (vec3Ball 0 1)))
    (hw : ∀ i : Fin 3, HasWeakGradientOn (vec3Ball 0 1)
      (fun x ↦ v x i) (fun x ↦ D x i)) :
    eLpNorm v 6 (volume.restrict (vec3Ball 0 1)) ^ 2 ≤
      2 * fullUnitBallH1Coefficient ^ 2 *
        (eLpNorm D 2 (volume.restrict (vec3Ball 0 1)) ^ 2 +
          eLpNorm v 2 (volume.restrict (vec3Ball 0 1)) ^ 2) := by
  have hadd := ENNReal.rpow_add_le_mul_rpow_add_rpow
    (eLpNorm D 2 (volume.restrict (vec3Ball 0 1)))
    (eLpNorm v 2 (volume.restrict (vec3Ball 0 1))) (by norm_num : (1 : ℝ) ≤ 2)
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.rpow_ofNat] at hadd
  have hs := pow_le_pow_left' (fullUnitBallH1Vector_sobolev hv hD hw) 2
  rw [mul_pow] at hs
  exact (hs.trans (mul_le_mul' le_rfl hadd)).trans_eq (by ring)

/-- Actual suitable energy bounds the entire original endpoint velocity moment. -/
theorem suitable_fullBall_velocity_six_moment_le_energy
    {Ω : Set Vec3} {I : Set ℝ} {q a b : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) :
    (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
      (volume.restrict (vec3Ball 0 1)) ^ (2 : ℝ)) ≤
      2 * fullUnitBallH1Coefficient ^ 2 *
        ∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b,
          ‖D z‖ₑ ^ (2 : ℝ) + ‖u z‖ₑ ^ (2 : ℝ) := by
  have hw := ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)
  have hDs := hsol.toData.aestronglyMeasurable_gradient hbox
  have hUs := hsol.toData.aestronglyMeasurable_velocity hbox
  have hDA : AEMeasurable (fun t ↦ eLpNorm (fun x ↦ D (x, t)) 2
      (volume.restrict (vec3Ball 0 1)) ^ (2 : ℕ)) (volume.restrict (Ioo a b)) := by
    simpa only [ENNReal.rpow_ofNat] using aemeasurable_spatial_two_square hDs
  calc
    _ ≤ ∫⁻ t in Ioo a b, (2 * fullUnitBallH1Coefficient ^ 2) *
        (eLpNorm (fun x ↦ D (x, t)) 2 (volume.restrict (vec3Ball 0 1)) ^ 2 +
          eLpNorm (fun x ↦ u (x, t)) 2 (volume.restrict (vec3Ball 0 1)) ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [slice_memLp_ae_of_sws hsol hbox, hw] with t ht hwt
      simpa only [ENNReal.rpow_ofNat] using fullUnitBallH1Vector_six_square_energy
        ht.1 ht.2 hwt
    _ = 2 * fullUnitBallH1Coefficient ^ 2 *
        ((∫⁻ t in Ioo a b, eLpNorm (fun x ↦ D (x, t)) 2
          (volume.restrict (vec3Ball 0 1)) ^ (2 : ℕ)) +
          ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 2
            (volume.restrict (vec3Ball 0 1)) ^ (2 : ℕ)) := by
      rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top fullUnitBallH1Coefficient_ne_top))]
      exact congrArg (fun x : ℝ≥0∞ ↦ 2 * fullUnitBallH1Coefficient ^ 2 * x)
        (lintegral_add_left' hDA _)
    _ = _ := by
      apply congrArg (fun x : ℝ≥0∞ ↦ 2 * fullUnitBallH1Coefficient ^ 2 * x)
      exact (congrArg₂ (fun x y : ℝ≥0∞ ↦ x + y)
        (lintegral_spatial_two_sq_eq hDs) (lintegral_spatial_two_sq_eq hUs)).trans
          (lintegral_add_left' (hDs.enorm.pow_const (2 : ℝ)) _).symm

/-- The endpoint mixed source moment is genuinely finite for every original suitable box. -/
theorem suitable_fullBall_velocity_six_moment_lt_top
    {Ω : Set Vec3} {I : Set ℝ} {q a b : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) :
    (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
      (volume.restrict (vec3Ball 0 1)) ^ (2 : ℝ)) < ⊤ := by
  apply (suitable_fullBall_velocity_six_moment_le_energy hsol hbox).trans_lt
  apply ENNReal.mul_lt_top
  · exact (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top fullUnitBallH1Coefficient_ne_top)).lt_top
  · have he := hsol.toData.energy_lintegral_lt_top hbox
    apply lt_of_le_of_lt _ he
    apply lintegral_mono
    intro z
    exact add_comm _ _ |>.le

end FluidSingularSets
