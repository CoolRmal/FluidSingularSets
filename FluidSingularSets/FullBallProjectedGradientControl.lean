-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallHarmonicCutoffErrors
public import FluidSingularSets.GradientEnergyControl

/-!
# Original gradient controlled by genuine full-ball projected energy

The actual harmonic Hessian has a joint square bound by the original
endpoint velocity moment. The literal identity `Dv = Du + DH` then transfers
weighted projected dissipation to the original gradient on every inner set
where the actual spatial cutoff is one.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The literal squared gradient density is nonnegative. -/
theorem projectedGradientSquare_nonneg (D : Fin 3 → Vec3) :
    0 ≤ projectedGradientSquare D :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The actual matrix norm is bounded by its literal squared gradient density. -/
theorem norm_sq_le_projectedGradientSquare (D : Fin 3 → Vec3) :
    ‖D‖ ^ 2 ≤ projectedGradientSquare D :=
  array_norm_sq_le_spatialGradientSq (fun _ ↦ 0) (fun _ ↦ D) (0, 0)

/-- Nine actual scalar entries bound the literal squared gradient density. -/
theorem projectedGradientSquare_le_nine_norm_sq (D : Fin 3 → Vec3) :
    projectedGradientSquare D ≤ 9 * ‖D‖ ^ 2 := by
  have ht (i j : Fin 3) : (D i j) ^ 2 ≤ ‖D‖ ^ 2 := by
    have hn := (norm_le_pi_norm (D i) j).trans (norm_le_pi_norm D i)
    simpa only [Real.norm_eq_abs, sq_abs] using
      pow_le_pow_left₀ (norm_nonneg _) hn 2
  calc
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖D‖ ^ 2 :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ht i j
    _ = _ := by simp; ring

/-- The literal squared density obeys the same nine-entry extended norm bound. -/
theorem projectedGradientSquare_enorm_le_nine (D : Fin 3 → Vec3) :
    ENNReal.ofReal (projectedGradientSquare D) ≤ 9 * ‖D‖ₑ ^ (2 : ℝ) := by
  have hh := ENNReal.ofReal_le_ofReal (projectedGradientSquare_le_nine_norm_sq D)
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9)] at hh
  simpa only [ENNReal.ofReal_ofNat, ENNReal.rpow_ofNat, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _)] using hh

/-- The genuine difference of two gradient arrays has the usual quadratic bound. -/
theorem projectedGradientSquare_sub_le_two (A B : Fin 3 → Vec3) :
    projectedGradientSquare (A - B) ≤
      2 * projectedGradientSquare A + 2 * projectedGradientSquare B := by
  calc
    _ ≤ ∑ i, ∑ j, (2 * (A i j) ^ 2 + 2 * (B i j) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [Pi.sub_apply]
      nlinarith [sq_nonneg (A i j + B i j)]
    _ = _ := by simp [projectedGradientSquare, Finset.sum_add_distrib,
      Finset.mul_sum]

/-- The actual harmonic joint-square coefficient relative to the true endpoint moment. -/
def fullBallProjectedHarmonicSquareCoefficient (ρ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (fullBallProjectedHarmonicHessianVelocityConstant ρ) ^ 2 *
    volume (vec3Ball (0 : Vec3) 1) ^ (5 / 3 : ℝ)

/-- The genuine correction coefficient is finite at each interior radius. -/
theorem fullBallProjectedHarmonicSquareCoefficient_ne_top (ρ : ℝ) :
    fullBallProjectedHarmonicSquareCoefficient ρ ≠ ⊤ := by
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (volume_vec3Ball_lt_top (x := 0) (r := 1)).ne).ne

section LocalBox

variable {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

/-- The actual harmonic matrix has a true joint-square bound by the full velocity source. -/
theorem fullBallProjectedHarmonicDerivativeAmbient_joint_square_le_six_moment
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) {B : Set Vec3}
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ) :
    (∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
      ‖fullBallProjectedHarmonicDerivativeAmbient u D p a b c z‖ₑ ^ (2 : ℝ)) ≤
        fullBallProjectedHarmonicSquareCoefficient ρ *
          ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
            (volume.restrict (vec3Ball 0 1)) ^ 2 := by
  let H := fullBallProjectedHarmonicDerivativeAmbient u D p a b c
  let C := fullBallProjectedHarmonicHessianVelocityConstant ρ
  have hC : 0 ≤ C := fullBallProjectedHarmonicHessianVelocityConstant_nonneg hρone
  have hB1 := hBK.trans (fullBallCompactInterior_subset_unit hρ hρone)
  have hH := (fullBallProjected_correction_ambient_joint_memLp_top
    hsol hbox hab hc hρ hρone).2
  have hHm := hH.aestronglyMeasurable.mono_measure
    (Measure.restrict_mono_set volume (prod_mono hBK Subset.rfl))
  have heq : (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ H (x, t)) 2
      (volume.restrict B) ^ 2) =
      ∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
        ‖fullBallProjectedHarmonicDerivativeAmbient u D p a b c z‖ₑ ^ (2 : ℝ) :=
    lintegral_spatial_two_sq_eq hHm
  rw [← heq]
  have hb := fullBall_projected_harmonic_hessian_velocity_bound_ae
    hsol hbox hab hc hρ hρone
  have hu := fullBall_velocityCurve_two_le_six_ae hsol hbox
  have hm := hHm
  rw [volume_parabolicPoint_eq_prod, ← Measure.prod_restrict] at hm
  have hp : ∀ᵐ t ∂volume.restrict (Ioo a b),
      eLpNorm (fun x ↦ H (x, t)) 2 (volume.restrict B) ^ 2 ≤
        fullBallProjectedHarmonicSquareCoefficient ρ *
          eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) ^ 2 := by
    filter_upwards [hb, hu, hm.prodMk_right] with t ht hut hmt
    have hbound : ∀ᵐ x ∂volume.restrict B,
        ‖H (x, t)‖ ≤ C * ‖unitBallVelocityCurve u t‖ := by
      filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg _))).mpr
      intro i
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg _))).mpr
      intro j
      exact ht ⟨x, hBK hx⟩ i j
    have hn := eLpNorm_le_of_ae_bound (p := 2) hmt hbound
    simp only [ENNReal.toReal_ofNat, inv_eq_one_div, Measure.restrict_apply_univ,
      ENNReal.ofReal_mul hC, ofReal_norm] at hn
    have hs : eLpNorm (fun x ↦ H (x, t)) 2 (volume.restrict B) ≤
        ENNReal.ofReal C * volume (vec3Ball (0 : Vec3) 1) ^ (5 / 6 : ℝ) *
          eLpNorm (fun x ↦ u (x, t)) 6 (volume.restrict (vec3Ball 0 1)) := by
      apply hn.trans
      calc
        _ ≤ volume (vec3Ball (0 : Vec3) 1) ^ (1 / 2 : ℝ) *
            (ENNReal.ofReal C * (eLpNorm (fun x ↦ u (x, t)) 6
              (volume.restrict (vec3Ball 0 1)) *
                volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ))) :=
          mul_le_mul' (ENNReal.rpow_le_rpow (measure_mono hB1) (by norm_num))
            (mul_le_mul' le_rfl hut)
        _ = _ := by
          rw [show (5 / 6 : ℝ) = 1 / 2 + 1 / 3 by norm_num,
            ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 3 : ℝ)
              (by norm_num) (by norm_num)]
          ring
    have hs2 := pow_le_pow_left' hs 2
    rw [mul_pow, mul_pow,
      ← ENNReal.rpow_natCast (volume (vec3Ball (0 : Vec3) 1) ^ (5 / 6 : ℝ)) 2,
      ← ENNReal.rpow_mul] at hs2
    norm_num only [show (5 / 6 : ℝ) * 2 = 5 / 3 by norm_num] at hs2
    exact hs2
  exact (lintegral_mono_ae hp).trans_eq
    (lintegral_const_mul' _ _ (fullBallProjectedHarmonicSquareCoefficient_ne_top ρ))

/-- The literal harmonic Hessian density is bounded by the actual endpoint velocity moment. -/
theorem fullBallProjectedHarmonicGradientSquare_joint_le_six_moment
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) {B : Set Vec3}
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ) :
    (∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
      ENNReal.ofReal (projectedGradientSquare
        (fullBallProjectedHarmonicDerivativeAmbient u D p a b c z))) ≤
      9 * fullBallProjectedHarmonicSquareCoefficient ρ *
        ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2 := by
  calc
    _ ≤ ∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
        9 * ‖fullBallProjectedHarmonicDerivativeAmbient u D p a b c z‖ₑ ^ (2 : ℝ) := by
      apply lintegral_mono
      intro z
      exact projectedGradientSquare_enorm_le_nine _
    _ = 9 * ∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
        ‖fullBallProjectedHarmonicDerivativeAmbient u D p a b c z‖ₑ ^ (2 : ℝ) :=
      lintegral_const_mul' _ _ (by norm_num)
    _ ≤ _ := (mul_le_mul' le_rfl
      (fullBallProjectedHarmonicDerivativeAmbient_joint_square_le_six_moment
        hsol hbox hab hc hρ hρone hB hBK)).trans_eq (by ring)

/-- The genuine projected derivative minus its harmonic correction is the original datum. -/
theorem fullBallProjectedVelocityDerivativeAmbient_sub_harmonic
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (z : ParabolicPoint) :
    fullBallProjectedVelocityDerivativeAmbient u D p a b c z -
      fullBallProjectedHarmonicDerivativeAmbient u D p a b c z = D z :=
  add_sub_cancel_right _ _

/-- Actual unit-cutoff inner gradients are bounded by weighted projected dissipation
and the true full-ball harmonic source, without an assumed energy estimate. -/
theorem fullBall_original_gradient_le_weighted_projected_and_source
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) {A B : Set Vec3}
    (hA : IsOpen A) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ) (hAB : A ⊆ B)
    {φ : Vec3 → ℝ} (hφone : ∀ x ∈ A, φ x = 1) :
    (∫⁻ z : ParabolicPoint in A ×ˢ Ioo a b, ENNReal.ofReal (projectedGradientSquare (D z))) ≤
      2 * (∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
        ENNReal.ofReal (projectedGradientSquare
          (fullBallProjectedVelocityDerivativeAmbient u D p a b c z)) *
            ENNReal.ofReal (φ z.1 ^ 6)) +
      18 * fullBallProjectedHarmonicSquareCoefficient ρ *
        ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2 := by
  let V := fullBallProjectedVelocityDerivativeAmbient u D p a b c
  let H := fullBallProjectedHarmonicDerivativeAmbient u D p a b c
  have hp (z : ParabolicPoint) : ENNReal.ofReal (projectedGradientSquare (D z)) ≤
      2 * ENNReal.ofReal (projectedGradientSquare (V z)) +
        2 * ENNReal.ofReal (projectedGradientSquare (H z)) := by
    have he : V z - H z = D z :=
      fullBallProjectedVelocityDerivativeAmbient_sub_harmonic u D p a b c z
    have hh := ENNReal.ofReal_le_ofReal (projectedGradientSquare_sub_le_two (V z) (H z))
    rw [he, ENNReal.ofReal_add
      (mul_nonneg (by norm_num) (projectedGradientSquare_nonneg _))
      (mul_nonneg (by norm_num) (projectedGradientSquare_nonneg _)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at hh
    simpa only [ENNReal.ofReal_ofNat] using hh
  have hv : (∫⁻ z : ParabolicPoint in A ×ˢ Ioo a b,
      ENNReal.ofReal (projectedGradientSquare (V z))) ≤
      ∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
        ENNReal.ofReal (projectedGradientSquare (V z)) * ENNReal.ofReal (φ z.1 ^ 6) := by
    calc
      _ = ∫⁻ z : ParabolicPoint in A ×ˢ Ioo a b,
          ENNReal.ofReal (projectedGradientSquare (V z)) *
            ENNReal.ofReal (φ z.1 ^ 6) := by
        apply setLIntegral_congr_fun (hA.measurableSet.prod measurableSet_Ioo)
        intro z hz
        change ENNReal.ofReal (projectedGradientSquare (V z)) =
          ENNReal.ofReal (projectedGradientSquare (V z)) * ENNReal.ofReal (φ z.1 ^ 6)
        rw [hφone z.1 hz.1]
        simp
      _ ≤ _ := lintegral_mono_set (prod_mono hAB Subset.rfl)
  have hHsource := fullBallProjectedHarmonicGradientSquare_joint_le_six_moment
    hsol hbox hab hc hρ hρone hB hBK
  have hHs : (∫⁻ z : ParabolicPoint in A ×ˢ Ioo a b,
      ENNReal.ofReal (projectedGradientSquare (H z))) ≤
      9 * fullBallProjectedHarmonicSquareCoefficient ρ *
        ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2 :=
    (lintegral_mono_set (prod_mono hAB Subset.rfl)).trans hHsource
  calc
    _ ≤ ∫⁻ z : ParabolicPoint in A ×ˢ Ioo a b,
        2 * ENNReal.ofReal (projectedGradientSquare (V z)) +
          2 * ENNReal.ofReal (projectedGradientSquare (H z)) := lintegral_mono hp
    _ = 2 * (∫⁻ z : ParabolicPoint in A ×ˢ Ioo a b,
        ENNReal.ofReal (projectedGradientSquare (V z))) +
      2 * (∫⁻ z : ParabolicPoint in A ×ˢ Ioo a b,
        ENNReal.ofReal (projectedGradientSquare (H z))) := by
      obtain ⟨_, hD⟩ := fullBallProjectedVelocityAmbient_joint_memLp_two
        hsol hbox hab hc hρ hρone hBK
      have hm := hD.aestronglyMeasurable.mono_measure
        (Measure.restrict_mono_set volume (prod_mono hAB Subset.rfl))
      have hcont : Continuous (fun W : Fin 3 → Vec3 ↦
          (2 : ℝ≥0∞) * ENNReal.ofReal (projectedGradientSquare W)) := by
        unfold projectedGradientSquare
        exact (ENNReal.continuous_const_mul (by norm_num)).comp
          (ENNReal.continuous_ofReal.comp (by fun_prop))
      have hvm : AEMeasurable (fun z : ParabolicPoint ↦
          (2 : ℝ≥0∞) * ENNReal.ofReal (projectedGradientSquare (V z)))
          (volume.restrict (A ×ˢ Ioo a b)) :=
        (hcont.comp_aestronglyMeasurable hm).aemeasurable
      have hadd : (∫⁻ z : ParabolicPoint in A ×ˢ Ioo a b,
          2 * ENNReal.ofReal (projectedGradientSquare (V z)) +
            2 * ENNReal.ofReal (projectedGradientSquare (H z))) =
          (∫⁻ z : ParabolicPoint in A ×ˢ Ioo a b,
            2 * ENNReal.ofReal (projectedGradientSquare (V z))) +
          (∫⁻ z : ParabolicPoint in A ×ˢ Ioo a b,
            2 * ENNReal.ofReal (projectedGradientSquare (H z))) :=
        lintegral_add_left' hvm _
      exact hadd.trans (congrArg₂ (fun r s : ℝ≥0∞ ↦ r + s)
        (lintegral_const_mul' _ _ (by norm_num))
        (lintegral_const_mul' _ _ (by norm_num)))
    _ ≤ _ := (add_le_add (mul_le_mul' le_rfl hv)
      (mul_le_mul' le_rfl hHs)).trans_eq (by ring)

end LocalBox

end FluidSingularSets
