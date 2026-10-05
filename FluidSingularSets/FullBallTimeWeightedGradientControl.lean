-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallProjectedGradientControl

/-!
# Actual original gradient transfer with a genuine time cutoff

The literal corrected gradient, multiplied by sqrt(θ) φ³, is bounded by the
same θ φ⁶ coordinate density that appears in the projected local energy.
On every inner spacetime set where the test is one, this actual weighted
dissipation controls the original gradient, with a genuine source error.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual time-weighted matrix norm is bounded by the literal tested gradient density. -/
theorem time_weighted_gradient_enorm_sq_le_density
    (D : Fin 3 → Vec3) (φ : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ‖(Real.sqrt θ * φ ^ 3) • D‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (projectedGradientSquare D) * ENNReal.ofReal (φ ^ 6) *
        ENNReal.ofReal θ := by
  have hp : 0 ≤ φ ^ 6 := by positivity
  have hl : ‖(Real.sqrt θ * φ ^ 3) • D‖ ^ 2 ≤
      projectedGradientSquare D * φ ^ 6 * θ := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hθ,
      ← pow_mul]
    exact (mul_le_mul_of_nonneg_left (norm_sq_le_projectedGradientSquare D)
      (mul_nonneg hθ hp)).trans_eq (by ring)
  have hh := ENNReal.ofReal_le_ofReal hl
  simpa only [ENNReal.rpow_ofNat, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_mul
      (projectedGradientSquare_nonneg D), ENNReal.ofReal_mul
        (mul_nonneg (projectedGradientSquare_nonneg D) hp)] using hh

/-- The original gradient's literal density has its actual projected and harmonic split. -/
theorem fullBall_original_gradient_density_le_split
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (z : ParabolicPoint) :
    ENNReal.ofReal (projectedGradientSquare (D z)) ≤
      2 * ENNReal.ofReal (projectedGradientSquare
        (fullBallProjectedVelocityDerivativeAmbient u D p a b c z)) +
      2 * ENNReal.ofReal (projectedGradientSquare
        (fullBallProjectedHarmonicDerivativeAmbient u D p a b c z)) := by
  let V := fullBallProjectedVelocityDerivativeAmbient u D p a b c z
  let H := fullBallProjectedHarmonicDerivativeAmbient u D p a b c z
  have he : V - H = D z :=
    fullBallProjectedVelocityDerivativeAmbient_sub_harmonic u D p a b c z
  have hh := ENNReal.ofReal_le_ofReal (projectedGradientSquare_sub_le_two V H)
  rw [he, ENNReal.ofReal_add
    (mul_nonneg (by norm_num) (projectedGradientSquare_nonneg _))
    (mul_nonneg (by norm_num) (projectedGradientSquare_nonneg _)),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at hh
  simpa only [ENNReal.ofReal_ofNat] using hh

/-- A genuine spacetime unit test transfers projected dissipation to the original solution. -/
theorem fullBall_original_gradient_le_actual_tested_projected_and_source
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) {A : Set ParabolicPoint} {B : Set Vec3}
    (hA : MeasurableSet A) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (hAB : A ⊆ B ×ˢ Ioo a b) {ψ : ParabolicPoint → ℝ}
    (hψone : ∀ z ∈ A, ψ z = 1) :
    (∫⁻ z in A, ENNReal.ofReal (projectedGradientSquare (D z))) ≤
      2 * (∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
        ENNReal.ofReal (projectedGradientSquare
          (fullBallProjectedVelocityDerivativeAmbient u D p a b c z)) *
            ENNReal.ofReal (ψ z)) +
      18 * fullBallProjectedHarmonicSquareCoefficient ρ *
        ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2 := by
  let V := fullBallProjectedVelocityDerivativeAmbient u D p a b c
  let H := fullBallProjectedHarmonicDerivativeAmbient u D p a b c
  have hv : (∫⁻ z in A, ENNReal.ofReal (projectedGradientSquare (V z))) ≤
      ∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
        ENNReal.ofReal (projectedGradientSquare (V z)) * ENNReal.ofReal (ψ z) := by
    calc
      _ = ∫⁻ z in A,
          ENNReal.ofReal (projectedGradientSquare (V z)) * ENNReal.ofReal (ψ z) := by
        apply setLIntegral_congr_fun hA
        intro z hz
        change ENNReal.ofReal (projectedGradientSquare (V z)) =
          ENNReal.ofReal (projectedGradientSquare (V z)) * ENNReal.ofReal (ψ z)
        rw [hψone z hz]
        simp
      _ ≤ _ := lintegral_mono_set hAB
  have hHs : (∫⁻ z in A, ENNReal.ofReal (projectedGradientSquare (H z))) ≤
      9 * fullBallProjectedHarmonicSquareCoefficient ρ *
        ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2 :=
    (lintegral_mono_set hAB).trans
      (fullBallProjectedHarmonicGradientSquare_joint_le_six_moment
        hsol hbox hab hc hρ hρone hB hBK)
  obtain ⟨_, hD⟩ := fullBallProjectedVelocityAmbient_joint_memLp_two
    hsol hbox hab hc hρ hρone hBK
  have hm := hD.aestronglyMeasurable.mono_measure (Measure.restrict_mono_set volume hAB)
  have hcont : Continuous (fun W : Fin 3 → Vec3 ↦
      (2 : ℝ≥0∞) * ENNReal.ofReal (projectedGradientSquare W)) := by
    unfold projectedGradientSquare
    exact (ENNReal.continuous_const_mul (by norm_num)).comp
      (ENNReal.continuous_ofReal.comp (by fun_prop))
  have hvm : AEMeasurable (fun z : ParabolicPoint ↦
      (2 : ℝ≥0∞) * ENNReal.ofReal (projectedGradientSquare (V z))) (volume.restrict A) :=
    (hcont.comp_aestronglyMeasurable hm).aemeasurable
  calc
    _ ≤ ∫⁻ z in A, 2 * ENNReal.ofReal (projectedGradientSquare (V z)) +
        2 * ENNReal.ofReal (projectedGradientSquare (H z)) :=
      lintegral_mono (fullBall_original_gradient_density_le_split u D p a b c)
    _ = (∫⁻ z in A, 2 * ENNReal.ofReal (projectedGradientSquare (V z))) +
        (∫⁻ z in A, 2 * ENNReal.ofReal (projectedGradientSquare (H z))) :=
      lintegral_add_left' hvm _
    _ = 2 * (∫⁻ z in A, ENNReal.ofReal (projectedGradientSquare (V z))) +
        2 * (∫⁻ z in A, ENNReal.ofReal (projectedGradientSquare (H z))) :=
      congrArg₂ (fun r s : ℝ≥0∞ ↦ r + s)
        (lintegral_const_mul' _ _ (by norm_num)) (lintegral_const_mul' _ _ (by norm_num))
    _ ≤ _ := (add_le_add (mul_le_mul' le_rfl hv)
      (mul_le_mul' le_rfl hHs)).trans_eq (by ring)

end FluidSingularSets
