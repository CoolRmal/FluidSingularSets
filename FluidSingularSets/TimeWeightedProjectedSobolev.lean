-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.WeightedProjectedSobolev
public import FluidSingularSets.FullBallProjectedSixControl

/-!
# Sobolev control with the genuine time weighted gradient

For each time the square-root weight is a spatial constant. Multiplication by
it preserves the actual weak gradient. Applying the proved cutoff Sobolev
estimate to these genuine scaled fields retains the time weight in the
weighted dissipation and bounds only the cutoff error by the unweighted data.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

private theorem weakGradient_const_smul {B : Set Vec3} {v : Vec3 → ℝ}
    {D : Vec3 → Vec3} (hw : HasWeakGradientOn B v D) (a : ℝ) :
    HasWeakGradientOn B (fun x ↦ a * v x) (fun x ↦ a • D x) := by
  intro i ψ hψ hc hs
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_const_mul, integral_const_mul, hw i ψ hψ hc hs]
  ring

/-- Genuine time weighted weak data gives the exact time weighted cutoff dissipation. -/
theorem integrated_timeWeighted_cutoff_cube_sobolev_quadratic_error
    {B : Set Vec3} {J : Set ℝ} (hB : IsOpen B)
    {V : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {φ : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J)))
    (hD : AEStronglyMeasurable D (volume.restrict (B ×ˢ J)))
    (hslices : ∀ᵐ t ∂volume.restrict J,
      MemLp (fun x ↦ V (x, t)) 2 (volume.restrict B) ∧
      MemLp (fun x ↦ D (x, t)) 2 (volume.restrict B) ∧
      ∀ i : Fin 3, HasWeakGradientOn B (fun x ↦ V (x, t) i) (fun x ↦ D (x, t) i))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ B)
    (hunit : tsupport φ ⊆ euclideanBall 0 1) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hθ : Continuous θ) (hθb : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1)
    {L : ℝ} (hL : 1 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L) :
    (∫⁻ t in J, eLpNorm (fun x ↦ Real.sqrt (θ t) • (φ x ^ 3 • V (x, t))) 6
      (volume.restrict B) ^ (2 : ℝ)) ≤
      2 * (3 * localSobolevConstant) ^ 2 *
        ((∫⁻ z : ParabolicPoint in B ×ˢ J,
          ‖Real.sqrt (θ z.2) • (φ z.1 ^ 3 • D z)‖ₑ ^ (2 : ℝ)) +
          1225 * ENNReal.ofReal L ^ 2 *
            ∫⁻ z : ParabolicPoint in B ×ˢ J, ‖V z‖ₑ ^ (2 : ℝ)) := by
  let Vθ : ParabolicPoint → Vec3 := fun z ↦ Real.sqrt (θ z.2) • V z
  let Dθ : ParabolicPoint → Fin 3 → Vec3 := fun z ↦ Real.sqrt (θ z.2) • D z
  have hscalar : Continuous (fun z : ParabolicPoint ↦ Real.sqrt (θ z.2)) :=
    Real.continuous_sqrt.comp (hθ.comp continuous_snd_parabolicPoint)
  have hVθ : AEStronglyMeasurable Vθ (volume.restrict (B ×ˢ J)) :=
    hscalar.aestronglyMeasurable.smul hV
  have hDθ : AEStronglyMeasurable Dθ (volume.restrict (B ×ˢ J)) :=
    hscalar.aestronglyMeasurable.smul hD
  have hVθp : AEStronglyMeasurable Vθ
      ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hVθ
  have hDθp : AEStronglyMeasurable Dθ
      ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hDθ
  have hsθ : ∀ᵐ t ∂volume.restrict J,
      MemLp (fun x ↦ Vθ (x, t)) 2 (volume.restrict B) ∧
      MemLp (fun x ↦ Dθ (x, t)) 2 (volume.restrict B) ∧
      ∀ i : Fin 3, HasWeakGradientOn B (fun x ↦ Vθ (x, t) i) (fun x ↦ Dθ (x, t) i) := by
    filter_upwards [hslices, hVθp.prodMk_right, hDθp.prodMk_right] with t ht hvt hdt
    refine ⟨?_, ?_, ?_⟩
    · apply ht.1.of_le_enorm hvt
      exact ae_of_all _ fun x ↦ by
        simpa only [Vθ, pow_one] using cutoff_power_smul_enorm_le (V (x, t))
          (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr (hθb t).2) 1
    · apply ht.2.1.of_le_enorm hdt
      exact ae_of_all _ fun x ↦ by
        simpa only [Dθ, pow_one] using cutoff_power_smul_enorm_le (D (x, t))
          (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr (hθb t).2) 1
    intro i
    simpa only [Vθ, Dθ, Pi.smul_apply, smul_eq_mul] using
      weakGradient_const_smul (ht.2.2 i) (Real.sqrt (θ t))
  have herror : (∫⁻ z : ParabolicPoint in B ×ˢ J, ‖Vθ z‖ₑ ^ (2 : ℝ)) ≤
      ∫⁻ z : ParabolicPoint in B ×ˢ J, ‖V z‖ₑ ^ (2 : ℝ) := by
    apply lintegral_mono
    intro z
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    simpa only [Vθ, pow_one] using cutoff_power_smul_enorm_le (V z)
      (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr (hθb z.2).2) 1
  have hh := integrated_cutoff_cube_sobolev_quadratic_error hB hVθ hDθ hsθ
    hφ hc hs hunit hb hL hgrad
  dsimp only [Vθ, Dθ] at hh
  simp_rw [smul_comm (φ _ ^ (3 : ℕ)) (Real.sqrt (θ _))] at hh
  exact hh.trans (mul_le_mul' le_rfl
    (add_le_add le_rfl (mul_le_mul' le_rfl herror)))

/-- Actual suitable projected data retain the time weighted gradient and original source moment. -/
theorem fullBallProjectedVelocityAmbient_timeWeighted_sobolev_le_source
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    {B : Set Vec3} (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcompact : HasCompactSupport φ)
    (hs : tsupport φ ⊆ B) (hunit : tsupport φ ⊆ euclideanBall 0 1)
    (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1)
    {L : ℝ} (hL : 1 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L) :
    (∫⁻ t in Ioo a b, eLpNorm
      (fun x ↦ Real.sqrt (θ t) •
        (φ x ^ 3 • fullBallProjectedVelocityAmbient u D p a b c (x, t))) 6
        (volume.restrict B) ^ (2 : ℝ)) ≤ 2 * (3 * localSobolevConstant) ^ 2 *
          ((∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
              ‖Real.sqrt (θ z.2) •
                (φ z.1 ^ 3 • fullBallProjectedVelocityDerivativeAmbient u D p a b c z)‖ₑ ^
                  (2 : ℝ)) +
            1225 * ENNReal.ofReal L ^ 2 * fullBallProjectedVelocitySquareCoefficient ρ *
              ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
                (volume.restrict (vec3Ball 0 1)) ^ 2) := by
  obtain ⟨hV, hD⟩ :=
    fullBallProjectedVelocityAmbient_joint_memLp_two hsol hbox hab hc hρ hρone hBK
  have hslices := fullBallProjectedVelocityAmbient_weak_gradient_slices_ae
    u D p a b c hsol hbox hρ hρone hB hBK
  have hh := integrated_timeWeighted_cutoff_cube_sobolev_quadratic_error hB
    hV.aestronglyMeasurable hD.aestronglyMeasurable hslices
    hφ hcompact hs hunit hb hθ hθb hL hgrad
  have hsource := fullBallProjectedVelocityAmbient_joint_square_le_six_moment
    hsol hbox hab hc hρ hρone hB hBK
  apply hh.trans
  apply mul_le_mul' le_rfl
  apply add_le_add le_rfl
  calc
    _ ≤ (1225 * ENNReal.ofReal L ^ 2) *
        (fullBallProjectedVelocitySquareCoefficient ρ *
          ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
            (volume.restrict (vec3Ball 0 1)) ^ 2) :=
      mul_le_mul' (le_refl (1225 * ENNReal.ofReal L ^ 2)) hsource
    _ = _ := by ring

end FluidSingularSets
