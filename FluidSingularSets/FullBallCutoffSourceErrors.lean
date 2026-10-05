-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallVelocityMomentFinite

/-!
# Actual quadratic source errors for projected cutoff energy

The genuine corrected velocity has integrable Euclidean square, bounded by the
original endpoint mixed moment. The quantitative time error uses only an upper
bound on the time derivative. A separate compact-support derivative bound proves
integrability, so a large negative future derivative does not enter its cost.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- The true Euclidean square estimate applies to arbitrary measurable source domains. -/
theorem lintegral_vec3Euclidean_square_le_nine
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {v : X → Vec3}
    (hv : AEStronglyMeasurable v μ) :
    (∫⁻ x, ENNReal.ofReal (vec3EuclideanNorm (v x) ^ 2) ∂μ) ≤
      9 * ∫⁻ x, ‖v x‖ₑ ^ (2 : ℝ) ∂μ := by
  have he := CKN.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hv
  have hE := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) he
  have hN := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hv
  norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat] at hE hN
  have h := ENNReal.rpow_le_rpow (eLpNorm_vec3EuclideanNorm_le_three hv 2)
    (by norm_num : (0 : ℝ) ≤ 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hE, hN,
    show (3 : ℝ≥0∞) ^ (2 : ℝ) = 9 by norm_num] at h
  simpa only [← ofReal_norm, Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _),
    ENNReal.rpow_ofNat, ← ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _)] using h

section LocalBox

variable {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {B : Set Vec3}

/-- Actual suitable data give the genuine corrected Euclidean square integrability. -/
theorem fullBallProjectedVelocityAmbient_euclidean_square_integrable
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hBK : B ⊆ fullBallCompactInterior ρ) :
    Integrable (fun z : ParabolicPoint ↦
      vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z) ^ 2)
        (volume.restrict (B ×ˢ Ioo a b)) := by
  have hv := (fullBallProjectedVelocityAmbient_joint_memLp_two
    hsol hbox hab hc hρ hρone hBK).1
  have he : MemLp (fun z ↦
      vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z)) 2
        (volume.restrict (B ×ˢ Ioo a b)) :=
    (eLpNorm_vec3EuclideanNorm_le_three hv.aestronglyMeasurable 2).trans_lt
      (ENNReal.mul_lt_top (by norm_num) hv)
  exact (he.integrable_mul he).congr
    (ae_of_all _ fun z ↦ by simp only [Pi.mul_apply, pow_two])

/-- The actual projected Euclidean joint square has its true endpoint source bound. -/
theorem fullBallProjectedVelocityAmbient_euclidean_square_lintegral_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ) :
    (∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b, ENNReal.ofReal
      (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z) ^ 2)) ≤
      9 * fullBallProjectedVelocitySquareCoefficient ρ *
        ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2 := by
  have hv := (fullBallProjectedVelocityAmbient_joint_memLp_two
    hsol hbox hab hc hρ hρone hBK).1
  exact (lintegral_vec3Euclidean_square_le_nine hv.aestronglyMeasurable).trans
    ((mul_le_mul' le_rfl (fullBallProjectedVelocityAmbient_joint_square_le_six_moment
      hsol hbox hab hc hρ hρone hB hBK)).trans_eq (mul_assoc _ _ _).symm)

/-- Genuine endpoint moment finiteness converts the actual Euclidean source bound to reals. -/
theorem fullBallProjectedVelocityAmbient_euclidean_square_integral_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ) :
    (∫ z : ParabolicPoint in B ×ˢ Ioo a b,
      vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z) ^ 2) ≤
      9 * (fullBallProjectedVelocitySquareCoefficient ρ).toReal *
        (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2).toReal := by
  have hu : (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
      (volume.restrict (vec3Ball 0 1)) ^ 2) < ⊤ := by
    simpa only [ENNReal.rpow_ofNat] using suitable_fullBall_velocity_six_moment_lt_top hsol hbox
  have he := fullBallProjectedVelocityAmbient_euclidean_square_integrable
    hsol hbox hab hc hρ hρone hBK
  have hb := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
      (fullBallProjectedVelocitySquareCoefficient_ne_top ρ)) hu.ne)
    (fullBallProjectedVelocityAmbient_euclidean_square_lintegral_bound
      hsol hbox hab hc hρ hρone hB hBK)
  rw [← integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun z ↦ sq_nonneg _) he.aestronglyMeasurable,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hb
  exact hb

/-- The true time-source integral uses the derivative upper bound, independently of its
absolute compact-support bound used only to establish integrability. -/
theorem suitable_fullBall_time_cutoff_source_integrable_and_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hcθ : HasCompactSupport θ)
    {T : ℝ} (hT : 0 ≤ T) (hdθ : ∀ t, deriv θ t ≤ T)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) :
    Integrable (fun z : ParabolicPoint ↦
      vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z) ^ 2 *
        φ z.1 ^ 6 * deriv θ z.2 * χ z.2) (volume.restrict (B ×ˢ Ioo a b)) ∧
    (∫ z : ParabolicPoint in B ×ˢ Ioo a b,
      vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z) ^ 2 *
        φ z.1 ^ 6 * deriv θ z.2 * χ z.2) ≤
      9 * T * (fullBallProjectedVelocitySquareCoefficient ρ).toReal *
        (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2).toReal := by
  let E : ParabolicPoint → ℝ := fun z ↦
    vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z) ^ 2
  have he := fullBallProjectedVelocityAmbient_euclidean_square_integrable
    hsol hbox hab hc hρ hρone hBK
  have hp (x : Vec3) : ‖φ x ^ 6‖ ≤ 1 := by
    rw [norm_pow, Real.norm_of_nonneg (hb x).1]
    exact pow_le_one₀ (hb x).1 (hb x).2
  have hχn (t : ℝ) : ‖χ t‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hbχ t).1]
    exact (hbχ t).2
  have hdc : Continuous (deriv θ) := hθ.continuous_deriv (by simp)
  obtain ⟨K, hK⟩ := hcθ.deriv.exists_bound_of_continuous hdc
  have hi := ((he.mul_bdd ((hφ.pow 6).continuous.comp
    continuous_fst_parabolicPoint).aestronglyMeasurable
      (ae_of_all _ fun z ↦ hp z.1)).mul_bdd
        (hdc.comp continuous_snd_parabolicPoint).aestronglyMeasurable
          (ae_of_all _ fun z ↦ hK z.2)).mul_bdd
            (hχ.comp continuous_snd_parabolicPoint).aestronglyMeasurable
              (ae_of_all _ fun z ↦ hχn z.2)
  refine ⟨hi, ?_⟩
  have hpoint (z : ParabolicPoint) : E z * φ z.1 ^ 6 * deriv θ z.2 * χ z.2 ≤ T * E z := by
    have hs : 0 ≤ φ z.1 ^ 6 * χ z.2 := mul_nonneg (pow_nonneg (hb z.1).1 6) (hbχ z.2).1
    have hsone : φ z.1 ^ 6 * χ z.2 ≤ 1 :=
      (mul_le_mul (pow_le_one₀ (hb z.1).1 (hb z.1).2) (hbχ z.2).2
        (hbχ z.2).1 (by norm_num)).trans_eq (one_mul 1)
    have hen : 0 ≤ E z := sq_nonneg _
    calc
      _ = (φ z.1 ^ 6 * χ z.2) * (deriv θ z.2 * E z) := by ring
      _ ≤ (φ z.1 ^ 6 * χ z.2) * (T * E z) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hdθ z.2) hen) hs
      _ ≤ 1 * (T * E z) := mul_le_mul_of_nonneg_right hsone (mul_nonneg hT hen)
      _ = _ := one_mul _
  calc
    _ ≤ ∫ z : ParabolicPoint in B ×ˢ Ioo a b, T * E z :=
      integral_mono_ae hi (he.const_mul T) (ae_of_all _ hpoint)
    _ = T * ∫ z : ParabolicPoint in B ×ˢ Ioo a b, E z := integral_const_mul _ _
    _ ≤ T * (9 * (fullBallProjectedVelocitySquareCoefficient ρ).toReal *
        (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2).toReal) :=
      mul_le_mul_of_nonneg_left (fullBallProjectedVelocityAmbient_euclidean_square_integral_bound
        hsol hbox hab hc hρ hρone hB hBK) hT
    _ = _ := by ring

/-- Actual spatial cutoff errors are integrable and have the true quadratic source cost.
A global Laplacian bound already ensures the bounded multiplier required for integrability. -/
theorem suitable_fullBall_laplacian_cutoff_source_integrable_and_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hlap : ∀ x, ‖spatialLaplacian (fun y ↦ φ y ^ 6) x‖ ≤ Λ)
    {η : ℝ → ℝ} (hη : Continuous η) (hbη : ∀ t, ‖η t‖ ≤ 1) :
    Integrable (fun z : ParabolicPoint ↦
      vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z) ^ 2 *
        spatialLaplacian (fun y ↦ φ y ^ 6) z.1 * η z.2)
      (volume.restrict (B ×ˢ Ioo a b)) ∧
    ‖∫ z : ParabolicPoint in B ×ˢ Ioo a b,
      vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z) ^ 2 *
        spatialLaplacian (fun y ↦ φ y ^ 6) z.1 * η z.2‖ ≤
      9 * Λ * (fullBallProjectedVelocitySquareCoefficient ρ).toReal *
        (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2).toReal := by
  let E : ParabolicPoint → ℝ := fun z ↦
    vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z) ^ 2
  have he := fullBallProjectedVelocityAmbient_euclidean_square_integrable
    hsol hbox hab hc hρ hρone hBK
  have hΔ := (contDiff_spatialLaplacian_smooth (hφ.pow 6)).continuous
  have hi := (he.mul_bdd (hΔ.comp continuous_fst_parabolicPoint).aestronglyMeasurable
    (ae_of_all _ fun z ↦ hlap z.1)).mul_bdd
      (hη.comp continuous_snd_parabolicPoint).aestronglyMeasurable
        (ae_of_all _ fun z ↦ hbη z.2)
  refine ⟨hi, ?_⟩
  have hpoint (z : ParabolicPoint) :
      ‖E z * spatialLaplacian (fun y ↦ φ y ^ 6) z.1 * η z.2‖ ≤ Λ * E z := by
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ E z * Λ * 1 := by gcongr; exact hlap z.1; exact hbη z.2
      _ = _ := by ring
  calc
    _ ≤ ∫ z : ParabolicPoint in B ×ˢ Ioo a b,
        ‖E z * spatialLaplacian (fun y ↦ φ y ^ 6) z.1 * η z.2‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z : ParabolicPoint in B ×ˢ Ioo a b, Λ * E z :=
      integral_mono_ae hi.norm (he.const_mul Λ) (ae_of_all _ hpoint)
    _ = Λ * ∫ z : ParabolicPoint in B ×ˢ Ioo a b, E z := integral_const_mul _ _
    _ ≤ Λ * (9 * (fullBallProjectedVelocitySquareCoefficient ρ).toReal *
        (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2).toReal) :=
      mul_le_mul_of_nonneg_left (fullBallProjectedVelocityAmbient_euclidean_square_integral_bound
        hsol hbox hab hc hρ hρone hB hBK) hΛ
    _ = _ := by ring

end LocalBox

end FluidSingularSets
