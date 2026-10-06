-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallDissipationTransport

/-!
# Actual projected energy on a genuine cutoff plateau

Literal unweighted projected slice energy and coordinate dissipation on an
inner cylinder are bounded by the actual weighted test energy when the cutoff
is one there. This is a geometric comparison and does not assume an energy
inequality or regularity criterion.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The literal Euclidean energy carries exactly the cutoff weight. -/
theorem fullBallTimeWeightedProjectedVelocity_square_weight
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (φ : Vec3 → ℝ) {θ : ℝ → ℝ}
    (hθ : ∀ t, 0 ≤ θ t) (z : ParabolicPoint) :
    vec3EuclideanNorm (fullBallTimeWeightedProjectedVelocity u D p a b c φ θ z) ^ 2 =
      φ z.1 ^ 6 * θ z.2 *
        vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z) ^ 2 := by
  simp only [fullBallTimeWeightedProjectedVelocity, fullBallProjectedCutoffVelocity,
    vec3EuclideanNorm_smul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (hθ z.2), sq_abs, ← pow_mul]
  ring

/-- Genuine plateau geometry compares actual inner Euclidean slice energy with the test bound. -/
theorem fullBall_projected_sliceEnergy_le_tested_plateau
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c a₀ b₀ : ℝ) {B : Set Vec3} {r : ℝ}
    {φ : Vec3 → ℝ} {θ : ℝ → ℝ} (hθ : ∀ t, 0 ≤ θ t)
    (hball : vec3Ball 0 r ⊆ B) (htime : Ioo a₀ b₀ ⊆ Ioo a b)
    (hplateau : ∀ z : ParabolicPoint, z ∈ vec3Ball 0 r ×ˢ Ioo a₀ b₀ →
      φ z.1 ^ 6 * θ z.2 = 1) :
    essSup (fun t ↦ ∫⁻ x in vec3Ball 0 r, ENNReal.ofReal
      (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c (x, t)) ^ 2))
        (volume.restrict (Ioo a₀ b₀)) ≤
      fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ := by
  let E : ℝ → ℝ≥0∞ := fun t ↦ ∫⁻ x in B, ‖vec3EuclideanNorm
    (fullBallTimeWeightedProjectedVelocity u D p a b c φ θ (x, t))‖ₑ ^ (2 : ℝ)
  have hae : ∀ᵐ t : ℝ ∂volume, t ∈ Ioo a b → E t ≤ essSup E (volume.restrict (Ioo a b)) :=
    (ae_restrict_iff' measurableSet_Ioo).mp (ENNReal.ae_le_essSup E)
  refine essSup_le_of_ae_le _ ?_
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hae] with t ht htinner
  have hpoint (x : Vec3) (hx : x ∈ vec3Ball 0 r) :
      ENNReal.ofReal
        (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c (x, t)) ^ 2) =
      ‖vec3EuclideanNorm
        (fullBallTimeWeightedProjectedVelocity u D p a b c φ θ (x, t))‖ₑ ^ (2 : ℝ) := by
    simp only [← ofReal_norm, Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _),
      ENNReal.rpow_ofNat, ← ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _)]
    rw [fullBallTimeWeightedProjectedVelocity_square_weight u D p a b c φ hθ (x, t),
      hplateau (x, t) ⟨hx, htinner⟩, one_mul]
  calc
    _ = ∫⁻ x in vec3Ball 0 r, ‖vec3EuclideanNorm
        (fullBallTimeWeightedProjectedVelocity u D p a b c φ θ (x, t))‖ₑ ^ (2 : ℝ) :=
      setLIntegral_congr_fun (vec3Ball_measurable 0 r) hpoint
    _ ≤ E t := lintegral_mono_set hball
    _ ≤ _ := ht (htime htinner)

/-- Genuine plateau geometry compares actual coordinate dissipation with the test density. -/
theorem fullBall_projected_dissipation_le_tested_plateau
    (ρ : ℝ) (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c a₀ b₀ : ℝ) {B : Set Vec3} {r : ℝ}
    {φ : Vec3 → ℝ} {θ : ℝ → ℝ} (hB : MeasurableSet B) (hs : tsupport φ ⊆ B)
    (hBK : B ⊆ fullBallCompactInterior ρ) (hθ : ∀ t, 0 ≤ θ t)
    (hball : vec3Ball 0 r ⊆ B) (htime : Ioo a₀ b₀ ⊆ Ioo a b)
    (hplateau : ∀ z : ParabolicPoint, z ∈ vec3Ball 0 r ×ˢ Ioo a₀ b₀ →
      φ z.1 ^ 6 * θ z.2 = 1) :
    (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo a₀ b₀, ENNReal.ofReal
      (projectedGradientSquare (fullBallProjectedVelocityDerivativeAmbient u D p a b c z))) ≤
      fullBallTimeWeightedProjectedDissipation ρ u D p a b c φ θ := by
  rw [fullBallTimeWeightedProjectedDissipation_eq_native ρ u D p a b c hB hs hBK hθ]
  calc
    _ = ∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo a₀ b₀,
        ENNReal.ofReal (projectedGradientSquare
          (fullBallProjectedVelocityDerivativeAmbient u D p a b c z)) *
            ENNReal.ofReal (φ z.1 ^ 6) * ENNReal.ofReal (θ z.2) := by
      have hp (z : ParabolicPoint) (hz : z ∈ vec3Ball 0 r ×ˢ Ioo a₀ b₀) :
          ENNReal.ofReal (projectedGradientSquare
            (fullBallProjectedVelocityDerivativeAmbient u D p a b c z)) =
          ENNReal.ofReal (projectedGradientSquare
            (fullBallProjectedVelocityDerivativeAmbient u D p a b c z)) *
              ENNReal.ofReal (φ z.1 ^ 6) * ENNReal.ofReal (θ z.2) := by
        rw [mul_assoc, ← ENNReal.ofReal_mul (by positivity), hplateau z hz,
          ENNReal.ofReal_one, mul_one]
      exact setLIntegral_congr_fun ((vec3Ball_measurable 0 r).prod measurableSet_Ioo) hp
    _ ≤ _ := lintegral_mono_set (Set.prod_mono hball htime)

end FluidSingularSets
