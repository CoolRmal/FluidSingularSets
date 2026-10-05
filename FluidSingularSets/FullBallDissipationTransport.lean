-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallTestedEnergyBounds
public import FluidSingularSets.FullBallTimeWeightedGradientControl

/-!
# Genuine transport of the tested corrected dissipation

The actual compact-subtype dissipation is exactly its native spacetime density
on every containing spatial patch. It controls the true square-root time
weighted corrected-gradient norm, with no extra energy hypothesis.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Actual compact-subtype integration transports exactly to the containing native patch. -/
theorem fullBallTimeWeightedProjectedDissipation_eq_native
    (ρ : ℝ) (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) {B : Set Vec3} (hB : MeasurableSet B)
    {φ : Vec3 → ℝ} {θ : ℝ → ℝ} (hs : tsupport φ ⊆ B)
    (hBK : B ⊆ fullBallCompactInterior ρ) (hθ : ∀ t, 0 ≤ θ t) :
    fullBallTimeWeightedProjectedDissipation ρ u D p a b c φ θ =
      ∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
        ENNReal.ofReal (projectedGradientSquare
          (fullBallProjectedVelocityDerivativeAmbient u D p a b c z)) *
            ENNReal.ofReal (φ z.1 ^ 6) * ENNReal.ofReal (θ z.2) := by
  let J := Ioo a b
  let K := fullBallCompactInterior ρ
  let F : ParabolicPoint → ℝ≥0∞ := fun z ↦ ENNReal.ofReal
    (projectedGradientSquare (fullBallProjectedVelocityDerivativeAmbient u D p a b c z)) *
      ENNReal.ofReal (φ z.1 ^ 6) * ENNReal.ofReal (θ z.2)
  have hK : MeasurableSet K := isClosed_closure.measurableSet
  have he : MeasurableEmbedding
      (fun z : fullBallCompactInterior ρ × ℝ ↦ (z.1.1, z.2)) :=
    (MeasurableEmbedding.subtype_coe hK).prodMap
      (MeasurableEmbedding.id : MeasurableEmbedding (id : ℝ → ℝ))
  have hchange := (fullBallInterior_product_measurePreserving ρ J).lintegral_comp_emb he F
  rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod] at hchange
  have hz (z : ParabolicPoint) (hzB : z.1 ∉ B) : F z = 0 := by
    have hzφ : φ z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hzB (hs h))
    simp only [F, hzφ, zero_pow (by norm_num : (6 : ℕ) ≠ 0), ENNReal.ofReal_zero,
      mul_zero, zero_mul]
  calc
    _ = ∫⁻ z : fullBallCompactInterior ρ × ℝ, F (z.1.1, z.2)
        ∂(fullBallInteriorMeasure ρ).prod (volume.restrict J) := by
      apply lintegral_congr
      intro z
      dsimp only [F, fullBallProjectedVelocityDerivativeAmbient]
      rw [ENNReal.ofReal_mul (projectedGradientSquare_nonneg _),
        ENNReal.ofReal_mul' (hθ z.2)]
      ring
    _ = ∫⁻ z : ParabolicPoint in K ×ˢ J, F z := hchange
    _ = ∫⁻ z : ParabolicPoint in B ×ˢ J, F z := by
      have hKJ : MeasurableSet (K ×ˢ J : Set ParabolicPoint) := hK.prod measurableSet_Ioo
      have hBJ : MeasurableSet (B ×ˢ J : Set ParabolicPoint) := hB.prod measurableSet_Ioo
      calc
        _ = ∫⁻ z : ParabolicPoint, (K ×ˢ J).indicator F z :=
          (lintegral_indicator (α := ParabolicPoint) hKJ F).symm
        _ = ∫⁻ z : ParabolicPoint, (B ×ˢ J).indicator F z := by
          apply lintegral_congr
          intro z
          by_cases hzB : z.1 ∈ B
          · have hzK : z.1 ∈ K := hBK hzB
            by_cases hzJ : z.2 ∈ J <;> simp [hzB, hzK, hzJ]
          · have hzF : F z = 0 := hz z hzB
            by_cases hzK : z.1 ∈ K <;> by_cases hzJ : z.2 ∈ J <;>
              simp [hzB, hzK, hzJ, hzF]
        _ = _ := lintegral_indicator (α := ParabolicPoint) hBJ F

/-- The true weighted corrected matrix norm is controlled by the actual tested dissipation. -/
theorem fullBallTimeWeightedProjectedGradient_square_le_dissipation
    (ρ : ℝ) (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) {B : Set Vec3} (hB : MeasurableSet B)
    {φ : Vec3 → ℝ} {θ : ℝ → ℝ} (hs : tsupport φ ⊆ B)
    (hBK : B ⊆ fullBallCompactInterior ρ) (hθ : ∀ t, 0 ≤ θ t) :
    (∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
      ‖Real.sqrt (θ z.2) •
        (φ z.1 ^ 3 • fullBallProjectedVelocityDerivativeAmbient u D p a b c z)‖ₑ ^
          (2 : ℝ)) ≤ fullBallTimeWeightedProjectedDissipation ρ u D p a b c φ θ := by
  rw [fullBallTimeWeightedProjectedDissipation_eq_native ρ u D p a b c hB hs hBK hθ]
  apply lintegral_mono
  intro z
  simpa only [smul_smul] using time_weighted_gradient_enorm_sq_le_density
    (fullBallProjectedVelocityDerivativeAmbient u D p a b c z) (φ z.1) (hθ z.2)

end FluidSingularSets
