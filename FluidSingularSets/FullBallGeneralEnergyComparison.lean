-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallGeneralTestedEnergy
public import FluidSingularSets.FullBallProjectedGradientControl

/-!
# True lower-test comparisons for general projected energy

A genuine pointwise lower bound on a joint nonnegative test controls the
literal unweighted slice energy and coordinate dissipation on an inner patch.
The actual suitable energy integrability supplies the real-to-extended integral
identity, including its almost-everywhere good time slices.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A genuine lower test controls the actual inner Euclidean essential slice energy. -/
theorem suitable_fullBall_general_slice_energy_comparison
    {Ω : Set Vec3} {I J : Set ℝ} {q a b c ρ C : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {B : Set Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : MeasurableSet B)
    (hBK : B ⊆ fullBallCompactInterior ρ) (hJ : MeasurableSet J) (hJsub : J ⊆ Ioo a b)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hnψ : ∀ z, 0 ≤ ψ z) (hsupp : tsupport ψ ⊆ fullBallCompactInterior ρ ×ˢ Ioo a b)
    (hC : 0 ≤ C) (hlower : ∀ z : ParabolicPoint, z ∈ B ×ˢ J → 1 ≤ C * ψ z) :
    essSup (fun t ↦ ∫⁻ x in B, ENNReal.ofReal
      (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c (x, t)) ^ 2))
        (volume.restrict J) ≤
      ENNReal.ofReal C * fullBallGeneralProjectedEnergySup ρ u D p a b c ψ := by
  let V := fullBallProjectedVelocityAmbient u D p a b c
  let E := fullBallProjectedEnergyDensity ρ u D p a b c ψ
  let K := fullBallCompactInterior ρ
  have hE := (suitable_fullBall_projected_time_energy_integrable_localBox
    ρ hρ hρone hsol hbox hab hc hψ hnψ hsupp).1
  have hg : ∀ᵐ t ∂volume.restrict J,
      Integrable (fun x ↦ E (x, t)) (fullBallInteriorMeasure ρ) :=
    hE.prod_left_ae.filter_mono (ae_mono (Measure.restrict_mono hJsub le_rfl))
  have hs : ∀ᵐ t ∂volume.restrict J,
      ENNReal.ofReal (∫ x, E (x, t) ∂fullBallInteriorMeasure ρ) ≤
        fullBallGeneralProjectedEnergySup ρ u D p a b c ψ :=
    (ENNReal.ae_le_essSup (μ := volume.restrict (Ioo a b))
      (fun t ↦ ENNReal.ofReal (∫ x, E (x, t) ∂fullBallInteriorMeasure ρ))).filter_mono
        (ae_mono (Measure.restrict_mono hJsub le_rfl))
  refine essSup_le_of_ae_le _ ?_
  filter_upwards [hg, hs, ae_restrict_mem hJ] with t ht hsup htJ
  let F : Vec3 → ℝ≥0∞ := fun x ↦ ENNReal.ofReal
    (vec3EuclideanNorm (V (x, t)) ^ 2 * ψ (x, t))
  have hcompact : (∫⁻ x : fullBallCompactInterior ρ, F x.1 ∂fullBallInteriorMeasure ρ) =
      ∫⁻ x in K, F x :=
    (fullBallInterior_measurePreserving ρ).lintegral_comp_emb
      (MeasurableEmbedding.subtype_coe isClosed_closure.measurableSet) F
  have heq : (∫⁻ x in K, F x) =
      ENNReal.ofReal (∫ x, E (x, t) ∂fullBallInteriorMeasure ρ) := by
    rw [← hcompact]
    exact (ofReal_integral_eq_lintegral_ofReal ht (ae_of_all _ fun x ↦
      fullBallProjectedEnergyDensity_nonneg ρ u D p a b c hnψ (x, t))).symm
  calc
    _ ≤ ∫⁻ x in B, ENNReal.ofReal C * F x := by
      apply setLIntegral_mono' hB
      intro x hx
      have h := mul_le_mul_of_nonneg_left (hlower (x, t) ⟨hx, htJ⟩)
        (sq_nonneg (vec3EuclideanNorm (V (x, t))))
      change ENNReal.ofReal (vec3EuclideanNorm (V (x, t)) ^ 2) ≤
        ENNReal.ofReal C * ENNReal.ofReal (vec3EuclideanNorm (V (x, t)) ^ 2 * ψ (x, t))
      rw [← ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      nlinarith only [h]
    _ = ENNReal.ofReal C * ∫⁻ x in B, F x :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * ∫⁻ x in K, F x :=
      mul_le_mul' le_rfl (lintegral_mono_set hBK)
    _ ≤ _ := mul_le_mul' le_rfl (heq ▸ hsup)

/-- A genuine lower test controls the actual inner coordinate dissipation. -/
theorem fullBall_general_dissipation_comparison
    (ρ : ℝ) (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) {B : Set Vec3} {J : Set ℝ}
    (hB : MeasurableSet B) (hBK : B ⊆ fullBallCompactInterior ρ) (hJ : MeasurableSet J)
    (hJsub : J ⊆ Ioo a b) {ψ : Vec3 × ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hlower : ∀ z : ParabolicPoint, z ∈ B ×ˢ J → 1 ≤ C * ψ z) :
    (∫⁻ z : ParabolicPoint in B ×ˢ J, ENNReal.ofReal (projectedGradientSquare
      (fullBallProjectedVelocityDerivativeAmbient u D p a b c z))) ≤
        ENNReal.ofReal C * fullBallGeneralProjectedDissipation ρ u D p a b c ψ := by
  let K := fullBallCompactInterior ρ
  let F : ParabolicPoint → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (projectedGradientSquare
    (fullBallProjectedVelocityDerivativeAmbient u D p a b c z) * ψ z)
  have he : MeasurableEmbedding
      (fun z : fullBallCompactInterior ρ × ℝ ↦ (z.1.1, z.2)) :=
    (MeasurableEmbedding.subtype_coe isClosed_closure.measurableSet).prodMap
      (MeasurableEmbedding.id : MeasurableEmbedding (id : ℝ → ℝ))
  have hchange := (fullBallInterior_product_measurePreserving ρ (Ioo a b)).lintegral_comp_emb
    he F
  rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod] at hchange
  calc
    _ ≤ ∫⁻ z : ParabolicPoint in B ×ˢ J, ENNReal.ofReal C * F z := by
      apply setLIntegral_mono' (hB.prod hJ)
      intro z hz
      have h := mul_le_mul_of_nonneg_left (hlower z hz)
        (projectedGradientSquare_nonneg
          (fullBallProjectedVelocityDerivativeAmbient u D p a b c z))
      change ENNReal.ofReal (projectedGradientSquare
        (fullBallProjectedVelocityDerivativeAmbient u D p a b c z)) ≤
        ENNReal.ofReal C * ENNReal.ofReal (projectedGradientSquare
          (fullBallProjectedVelocityDerivativeAmbient u D p a b c z) * ψ z)
      rw [← ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      nlinarith only [h]
    _ = ENNReal.ofReal C * ∫⁻ z : ParabolicPoint in B ×ˢ J, F z :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * ∫⁻ z : ParabolicPoint in K ×ˢ Ioo a b, F z :=
      mul_le_mul' le_rfl (lintegral_mono_set (Set.prod_mono hBK hJsub))
    _ = _ := congrArg (fun y : ℝ≥0∞ ↦ ENNReal.ofReal C * y) hchange.symm

end FluidSingularSets
