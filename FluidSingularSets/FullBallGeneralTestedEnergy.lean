-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallProjectedTimeEnergy
public import FluidSingularSets.TestedTimeEnergyBounds

/-!
# Genuine projected time energy for arbitrary space-time tests

The literal suitable projected inequality controls both the essential energy
supremum and full dissipation for any actual compact nonnegative smooth test.
The test may depend jointly on space and time, as the backward heat kernel does.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual corrected energy essential supremum for a joint space-time test. -/
def fullBallGeneralProjectedEnergySup
    (ρ : ℝ) (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 × ℝ → ℝ) : ℝ≥0∞ :=
  essSup (fun t ↦ ENNReal.ofReal (∫ x,
    fullBallProjectedEnergyDensity ρ u D p a b c ψ (x, t)
      ∂fullBallInteriorMeasure ρ)) (volume.restrict (Ioo a b))

/-- The actual corrected coordinate dissipation for a joint nonnegative test. -/
def fullBallGeneralProjectedDissipation
    (ρ : ℝ) (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 × ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z : fullBallCompactInterior ρ × ℝ,
    ENNReal.ofReal (projectedGradientSquare
      (fullBallProjectedVelocityDerivativeAmbient u D p a b c (z.1.1, z.2)) *
        ψ (z.1.1, z.2))
      ∂(fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))

/-- A genuine suitable inequality and its literal tested RHS control both joint-test energies. -/
theorem suitable_fullBall_general_tested_energy_dissipation_bound
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hnψ : ∀ z, 0 ≤ ψ z) (hsupp : tsupport ψ ⊆ fullBallCompactInterior ρ ×ˢ Ioo a b)
    {A : ℝ} (hRcut : ∀ t h : ℝ, 0 < h →
      (∫ z, fullBallProjectedRhsDensity ρ u D p a b c ψ z * backwardTimeCutoff t h z.2
        ∂(fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))) ≤ A) :
    fullBallGeneralProjectedEnergySup ρ u D p a b c ψ ≤ ENNReal.ofReal A ∧
      fullBallGeneralProjectedDissipation ρ u D p a b c ψ ≤ ENNReal.ofReal (A / 2) := by
  let μ := fullBallInteriorMeasure ρ
  let ν := volume.restrict (Ioo a b)
  obtain ⟨hE, hDD, hR⟩ := suitable_fullBall_projected_time_energy_integrable_localBox
    ρ hρ hρone hsol hbox hab hc hψ hnψ hsupp
  obtain ⟨hME, hDE⟩ := tested_backwardTimeCutoff_product_energy_dissipation_bound
    measurableSet_Ioo hE hDD hR
    (fullBallProjectedEnergyDensity_nonneg ρ u D p a b c hnψ)
    (fullBallProjectedDissipationDensity_nonneg ρ u D p a b c hnψ)
    (suitable_fullBall_projected_backward_cutoff_energy_localBox
      ρ hρ hρone hsol hbox hab hc hψ hnψ hsupp) hRcut
  refine ⟨?_, ?_⟩
  · rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo,
      eLpNorm_exponent_top hE.integral_prod_right.aestronglyMeasurable,
      eLpNormEssSup_eq_essSup_enorm] at hME
    change essSup (fun t ↦ ENNReal.ofReal (∫ x,
      fullBallProjectedEnergyDensity ρ u D p a b c ψ (x, t) ∂μ)) ν ≤ ENNReal.ofReal A
    calc
      _ = essSup (fun t ↦ ‖∫ x,
          fullBallProjectedEnergyDensity ρ u D p a b c ψ (x, t) ∂μ‖ₑ) ν := by
        apply essSup_congr_ae
        exact ae_of_all _ fun t ↦ by
          dsimp only
          rw [← ofReal_norm, Real.norm_of_nonneg (integral_nonneg fun x ↦
            fullBallProjectedEnergyDensity_nonneg ρ u D p a b c hnψ (x, t))]
      _ ≤ _ := hME
  · let d : fullBallCompactInterior ρ × ℝ → ℝ := fun z ↦ projectedGradientSquare
      (fullBallProjectedVelocityDerivativeAmbient u D p a b c (z.1.1, z.2)) * ψ (z.1.1, z.2)
    have heq : fullBallProjectedDissipationDensity ρ u D p a b c ψ = fun z ↦ 2 * d z := by
      funext z
      simp only [fullBallProjectedDissipationDensity, d,
        fullBallProjectedVelocityDerivativeAmbient]
      ring
    have hd : Integrable d (μ.prod ν) := by
      convert hDD.const_mul (1 / 2 : ℝ) using 1
      funext z
      rw [heq]
      ring
    have hdn : ∀ z, 0 ≤ d z := fun z ↦ mul_nonneg
      (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
        (hnψ (z.1.1, z.2))
    have hdb : (∫ z, d z ∂μ.prod ν) ≤ A / 2 := by
      rw [heq, integral_const_mul] at hDE
      linarith
    change (∫⁻ z, ENNReal.ofReal (d z) ∂μ.prod ν) ≤ ENNReal.ofReal (A / 2)
    rw [← ofReal_integral_eq_lintegral_ofReal hd (ae_of_all _ hdn)]
    exact ENNReal.ofReal_le_ofReal hdb

end FluidSingularSets
