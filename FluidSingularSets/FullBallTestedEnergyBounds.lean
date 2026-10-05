-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallTimeWeightedEnergy
public import FluidSingularSets.TestedTimeEnergyBounds

/-!
# Actual weighted energy bounds from tested right hand sides

The literal tested right hand side controls the actual time-weighted Euclidean
energy and the whole corrected coordinate dissipation. Decreasing the time
weight genuinely decreases its energy supremum.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- The genuine square-root time weight has exactly its literal energy factor. -/
theorem fullBallTimeWeightedProjectedVelocity_square_eq
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (φ : Vec3 → ℝ) {θ : ℝ → ℝ}
    (hθ : ∀ t, 0 ≤ θ t) (z : ParabolicPoint) :
    vec3EuclideanNorm (fullBallTimeWeightedProjectedVelocity u D p a b c φ θ z) ^ 2 =
      θ z.2 * vec3EuclideanNorm (fullBallProjectedCutoffVelocity u D p a b c φ z) ^ 2 := by
  simp only [fullBallTimeWeightedProjectedVelocity, vec3EuclideanNorm_smul,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hθ z.2)]

/-- Actual smaller nonnegative time weights have smaller literal Euclidean energy. -/
theorem fullBallTimeWeightedProjectedEnergySup_mono
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (B : Set Vec3) (φ : Vec3 → ℝ)
    {η θ : ℝ → ℝ} (hη : ∀ t, 0 ≤ η t) (hηθ : ∀ t, η t ≤ θ t) :
    fullBallTimeWeightedProjectedEnergySup u D p a b c B φ η ≤
      fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ := by
  refine essSup_mono_ae ?_
  filter_upwards [] with t
  apply lintegral_mono
  intro x
  have hsq := mul_le_mul_of_nonneg_right (hηθ t)
    (sq_nonneg (vec3EuclideanNorm (fullBallProjectedCutoffVelocity u D p a b c φ (x, t))))
  rw [← fullBallTimeWeightedProjectedVelocity_square_eq u D p a b c φ hη (x, t),
    ← fullBallTimeWeightedProjectedVelocity_square_eq u D p a b c φ
      (fun t ↦ (hη t).trans (hηθ t)) (x, t)] at hsq
  simpa only [← ofReal_norm,
    Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _), ENNReal.rpow_ofNat,
    ← ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _)] using ENNReal.ofReal_le_ofReal hsq

/-- Every true backward-ramp truncation decreases the tested energy supremum. -/
theorem fullBallTimeWeightedProjectedEnergySup_mul_backwardTimeCutoff_le
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (B : Set Vec3) (φ : Vec3 → ℝ)
    {θ : ℝ → ℝ} (hθ : ∀ s, 0 ≤ θ s) (t h : ℝ) :
    fullBallTimeWeightedProjectedEnergySup u D p a b c B φ
      (fun s ↦ θ s * backwardTimeCutoff t h s) ≤
        fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ :=
  fullBallTimeWeightedProjectedEnergySup_mono u D p a b c B φ
    (fun s ↦ mul_nonneg (hθ s) backwardTimeCutoff_nonneg)
    (fun s ↦ mul_le_of_le_one_right (hθ s) backwardTimeCutoff_le_one)

/-- The actual coordinate dissipation of the corrected time-weighted velocity. -/
def fullBallTimeWeightedProjectedDissipation
    (ρ : ℝ) (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (φ : Vec3 → ℝ) (θ : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z : fullBallCompactInterior ρ × ℝ,
    ENNReal.ofReal (projectedGradientSquare
      (D (z.1.1, z.2) +
        fullBallProjectedHarmonicDerivativeAmbient u D p a b c (z.1.1, z.2)) *
          (φ z.1.1 ^ 6 * θ z.2))
      ∂(fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))

section LocalBox

variable {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {B : Set Vec3} {φ : Vec3 → ℝ} {θ : ℝ → ℝ}

/-- A genuine uniform tested right hand side bounds both actual weighted energies.
The right hand side hypothesis is the literal signed density, before any estimates. -/
theorem suitable_fullBall_tested_energy_dissipation_bound_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hs : tsupport φ ⊆ B) (hθ : ∀ t, 0 ≤ θ t)
    (hψ : (fun z : Vec3 × ℝ ↦ φ z.1 ^ 6 * θ z.2) ∈
      spaceTimeTestFunction (V := ℝ) Ω I)
    (hsupp : tsupport (fun z : Vec3 × ℝ ↦ φ z.1 ^ 6 * θ z.2) ⊆
      fullBallCompactInterior ρ ×ˢ Ioo a b)
    {A : ℝ} (hRcut : ∀ t h : ℝ, 0 < h →
      (∫ z, fullBallProjectedRhsDensity ρ u D p a b c
        (fun z ↦ φ z.1 ^ 6 * θ z.2) z * backwardTimeCutoff t h z.2
          ∂(fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))) ≤ A) :
    fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ ≤ ENNReal.ofReal A ∧
      fullBallTimeWeightedProjectedDissipation ρ u D p a b c φ θ ≤
        ENNReal.ofReal (A / 2) := by
  let ψ : Vec3 × ℝ → ℝ := fun z ↦ φ z.1 ^ 6 * θ z.2
  let μ := fullBallInteriorMeasure ρ
  let ν := volume.restrict (Ioo a b)
  have hnψ : ∀ z, 0 ≤ ψ z := fun z ↦ mul_nonneg (pow_nonneg (hb z.1).1 6) (hθ z.2)
  obtain ⟨hE, hDD, hR⟩ := suitable_fullBall_projected_time_energy_integrable_localBox
    ρ hρ hρone hsol hbox hab hc hψ hnψ hsupp
  obtain ⟨hME, hDE⟩ := tested_backwardTimeCutoff_product_energy_dissipation_bound
    measurableSet_Ioo hE hDD hR
    (fullBallProjectedEnergyDensity_nonneg ρ u D p a b c hnψ)
    (fullBallProjectedDissipationDensity_nonneg ρ u D p a b c hnψ)
    (suitable_fullBall_projected_backward_cutoff_energy_localBox
      ρ hρ hρone hsol hbox hab hc hψ hnψ hsupp) hRcut
  refine ⟨?_, ?_⟩
  · rw [fullBallTimeWeightedProjectedEnergySup_eq_tested_energy
      hsol hbox hρ hρone hB hBK hφ hb hs hθ]
    rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo,
      eLpNorm_exponent_top hE.integral_prod_right.aestronglyMeasurable,
      eLpNormEssSup_eq_essSup_enorm] at hME
    have hnorm (t : ℝ) :
        ‖∫ x, fullBallProjectedEnergyDensity ρ u D p a b c ψ (x, t) ∂μ‖ =
          ∫ x, fullBallProjectedEnergyDensity ρ u D p a b c ψ (x, t) ∂μ :=
      Real.norm_of_nonneg (integral_nonneg (fun x ↦
        fullBallProjectedEnergyDensity_nonneg ρ u D p a b c hnψ (x, t)))
    change essSup (fun t ↦ ENNReal.ofReal
      (∫ x, fullBallProjectedEnergyDensity ρ u D p a b c ψ (x, t) ∂μ)) ν ≤
        ENNReal.ofReal A
    calc
      _ = essSup (fun t ↦ ‖∫ x,
          fullBallProjectedEnergyDensity ρ u D p a b c ψ (x, t) ∂μ‖ₑ) ν := by
        apply essSup_congr_ae
        exact ae_of_all _ fun t ↦ by
          dsimp only
          rw [← ofReal_norm, hnorm t]
      _ ≤ ENNReal.ofReal A := hME
  · let d : fullBallCompactInterior ρ × ℝ → ℝ := fun z ↦ projectedGradientSquare
      (D (z.1.1, z.2) +
        fullBallProjectedHarmonicDerivativeAmbient u D p a b c (z.1.1, z.2)) * ψ (z.1.1, z.2)
    have heq : fullBallProjectedDissipationDensity ρ u D p a b c ψ =
        fun z ↦ 2 * d z := by
      funext z
      simp only [fullBallProjectedDissipationDensity, d]
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

end LocalBox

end FluidSingularSets
