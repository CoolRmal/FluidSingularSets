-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallTestedCaccioppoli
public import FluidSingularSets.FullBallCylinderCaccioppoli

/-!
# Genuine initial tested projected energy

Actual suitable data and supported smooth cutoffs bound the true time-weighted
projected supremum and dissipation. Scalar absorption removes their occurrence
on the tested right hand side; no tested-energy conclusion is assumed.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Actual cutoffs and suitability give finite projected energy with an explicit source bound. -/
theorem suitable_fullBall_tested_projected_energy_bound
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {B : Set Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ B) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hlap : ∀ x, ‖spatialLaplacian (fun y ↦ φ y ^ 6) x‖ ≤ Λ)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hcθ : HasCompactSupport θ)
    (hbθ : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    (hdθ : ∀ t, deriv θ t ≤ T)
    (hψ : fullBallSeparatedCutoffTest φ θ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hsupp : tsupport (fullBallSeparatedCutoffTest φ θ) ⊆
      fullBallCompactInterior ρ ×ˢ Ioo a b)
    (hsuppB : tsupport (fullBallSeparatedCutoffTest φ θ) ⊆ B ×ˢ Ioo a b)
    {δ : ℝ} (hδ : 0 < δ) :
    let X := (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
      (volume.restrict (vec3Ball 0 1)) ^ 2).toReal
    let M := fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ
    let N := fullBallTimeWeightedProjectedDissipation ρ u D p a b c φ θ
    let c₀ := fullBallEndpointQuadraticCost ρ L Λ T δ
    let c₁ := fullBallEndpointConvectionCost ρ L a b
    let c₂ := fullBallEndpointPressureCost ρ L
    M < ⊤ ∧ N < ⊤ ∧ M.toReal + 2 * N.toReal ≤
      (4 * c₀ + 2 * (fullBallProjectedVelocitySliceCoefficient ρ).toReal ^ 2) * X +
        131072 * c₁ ^ 6 * X ^ 4 + 32 * c₂ ^ 2 * X ^ 2 +
          24 * δ * (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b,
            ‖D z‖ₑ ^ (2 : ℝ)).toReal := by
  let X : ℝ≥0∞ := ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
    (volume.restrict (vec3Ball 0 1)) ^ 2
  let E : ℝ≥0∞ := ∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b, ‖D z‖ₑ ^ (2 : ℝ)
  let M := fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ
  let N := fullBallTimeWeightedProjectedDissipation ρ u D p a b c φ θ
  let κ := (fullBallProjectedVelocitySliceCoefficient ρ).toReal
  let Y : ℝ := M.toReal + 2 * N.toReal + κ ^ 2 * X.toReal
  let A₀ := fullBallTestedRhsCost ρ L Λ T δ a b X E M
  let c₀ := fullBallEndpointQuadraticCost ρ L Λ T δ
  let c₁ := fullBallEndpointConvectionCost ρ L a b
  let c₂ := fullBallEndpointPressureCost ρ L
  have hX : X ≠ ⊤ := by
    simpa only [X, ENNReal.rpow_ofNat] using
      (suitable_fullBall_velocity_six_moment_lt_top hsol hbox).ne
  have hE : E ≠ ⊤ := (suitable_fullBall_gradient_energy_lt_top hsol hbox).ne
  have hM : M ≠ ⊤ := (fullBallTimeWeightedProjectedEnergySup_lt_top
    hsol hbox hab hc hρ hρone hB hBK hφ hb hbθ).ne
  have hA₀ : 0 ≤ A₀ := fullBallTestedRhsCost_nonneg X E M hL hΛ hT
  have hRcut (t h : ℝ) (_hh : 0 < h) :
      (∫ z, fullBallProjectedRhsDensity ρ u D p a b c
        (fun z ↦ φ z.1 ^ 6 * θ z.2) z * backwardTimeCutoff t h z.2
          ∂(fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))) ≤ A₀ :=
    suitable_fullBall_tested_rhs_uniform_bound
      hsol hbox hab hc hρ hρone hB hBK hφ hcφ hsφ hb hL hgrad hΛ hlap
      hθ hcθ hbθ hT hdθ hψ hsupp hsuppB hδ backwardTimeCutoff_smooth.continuous
        (fun _ ↦ ⟨backwardTimeCutoff_nonneg, backwardTimeCutoff_le_one⟩)
  obtain ⟨hME, hNE⟩ := suitable_fullBall_tested_energy_dissipation_bound_localBox
    hsol hbox hab hc hρ hρone hB hBK hφ hb hsφ (fun t ↦ (hbθ t).1) hψ hsupp hRcut
  have hMr : M.toReal ≤ A₀ := by
    simpa only [ENNReal.toReal_ofReal hA₀] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hME
  have hNr : N.toReal ≤ A₀ / 2 := by
    simpa only [ENNReal.toReal_ofReal (div_nonneg hA₀ (by norm_num : (0 : ℝ) ≤ 2))] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hNE
  have hN : N ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hNE
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have hMr0 : 0 ≤ M.toReal := ENNReal.toReal_nonneg
  have hNr0 : 0 ≤ N.toReal := ENNReal.toReal_nonneg
  have hSX0 : 0 ≤ κ ^ 2 * X.toReal := by positivity
  have hconnector : Y ≤ 2 * A₀ + κ ^ 2 * X.toReal := by
    dsimp only [Y]
    linarith
  have hMY : M.toReal ≤ Y := by dsimp only [Y]; linarith
  have hMX : M.toReal + κ ^ 2 * X.toReal ≤ Y := by dsimp only [Y]; linarith
  have hc₁ : 0 ≤ c₁ := by dsimp only [c₁, fullBallEndpointConvectionCost]; positivity
  have hc₂ : 0 ≤ c₂ := by
    have hh := fullBallProjectedHarmonicHessianVelocityConstant_nonneg hρone
    dsimp only [c₂, fullBallEndpointPressureCost]
    positivity
  have hcost : A₀ ≤ c₀ * X.toReal + c₁ * X.toReal ^ (2 / 3 : ℝ) * Y ^ (5 / 6 : ℝ) +
      c₂ * X.toReal * Y ^ (1 / 2 : ℝ) + (6 * δ) * E.toReal := by
    calc
      _ = c₀ * X.toReal + c₁ * X.toReal ^ (2 / 3 : ℝ) *
          (M.toReal + κ ^ 2 * X.toReal) ^ (5 / 6 : ℝ) +
          c₂ * X.toReal * M.toReal ^ (1 / 2 : ℝ) + (6 * δ) * E.toReal := by
        change fullBallTestedRhsCost ρ L Λ T δ a b X E M = _
        rw [fullBallTestedRhsCost_eq_explicit hρone hL hδ hX hE hM]
        dsimp only [c₀, c₁, c₂, fullBallEndpointQuadraticCost,
          fullBallEndpointConvectionCost, fullBallEndpointPressureCost, κ]
        ring
      _ ≤ _ := by gcongr
  have hbound := endpoint_squaredSource_connector_absorption hY ENNReal.toReal_nonneg
    hc₁ hc₂ hconnector hcost
  refine ⟨hM.lt_top, hN.lt_top, ?_⟩
  have hMYN : M.toReal + 2 * N.toReal ≤ Y := by
    dsimp only [Y]
    linarith
  exact hMYN.trans (hbound.trans_eq (by ring))

/-- Actual canonical tests uniformly bound the projected supremum and dissipation. -/
theorem suitable_fullBall_canonical_tested_projected_energy
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0))
    {r δ : ℝ} (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) (hδ : 0 < δ) :
    let X := (velocityCylinderSixMoment u 1).toReal
    let M := fullBallTimeWeightedProjectedEnergySup u D p (-1) 0 (-(1 / 2))
      (vec3Ball 0 (fullBallCanonicalPressureRadius r))
      (fullBallCanonicalSpatialCutoff r) (fullBallCanonicalTimeCutoff r δ)
    let N := fullBallTimeWeightedProjectedDissipation (fullBallCanonicalPressureRadius r)
      u D p (-1) 0 (-(1 / 2))
      (fullBallCanonicalSpatialCutoff r) (fullBallCanonicalTimeCutoff r δ)
    M < ⊤ ∧ N < ⊤ ∧ M.toReal + 2 * N.toReal ≤
      (3 / 4) * (coordinateCylinderMass D 1).toReal +
        fullCylinderEndpointForcingConstant / (1 - r) ^ 12 * (X + X ^ 2 + X ^ 4) := by
  obtain ⟨_hr0, _hrR, _hR0, _hRρ, hρ0, hρone, _hw⟩ := fullBallCanonical_radii hr hrone
  obtain ⟨hφ, hcφ, hbφ, _hs⟩ := fullBallCanonical_spatial_data hr hrone
  obtain ⟨hθ, hcθ, hbθ, _hts, _hdt, hdθ⟩ := fullBallCanonical_time_data hr hrone hδ
  have hh := suitable_fullBall_tested_projected_energy_bound
    hsol hbox (by norm_num : (-1 : ℝ) < 0) (c := -(1 / 2)) (by constructor <;> norm_num)
    hρ0 hρone (isOpen_vec3Ball 0 _) (fullBallCanonical_ball_subset_compact r)
    hφ hcφ (fullBallCanonical_spatial_support hr hrone) hbφ
    (L := 64 / (1 - r)) (by positivity) (fullBallCanonical_gradient_bound hr hrone)
    (Λ := 4 * canonicalBallCutoffSixthLaplacianConstant / (1 - r) ^ 2)
    (by positivity [canonicalBallCutoffSixthLaplacianConstant_nonneg])
    (fun x ↦ by simpa only [Real.norm_eq_abs] using fullBallCanonical_laplacian_bound hr hrone x)
    hθ hcθ hbθ (T := 32 / (1 - r)) (by positivity) hdθ
    (fullBallCanonical_test_admissible hbox hr hrone hδ)
    (fullBallCanonical_test_support_compact hr hrone hδ)
    (fullBallCanonical_test_support hr hrone hδ) (δ := 1 / 32) (by norm_num)
  dsimp only at hh ⊢
  have hE : (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo (-1 : ℝ) 0,
      ‖D z‖ₑ ^ (2 : ℝ)).toReal ≤ (coordinateCylinderMass D 1).toReal := by
    simp only [coordinateCylinderMass, one_pow]
    apply ENNReal.toReal_mono
      (suitable_fullBall_gradient_coordinate_moment_lt_top hsol hbox).ne
    exact lintegral_mono fun z ↦ gradient_enorm_square_le_coordinate (D z)
  let X := (velocityCylinderSixMoment u 1).toReal
  have hX : 0 ≤ X := ENNReal.toReal_nonneg
  have hpoly := fullBall_canonical_source_polynomial_le_gap12
    (by linarith : 0 ≤ r) hrone hX
  have hH : 0 ≤ 18 * (fullBallProjectedHarmonicSquareCoefficient
      (fullBallCanonicalPressureRadius r)).toReal * X := by positivity
  dsimp only [X, velocityCylinderSixMoment] at hH
  simp only [one_pow] at hH
  refine ⟨hh.1, hh.2.1, hh.2.2.trans ?_⟩
  change _ ≤ (3 / 4) * (coordinateCylinderMass D 1).toReal +
    fullCylinderEndpointForcingConstant / (1 - r) ^ 12 * (X + X ^ 2 + X ^ 4)
  calc
    _ ≤ fullBallCanonicalLinearSourceCoefficient r * X +
        fullBallCanonicalQuadraticSourceCoefficient r * X ^ 2 +
        fullBallCanonicalFourthSourceCoefficient r * X ^ 4 +
          (3 / 4) * (coordinateCylinderMass D 1).toReal := by
      dsimp only [fullBallCanonicalLinearSourceCoefficient,
        fullBallCanonicalQuadraticSourceCoefficient, fullBallCanonicalFourthSourceCoefficient,
        X, velocityCylinderSixMoment]
      norm_num only [one_pow, show (24 : ℝ) * (1 / 32) = 3 / 4 by norm_num]
      nlinarith [hH]
    _ ≤ _ := by dsimp only [fullCylinderEndpointForcingConstant]; linarith [hpoly]

end FluidSingularSets
