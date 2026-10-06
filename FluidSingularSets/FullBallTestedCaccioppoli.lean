-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallTestedRhsBounds
public import FluidSingularSets.FullBallTestedOriginalGradient
public import FluidSingularSets.FullBallEndpointAbsorption

/-!
# Genuine suitable cutoff Caccioppoli inequality

All tested-energy and signed-error hypotheses are discharged from the actual
suitable solution and the genuine compact cutoff. Young absorption gives the
original gradient a bound involving only the original endpoint velocity moment,
the adjustable outer gradient energy, and actual cutoff coefficients.
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

/-- The literal quadratic source cost in the genuine tested right hand side. -/
def fullBallEndpointQuadraticCost (ρ L Λ T δ : ℝ) : ℝ :=
  9 * (T + Λ) * (fullBallProjectedVelocitySquareCoefficient ρ).toReal +
    (3 / 2 : ℝ) * (fullBallViscousMixedPairingCoefficient ρ L).toReal ^ 2 / δ

/-- The literal sharp convection coefficient, with its actual original time interval. -/
def fullBallEndpointConvectionCost (ρ L a b : ℝ) : ℝ :=
  162 * L * (fullBallProjectedVelocitySliceCoefficient ρ).toReal ^ (1 / 3 : ℝ) *
    (volume (Ioo a b)).toReal ^ (1 / 4 : ℝ)

/-- The actual nonlinear pressure and harmonic Hessian square-root coefficient. -/
def fullBallEndpointPressureCost (ρ L : ℝ) : ℝ :=
  432 * L * (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ) +
    18 * fullBallProjectedHarmonicHessianVelocityConstant ρ *
      (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (2 / 3 : ℝ)

/-- The actual tested cost is nonnegative for genuine nonnegative cutoff bounds. -/
theorem fullBallTestedRhsCost_nonneg {ρ L Λ T δ a b : ℝ} (X E M : ℝ≥0∞)
    (hL : 0 ≤ L) (hΛ : 0 ≤ Λ) (hT : 0 ≤ T) :
    0 ≤ fullBallTestedRhsCost ρ L Λ T δ a b X E M := by
  unfold fullBallTestedRhsCost
  positivity

/-- Genuine suitable data and actual supported cutoffs imply the original-gradient estimate.
No tested energy inequality or quantitative right hand side is assumed. -/
theorem suitable_fullBall_tested_original_gradient_caccioppoli
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {B : Set Vec3} {A : Set ParabolicPoint}
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
    (hA : MeasurableSet A) (hAB : A ⊆ B ×ˢ Ioo a b)
    (hψone : ∀ z ∈ A, φ z.1 ^ 6 * θ z.2 = 1) {δ : ℝ} (hδ : 0 < δ) :
    let X := (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
      (volume.restrict (vec3Ball 0 1)) ^ 2).toReal
    let c₀ := fullBallEndpointQuadraticCost ρ L Λ T δ
    let c₁ := fullBallEndpointConvectionCost ρ L a b
    let c₂ := fullBallEndpointPressureCost ρ L
    (∫⁻ z in A, ENNReal.ofReal (projectedGradientSquare (D z))) < ⊤ ∧
    (∫⁻ z in A, ENNReal.ofReal (projectedGradientSquare (D z))).toReal ≤
      24 * δ * (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b, ‖D z‖ₑ ^ (2 : ℝ)).toReal +
      (4 * c₀ + 2 * (fullBallProjectedVelocitySliceCoefficient ρ).toReal ^ 2 +
        18 * (fullBallProjectedHarmonicSquareCoefficient ρ).toReal) * X +
      32 * c₂ ^ 2 * X ^ 2 + 131072 * c₁ ^ 6 * X ^ 4 := by
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
  have hinner := suitable_fullBall_original_gradient_le_tested_dissipation
    hsol hbox hab hc hρ hρone hA hB hBK hAB hsφ (fun t ↦ (hbθ t).1) hψone
  have hN₂ : (2 : ℝ≥0∞) * N ≠ ⊤ := by finiteness
  have hH : 18 * fullBallProjectedHarmonicSquareCoefficient ρ * X ≠ ⊤ := by
    finiteness [fullBallProjectedHarmonicSquareCoefficient_ne_top ρ]
  have hsum : 2 * N + 18 * fullBallProjectedHarmonicSquareCoefficient ρ * X ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hN₂, hH⟩
  refine ⟨hinner.trans_lt hsum.lt_top, ?_⟩
  have hir := ENNReal.toReal_mono hsum hinner
  simp only [ENNReal.toReal_add hN₂ hH, ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hir
  have hNY : 2 * N.toReal ≤ Y := by dsimp only [Y]; linarith
  calc
    _ ≤ Y + 18 * (fullBallProjectedHarmonicSquareCoefficient ρ).toReal * X.toReal :=
      hir.trans (add_le_add hNY le_rfl)
    _ ≤ (4 * c₀ + 2 * κ ^ 2) * X.toReal + 131072 * c₁ ^ 6 * X.toReal ^ 4 +
        32 * c₂ ^ 2 * X.toReal ^ 2 + 4 * (6 * δ) * E.toReal +
          18 * (fullBallProjectedHarmonicSquareCoefficient ρ).toReal * X.toReal :=
      add_le_add hbound le_rfl
    _ = _ := by ring

end FluidSingularSets
