-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallTestedRhsDecomposition
public import FluidSingularSets.FullBallTestedEnergyBounds

/-!
# Genuine uniform bounds for the actual tested projected right hand side

The literal five-family decomposition combines the actual upper time error,
absolute Laplacian and convection errors, and signed pressure/harmonic errors.
Every smaller backward weight is bounded using the original tested energy.
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

/-- The actual proved signed pressure/harmonic error cost, retaining infinite inputs. -/
def fullBallPressureHarmonicErrorCost (ρ L δ : ℝ) (X E M : ℝ≥0∞) : ℝ≥0∞ :=
  6 * (12 * volume (vec3Ball (0 : Vec3) 1) ^ (1 / 6 : ℝ) * X *
    ENNReal.ofReal (6 * L) * M ^ (1 / 2 : ℝ)) +
  6 * (ENNReal.ofReal δ * E +
    fullBallViscousMixedPairingCoefficient ρ L ^ 2 / (4 * ENNReal.ofReal δ) * X) +
  18 * (ENNReal.ofReal (fullBallProjectedHarmonicHessianVelocityConstant ρ) *
    volume (vec3Ball (0 : Vec3) 1) ^ (2 / 3 : ℝ) * X * M ^ (1 / 2 : ℝ))

/-- Genuine positive Young parameter and finite actual inputs give a finite error cost. -/
theorem fullBallPressureHarmonicErrorCost_ne_top {ρ L δ : ℝ} {X E M : ℝ≥0∞}
    (hδ : 0 < δ) (hX : X ≠ ⊤) (hE : E ≠ ⊤) (hM : M ≠ ⊤) :
    fullBallPressureHarmonicErrorCost ρ L δ X E M ≠ ⊤ := by
  have hv : volume (vec3Ball (0 : Vec3) 1) ≠ ⊤ := (volume_vec3Ball_lt_top).ne
  have hd : 4 * ENNReal.ofReal δ ≠ 0 :=
    mul_ne_zero (by norm_num) (ENNReal.ofReal_pos.mpr hδ).ne'
  unfold fullBallPressureHarmonicErrorCost
  finiteness [hX, hE, hM, hv, hd, fullBallViscousMixedPairingCoefficient_ne_top ρ L]

/-- A genuinely smaller tested energy decreases every actual pressure/harmonic cost. -/
theorem fullBallPressureHarmonicErrorCost_mono {ρ L δ : ℝ} {X E M N : ℝ≥0∞}
    (hMN : M ≤ N) :
    fullBallPressureHarmonicErrorCost ρ L δ X E M ≤
      fullBallPressureHarmonicErrorCost ρ L δ X E N := by
  unfold fullBallPressureHarmonicErrorCost
  gcongr

/-- The finite actual signed error cost has the exact real Young/endpoint form. -/
theorem fullBallPressureHarmonicErrorCost_toReal {ρ L δ : ℝ} {X E M : ℝ≥0∞}
    (hρone : ρ < 1) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hX : X ≠ ⊤) (hE : E ≠ ⊤) (hM : M ≠ ⊤) :
    (fullBallPressureHarmonicErrorCost ρ L δ X E M).toReal =
      (432 * L * (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ) +
        18 * fullBallProjectedHarmonicHessianVelocityConstant ρ *
          (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (2 / 3 : ℝ)) *
        X.toReal * M.toReal ^ (1 / 2 : ℝ) +
      (3 / 2 : ℝ) * (fullBallViscousMixedPairingCoefficient ρ L).toReal ^ 2 / δ * X.toReal +
      6 * δ * E.toReal := by
  have hv : volume (vec3Ball (0 : Vec3) 1) ≠ ⊤ := (volume_vec3Ball_lt_top).ne
  have hd : 4 * ENNReal.ofReal δ ≠ 0 :=
    mul_ne_zero (by norm_num) (ENNReal.ofReal_pos.mpr hδ).ne'
  have hC : 6 * (12 * volume (vec3Ball (0 : Vec3) 1) ^ (1 / 6 : ℝ) * X *
      ENNReal.ofReal (6 * L) * M ^ (1 / 2 : ℝ)) ≠ ⊤ := by finiteness
  have hVE : ENNReal.ofReal δ * E ≠ ⊤ := by finiteness
  have hVX : fullBallViscousMixedPairingCoefficient ρ L ^ 2 /
      (4 * ENNReal.ofReal δ) * X ≠ ⊤ := by
    finiteness [fullBallViscousMixedPairingCoefficient_ne_top ρ L]
  have hV : 6 * (ENNReal.ofReal δ * E +
      fullBallViscousMixedPairingCoefficient ρ L ^ 2 / (4 * ENNReal.ofReal δ) * X) ≠ ⊤ := by
    finiteness
  have hH : 18 * (ENNReal.ofReal (fullBallProjectedHarmonicHessianVelocityConstant ρ) *
      volume (vec3Ball (0 : Vec3) 1) ^ (2 / 3 : ℝ) * X * M ^ (1 / 2 : ℝ)) ≠ ⊤ := by
    finiteness
  unfold fullBallPressureHarmonicErrorCost
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hC, hV⟩) hH,
    ENNReal.toReal_add hC hV]
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofNat]
  rw [ENNReal.toReal_add hVE hVX]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 6 * L),
    ENNReal.toReal_ofReal hδ.le,
    ENNReal.toReal_ofReal (fullBallProjectedHarmonicHessianVelocityConstant_nonneg hρone)]
  field_simp [hδ.ne']
  ring

/-- The real tested cost retains the true original weighted energy and source moments. -/
def fullBallTestedRhsCost (ρ L Λ T δ a b : ℝ) (X E M : ℝ≥0∞) : ℝ :=
  9 * (T + Λ) * (fullBallProjectedVelocitySquareCoefficient ρ).toReal * X.toReal +
  162 * L * ((fullBallProjectedVelocitySliceCoefficient ρ).toReal ^ (1 / 3 : ℝ) *
    (M.toReal + (fullBallProjectedVelocitySliceCoefficient ρ).toReal ^ 2 * X.toReal)
      ^ (5 / 6 : ℝ) * X.toReal ^ (2 / 3 : ℝ) * (volume (Ioo a b)).toReal ^ (1 / 4 : ℝ)) +
  (fullBallPressureHarmonicErrorCost ρ L δ X E M).toReal

/-- The true tested cost is exactly the quadratic, convection, pressure and Young expression. -/
theorem fullBallTestedRhsCost_eq_explicit {ρ L Λ T δ a b : ℝ} {X E M : ℝ≥0∞}
    (hρone : ρ < 1) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hX : X ≠ ⊤) (hE : E ≠ ⊤) (hM : M ≠ ⊤) :
    fullBallTestedRhsCost ρ L Λ T δ a b X E M =
      (9 * (T + Λ) * (fullBallProjectedVelocitySquareCoefficient ρ).toReal +
        (3 / 2 : ℝ) * (fullBallViscousMixedPairingCoefficient ρ L).toReal ^ 2 / δ) * X.toReal +
      162 * L * (fullBallProjectedVelocitySliceCoefficient ρ).toReal ^ (1 / 3 : ℝ) *
        (M.toReal + (fullBallProjectedVelocitySliceCoefficient ρ).toReal ^ 2 * X.toReal)
          ^ (5 / 6 : ℝ) * X.toReal ^ (2 / 3 : ℝ) * (volume (Ioo a b)).toReal ^ (1 / 4 : ℝ) +
      (432 * L * (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ) +
        18 * fullBallProjectedHarmonicHessianVelocityConstant ρ *
          (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (2 / 3 : ℝ)) *
        X.toReal * M.toReal ^ (1 / 2 : ℝ) + 6 * δ * E.toReal := by
  unfold fullBallTestedRhsCost
  rw [fullBallPressureHarmonicErrorCost_toReal hρone hL hδ hX hE hM]
  ring

/-- Actual suitable original gradient energy is finite on the same unforced box. -/
theorem suitable_fullBall_gradient_energy_lt_top
    {Ω : Set Vec3} {I : Set ℝ} {q a b : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) :
    (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b, ‖D z‖ₑ ^ (2 : ℝ)) < ⊤ :=
  (lintegral_mono fun _ ↦ le_add_left le_rfl).trans_lt
    (hsol.toData.energy_lintegral_lt_top hbox)

/-- The genuine five-family decomposition gives a uniform RHS bound
for every smaller time weight. -/
theorem suitable_fullBall_tested_rhs_uniform_bound
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
    {δ : ℝ} (hδ : 0 < δ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) :
    (∫ z, fullBallProjectedRhsDensity ρ u D p a b c
      (fullBallSeparatedCutoffTest φ θ) z * χ z.2
        ∂(fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))) ≤
      fullBallTestedRhsCost ρ L Λ T δ a b
        (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2)
        (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b, ‖D z‖ₑ ^ (2 : ℝ))
        (fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ) := by
  let η : ℝ → ℝ := fun t ↦ θ t * χ t
  let X : ℝ≥0∞ := ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
    (volume.restrict (vec3Ball 0 1)) ^ 2
  let E : ℝ≥0∞ := ∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b, ‖D z‖ₑ ^ (2 : ℝ)
  let M : ℝ≥0∞ := fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ
  let N : ℝ≥0∞ := fullBallTimeWeightedProjectedEnergySup u D p a b c B φ η
  let W : ℝ≥0∞ := fullBallTimeWeightedProjectedSixMoment u D p a b c B φ η
  let κ : ℝ≥0∞ := fullBallProjectedVelocitySliceCoefficient ρ
  have hη : Continuous η := hθ.continuous.mul hχ
  have hηb (t : ℝ) : 0 ≤ η t ∧ η t ≤ 1 :=
    ⟨mul_nonneg (hbθ t).1 (hbχ t).1,
      (mul_le_mul (hbθ t).2 (hbχ t).2 (hbχ t).1 (by norm_num)).trans_eq (one_mul 1)⟩
  have hηn (t : ℝ) : ‖η t‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hηb t).1]
    exact (hηb t).2
  have hXr := suitable_fullBall_velocity_six_moment_lt_top hsol hbox
  have hX : X ≠ ⊤ := by simpa only [X, ENNReal.rpow_ofNat] using hXr.ne
  have hE : E ≠ ⊤ := (suitable_fullBall_gradient_energy_lt_top hsol hbox).ne
  have hM : M ≠ ⊤ := (fullBallTimeWeightedProjectedEnergySup_lt_top
    hsol hbox hab hc hρ hρone hB hBK hφ hb hbθ).ne
  have hNM : N ≤ M := fullBallTimeWeightedProjectedEnergySup_mono u D p a b c B φ
    (fun t ↦ (hηb t).1) (fun t ↦
      mul_le_of_le_one_right (hbθ t).1 (hbχ t).2)
  have hW : W ≤ κ ^ 2 * X := by
    simpa only [κ, X, ENNReal.rpow_ofNat] using fullBallTimeWeightedProjectedSixMoment_le_source
      hsol hbox hab hc hρ hρone hB hBK hφ hb hη hηb
  have hκ : κ ≠ ⊤ := fullBallProjectedVelocitySliceCoefficient_ne_top ρ
  have hsum : (N + W).toReal ≤ M.toReal + κ.toReal ^ 2 * X.toReal := by
    have hh := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hM, ENNReal.mul_ne_top (ENNReal.pow_ne_top hκ) hX⟩)
      (add_le_add hNM hW)
    simpa only [ENNReal.toReal_add hM (ENNReal.mul_ne_top (ENNReal.pow_ne_top hκ) hX),
      ENNReal.toReal_mul, ENNReal.toReal_pow] using hh
  have hTbound := (suitable_fullBall_time_cutoff_source_integrable_and_bound
    hsol hbox hab hc hρ hρone hB hBK hφ hb hθ hcθ hT hdθ hχ hbχ).2
  have hLbound := (suitable_fullBall_laplacian_cutoff_source_integrable_and_bound
    hsol hbox hab hc hρ hρone hB hBK hφ hΛ hlap hη hηn).2
  have hCbound := (fullBall_timeWeighted_convection_flux_integrable_and_abs_integral_le_source
    hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hη hηb hXr).2
  have hC : (∫ z : ParabolicPoint in B ×ˢ Ioo a b,
      fullBallNativeConvectionError u D p a b c φ η z) ≤
      162 * L * (κ.toReal ^ (1 / 3 : ℝ) *
        (M.toReal + κ.toReal ^ 2 * X.toReal) ^ (5 / 6 : ℝ) *
          X.toReal ^ (2 / 3 : ℝ) * (volume (Ioo a b)).toReal ^ (1 / 4 : ℝ)) := by
    apply (le_abs_self _).trans
    apply hCbound.trans
    simp only [ENNReal.rpow_ofNat]
    change 162 * L * (κ.toReal ^ (1 / 3 : ℝ) * (N + W).toReal ^ (5 / 6 : ℝ) *
      X.toReal ^ (2 / 3 : ℝ) * (volume (Ioo a b)).toReal ^ (1 / 4 : ℝ)) ≤ _
    gcongr
  have hPH := suitable_fullBall_timeWeighted_pressure_harmonic_signed_error_bound
    hsol hbox hab hc hρ hρone hB hBK hφ hcφ hsφ hb hL hgrad hη hηb hδ
      (σP := 2) (σH := 2) (by norm_num) (by norm_num)
  change ‖2 * (∫ t in Ioo a b, ∫ x in B,
      fullBallNativePressureError u D p a b c φ η (x, t)) +
    2 * (∫ z : ParabolicPoint in B ×ˢ Ioo a b,
      fullBallNativeHarmonicError u D p a b c φ η z)‖ₑ ≤
        fullBallPressureHarmonicErrorCost ρ L δ X E N at hPH
  have hPHreal := ENNReal.toReal_mono
    (fullBallPressureHarmonicErrorCost_ne_top hδ hX hE hM)
    (hPH.trans (fullBallPressureHarmonicErrorCost_mono hNM))
  simp only [toReal_enorm] at hPHreal
  have hPHupper : 2 * (∫ t in Ioo a b, ∫ x in B,
      fullBallNativePressureError u D p a b c φ η (x, t)) +
    2 * (∫ z : ParabolicPoint in B ×ˢ Ioo a b,
      fullBallNativeHarmonicError u D p a b c φ η z) ≤
        (fullBallPressureHarmonicErrorCost ρ L δ X E M).toReal :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hPHreal)
  have hLupper : (∫ z : ParabolicPoint in B ×ˢ Ioo a b,
      fullBallNativeLaplacianError u D p a b c φ η z) ≤
      9 * Λ * (fullBallProjectedVelocitySquareCoefficient ρ).toReal * X.toReal :=
    (Real.le_norm_self _).trans hLbound
  have hd := (suitable_fullBall_tested_rhs_integrable_decomposition
    hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hΛ hlap hθ hcθ hbθ hT hdθ
      hψ hsupp hsuppB hχ hbχ).2
  rw [hd]
  calc
    _ = (∫ z : ParabolicPoint in B ×ˢ Ioo a b,
        fullBallNativeTimeError u D p a b c φ θ χ z) +
      (∫ z : ParabolicPoint in B ×ˢ Ioo a b,
        fullBallNativeLaplacianError u D p a b c φ η z) +
      (∫ z : ParabolicPoint in B ×ˢ Ioo a b,
        fullBallNativeConvectionError u D p a b c φ η z) +
      (2 * (∫ t in Ioo a b, ∫ x in B,
        fullBallNativePressureError u D p a b c φ η (x, t)) +
        2 * (∫ z : ParabolicPoint in B ×ˢ Ioo a b,
          fullBallNativeHarmonicError u D p a b c φ η z)) := by ring
    _ ≤ (9 * T * (fullBallProjectedVelocitySquareCoefficient ρ).toReal * X.toReal) +
        (9 * Λ * (fullBallProjectedVelocitySquareCoefficient ρ).toReal * X.toReal) +
      (162 * L * (κ.toReal ^ (1 / 3 : ℝ) *
        (M.toReal + κ.toReal ^ 2 * X.toReal) ^ (5 / 6 : ℝ) *
          X.toReal ^ (2 / 3 : ℝ) * (volume (Ioo a b)).toReal ^ (1 / 4 : ℝ))) +
      (fullBallPressureHarmonicErrorCost ρ L δ X E M).toReal :=
        add_le_add (add_le_add (add_le_add hTbound hLupper) hC) hPHupper
    _ = _ := by unfold fullBallTestedRhsCost; ring

end FluidSingularSets
