-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallNativeErrorDecomposition
public import FluidSingularSets.FullBallCutoffSourceErrors
public import FluidSingularSets.FullBallTimeWeightedConvection
public import FluidSingularSets.FullBallTimeWeightedPressureErrors

/-!
# Genuine integral decomposition of the tested projected right hand side

Actual joint integrability of the projected right hand side and its four other
error families gives joint integrability of the literal pressure pairing.
Fubini then connects the native joint inequality to the actual mixed pressure
estimate. No joint pressure-integrability premise is assumed.
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

/-- Every actual compact tested RHS has its genuine native signed-error decomposition. -/
theorem suitable_fullBall_tested_rhs_integrable_decomposition
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {B : Set Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hlap : ∀ x, ‖spatialLaplacian (fun y ↦ φ y ^ 6) x‖ ≤ Λ)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hcθ : HasCompactSupport θ)
    (hbθ : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    (hdθ : ∀ t, deriv θ t ≤ T)
    (hψ : fullBallSeparatedCutoffTest φ θ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hsupp : tsupport (fullBallSeparatedCutoffTest φ θ) ⊆
      fullBallCompactInterior ρ ×ˢ Ioo a b)
    (hsuppB : tsupport (fullBallSeparatedCutoffTest φ θ) ⊆ B ×ˢ Ioo a b)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) :
    Integrable (fullBallNativePressureError u D p a b c φ (fun t ↦ θ t * χ t))
      (volume.restrict (B ×ˢ Ioo a b)) ∧
    (∫ z, fullBallProjectedRhsDensity ρ u D p a b c
      (fullBallSeparatedCutoffTest φ θ) z * χ z.2
        ∂(fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))) =
      (∫ z : ParabolicPoint in B ×ˢ Ioo a b, fullBallNativeTimeError u D p a b c φ θ χ z) +
      (∫ z : ParabolicPoint in B ×ˢ Ioo a b,
        fullBallNativeLaplacianError u D p a b c φ (fun t ↦ θ t * χ t) z) +
      (∫ z : ParabolicPoint in B ×ˢ Ioo a b,
        fullBallNativeConvectionError u D p a b c φ (fun t ↦ θ t * χ t) z) +
      2 * (∫ t in Ioo a b, ∫ x in B,
        fullBallNativePressureError u D p a b c φ (fun s ↦ θ s * χ s) (x, t)) +
      2 * (∫ z : ParabolicPoint in B ×ˢ Ioo a b,
        fullBallNativeHarmonicError u D p a b c φ (fun t ↦ θ t * χ t) z) := by
  let η : ℝ → ℝ := fun t ↦ θ t * χ t
  let R : ParabolicPoint → ℝ := fun z ↦
    fullBallNativeProjectedRhsDensity u D p a b c (fullBallSeparatedCutoffTest φ θ) z * χ z.2
  let TE := fullBallNativeTimeError u D p a b c φ θ χ
  let LE := fullBallNativeLaplacianError u D p a b c φ η
  let CE := fullBallNativeConvectionError u D p a b c φ η
  let PE := fullBallNativePressureError u D p a b c φ η
  let HE := fullBallNativeHarmonicError u D p a b c φ η
  let μ : Measure ParabolicPoint := volume.restrict (B ×ˢ Ioo a b)
  have hη : Continuous η := hθ.continuous.mul hχ
  have hηb (t : ℝ) : 0 ≤ η t ∧ η t ≤ 1 :=
    ⟨mul_nonneg (hbθ t).1 (hbχ t).1,
      (mul_le_mul (hbθ t).2 (hbχ t).2 (hbχ t).1 (by norm_num)).trans_eq (one_mul 1)⟩
  have hηn (t : ℝ) : ‖η t‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hηb t).1]
    exact (hηb t).2
  have hnψ (z : Vec3 × ℝ) : 0 ≤ fullBallSeparatedCutoffTest φ θ z :=
    mul_nonneg (pow_nonneg (hb z.1).1 6) (hbθ z.2).1
  have hRglobal := suitable_fullBall_native_projected_rhs_integrable
    hρ hρone hsol hbox hab hc hψ hnψ hsupp
  have hR : Integrable R μ := hRglobal.restrict.mul_bdd
    (hχ.comp continuous_snd_parabolicPoint).aestronglyMeasurable
    (ae_of_all _ fun z ↦ by
      rw [Real.norm_of_nonneg (hbχ z.2).1]
      exact (hbχ z.2).2)
  have hTE : Integrable TE μ :=
    (suitable_fullBall_time_cutoff_source_integrable_and_bound
      hsol hbox hab hc hρ hρone hB hBK hφ hb hθ hcθ hT hdθ hχ hbχ).1
  have hLE : Integrable LE μ :=
    (suitable_fullBall_laplacian_cutoff_source_integrable_and_bound
      hsol hbox hab hc hρ hρone hB hBK hφ hΛ hlap hη hηn).1
  have hCE : Integrable CE μ :=
    (fullBall_timeWeighted_convection_flux_integrable_and_abs_integral_le_source
      hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hη hηb
        (suitable_fullBall_velocity_six_moment_lt_top hsol hbox)).1
  have hHE : Integrable HE μ :=
    (suitable_fullBall_timeWeighted_harmonic_sum_integrable_and_bound
      hsol hbox hab hc hρ hρone hB hBK hφ hb hη hηb).1
  have heq : R =ᵐ[μ] fun z ↦ TE z + LE z + CE z + 2 * PE z + 2 * HE z := by
    filter_upwards [ae_restrict_mem (hB.measurableSet.prod measurableSet_Ioo)] with z hz
    exact fullBallNativeProjectedRhsDensity_mul_cutoff_eq
      ρ u D p a b c hφ hθ χ z (hBK hz.1)
  have hPE : Integrable PE μ := by
    have hi := ((((hR.sub hTE).sub hLE).sub hCE).sub (hHE.const_mul 2)).const_mul (1 / 2)
    apply hi.congr
    filter_upwards [heq] with z hz
    change (1 / 2) * ((((R z - TE z) - LE z) - CE z) - 2 * HE z) = PE z
    rw [hz]
    ring
  refine ⟨hPE, ?_⟩
  have hcompact : (∫ z, fullBallProjectedRhsDensity ρ u D p a b c
      (fullBallSeparatedCutoffTest φ θ) z * χ z.2
      ∂(fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))) =
        ∫ z : ParabolicPoint, R z := by
    exact integral_fullBallInterior_product_eq_integral ρ R (fun z hz ↦ by
      change fullBallNativeProjectedRhsDensity u D p a b c
        (fullBallSeparatedCutoffTest φ θ) z * χ z.2 = 0
      rw [fullBallNativeProjectedRhsDensity_zero_off_tsupport
        u D p a b c (fullBallSeparatedCutoffTest φ θ) z (fun h ↦ hz (hsupp h)), zero_mul])
  have hBglobal : (∫ z : ParabolicPoint, R z) = ∫ z, R z ∂μ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz ↦ by
      change fullBallNativeProjectedRhsDensity u D p a b c
        (fullBallSeparatedCutoffTest φ θ) z * χ z.2 = 0
      rw [fullBallNativeProjectedRhsDensity_zero_off_tsupport
        u D p a b c (fullBallSeparatedCutoffTest φ θ) z (fun h ↦ hz (hsuppB h)),
          zero_mul])).symm
  have hsplit : (∫ z, R z ∂μ) =
      (∫ z, TE z ∂μ) + (∫ z, LE z ∂μ) + (∫ z, CE z ∂μ) +
        2 * (∫ z, PE z ∂μ) + 2 * (∫ z, HE z ∂μ) := by
    rw [integral_congr_ae heq,
      integral_add (f := fun z ↦ TE z + LE z + CE z + 2 * PE z)
        (g := fun z ↦ 2 * HE z)
        (((hTE.add hLE).add hCE).add (hPE.const_mul 2)) (hHE.const_mul 2),
      integral_add (f := fun z ↦ TE z + LE z + CE z) (g := fun z ↦ 2 * PE z)
        ((hTE.add hLE).add hCE) (hPE.const_mul 2),
      integral_add (f := fun z ↦ TE z + LE z) (g := CE) (hTE.add hLE) hCE,
      integral_add hTE hLE,
      integral_const_mul, integral_const_mul]
  have hPfubini : (∫ z, PE z ∂μ) = ∫ t in Ioo a b, ∫ x in B, PE (x, t) := by
    change (∫ z : ParabolicPoint in B ×ˢ Ioo a b, PE z) = _
    rw [volume_parabolicPoint_eq_prod, ← Measure.prod_restrict]
    exact integral_prod_symm _ (by
      rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
      exact hPE)
  exact (hcompact.trans hBglobal).trans (hsplit.trans (by rw [hPfubini]))

end FluidSingularSets
