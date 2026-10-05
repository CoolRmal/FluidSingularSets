-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallHarmonicCutoffErrors

/-!
# Genuine summed pressure and harmonic cutoff errors

The original pressure mean cancels in the actual sixth-cutoff divergence test.
The resulting literal pressure integral is the sum of the genuine convective
and viscous Stokes pairings. Their proved component bounds and the actual
harmonic cross bounds then control the full signed error on the original
interval, with every boundary-margin and absorption coefficient explicit.
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

/-- The actual sixth power of a compact cutoff is a genuine weak spatial test. -/
def fullBallSixthCutoffWeakTest {B : Set Vec3} {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ B) : WeakTestFunction B where
  toFun := fun x ↦ φ x ^ (6 : ℕ)
  contDiff := hφ.pow 6
  hasCompactSupport := by
    simpa only [HasCompactSupport, tsupport, Function.support_pow (n := 6) φ (by norm_num)] using hc
  tsupport_subset := by
    simpa only [tsupport, Function.support_pow (n := 6) φ (by norm_num)] using hs

/-- Literal finite sums retain their actual integral and component error bound. -/
theorem integral_finite_family_enorm_bound
    {A : Type*} [MeasurableSpace A] {μ : Measure A} {ι : Type*} [Fintype ι]
    {f : ι → A → ℝ} (hf : ∀ i, Integrable (f i) μ) {C : ℝ≥0∞}
    (hbound : ∀ i, ‖∫ x, f i x ∂μ‖ₑ ≤ C) :
    Integrable (fun x ↦ ∑ i, f i x) μ ∧
      ‖∫ x, ∑ i, f i x ∂μ‖ₑ ≤ Fintype.card ι * C := by
  refine ⟨integrable_finsetSum _ (fun i _ ↦ hf i), ?_⟩
  rw [integral_finsetSum _ (fun i _ ↦ hf i)]
  exact (enorm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ ↦ hbound i).trans_eq (by simp))

section LocalBox

variable {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {B : Set Vec3}

/-- The actual spatial pressure test is its literal sum of sixth-cutoff components. -/
theorem fullBall_pressure_cutoff_pairing_eq_components_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1)
    (P : ℝ → Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      (∫ x in B, P t x * fullBallProjectedPressureTest u D p a b c
        (fun y ↦ φ y ^ (6 : ℕ)) θ (x, t)) =
      ∑ i : Fin 3, ∫ x in B, P t x *
        fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t) := by
  have hB1 := hBK.trans (fullBallCompactInterior_subset_unit hρ hρone)
  have hGs := ae_all_iff.mpr fun i : Fin 3 ↦
    (fullBallProjectedPressureCutoffComponent_top_data
      hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hθ hθb i).1.slices
  filter_upwards [hGs] with t ht
  have hp := (Lp.memLp (P t)).mono_measure (Measure.restrict_mono_set volume hB1)
  have hi (i : Fin 3) : Integrable (fun x ↦ P t x *
      fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t))
        (volume.restrict B) := hp.integrable_mul (ht i)
  have heq (x : Vec3) : P t x * fullBallProjectedPressureTest u D p a b c
      (fun y ↦ φ y ^ (6 : ℕ)) θ (x, t) =
      ∑ i : Fin 3, P t x *
        fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t) := by
    simp only [fullBallProjectedPressureTest, fullBallProjectedPressureCutoffComponent,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [heq]
  exact integral_finsetSum _ (fun i _ ↦ hi i)

/-- Actual original mean cancellation gives the complete literal two-pressure component form. -/
theorem suitable_fullBall_pressure_cutoff_pairing_eq_components_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ B) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      (∫ x in B, (p (x, t) - fullBallProjectedMomentumPressure u D p t x) *
        fullBallProjectedPressureTest u D p a b c (fun y ↦ φ y ^ (6 : ℕ)) θ (x, t)) =
      (∑ i : Fin 3, ∫ x in B, (unitBallConvectivePressureCurve u t).val x *
        fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t)) +
      (∑ i : Fin 3, ∫ x in B, (unitBallViscousPressureCurve D t).val x *
        fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t)) := by
  let ψ := fullBallSixthCutoffWeakTest hφ hcφ hsφ
  filter_upwards [suitable_fullBall_pressure_pairing_eq_stokes_ae_localBox
    (c := c) hsol hbox hρ hρone hB hBK ψ θ,
    fullBall_pressure_cutoff_pairing_eq_components_ae
      hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hθ hθb
        (fun t ↦ (unitBallConvectivePressureCurve u t).val),
    fullBall_pressure_cutoff_pairing_eq_components_ae
      hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hθ hθb
        (fun t ↦ (unitBallViscousPressureCurve D t).val)] with t ht hcpt hvpt
  exact ht.trans (congrArg₂ (fun r s : ℝ ↦ r + s) hcpt hvpt)

/-- The actual pressure cutoff integral is integrable in time and has its weighted error bound. -/
theorem suitable_fullBall_pressure_cutoff_integrable_and_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ B) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t ↦ ∫ x in B, (p (x, t) - fullBallProjectedMomentumPressure u D p t x) *
      fullBallProjectedPressureTest u D p a b c (fun y ↦ φ y ^ (6 : ℕ)) θ (x, t))
        (volume.restrict (Ioo a b)) ∧
    ‖∫ t in Ioo a b, ∫ x in B,
      (p (x, t) - fullBallProjectedMomentumPressure u D p t x) *
        fullBallProjectedPressureTest u D p a b c (fun y ↦ φ y ^ (6 : ℕ)) θ (x, t)‖ₑ ≤
      3 * (12 * volume (vec3Ball (0 : Vec3) 1) ^ (1 / 6 : ℝ) *
        (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2) * ENNReal.ofReal (6 * L) *
            fullBallProjectedCutoffSliceEnergy u D p a b c B φ ^ (1 / 2 : ℝ)) +
      3 * (ENNReal.ofReal δ *
        (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b, ‖D z‖ₑ ^ (2 : ℝ)) +
          fullBallViscousMixedPairingCoefficient ρ L ^ 2 / (4 * ENNReal.ofReal δ) *
            (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
              (volume.restrict (vec3Ball 0 1)) ^ 2)) := by
  have hC (i : Fin 3) := suitable_fullBall_convective_pressure_cutoff_component_bound
    hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hθ hθb i
  have hV (i : Fin 3) := suitable_fullBall_viscous_mixed_pairing_bound_localBox
    hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hθ hθb i
  have hVy (i : Fin 3) := suitable_fullBall_viscous_mixed_pairing_young_localBox
    hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hθ hθb i hδ
  have hCs := integral_finite_family_enorm_bound (fun i ↦ (hC i).1) (fun i ↦ (hC i).2)
  have hVs := integral_finite_family_enorm_bound (fun i ↦ (hV i).1) hVy
  have heq := suitable_fullBall_pressure_cutoff_pairing_eq_components_ae
    hsol hbox hab hc hρ hρone hB hBK hφ hcφ hsφ hb hL hgrad hθ hθb
  refine ⟨(hCs.1.add hVs.1).congr (heq.mono fun _ ht ↦ ht.symm), ?_⟩
  rw [integral_congr_ae heq, integral_add hCs.1 hVs.1]
  exact (enorm_add_le _ _).trans (add_le_add hCs.2 hVs.2)

/-- All nine actual harmonic cross components are integrable with their literal summed bound. -/
theorem suitable_fullBall_harmonic_cutoff_sum_integrable_and_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) :
    Integrable (fun z : ParabolicPoint ↦ ∑ i : Fin 3, ∑ j : Fin 3,
      θ z.2 * φ z.1 ^ 6 * u z j *
        fullBallProjectedHarmonicDerivativeAmbient u D p a b c z i j *
          fullBallProjectedVelocityAmbient u D p a b c z i)
      (volume.restrict (B ×ˢ Ioo a b)) ∧
    ‖∫ z : ParabolicPoint in B ×ˢ Ioo a b, ∑ i : Fin 3, ∑ j : Fin 3,
      θ z.2 * φ z.1 ^ 6 * u z j *
        fullBallProjectedHarmonicDerivativeAmbient u D p a b c z i j *
          fullBallProjectedVelocityAmbient u D p a b c z i‖ₑ ≤
      9 * (ENNReal.ofReal (fullBallProjectedHarmonicHessianVelocityConstant ρ) *
        volume (vec3Ball (0 : Vec3) 1) ^ (2 / 3 : ℝ) *
          (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
            (volume.restrict (vec3Ball 0 1)) ^ 2) *
              fullBallProjectedCutoffSliceEnergy u D p a b c B φ ^ (1 / 2 : ℝ)) := by
  have hI (ij : Fin 3 × Fin 3) :=
    (suitable_fullBall_harmonic_cutoff_component_integrable_and_bound
      hsol hbox hab hc hρ hρone hB hBK hφ hb hθ hθb ij.1 ij.2).1
  have hE (ij : Fin 3 × Fin 3) := suitable_fullBall_harmonic_cutoff_component_endpoint_bound
    hsol hbox hab hc hρ hρone hB hBK hφ hb hθ hθb ij.1 ij.2
  have hh := integral_finite_family_enorm_bound hI hE
  simpa only [Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_fin,
    Nat.reduceMul, Nat.cast_ofNat] using hh

/-- Literal pressure and harmonic signed errors obey the genuine sum of their proved bounds. -/
theorem suitable_fullBall_pressure_harmonic_signed_error_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ B) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) {σP σH : ℝ} (hσP : ‖σP‖ ≤ 2) (hσH : ‖σH‖ ≤ 2) :
    ‖σP * (∫ t in Ioo a b, ∫ x in B,
      (p (x, t) - fullBallProjectedMomentumPressure u D p t x) *
        fullBallProjectedPressureTest u D p a b c (fun y ↦ φ y ^ (6 : ℕ)) θ (x, t)) +
      σH * (∫ z : ParabolicPoint in B ×ˢ Ioo a b, ∑ i : Fin 3, ∑ j : Fin 3,
        θ z.2 * φ z.1 ^ 6 * u z j *
          fullBallProjectedHarmonicDerivativeAmbient u D p a b c z i j *
            fullBallProjectedVelocityAmbient u D p a b c z i)‖ₑ ≤
      6 * (12 * volume (vec3Ball (0 : Vec3) 1) ^ (1 / 6 : ℝ) *
        (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2) * ENNReal.ofReal (6 * L) *
            fullBallProjectedCutoffSliceEnergy u D p a b c B φ ^ (1 / 2 : ℝ)) +
      6 * (ENNReal.ofReal δ *
        (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b, ‖D z‖ₑ ^ (2 : ℝ)) +
          fullBallViscousMixedPairingCoefficient ρ L ^ 2 / (4 * ENNReal.ofReal δ) *
            (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
              (volume.restrict (vec3Ball 0 1)) ^ 2)) +
      18 * (ENNReal.ofReal (fullBallProjectedHarmonicHessianVelocityConstant ρ) *
        volume (vec3Ball (0 : Vec3) 1) ^ (2 / 3 : ℝ) *
          (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
            (volume.restrict (vec3Ball 0 1)) ^ 2) *
              fullBallProjectedCutoffSliceEnergy u D p a b c B φ ^ (1 / 2 : ℝ)) := by
  have hp := (suitable_fullBall_pressure_cutoff_integrable_and_bound
    hsol hbox hab hc hρ hρone hB hBK hφ hcφ hsφ hb hL hgrad hθ hθb hδ).2
  have hh := (suitable_fullBall_harmonic_cutoff_sum_integrable_and_bound
    hsol hbox hab hc hρ hρone hB hBK hφ hb hθ hθb).2
  have hP : ‖σP‖ₑ ≤ (2 : ℝ≥0∞) := by
    simpa only [← ofReal_norm, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hσP
  have hH : ‖σH‖ₑ ≤ (2 : ℝ≥0∞) := by
    simpa only [← ofReal_norm, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hσH
  exact (enorm_add_le _ _).trans
    ((add_le_add (by simpa only [enorm_mul] using mul_le_mul' hP hp)
      (by simpa only [enorm_mul] using mul_le_mul' hH hh)).trans_eq (by ring))

end LocalBox

end FluidSingularSets
