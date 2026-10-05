-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.TimeWeightedProjectedConvection
public import FluidSingularSets.FullBallTimeWeightedEnergy

/-!
# Actual full ball time weighted endpoint convection

Genuine suitable projected fields give the square-root time weighted energy.
The sharp endpoint Hölder estimate and the actual harmonic source bounds then
control convection by that tested energy and the original velocity mixed norm.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- The literal square mixed norm of the actual square-root time weighted velocity. -/
def fullBallTimeWeightedProjectedSixMoment
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (B : Set Vec3)
    (φ : Vec3 → ℝ) (θ : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo a b, eLpNorm
    (fun x ↦ fullBallTimeWeightedProjectedVelocity u D p a b c φ θ (x, t)) 6
    (volume.restrict B) ^ (2 : ℝ)

/-- The genuine nonnegative norm density controlling the tested convection. -/
def fullBallTimeWeightedConvectionNormDensity
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (φ : Vec3 → ℝ) (θ : ℝ → ℝ)
    (z : ParabolicPoint) : ℝ :=
  θ z.2 * φ z.1 ^ 5 * ‖u z‖ * ‖fullBallProjectedVelocityAmbient u D p a b c z‖ ^ 2

/-- The literal convection term of the actual time-weighted sixth-cutoff energy test. -/
def fullBallTimeWeightedConvectionFlux
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (φ : Vec3 → ℝ) (θ : ℝ → ℝ)
    (z : ParabolicPoint) : ℝ :=
  θ z.2 * vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z) ^ 2 *
    ∑ j : Fin 3, u z j * spatialDeriv (fun x ↦ φ x ^ (6 : ℕ)) j z.1

/-- Actual coordinate and Euclidean norm bounds control the literal tested flux pointwise. -/
theorem fullBallTimeWeightedConvectionFlux_abs_le
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x)
    {θ : ℝ → ℝ} (hθ : ∀ t, 0 ≤ θ t) {L : ℝ} (_hL : 0 ≤ L)
    (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L) (z : ParabolicPoint) :
    |fullBallTimeWeightedConvectionFlux u D p a b c φ θ z| ≤
      162 * L * fullBallTimeWeightedConvectionNormDensity u D p a b c φ θ z := by
  let V := fullBallProjectedVelocityAmbient u D p a b c z
  have hE : vec3EuclideanNorm V ^ 2 ≤ 9 * ‖V‖ ^ 2 := by
    have hs : Real.sqrt 3 ≤ (3 : ℝ) := by
      exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
    have hn := (vec3EuclideanNorm_le_sqrt_three_mul_norm V).trans
      (mul_le_mul_of_nonneg_right hs (norm_nonneg V))
    nlinarith [vec3EuclideanNorm_nonneg V, norm_nonneg V]
  have hd (j : Fin 3) : |spatialDeriv φ j z.1| ≤ L := by
    have hh := (norm_le_pi_norm (classicalGradient φ z.1) j).trans (hgrad z.1)
    simpa only [Real.norm_eq_abs, classicalGradient, spatialDeriv] using hh
  have hu (j : Fin 3) : |u z j| ≤ ‖u z‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (u z) j
  have hφ0 : 0 ≤ φ z.1 := hb z.1
  have hj (j : Fin 3) : |u z j * spatialDeriv (fun x ↦ φ x ^ (6 : ℕ)) j z.1| ≤
      6 * L * φ z.1 ^ 5 * ‖u z‖ := by
    rw [spatialDeriv_cutoff_sixth hφ, abs_mul, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 6), abs_pow, abs_of_nonneg (hb z.1)]
    have hh := mul_le_mul (hu j)
      (mul_le_mul_of_nonneg_left (hd j) (by positivity : 0 ≤ 6 * φ z.1 ^ 5))
      (by positivity) (norm_nonneg _)
    nlinarith
  have hsum : |∑ j : Fin 3, u z j * spatialDeriv (fun x ↦ φ x ^ (6 : ℕ)) j z.1| ≤
      18 * L * φ z.1 ^ 5 * ‖u z‖ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _j : Fin 3, 6 * L * φ z.1 ^ 5 * ‖u z‖ :=
        Finset.sum_le_sum fun j _ ↦ hj j
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  rw [fullBallTimeWeightedConvectionFlux, abs_mul, abs_mul,
    abs_of_nonneg (hθ z.2), abs_pow, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
  have hh := mul_le_mul
    (mul_le_mul_of_nonneg_left hE (hθ z.2)) hsum (abs_nonneg _)
    (by positivity [hθ z.2] : 0 ≤ θ z.2 * (9 * ‖V‖ ^ 2))
  exact hh.trans_eq (by dsimp only [V, fullBallTimeWeightedConvectionNormDensity]; ring)

private theorem endpoint_product_le_source {M W XU XV X κ T : ℝ≥0∞}
    (hu : XU ≤ X) (hv : XV ≤ κ ^ 2 * X) :
    (M + W) ^ (5 / 6 : ℝ) * XU ^ (1 / 2 : ℝ) * XV ^ (1 / 6 : ℝ) *
        T ^ (1 / 4 : ℝ) ≤
      κ ^ (1 / 3 : ℝ) * (M + W) ^ (5 / 6 : ℝ) * X ^ (2 / 3 : ℝ) *
        T ^ (1 / 4 : ℝ) := by
  have hu' := ENNReal.rpow_le_rpow hu (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hv' := ENNReal.rpow_le_rpow hv (by norm_num : (0 : ℝ) ≤ 1 / 6)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast κ 2,
    ← ENNReal.rpow_mul] at hv'
  norm_num only [show (2 : ℝ) * (1 / 6) = 1 / 3 by norm_num] at hv'
  apply (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hu') hv') le_rfl).trans_eq
  calc
    _ = κ ^ (1 / 3 : ℝ) * (M + W) ^ (5 / 6 : ℝ) *
        (X ^ (1 / 2 : ℝ) * X ^ (1 / 6 : ℝ)) * T ^ (1 / 4 : ℝ) := by ring
    _ = _ := by
      rw [← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 6 : ℝ) (by norm_num) (by norm_num)]
      norm_num

section Suitable

variable {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {B : Set Vec3} {φ : Vec3 → ℝ} {θ : ℝ → ℝ}

/-- The true time weighted mixed norm is bounded by the original endpoint source moment. -/
theorem fullBallTimeWeightedProjectedSixMoment_le_source
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hθ : Continuous θ) (hθb : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1) :
    fullBallTimeWeightedProjectedSixMoment u D p a b c B φ θ ≤
      fullBallProjectedVelocitySliceCoefficient ρ ^ 2 *
        ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ (2 : ℝ) := by
  have hW := fullBallTimeWeightedProjectedVelocity_aestronglyMeasurable
    hsol hbox hab hc hρ hρone hBK hφ hθ
  have hnorm (z : ParabolicPoint) :
      ‖fullBallTimeWeightedProjectedVelocity u D p a b c φ θ z‖ ≤
        ‖fullBallProjectedVelocityAmbient u D p a b c z‖ :=
    (fullBallTimeWeightedProjectedVelocity_norm_le u D p a b c φ hθb z).trans
      (projected_cutoff_power_norm_le
        (fullBallProjectedVelocityAmbient u D p a b c z) (hb z.1).1 (hb z.1).2 3)
  have hp : ∀ᵐ t ∂volume.restrict (Ioo a b),
      eLpNorm (fun x ↦ fullBallTimeWeightedProjectedVelocity u D p a b c φ θ (x, t)) 6
        (volume.restrict B) ^ (2 : ℝ) ≤
      eLpNorm (fun x ↦ fullBallProjectedVelocityAmbient u D p a b c (x, t)) 6
        (volume.restrict B) ^ (2 : ℝ) := by
    filter_upwards [hW.prodMk_right] with t hwt
    exact ENNReal.rpow_le_rpow (eLpNorm_mono_ae hwt (ae_of_all _ fun x ↦ hnorm (x, t)))
      (by norm_num)
  exact (lintegral_mono_ae hp).trans (by
    simpa only [ENNReal.rpow_ofNat] using
      fullBallProjectedVelocityAmbient_six_square_moment_le hsol hbox hab hc hρ hρone hB hBK)

/-- A genuinely finite original endpoint moment makes the actual weighted mixed cost finite. -/
theorem fullBallTimeWeightedProjectedSixMoment_lt_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hθ : Continuous θ) (hθb : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1)
    (hX : (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
      (volume.restrict (vec3Ball 0 1)) ^ (2 : ℝ)) < ∞) :
    fullBallTimeWeightedProjectedSixMoment u D p a b c B φ θ < ∞ :=
  (fullBallTimeWeightedProjectedSixMoment_le_source
    hsol hbox hab hc hρ hρone hB hBK hφ hb hθ hθb).trans_lt
      (ENNReal.mul_lt_top
        (lt_top_iff_ne_top.mpr (ENNReal.pow_ne_top
          (fullBallProjectedVelocitySliceCoefficient_ne_top ρ))) hX)

/-- Actual suitable data give the genuine sharp time weighted convection source bound. -/
theorem fullBall_timeWeighted_convection_lintegral_le_source
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hθ : Continuous θ) (hθb : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1) :
    (∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
      ENNReal.ofReal (θ z.2) * ENNReal.ofReal (φ z.1) ^ 5 * ‖u z‖ₑ *
        ‖fullBallProjectedVelocityAmbient u D p a b c z‖ₑ ^ (2 : ℝ)) ≤
      fullBallProjectedVelocitySliceCoefficient ρ ^ (1 / 3 : ℝ) *
        (fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ +
          fullBallTimeWeightedProjectedSixMoment u D p a b c B φ θ) ^ (5 / 6 : ℝ) *
        (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ (2 : ℝ)) ^ (2 / 3 : ℝ) *
            volume (Ioo a b) ^ (1 / 4 : ℝ) := by
  have hB1 : B ⊆ vec3Ball 0 1 :=
    hBK.trans (fullBallCompactInterior_subset_unit hρ hρone)
  have hU := (hsol.toData.aestronglyMeasurable_velocity hbox).mono_measure
    (Measure.restrict_mono (Set.prod_mono hB1 Subset.rfl) le_rfl)
  have hV := (fullBallProjectedVelocityAmbient_joint_memLp_two
    hsol hbox hab hc hρ hρone hBK).1.aestronglyMeasurable
  have hΦ : AEStronglyMeasurable (fun z : ParabolicPoint ↦ φ z.1)
      (volume.restrict (B ×ˢ Ioo a b)) :=
    (hφ.continuous.comp continuous_fst_parabolicPoint).aestronglyMeasurable
  have hΘ : AEStronglyMeasurable (fun z : ParabolicPoint ↦ θ z.2)
      (volume.restrict (B ×ˢ Ioo a b)) :=
    (hθ.comp continuous_snd_parabolicPoint).aestronglyMeasurable
  have hM := fullBallTimeWeightedProjectedEnergySup_lt_top
    hsol hbox hab hc hρ hρone hB hBK hφ hb hθb
  have hE : ∀ᵐ t ∂volume.restrict (Ioo a b),
      (∫⁻ x in B, ‖Real.sqrt (θ t) •
        (φ x ^ 3 • fullBallProjectedVelocityAmbient u D p a b c (x, t))‖ₑ ^ (2 : ℝ)) ≤
          fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ := by
    simpa only [fullBallTimeWeightedProjectedVelocity, fullBallProjectedCutoffVelocity] using
      (fullBallTimeWeightedProjectedVelocity_energy_bound_ae
        (u := u) (D := D) (p := p) (a := a) (b := b) (c := c)
        (B := B) (φ := φ) (θ := θ))
  have hh := time_weighted_fifth_mixedEnergy_convection_lintegral_le
    hU hV hΦ hΘ (fun z ↦ (hb z.1).1) (fun z ↦ hθb z.2) hM hE
  dsimp only at hh
  have hu : (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
      (volume.restrict B) ^ (2 : ℝ)) ≤
      ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
        (volume.restrict (vec3Ball 0 1)) ^ (2 : ℝ) :=
    lintegral_mono fun t ↦ ENNReal.rpow_le_rpow
      (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hB1)) (by norm_num)
  have hv := fullBallProjectedVelocityAmbient_six_square_moment_le
    hsol hbox hab hc hρ hρone hB hBK
  have hv' : (∫⁻ t in Ioo a b, eLpNorm
      (fun x ↦ fullBallProjectedVelocityAmbient u D p a b c (x, t)) 6
      (volume.restrict B) ^ (2 : ℝ)) ≤ fullBallProjectedVelocitySliceCoefficient ρ ^ 2 *
        ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ (2 : ℝ) := by
    simpa only [ENNReal.rpow_ofNat] using hv
  apply hh.trans
  simpa only [fullBallTimeWeightedProjectedSixMoment, fullBallTimeWeightedProjectedVelocity,
    fullBallProjectedCutoffVelocity] using endpoint_product_le_source hu hv'

/-- The actual nonnegative convection norm density is integrable with the sharp source bound. -/
theorem fullBall_timeWeighted_convection_density_integrable_and_integral_le_source
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hθ : Continuous θ) (hθb : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1)
    (hX : (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
      (volume.restrict (vec3Ball 0 1)) ^ (2 : ℝ)) < ∞) :
    Integrable (fullBallTimeWeightedConvectionNormDensity u D p a b c φ θ)
      (volume.restrict (B ×ˢ Ioo a b)) ∧
      (∫ z : ParabolicPoint in B ×ˢ Ioo a b,
        fullBallTimeWeightedConvectionNormDensity u D p a b c φ θ z) ≤
      (fullBallProjectedVelocitySliceCoefficient ρ).toReal ^ (1 / 3 : ℝ) *
        (fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ +
          fullBallTimeWeightedProjectedSixMoment u D p a b c B φ θ).toReal ^ (5 / 6 : ℝ) *
        (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ (2 : ℝ)).toReal ^ (2 / 3 : ℝ) *
            (volume (Ioo a b)).toReal ^ (1 / 4 : ℝ) := by
  have hB1 : B ⊆ vec3Ball 0 1 :=
    hBK.trans (fullBallCompactInterior_subset_unit hρ hρone)
  have hU := (hsol.toData.aestronglyMeasurable_velocity hbox).mono_measure
    (Measure.restrict_mono (Set.prod_mono hB1 Subset.rfl) le_rfl)
  have hV := (fullBallProjectedVelocityAmbient_joint_memLp_two
    hsol hbox hab hc hρ hρone hBK).1.aestronglyMeasurable
  have hΦ : AEStronglyMeasurable (fun z : ParabolicPoint ↦ φ z.1)
      (volume.restrict (B ×ˢ Ioo a b)) :=
    (hφ.continuous.comp continuous_fst_parabolicPoint).aestronglyMeasurable
  have hΘ : AEStronglyMeasurable (fun z : ParabolicPoint ↦ θ z.2)
      (volume.restrict (B ×ˢ Ioo a b)) :=
    (hθ.comp continuous_snd_parabolicPoint).aestronglyMeasurable
  have hm : AEStronglyMeasurable (fullBallTimeWeightedConvectionNormDensity u D p a b c φ θ)
      (volume.restrict (B ×ˢ Ioo a b)) :=
    ((hΘ.mul (hΦ.pow 5)).mul hU.norm).mul (hV.norm.pow 2)
  have hM := fullBallTimeWeightedProjectedEnergySup_lt_top
    hsol hbox hab hc hρ hρone hB hBK hφ hb hθb
  have hW := fullBallTimeWeightedProjectedSixMoment_lt_top
    hsol hbox hab hc hρ hρone hB hBK hφ hb hθ hθb hX
  have hJ : volume (Ioo a b) < ∞ :=
    (measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top
  have hfin : fullBallProjectedVelocitySliceCoefficient ρ ^ (1 / 3 : ℝ) *
      (fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ +
        fullBallTimeWeightedProjectedSixMoment u D p a b c B φ θ) ^ (5 / 6 : ℝ) *
      (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
        (volume.restrict (vec3Ball 0 1)) ^ (2 : ℝ)) ^ (2 / 3 : ℝ) *
          volume (Ioo a b) ^ (1 / 4 : ℝ) ≠ ∞ := by
    finiteness [fullBallProjectedVelocitySliceCoefficient_ne_top ρ, hM.ne, hW.ne, hX.ne, hJ.ne]
  have hs := fullBall_timeWeighted_convection_lintegral_le_source
    hsol hbox hab hc hρ hρone hB hBK hφ hb hθ hθb
  have hnorm (z : ParabolicPoint) :
      ‖fullBallTimeWeightedConvectionNormDensity u D p a b c φ θ z‖ₑ =
        ENNReal.ofReal (θ z.2) * ENNReal.ofReal (φ z.1) ^ 5 * ‖u z‖ₑ *
          ‖fullBallProjectedVelocityAmbient u D p a b c z‖ₑ ^ (2 : ℝ) := by
    simp only [fullBallTimeWeightedConvectionNormDensity, enorm_mul, enorm_pow, enorm_norm,
      Real.enorm_of_nonneg (hb z.1).1, Real.enorm_of_nonneg (hθb z.2).1, ENNReal.rpow_ofNat]
  have hi : Integrable (fullBallTimeWeightedConvectionNormDensity u D p a b c φ θ)
      (volume.restrict (B ×ˢ Ioo a b)) := by
    apply memLp_one_iff_integrable.mp
    rw [memLp_iff, eLpNorm_one_eq_lintegral_enorm hm]
    simpa only [hnorm] using hs.trans_lt (lt_top_iff_ne_top.mpr hfin)
  refine ⟨hi, ?_⟩
  have hr := ENNReal.toReal_mono hfin hs
  have heq : (∫ z : ParabolicPoint in B ×ˢ Ioo a b,
      fullBallTimeWeightedConvectionNormDensity u D p a b c φ θ z) =
      (∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
        ENNReal.ofReal (θ z.2) * ENNReal.ofReal (φ z.1) ^ 5 * ‖u z‖ₑ *
          ‖fullBallProjectedVelocityAmbient u D p a b c z‖ₑ ^ (2 : ℝ)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun z ↦ by
        dsimp only [fullBallTimeWeightedConvectionNormDensity]
        positivity [(hb z.1).1, (hθb z.2).1]) hm]
    congr 1
    apply lintegral_congr
    intro z
    rw [← hnorm, Real.enorm_of_nonneg (by
      dsimp only [fullBallTimeWeightedConvectionNormDensity]
      positivity [(hb z.1).1, (hθb z.2).1])]
  rw [heq]
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] using hr

/-- The literal suitable convection flux is integrable and has the true tested energy bound. -/
theorem fullBall_timeWeighted_convection_flux_integrable_and_abs_integral_le_source
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    (hθ : Continuous θ) (hθb : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1)
    (hX : (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
      (volume.restrict (vec3Ball 0 1)) ^ (2 : ℝ)) < ∞) :
    Integrable (fullBallTimeWeightedConvectionFlux u D p a b c φ θ)
      (volume.restrict (B ×ˢ Ioo a b)) ∧
      |∫ z : ParabolicPoint in B ×ˢ Ioo a b,
        fullBallTimeWeightedConvectionFlux u D p a b c φ θ z| ≤
      162 * L * ((fullBallProjectedVelocitySliceCoefficient ρ).toReal ^ (1 / 3 : ℝ) *
        (fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ +
          fullBallTimeWeightedProjectedSixMoment u D p a b c B φ θ).toReal ^ (5 / 6 : ℝ) *
        (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ (2 : ℝ)).toReal ^ (2 / 3 : ℝ) *
            (volume (Ioo a b)).toReal ^ (1 / 4 : ℝ)) := by
  obtain ⟨hN, hNb⟩ := fullBall_timeWeighted_convection_density_integrable_and_integral_le_source
    hsol hbox hab hc hρ hρone hB hBK hφ hb hθ hθb hX
  have hB1 : B ⊆ vec3Ball 0 1 :=
    hBK.trans (fullBallCompactInterior_subset_unit hρ hρone)
  have hU := (hsol.toData.aestronglyMeasurable_velocity hbox).mono_measure
    (Measure.restrict_mono (Set.prod_mono hB1 Subset.rfl) le_rfl)
  have hV := (fullBallProjectedVelocityAmbient_joint_memLp_two
    hsol hbox hab hc hρ hρone hBK).1.aestronglyMeasurable
  have hΘ : AEStronglyMeasurable (fun z : ParabolicPoint ↦ θ z.2)
      (volume.restrict (B ×ˢ Ioo a b)) :=
    (hθ.comp continuous_snd_parabolicPoint).aestronglyMeasurable
  have hgradφ (j : Fin 3) : Continuous
      (fun z : ParabolicPoint ↦ spatialDeriv (fun x ↦ φ x ^ (6 : ℕ)) j z.1) :=
    (contDiff_spatialDeriv_smooth (hφ.pow 6) j).continuous.comp continuous_fst_parabolicPoint
  have hsum : AEStronglyMeasurable
      (fun z : ParabolicPoint ↦ ∑ j : Fin 3, u z j *
        spatialDeriv (fun x ↦ φ x ^ (6 : ℕ)) j z.1) (volume.restrict (B ×ˢ Ioo a b)) :=
    Finset.aestronglyMeasurable_fun_sum _ fun j _ ↦
      ((continuous_apply j).comp_aestronglyMeasurable hU).mul (hgradφ j).aestronglyMeasurable
  have hm : AEStronglyMeasurable (fullBallTimeWeightedConvectionFlux u D p a b c φ θ)
      (volume.restrict (B ×ˢ Ioo a b)) :=
    (hΘ.mul ((CKN.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hV).pow 2)).mul hsum
  have hpoint (z : ParabolicPoint) :
      |fullBallTimeWeightedConvectionFlux u D p a b c φ θ z| ≤
        162 * L * fullBallTimeWeightedConvectionNormDensity u D p a b c φ θ z :=
    fullBallTimeWeightedConvectionFlux_abs_le u D p a b c hφ
      (fun x ↦ (hb x).1) (fun t ↦ (hθb t).1) hL hgrad z
  have hDom := hN.const_mul (162 * L)
  have hflux : Integrable (fullBallTimeWeightedConvectionFlux u D p a b c φ θ)
      (volume.restrict (B ×ˢ Ioo a b)) :=
    hDom.mono' hm (ae_of_all _ fun z ↦ by simpa only [Real.norm_eq_abs] using hpoint z)
  refine ⟨hflux, ?_⟩
  calc
    _ ≤ ∫ z : ParabolicPoint in B ×ˢ Ioo a b,
        |fullBallTimeWeightedConvectionFlux u D p a b c φ θ z| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z : ParabolicPoint in B ×ˢ Ioo a b,
        162 * L * fullBallTimeWeightedConvectionNormDensity u D p a b c φ θ z :=
      integral_mono hflux.abs hDom hpoint
    _ = 162 * L * ∫ z : ParabolicPoint in B ×ˢ Ioo a b,
        fullBallTimeWeightedConvectionNormDensity u D p a b c φ θ z := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hNb (by positivity)

end Suitable

end FluidSingularSets
