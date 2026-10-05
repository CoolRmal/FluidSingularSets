-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallTimeWeightedEnergy
public import FluidSingularSets.FullBallProjectedSignedErrors

/-!
# Pressure and harmonic errors controlled by the genuine tested energy

The true energy contains the field sqrt(θ) φ³V. The actual pressure test and
harmonic cross terms contain θ φ³V, which is pointwise dominated by that field
for a time cutoff between zero and one. The bounds below retain this actual
time-weighted Euclidean energy instead of replacing it by an unweighted supremum.
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

section LocalBox

variable {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {B : Set Vec3}

/-- The actual pressure cutoff class is controlled by the genuine time-weighted energy. -/
theorem fullBallTimeWeightedPressureCutoffComponent_top_data
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hbθ : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1) (i : Fin 3) :
    ProjectedEnergySliceData (volume.restrict B) (volume.restrict (Ioo a b)) ⊤
      (fullBallProjectedPressureCutoffComponent u D p a b c φ θ i) ∧
    eLpNorm (actualSliceLp (μ := volume.restrict B) (p := 2)
      (fullBallProjectedPressureCutoffComponent u D p a b c φ θ i)) ⊤
        (volume.restrict (Ioo a b)) ≤
      ENNReal.ofReal (6 * L) *
        fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ ^ (1 / 2 : ℝ) := by
  have hθn (t : ℝ) : ‖θ t‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hbθ t).1]
    exact (hbθ t).2
  have hm := (fullBallProjectedPressureCutoffComponent_top_data
    hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hθ hθn i).1.joint
  apply fullBallTimeWeightedProjectedScalar_curve_data
    hsol hbox hab hc hρ hρone hB hBK hφ hb hθ hbθ hm
  exact ae_of_all _ fun t ↦ ae_of_all _ fun x ↦ by
    have heq : fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t) =
        (6 * φ x ^ 2 * spatialDeriv φ i x) *
          (θ t • fullBallProjectedCutoffVelocity u D p a b c φ (x, t)) i := by
      simp only [fullBallProjectedPressureCutoffComponent, spatialDeriv_cutoff_sixth hφ,
        fullBallProjectedCutoffVelocity, Pi.smul_apply, smul_eq_mul]
      ring
    have hg : ‖spatialDeriv φ i x‖ ≤ L :=
      (norm_le_pi_norm (classicalGradient φ x) i).trans (hgrad x)
    have hp : ‖φ x ^ 2‖ ≤ 1 := by
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (hb x).1]
      exact pow_le_one₀ (hb x).1 (hb x).2
    have hcoeff : ‖6 * φ x ^ 2 * spatialDeriv φ i x‖ ≤ 6 * L := by
      simp only [norm_mul, Real.norm_ofNat]
      calc
        _ ≤ 6 * 1 * L := by gcongr
        _ = 6 * L := by ring
    rw [heq, norm_mul]
    exact mul_le_mul hcoeff ((norm_le_pi_norm _ i).trans
      (fullBallTimeWeightedProjectedVelocity_time_smul_norm_le u D p a b c φ hbθ (x, t)))
        (norm_nonneg _) (by positivity)

/-- A genuine time L¹ pressure class pairs with the actual weighted full-ball cutoff test. -/
theorem suitable_fullBall_timeWeighted_pressure_component_one_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1) (i : Fin 3)
    {P : ℝ → Lp ℝ 2 (volume.restrict (vec3Ball 0 1))}
    (hP : MemLp P 1 (volume.restrict (Ioo a b))) :
    Integrable (fun t ↦ ∫ x in B, P t x *
      fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t))
        (volume.restrict (Ioo a b)) ∧
    ‖∫ t in Ioo a b, ∫ x in B, P t x *
      fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t)‖ₑ ≤
        eLpNorm P 1 (volume.restrict (Ioo a b)) * ENNReal.ofReal (6 * L) *
          fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ ^ (1 / 2 : ℝ) := by
  have hB1 := hBK.trans (fullBallCompactInterior_subset_unit hρ hρone)
  have hG := fullBallTimeWeightedPressureCutoffComponent_top_data
    hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hθ hθb i
  have hh := pressureCurve_pairing_restrict_one_top_integrable_and_bound
    (Measure.restrict_mono_set volume hB1) hP hG.1.slices hG.1.classMemLp
  exact ⟨hh.1, hh.2.trans ((mul_le_mul' le_rfl hG.2).trans_eq (by ring))⟩

/-- Actual same-ball suitability supplies the true convective pressure weighted pairing bound. -/
theorem suitable_fullBall_timeWeighted_convective_pressure_component_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1) (i : Fin 3) :
    Integrable (fun t ↦ ∫ x in B, (unitBallConvectivePressureCurve u t).val x *
      fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t))
        (volume.restrict (Ioo a b)) ∧
    ‖∫ t in Ioo a b, ∫ x in B, (unitBallConvectivePressureCurve u t).val x *
      fullBallProjectedPressureCutoffComponent u D p a b c φ θ i (x, t)‖ₑ ≤
      12 * volume (vec3Ball (0 : Vec3) 1) ^ (1 / 6 : ℝ) *
        (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2) * ENNReal.ofReal (6 * L) *
            fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ ^ (1 / 2 : ℝ) := by
  let ν := volume.restrict (Ioo a b)
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ioo])
  have hP : MemLp (unitBallConvectivePressureCurve u) 1 ν :=
    ((suitable_convectiveTensorCurve_memLp_localBox hsol hbox).continuousLinearMap_comp
      unitBallTensorPressureL).mono_exponent (by norm_num)
  have hPv : MemLp (fun t ↦ (unitBallConvectivePressureCurve u t).val) 1 ν :=
    hP.continuousLinearMap_comp unitBallMeanZeroL2.toSubmodule.subtypeL
  have hPeq : eLpNorm (fun t ↦ (unitBallConvectivePressureCurve u t).val) 1 ν =
      eLpNorm (unitBallConvectivePressureCurve u) 1 ν :=
    eLpNorm_congr_norm_ae hPv.aestronglyMeasurable hP.aestronglyMeasurable
      (ae_of_all _ fun _ ↦ rfl)
  have hh := suitable_fullBall_timeWeighted_pressure_component_one_bound
    hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hθ hθb i hPv
  have hu : AEStronglyMeasurable u ((volume.restrict (vec3Ball 0 1)).prod ν) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hsol.toData.aestronglyMeasurable_velocity hbox
  have hpn := unitBallConvectivePressureCurve_eLpNorm_one_le_six_moment hu
    (suitable_fullBall_source_memLp_six_ae hsol hbox)
  rw [hPeq] at hh
  exact ⟨hh.1, hh.2.trans (mul_le_mul' (mul_le_mul' hpn le_rfl) le_rfl)⟩

/-- Bounded time tests preserve the actual weighted corrected class and its weighted energy. -/
theorem fullBallTimeWeightedCutoff_component_time_test_data
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1) (i : Fin 3) :
    ProjectedEnergySliceData (volume.restrict B) (volume.restrict (Ioo a b)) ⊤
      (fun z : ParabolicPoint ↦ θ z.2 * fullBallProjectedCutoffVelocity u D p a b c φ z i) ∧
    eLpNorm (actualSliceLp (μ := volume.restrict B) (p := 2)
      (fun z : ParabolicPoint ↦ θ z.2 * fullBallProjectedCutoffVelocity u D p a b c φ z i)) ⊤
        (volume.restrict (Ioo a b)) ≤
      fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ ^ (1 / 2 : ℝ) := by
  have hW := fullBallProjectedCutoffVelocity_aestronglyMeasurable
    hsol hbox hab hc hρ hρone hBK hφ
  have hm : AEStronglyMeasurable
      (fun z : ParabolicPoint ↦ θ z.2 * fullBallProjectedCutoffVelocity u D p a b c φ z i)
      ((volume.restrict B).prod (volume.restrict (Ioo a b))) :=
    (hθ.comp continuous_snd).aestronglyMeasurable.mul
      ((continuous_apply i).comp_aestronglyMeasurable hW)
  have hd := fullBallTimeWeightedProjectedScalar_curve_data
    hsol hbox hab hc hρ hρone hB hBK hφ hb hθ hθb hm
    (C := 1) (ae_of_all _ fun t ↦ ae_of_all _ fun x ↦ by
      rw [one_mul]
      change ‖(θ t • fullBallProjectedCutoffVelocity u D p a b c φ (x, t)) i‖ ≤ _
      exact (norm_le_pi_norm _ i).trans
        (fullBallTimeWeightedProjectedVelocity_time_smul_norm_le u D p a b c φ hθb (x, t)))
  refine ⟨hd.1, ?_⟩
  simpa only [ENNReal.ofReal_one, one_mul] using hd.2

/-- The true cutoff harmonic component is integrable with its external full-source bound. -/
theorem suitable_fullBall_timeWeighted_harmonic_component_integrable_and_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1) (i j : Fin 3) :
    Integrable (fun z : ParabolicPoint ↦ θ z.2 * φ z.1 ^ 6 * u z j *
      fullBallProjectedHarmonicDerivativeAmbient u D p a b c z i j *
        fullBallProjectedVelocityAmbient u D p a b c z i)
      (volume.restrict (B ×ˢ Ioo a b)) ∧
    ‖∫ z : ParabolicPoint in B ×ˢ Ioo a b,
      θ z.2 * φ z.1 ^ 6 * u z j *
        fullBallProjectedHarmonicDerivativeAmbient u D p a b c z i j *
          fullBallProjectedVelocityAmbient u D p a b c z i‖ₑ ≤
      ENNReal.ofReal (fullBallProjectedHarmonicHessianVelocityConstant ρ) *
        eLpNorm (unitBallVelocityCurve u) 2
          (volume.restrict (Ioo a b)) ^ 2 *
            fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ ^ (1 / 2 : ℝ) := by
  let J := Ioo a b
  let F : ParabolicPoint → ℝ := fun z ↦ φ z.1 ^ 3 * u z j *
    fullBallProjectedHarmonicDerivativeAmbient u D p a b c z i j
  let G : ParabolicPoint → ℝ :=
    fun z ↦ θ z.2 * fullBallProjectedCutoffVelocity u D p a b c φ z i
  have hB1 := hBK.trans (fullBallCompactInterior_subset_unit hρ hρone)
  have hU : AEStronglyMeasurable u ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact (hsol.toData.aestronglyMeasurable_velocity
      hbox).mono_measure
        (Measure.restrict_mono_set volume (Set.prod_mono hB1 le_rfl))
  have hDH : AEStronglyMeasurable
      (fun z ↦ fullBallProjectedHarmonicDerivativeAmbient u D p a b c z i j)
      ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    have h0 := (fullBallProjected_correction_ambient_joint_memLp_top
      hsol hbox hab hc hρ hρone).2
    have h1 := h0.mono_measure (Measure.restrict_mono_set volume (Set.prod_mono hBK le_rfl))
    exact ((h1.eval i).eval j).aestronglyMeasurable
  have hF : AEStronglyMeasurable F ((volume.restrict B).prod (volume.restrict J)) :=
    (((hφ.pow 3).continuous.comp continuous_fst).aestronglyMeasurable.mul
      ((continuous_apply j).comp_aestronglyMeasurable hU)).mul hDH
  have hgd := fullBallTimeWeightedCutoff_component_time_test_data
    hsol hbox hab hc hρ hρone hB hBK hφ hb hθ hθb i
  have hUs : ∀ᵐ t ∂volume.restrict J,
      MemLp (fun x ↦ u (x, t) j) 2 (volume.restrict B) := by
    filter_upwards [slice_memLp_ae_of_sws hsol
      hbox] with t ht
    exact (ht.1.mono_measure (Measure.restrict_mono_set volume hB1)).eval j
  have hcap : ∀ᵐ t ∂volume.restrict J,
      ‖actualSliceLp (μ := volume.restrict B) (p := 2) (fun z ↦ u z j) t‖ ≤
        ‖(‖unitBallVelocityCurve u t‖ : ℝ)‖ := by
    simpa only [norm_norm] using
      suitable_fullBall_inner_velocity_component_class_le_full_ae hsol hbox hB1 j
  have hbound : ∀ᵐ t ∂volume.restrict J, ∀ᵐ x ∂volume.restrict B,
      ‖F (x, t)‖ ≤ (fullBallProjectedHarmonicHessianVelocityConstant ρ *
        ‖(‖unitBallVelocityCurve u t‖ : ℝ)‖) * ‖u (x, t) j‖ := by
    filter_upwards [fullBall_projected_harmonic_hessian_velocity_bound_ae
      hsol hbox hab hc hρ hρone] with t ht
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    have hdh := ht ⟨x, hBK hx⟩ i j
    have hφn : ‖φ x ^ 3‖ ≤ 1 := by
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (hb x).1]
      exact pow_le_one₀ (hb x).1 (hb x).2
    calc
      _ = ‖φ x ^ 3‖ * ‖u (x, t) j‖ *
          ‖fullBallProjectedHarmonicDerivativeAmbient u D p a b c (x, t) i j‖ := by
        simp only [F, norm_mul]
      _ ≤ 1 * ‖u (x, t) j‖ *
          (fullBallProjectedHarmonicHessianVelocityConstant ρ * ‖unitBallVelocityCurve u t‖) := by
        gcongr
      _ = _ := by rw [norm_norm]; ring
  have ha := suitable_velocityCurve_memLp_localBox hsol hbox
  have hresult := integrable_product_bound_external_quadratic_source
    ((continuous_apply j).comp_aestronglyMeasurable hU) hF hgd.1.joint hUs ha.norm hcap
    hgd.1.slices hgd.1.classMemLp
      (fullBallProjectedHarmonicHessianVelocityConstant_nonneg hρone) hbound
  have heq : (fun z : ParabolicPoint ↦ θ z.2 * φ z.1 ^ 6 * u z j *
      fullBallProjectedHarmonicDerivativeAmbient u D p a b c z i j *
        fullBallProjectedVelocityAmbient u D p a b c z i) = fun z ↦ F z * G z := by
    funext z
    simp only [F, G, fullBallProjectedCutoffVelocity, Pi.smul_apply, smul_eq_mul]
    ring
  have hm : (volume : Measure ParabolicPoint).restrict (B ×ˢ J) =
      (volume.restrict B).prod (volume.restrict J) := by
    rw [Measure.prod_restrict, volume_parabolicPoint_eq_prod]
  rw [heq, hm]
  refine ⟨hresult.1, ?_⟩
  rw [eLpNorm_norm _ ha.aestronglyMeasurable] at hresult
  exact hresult.2.trans (mul_le_mul' le_rfl hgd.2)

/-- The genuine endpoint moment bounds the literal harmonic cross error at any inner radius. -/
theorem suitable_fullBall_timeWeighted_harmonic_component_endpoint_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1) (i j : Fin 3) :
    ‖∫ z : ParabolicPoint in B ×ˢ Ioo a b,
      θ z.2 * φ z.1 ^ 6 * u z j *
        fullBallProjectedHarmonicDerivativeAmbient u D p a b c z i j *
          fullBallProjectedVelocityAmbient u D p a b c z i‖ₑ ≤
      ENNReal.ofReal (fullBallProjectedHarmonicHessianVelocityConstant ρ) *
        volume (vec3Ball (0 : Vec3) 1) ^ (2 / 3 : ℝ) *
          (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
            (volume.restrict (vec3Ball 0 1)) ^ 2) *
              fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ ^ (1 / 2 : ℝ) := by
  have hbnd := (suitable_fullBall_timeWeighted_harmonic_component_integrable_and_bound
    hsol hbox hab hc hρ hρone hB hBK hφ hb hθ hθb i j).2
  exact hbnd.trans ((mul_le_mul'
    (mul_le_mul' le_rfl (localBox_velocityCurve_two_sq_le_six_moment hsol hbox))
      le_rfl).trans_eq (by ring))

/-- The actual pressure cutoff integral is integrable in time and has its weighted error bound. -/
theorem suitable_fullBall_timeWeighted_pressure_integrable_and_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ B) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1)
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
            fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ ^ (1 / 2 : ℝ)) +
      3 * (ENNReal.ofReal δ *
        (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b, ‖D z‖ₑ ^ (2 : ℝ)) +
          fullBallViscousMixedPairingCoefficient ρ L ^ 2 / (4 * ENNReal.ofReal δ) *
            (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
              (volume.restrict (vec3Ball 0 1)) ^ 2)) := by
  have hθn (t : ℝ) : ‖θ t‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hθb t).1]
    exact (hθb t).2
  have hC (i : Fin 3) := suitable_fullBall_timeWeighted_convective_pressure_component_bound
    hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hθ hθb i
  have hV (i : Fin 3) := suitable_fullBall_viscous_mixed_pairing_bound_localBox
    hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hθ hθn i
  have hVy (i : Fin 3) := suitable_fullBall_viscous_mixed_pairing_young_localBox
    hsol hbox hab hc hρ hρone hB hBK hφ hb hL hgrad hθ hθn i hδ
  have hCs := integral_finite_family_enorm_bound (fun i ↦ (hC i).1) (fun i ↦ (hC i).2)
  have hVs := integral_finite_family_enorm_bound (fun i ↦ (hV i).1) hVy
  have heq := suitable_fullBall_pressure_cutoff_pairing_eq_components_ae
    hsol hbox hab hc hρ hρone hB hBK hφ hcφ hsφ hb hL hgrad hθ hθn
  refine ⟨(hCs.1.add hVs.1).congr (heq.mono fun _ ht ↦ ht.symm), ?_⟩
  rw [integral_congr_ae heq, integral_add hCs.1 hVs.1]
  exact (enorm_add_le _ _).trans (add_le_add hCs.2 hVs.2)

/-- All nine actual harmonic cross components are integrable with their literal summed bound. -/
theorem suitable_fullBall_timeWeighted_harmonic_sum_integrable_and_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1) :
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
              fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ ^ (1 / 2 : ℝ)) := by
  have hI (ij : Fin 3 × Fin 3) :=
    (suitable_fullBall_timeWeighted_harmonic_component_integrable_and_bound
      hsol hbox hab hc hρ hρone hB hBK hφ hb hθ hθb ij.1 ij.2).1
  have hE (ij : Fin 3 × Fin 3) := suitable_fullBall_timeWeighted_harmonic_component_endpoint_bound
    hsol hbox hab hc hρ hρone hB hBK hφ hb hθ hθb ij.1 ij.2
  have hh := integral_finite_family_enorm_bound hI hE
  simpa only [Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_fin,
    Nat.reduceMul, Nat.cast_ofNat] using hh

/-- Literal pressure and harmonic signed errors obey the genuine sum of their proved bounds. -/
theorem suitable_fullBall_timeWeighted_pressure_harmonic_signed_error_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ B) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, 0 ≤ θ t ∧ θ t ≤ 1)
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
            fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ ^ (1 / 2 : ℝ)) +
      6 * (ENNReal.ofReal δ *
        (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b, ‖D z‖ₑ ^ (2 : ℝ)) +
          fullBallViscousMixedPairingCoefficient ρ L ^ 2 / (4 * ENNReal.ofReal δ) *
            (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
              (volume.restrict (vec3Ball 0 1)) ^ 2)) +
      18 * (ENNReal.ofReal (fullBallProjectedHarmonicHessianVelocityConstant ρ) *
        volume (vec3Ball (0 : Vec3) 1) ^ (2 / 3 : ℝ) *
          (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
            (volume.restrict (vec3Ball 0 1)) ^ 2) *
              fullBallTimeWeightedProjectedEnergySup u D p a b c B φ θ ^ (1 / 2 : ℝ)) := by
  have hp := (suitable_fullBall_timeWeighted_pressure_integrable_and_bound
    hsol hbox hab hc hρ hρone hB hBK hφ hcφ hsφ hb hL hgrad hθ hθb hδ).2
  have hh := (suitable_fullBall_timeWeighted_harmonic_sum_integrable_and_bound
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
