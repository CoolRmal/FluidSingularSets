-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallProjectedPressurePairings

/-!
# Actual harmonic cutoff errors with the full projection margin

The genuine Hessian of the actual projected force primitive is controlled by
the original full-ball velocity class. The true quadratic-source pairing then
bounds each literal harmonic cross term by the original endpoint mixed cost
and the weighted corrected slice energy on the original time interval.
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

local instance fullBallHarmonicCutoffForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The true Hessian-to-source coefficient at the intermediate boundary margin. -/
def fullBallProjectedHarmonicHessianVelocityConstant (ρ : ℝ) : ℝ :=
  fullBallHarmonicForceHessianCoefficient ((ρ + 1) / 2) *
    (3 * (stokesTestPoincareConstant (vec3Ball (0 : Vec3) 1)).toReal)

theorem fullBallProjectedHarmonicHessianVelocityConstant_nonneg {ρ : ℝ} (hρone : ρ < 1) :
    0 ≤ fullBallProjectedHarmonicHessianVelocityConstant ρ := by
  unfold fullBallProjectedHarmonicHessianVelocityConstant
  exact mul_nonneg (fullBallHarmonicForceHessianCoefficient_nonneg (by linarith))
    (by positivity)

/-- Original suitable momentum controls every actual harmonic Hessian entry. -/
theorem fullBall_projected_harmonic_hessian_velocity_bound_ae
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ x : fullBallCompactInterior ρ, ∀ i j : Fin 3,
      ‖fullBallProjectedHarmonicDerivativeAmbient u D p a b c (x.1, t) i j‖ ≤
        fullBallProjectedHarmonicHessianVelocityConstant ρ * ‖unitBallVelocityCurve u t‖ := by
  let H := fullBallProjectedHessianOperator hρ hρone
  filter_upwards [suitable_unitBall_velocityForce_ae_primitive_localBox hsol hbox hab hc]
    with t ht
  intro x i j
  change ‖H (-localBoxForcePrimitive u D p a b c t) x (j, i)‖ ≤ _
  rw [← ht]
  have hb := fullBallHarmonicHessianExtended_norm_le (fullBallCompactInterior ρ)
    (fullBallCompactInterior_subset_unit hρ hρone)
    (show (ρ + 1) / 2 < 1 by linarith)
    (fullBallCompactInterior_subset hρ (show ρ < (ρ + 1) / 2 by linarith))
    (-unitBallVelocityForceCurve u t)
  rw [norm_neg] at hb
  exact ((PiLp.norm_apply_le _ (j, i)).trans
    (((H (-unitBallVelocityForceCurve u t)).norm_coe_le_norm x).trans hb)).trans
      ((mul_le_mul_of_nonneg_left (unitBallVelocityForceCurve_norm_le_actual_class u t)
        (fullBallHarmonicForceHessianCoefficient_nonneg (by linarith))).trans_eq
          (by unfold fullBallProjectedHarmonicHessianVelocityConstant; ring))

section LocalBox

variable {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {B : Set Vec3}

/-- The distinct inner scalar source class is bounded by the genuine full-ball source class. -/
theorem suitable_fullBall_inner_velocity_component_class_le_full_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    (hB1 : B ⊆ vec3Ball 0 1) (j : Fin 3) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      ‖actualSliceLp (μ := volume.restrict B) (p := 2) (fun z ↦ u z j) t‖ ≤
        ‖unitBallVelocityCurve u t‖ := by
  filter_upwards [slice_memLp_ae_of_sws hsol hbox] with t ht
  have huB := ht.1.mono_measure (Measure.restrict_mono_set volume hB1)
  have hb : ‖actualSliceLp (μ := volume.restrict B) (p := 2) (fun z ↦ u z j) t‖ₑ ≤
      ‖unitBallVelocityCurve u t‖ₑ := by
    rw [actualSliceLp_enorm (fun z ↦ u z j) t (huB.eval j),
      unitBallVelocityCurve, actualSliceLp_enorm u t ht.1]
    exact (eLpNorm_mono_ae (huB.eval j).aestronglyMeasurable
      (ae_of_all _ fun x ↦ norm_le_pi_norm (u (x, t)) j)).trans
        (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hB1))
  have hreal := ENNReal.toReal_mono (by simp) hb
  simpa only [toReal_enorm] using hreal

/-- Bounded time tests preserve the actual weighted corrected class and its weighted energy. -/
theorem fullBallProjectedCutoff_component_time_test_data
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) (i : Fin 3) :
    ProjectedEnergySliceData (volume.restrict B) (volume.restrict (Ioo a b)) ⊤
      (fun z : ParabolicPoint ↦ θ z.2 * fullBallProjectedCutoffVelocity u D p a b c φ z i) ∧
    eLpNorm (actualSliceLp (μ := volume.restrict B) (p := 2)
      (fun z : ParabolicPoint ↦ θ z.2 * fullBallProjectedCutoffVelocity u D p a b c φ z i)) ⊤
        (volume.restrict (Ioo a b)) ≤
      fullBallProjectedCutoffSliceEnergy u D p a b c B φ ^ (1 / 2 : ℝ) := by
  have hW := fullBallProjectedCutoffVelocity_aestronglyMeasurable
    hsol hbox hab hc hρ hρone hBK hφ
  have hm : AEStronglyMeasurable
      (fun z : ParabolicPoint ↦ θ z.2 * fullBallProjectedCutoffVelocity u D p a b c φ z i)
      ((volume.restrict B).prod (volume.restrict (Ioo a b))) :=
    (hθ.comp continuous_snd).aestronglyMeasurable.mul
      ((continuous_apply i).comp_aestronglyMeasurable hW)
  have hd := fullBallProjectedCutoffScalar_curve_data
    hsol hbox hab hc hρ hρone hB hBK hφ hb hm
    (C := 1) (ae_of_all _ fun t ↦ ae_of_all _ fun x ↦ by
      rw [norm_mul, one_mul]
      exact (mul_le_mul (hθb t) (norm_le_pi_norm _ i)
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  refine ⟨hd.1, ?_⟩
  simpa only [ENNReal.ofReal_one, one_mul] using hd.2

/-- The true cutoff harmonic component is integrable with its external full-source bound. -/
theorem suitable_fullBall_harmonic_cutoff_component_integrable_and_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) (i j : Fin 3) :
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
            fullBallProjectedCutoffSliceEnergy u D p a b c B φ ^ (1 / 2 : ℝ) := by
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
  have hgd := fullBallProjectedCutoff_component_time_test_data
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
theorem suitable_fullBall_harmonic_cutoff_component_endpoint_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1)
    (hB : IsOpen B) (hBK : B ⊆ fullBallCompactInterior ρ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθb : ∀ t, ‖θ t‖ ≤ 1) (i j : Fin 3) :
    ‖∫ z : ParabolicPoint in B ×ˢ Ioo a b,
      θ z.2 * φ z.1 ^ 6 * u z j *
        fullBallProjectedHarmonicDerivativeAmbient u D p a b c z i j *
          fullBallProjectedVelocityAmbient u D p a b c z i‖ₑ ≤
      ENNReal.ofReal (fullBallProjectedHarmonicHessianVelocityConstant ρ) *
        volume (vec3Ball (0 : Vec3) 1) ^ (2 / 3 : ℝ) *
          (∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
            (volume.restrict (vec3Ball 0 1)) ^ 2) *
              fullBallProjectedCutoffSliceEnergy u D p a b c B φ ^ (1 / 2 : ℝ) := by
  have hbnd := (suitable_fullBall_harmonic_cutoff_component_integrable_and_bound
    hsol hbox hab hc hρ hρone hB hBK hφ hb hθ hθb i j).2
  exact hbnd.trans ((mul_le_mul'
    (mul_le_mul' le_rfl (localBox_velocityCurve_two_sq_le_six_moment hsol hbox))
      le_rfl).trans_eq (by ring))

end LocalBox

end FluidSingularSets
