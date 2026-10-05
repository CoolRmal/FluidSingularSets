-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallSuitableSmoothApprox

/-!
# Genuine projected local energy on arbitrary compact interior balls

The actual force primitive and genuine harmonic spatial kernels supply smooth
tests on every compact ball strictly inside the projection ball. Strong limits
of all literal monomials give the projected local energy inequality on the
original time interval, with no enlarged future interval or assumed cancellation.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

local instance fullBallEnergyForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance fullBallEnergyForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

variable (ρ σ θ : ℝ) (hρ : 0 < ρ) (hρσ : ρ < σ) (hσθ : σ < θ) (hθ : θ < 1)

/-- The literal jointly smooth gradient of the negative actual force approximants. -/
def fullBallJointApproxGradient (fs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1))
    (n : ℕ) : Vec3 × ℝ → Vec3 :=
  fullBallJointSmoothGradient σ θ (hρ.trans hρσ) hσθ hθ
    (fullBallSuitableSmoothRadius_pos hρσ n) (fun t ↦ -fs n t)

/-- The literal jointly smooth Hessian in velocity-component/derivative order. -/
def fullBallJointApproxDerivative (fs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1))
    (n : ℕ) : Vec3 × ℝ → Fin 3 → Vec3 :=
  fullBallJointSmoothHessian σ θ (hρ.trans hρσ) hσθ hθ
    (fullBallSuitableSmoothRadius_pos hρσ n) (fun t ↦ -fs n t)

/-- The literal pressure of the negative derivative-force approximants. -/
def fullBallJointApproxPressure (gs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1))
    (n : ℕ) : Vec3 × ℝ → ℝ :=
  fullBallJointSmoothPressure σ θ (hρ.trans hρσ) hσθ hθ
    (fullBallSuitableSmoothRadius_pos hρσ n) (fun t ↦ -gs n t)

/-- Actual compact operator convergence gives true uniform field and Hessian errors. -/
theorem fullBall_uniform_approximations_localBox
    {Ω : Set Vec3} {I : Set ℝ} {q a b c : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    {fs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1)}
    (hfs : ∀ n, ContDiff ℝ ∞ (fs n))
    (hforce : TendstoUniformly fs (localBoxForcePrimitive u D p a b c) atTop) :
    ∃ CH CB : ℕ → ℝ,
      (∀ n, 0 ≤ CH n) ∧ Tendsto CH atTop (𝓝 0) ∧
      (∀ n, 0 ≤ CB n) ∧ Tendsto CB atTop (𝓝 0) ∧
      (∀ n t, t ∈ Icc a b → ∀ x : fullBallCompactInterior ρ,
        ‖fullBallJointApproxGradient ρ σ θ hρ hρσ hσθ hθ fs n (x.1, t) -
          fullBallProjectedHarmonicGradientAmbient u D p a b c (x.1, t)‖ ≤ CH n) ∧
      (∀ n t, t ∈ Icc a b → ∀ x : fullBallCompactInterior ρ, ∀ i j,
        ‖fullBallJointApproxDerivative ρ σ θ hρ hρσ hσθ hθ fs n (x.1, t) i j -
          fullBallProjectedHarmonicDerivativeAmbient u D p a b c (x.1, t) i j‖ ≤ CB n) ∧
      (∀ n, MemLp (fun z : fullBallCompactInterior ρ × ℝ ↦
        fullBallJointApproxGradient ρ σ θ hρ hρσ hσθ hθ fs n (z.1.1, z.2)) ⊤
          ((fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b)))) ∧
      (∀ n i j, MemLp (fun z : fullBallCompactInterior ρ × ℝ ↦
        fullBallJointApproxDerivative ρ σ θ hρ hρσ hσθ hθ fs n (z.1.1, z.2) i j) ⊤
          ((fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b)))) := by
  let T := Icc a b
  let M := localBoxForcePrimitive u D p a b c
  obtain ⟨_, hg⟩ := suitable_unitBall_momentumForces_integrable_localBox hsol hbox
  have hM : Continuous M := averagedTimePrimitive_continuous hg
  have hn : TendstoUniformly (fun n (t : T) ↦ -fs n t.1) (fun t ↦ -M t.1) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hforce ε hε] with n hn t
    simpa only [dist_neg_neg] using hn t.1
  have hHu := fullBallSmoothCompactGradient_tendstoUniformly ρ σ θ hρ hρσ hσθ hθ
    (fullBallSuitableSmoothRadius_tendsto ρ σ) (fullBallSuitableSmoothRadius_pos hρσ)
    (fullBallSuitableSmoothRadius_le_six hρσ) (hM.comp continuous_subtype_val).neg hn
  have hBu := fullBallSmoothCompactHessian_tendstoUniformly ρ σ θ hρ hρσ hσθ hθ
    (fullBallSuitableSmoothRadius_tendsto ρ σ) (fullBallSuitableSmoothRadius_pos hρσ)
    (fullBallSuitableSmoothRadius_le_six hρσ) (hM.comp continuous_subtype_val).neg hn
  obtain ⟨CH, hCH, hCHzero, hCHbound⟩ := exists_uniform_error_sequence
    ((fullBallCompactGradientOperator ρ σ hρ hρσ (hσθ.trans hθ)).continuous.comp
      (hM.comp continuous_subtype_val).neg)
    (fun n ↦ (fullBallSmoothCompactGradient ρ σ θ hρ hρσ hσθ hθ
      (fullBallSuitableSmoothRadius_pos hρσ n)
      (fullBallSuitableSmoothRadius_le_six hρσ n)).continuous.comp
        ((hfs n).continuous.comp continuous_subtype_val).neg) hHu
  obtain ⟨CB, hCB, hCBzero, hCBbound⟩ := exists_uniform_error_sequence
    ((fullBallCompactHessianOperator ρ σ hρ hρσ (hσθ.trans hθ)).continuous.comp
      (hM.comp continuous_subtype_val).neg)
    (fun n ↦ (fullBallSmoothCompactHessian ρ σ θ hρ hρσ hσθ hθ
      (fullBallSuitableSmoothRadius_pos hρσ n)
      (fullBallSuitableSmoothRadius_le_six hρσ n)).continuous.comp
        ((hfs n).continuous.comp continuous_subtype_val).neg) hBu
  have hbH (n : ℕ) (t : ℝ) (ht : t ∈ T) (x : fullBallCompactInterior ρ) :
      ‖fullBallJointApproxGradient ρ σ θ hρ hρσ hσθ hθ fs n (x.1, t) -
        fullBallProjectedHarmonicGradientAmbient u D p a b c (x.1, t)‖ ≤ CH n := by
    exact ((fullBallSmoothCompactGradient ρ σ θ hρ hρσ hσθ hθ
      (fullBallSuitableSmoothRadius_pos hρσ n)
      (fullBallSuitableSmoothRadius_le_six hρσ n) (-fs n t) -
      fullBallCompactGradientOperator ρ σ hρ hρσ (hσθ.trans hθ) (-M t)).norm_coe_le_norm x).trans
        (hCHbound n ⟨t, ht⟩)
  have hbB (n : ℕ) (t : ℝ) (ht : t ∈ T) (x : fullBallCompactInterior ρ) (i j : Fin 3) :
      ‖fullBallJointApproxDerivative ρ σ θ hρ hρσ hσθ hθ fs n (x.1, t) i j -
        fullBallProjectedHarmonicDerivativeAmbient u D p a b c (x.1, t) i j‖ ≤ CB n := by
    exact ((PiLp.norm_apply_le _ (j, i)).trans
      ((fullBallSmoothCompactHessian ρ σ θ hρ hρσ hσθ hθ
        (fullBallSuitableSmoothRadius_pos hρσ n)
        (fullBallSuitableSmoothRadius_le_six hρσ n) (-fs n t) -
        fullBallCompactHessianOperator ρ σ hρ hρσ (hσθ.trans hθ) (-M t)).norm_coe_le_norm x)).trans
          (hCBbound n ⟨t, ht⟩)
  have htime : ∀ᵐ z : fullBallCompactInterior ρ × ℝ
      ∂(fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b)), z.2 ∈ Ioo a b :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Ioo)).mpr
      (ae_of_all _ fun _ ↦ ae_restrict_mem measurableSet_Ioo)
  obtain ⟨hHtop, hBtop⟩ := fullBallProjected_correction_joint_memLp_top
    hsol hbox hab hc hρ (hρσ.trans (hσθ.trans hθ))
  refine ⟨CH, CB, hCH, hCHzero, hCB, hCBzero, hbH, hbB, ?_, ?_⟩
  · intro n
    have hcont := (fullBallJointSmoothGradient_contDiff σ θ (hρ.trans hρσ) hσθ hθ
      (fullBallSuitableSmoothRadius_pos hρσ n) (hfs n).neg).continuous
    apply memLp_top_of_uniform_difference hHtop
      (hcont.comp ((continuous_subtype_val.comp continuous_fst).prodMk
        continuous_snd)).aestronglyMeasurable
    exact htime.mono fun z hz ↦ hbH n z.2 (Ioo_subset_Icc_self hz) z.1
  · intro n i j
    have hcont := (fullBallJointSmoothHessian_contDiff σ θ (hρ.trans hρσ) hσθ hθ
      (fullBallSuitableSmoothRadius_pos hρσ n) (hfs n).neg).continuous
    have hcij : Continuous (fun z : fullBallCompactInterior ρ × ℝ ↦
        fullBallJointApproxDerivative ρ σ θ hρ hρσ hσθ hθ fs n (z.1.1, z.2) i j) :=
      ((continuous_apply j).comp ((continuous_apply i).comp hcont)).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    apply memLp_top_of_uniform_difference (hBtop i j) hcij.aestronglyMeasurable
    exact htime.mono fun z hz ↦ hbB n z.2 (Ioo_subset_Icc_self hz) z.1 i j

/-- Actual pressure smoothing converges in the literal mixed spatial L²/time L¹ class. -/
theorem fullBall_pressure_sliceStrong_localBox
    {Ω : Set Vec3} {I : Set ℝ} {q a b : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    {gs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1)}
    (hgs : ∀ n, MemLp (gs n) 1 volume)
    (hconv : Tendsto (fun n ↦ eLpNorm
      ((Ioo a b).indicator (unitBallMomentumForceCurve u D p) - gs n)
      1 volume) atTop (𝓝 0)) :
    ProjectedEnergySliceStrong (fullBallInteriorMeasure ρ) (volume.restrict (Ioo a b)) 1
      (fun z : fullBallCompactInterior ρ × ℝ ↦ fullBallProjectedPressureCompact u D p
        hρ (hρσ.trans (hσθ.trans hθ)) z.2 z.1)
      (fun n z ↦ fullBallJointApproxPressure ρ σ θ hρ hρσ hσθ hθ gs n (z.1.1, z.2)) := by
  let J := Ioo a b
  let g := unitBallMomentumForceCurve u D p
  let L := fullBallCompactValueOperator ρ σ hρ hρσ (hσθ.trans hθ)
  let Ls (n : ℕ) := fullBallSmoothCompactValue ρ σ θ hρ hρσ hσθ hθ
    (fullBallSuitableSmoothRadius_pos hρσ n) (fullBallSuitableSmoothRadius_le_six hρσ n)
  let F (t : ℝ) := L (-g t)
  let Fs (n : ℕ) (t : ℝ) := Ls n (-gs n t)
  obtain ⟨_, hg⟩ := suitable_unitBall_momentumForces_integrable_localBox hsol hbox
  have hg₀ : MemLp (J.indicator g) 1 volume :=
    memLp_one_iff_integrable.mpr (hg.integrable_indicator measurableSet_Ioo)
  have hneg : Tendsto (fun n ↦ eLpNorm
      ((fun t ↦ -gs n t) - fun t ↦ -(J.indicator g t)) 1 volume) atTop (𝓝 0) := by
    convert hconv using 1
    funext n
    congr 1
    funext t
    simp only [Pi.sub_apply]
    abel
  have hglobal := fullBallSmoothCompactValue_strong_one ρ σ θ hρ hρσ hσθ hθ
    (fullBallSuitableSmoothRadius_tendsto ρ σ) (fullBallSuitableSmoothRadius_pos hρσ)
    (fullBallSuitableSmoothRadius_le_six hρσ) hg₀.neg (fun n ↦ (hgs n).neg) hneg
  have hlocal : Tendsto (fun n ↦ eLpNorm (Fs n - F) 1 (volume.restrict J)) atTop (𝓝 0) := by
    have hrestr : Tendsto (fun n ↦ eLpNorm (fun t ↦ Fs n t - L (-(J.indicator g t)))
        1 (volume.restrict J)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglobal
        (fun _ ↦ zero_le) (fun _ ↦ eLpNorm_mono_measure _ Measure.restrict_le_self)
    convert hrestr using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [Fs, F, Pi.sub_apply, J, indicator_of_mem ht]
  have hF : MemLp F 1 (volume.restrict J) :=
    (memLp_one_iff_integrable.mpr hg).neg.continuousLinearMap_comp L
  have hFs (n : ℕ) : MemLp (Fs n) 1 (volume.restrict J) :=
    ((hgs n).mono_measure Measure.restrict_le_self).neg.continuousLinearMap_comp (Ls n)
  exact projectedEnergySliceStrong_one_continuousMap
    (μ := fullBallInteriorMeasure ρ) hF hFs hlocal

/-- The literal projected energy density on an arbitrary compact interior. -/
def fullBallProjectedLocalEnergyDensity
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 × ℝ → ℝ)
    (z : fullBallCompactInterior ρ × ℝ) : ℝ :=
  projectedEnergyDeficitPolynomial (u (z.1.1, z.2))
    (fullBallProjectedHarmonicGradientAmbient u D p a b c (z.1.1, z.2))
    (fun j ↦ spatialPartial ψ j (z.1.1, z.2)) (D (z.1.1, z.2))
    (fullBallProjectedHarmonicDerivativeAmbient u D p a b c (z.1.1, z.2))
    (p (z.1.1, z.2) - unitBallFullHarmonicForcePressureRepresentative
      (unitBallGradientFreeForceProjection (-unitBallMomentumForceCurve u D p z.2)) z.1.1)
    (ψ (z.1.1, z.2)) (timePartial ψ (z.1.1, z.2))
    (∑ j, spatialSecondPartial ψ j j (z.1.1, z.2))

omit σ θ hρσ hσθ hθ in
/-- Actual suitability supplies projected local energy on every genuine compact
interior ball and on the original time interval. -/
theorem suitable_fullBall_projected_local_energy_localBox
    {Ω : Set Vec3} {I : Set ℝ} {q a b c : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hρ : 0 < ρ) (hρone : ρ < 1)
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hnψ : ∀ z, 0 ≤ ψ z)
    (hsupp : tsupport ψ ⊆ fullBallCompactInterior ρ ×ˢ Ioo a b) :
    Integrable (fullBallProjectedLocalEnergyDensity ρ u Du p a b c ψ)
      ((fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))) ∧
      (∫ z, fullBallProjectedLocalEnergyDensity ρ u Du p a b c ψ z
        ∂(fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo a b))) ≤ 0 := by
  let J := Ioo a b
  let T := Icc a b
  let μ := fullBallInteriorMeasure ρ
  let ν := volume.restrict J
  let σ := (2 * ρ + 1) / 3
  let θ := (ρ + 2) / 3
  have hρσ : ρ < σ := by dsimp [σ]; linarith
  have hσθ : σ < θ := by dsimp [σ, θ]; linarith
  have hθ : θ < 1 := by dsimp [θ]; linarith
  let U : fullBallCompactInterior ρ × ℝ → Vec3 := fun z ↦ u (z.1.1, z.2)
  let D : fullBallCompactInterior ρ × ℝ → Fin 3 → Vec3 := fun z ↦ Du (z.1.1, z.2)
  let P : fullBallCompactInterior ρ × ℝ → ℝ := fun z ↦ p (z.1.1, z.2)
  let H : fullBallCompactInterior ρ × ℝ → Vec3 := fun z ↦
    fullBallProjectedHarmonicGradientAmbient u Du p a b c (z.1.1, z.2)
  let B : fullBallCompactInterior ρ × ℝ → Fin 3 → Vec3 := fun z ↦
    fullBallProjectedHarmonicDerivativeAmbient u Du p a b c (z.1.1, z.2)
  let Q : fullBallCompactInterior ρ × ℝ → ℝ := fun z ↦
    fullBallProjectedPressureCompact u Du p hρ hρone z.2 z.1
  let G : fullBallCompactInterior ρ × ℝ → Vec3 :=
    fun z j ↦ spatialPartial ψ j (z.1.1, z.2)
  let Ψ : fullBallCompactInterior ρ × ℝ → ℝ := fun z ↦ ψ (z.1.1, z.2)
  let τ : fullBallCompactInterior ρ × ℝ → ℝ := fun z ↦ timePartial ψ (z.1.1, z.2)
  let Λ : fullBallCompactInterior ρ × ℝ → ℝ :=
    fun z ↦ ∑ j, spatialSecondPartial ψ j j (z.1.1, z.2)
  obtain ⟨gs, fs, hsm, _hAE, hconv, hforce, _hbound, hjoint, _hfield, _hHess, _hpressure⟩ :=
    exists_suitable_fullBall_joint_smooth_sequence_localBox hsol hbox hab hc hρ hρσ hσθ hθ
  let Hs : ℕ → fullBallCompactInterior ρ × ℝ → Vec3 :=
    fun n z ↦ fullBallJointApproxGradient ρ σ θ hρ hρσ hσθ hθ fs n (z.1.1, z.2)
  let Bs : ℕ → fullBallCompactInterior ρ × ℝ → Fin 3 → Vec3 :=
    fun n z ↦ fullBallJointApproxDerivative ρ σ θ hρ hρσ hσθ hθ fs n (z.1.1, z.2)
  let Qs : ℕ → fullBallCompactInterior ρ × ℝ → ℝ :=
    fun n z ↦ fullBallJointApproxPressure ρ σ θ hρ hρσ hσθ hθ gs n (z.1.1, z.2)
  obtain ⟨CH, CB, hCH, hCHzero, hCB, hCBzero, hHb, hBb, hHs, hBs⟩ :=
    fullBall_uniform_approximations_localBox ρ σ θ hρ hρσ hσθ hθ hsol hbox hab hc
      (fun n ↦ (hsm n).2.1) hforce
  obtain ⟨hU, hD, hP⟩ := fullBallProjected_memLp hsol hbox hab hρ hρone
  obtain ⟨hHraw, hBraw⟩ := fullBallProjected_correction_joint_memLp_top
    hsol hbox hab hc hρ hρone
  have hH : MemLp H ⊤ (μ.prod ν) := hHraw
  have hB (i j : Fin 3) : MemLp (fun z ↦ B z i j) ⊤ (μ.prod ν) := hBraw i j
  have ht : ∀ᵐ z : fullBallCompactInterior ρ × ℝ ∂μ.prod ν, z.2 ∈ J :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Ioo)).mpr
      (ae_of_all _ fun _ ↦ ae_restrict_mem measurableSet_Ioo)
  have hHbAE (n : ℕ) : ∀ᵐ z ∂μ.prod ν, ‖Hs n z - H z‖ ≤ CH n :=
    ht.mono fun z hz ↦ hHb n z.2 (Ioo_subset_Icc_self hz) z.1
  have hBbAE (n : ℕ) (i j : Fin 3) :
      ∀ᵐ z ∂μ.prod ν, ‖Bs n z i j - B z i j‖ ≤ CB n :=
    ht.mono fun z hz ↦ hBb n z.2 (Ioo_subset_Icc_self hz) z.1 i j
  have hV (i : Fin 3) : MemLp (fun z ↦ U z i + H z i) 3 (μ.prod ν) :=
    (memLp_pi_iff.mp hU i).add ((memLp_pi_iff.mp hH i).mono_exponent le_top)
  have hVs (n : ℕ) (i : Fin 3) : MemLp (fun z ↦ U z i + Hs n z i) 3 (μ.prod ν) :=
    (memLp_pi_iff.mp hU i).add ((memLp_pi_iff.mp (hHs n) i).mono_exponent le_top)
  have hW (i j : Fin 3) : MemLp (fun z ↦ D z i j + B z i j) 2 (μ.prod ν) :=
    (memLp_pi_iff.mp (memLp_pi_iff.mp hD i) j).add ((hB i j).mono_exponent le_top)
  have hWs (n : ℕ) (i j : Fin 3) :
      MemLp (fun z ↦ D z i j + Bs n z i j) 2 (μ.prod ν) :=
    (memLp_pi_iff.mp (memLp_pi_iff.mp hD i) j).add ((hBs n i j).mono_exponent le_top)
  have hVc (i : Fin 3) : Tendsto (fun n ↦ eLpNorm
      (fun z ↦ (U z i + Hs n z i) - (U z i + H z i)) 3 (μ.prod ν)) atTop (𝓝 0) := by
    have hc := tendsto_eLpNorm_sub_of_uniform_bound (p := 3) (by norm_num) (by norm_num)
      (memLp_pi_iff.mp hH i).aestronglyMeasurable
      (fun n ↦ (memLp_pi_iff.mp (hHs n) i).aestronglyMeasurable) hCH hCHzero
      (fun n ↦ (hHbAE n).mono fun z hz ↦ (norm_le_pi_norm (Hs n z - H z) i).trans hz)
    convert hc using 1
    funext n
    congr 1
    ext z
    simp only [Pi.sub_apply]
    ring
  have hWc (i j : Fin 3) : Tendsto (fun n ↦ eLpNorm
      (fun z ↦ (D z i j + Bs n z i j) - (D z i j + B z i j)) 2 (μ.prod ν))
      atTop (𝓝 0) := by
    have hc := tendsto_eLpNorm_sub_of_uniform_bound (p := 2) (by norm_num) (by norm_num)
      (hB i j).aestronglyMeasurable (fun n ↦ (hBs n i j).aestronglyMeasurable)
      hCB hCBzero (fun n ↦ hBbAE n i j)
    convert hc using 1
    funext n
    congr 1
    ext z
    simp only [Pi.sub_apply]
    ring
  have hBc (i j : Fin 3) : Tendsto (fun n ↦ eLpNorm
      (fun z ↦ Bs n z i j - B z i j) ⊤ (μ.prod ν)) atTop (𝓝 0) :=
    tendsto_eLpNorm_top_sub_of_uniform_bound (hB i j).aestronglyMeasurable
      (fun n ↦ (hBs n i j).aestronglyMeasurable) hCBzero (fun n ↦ hBbAE n i j)
  have hGcont : Continuous (fun z : Vec3 × ℝ ↦ fun j ↦ spatialPartial ψ j z) :=
    continuous_pi fun j ↦ (spatialPartial_contDiff hψ.1 j).continuous
  let GK : C(fullBallCompactInterior ρ × T, Vec3) :=
    ⟨fun z ↦ G (z.1, z.2.1), hGcont.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))⟩
  have hGb (t : ℝ) (ht : t ∈ T) (x : fullBallCompactInterior ρ) :
      ‖G (x, t)‖ ≤ ‖GK‖ := GK.norm_coe_le_norm (x, ⟨t, ht⟩)
  have hG : MemLp G ⊤ (μ.prod ν) := MemLp.of_bound
    (hGcont.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      continuous_snd)).aestronglyMeasurable ‖GK‖
    (ht.mono fun z hz ↦ hGb z.2 (Ioo_subset_Icc_self hz) z.1)
  have hΨ : MemLp Ψ ⊤ (μ.prod ν) := by
    obtain ⟨C, hC⟩ := exists_bound_of_mem_spaceTimeTestFunction hψ
    exact MemLp.of_bound
      (hψ.1.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk
        continuous_snd)).aestronglyMeasurable C (ae_of_all _ fun z ↦ hC (z.1.1, z.2))
  have hτ : MemLp τ ⊤ (μ.prod ν) := by
    obtain ⟨C, hC⟩ := exists_bound_timePartial_of_mem_spaceTimeTestFunction hψ
    exact MemLp.of_bound
      ((contDiff_timePartial hψ.1).continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).aestronglyMeasurable
      C (ae_of_all _ fun z ↦ hC (z.1.1, z.2))
  have hΛ : MemLp Λ ⊤ (μ.prod ν) := by
    apply memLp_finsetSum
    intro i _
    obtain ⟨C, hC⟩ := exists_bound_spatialSecondPartial_of_mem_spaceTimeTestFunction hψ i i
    exact MemLp.of_bound
      ((spatialPartial_contDiff (spatialPartial_contDiff hψ.1 i) i).continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).aestronglyMeasurable
      C (ae_of_all _ fun z ↦ hC (z.1.1, z.2))
  obtain ⟨hUslices, hUclass⟩ := fullBallProjected_velocity_slice_data hsol hbox hab hρ hρone
  obtain ⟨hHslices, hHclass⟩ := actualSliceLp_memLp_top_of_joint_memLp_top hH
  have hVslice := actual_velocity_slice_data_add hUslices hHslices hUclass hHclass
  have hVnslice (n : ℕ) := actual_velocity_slice_data_add hUslices
    (actualSliceLp_memLp_top_of_joint_memLp_top (hHs n)).1 hUclass
    (actualSliceLp_memLp_top_of_joint_memLp_top (hHs n)).2
  have hGN : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, ‖G (x, t)‖ ≤ ‖GK‖ :=
    (ae_restrict_mem measurableSet_Ioo).mono fun t ht ↦
      ae_of_all _ fun x ↦ hGb t (Ioo_subset_Icc_self ht) x
  have hA : ProjectedEnergySliceData μ ν ⊤ (projectedTestedVelocity U H G) :=
    projectedEnergySliceData_top_tested_velocity
      (hU.aestronglyMeasurable.add hH.aestronglyMeasurable) hG.aestronglyMeasurable
      hVslice.1 hVslice.2 hGN
  have hAs (n : ℕ) :
      ProjectedEnergySliceData μ ν ⊤ (projectedTestedVelocity U (Hs n) G) :=
    projectedEnergySliceData_top_tested_velocity
      (hU.aestronglyMeasurable.add (hHs n).aestronglyMeasurable) hG.aestronglyMeasurable
      (hVnslice n).1 (hVnslice n).2 hGN
  have hAzero : Tendsto (fun n ↦ 3 * CH n * ‖GK‖) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (tendsto_const_nhds.mul hCHzero).mul tendsto_const_nhds
  have hAstrong : ProjectedEnergySliceStrong μ ν ⊤
      (projectedTestedVelocity U H G) (fun n ↦ projectedTestedVelocity U (Hs n) G) := by
    apply projectedEnergySliceStrong_top_of_uniform_bound hA hAs
      (fun n ↦ mul_nonneg (mul_nonneg (by norm_num) (hCH n)) (norm_nonneg _)) hAzero
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    apply ae_of_all
    intro x
    apply (projectedTestedVelocity_sub_norm_le (U (x, t)) (H (x, t))
      (Hs n (x, t)) (G (x, t))).trans
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hHb n t (Ioo_subset_Icc_self ht) x) (by norm_num))
      (hGb t (Ioo_subset_Icc_self ht) x) (norm_nonneg _)
      (mul_nonneg (by norm_num) (hCH n))
  have hQ := fullBall_pressure_sliceStrong_localBox ρ σ θ hρ hρσ hσθ hθ hsol hbox
    (fun n ↦ (hsm n).2.2.2.2.1) hconv
  have hLEI : ∀ᶠ n in atTop, (∫ z, projectedEnergyDeficitPolynomial (U z) (Hs n z)
      (G z) (D z) (Bs n z) (P z - Qs n z) (Ψ z) (τ z) (Λ z) ∂μ.prod ν) ≤ 0 := by
    apply Eventually.of_forall
    intro n
    let Hn := fullBallJointApproxGradient ρ σ θ hρ hρσ hσθ hθ fs n
    let Qn := fullBallJointApproxPressure ρ σ θ hρ hρσ hσθ hθ gs n
    let F : Vec3 × ℝ → ℝ := fun z ↦ projectedEnergyDeficitPolynomial (u z) (Hn z)
      (fun j ↦ spatialPartial ψ j z) (Du z)
      (fun i j ↦ spatialPartial (fun w ↦ Hn w i) j z)
      (p z - Qn z) (ψ z) (timePartial ψ z) (∑ j, spatialSecondPartial ψ j j z)
    have hineq := suitable_smooth_projected_local_energy hsol (hjoint n).1 (hjoint n).2.1
      hψ hnψ (fun i z hz ↦ (hjoint n).2.2.2.2 z i (hsupp hz).1)
      (fun z hz ↦ (hjoint n).2.2.2.1 z (hsupp hz).1)
      (fun i z _hz ↦ (hjoint n).2.2.1 z i)
    have heq := integral_fullBallInterior_product_eq_integral ρ (J := J) F (by
      intro z hz
      exact projectedEnergyDeficitPolynomial_zero_off_tsupport u Hn Du
        (fun w i j ↦ spatialPartial (fun v ↦ Hn v i) j w) (fun w ↦ p w - Qn w) ψ z
        (fun h ↦ hz (hsupp h)))
    have hdens : (fun z ↦ projectedEnergyDeficitPolynomial (U z) (Hs n z)
        (G z) (D z) (Bs n z) (P z - Qs n z) (Ψ z) (τ z) (Λ z)) =
          fun z : fullBallCompactInterior ρ × ℝ ↦ F (z.1.1, z.2) := by
      funext z
      congr 1
      funext i j
      exact (fullBallJointSmoothGradient_spatialPartial σ θ (hρ.trans hρσ) hσθ hθ
        (fullBallSuitableSmoothRadius_pos hρσ n) (fun t ↦ -fs n t) (z.1.1, z.2) i j).symm
    rw [hdens, heq]
    exact hineq.2
  exact projectedEnergy_inequality_of_strongLp (memLp_pi_iff.mp hU) hV hW hB hP
    hVs hWs hBs (memLp_pi_iff.mp hG) hΨ hτ hΛ hVc hWc hBc hQ hAstrong hLEI

end FluidSingularSets
