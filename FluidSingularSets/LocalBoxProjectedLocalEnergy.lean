-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.LocalBoxProjectedTime
public import FluidSingularSets.SuitableProjectedLocalEnergy

/-!
# Actual projected local energy on the original interval

The genuine suitable source classes, force primitive, and smooth approximation
are assembled on the supplied local unit ball and time interval. No fixed
future-time or doubled spatial enlargement appears in the theorem.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

local instance localBoxProjectedEnergyForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance localBoxProjectedEnergyForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- Actual suitable data give all three compact-interior joint classes. -/
theorem localBox_harmonicInterior_memLp
    {Ω : Set Vec3} {I : Set ℝ} {q a b : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) :
    MemLp (fun z : unitBallPressureCompactInterior × ℝ ↦ u (z.1.1, z.2)) 3
      (harmonicInteriorMeasure.prod (volume.restrict (Ioo a b))) ∧
      MemLp (fun z : unitBallPressureCompactInterior × ℝ ↦ Du (z.1.1, z.2)) 2
        (harmonicInteriorMeasure.prod (volume.restrict (Ioo a b))) ∧
      MemLp (fun z : unitBallPressureCompactInterior × ℝ ↦ p (z.1.1, z.2))
        (ENNReal.ofReal (3 / 2 : ℝ))
        (harmonicInteriorMeasure.prod (volume.restrict (Ioo a b))) := by
  let J := Ioo a b
  let S : Set ParabolicPoint := unitBallPressureCompactInterior ×ˢ Icc a b
  have hS : IsCompact S := parabolicHomeomorph.isCompact_preimage.mpr
    ((isCompact_closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 16)).prod isCompact_Icc)
  have hSdom : S ⊆ spaceTimeSet Ω I := by
    intro z hz
    refine ⟨hbox.2.2.1 (subset_closure ?_), hbox.2.2.2.2.2 ?_⟩
    · exact vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1)
        (unitBallPressureCompactInterior_subset_eighth hz.1)
    · rw [closure_Ioo hab.ne]
      exact hz.2
  have hu : MemLp u 3 (volume.restrict S) := by
    simpa using velocity_memLp_three_on_compact_of_data hsol.toData hS hSdom
  have hd := gradient_memLp_two_on_compact_of_data hsol.toData hS hSdom
  have hp := pressure_memLp_threeHalves_on_compact_of_data hsol.toData hS hSdom
  have hsub : unitBallPressureCompactInterior ×ˢ J ⊆ S :=
    prod_mono le_rfl Ioo_subset_Icc_self
  have hUP : MemLp (fun z : Vec3 × ℝ ↦ u z) 3
      ((volume.restrict unitBallPressureCompactInterior).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict,
      ← CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    exact hu.mono_measure (Measure.restrict_mono_set volume hsub)
  have hDP : MemLp (fun z : Vec3 × ℝ ↦ Du z) 2
      ((volume.restrict unitBallPressureCompactInterior).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict,
      ← CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    exact hd.mono_measure (Measure.restrict_mono_set volume hsub)
  have hPP : MemLp (fun z : Vec3 × ℝ ↦ p z) (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume.restrict unitBallPressureCompactInterior).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict,
      ← CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    exact hp.mono_measure (Measure.restrict_mono_set volume hsub)
  exact ⟨hUP.comp_measurePreserving (harmonicInterior_product_measurePreserving J),
    hDP.comp_measurePreserving (harmonicInterior_product_measurePreserving J),
    hPP.comp_measurePreserving (harmonicInterior_product_measurePreserving J)⟩

/-- The actual original slice energy gives the compact velocity time class. -/
theorem localBox_harmonicInterior_velocity_slice_data
    {Ω : Set Vec3} {I : Set ℝ} {q a b : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) :
    (∀ᵐ t ∂volume.restrict (Ioo a b),
      MemLp (fun x : unitBallPressureCompactInterior ↦ u (x.1, t)) 2
        harmonicInteriorMeasure) ∧
      MemLp (actualSliceLp (μ := harmonicInteriorMeasure) (p := 2)
        (fun z : unitBallPressureCompactInterior × ℝ ↦ u (z.1.1, z.2))) ⊤
        (volume.restrict (Ioo a b)) := by
  let J := Ioo a b
  have hsub : unitBallPressureCompactInterior ⊆ vec3Ball (0 : Vec3) 1 :=
    fun x hx ↦ vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1)
      (unitBallPressureCompactInterior_subset_eighth hx)
  refine ⟨?_, ?_⟩
  · filter_upwards [slice_memLp_ae_of_sws hsol hbox] with t ht
    exact (ht.1.mono_measure (Measure.restrict_mono_set volume hsub)).comp_measurePreserving
      harmonicInterior_measurePreserving
  · have hmeas := (localBox_harmonicInterior_memLp hsol hbox hab).1.aestronglyMeasurable
    apply actualSliceLp_memLp_top_of_sliceEnergy hmeas
    apply lt_of_le_of_lt _ (hsol.toData.essSup_sliceEnergy_lt_top hbox)
    refine essSup_mono_ae (ae_of_all _ fun t ↦ ?_)
    ·
      let ft : Vec3 → ℝ≥0∞ := fun x ↦ ‖u ((x, t) : ParabolicPoint)‖ₑ ^ (2 : ℝ)
      have hs : MeasurableSet unitBallPressureCompactInterior := isClosed_closure.measurableSet
      have hm : (volume.restrict unitBallPressureCompactInterior).restrict
          unitBallPressureCompactInterior = volume.restrict unitBallPressureCompactInterior := by
        rw [Measure.restrict_restrict hs, inter_self]
      change (∫⁻ x : unitBallPressureCompactInterior, ft x.1
        ∂(volume.restrict unitBallPressureCompactInterior).comap Subtype.val) ≤
          ∫⁻ x in vec3Ball 0 1, ft x
      calc
        _ = ∫⁻ x in unitBallPressureCompactInterior, ft x
            ∂volume.restrict unitBallPressureCompactInterior := lintegral_subtype_comap hs ft
        _ = ∫⁻ x in unitBallPressureCompactInterior, ft x :=
          congrArg (fun ρ : Measure Vec3 ↦ ∫⁻ x, ft x ∂ρ) hm
        _ ≤ _ := lintegral_mono_set hsub

/-- The literal harmonic gradient of the actual original-interval primitive. -/
def localBoxProjectedHarmonicGradient
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) : unitBallPressureCompactInterior × ℝ → Vec3 :=
  fun z ↦ localBoxHarmonicTimePrimitive u Du p a b c z.2 z.1

/-- The genuine harmonic Hessian in velocity-gradient index order. -/
def localBoxProjectedHarmonicDerivative
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) :
    unitBallPressureCompactInterior × ℝ → Fin 3 → Vec3 :=
  fun z i j ↦ harmonicCompactHessianOperator
    (-averagedTimePrimitive (unitBallVelocityForceCurve u)
      (unitBallMomentumForceCurve u Du p) a b c z.2) z.1 (j, i)

/-- The original suitable source controls the true correction and Hessian classes. -/
theorem localBox_harmonicInterior_correction_memLp_top
    {Ω : Set Vec3} {I : Set ℝ} {q a b c : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b) :
    MemLp (localBoxProjectedHarmonicGradient u Du p a b c) ⊤
      (harmonicInteriorMeasure.prod (volume.restrict (Ioo a b))) ∧
      (∀ i j, MemLp (fun z ↦ localBoxProjectedHarmonicDerivative u Du p a b c z i j) ⊤
        (harmonicInteriorMeasure.prod (volume.restrict (Ioo a b)))) := by
  have hM := (suitable_velocityForceCurve_memLp_top hsol hbox).ae_eq
    (suitable_unitBall_velocityForce_ae_primitive_localBox hsol hbox hab hc)
  have hH : MemLp (localBoxHarmonicTimePrimitive u Du p a b c) ⊤
      (volume.restrict (Ioo a b)) :=
    hM.continuousLinearMap_comp (-unitBallHarmonicForceGradientExtended)
  refine ⟨memLp_continuousMap_field hH, ?_⟩
  have hB := memLp_continuousMap_field (μ := harmonicInteriorMeasure)
    (hM.neg.continuousLinearMap_comp harmonicCompactHessianOperator)
  intro i j
  exact hB.eval_piLp (j, i)

/-- Actual momentum approximation gives the true strong mixed pressure limit. -/
theorem localBox_harmonicInterior_pressure_sliceStrong
    {Ω : Set Vec3} {I : Set ℝ} {q a b : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b))
    {gs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1)}
    (hgs : ∀ n, MemLp (gs n) 1 volume)
    (hconv : Tendsto (fun n ↦ eLpNorm
      ((Ioo a b).indicator (unitBallMomentumForceCurve u Du p) - gs n)
      1 volume) atTop (𝓝 0)) :
    ProjectedEnergySliceStrong harmonicInteriorMeasure
      (volume.restrict (Ioo a b)) 1
      (fun z : unitBallPressureCompactInterior × ℝ ↦
        harmonicCompactPressureValues (-unitBallMomentumForceCurve u Du p z.2) z.1)
      (fun n z ↦ unitBallJointHarmonicApproxPressure gs n (z.1.1, z.2)) := by
  let J := Ioo a b
  let g := unitBallMomentumForceCurve u Du p
  let F : ℝ → C(unitBallPressureCompactInterior, ℝ) :=
    fun t ↦ harmonicCompactPressureValues (-g t)
  let Fs : ℕ → ℝ → C(unitBallPressureCompactInterior, ℝ) := fun n t ↦
    harmonicSmoothCompactPressureValues (suitableHarmonicSmoothRadius_pos n)
      (suitableHarmonicSmoothRadius_le n) (-gs n t)
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
  have hglobal := harmonicSmoothCompactPressureValues_strong_one
    suitableHarmonicSmoothRadius_tendsto suitableHarmonicSmoothRadius_pos
    suitableHarmonicSmoothRadius_le hg₀.neg (fun n ↦ (hgs n).neg) hneg
  have hlocal : Tendsto (fun n ↦ eLpNorm (Fs n - F) 1 (volume.restrict J)) atTop (𝓝 0) := by
    have hrestr : Tendsto (fun n ↦ eLpNorm (fun t ↦ Fs n t -
        harmonicCompactPressureValues (-(J.indicator g t))) 1 (volume.restrict J))
        atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglobal
        (fun _ ↦ zero_le) (fun _ ↦ eLpNorm_mono_measure _ Measure.restrict_le_self)
    convert hrestr using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [Fs, F, Pi.sub_apply, J, indicator_of_mem ht]
  have hF : MemLp F 1 (volume.restrict J) :=
    (memLp_one_iff_integrable.mpr hg).neg.continuousLinearMap_comp harmonicCompactPressureValues
  have hFs (n : ℕ) : MemLp (Fs n) 1 (volume.restrict J) :=
    ((hgs n).mono_measure Measure.restrict_le_self).neg.continuousLinearMap_comp
      (harmonicSmoothCompactPressureValues (suitableHarmonicSmoothRadius_pos n)
        (suitableHarmonicSmoothRadius_le n))
  have h := projectedEnergySliceStrong_one_continuousMap
    (μ := harmonicInteriorMeasure) hF hFs hlocal
  convert h using 1
  ext n z
  exact (harmonicSmoothCompactPressureValues_apply
    (suitableHarmonicSmoothRadius_pos n) (suitableHarmonicSmoothRadius_le n)
    (-gs n z.2) z.1).trans
      (harmonicJointSmoothPressure_apply (suitableHarmonicSmoothRadius_pos n)
        (fun t ↦ -gs n t) (z.1.1, z.2)).symm

/-- The actual force approximants retain joint smoothness and true harmonic identities. -/
theorem exists_suitable_unitBall_harmonic_joint_smooth_sequence_localBox
    {Ω : Set Vec3} {I : Set ℝ} {q a b c : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b) :
    ∃ gs fs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1),
      (∀ n, ContDiff ℝ ∞ (gs n) ∧ ContDiff ℝ ∞ (fs n) ∧
        HasCompactSupport (gs n) ∧
        tsupport (gs n) ⊆ meanApproxTimeSet a b ∧
        MemLp (gs n) 1 volume ∧ (∀ t, HasDerivAt (fs n) (gs n t) t)) ∧
      unitBallVelocityForceCurve u =ᵐ[volume.restrict (Ioo a b)]
        averagedTimePrimitive (unitBallVelocityForceCurve u)
          (unitBallMomentumForceCurve u Du p) a b c ∧
      Tendsto (fun n ↦ eLpNorm
        ((Ioo a b).indicator (unitBallMomentumForceCurve u Du p) - gs n)
        1 volume) atTop (𝓝 0) ∧
      TendstoUniformly fs
        (averagedTimePrimitive (unitBallVelocityForceCurve u)
          (unitBallMomentumForceCurve u Du p) a b c) atTop ∧
      (∃ C : ℝ, 0 < C ∧ ∀ n t, t ∈ Icc a b → ‖fs n t‖ ≤ C) ∧
      (∀ n, ContDiff ℝ ∞ (unitBallJointHarmonicApproxGradient fs n) ∧
        ContDiff ℝ ∞ (unitBallJointHarmonicApproxPressure gs n) ∧
        (∀ z i, timePartial (fun w ↦ unitBallJointHarmonicApproxGradient fs n w i) z =
          spatialPartial (unitBallJointHarmonicApproxPressure gs n) i z) ∧
        (∀ z, z.1 ∈ vec3Ball 0 (1 / 12) →
          (∑ i : Fin 3, spatialPartial
            (fun w ↦ unitBallJointHarmonicApproxGradient fs n w i) i z) = 0) ∧
        (∀ z i, z.1 ∈ vec3Ball 0 (1 / 12) →
          (∑ j : Fin 3, spatialSecondPartial
            (fun w ↦ unitBallJointHarmonicApproxGradient fs n w i) j j z) = 0)) ∧
      TendstoUniformly
        (fun n (z : unitBallPressureCompactInterior × Icc a b) ↦
          unitBallJointHarmonicApproxGradient fs n (z.1.1, z.2.1))
        (fun z ↦ localBoxHarmonicTimePrimitive u Du p a b c z.2.1 z.1) atTop ∧
      Tendsto (fun n ↦ eLpNorm (fun t ↦
        harmonicSmoothCompactPressureValues (suitableHarmonicSmoothRadius_pos n)
          (suitableHarmonicSmoothRadius_le n) (-gs n t) -
        harmonicCompactPressureValues
          (-((Ioo a b).indicator (unitBallMomentumForceCurve u Du p) t)))
        1 volume) atTop (𝓝 0) := by
  obtain ⟨gs, fs, hsm, hAE, hconv, hunif, C, hC, hbound⟩ :=
    exists_suitable_unitBall_force_smooth_sequence_localBox hsol hbox hab hc
  refine ⟨gs, fs, hsm, hAE, hconv, hunif, ⟨C, hC, hbound⟩, ?_, ?_, ?_⟩
  · intro n
    refine ⟨harmonicJointSmoothGradient_contDiff _ (hsm n).2.1.neg,
      harmonicJointSmoothPressure_contDiff _ (hsm n).1.neg, ?_, ?_, ?_⟩
    · intro z i
      exact harmonicJointSmoothGradient_timePartial _ (fun t ↦ ((hsm n).2.2.2.2.2 t).neg) z i
    · intro z hz
      exact harmonicJointSmoothGradient_divergence _ (suitableHarmonicSmoothRadius_le n)
        _ z hz
    · intro z i hz
      exact harmonicJointSmoothGradient_spatialSecondPartial _
        (suitableHarmonicSmoothRadius_le n) _ i z hz
  · have hneg : TendstoUniformly (fun n t ↦ -fs n t)
        (fun t ↦ -averagedTimePrimitive (unitBallVelocityForceCurve u)
          (unitBallMomentumForceCurve u Du p) a b c t) atTop := by
      apply Metric.tendstoUniformly_iff.mpr
      intro δ hδ
      filter_upwards [(Metric.tendstoUniformly_iff.mp hunif) δ hδ] with n hn t
      simpa only [localBoxForcePrimitive, dist_neg_neg] using hn t
    have h := harmonicJointSmoothGradient_tendstoUniformly hneg hC.le
      (fun n t ht ↦ by simpa only [norm_neg] using hbound n t ht)
      suitableHarmonicSmoothRadius_tendsto suitableHarmonicSmoothRadius_pos
      suitableHarmonicSmoothRadius_le
    simpa only [unitBallJointHarmonicApproxGradient, localBoxHarmonicTimePrimitive,
      localBoxForcePrimitive, map_neg] using h
  · obtain ⟨_, hg⟩ := suitable_unitBall_momentumForces_integrable_localBox hsol hbox
    have hg₀ : MemLp ((Ioo a b).indicator
        (unitBallMomentumForceCurve u Du p)) 1 volume :=
      memLp_one_iff_integrable.mpr (hg.integrable_indicator measurableSet_Ioo)
    have hnegconv : Tendsto (fun n ↦ eLpNorm
        ((fun t ↦ -gs n t) - fun t ↦
          -((Ioo a b).indicator (unitBallMomentumForceCurve u Du p) t))
        1 volume) atTop (𝓝 0) := by
      convert hconv using 1
      funext n
      congr 1
      funext t
      simp only [Pi.sub_apply]
      abel
    exact harmonicSmoothCompactPressureValues_strong_one suitableHarmonicSmoothRadius_tendsto
      suitableHarmonicSmoothRadius_pos suitableHarmonicSmoothRadius_le
      hg₀.neg (fun n ↦ (hsm n).2.2.2.2.1.neg) hnegconv

/-- Actual uniform force convergence supplies genuine correction and Hessian errors. -/
theorem localBox_harmonicInterior_uniform_approximations
    {Ω : Set Vec3} {I : Set ℝ} {q a b c : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    {fs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1)}
    (hfs : ∀ n, ContDiff ℝ ∞ (fs n))
    (hforce : TendstoUniformly fs
      (averagedTimePrimitive (unitBallVelocityForceCurve u)
        (unitBallMomentumForceCurve u Du p) a b c) atTop)
    (hfield : TendstoUniformly
      (fun n (z : unitBallPressureCompactInterior × Icc a b) ↦
        unitBallJointHarmonicApproxGradient fs n (z.1.1, z.2.1))
      (fun z ↦ localBoxHarmonicTimePrimitive u Du p a b c z.2.1 z.1) atTop) :
    ∃ CH CB : ℕ → ℝ,
      (∀ n, 0 ≤ CH n) ∧ Tendsto CH atTop (𝓝 0) ∧
      (∀ n, 0 ≤ CB n) ∧ Tendsto CB atTop (𝓝 0) ∧
      (∀ n t, t ∈ Icc a b → ∀ x : unitBallPressureCompactInterior,
        ‖unitBallJointHarmonicApproxGradient fs n (x.1, t) -
          localBoxProjectedHarmonicGradient u Du p a b c (x, t)‖ ≤ CH n) ∧
      (∀ n t, t ∈ Icc a b → ∀ x : unitBallPressureCompactInterior,
        ∀ i j, ‖unitBallJointHarmonicApproxDerivative fs n (x, t) i j -
          localBoxProjectedHarmonicDerivative u Du p a b c (x, t) i j‖ ≤ CB n) ∧
      (∀ n, MemLp (fun z : unitBallPressureCompactInterior × ℝ ↦
        unitBallJointHarmonicApproxGradient fs n (z.1.1, z.2)) ⊤
        (harmonicInteriorMeasure.prod (volume.restrict (Ioo a b)))) ∧
      (∀ n i j, MemLp (fun z ↦ unitBallJointHarmonicApproxDerivative fs n z i j) ⊤
        (harmonicInteriorMeasure.prod (volume.restrict (Ioo a b)))) := by
  let J := Ioo a b
  let T := Icc a b
  let M := averagedTimePrimitive (unitBallVelocityForceCurve u)
    (unitBallMomentumForceCurve u Du p) a b c
  obtain ⟨_, hg⟩ := suitable_unitBall_momentumForces_integrable_localBox hsol hbox
  have hM : Continuous M := averagedTimePrimitive_continuous hg
  have hH : Continuous (localBoxHarmonicTimePrimitive u Du p a b c) :=
    (unitBallHarmonicForceGradientExtended.continuous.comp hM).neg
  have hHjoint : Continuous (fun z : unitBallPressureCompactInterior × T ↦
      localBoxHarmonicTimePrimitive u Du p a b c z.2.1 z.1) :=
    continuous_eval.comp ((hH.comp (continuous_subtype_val.comp continuous_snd)).prodMk
      continuous_fst)
  have hHn (n : ℕ) : Continuous (unitBallJointHarmonicApproxGradient fs n) :=
    (harmonicJointSmoothGradient_contDiff _ (hfs n).neg).continuous
  obtain ⟨CH, hCH, hCHzero, hCHbound⟩ := exists_uniform_error_sequence hHjoint
    (fun n ↦ (hHn n).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))) hfield
  have hnegative : TendstoUniformly (fun n (t : T) ↦ -fs n t.1)
      (fun t : T ↦ -M t.1) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp hforce) ε hε] with n hn t
    simpa only [dist_neg_neg] using hn t.1
  have hBuniform := harmonicSmoothCompactHessian_tendstoUniformly
    suitableHarmonicSmoothRadius_tendsto suitableHarmonicSmoothRadius_pos
    suitableHarmonicSmoothRadius_le (hM.comp continuous_subtype_val).neg hnegative
  obtain ⟨CB, hCB, hCBzero, hCBbound⟩ := exists_uniform_error_sequence
    (harmonicCompactHessianOperator.continuous.comp (hM.comp continuous_subtype_val).neg)
    (fun n ↦ (harmonicSmoothCompactHessian (suitableHarmonicSmoothRadius_pos n)
      (suitableHarmonicSmoothRadius_le n)).continuous.comp
        ((hfs n).continuous.comp continuous_subtype_val).neg) hBuniform
  have hbH (n : ℕ) (t : ℝ) (ht : t ∈ T) (x : unitBallPressureCompactInterior) :
      ‖unitBallJointHarmonicApproxGradient fs n (x.1, t) -
        localBoxProjectedHarmonicGradient u Du p a b c (x, t)‖ ≤ CH n :=
    hCHbound n (x, ⟨t, ht⟩)
  have hbB (n : ℕ) (t : ℝ) (ht : t ∈ T) (x : unitBallPressureCompactInterior)
      (i j : Fin 3) : ‖unitBallJointHarmonicApproxDerivative fs n (x, t) i j -
        localBoxProjectedHarmonicDerivative u Du p a b c (x, t) i j‖ ≤ CB n := by
    rw [unitBallJointHarmonicApproxDerivative,
      unitBallJointHarmonicApproxGradient_spatialPartial]
    have he := (harmonicSmoothCompactHessian_apply (suitableHarmonicSmoothRadius_pos n)
      (suitableHarmonicSmoothRadius_le n) (-fs n t) x j i).symm
    rw [he]
    exact ((PiLp.norm_apply_le _ (j, i)).trans
      ((harmonicSmoothCompactHessian (suitableHarmonicSmoothRadius_pos n)
        (suitableHarmonicSmoothRadius_le n) (-fs n t) -
        harmonicCompactHessianOperator (-M t)).norm_coe_le_norm x)).trans
      (hCBbound n ⟨t, ht⟩)
  have htime : ∀ᵐ z : unitBallPressureCompactInterior × ℝ
      ∂harmonicInteriorMeasure.prod (volume.restrict J), z.2 ∈ J :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Ioo)).mpr
      (ae_of_all _ fun _ ↦ ae_restrict_mem measurableSet_Ioo)
  obtain ⟨hHtop, hBtop⟩ := localBox_harmonicInterior_correction_memLp_top hsol hbox hab hc
  refine ⟨CH, CB, hCH, hCHzero, hCB, hCBzero, hbH, hbB, ?_, ?_⟩
  · intro n
    apply memLp_top_of_uniform_difference hHtop
      ((hHn n).comp ((continuous_subtype_val.comp continuous_fst).prodMk
        continuous_snd)).aestronglyMeasurable
    exact htime.mono fun z hz ↦ hbH n z.2 (Ioo_subset_Icc_self hz) z.1
  · intro n i j
    have hc := (spatialPartial_contDiff ((contDiff_apply ℝ ℝ i).comp
      (harmonicJointSmoothGradient_contDiff (suitableHarmonicSmoothRadius_pos n)
        (hfs n).neg)) j).continuous
    apply memLp_top_of_uniform_difference (hBtop i j)
      (hc.comp ((continuous_subtype_val.comp continuous_fst).prodMk
        continuous_snd)).aestronglyMeasurable
    exact htime.mono fun z hz ↦ hbB n z.2 (Ioo_subset_Icc_self hz) z.1 i j

/-- The literal original-interval projected energy density. -/
def localBoxProjectedLocalEnergyDensity
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 × ℝ → ℝ)
    (z : unitBallPressureCompactInterior × ℝ) : ℝ :=
  projectedEnergyDeficitPolynomial (u (z.1.1, z.2))
    (localBoxProjectedHarmonicGradient u Du p a b c z)
    (fun j ↦ spatialPartial ψ j (z.1.1, z.2)) (Du (z.1.1, z.2))
    (localBoxProjectedHarmonicDerivative u Du p a b c z)
    (p (z.1.1, z.2) -
      harmonicCompactPressureValues (-unitBallMomentumForceCurve u Du p z.2) z.1)
    (ψ (z.1.1, z.2)) (timePartial ψ (z.1.1, z.2))
    (∑ j, spatialSecondPartial ψ j j (z.1.1, z.2))

set_option maxHeartbeats 1000000 in
/-- Actual suitability implies projected local energy on the original local interval. -/
theorem suitable_projected_local_energy_localBox
    {Ω : Set Vec3} {I : Set ℝ} {q a b c : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hnψ : ∀ z, 0 ≤ ψ z)
    (hsupp : tsupport ψ ⊆
      unitBallPressureCompactInterior ×ˢ Ioo a b) :
    Integrable (localBoxProjectedLocalEnergyDensity u Du p a b c ψ)
      (harmonicInteriorMeasure.prod (volume.restrict (Ioo a b))) ∧
      (∫ z, localBoxProjectedLocalEnergyDensity u Du p a b c ψ z
        ∂harmonicInteriorMeasure.prod (volume.restrict (Ioo a b))) ≤ 0 := by
  let J := Ioo a b
  let T := Icc a b
  let μ := harmonicInteriorMeasure
  let ν := volume.restrict J
  let U : unitBallPressureCompactInterior × ℝ → Vec3 := fun z ↦ u (z.1.1, z.2)
  let D : unitBallPressureCompactInterior × ℝ → Fin 3 → Vec3 := fun z ↦ Du (z.1.1, z.2)
  let P : unitBallPressureCompactInterior × ℝ → ℝ := fun z ↦ p (z.1.1, z.2)
  let H := localBoxProjectedHarmonicGradient u Du p a b c
  let B := localBoxProjectedHarmonicDerivative u Du p a b c
  let Q : unitBallPressureCompactInterior × ℝ → ℝ := fun z ↦
    harmonicCompactPressureValues (-unitBallMomentumForceCurve u Du p z.2) z.1
  let G : unitBallPressureCompactInterior × ℝ → Vec3 :=
    fun z j ↦ spatialPartial ψ j (z.1.1, z.2)
  let Ψ : unitBallPressureCompactInterior × ℝ → ℝ := fun z ↦ ψ (z.1.1, z.2)
  let τ : unitBallPressureCompactInterior × ℝ → ℝ := fun z ↦ timePartial ψ (z.1.1, z.2)
  let Λ : unitBallPressureCompactInterior × ℝ → ℝ :=
    fun z ↦ ∑ j, spatialSecondPartial ψ j j (z.1.1, z.2)
  obtain ⟨gs, fs, hsm, _hAE, hconv, hforce, _hbound, hjoint, hfield, _hpressure⟩ :=
    exists_suitable_unitBall_harmonic_joint_smooth_sequence_localBox hsol hbox hab hc
  let Hs : ℕ → unitBallPressureCompactInterior × ℝ → Vec3 :=
    fun n z ↦ unitBallJointHarmonicApproxGradient fs n (z.1.1, z.2)
  let Bs := unitBallJointHarmonicApproxDerivative fs
  let Qs : ℕ → unitBallPressureCompactInterior × ℝ → ℝ :=
    fun n z ↦ unitBallJointHarmonicApproxPressure gs n (z.1.1, z.2)
  obtain ⟨CH, CB, hCH, hCHzero, hCB, hCBzero, hHb, hBb, hHs, hBs⟩ :=
    localBox_harmonicInterior_uniform_approximations hsol hbox hab hc
      (fun n ↦ (hsm n).2.1) hforce hfield
  obtain ⟨hU, hD, hP⟩ := localBox_harmonicInterior_memLp hsol hbox hab
  obtain ⟨hH, hB⟩ := localBox_harmonicInterior_correction_memLp_top hsol hbox hab hc
  have ht : ∀ᵐ z : unitBallPressureCompactInterior × ℝ ∂μ.prod ν, z.2 ∈ J :=
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
  let GK : C(unitBallPressureCompactInterior × T, Vec3) :=
    ⟨fun z ↦ G (z.1, z.2.1), hGcont.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))⟩
  have hGb (t : ℝ) (ht : t ∈ T) (x : unitBallPressureCompactInterior) :
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
  obtain ⟨hUslices, hUclass⟩ := localBox_harmonicInterior_velocity_slice_data hsol hbox hab
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
  have hQ := localBox_harmonicInterior_pressure_sliceStrong hsol hbox
    (fun n ↦ (hsm n).2.2.2.2.1) hconv
  have hLEI : ∀ᶠ n in atTop, (∫ z, projectedEnergyDeficitPolynomial (U z) (Hs n z)
      (G z) (D z) (Bs n z) (P z - Qs n z) (Ψ z) (τ z) (Λ z) ∂μ.prod ν) ≤ 0 :=
    Eventually.of_forall fun n ↦ suitable_unitBall_joint_smooth_projected_energy_compact
      hsol (fun n ↦ ⟨(hsm n).1, (hsm n).2.1, (hsm n).2.2.2.2.2⟩) hψ hnψ hsupp n
  exact projectedEnergy_inequality_of_strongLp (memLp_pi_iff.mp hU) hV hW hB hP
    hVs hWs hBs (memLp_pi_iff.mp hG) hΨ hτ hΛ hVc hWc hBc hQ hAstrong hLEI

end FluidSingularSets
