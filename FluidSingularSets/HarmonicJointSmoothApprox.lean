-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.HarmonicSpatialSmoothApprox
public import FluidSingularSets.CanonicalForcePressureValues

/-!
# Joint smoothing in the actual harmonic-pressure image

The true continuous dual pressure kernel is cut off and convolved in space.
The resulting operator kernel is globally smooth. Applying it to smooth force
primitives preserves actual harmonicity, divergence, and the time-gradient
identity, without choosing arbitrary continuous-field approximations.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

local instance harmonicJointForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance harmonicJointForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance harmonicJointSpaceSecondCountable : SecondCountableTopology Vec3 :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → ℝ))

local instance harmonicJointSpaceDualSecondCountable :
    SecondCountableTopologyEither Vec3 (StokesEnergyForce (vec3Ball 0 1) →L[ℝ] ℝ) :=
  ⟨Or.inl harmonicJointSpaceSecondCountable⟩

private theorem harmonicJoint_cutoff_support :
    tsupport harmonicSpatialCutoff ⊆ vec3Ball 0 (1 / 5) := by
  have h := mollifiedBallCutoff_tsupport_subset_outer 0
    (by norm_num : (0 : ℝ) < 1 / 4)
  rw [euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 3 * (1 / 4) / 4)] at h
  exact h.trans (vec3Ball_mono (by norm_num))

/-- The actual pressure evaluation kernel, extended by zero outside the interior ball. -/
def harmonicSpatialRawPressureKernel (x : Vec3) :
    StokesEnergyForce (vec3Ball 0 1) →L[ℝ] ℝ := by
  classical
  exact if hx : x ∈ vec3Ball 0 (1 / 5) then
    unitBallHarmonicForcePressureValueKernel ⟨x, subset_closure hx⟩
  else 0

/-- A genuine compact continuous dual kernel of the cutoff pressure potential. -/
def harmonicSpatialCutoffPressureKernel (x : Vec3) :
    StokesEnergyForce (vec3Ball 0 1) →L[ℝ] ℝ :=
  harmonicSpatialCutoff x • harmonicSpatialRawPressureKernel x

theorem harmonicSpatialCutoffPressureKernel_apply (x : Vec3)
    (F : StokesEnergyForce (vec3Ball 0 1)) :
    harmonicSpatialCutoffPressureKernel x F = harmonicSpatialCutoffPressure F x := by
  by_cases hx : x ∈ vec3Ball (0 : Vec3) (1 / 5)
  · simp only [harmonicSpatialCutoffPressureKernel, harmonicSpatialRawPressureKernel,
      dite_eq_left hx, smul_apply,
      unitBallHarmonicForcePressureValueKernel_apply, smul_eq_mul,
      harmonicSpatialCutoffPressure, harmonicSpatialPressureRepresentative]
  · have hz : harmonicSpatialCutoff x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hx (harmonicJoint_cutoff_support h))
    simp only [harmonicSpatialCutoffPressureKernel, harmonicSpatialCutoffPressure, hz,
      zero_smul, zero_apply, zero_mul]

theorem harmonicSpatialCutoffPressureKernel_continuous :
    Continuous harmonicSpatialCutoffPressureKernel := by
  have hχ : Continuous harmonicSpatialCutoff :=
    (mollifiedBallCutoff_smooth 0 (by norm_num : (0 : ℝ) < 1 / 4)).continuous
  have hon : ContinuousOn harmonicSpatialCutoffPressureKernel (vec3Ball 0 (1 / 5)) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let inc : vec3Ball (0 : Vec3) (1 / 5) → unitBallPressureValueCompactInterior :=
      fun x ↦ ⟨x.1, subset_closure x.property⟩
    have hi : Continuous inc := continuous_subtype_val.subtype_mk _
    have hh := (hχ.comp continuous_subtype_val).smul
      (unitBallHarmonicForcePressureValueKernel_continuous.comp hi)
    convert hh using 1
    funext x
    simp only [Set.domRestrict, harmonicSpatialCutoffPressureKernel,
      harmonicSpatialRawPressureKernel, dite_eq_left x.property, inc]
    rfl
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ vec3Ball (0 : Vec3) (1 / 5)
  · exact hon.continuousAt ((isOpen_vec3Ball 0 (1 / 5)).mem_nhds hx)
  · have hn : x ∉ tsupport harmonicSpatialCutoff :=
      fun h ↦ hx (harmonicJoint_cutoff_support h)
    have hz : harmonicSpatialCutoffPressureKernel =ᶠ[𝓝 x] fun _ ↦ 0 :=
      ((isClosed_tsupport harmonicSpatialCutoff).isOpen_compl.eventually_mem hn).mono
        fun y hy ↦ by
          simp only [harmonicSpatialCutoffPressureKernel,
            image_eq_zero_of_notMem_tsupport hy, zero_smul]
    exact continuousAt_const.congr hz.symm

theorem harmonicSpatialCutoffPressureKernel_hasCompactSupport :
    HasCompactSupport harmonicSpatialCutoffPressureKernel :=
  (mollifiedBallCutoff_hasCompactSupport 0 (by norm_num : (0 : ℝ) < 1 / 4)).smul_right

/-- Spatial convolution of the actual dual pressure kernel. -/
def harmonicSpatialSmoothPressureKernel {ε : ℝ} (hε : 0 < ε) :
    Vec3 → StokesEnergyForce (vec3Ball 0 1) →L[ℝ] ℝ :=
  convolution (mollifier ε hε) harmonicSpatialCutoffPressureKernel
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (StokesEnergyForce (vec3Ball 0 1))) volume

theorem harmonicSpatialSmoothPressureKernel_contDiff {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (harmonicSpatialSmoothPressureKernel hε) :=
  (mollifier_hasCompactSupport hε).contDiff_convolution_left
    (L := (ContinuousLinearMap.lsmul ℝ ℝ).precompR (StokesEnergyForce (vec3Ball 0 1)))
    (mollifier_contDiff hε)
      harmonicSpatialCutoffPressureKernel_continuous.locallyIntegrable

/-- The operator convolution evaluates to the original genuine scalar mollification. -/
theorem harmonicSpatialSmoothPressureKernel_apply {ε : ℝ} (hε : 0 < ε)
    (x : Vec3) (F : StokesEnergyForce (vec3Ball 0 1)) :
    harmonicSpatialSmoothPressureKernel hε x F = harmonicSpatialSmoothPressure F hε x := by
  have h := convolution_precompR_apply (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (mollifier_locallyIntegrable hε) harmonicSpatialCutoffPressureKernel_hasCompactSupport
      harmonicSpatialCutoffPressureKernel_continuous x F
  change harmonicSpatialSmoothPressureKernel hε x F =
    mollify (harmonicSpatialCutoffPressure F) ε hε x
  exact h.trans (congrArg (fun f : Vec3 → ℝ ↦ mollify f ε hε x)
    (funext fun y ↦ harmonicSpatialCutoffPressureKernel_apply y F))

/-- A true coordinate derivative of the smooth dual kernel. -/
def harmonicSpatialSmoothGradientKernel {ε : ℝ} (hε : 0 < ε) (i : Fin 3) :
    Vec3 → StokesEnergyForce (vec3Ball 0 1) →L[ℝ] ℝ :=
  fun x ↦ (fderiv ℝ (harmonicSpatialSmoothPressureKernel hε) x) (basisVec i)

theorem harmonicSpatialSmoothGradientKernel_contDiff {ε : ℝ} (hε : 0 < ε) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (harmonicSpatialSmoothGradientKernel hε i) := by
  have h := (harmonicSpatialSmoothPressureKernel_contDiff hε).contDiff_fderiv_apply
    (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (by simp)
  exact h.comp (contDiff_id.prodMk contDiff_const)

/-- Kernel differentiation gives the actual scalar pressure gradient. -/
theorem harmonicSpatialSmoothGradientKernel_apply {ε : ℝ} (hε : 0 < ε)
    (i : Fin 3) (x : Vec3) (F : StokesEnergyForce (vec3Ball 0 1)) :
    harmonicSpatialSmoothGradientKernel hε i x F =
      harmonicSpatialSmoothGradient F hε x i := by
  let ev := ContinuousLinearMap.apply ℝ ℝ F
  have heq : harmonicSpatialSmoothPressure F hε =
      fun y ↦ ev (harmonicSpatialSmoothPressureKernel hε y) := by
    funext y
    exact (harmonicSpatialSmoothPressureKernel_apply hε y F).symm
  have hd := ev.hasFDerivAt.comp x
    ((harmonicSpatialSmoothPressureKernel_contDiff hε).differentiable
      (by simp) x).hasFDerivAt
  change _ = (fderiv ℝ (harmonicSpatialSmoothPressure F hε) x) (basisVec i)
  rw [heq]
  change _ = (fderiv ℝ (ev ∘ harmonicSpatialSmoothPressureKernel hε) x) (basisVec i)
  rw [hd.fderiv]
  rfl

/-- Actual jointly smooth pressure data from the true force curve. -/
def harmonicJointSmoothPressure {ε : ℝ} (hε : 0 < ε)
    (g : ℝ → StokesEnergyForce (vec3Ball 0 1)) : Vec3 × ℝ → ℝ :=
  fun z ↦ harmonicSpatialSmoothPressureKernel hε z.1 (g z.2)

/-- Actual jointly smooth harmonic-gradient data from the true force primitive. -/
def harmonicJointSmoothGradient {ε : ℝ} (hε : 0 < ε)
    (f : ℝ → StokesEnergyForce (vec3Ball 0 1)) : Vec3 × ℝ → Vec3 :=
  fun z i ↦ harmonicSpatialSmoothGradientKernel hε i z.1 (f z.2)

theorem harmonicJointSmoothPressure_contDiff {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → StokesEnergyForce (vec3Ball 0 1)} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (harmonicJointSmoothPressure hε g) :=
  ((harmonicSpatialSmoothPressureKernel_contDiff hε).comp contDiff_fst).clm_apply
    (hg.comp contDiff_snd)

theorem harmonicJointSmoothGradient_contDiff {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → StokesEnergyForce (vec3Ball 0 1)} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (harmonicJointSmoothGradient hε f) := by
  apply contDiff_pi.mpr
  intro i
  exact ((harmonicSpatialSmoothGradientKernel_contDiff hε i).comp contDiff_fst).clm_apply
    (hf.comp contDiff_snd)

theorem harmonicJointSmoothPressure_apply {ε : ℝ} (hε : 0 < ε)
    (g : ℝ → StokesEnergyForce (vec3Ball 0 1)) (z : Vec3 × ℝ) :
    harmonicJointSmoothPressure hε g z = harmonicSpatialSmoothPressure (g z.2) hε z.1 :=
  harmonicSpatialSmoothPressureKernel_apply hε z.1 (g z.2)

theorem harmonicJointSmoothGradient_apply {ε : ℝ} (hε : 0 < ε)
    (f : ℝ → StokesEnergyForce (vec3Ball 0 1)) (z : Vec3 × ℝ) (i : Fin 3) :
    harmonicJointSmoothGradient hε f z i = harmonicSpatialSmoothGradient (f z.2) hε z.1 i :=
  harmonicSpatialSmoothGradientKernel_apply hε i z.1 (f z.2)

/-- A genuine force primitive supplies the exact time-gradient identity everywhere. -/
theorem harmonicJointSmoothGradient_timePartial {ε : ℝ} (hε : 0 < ε)
    {f g : ℝ → StokesEnergyForce (vec3Ball 0 1)}
    (hfg : ∀ t, HasDerivAt f (g t) t) (z : Vec3 × ℝ) (i : Fin 3) :
    timePartial (fun w ↦ harmonicJointSmoothGradient hε f w i) z =
      spatialPartial (harmonicJointSmoothPressure hε g) i z := by
  have hd := (harmonicSpatialSmoothGradientKernel hε i z.1).hasFDerivAt.comp_hasDerivAt
    z.2 (hfg z.2)
  change deriv (fun t ↦ harmonicSpatialSmoothGradientKernel hε i z.1 (f t)) z.2 =
    (fderiv ℝ (fun x ↦ harmonicJointSmoothPressure hε g (x, z.2)) z.1) (basisVec i)
  change deriv ((harmonicSpatialSmoothGradientKernel hε i z.1) ∘ f) z.2 = _
  rw [hd.deriv]
  simp_rw [harmonicJointSmoothPressure_apply]
  exact harmonicSpatialSmoothGradientKernel_apply hε i z.1 (g z.2)

/-- Spatial divergence vanishes for every time slice of the genuine smoothed primitive. -/
theorem harmonicJointSmoothGradient_divergence {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ 1 / 100) (f : ℝ → StokesEnergyForce (vec3Ball 0 1))
    (z : Vec3 × ℝ) (hz : z.1 ∈ vec3Ball 0 (1 / 12)) :
    (∑ i : Fin 3, spatialPartial (fun w ↦ harmonicJointSmoothGradient hε f w i) i z) = 0 := by
  simp_rw [spatialPartial, harmonicJointSmoothGradient_apply]
  exact harmonicSpatialSmoothGradient_divergence (f z.2) hε hsmall z.1 hz

/-- Every gradient component remains genuinely harmonic at every time. -/
theorem harmonicJointSmoothGradient_harmonic {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ 1 / 100) (f : ℝ → StokesEnergyForce (vec3Ball 0 1))
    (i : Fin 3) (z : Vec3 × ℝ) (hz : z.1 ∈ vec3Ball 0 (1 / 12)) :
    spatialLaplacian (fun x ↦ harmonicJointSmoothGradient hε f (x, z.2) i) z.1 = 0 := by
  simp_rw [harmonicJointSmoothGradient_apply]
  exact harmonicSpatialSmoothGradient_harmonic (f z.2) hε hsmall i z.1 hz

/-- The literal iterated derivatives used by the suitable local energy inequality. -/
theorem harmonicJointSmoothGradient_spatialSecondPartial {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ 1 / 100) (f : ℝ → StokesEnergyForce (vec3Ball 0 1))
    (i : Fin 3) (z : Vec3 × ℝ) (hz : z.1 ∈ vec3Ball 0 (1 / 12)) :
    (∑ j : Fin 3, spatialSecondPartial
      (fun w ↦ harmonicJointSmoothGradient hε f w i) j j z) = 0 := by
  change spatialLaplacian (fun x ↦ harmonicJointSmoothGradient hε f (x, z.2) i) z.1 = 0
  exact harmonicJointSmoothGradient_harmonic hε hsmall f i z hz

private theorem harmonicJoint_scalar_fderiv_bound {f : Vec3 → ℝ} (x : Vec3)
    {M : ℝ} (hM : 0 ≤ M) (hcoord : ∀ i : Fin 3, |spatialDeriv f i x| ≤ M) :
    ‖fderiv ℝ f x‖ ≤ 9 * M := by
  have hg : ‖classicalGradient f x‖ ≤ M :=
    (pi_norm_le_iff_of_nonneg hM).mpr fun i ↦ by
      simpa only [classicalGradient_apply, spatialDeriv, Real.norm_eq_abs] using hcoord i
  calc
    ‖fderiv ℝ f x‖ ≤ 3 * vec3EuclideanNorm (classicalGradient f x) :=
      fderiv_norm_le_three_euclidean_classicalGradient x
    _ ≤ 3 * (3 * ‖classicalGradient f x‖) := mul_le_mul_of_nonneg_left
      (euclideanNorm_le_three_mul_space_norm (classicalGradient f x)) (by norm_num)
    _ ≤ 9 * M := by nlinarith

/-- The compact potential retains the genuine uniform force-Hessian bound in the inner ball. -/
theorem harmonicSpatialCutoffPressure_mixedSecond_bound
    (F : StokesEnergyForce (vec3Ball 0 1)) (x : Vec3)
    (hx : x ∈ vec3Ball 0 (1 / 8)) (i j : Fin 3) :
    |mixedSecond (harmonicSpatialCutoffPressure F) i j x| ≤
      unitBallPressureHessianConstant * ‖F‖ := by
  have heq := mixedSecond_eqOn_of_eqOn (isOpen_vec3Ball 0 (1 / 8))
    (harmonicSpatialCutoffPressure_eqOn F) i j hx
  rw [heq]
  have hb := (unitBallPressure_representative_derivative_bounds
    (unitBallGradientFreeForceProjection F).1
    (unitBallStokesPressure_weaklyHarmonic _ (unitBallGradientFreeForceProjection F).property)
    (harmonicSpatialPressureRepresentative F)
    (unitBallHarmonicForcePressureRepresentative_contDiff _)
    (unitBallHarmonicForcePressureRepresentative_pressure_ae _)).2 x hx i j
  exact hb.trans (mul_le_mul_of_nonneg_left (unitBallGradientFreeForceProjection_norm_le F)
    unitBallPressureHessianConstant_nonneg)

private theorem harmonicJoint_compact_point_inner (x : unitBallPressureCompactInterior) :
    x.1 ∈ vec3Ball 0 (1 / 8) := by
  have hx := x.property
  change x.1 ∈ closure (vec3Ball 0 (1 / 16)) at hx
  rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 16)] at hx
  change vec3EuclideanNorm (x.1 - 0) ≤ 1 / 16 at hx
  exact hx.trans_lt (by norm_num)

private theorem harmonicJoint_compact_ball_inner (x : unitBallPressureCompactInterior)
    {ε : ℝ} (hsmall : ε ≤ 1 / 100) : Metric.ball x.1 ε ⊆ vec3Ball 0 (1 / 8) := by
  intro y hy
  have hx := x.property
  change x.1 ∈ closure (vec3Ball 0 (1 / 16)) at hx
  rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 16)] at hx
  change vec3EuclideanNorm (x.1 - 0) ≤ 1 / 16 at hx
  have hn := euclideanNorm_le_three_mul_space_norm (y - x.1)
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have he : vec3EuclideanNorm (y - x.1) ≤ 3 * ε :=
    hn.trans (mul_le_mul_of_nonneg_left hy.le (by norm_num))
  have ht := vec3EuclideanNorm_add_le (y - x.1) x.1
  rw [sub_add_cancel] at ht
  rw [mem_vec3Ball]
  norm_num only [sub_zero] at hx ⊢
  linarith

/-- The genuine Hessian estimate gives a uniform quantitative gradient smoothing error. -/
theorem harmonicSpatialSmoothGradient_component_error_le
    (F : StokesEnergyForce (vec3Ball 0 1)) {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε ≤ 1 / 100) (x : unitBallPressureCompactInterior) (i : Fin 3) :
    |harmonicSpatialSmoothGradient F hε x i -
      unitBallHarmonicForceGradientExtended F x i| ≤
        9 * unitBallPressureHessianConstant * ‖F‖ * ε := by
  let g := harmonicSpatialCutoffPressure F
  let M := unitBallPressureHessianConstant * ‖F‖
  have hM : 0 ≤ M := mul_nonneg unitBallPressureHessianConstant_nonneg (norm_nonneg F)
  have hfirst : ContDiff ℝ (1 : ℕ∞) (spatialDeriv g i) := by
    have h := (harmonicSpatialCutoffPressure_contDiff F).contDiff_fderiv_apply
      (m := (1 : ℕ∞)) (n := (2 : ℕ∞)) (by norm_num)
    exact h.comp (contDiff_id.prodMk contDiff_const)
  have hb : ∀ y ∈ vec3Ball 0 (1 / 8), ‖fderiv ℝ (spatialDeriv g i) y‖ ≤ 9 * M := by
    intro y hy
    exact harmonicJoint_scalar_fderiv_bound y hM fun j ↦
      harmonicSpatialCutoffPressure_mixedSecond_bound F y hy j i
  have hconv : Convex ℝ (vec3Ball (0 : Vec3) (1 / 8)) := by
    rw [← euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1 / 8)]
    exact convex_euclideanBall (by norm_num)
  have hlocal : ∀ y ∈ Metric.ball x.1 ε,
      dist (spatialDeriv g i y) (spatialDeriv g i x.1) ≤ 9 * M * ε := by
    intro y hy
    have hn := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _hz ↦ hfirst.differentiable (by norm_num) z) hb hconv
      (harmonicJoint_compact_point_inner x) (harmonicJoint_compact_ball_inner x hsmall hy)
    have hd : ‖y - x.1‖ ≤ ε := (Metric.mem_ball.mp hy).le
    rw [dist_eq_norm]
    exact hn.trans (mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num) hM))
  have hm := (standardMollifier (d := 3) ε hε).dist_normed_convolution_le
    (μ := volume) hfirst.continuous.aestronglyMeasurable
    (x₀ := x.1) (ε := 9 * M * ε) hlocal
  have heq := congrArg (fun v : Vec3 ↦ v i)
    (classicalGradient_eqOn_of_eqOn (isOpen_vec3Ball 0 (1 / 8))
      (harmonicSpatialCutoffPressure_eqOn F) (harmonicJoint_compact_point_inner x))
  change spatialDeriv g i x.1 = unitBallHarmonicForceGradientExtended F x i at heq
  change |spatialDeriv (harmonicSpatialSmoothPressure F hε) i x.1 -
    unitBallHarmonicForceGradientExtended F x i| ≤ _
  rw [harmonicSpatialSmoothPressure_spatialDeriv, ← heq]
  simpa only [dist_eq_norm, Real.norm_eq_abs, M, mul_assoc, mollify, mollifier, g] using hm

/-- All genuine gradient coordinates satisfy the same uniform force-dependent error bound. -/
theorem harmonicSpatialSmoothGradient_error_le
    (F : StokesEnergyForce (vec3Ball 0 1)) {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε ≤ 1 / 100) (x : unitBallPressureCompactInterior) :
    ‖harmonicSpatialSmoothGradient F hε x - unitBallHarmonicForceGradientExtended F x‖ ≤
      9 * unitBallPressureHessianConstant * ‖F‖ * ε := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) unitBallPressureHessianConstant_nonneg)
      (norm_nonneg F)) hε.le)).mpr
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    harmonicSpatialSmoothGradient_component_error_le F hε hsmall x i

/-- The actual joint field inherits the quantitative estimate at every time. -/
theorem harmonicJointSmoothGradient_error_le {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε ≤ 1 / 100) (f : ℝ → StokesEnergyForce (vec3Ball 0 1))
    (x : unitBallPressureCompactInterior) (t : ℝ) :
    ‖harmonicJointSmoothGradient hε f (x.1, t) - unitBallHarmonicForceGradientExtended (f t) x‖ ≤
      9 * unitBallPressureHessianConstant * ‖f t‖ * ε := by
  have heq : harmonicJointSmoothGradient hε f (x.1, t) =
      harmonicSpatialSmoothGradient (f t) hε x.1 := by
    funext i
    exact harmonicJointSmoothGradient_apply hε f (x.1, t) i
  rw [heq]
  exact harmonicSpatialSmoothGradient_error_le (f t) hε hsmall x

/-- The genuine pressure value kernel gives the corresponding scalar smoothing error. -/
theorem harmonicSpatialSmoothPressure_error_le
    (F : StokesEnergyForce (vec3Ball 0 1)) {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε ≤ 1 / 100) (x : unitBallPressureCompactInterior) :
    |harmonicSpatialSmoothPressure F hε x - harmonicSpatialPressureRepresentative F x| ≤
      3 * unitBallPressureGradientConstant * ‖F‖ * ε := by
  have hx := harmonicJoint_compact_point_inner x
  let xv : unitBallPressureValueCompactInterior :=
    ⟨x.1, subset_closure (vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1 / 5) hx)⟩
  have hlocal : ∀ y ∈ Metric.ball x.1 ε,
      dist (harmonicSpatialCutoffPressure F y) (harmonicSpatialCutoffPressure F x.1) ≤
        3 * unitBallPressureGradientConstant * ‖F‖ * ε := by
    intro y hy
    have hyi := harmonicJoint_compact_ball_inner x hsmall hy
    let yv : unitBallPressureValueCompactInterior :=
      ⟨y, subset_closure (vec3Ball_mono (by norm_num : (1 / 8 : ℝ) ≤ 1 / 5) hyi)⟩
    rw [harmonicSpatialCutoffPressure_eqOn F hyi, harmonicSpatialCutoffPressure_eqOn F hx,
      dist_eq_norm]
    have hb := unitBallHarmonicForcePressureValues_sub_le
      (unitBallGradientFreeForceProjection F) yv xv
    change ‖harmonicSpatialPressureRepresentative F y -
      harmonicSpatialPressureRepresentative F x.1‖ ≤
      (3 * unitBallPressureGradientConstant) * ‖unitBallGradientFreeForceProjection F‖ *
        ‖y - x.1‖ at hb
    have hc : 0 ≤ 3 * unitBallPressureGradientConstant :=
      mul_nonneg (by norm_num) unitBallPressureGradientConstant_nonneg
    have hd : ‖y - x.1‖ ≤ ε := (Metric.mem_ball.mp hy).le
    exact hb.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (unitBallGradientFreeForceProjection_norm_le F) hc)
      hd (norm_nonneg _) (mul_nonneg hc (norm_nonneg F)))
  have hm := (standardMollifier (d := 3) ε hε).dist_normed_convolution_le
    (μ := volume) (harmonicSpatialCutoffPressure_contDiff F).continuous.aestronglyMeasurable
    (x₀ := x.1) (ε := 3 * unitBallPressureGradientConstant * ‖F‖ * ε) hlocal
  rw [harmonicSpatialCutoffPressure_eqOn F hx] at hm
  simpa only [harmonicSpatialSmoothPressure, mollify, mollifier, dist_eq_norm,
    Real.norm_eq_abs] using hm

/-- Actual joint scalar pressures obey the force-dependent estimate at every time. -/
theorem harmonicJointSmoothPressure_error_le {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε ≤ 1 / 100) (g : ℝ → StokesEnergyForce (vec3Ball 0 1))
    (x : unitBallPressureCompactInterior) (t : ℝ) :
    |harmonicJointSmoothPressure hε g (x.1, t) -
      harmonicSpatialPressureRepresentative (g t) x| ≤
        3 * unitBallPressureGradientConstant * ‖g t‖ * ε := by
  rw [harmonicJointSmoothPressure_apply]
  exact harmonicSpatialSmoothPressure_error_le (g t) hε hsmall x

end FluidSingularSets
