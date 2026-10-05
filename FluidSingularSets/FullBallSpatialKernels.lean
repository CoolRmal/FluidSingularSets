-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallSpatialSmoothApprox
public import FluidSingularSets.HarmonicJointSmoothApprox

/-!
# Actual dual smoothing kernels on arbitrary compact interiors

The genuine full-ball pressure evaluation kernel is cut off inside any chosen
interior radius. Its actual convolution is smooth in the energy-force dual,
and differentiation evaluates to the literal scalar pressure derivatives.
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

local instance fullBallKernelForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance fullBallKernelForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance fullBallKernelSpaceSecondCountable : SecondCountableTopology Vec3 :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → ℝ))

local instance fullBallKernelSpaceDualSecondCountable :
    SecondCountableTopologyEither Vec3 (StokesEnergyForce (vec3Ball 0 1) →L[ℝ] ℝ) :=
  ⟨Or.inl fullBallKernelSpaceSecondCountable⟩

variable (σ θ : ℝ) (hσ : 0 < σ) (hσθ : σ < θ) (hθ : θ < 1)

/-- Actual full-ball pressure evaluation, extended by zero outside the cutoff ball. -/
def fullBallSpatialRawPressureKernel (x : Vec3) :
    StokesEnergyForce (vec3Ball 0 1) →L[ℝ] ℝ := by
  classical
  have hθpos : 0 < θ := hσ.trans hσθ
  have hβone : (θ + 1) / 2 < 1 := by linarith
  have hθβ : θ < (θ + 1) / 2 := by linarith
  exact if hx : x ∈ vec3Ball 0 θ then
    fullBallHarmonicValueKernel (fullBallCompactInterior θ)
      (fullBallCompactInterior_subset_unit hθpos hθ) hβone
      (fullBallCompactInterior_subset hθpos hθβ) ⟨x, subset_closure hx⟩
  else 0

/-- The actual compact continuous dual kernel of the true pressure extension. -/
def fullBallSpatialCutoffPressureKernel (x : Vec3) :
    StokesEnergyForce (vec3Ball 0 1) →L[ℝ] ℝ :=
  fullBallSpatialCutoff σ θ x • fullBallSpatialRawPressureKernel σ θ hσ hσθ hθ x

/-- The actual kernel evaluates to the same genuine scalar cutoff potential. -/
theorem fullBallSpatialCutoffPressureKernel_apply (x : Vec3)
    (F : StokesEnergyForce (vec3Ball 0 1)) :
    fullBallSpatialCutoffPressureKernel σ θ hσ hσθ hθ x F =
      fullBallSpatialCutoffPressure σ θ F x := by
  by_cases hx : x ∈ vec3Ball (0 : Vec3) θ
  · simp only [fullBallSpatialCutoffPressureKernel, fullBallSpatialRawPressureKernel,
      dite_eq_left hx, smul_apply, smul_eq_mul, fullBallSpatialCutoffPressure,
      fullBallSpatialPressureRepresentative]
    rfl
  · have hz : fullBallSpatialCutoff σ θ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hx (fullBallSpatialCutoff_support hσ hσθ h))
    simp only [fullBallSpatialCutoffPressureKernel, fullBallSpatialCutoffPressure, hz,
      zero_smul, zero_apply, zero_mul]

/-- The true dual pressure kernel is globally continuous. -/
theorem fullBallSpatialCutoffPressureKernel_continuous :
    Continuous (fullBallSpatialCutoffPressureKernel σ θ hσ hσθ hθ) := by
  have hχ : Continuous (fullBallSpatialCutoff σ θ) :=
    (fullBallSpatialCutoff_smooth hσ hσθ).continuous
  have hθpos : 0 < θ := hσ.trans hσθ
  have hβpos : 0 < (θ + 1) / 2 := by linarith
  have hβone : (θ + 1) / 2 < 1 := by linarith
  have hθβ : θ < (θ + 1) / 2 := by linarith
  have hon : ContinuousOn (fullBallSpatialCutoffPressureKernel σ θ hσ hσθ hθ)
      (vec3Ball 0 θ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let inc : vec3Ball (0 : Vec3) θ → fullBallCompactInterior θ :=
      fun x ↦ ⟨x.1, subset_closure x.property⟩
    have hi : Continuous inc := continuous_subtype_val.subtype_mk _
    have hk := fullBallHarmonicValueKernel_continuous (fullBallCompactInterior θ)
      (fullBallCompactInterior_subset_unit hθpos hθ) hβpos hβone
      (fullBallCompactInterior_subset hθpos hθβ)
    have hh := (hχ.comp continuous_subtype_val).smul (hk.comp hi)
    convert hh using 1
    funext x
    simp only [Set.domRestrict, fullBallSpatialCutoffPressureKernel,
      fullBallSpatialRawPressureKernel, dite_eq_left x.property, inc]
    rfl
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ vec3Ball (0 : Vec3) θ
  · exact hon.continuousAt ((isOpen_vec3Ball 0 θ).mem_nhds hx)
  · have hn : x ∉ tsupport (fullBallSpatialCutoff σ θ) :=
      fun h ↦ hx (fullBallSpatialCutoff_support hσ hσθ h)
    have hz : fullBallSpatialCutoffPressureKernel σ θ hσ hσθ hθ =ᶠ[𝓝 x] fun _ ↦ 0 :=
      ((isClosed_tsupport (fullBallSpatialCutoff σ θ)).isOpen_compl.eventually_mem hn).mono
        fun y hy ↦ by
          simp only [fullBallSpatialCutoffPressureKernel,
            image_eq_zero_of_notMem_tsupport hy, zero_smul]
    exact continuousAt_const.congr hz.symm

/-- The actual dual kernel has true compact support. -/
theorem fullBallSpatialCutoffPressureKernel_hasCompactSupport :
    HasCompactSupport (fullBallSpatialCutoffPressureKernel σ θ hσ hσθ hθ) :=
  (canonicalBallCutoff_hasCompactSupport (x₀ := (0 : Vec3)) hσ.le hσθ).smul_right

/-- Genuine spatial convolution of the actual full-ball dual pressure kernel. -/
def fullBallSpatialSmoothPressureKernel {ε : ℝ} (hε : 0 < ε) :
    Vec3 → StokesEnergyForce (vec3Ball 0 1) →L[ℝ] ℝ :=
  convolution (mollifier ε hε) (fullBallSpatialCutoffPressureKernel σ θ hσ hσθ hθ)
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (StokesEnergyForce (vec3Ball 0 1))) volume

/-- Actual operator convolution is globally smooth in the force dual. -/
theorem fullBallSpatialSmoothPressureKernel_contDiff {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (fullBallSpatialSmoothPressureKernel σ θ hσ hσθ hθ hε) :=
  (mollifier_hasCompactSupport hε).contDiff_convolution_left
    (L := (ContinuousLinearMap.lsmul ℝ ℝ).precompR (StokesEnergyForce (vec3Ball 0 1)))
    (mollifier_contDiff hε)
      (fullBallSpatialCutoffPressureKernel_continuous σ θ hσ hσθ hθ).locallyIntegrable

/-- The actual operator convolution evaluates to the same literal scalar mollification. -/
theorem fullBallSpatialSmoothPressureKernel_apply {ε : ℝ} (hε : 0 < ε)
    (x : Vec3) (F : StokesEnergyForce (vec3Ball 0 1)) :
    fullBallSpatialSmoothPressureKernel σ θ hσ hσθ hθ hε x F =
      fullBallSpatialSmoothPressure σ θ F hε x := by
  have ht := convolution_precompR_apply (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (mollifier_locallyIntegrable hε)
    (fullBallSpatialCutoffPressureKernel_hasCompactSupport σ θ hσ hσθ hθ)
    (fullBallSpatialCutoffPressureKernel_continuous σ θ hσ hσθ hθ) x F
  change _ = mollify (fullBallSpatialCutoffPressure σ θ F) ε hε x
  exact ht.trans (congrArg (fun f : Vec3 → ℝ ↦ mollify f ε hε x)
    (funext fun y ↦ fullBallSpatialCutoffPressureKernel_apply σ θ hσ hσθ hθ y F))

/-- The true spatial derivative of the actual smoothed force-dual kernel. -/
def fullBallSpatialSmoothGradientKernel {ε : ℝ} (hε : 0 < ε) (i : Fin 3) :
    Vec3 → StokesEnergyForce (vec3Ball 0 1) →L[ℝ] ℝ :=
  fun x ↦ (fderiv ℝ (fullBallSpatialSmoothPressureKernel σ θ hσ hσθ hθ hε) x) (basisVec i)

/-- The actual force-dual gradient kernel is smooth. -/
theorem fullBallSpatialSmoothGradientKernel_contDiff {ε : ℝ} (hε : 0 < ε) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fullBallSpatialSmoothGradientKernel σ θ hσ hσθ hθ hε i) := by
  have hs := fullBallSpatialSmoothPressureKernel_contDiff σ θ hσ hσθ hθ hε
  have ht := hs.contDiff_fderiv_apply (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (by simp)
  exact ht.comp (contDiff_id.prodMk contDiff_const)

/-- Actual kernel differentiation evaluates to the true scalar pressure gradient. -/
theorem fullBallSpatialSmoothGradientKernel_apply {ε : ℝ} (hε : 0 < ε)
    (i : Fin 3) (x : Vec3) (F : StokesEnergyForce (vec3Ball 0 1)) :
    fullBallSpatialSmoothGradientKernel σ θ hσ hσθ hθ hε i x F =
      fullBallSpatialSmoothGradient σ θ F hε x i := by
  let ev := ContinuousLinearMap.apply ℝ ℝ F
  have heq : fullBallSpatialSmoothPressure σ θ F hε =
      fun y ↦ ev (fullBallSpatialSmoothPressureKernel σ θ hσ hσθ hθ hε y) := by
    funext y
    exact (fullBallSpatialSmoothPressureKernel_apply σ θ hσ hσθ hθ hε y F).symm
  have hd := ev.hasFDerivAt.comp x
    ((fullBallSpatialSmoothPressureKernel_contDiff σ θ hσ hσθ hθ hε).differentiable
      (by simp) x).hasFDerivAt
  change _ = (fderiv ℝ (fullBallSpatialSmoothPressure σ θ F hε) x) (basisVec i)
  rw [heq]
  change _ =
    (fderiv ℝ (ev ∘ fullBallSpatialSmoothPressureKernel σ θ hσ hσθ hθ hε) x) (basisVec i)
  rw [hd.fderiv]
  rfl

/-- The true derivative-first Hessian kernel of the same actual smoothed pressure. -/
def fullBallSpatialSmoothHessianKernel {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) :
    Vec3 → StokesEnergyForce (vec3Ball 0 1) →L[ℝ] ℝ :=
  fun x ↦ (fderiv ℝ (fullBallSpatialSmoothGradientKernel σ θ hσ hσθ hθ hε j) x) (basisVec i)

/-- The true force-dual Hessian kernel is smooth. -/
theorem fullBallSpatialSmoothHessianKernel_contDiff {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fullBallSpatialSmoothHessianKernel σ θ hσ hσθ hθ hε i j) := by
  have hs := fullBallSpatialSmoothGradientKernel_contDiff σ θ hσ hσθ hθ hε j
  have ht := hs.contDiff_fderiv_apply (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (by simp)
  exact ht.comp (contDiff_id.prodMk contDiff_const)

/-- Actual Hessian-kernel evaluation is the literal scalar second derivative. -/
theorem fullBallSpatialSmoothHessianKernel_apply {ε : ℝ} (hε : 0 < ε)
    (i j : Fin 3) (x : Vec3) (F : StokesEnergyForce (vec3Ball 0 1)) :
    fullBallSpatialSmoothHessianKernel σ θ hσ hσθ hθ hε i j x F =
      mixedSecond (fullBallSpatialSmoothPressure σ θ F hε) i j x := by
  let ev := ContinuousLinearMap.apply ℝ ℝ F
  have heq : spatialDeriv (fullBallSpatialSmoothPressure σ θ F hε) j =
      fun y ↦ ev (fullBallSpatialSmoothGradientKernel σ θ hσ hσθ hθ hε j y) := by
    funext y
    exact (fullBallSpatialSmoothGradientKernel_apply σ θ hσ hσθ hθ hε j y F).symm
  have hd := ev.hasFDerivAt.comp x
    ((fullBallSpatialSmoothGradientKernel_contDiff σ θ hσ hσθ hθ hε j).differentiable
      (by simp) x).hasFDerivAt
  change _ =
    (fderiv ℝ (spatialDeriv (fullBallSpatialSmoothPressure σ θ F hε) j) x) (basisVec i)
  rw [heq]
  change _ =
    (fderiv ℝ (ev ∘ fullBallSpatialSmoothGradientKernel σ θ hσ hσθ hθ hε j) x) (basisVec i)
  rw [hd.fderiv]
  rfl

end FluidSingularSets
