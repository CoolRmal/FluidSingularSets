-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallSpatialKernels
public import FluidSingularSets.HarmonicJointSmoothApprox

/-!
# Genuine joint smooth approximations at arbitrary spatial margins

Actual smoothed force-dual kernels applied to smooth time curves yield genuine
jointly smooth pressure, gradient, and Hessian fields. A true force primitive
supplies the exact time-gradient identity, while actual scalar harmonicity
supplies spatial divergence and Laplacian cancellation on every valid inner ball.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology BigOperators ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

local instance fullBallJointForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance fullBallJointForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

variable (σ θ : ℝ) (hσ : 0 < σ) (hσθ : σ < θ) (hθ : θ < 1)

/-- Genuine joint smooth pressure obtained from the actual derivative force curve. -/
def fullBallJointSmoothPressure {ε : ℝ} (hε : 0 < ε)
    (g : ℝ → StokesEnergyForce (vec3Ball 0 1)) : Vec3 × ℝ → ℝ :=
  fun z ↦ fullBallSpatialSmoothPressureKernel σ θ hσ hσθ hθ hε z.1 (g z.2)

/-- Genuine joint smooth correction obtained from the actual force primitive. -/
def fullBallJointSmoothGradient {ε : ℝ} (hε : 0 < ε)
    (f : ℝ → StokesEnergyForce (vec3Ball 0 1)) : Vec3 × ℝ → Vec3 :=
  fun z i ↦ fullBallSpatialSmoothGradientKernel σ θ hσ hσθ hθ hε i z.1 (f z.2)

/-- Its actual Hessian in velocity-component/derivative order. -/
def fullBallJointSmoothHessian {ε : ℝ} (hε : 0 < ε)
    (f : ℝ → StokesEnergyForce (vec3Ball 0 1)) : Vec3 × ℝ → Fin 3 → Vec3 :=
  fun z i j ↦ fullBallSpatialSmoothHessianKernel σ θ hσ hσθ hθ hε j i z.1 (f z.2)

/-- Smooth time derivative data give genuine joint smoothness of the pressure. -/
theorem fullBallJointSmoothPressure_contDiff {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → StokesEnergyForce (vec3Ball 0 1)} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fullBallJointSmoothPressure σ θ hσ hσθ hθ hε g) :=
  ((fullBallSpatialSmoothPressureKernel_contDiff σ θ hσ hσθ hθ hε).comp
    contDiff_fst).clm_apply (hg.comp contDiff_snd)

/-- Smooth force primitives give genuine joint smoothness of the correction. -/
theorem fullBallJointSmoothGradient_contDiff {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → StokesEnergyForce (vec3Ball 0 1)} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fullBallJointSmoothGradient σ θ hσ hσθ hθ hε f) := by
  apply contDiff_pi.mpr
  intro i
  exact ((fullBallSpatialSmoothGradientKernel_contDiff σ θ hσ hσθ hθ hε i).comp
    contDiff_fst).clm_apply (hf.comp contDiff_snd)

/-- The literal Hessian array is jointly smooth as well. -/
theorem fullBallJointSmoothHessian_contDiff {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → StokesEnergyForce (vec3Ball 0 1)} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fullBallJointSmoothHessian σ θ hσ hσθ hθ hε f) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact ((fullBallSpatialSmoothHessianKernel_contDiff σ θ hσ hσθ hθ hε j i).comp
    contDiff_fst).clm_apply (hf.comp contDiff_snd)

/-- Actual pressure evaluation is the literal scalar spatial mollification. -/
theorem fullBallJointSmoothPressure_apply {ε : ℝ} (hε : 0 < ε)
    (g : ℝ → StokesEnergyForce (vec3Ball 0 1)) (z : Vec3 × ℝ) :
    fullBallJointSmoothPressure σ θ hσ hσθ hθ hε g z =
      fullBallSpatialSmoothPressure σ θ (g z.2) hε z.1 :=
  fullBallSpatialSmoothPressureKernel_apply σ θ hσ hσθ hθ hε z.1 (g z.2)

/-- Actual gradient evaluation is the true scalar spatial derivative. -/
theorem fullBallJointSmoothGradient_apply {ε : ℝ} (hε : 0 < ε)
    (f : ℝ → StokesEnergyForce (vec3Ball 0 1)) (z : Vec3 × ℝ) (i : Fin 3) :
    fullBallJointSmoothGradient σ θ hσ hσθ hθ hε f z i =
      fullBallSpatialSmoothGradient σ θ (f z.2) hε z.1 i :=
  fullBallSpatialSmoothGradientKernel_apply σ θ hσ hσθ hθ hε i z.1 (f z.2)

/-- Actual Hessian evaluation is the true iterated scalar spatial derivative. -/
theorem fullBallJointSmoothHessian_apply {ε : ℝ} (hε : 0 < ε)
    (f : ℝ → StokesEnergyForce (vec3Ball 0 1)) (z : Vec3 × ℝ) (i j : Fin 3) :
    fullBallJointSmoothHessian σ θ hσ hσθ hθ hε f z i j =
      mixedSecond (fullBallSpatialSmoothPressure σ θ (f z.2) hε) j i z.1 :=
  fullBallSpatialSmoothHessianKernel_apply σ θ hσ hσθ hθ hε j i z.1 (f z.2)

/-- The actual spatial derivative of the joint correction is its literal Hessian. -/
theorem fullBallJointSmoothGradient_spatialPartial {ε : ℝ} (hε : 0 < ε)
    (f : ℝ → StokesEnergyForce (vec3Ball 0 1)) (z : Vec3 × ℝ) (i j : Fin 3) :
    spatialPartial (fun w ↦ fullBallJointSmoothGradient σ θ hσ hσθ hθ hε f w i) j z =
      fullBallJointSmoothHessian σ θ hσ hσθ hθ hε f z i j := by
  simp_rw [spatialPartial, fullBallJointSmoothGradient_apply,
    fullBallJointSmoothHessian_apply]
  rfl

/-- A true force primitive supplies the exact time-gradient identity everywhere. -/
theorem fullBallJointSmoothGradient_timePartial {ε : ℝ} (hε : 0 < ε)
    {f g : ℝ → StokesEnergyForce (vec3Ball 0 1)}
    (hfg : ∀ t, HasDerivAt f (g t) t) (z : Vec3 × ℝ) (i : Fin 3) :
    timePartial (fun w ↦ fullBallJointSmoothGradient σ θ hσ hσθ hθ hε f w i) z =
      spatialPartial (fullBallJointSmoothPressure σ θ hσ hσθ hθ hε g) i z := by
  let L := fullBallSpatialSmoothGradientKernel σ θ hσ hσθ hθ hε i z.1
  have hd := L.hasFDerivAt.comp_hasDerivAt z.2 (hfg z.2)
  change deriv (fun t ↦
    fullBallSpatialSmoothGradientKernel σ θ hσ hσθ hθ hε i z.1 (f t)) z.2 =
      (fderiv ℝ (fun x ↦ fullBallJointSmoothPressure σ θ hσ hσθ hθ hε g (x, z.2))
        z.1) (basisVec i)
  change deriv ((fullBallSpatialSmoothGradientKernel σ θ hσ hσθ hθ hε i z.1) ∘ f) z.2 = _
  rw [hd.deriv]
  simp_rw [fullBallJointSmoothPressure_apply]
  exact fullBallSpatialSmoothGradientKernel_apply σ θ hσ hσθ hθ hε i z.1 (g z.2)

/-- Genuine spatial divergence vanishes on every admissible inner ball. -/
theorem fullBallJointSmoothGradient_divergence {ρ ε : ℝ} (hρσ : ρ < σ) (hε : 0 < ε)
    (hsmall : ε ≤ (σ - ρ) / 6) (f : ℝ → StokesEnergyForce (vec3Ball 0 1))
    (z : Vec3 × ℝ) (hz : z.1 ∈ vec3Ball 0 ρ) :
    (∑ i : Fin 3, spatialPartial
      (fun w ↦ fullBallJointSmoothGradient σ θ hσ hσθ hθ hε f w i) i z) = 0 := by
  simp_rw [spatialPartial, fullBallJointSmoothGradient_apply]
  exact fullBallSpatialSmoothGradient_divergence hσ hσθ hθ (f z.2) hρσ hε hsmall z.1 hz

/-- Every actual smoothed gradient component remains harmonic on that inner ball. -/
theorem fullBallJointSmoothGradient_harmonic {ρ ε : ℝ} (hρσ : ρ < σ) (hε : 0 < ε)
    (hsmall : ε ≤ (σ - ρ) / 6) (f : ℝ → StokesEnergyForce (vec3Ball 0 1))
    (i : Fin 3) (z : Vec3 × ℝ) (hz : z.1 ∈ vec3Ball 0 ρ) :
    spatialLaplacian
      (fun x ↦ fullBallJointSmoothGradient σ θ hσ hσθ hθ hε f (x, z.2) i) z.1 = 0 := by
  simp_rw [fullBallJointSmoothGradient_apply]
  exact fullBallSpatialSmoothGradient_harmonic hσ hσθ hθ (f z.2) hρσ hε hsmall i z.1 hz

/-- Literal iterated derivatives in the suitable energy test have exact zero Laplacian. -/
theorem fullBallJointSmoothGradient_spatialSecondPartial
    {ρ ε : ℝ} (hρσ : ρ < σ) (hε : 0 < ε) (hsmall : ε ≤ (σ - ρ) / 6)
    (f : ℝ → StokesEnergyForce (vec3Ball 0 1))
    (i : Fin 3) (z : Vec3 × ℝ) (hz : z.1 ∈ vec3Ball 0 ρ) :
    (∑ j : Fin 3, spatialSecondPartial
      (fun w ↦ fullBallJointSmoothGradient σ θ hσ hσθ hθ hε f w i) j j z) = 0 := by
  change spatialLaplacian
    (fun x ↦ fullBallJointSmoothGradient σ θ hσ hσθ hθ hε f (x, z.2) i) z.1 = 0
  exact fullBallJointSmoothGradient_harmonic σ θ hσ hσθ hθ hρσ hε hsmall f i z hz

end FluidSingularSets
