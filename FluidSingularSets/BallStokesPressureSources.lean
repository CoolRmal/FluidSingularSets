-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.BallStokesPressureProjection
public import FluidSingularSets.StokesPressureCurves
public import FluidSingularSets.StokesTensorPressurePoisson
public import FluidSingularSets.StokesVectorForceLinear

/-!
# Genuine local Stokes pressures on arbitrary balls

The actual ball energy-dual pressure operator is applied to the genuine
convective tensor, viscous gradient, and velocity source. The physical compact
test identities give their literal distributional Poisson equations. Actual
suitable weak data supply the local spatial L⁴ slices needed by convection.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The true stress-to-pressure operator on the physical ball. -/
def ballTensorPressureL (x : Vec3) {r : ℝ} (hr : 0 < r) :
    StokesGradientL2 (vec3Ball x r) →L[ℝ] Lp ℝ 2 (volume.restrict (vec3Ball x r)) :=
  (ballStokesPressureL x hr).comp (stokesTensorForceL (vec3Ball x r))

@[simp]
theorem ballTensorPressureL_apply (x : Vec3) {r : ℝ} (hr : 0 < r)
    (T : StokesGradientL2 (vec3Ball x r)) :
    ballTensorPressureL x hr T = ballStokesPressureL x hr (stokesTensorForce T) := rfl

/-- The genuine tensor-pressure estimate has a center- and radius-independent constant. -/
theorem ballTensorPressureL_norm_le (x : Vec3) {r : ℝ} (hr : 0 < r)
    (T : StokesGradientL2 (vec3Ball x r)) : ‖ballTensorPressureL x hr T‖ ≤ 4 * ‖T‖ :=
  (ballStokesPressureL_norm_le x hr _).trans
    (mul_le_mul_of_nonneg_left (stokesTensorForce_norm_le T) (by norm_num))

/-- The literal physical-ball nonlinear pressure of actual spatial L⁴ velocity data. -/
def ballNonlinearPressure (x : Vec3) {r : ℝ} (hr : 0 < r) (u : Vec3 → Vec3)
    (hu : MemLp u 4 (volume.restrict (vec3Ball x r))) :
    Lp ℝ 2 (volume.restrict (vec3Ball x r)) :=
  ballTensorPressureL x hr (stokesConvectiveTensorL2 u hu)

/-- The physical nonlinear pressure is bounded by the actual spatial L⁴ velocity norm. -/
theorem ballNonlinearPressure_norm_le (x : Vec3) {r : ℝ} (hr : 0 < r)
    (u : Vec3 → Vec3) (hu : MemLp u 4 (volume.restrict (vec3Ball x r))) :
    ‖ballNonlinearPressure x hr u hu‖ ≤
      12 * (eLpNorm u 4 (volume.restrict (vec3Ball x r))).toReal ^ 2 := by
  exact (ballTensorPressureL_norm_le x hr _).trans
    (by nlinarith [stokesConvectiveTensorL2_norm_le u hu])

/-- The actual physical-ball viscous pressure, with the momentum-equation sign. -/
def ballRawViscousPressure (x : Vec3) {r : ℝ} (hr : 0 < r)
    (D : Vec3 → Fin 3 → Vec3) (hD : MemLp D 2 (volume.restrict (vec3Ball x r))) :
    Lp ℝ 2 (volume.restrict (vec3Ball x r)) :=
  ballTensorPressureL x hr (-stokesRawGradientL2 D hD)

/-- The true raw derivative array controls the physical viscous pressure uniformly. -/
theorem ballRawViscousPressure_norm_le (x : Vec3) {r : ℝ} (hr : 0 < r)
    (D : Vec3 → Fin 3 → Vec3) (hD : MemLp D 2 (volume.restrict (vec3Ball x r))) :
    ‖ballRawViscousPressure x hr D hD‖ ≤
      12 * (eLpNorm D 2 (volume.restrict (vec3Ball x r))).toReal := by
  have h := ballTensorPressureL_norm_le x hr (-stokesRawGradientL2 D hD)
  simp only [norm_neg] at h
  exact h.trans (by nlinarith [stokesRawGradientL2_norm_le D hD])

/-- The actual velocity-to-pressure operator on a physical ball. -/
def ballVectorPressureL (x : Vec3) {r : ℝ} (hr : 0 < r) :
    Lp Vec3 2 (volume.restrict (vec3Ball x r)) →L[ℝ]
      Lp ℝ 2 (volume.restrict (vec3Ball x r)) :=
  (ballStokesPressureL x hr).comp (stokesVectorForceL (vec3Ball x r))

/-- The actual velocity pressure has the genuine domain Poincare bound. -/
theorem ballVectorPressureL_norm_le (x : Vec3) {r : ℝ} (hr : 0 < r)
    (u : Lp Vec3 2 (volume.restrict (vec3Ball x r))) :
    ‖ballVectorPressureL x hr u‖ ≤
      12 * (stokesTestPoincareConstant (vec3Ball x r)).toReal * ‖u‖ := by
  have h := (ballStokesPressureL_norm_le x hr (stokesVectorForce (vec3Ball x r) u)).trans
    (mul_le_mul_of_nonneg_left (stokesVectorForce_norm_le (vec3Ball_measurable x r)
      volume_vec3Ball_lt_top.ne u) (by norm_num))
  change ‖ballStokesPressureL x hr (stokesVectorForce (vec3Ball x r) u)‖ ≤ _
  convert h using 1; ring

/-- The actual arbitrary-ball pressure supplies its literal Laplacian pairing. -/
theorem ballStokesPressureL_laplacian_pairing (x : Vec3) {r : ℝ} (hr : 0 < r)
    (F : StokesEnergyForce (vec3Ball x r)) (ψ : WeakTestFunction (vec3Ball x r)) :
    Integrable (fun y ↦ ballStokesPressureL x hr F y * spatialLaplacian ψ.toFun y)
      (volume.restrict (vec3Ball x r)) ∧
    (∫ y in vec3Ball x r, ballStokesPressureL x hr F y * spatialLaplacian ψ.toFun y) =
      -F (stokesEnergyTest (stokesScalarGradientTest ψ)) := by
  obtain ⟨hi, hp⟩ := ballStokesPressureL_test x hr F (stokesScalarGradientTest ψ)
  change Integrable (fun y ↦ ballStokesPressureL x hr F y * spatialLaplacian ψ.toFun y)
    (volume.restrict (vec3Ball x r)) at hi
  change inner ℝ (stokesEnergySolution F : stokesGradientEnergySpace (vec3Ball x r))
      (stokesEnergyTest (stokesScalarGradientTest ψ)) -
      (∫ y in vec3Ball x r, ballStokesPressureL x hr F y * spatialLaplacian ψ.toFun y) =
        F (stokesEnergyTest (stokesScalarGradientTest ψ)) at hp
  rw [stokesEnergySolution_inner_gradientTest] at hp
  exact ⟨hi, by linarith⟩

/-- The actual physical tensor pressure solves its literal Poisson equation. -/
theorem ballTensorPressureL_poisson (x : Vec3) {r : ℝ} (hr : 0 < r)
    (T : StokesGradientL2 (vec3Ball x r)) (ψ : WeakTestFunction (vec3Ball x r)) :
    Integrable (fun y ↦ ∑ ij : Fin 3 × Fin 3,
      T y ij * mixedSecond ψ.toFun ij.1 ij.2 y) (volume.restrict (vec3Ball x r)) ∧
    (∫ y in vec3Ball x r, ballTensorPressureL x hr T y * spatialLaplacian ψ.toFun y) =
      -(∫ y in vec3Ball x r, ∑ ij : Fin 3 × Fin 3,
        T y ij * mixedSecond ψ.toFun ij.1 ij.2 y) := by
  obtain ⟨hi, hp⟩ := stokesTensorForce_compactTest T (stokesScalarGradientTest ψ)
  change Integrable (fun y ↦ ∑ ij : Fin 3 × Fin 3,
    T y ij * mixedSecond ψ.toFun ij.1 ij.2 y) (volume.restrict (vec3Ball x r)) at hi
  change stokesTensorForce T (stokesEnergyTest (stokesScalarGradientTest ψ)) =
    ∫ y in vec3Ball x r, ∑ ij : Fin 3 × Fin 3,
      T y ij * mixedSecond ψ.toFun ij.1 ij.2 y at hp
  exact ⟨hi, (ballStokesPressureL_laplacian_pairing x hr _ ψ).2.trans
    (congrArg Neg.neg hp)⟩

/-- The actual physical nonlinear pressure has the genuine velocity-product Poisson source. -/
theorem ballNonlinearPressure_poisson (x : Vec3) {r : ℝ} (hr : 0 < r)
    (u : Vec3 → Vec3) (hu : MemLp u 4 (volume.restrict (vec3Ball x r)))
    (ψ : WeakTestFunction (vec3Ball x r)) :
    Integrable (fun y ↦ ∑ ij : Fin 3 × Fin 3,
      (u y ij.1 * u y ij.2) * mixedSecond ψ.toFun ij.1 ij.2 y)
        (volume.restrict (vec3Ball x r)) ∧
    (∫ y in vec3Ball x r, ballNonlinearPressure x hr u hu y * spatialLaplacian ψ.toFun y) =
      -(∫ y in vec3Ball x r, ∑ ij : Fin 3 × Fin 3,
        (u y ij.1 * u y ij.2) * mixedSecond ψ.toFun ij.1 ij.2 y) := by
  obtain ⟨hi, hp⟩ := stokesConvectiveTensorL2_compactTest u hu (stokesScalarGradientTest ψ)
  change Integrable (fun y ↦ ∑ ij : Fin 3 × Fin 3,
    (u y ij.1 * u y ij.2) * mixedSecond ψ.toFun ij.1 ij.2 y)
      (volume.restrict (vec3Ball x r)) at hi
  change stokesTensorForce (stokesConvectiveTensorL2 u hu)
      (stokesEnergyTest (stokesScalarGradientTest ψ)) =
    ∫ y in vec3Ball x r, ∑ ij : Fin 3 × Fin 3,
      (u y ij.1 * u y ij.2) * mixedSecond ψ.toFun ij.1 ij.2 y at hp
  exact ⟨hi, (ballStokesPressureL_laplacian_pairing x hr _ ψ).2.trans
    (congrArg Neg.neg hp)⟩

/-- The actual derivative of a weakly divergence-free velocity has harmonic viscous pressure. -/
theorem ballRawViscousPressure_weaklyHarmonic (x : Vec3) {r : ℝ} (hr : 0 < r)
    (u : Vec3 → Vec3) (D : Vec3 → Fin 3 → Vec3)
    (hu : MemLp u 2 (volume.restrict (vec3Ball x r)))
    (hD : MemLp D 2 (volume.restrict (vec3Ball x r)))
    (hgrad : ∀ i : Fin 3, HasWeakGradientOn (vec3Ball x r)
      (fun y ↦ u y i) (fun y ↦ D y i))
    (hdiv : ∀ ψ : WeakTestFunction (vec3Ball x r),
      (∫ y in vec3Ball x r, ∑ i : Fin 3, u y i * spatialDeriv ψ.toFun i y) = 0) :
    WeaklyHarmonicOn (vec3Ball x r) (ballRawViscousPressure x hr D hD) := by
  intro ψ hψ hcompact hsub
  let φ : WeakTestFunction (vec3Ball x r) := ⟨ψ, hψ, hcompact, hsub⟩
  have hp := (ballTensorPressureL_poisson x hr (-stokesRawGradientL2 D hD) φ).2
  have hae : (fun y ↦ ∑ ij : Fin 3 × Fin 3,
      (-stokesRawGradientL2 D hD) y ij * mixedSecond ψ ij.1 ij.2 y) =ᵐ[
        volume.restrict (vec3Ball x r)]
      (fun y ↦ -(∑ ij : Fin 3 × Fin 3, D y ij.2 ij.1 * mixedSecond ψ ij.1 ij.2 y)) := by
    filter_upwards [Lp.coeFn_neg (stokesRawGradientL2 D hD),
      (stokesRawGradientMatrix_memLp D hD).coeFn_toLp] with y hy ht
    change stokesRawGradientL2 D hD y = stokesRawGradientMatrix D y at ht
    rw [hy]
    change (∑ ij : Fin 3 × Fin 3,
      (-(stokesRawGradientL2 D hD y)) ij * mixedSecond ψ ij.1 ij.2 y) = _
    rw [ht]
    simp only [PiLp.neg_apply, neg_mul, Finset.sum_neg_distrib, stokesRawGradientMatrix]
  have hzero := weakGradient_hessian_pairing_zero u D hu hD hgrad hdiv φ
  rw [integral_congr_ae hae, integral_neg, hzero, neg_zero, neg_zero] at hp
  exact hp

/-- The physical spatial Poincare constant has its genuine linear radius scaling. -/
theorem stokesTestPoincareConstant_ball_toReal (x : Vec3) {r : ℝ} (hr : 0 < r) :
    (stokesTestPoincareConstant (vec3Ball x r)).toReal =
      r * (stokesTestPoincareConstant (vec3Ball 0 1)).toReal := by
  have hv : (volume (vec3Ball x r)).toReal =
      r ^ 3 * (volume (vec3Ball 0 1)).toReal := by
    rw [volume_vec3Ball_eq, volume_vec3Ball_eq, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr.le]
    norm_num
  have hc : (r ^ 3) ^ (1 / 3 : ℝ) = r := by
    rw [← Real.rpow_natCast_mul hr.le]
    norm_num
  unfold stokesTestPoincareConstant
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  rw [hv, Real.mul_rpow (by positivity) ENNReal.toReal_nonneg, hc]
  ring

/-- The genuine velocity-pressure bound displays its exact linear radius factor. -/
theorem ballVectorPressureL_norm_le_radius (x : Vec3) {r : ℝ} (hr : 0 < r)
    (u : Lp Vec3 2 (volume.restrict (vec3Ball x r))) :
    ‖ballVectorPressureL x hr u‖ ≤
      12 * (stokesTestPoincareConstant (vec3Ball 0 1)).toReal * r * ‖u‖ := by
  have h := ballVectorPressureL_norm_le x hr u
  rw [stokesTestPoincareConstant_ball_toReal x hr] at h
  convert h using 1; ring

/-- Genuine local H¹ data give spatial L⁴ on every smaller concentric ball. -/
theorem ballH1Vector_memLp_four (x : Vec3) {r : ℝ} (hr : 0 < r)
    {u : Vec3 → Vec3} {D : Vec3 → Fin 3 → Vec3}
    (hu : MemLp u 2 (volume.restrict (euclideanBall x (2 * r))))
    (hD : MemLp D 2 (volume.restrict (euclideanBall x (2 * r))))
    (hw : ∀ j : Fin 3, HasWeakGradientOn (euclideanBall x (2 * r))
      (fun y ↦ u y j) (fun y ↦ D y j)) :
    MemLp u 4 (volume.restrict (euclideanBall x r)) := by
  have hvol : volume (euclideanBall x r) ≠ ∞ := by
    rw [euclideanBall_eq_vec3Ball hr]
    exact volume_vec3Ball_lt_top.ne
  let : IsFiniteMeasure (volume.restrict (euclideanBall x r)) :=
    isFiniteMeasure_restrict.mpr hvol
  apply MemLp.of_eval
  intro j
  let v : H1Function (euclideanBall x (2 * r)) :=
    { toFun := fun y ↦ u y j
      grad := fun y ↦ D y j
      memL2 := hu.eval j
      gradMemL2 := fun i ↦ (hD.eval j).eval i
      hasWeakGradient := hw j }
  have hs := h1SobolevBall hr v
  change eLpNorm (fun y ↦ u y j) 6 (volume.restrict (euclideanBall x r)) ≤
    localSobolevConstant *
      (eLpNorm (fun y ↦ D y j) 2 (volume.restrict (euclideanBall x (2 * r))) +
        (Real.toNNReal (32 / r) : ℝ≥0∞) *
          eLpNorm (fun y ↦ u y j) 2 (volume.restrict (euclideanBall x (2 * r)))) at hs
  have hm : MemLp (fun y ↦ u y j) 6 (volume.restrict (euclideanBall x r)) := by
    apply memLp_iff.mpr
    exact hs.trans_lt (by
      unfold localSobolevConstant
      finiteness [hu.eval j, hD.eval j])
  exact hm.mono_exponent (by norm_num)

/-- Actual suitable weak data supply the needed L⁴ slices on an arbitrary interior ball. -/
theorem suitable_ball_memLp_four_ae
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (x : Vec3) {r : ℝ} (hr : 0 < r)
    (hbox : localBox Ω I (euclideanBall x (2 * r)) J) :
    ∀ᵐ t ∂volume.restrict J,
      MemLp (fun y ↦ u (y, t)) 4 (volume.restrict (vec3Ball x r)) := by
  have hw : ∀ᵐ t ∂volume.restrict J, ∀ j : Fin 3,
      HasWeakGradientOn (euclideanBall x (2 * r))
        (fun y ↦ u (y, t) j) (fun y ↦ D (y, t) j) :=
    ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)
  filter_upwards [slice_memLp_ae_of_sws hsol hbox, hw] with t ht hwt
  rw [← euclideanBall_eq_vec3Ball hr]
  exact ballH1Vector_memLp_four x hr ht.1 ht.2 hwt

end FluidSingularSets
