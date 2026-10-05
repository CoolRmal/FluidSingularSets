-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallHarmonicForceExtension
public import CKN.Foundation.Harmonic.InteriorDisplayBounds
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Canonical interior pressure values and their continuous dual kernel

The genuine harmonic Stokes pressure of a gradient-annihilating energy force
defines a bounded linear map into continuous scalar functions on a compact
interior ball. Composing with the actual orthogonal force projection extends
this map to all energy forces. The evaluation kernel is Lipschitz in the
operator norm, proved from the true interior gradient estimate.
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

local instance pressureValuesForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance pressureValuesForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- This compact ball contains the support of the fixed radius-quarter cutoff. -/
def unitBallPressureValueCompactInterior : Set Vec3 := closure (vec3Ball 0 (1 / 5))

instance unitBallPressureValueCompactInterior_compactSpace :
    CompactSpace unitBallPressureValueCompactInterior :=
  isCompact_iff_compactSpace.mp (isCompact_closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 5))

theorem unitBallPressureValueCompactInterior_subset :
    unitBallPressureValueCompactInterior ⊆ vec3Ball 0 (1 / 4) := by
  rw [unitBallPressureValueCompactInterior, closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 5)]
  intro x hx
  change vec3EuclideanNorm (x - 0) ≤ 1 / 5 at hx
  change vec3EuclideanNorm (x - 0) < 1 / 4
  exact hx.trans_lt (by norm_num : (1 / 5 : ℝ) < 1 / 4)

/-- The native Weyl value estimate combined with the genuine Stokes pressure norm bound. -/
def unitBallPressureValueConstant : ℝ :=
  weakHarmonicInteriorSupConstant *
    (4 * (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ))

theorem unitBallPressureValueConstant_nonneg : 0 ≤ unitBallPressureValueConstant :=
  mul_nonneg weakHarmonicInteriorSupConstant_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.rpow_nonneg ENNReal.toReal_nonneg _))

/-- Any genuine continuous pressure representative has the actual force-norm value bound. -/
theorem unitBallPressure_representative_value_bound
    (F : StokesEnergyForce (vec3Ball 0 1))
    (hweak : WeaklyHarmonicOn (vec3Ball 0 1) (unitBallPressureFunction F))
    (H : Vec3 → ℝ) (hH : ContDiffOn ℝ (2 : ℕ∞) H (vec3Ball 0 (1 / 4)))
    (hae : unitBallPressureFunction F =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))] H) :
    ∀ x ∈ vec3Ball 0 (1 / 4), |H x| ≤ unitBallPressureValueConstant * ‖F‖ := by
  have hm := unitBallPressureFunction_memLp_threeHalves F
  have hw := hweak
  rw [← euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1)] at hm hw
  obtain ⟨G, hG, hGa, hGval, _hGgrad⟩ := weakly_harmonic_interior_smooth
    (by norm_num : (0 : ℝ) < 1) hm hw
  rw [euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1 / 2)] at hG hGa hGval
  have hsub : vec3Ball (0 : Vec3) (1 / 4) ⊆ vec3Ball 0 (1 / 2) :=
    vec3Ball_mono (by norm_num)
  have hHG : H =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))] G :=
    hae.symm.trans (ae_restrict_of_ae_restrict_of_subset hsub hGa)
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq hHG (isOpen_vec3Ball 0 (1 / 4))
    hH.continuousOn (hG.continuousOn.mono hsub)
  intro x hx
  rw [heq hx]
  have hv := hGval x (hsub hx)
  rw [euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1)] at hv
  norm_num only [one_pow, inv_one, mul_one] at hv
  exact hv.trans (by
    unfold unitBallPressureValueConstant
    have ht := mul_le_mul_of_nonneg_left (unitBallPressureFunction_lpNorm_threeHalves_le F)
      weakHarmonicInteriorSupConstant_nonneg
    convert ht using 1; ring)

/-- Actual pressure values on the fixed compact interior. -/
def unitBallHarmonicForcePressureValueMap (F : unitBallGradientFreeForce) :
    C(unitBallPressureValueCompactInterior, ℝ) where
  toFun := fun x ↦ unitBallHarmonicForcePressureRepresentative F x.1
  continuous_toFun := continuousOn_iff_continuous_domRestrict.mp
    ((unitBallHarmonicForcePressureRepresentative_contDiff F).continuousOn.mono
      unitBallPressureValueCompactInterior_subset)

theorem unitBallHarmonicForcePressureValueMap_add (F G : unitBallGradientFreeForce) :
    unitBallHarmonicForcePressureValueMap (F + G) =
      unitBallHarmonicForcePressureValueMap F + unitBallHarmonicForcePressureValueMap G := by
  ext x
  exact unitBallHarmonicForcePressureRepresentative_add F G
    (unitBallPressureValueCompactInterior_subset x.property)

theorem unitBallHarmonicForcePressureValueMap_smul (c : ℝ) (F : unitBallGradientFreeForce) :
    unitBallHarmonicForcePressureValueMap (c • F) =
      c • unitBallHarmonicForcePressureValueMap F := by
  ext x
  exact unitBallHarmonicForcePressureRepresentative_smul c F
    (unitBallPressureValueCompactInterior_subset x.property)

theorem unitBallHarmonicForcePressureValueMap_norm_le (F : unitBallGradientFreeForce) :
    ‖unitBallHarmonicForcePressureValueMap F‖ ≤ unitBallPressureValueConstant * ‖F‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg unitBallPressureValueConstant_nonneg (norm_nonneg F))).mpr
  intro x
  exact unitBallPressure_representative_value_bound F.1
    (unitBallStokesPressure_weaklyHarmonic F.1 F.property)
    (unitBallHarmonicForcePressureRepresentative F)
    (unitBallHarmonicForcePressureRepresentative_contDiff F)
    (unitBallHarmonicForcePressureRepresentative_pressure_ae F) x.1
    (unitBallPressureValueCompactInterior_subset x.property)

/-- Bounded linear actual harmonic pressure values for genuine gradient-annihilating forces. -/
def unitBallHarmonicForcePressureValues : unitBallGradientFreeForce →L[ℝ]
    C(unitBallPressureValueCompactInterior, ℝ) :=
  ({ toFun := unitBallHarmonicForcePressureValueMap
     map_add' := unitBallHarmonicForcePressureValueMap_add
     map_smul' := unitBallHarmonicForcePressureValueMap_smul } :
       unitBallGradientFreeForce →ₗ[ℝ] C(unitBallPressureValueCompactInterior, ℝ)).mkContinuous
    unitBallPressureValueConstant unitBallHarmonicForcePressureValueMap_norm_le

@[simp]
theorem unitBallHarmonicForcePressureValues_apply (F : unitBallGradientFreeForce)
    (x : unitBallPressureValueCompactInterior) :
    unitBallHarmonicForcePressureValues F x =
      unitBallHarmonicForcePressureRepresentative F x.1 := rfl

theorem unitBallHarmonicForcePressureValues_norm_le (F : unitBallGradientFreeForce) :
    ‖unitBallHarmonicForcePressureValues F‖ ≤ unitBallPressureValueConstant * ‖F‖ :=
  unitBallHarmonicForcePressureValueMap_norm_le F

/-- Values of the actual harmonic pressure of the canonically projected force. -/
def unitBallHarmonicForcePressureValuesExtended : StokesEnergyForce (vec3Ball 0 1) →L[ℝ]
    C(unitBallPressureValueCompactInterior, ℝ) :=
  unitBallHarmonicForcePressureValues.comp unitBallGradientFreeForceProjection

@[simp]
theorem unitBallHarmonicForcePressureValuesExtended_apply
    (F : StokesEnergyForce (vec3Ball 0 1)) (x : unitBallPressureValueCompactInterior) :
    unitBallHarmonicForcePressureValuesExtended F x =
      unitBallHarmonicForcePressureRepresentative (unitBallGradientFreeForceProjection F) x.1 :=
  rfl

theorem unitBallHarmonicForcePressureValues_opNorm_le :
    ‖unitBallHarmonicForcePressureValues‖ ≤ unitBallPressureValueConstant :=
  ContinuousLinearMap.opNorm_le_bound _ unitBallPressureValueConstant_nonneg
    unitBallHarmonicForcePressureValues_norm_le

theorem unitBallHarmonicForcePressureValuesExtended_of_gradientFree
    (F : unitBallGradientFreeForce) :
    unitBallHarmonicForcePressureValuesExtended F.1 = unitBallHarmonicForcePressureValues F := by
  simp only [unitBallHarmonicForcePressureValuesExtended, ContinuousLinearMap.comp_apply,
    unitBallGradientFreeForceProjection_of_gradientFree]

theorem unitBallHarmonicForcePressureValuesExtended_norm_le
    (F : StokesEnergyForce (vec3Ball 0 1)) :
    ‖unitBallHarmonicForcePressureValuesExtended F‖ ≤ unitBallPressureValueConstant * ‖F‖ :=
  (unitBallHarmonicForcePressureValues_norm_le _).trans
    (mul_le_mul_of_nonneg_left (unitBallGradientFreeForceProjection_norm_le F)
      unitBallPressureValueConstant_nonneg)

theorem unitBallHarmonicForcePressureValuesExtended_opNorm_le :
    ‖unitBallHarmonicForcePressureValuesExtended‖ ≤ unitBallPressureValueConstant :=
  ContinuousLinearMap.opNorm_le_bound _ unitBallPressureValueConstant_nonneg
    unitBallHarmonicForcePressureValuesExtended_norm_le

/-- The native coordinate derivative norm is controlled by the true Euclidean gradient. -/
theorem fderiv_norm_le_three_euclidean_classicalGradient {f : Vec3 → ℝ} (x : Vec3) :
    ‖fderiv ℝ f x‖ ≤ 3 * vec3EuclideanNorm (classicalGradient f x) :=
  fderiv_norm_le_three_classicalGradient x

/-- Actual pressure values obey the mean-value estimate on the compact interior ball. -/
theorem unitBallHarmonicForcePressureValues_sub_le (F : unitBallGradientFreeForce)
    (x y : unitBallPressureValueCompactInterior) :
    ‖unitBallHarmonicForcePressureValues F x - unitBallHarmonicForcePressureValues F y‖ ≤
      (3 * unitBallPressureGradientConstant) * ‖F‖ * ‖x.1 - y.1‖ := by
  have hd := (unitBallHarmonicForcePressureRepresentative_contDiff F).differentiableOn
    (by norm_num)
  have hb := (unitBallPressure_representative_derivative_bounds F.1
    (unitBallStokesPressure_weaklyHarmonic F.1 F.property)
    (unitBallHarmonicForcePressureRepresentative F)
    (unitBallHarmonicForcePressureRepresentative_contDiff F)
    (unitBallHarmonicForcePressureRepresentative_pressure_ae F)).1
  have hderiv : ∀ z ∈ vec3Ball 0 (1 / 4),
      ‖fderiv ℝ (unitBallHarmonicForcePressureRepresentative F) z‖ ≤
        (3 * unitBallPressureGradientConstant) * ‖F‖ := by
    intro z hz
    apply (fderiv_norm_le_three_euclidean_classicalGradient z).trans
    have h := mul_le_mul_of_nonneg_left (hb z hz) (by norm_num : (0 : ℝ) ≤ 3)
    rw [unitBallGradientFreeForce_norm_coe] at h
    simpa only [mul_assoc] using h
  have hconv : Convex ℝ (vec3Ball (0 : Vec3) (1 / 4)) := by
    rw [← euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1 / 4)]
    exact convex_euclideanBall (by norm_num)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz ↦ (hd z hz).differentiableAt ((isOpen_vec3Ball 0 (1 / 4)).mem_nhds hz))
    hderiv hconv (unitBallPressureValueCompactInterior_subset y.property)
      (unitBallPressureValueCompactInterior_subset x.property)

/-- The genuine dual evaluation kernel of the extended pressure-values operator. -/
def unitBallHarmonicForcePressureValueKernel (x : unitBallPressureValueCompactInterior) :
    StokesEnergyForce (vec3Ball 0 1) →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ x).comp unitBallHarmonicForcePressureValuesExtended

@[simp]
theorem unitBallHarmonicForcePressureValueKernel_apply
    (x : unitBallPressureValueCompactInterior) (F : StokesEnergyForce (vec3Ball 0 1)) :
    unitBallHarmonicForcePressureValueKernel x F =
      unitBallHarmonicForcePressureRepresentative (unitBallGradientFreeForceProjection F) x.1 :=
  rfl

/-- The true gradient estimate gives continuity of the kernel in the operator norm. -/
theorem unitBallHarmonicForcePressureValueKernel_sub_norm_le
    (x y : unitBallPressureValueCompactInterior) :
    ‖unitBallHarmonicForcePressureValueKernel x - unitBallHarmonicForcePressureValueKernel y‖ ≤
      (3 * unitBallPressureGradientConstant) * ‖x.1 - y.1‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (by norm_num) unitBallPressureGradientConstant_nonneg)
      (norm_nonneg _))
  intro F
  have h := unitBallHarmonicForcePressureValues_sub_le
    (unitBallGradientFreeForceProjection F) x y
  change ‖unitBallHarmonicForcePressureValues (unitBallGradientFreeForceProjection F) x -
    unitBallHarmonicForcePressureValues (unitBallGradientFreeForceProjection F) y‖ ≤ _
  apply h.trans
  calc
    _ ≤ (3 * unitBallPressureGradientConstant) * ‖F‖ * ‖x.1 - y.1‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (unitBallGradientFreeForceProjection_norm_le F)
          (mul_nonneg (by norm_num) unitBallPressureGradientConstant_nonneg)) (norm_nonneg _)
    _ = _ := by ring

theorem unitBallHarmonicForcePressureValueKernel_lipschitz :
    LipschitzWith (Real.toNNReal (3 * unitBallPressureGradientConstant))
      unitBallHarmonicForcePressureValueKernel := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Subtype.dist_eq, dist_eq_norm,
    Real.coe_toNNReal _ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
      unitBallPressureGradientConstant_nonneg)] using
    unitBallHarmonicForcePressureValueKernel_sub_norm_le x y

theorem unitBallHarmonicForcePressureValueKernel_continuous :
    Continuous unitBallHarmonicForcePressureValueKernel :=
  unitBallHarmonicForcePressureValueKernel_lipschitz.continuous

end FluidSingularSets
