-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallHarmonicForceExtension
public import FluidSingularSets.LocalHessianCalculus

/-!
# Actual energy-force harmonic pressure Hessian

The true derivative-first Hessian of the constructed C² pressure defines a
bounded linear operator on genuine gradient-annihilating energy forces.
Its compact radius-tenth domain contains the required mollification
neighborhoods. Orthogonal projection extends the actual operator to all
forces, fixing the genuine harmonic-pressure domain.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

local instance harmonicForceHessianForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance harmonicForceHessianForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- A compact interior containing the spatial mollification neighborhoods. -/
def unitBallPressureHessianCompactInterior : Set Vec3 := closure (vec3Ball 0 (1 / 10))

instance unitBallPressureHessianCompactInterior_compactSpace :
    CompactSpace unitBallPressureHessianCompactInterior :=
  isCompact_iff_compactSpace.mp (isCompact_closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 10))

theorem unitBallPressureHessianCompactInterior_subset_eighth :
    unitBallPressureHessianCompactInterior ⊆ vec3Ball 0 (1 / 8) := by
  rw [unitBallPressureHessianCompactInterior,
    closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 10)]
  intro x hx
  change vec3EuclideanNorm (x - 0) ≤ 1 / 10 at hx
  change vec3EuclideanNorm (x - 0) < 1 / 8
  exact hx.trans_lt (by norm_num : (1 / 10 : ℝ) < 1 / 8)

theorem unitBallPressureHessianCompactInterior_subset :
    unitBallPressureHessianCompactInterior ⊆ vec3Ball 0 (1 / 4) :=
  unitBallPressureHessianCompactInterior_subset_eighth.trans (vec3Ball_mono (by norm_num))

/-- The true derivative-first Hilbert Hessian matrix of the canonical pressure. -/
def unitBallHarmonicForceHessianMatrix (u : unitBallGradientFreeForce) (x : Vec3) :
    StokesGradientMatrix :=
  WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 ↦
    mixedSecond (unitBallHarmonicForcePressureRepresentative u) ij.1 ij.2 x)

@[simp]
theorem unitBallHarmonicForceHessianMatrix_apply (u : unitBallGradientFreeForce) (x : Vec3)
    (i j : Fin 3) :
    unitBallHarmonicForceHessianMatrix u x (i, j) =
      mixedSecond (unitBallHarmonicForcePressureRepresentative u) i j x := rfl

/-- The actual Hessian is the genuine weak gradient of the actual pressure-gradient components. -/
theorem unitBallHarmonicForcePressureRepresentative_gradient_hasWeakGradient
    (u : unitBallGradientFreeForce) (j : Fin 3) :
    HasWeakGradientOn (vec3Ball 0 (1 / 4))
      (fun x ↦ classicalGradient (unitBallHarmonicForcePressureRepresentative u) x j)
      (fun x i ↦ unitBallHarmonicForceHessianMatrix u x (i, j)) :=
  hasWeakGradientOn_gradient_of_contDiffOn_two (isOpen_vec3Ball 0 (1 / 4))
    (unitBallHarmonicForcePressureRepresentative_contDiff u) j

/-- The actual continuous Hessian on the genuinely compact interior. -/
def unitBallHarmonicForceHessianMap (u : unitBallGradientFreeForce) :
    C(unitBallPressureHessianCompactInterior, StokesGradientMatrix) where
  toFun := fun x ↦ unitBallHarmonicForceHessianMatrix u x.1
  continuous_toFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 × Fin 3 ↦ ℝ)).comp
    apply continuous_pi
    intro ij
    have hp := contDiffOn_spatialDeriv_of_two (isOpen_vec3Ball 0 (1 / 4))
      (unitBallHarmonicForcePressureRepresentative_contDiff u) ij.2
    have hd := hp.continuousOn_fderiv_of_isOpen (isOpen_vec3Ball 0 (1 / 4)) (by norm_num)
    exact continuousOn_iff_continuous_domRestrict.mp
      ((hd.clm_apply (g := fun _ ↦ basisVec ij.1) continuousOn_const).mono
        unitBallPressureHessianCompactInterior_subset)

/-- True pressure linearity gives actual Hessian linearity under addition. -/
theorem unitBallHarmonicForceHessianMap_add (u v : unitBallGradientFreeForce) :
    unitBallHarmonicForceHessianMap (u + v) = unitBallHarmonicForceHessianMap u +
      unitBallHarmonicForceHessianMap v := by
  ext x ij
  change mixedSecond (unitBallHarmonicForcePressureRepresentative (u + v)) ij.1 ij.2 x.1 =
    mixedSecond (unitBallHarmonicForcePressureRepresentative u) ij.1 ij.2 x.1 +
      mixedSecond (unitBallHarmonicForcePressureRepresentative v) ij.1 ij.2 x.1
  exact (mixedSecond_eqOn_of_eqOn (isOpen_vec3Ball 0 (1 / 4))
    (unitBallHarmonicForcePressureRepresentative_add u v) ij.1 ij.2
      (unitBallPressureHessianCompactInterior_subset x.property)).trans
    (mixedSecond_add_eqOn (isOpen_vec3Ball 0 (1 / 4))
      (unitBallHarmonicForcePressureRepresentative_contDiff u)
      (unitBallHarmonicForcePressureRepresentative_contDiff v) ij.1 ij.2
        (unitBallPressureHessianCompactInterior_subset x.property))

/-- True pressure linearity gives actual Hessian linearity under real scaling. -/
theorem unitBallHarmonicForceHessianMap_smul (c : ℝ) (u : unitBallGradientFreeForce) :
    unitBallHarmonicForceHessianMap (c • u) = c • unitBallHarmonicForceHessianMap u := by
  ext x ij
  change mixedSecond (unitBallHarmonicForcePressureRepresentative (c • u)) ij.1 ij.2 x.1 =
    c * mixedSecond (unitBallHarmonicForcePressureRepresentative u) ij.1 ij.2 x.1
  exact (mixedSecond_eqOn_of_eqOn (isOpen_vec3Ball 0 (1 / 4))
    (unitBallHarmonicForcePressureRepresentative_smul c u) ij.1 ij.2
      (unitBallPressureHessianCompactInterior_subset x.property)).trans
    (mixedSecond_smul_eqOn (isOpen_vec3Ball 0 (1 / 4))
      (unitBallHarmonicForcePressureRepresentative_contDiff u) c ij.1 ij.2
        (unitBallPressureHessianCompactInterior_subset x.property))

/-- The true Hilbert Hessian norm has the genuine uniform energy-force bound. -/
theorem unitBallHarmonicForceHessianMap_norm_le (F : unitBallGradientFreeForce) :
    ‖unitBallHarmonicForceHessianMap F‖ ≤ 3 * unitBallPressureHessianConstant * ‖F‖ := by
  have hb := (unitBallPressure_representative_derivative_bounds F.1
    (unitBallStokesPressure_weaklyHarmonic F.1 F.property)
    (unitBallHarmonicForcePressureRepresentative F)
    (unitBallHarmonicForcePressureRepresentative_contDiff F)
    (unitBallHarmonicForcePressureRepresentative_pressure_ae F)).2
  have hC : 0 ≤ unitBallPressureHessianConstant * ‖F‖ :=
    mul_nonneg unitBallPressureHessianConstant_nonneg (norm_nonneg F)
  rw [mul_assoc]
  apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hC)).mpr
  intro x
  have hentry (ij : Fin 3 × Fin 3) : ‖unitBallHarmonicForceHessianMatrix F x.1 ij‖ ≤
      unitBallPressureHessianConstant * ‖F‖ := by
    have h := hb x.1 (unitBallPressureHessianCompactInterior_subset_eighth x.property) ij.1 ij.2
    rw [unitBallGradientFreeForce_norm_coe] at h
    exact h
  have hsq : ‖unitBallHarmonicForceHessianMatrix F x.1‖ ^ 2 ≤
      9 * (unitBallPressureHessianConstant * ‖F‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _ij : Fin 3 × Fin 3, (unitBallPressureHessianConstant * ‖F‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro ij _
        exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hentry ij)
      _ = _ := by
        norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul]
  change ‖unitBallHarmonicForceHessianMatrix F x.1‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hC)).mp
  nlinarith [hsq]

/-- The genuine bounded linear harmonic-pressure Hessian on energy-dual forces. -/
def unitBallHarmonicForceHessian : unitBallGradientFreeForce →L[ℝ]
    C(unitBallPressureHessianCompactInterior, StokesGradientMatrix) :=
  ({ toFun := unitBallHarmonicForceHessianMap
     map_add' := unitBallHarmonicForceHessianMap_add
     map_smul' := unitBallHarmonicForceHessianMap_smul } :
       unitBallGradientFreeForce →ₗ[ℝ]
         C(unitBallPressureHessianCompactInterior, StokesGradientMatrix))
    |>.mkContinuous (3 * unitBallPressureHessianConstant) unitBallHarmonicForceHessianMap_norm_le

@[simp]
theorem unitBallHarmonicForceHessian_apply (F : unitBallGradientFreeForce)
    (x : unitBallPressureHessianCompactInterior) (i j : Fin 3) :
    unitBallHarmonicForceHessian F x (i, j) =
      mixedSecond (unitBallHarmonicForcePressureRepresentative F) i j x.1 := rfl

theorem unitBallHarmonicForceHessian_norm_le (F : unitBallGradientFreeForce) :
    ‖unitBallHarmonicForceHessian F‖ ≤ 3 * unitBallPressureHessianConstant * ‖F‖ :=
  unitBallHarmonicForceHessianMap_norm_le F

/-- The actual Hessian of the harmonic pressure of the canonically projected force. -/
def unitBallHarmonicForceHessianExtended : StokesEnergyForce (vec3Ball 0 1) →L[ℝ]
    C(unitBallPressureHessianCompactInterior, StokesGradientMatrix) :=
  unitBallHarmonicForceHessian.comp unitBallGradientFreeForceProjection

@[simp]
theorem unitBallHarmonicForceHessianExtended_apply
    (F : StokesEnergyForce (vec3Ball 0 1)) (x : unitBallPressureHessianCompactInterior)
    (i j : Fin 3) :
    unitBallHarmonicForceHessianExtended F x (i, j) =
      mixedSecond (unitBallHarmonicForcePressureRepresentative
        (unitBallGradientFreeForceProjection F)) i j x.1 := rfl

theorem unitBallHarmonicForceHessianExtended_of_gradientFree (F : unitBallGradientFreeForce) :
    unitBallHarmonicForceHessianExtended F.1 = unitBallHarmonicForceHessian F := by
  simp only [unitBallHarmonicForceHessianExtended, ContinuousLinearMap.comp_apply,
    unitBallGradientFreeForceProjection_of_gradientFree]

theorem unitBallHarmonicForceHessianExtended_norm_le
    (F : StokesEnergyForce (vec3Ball 0 1)) :
    ‖unitBallHarmonicForceHessianExtended F‖ ≤ 3 * unitBallPressureHessianConstant * ‖F‖ :=
  (unitBallHarmonicForceHessian_norm_le _).trans
    (mul_le_mul_of_nonneg_left (unitBallGradientFreeForceProjection_norm_le F)
      (mul_nonneg (by norm_num) unitBallPressureHessianConstant_nonneg))

theorem unitBallHarmonicForceHessianExtended_opNorm_le :
    ‖unitBallHarmonicForceHessianExtended‖ ≤ 3 * unitBallPressureHessianConstant :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (by norm_num) unitBallPressureHessianConstant_nonneg)
    unitBallHarmonicForceHessianExtended_norm_le

end FluidSingularSets
