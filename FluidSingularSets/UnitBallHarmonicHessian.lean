-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallHarmonicGradient
public import FluidSingularSets.LocalHessianCalculus

/-!
# Actual canonical harmonic pressure Hessian and spatial weak derivatives

The matrix uses derivative-first indices. It is the actual Hessian of the
constructed C² pressure representative. The genuine Weyl bound controls its
Hilbert norm, true pressure linearity makes it a bounded linear operator,
and actual local integration by parts gives the weak-gradient and divergence
identities required for the projected velocity.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual canonical representative is genuinely weakly harmonic on the inner ball. -/
theorem unitBallHarmonicPressureRepresentative_weaklyHarmonic (u : unitBallDivergenceFreeL2) :
    WeaklyHarmonicOn (vec3Ball 0 (1 / 4)) (unitBallHarmonicPressureRepresentative u) :=
  localWeaklyHarmonicOn_congr_ae (unitBallHarmonicPressureRepresentative_ae u)
    (localWeaklyHarmonicOn_restrict (vec3Ball_mono (by norm_num : (1 / 4 : ℝ) ≤ 1))
      (unitBallStokesPressure_weaklyHarmonic (unitBallHilbertVectorForce u.1) u.property))

/-- The actual canonical gradient is genuinely weakly divergence-free. -/
theorem unitBallHarmonicPressureRepresentative_gradient_divergenceFree
    (u : unitBallDivergenceFreeL2) (ψ : Vec3 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ vec3Ball 0 (1 / 4)) :
    (∫ x in vec3Ball 0 (1 / 4), ∑ i : Fin 3,
      classicalGradient (unitBallHarmonicPressureRepresentative u) x i * spatialDeriv ψ i x) = 0 :=
  classicalGradient_weakly_divergenceFree_of_weaklyHarmonic (isOpen_vec3Ball 0 (1 / 4))
    ((unitBallHarmonicPressureRepresentative_contDiff u).of_le (by norm_num))
    (unitBallHarmonicPressureRepresentative_weaklyHarmonic u) ψ hψ hc hs

/-- The true derivative-first Hilbert Hessian matrix of the canonical pressure. -/
def unitBallHarmonicHessianMatrix (u : unitBallDivergenceFreeL2) (x : Vec3) :
    StokesGradientMatrix :=
  WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 ↦
    mixedSecond (unitBallHarmonicPressureRepresentative u) ij.1 ij.2 x)

@[simp]
theorem unitBallHarmonicHessianMatrix_apply (u : unitBallDivergenceFreeL2) (x : Vec3)
    (i j : Fin 3) :
    unitBallHarmonicHessianMatrix u x (i, j) =
      mixedSecond (unitBallHarmonicPressureRepresentative u) i j x := rfl

/-- The actual Hessian is the genuine weak gradient of the actual pressure-gradient components. -/
theorem unitBallHarmonicPressureRepresentative_gradient_hasWeakGradient
    (u : unitBallDivergenceFreeL2) (j : Fin 3) :
    HasWeakGradientOn (vec3Ball 0 (1 / 4))
      (fun x ↦ classicalGradient (unitBallHarmonicPressureRepresentative u) x j)
      (fun x i ↦ unitBallHarmonicHessianMatrix u x (i, j)) :=
  hasWeakGradientOn_gradient_of_contDiffOn_two (isOpen_vec3Ball 0 (1 / 4))
    (unitBallHarmonicPressureRepresentative_contDiff u) j

theorem unitBallPressureCompactInterior_subset_eighth :
    unitBallPressureCompactInterior ⊆ vec3Ball 0 (1 / 8) := by
  rw [unitBallPressureCompactInterior, closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 16)]
  intro x hx
  change vec3EuclideanNorm (x - 0) ≤ 1 / 16 at hx
  change vec3EuclideanNorm (x - 0) < 1 / 8
  exact hx.trans_lt (by norm_num : (1 / 16 : ℝ) < 1 / 8)

/-- The actual continuous Hessian on the genuinely compact interior. -/
def unitBallHarmonicHessianMap (u : unitBallDivergenceFreeL2) :
    C(unitBallPressureCompactInterior, StokesGradientMatrix) where
  toFun := fun x ↦ unitBallHarmonicHessianMatrix u x.1
  continuous_toFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 × Fin 3 ↦ ℝ)).comp
    apply continuous_pi
    intro ij
    have hp := contDiffOn_spatialDeriv_of_two (isOpen_vec3Ball 0 (1 / 4))
      (unitBallHarmonicPressureRepresentative_contDiff u) ij.2
    have hd := hp.continuousOn_fderiv_of_isOpen (isOpen_vec3Ball 0 (1 / 4)) (by norm_num)
    exact continuousOn_iff_continuous_domRestrict.mp
      ((hd.clm_apply (g := fun _ ↦ basisVec ij.1) continuousOn_const).mono
        unitBallPressureCompactInterior_subset)

/-- True pressure linearity gives actual Hessian linearity under addition. -/
theorem unitBallHarmonicHessianMap_add (u v : unitBallDivergenceFreeL2) :
    unitBallHarmonicHessianMap (u + v) = unitBallHarmonicHessianMap u +
      unitBallHarmonicHessianMap v := by
  ext x ij
  change mixedSecond (unitBallHarmonicPressureRepresentative (u + v)) ij.1 ij.2 x.1 =
    mixedSecond (unitBallHarmonicPressureRepresentative u) ij.1 ij.2 x.1 +
      mixedSecond (unitBallHarmonicPressureRepresentative v) ij.1 ij.2 x.1
  exact (mixedSecond_eqOn_of_eqOn (isOpen_vec3Ball 0 (1 / 4))
    (unitBallHarmonicPressureRepresentative_add u v) ij.1 ij.2
      (unitBallPressureCompactInterior_subset x.property)).trans
    (mixedSecond_add_eqOn (isOpen_vec3Ball 0 (1 / 4))
      (unitBallHarmonicPressureRepresentative_contDiff u)
      (unitBallHarmonicPressureRepresentative_contDiff v) ij.1 ij.2
        (unitBallPressureCompactInterior_subset x.property))

/-- True pressure linearity gives actual Hessian linearity under real scaling. -/
theorem unitBallHarmonicHessianMap_smul (c : ℝ) (u : unitBallDivergenceFreeL2) :
    unitBallHarmonicHessianMap (c • u) = c • unitBallHarmonicHessianMap u := by
  ext x ij
  change mixedSecond (unitBallHarmonicPressureRepresentative (c • u)) ij.1 ij.2 x.1 =
    c * mixedSecond (unitBallHarmonicPressureRepresentative u) ij.1 ij.2 x.1
  exact (mixedSecond_eqOn_of_eqOn (isOpen_vec3Ball 0 (1 / 4))
    (unitBallHarmonicPressureRepresentative_smul c u) ij.1 ij.2
      (unitBallPressureCompactInterior_subset x.property)).trans
    (mixedSecond_smul_eqOn (isOpen_vec3Ball 0 (1 / 4))
      (unitBallHarmonicPressureRepresentative_contDiff u) c ij.1 ij.2
        (unitBallPressureCompactInterior_subset x.property))

/-- The true Hilbert Hessian norm has the genuine uniform vector-source bound. -/
theorem unitBallHarmonicHessianMap_norm_le (u : unitBallDivergenceFreeL2) :
    ‖unitBallHarmonicHessianMap u‖ ≤ 3 * stokesVectorPressureHessianConstant * ‖u‖ := by
  have hb := unitBallPressure_representative_derivative_bounds
    (unitBallHilbertVectorForce u.1)
    (unitBallStokesPressure_weaklyHarmonic _ u.property)
    (unitBallHarmonicPressureRepresentative u) (unitBallHarmonicPressureRepresentative_contDiff u)
    (unitBallHarmonicPressureRepresentative_ae u)
  have hf := stokesVectorForce_norm_le (isOpen_vec3Ball 0 1).measurableSet
    volume_vec3Ball_lt_top.ne (unitBallVectorCoordinates u.1)
  rw [← unitBallHilbertVectorForce_apply] at hf
  have hC : 0 ≤ stokesVectorPressureHessianConstant * ‖u‖ :=
    mul_nonneg stokesVectorPressureHessianConstant_nonneg (norm_nonneg u)
  rw [mul_assoc]
  apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hC)).mpr
  intro x
  have hentry (ij : Fin 3 × Fin 3) : ‖unitBallHarmonicHessianMatrix u x.1 ij‖ ≤
      stokesVectorPressureHessianConstant * ‖u‖ := by
    have h := hb.2 x.1 (unitBallPressureCompactInterior_subset_eighth x.property) ij.1 ij.2
    change ‖unitBallHarmonicHessianMatrix u x.1 ij‖ ≤ _
    rw [Real.norm_eq_abs]
    refine h.trans
      ((mul_le_mul_of_nonneg_left hf unitBallPressureHessianConstant_nonneg).trans ?_)
    simpa only [stokesVectorPressureHessianConstant, mul_assoc, ClosedSubmodule.norm_coe] using
      mul_le_mul_of_nonneg_left (unitBallVectorCoordinates_norm_le u.1)
        stokesVectorPressureHessianConstant_nonneg
  have hsq : ‖unitBallHarmonicHessianMatrix u x.1‖ ^ 2 ≤
      9 * (stokesVectorPressureHessianConstant * ‖u‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _ij : Fin 3 × Fin 3, (stokesVectorPressureHessianConstant * ‖u‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro ij _
        exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hentry ij)
      _ = _ := by simp
  change ‖unitBallHarmonicHessianMatrix u x.1‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hC)).mp
  nlinarith [hsq]

/-- The genuine bounded linear canonical harmonic-pressure Hessian. -/
def unitBallHarmonicHessian : unitBallDivergenceFreeL2 →L[ℝ]
    C(unitBallPressureCompactInterior, StokesGradientMatrix) :=
  ({ toFun := unitBallHarmonicHessianMap
     map_add' := unitBallHarmonicHessianMap_add
     map_smul' := unitBallHarmonicHessianMap_smul } :
       unitBallDivergenceFreeL2 →ₗ[ℝ]
         C(unitBallPressureCompactInterior, StokesGradientMatrix))
    |>.mkContinuous (3 * stokesVectorPressureHessianConstant) unitBallHarmonicHessianMap_norm_le

end FluidSingularSets
