-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallHarmonicRegularity
public import FluidSingularSets.UnitBallHarmonicForceHessian
public import FluidSingularSets.CanonicalForcePressureValues

/-!
# Genuine harmonic operators on arbitrary compact interiors

Full-ball pressure representatives are linear by their actual pressure-class
identity and continuous uniqueness. Their actual derivatives therefore give
bounded linear fields on every compact interior, with boundary-margin bounds.
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

/-- The actual closed spatial ball for any compact interior radius. -/
def fullBallCompactInterior (ρ : ℝ) : Set Vec3 := closure (vec3Ball 0 ρ)

instance fullBallCompactInterior_compactSpace (ρ : ℝ) :
    CompactSpace (fullBallCompactInterior ρ) := by
  apply isCompact_iff_compactSpace.mp
  by_cases hρ : 0 < ρ
  · exact isCompact_closure_vec3Ball hρ
  · have he : vec3Ball (0 : Vec3) ρ = ∅ := by
      ext x
      simp only [mem_vec3Ball, mem_empty_iff_false, iff_false]
      exact not_lt.mpr ((le_of_not_gt hρ).trans (vec3EuclideanNorm_nonneg _))
    simp only [fullBallCompactInterior, he, closure_empty]
    exact isCompact_empty

/-- The true compact ball is contained in every strictly larger ball. -/
theorem fullBallCompactInterior_subset {ρ σ : ℝ} (hρ : 0 < ρ) (hρσ : ρ < σ) :
    fullBallCompactInterior ρ ⊆ vec3Ball 0 σ := by
  rw [fullBallCompactInterior, closure_vec3Ball hρ]
  intro x hx
  exact hx.trans_lt hρσ

/-- The actual compact radius below one gives a genuine interior subtype. -/
theorem fullBallCompactInterior_subset_unit {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ < 1) :
    fullBallCompactInterior ρ ⊆ vec3Ball 0 1 :=
  fullBallCompactInterior_subset hρ hρone

/-- Actual pressure-class addition identifies the full-ball representatives pointwise. -/
theorem unitBallFullHarmonicForcePressureRepresentative_add (F G : unitBallGradientFreeForce) :
    EqOn (unitBallFullHarmonicForcePressureRepresentative (F + G))
      (unitBallFullHarmonicForcePressureRepresentative F +
        unitBallFullHarmonicForcePressureRepresentative G) (vec3Ball 0 1) := by
  have hc : unitBallHarmonicForcePressureClassL (F + G) =ᵐ[volume.restrict (vec3Ball 0 1)]
      (fun x ↦ unitBallHarmonicForcePressureClassL F x +
        unitBallHarmonicForcePressureClassL G x) := by
    rw [map_add]
    exact Lp.coeFn_add _ _
  have he := (unitBallFullHarmonicForcePressureRepresentative_ae (F + G)).symm.trans
    (hc.trans ((unitBallFullHarmonicForcePressureRepresentative_ae F).add
      (unitBallFullHarmonicForcePressureRepresentative_ae G)))
  exact Measure.eqOn_open_of_ae_eq he (isOpen_vec3Ball 0 1)
    (unitBallFullHarmonicForcePressureRepresentative_contDiff (F + G)).continuousOn
    ((unitBallFullHarmonicForcePressureRepresentative_contDiff F).continuousOn.add
      (unitBallFullHarmonicForcePressureRepresentative_contDiff G).continuousOn)

/-- Actual pressure-class scaling identifies the true full-ball representatives. -/
theorem unitBallFullHarmonicForcePressureRepresentative_smul (c : ℝ)
    (F : unitBallGradientFreeForce) :
    EqOn (unitBallFullHarmonicForcePressureRepresentative (c • F))
      (c • unitBallFullHarmonicForcePressureRepresentative F) (vec3Ball 0 1) := by
  have hc : unitBallHarmonicForcePressureClassL (c • F) =ᵐ[volume.restrict (vec3Ball 0 1)]
      (fun x ↦ c • unitBallHarmonicForcePressureClassL F x) := by
    rw [map_smul]
    exact Lp.coeFn_smul c _
  have he := (unitBallFullHarmonicForcePressureRepresentative_ae (c • F)).symm.trans
    (hc.trans ((unitBallFullHarmonicForcePressureRepresentative_ae F).const_smul c))
  exact Measure.eqOn_open_of_ae_eq he (isOpen_vec3Ball 0 1)
    (unitBallFullHarmonicForcePressureRepresentative_contDiff (c • F)).continuousOn
    ((unitBallFullHarmonicForcePressureRepresentative_contDiff F).continuousOn.const_smul c)

/-- The actual force-to-gradient coefficient at a given boundary margin. -/
def fullBallHarmonicForceGradientCoefficient (ρ : ℝ) : ℝ :=
  fullBallHarmonicGradientConstant ρ *
    (4 * (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 6 : ℝ))

/-- The true gradient coefficient is nonnegative for each interior radius. -/
theorem fullBallHarmonicForceGradientCoefficient_nonneg {ρ : ℝ} (hρ : ρ < 1) :
    0 ≤ fullBallHarmonicForceGradientCoefficient ρ :=
  mul_nonneg (fullBallHarmonicGradientConstant_nonneg hρ)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg ENNReal.toReal_nonneg _))

variable (K : Set Vec3) [CompactSpace K] (hK : K ⊆ vec3Ball 0 1)

/-- The literal continuous harmonic gradient on an arbitrary compact interior. -/
def fullBallHarmonicGradientMap (F : unitBallGradientFreeForce) : C(K, Vec3) where
  toFun := fun x ↦ classicalGradient (unitBallFullHarmonicForcePressureRepresentative F) x.1
  continuous_toFun := by
    have hreg := unitBallFullHarmonicForcePressureRepresentative_contDiff F
    have h := hreg.continuousOn_fderiv_of_isOpen (isOpen_vec3Ball 0 1) (by norm_num)
    apply continuous_pi
    intro i
    exact continuousOn_iff_continuous_domRestrict.mp
      ((h.clm_apply (g := fun _ ↦ basisVec i) continuousOn_const).mono hK)

omit [CompactSpace K] in
/-- The actual full-ball gradient fields preserve force addition. -/
theorem fullBallHarmonicGradientMap_add (F G : unitBallGradientFreeForce) :
    fullBallHarmonicGradientMap K hK (F + G) =
      fullBallHarmonicGradientMap K hK F + fullBallHarmonicGradientMap K hK G := by
  ext x i
  have hx := hK x.property
  have he := classicalGradient_eqOn_of_eqOn (isOpen_vec3Ball 0 1)
    (unitBallFullHarmonicForcePressureRepresentative_add F G) hx
  have hF := ((unitBallFullHarmonicForcePressureRepresentative_contDiff F).differentiableOn
    (by norm_num)).differentiableAt ((isOpen_vec3Ball 0 1).mem_nhds hx)
  have hG := ((unitBallFullHarmonicForcePressureRepresentative_contDiff G).differentiableOn
    (by norm_num)).differentiableAt ((isOpen_vec3Ball 0 1).mem_nhds hx)
  change spatialDeriv (unitBallFullHarmonicForcePressureRepresentative (F + G)) i x.1 = _
  rw [show spatialDeriv (unitBallFullHarmonicForcePressureRepresentative (F + G)) i x.1 =
    spatialDeriv (unitBallFullHarmonicForcePressureRepresentative F +
      unitBallFullHarmonicForcePressureRepresentative G) i x.1 from
        congrArg (fun g : Vec3 ↦ g i) he]
  simp only [spatialDeriv, fderiv_add hF hG, add_apply]
  rfl

omit [CompactSpace K] in
/-- The actual full-ball gradient fields preserve real force scaling. -/
theorem fullBallHarmonicGradientMap_smul (c : ℝ) (F : unitBallGradientFreeForce) :
    fullBallHarmonicGradientMap K hK (c • F) = c • fullBallHarmonicGradientMap K hK F := by
  ext x i
  have hx := hK x.property
  have he := classicalGradient_eqOn_of_eqOn (isOpen_vec3Ball 0 1)
    (unitBallFullHarmonicForcePressureRepresentative_smul c F) hx
  have hF := ((unitBallFullHarmonicForcePressureRepresentative_contDiff F).differentiableOn
    (by norm_num)).differentiableAt ((isOpen_vec3Ball 0 1).mem_nhds hx)
  change spatialDeriv (unitBallFullHarmonicForcePressureRepresentative (c • F)) i x.1 = _
  rw [show spatialDeriv (unitBallFullHarmonicForcePressureRepresentative (c • F)) i x.1 =
    spatialDeriv (c • unitBallFullHarmonicForcePressureRepresentative F) i x.1 from
      congrArg (fun g : Vec3 ↦ g i) he]
  simp only [spatialDeriv, fderiv_const_smul hF, smul_apply, smul_eq_mul]
  rfl

/-- The actual continuous gradient obeys the literal boundary-margin force bound. -/
theorem fullBallHarmonicGradientMap_norm_le {ρ : ℝ} (hρ : ρ < 1)
    (hKρ : K ⊆ vec3Ball 0 ρ) (F : unitBallGradientFreeForce) :
    ‖fullBallHarmonicGradientMap K hK F‖ ≤ fullBallHarmonicForceGradientCoefficient ρ * ‖F‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (fullBallHarmonicForceGradientCoefficient_nonneg hρ) (norm_nonneg F))).mpr
  intro x
  have hb := fullBallHarmonic_representative_gradient_bound
    (unitBallPressureFunction_memLp_threeHalves F.1)
    (unitBallStokesPressure_weaklyHarmonic F.1 F.property)
    (unitBallFullHarmonicForcePressureRepresentative_contDiff F)
    (unitBallFullHarmonicForcePressureRepresentative_ae F) hρ (hKρ x.property)
  apply (norm_le_vec3EuclideanNorm _).trans (hb.trans _)
  have hl := mul_le_mul_of_nonneg_left (unitBallPressureFunction_lpNorm_threeHalves_le F.1)
    (fullBallHarmonicGradientConstant_nonneg hρ)
  simpa only [fullBallHarmonicForceGradientCoefficient, unitBallGradientFreeForce_norm_coe,
    mul_assoc] using hl

/-- A genuine bounded linear harmonic gradient operator on every compact interior. -/
def fullBallHarmonicGradient {ρ : ℝ} (hρ : ρ < 1) (hKρ : K ⊆ vec3Ball 0 ρ) :
    unitBallGradientFreeForce →L[ℝ] C(K, Vec3) :=
  ({ toFun := fullBallHarmonicGradientMap K hK
     map_add' := fullBallHarmonicGradientMap_add K hK
     map_smul' := fullBallHarmonicGradientMap_smul K hK } :
       unitBallGradientFreeForce →ₗ[ℝ] C(K, Vec3)).mkContinuous
    (fullBallHarmonicForceGradientCoefficient ρ)
    (fullBallHarmonicGradientMap_norm_le K hK hρ hKρ)

end FluidSingularSets
