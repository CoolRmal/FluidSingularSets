-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallHarmonicGradient
public import FluidSingularSets.LocalHessianCalculus

/-!
# Actual harmonic pressure gradients of energy-dual forces

The domain is the closed space of genuine energy-dual forces annihilating
compact scalar gradient tests. The actual constructed Stokes pressure is
harmonic, and its unique interior gradient is a bounded linear map into
continuous vector fields. No spatial L² representative of the force is needed.
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

-- Pin the canonical operator-space instances before restricting the force domain.
local instance harmonicForceGradientForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance harmonicForceGradientForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- Actual energy-dual forces annihilating all compact scalar gradient tests. -/
def unitBallGradientFreeForce : ClosedSubmodule ℝ (StokesEnergyForce (vec3Ball 0 1)) where
  toSubmodule :=
    { carrier := {F | ∀ ψ : WeakTestFunction (vec3Ball 0 1),
        F (stokesEnergyTest (stokesScalarGradientTest ψ)) = 0}
      zero_mem' := by
        intro ψ
        rfl
      add_mem' := by
        intro F G hF hG ψ
        simp only [add_apply, hF ψ, hG ψ, add_zero]
      smul_mem' := by
        intro c F hF ψ
        simp only [smul_apply, hF ψ, smul_zero] }
  isClosed' := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro ψ
    exact isClosed_eq (ContinuousLinearMap.apply ℝ ℝ
      (stokesEnergyTest (stokesScalarGradientTest ψ))).continuous continuous_const

instance unitBallGradientFreeForce_normedAddCommGroup :
    NormedAddCommGroup unitBallGradientFreeForce :=
  inferInstanceAs (NormedAddCommGroup unitBallGradientFreeForce.toSubmodule)

instance unitBallGradientFreeForce_normedSpace : NormedSpace ℝ unitBallGradientFreeForce :=
  inferInstanceAs (NormedSpace ℝ unitBallGradientFreeForce.toSubmodule)

instance unitBallGradientFreeForce_completeSpace : CompleteSpace unitBallGradientFreeForce :=
  inferInstance

@[simp, norm_cast]
theorem unitBallGradientFreeForce_norm_coe (F : unitBallGradientFreeForce) :
    ‖(F : StokesEnergyForce (vec3Ball 0 1))‖ = ‖F‖ := rfl

/-- The genuine pressure class depends continuously and linearly on the true source. -/
def unitBallHarmonicForcePressureClassL : unitBallGradientFreeForce →L[ℝ]
    Lp ℝ 2 (volume.restrict (vec3Ball 0 1)) :=
  (unitBallMeanZeroL2.toSubmodule.subtypeL).comp
    (unitBallStokesPressureL.comp
      unitBallGradientFreeForce.toSubmodule.subtypeL)

theorem unitBallHarmonicForcePressure_exists (u : unitBallGradientFreeForce) :
    ∃ H : Vec3 → ℝ, ContDiffOn ℝ (2 : ℕ∞) H (vec3Ball 0 (1 / 4)) ∧
      unitBallHarmonicForcePressureClassL u =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))] H := by
  exact exists_unitBallStokesPressure_C2_representative u.1
    u.property

/-- A chosen actual C² representative; its interior derivatives are uniquely determined. -/
def unitBallHarmonicForcePressureRepresentative (u : unitBallGradientFreeForce) : Vec3 → ℝ :=
  Classical.choose (unitBallHarmonicForcePressure_exists u)

theorem unitBallHarmonicForcePressureRepresentative_contDiff (u : unitBallGradientFreeForce) :
    ContDiffOn ℝ (2 : ℕ∞) (unitBallHarmonicForcePressureRepresentative u) (vec3Ball 0 (1 / 4)) :=
  (Classical.choose_spec (unitBallHarmonicForcePressure_exists u)).1

theorem unitBallHarmonicForcePressureRepresentative_ae (u : unitBallGradientFreeForce) :
    unitBallHarmonicForcePressureClassL u =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))]
      unitBallHarmonicForcePressureRepresentative u :=
  (Classical.choose_spec (unitBallHarmonicForcePressure_exists u)).2

/-- True pressure linearity identifies the actual chosen representatives under addition. -/
theorem unitBallHarmonicForcePressureRepresentative_add (u v : unitBallGradientFreeForce) :
    EqOn (unitBallHarmonicForcePressureRepresentative (u + v))
      (unitBallHarmonicForcePressureRepresentative u +
        unitBallHarmonicForcePressureRepresentative v)
      (vec3Ball 0 (1 / 4)) := by
  have hc : unitBallHarmonicForcePressureClassL (u + v) =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))]
      (fun x ↦ unitBallHarmonicForcePressureClassL u x +
        unitBallHarmonicForcePressureClassL v x) := by
    rw [map_add]
    exact ae_restrict_of_ae_restrict_of_subset (vec3Ball_mono (by norm_num : (1 / 4 : ℝ) ≤ 1))
      (Lp.coeFn_add _ _)
  have he := (unitBallHarmonicForcePressureRepresentative_ae (u + v)).symm.trans
    (hc.trans ((unitBallHarmonicForcePressureRepresentative_ae u).add
      (unitBallHarmonicForcePressureRepresentative_ae v)))
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq he (isOpen_vec3Ball 0 (1 / 4))
    (unitBallHarmonicForcePressureRepresentative_contDiff (u + v)).continuousOn
    ((unitBallHarmonicForcePressureRepresentative_contDiff u).continuousOn.add
      (unitBallHarmonicForcePressureRepresentative_contDiff v).continuousOn)

/-- True pressure linearity identifies the actual representatives under real scaling. -/
theorem unitBallHarmonicForcePressureRepresentative_smul (c : ℝ) (u : unitBallGradientFreeForce) :
    EqOn (unitBallHarmonicForcePressureRepresentative (c • u))
      (c • unitBallHarmonicForcePressureRepresentative u) (vec3Ball 0 (1 / 4)) := by
  have hc : unitBallHarmonicForcePressureClassL (c • u) =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))]
      (fun x ↦ c • unitBallHarmonicForcePressureClassL u x) := by
    rw [map_smul]
    exact ae_restrict_of_ae_restrict_of_subset (vec3Ball_mono (by norm_num : (1 / 4 : ℝ) ≤ 1))
      (Lp.coeFn_smul c _)
  have he := (unitBallHarmonicForcePressureRepresentative_ae (c • u)).symm.trans
    (hc.trans ((unitBallHarmonicForcePressureRepresentative_ae u).const_smul c))
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq he (isOpen_vec3Ball 0 (1 / 4))
    (unitBallHarmonicForcePressureRepresentative_contDiff (c • u)).continuousOn
    ((unitBallHarmonicForcePressureRepresentative_contDiff u).continuousOn.const_smul c)

/-- The actual continuous gradient on the fixed compact inner ball. -/
def unitBallHarmonicForceGradientMap (u : unitBallGradientFreeForce) :
    C(unitBallPressureCompactInterior, Vec3) where
  toFun := fun x ↦ classicalGradient (unitBallHarmonicForcePressureRepresentative u) x.1
  continuous_toFun := by
    have h := (unitBallHarmonicForcePressureRepresentative_contDiff u).continuousOn_fderiv_of_isOpen
      (isOpen_vec3Ball 0 (1 / 4)) (by norm_num)
    apply continuous_pi
    intro i
    exact continuousOn_iff_continuous_domRestrict.mp
      ((h.clm_apply (g := fun _ ↦ basisVec i) continuousOn_const).mono
        unitBallPressureCompactInterior_subset)

theorem unitBallHarmonicForceGradientMap_add (u v : unitBallGradientFreeForce) :
    unitBallHarmonicForceGradientMap (u + v) = unitBallHarmonicForceGradientMap u +
      unitBallHarmonicForceGradientMap v := by
  ext x i
  have he := classicalGradient_eqOn_of_eqOn (isOpen_vec3Ball 0 (1 / 4))
    (unitBallHarmonicForcePressureRepresentative_add u v)
      (unitBallPressureCompactInterior_subset x.property)
  have hx := unitBallPressureCompactInterior_subset x.property
  have hu := ((unitBallHarmonicForcePressureRepresentative_contDiff u).differentiableOn
    (by norm_num)).differentiableAt ((isOpen_vec3Ball 0 (1 / 4)).mem_nhds hx)
  have hv := ((unitBallHarmonicForcePressureRepresentative_contDiff v).differentiableOn
    (by norm_num)).differentiableAt ((isOpen_vec3Ball 0 (1 / 4)).mem_nhds hx)
  change spatialDeriv (unitBallHarmonicForcePressureRepresentative (u + v)) i x.1 = _
  rw [show spatialDeriv (unitBallHarmonicForcePressureRepresentative (u + v)) i x.1 =
    spatialDeriv (unitBallHarmonicForcePressureRepresentative u +
      unitBallHarmonicForcePressureRepresentative v) i x.1 from congrArg (fun g : Vec3 ↦ g i) he]
  simp only [spatialDeriv, fderiv_add hu hv, add_apply]
  rfl

theorem unitBallHarmonicForceGradientMap_smul (c : ℝ) (u : unitBallGradientFreeForce) :
    unitBallHarmonicForceGradientMap (c • u) = c • unitBallHarmonicForceGradientMap u := by
  ext x i
  have he := classicalGradient_eqOn_of_eqOn (isOpen_vec3Ball 0 (1 / 4))
    (unitBallHarmonicForcePressureRepresentative_smul c u)
      (unitBallPressureCompactInterior_subset x.property)
  have hx := unitBallPressureCompactInterior_subset x.property
  have hu := ((unitBallHarmonicForcePressureRepresentative_contDiff u).differentiableOn
    (by norm_num)).differentiableAt ((isOpen_vec3Ball 0 (1 / 4)).mem_nhds hx)
  change spatialDeriv (unitBallHarmonicForcePressureRepresentative (c • u)) i x.1 = _
  rw [show spatialDeriv (unitBallHarmonicForcePressureRepresentative (c • u)) i x.1 =
    spatialDeriv (c • unitBallHarmonicForcePressureRepresentative u) i x.1 from
      congrArg (fun g : Vec3 ↦ g i) he]
  simp only [spatialDeriv, fderiv_const_smul hu, smul_apply, smul_eq_mul]
  rfl

theorem unitBallHarmonicForceGradientMap_norm_le (F : unitBallGradientFreeForce) :
    ‖unitBallHarmonicForceGradientMap F‖ ≤ unitBallPressureGradientConstant * ‖F‖ := by
  have hb := unitBallPressure_representative_derivative_bounds F.1
    (unitBallStokesPressure_weaklyHarmonic _ F.property)
    (unitBallHarmonicForcePressureRepresentative F)
    (unitBallHarmonicForcePressureRepresentative_contDiff F)
    (unitBallHarmonicForcePressureRepresentative_ae F)
  apply (ContinuousMap.norm_le _
    (mul_nonneg unitBallPressureGradientConstant_nonneg (norm_nonneg F))).mpr
  intro x
  exact (CKN.space_norm_le_euclideanNorm
    (classicalGradient (unitBallHarmonicForcePressureRepresentative F) x.1)).trans
      (hb.1 x.1 (unitBallPressureCompactInterior_subset x.property))

/-- The genuine bounded linear pressure-gradient operator on energy-dual forces. -/
def unitBallHarmonicForceGradient : unitBallGradientFreeForce →L[ℝ]
    C(unitBallPressureCompactInterior, Vec3) :=
  ({ toFun := unitBallHarmonicForceGradientMap
     map_add' := unitBallHarmonicForceGradientMap_add
     map_smul' := unitBallHarmonicForceGradientMap_smul } :
       unitBallGradientFreeForce →ₗ[ℝ] C(unitBallPressureCompactInterior, Vec3)).mkContinuous
    unitBallPressureGradientConstant unitBallHarmonicForceGradientMap_norm_le

@[simp]
theorem unitBallHarmonicForceGradient_apply (F : unitBallGradientFreeForce)
    (x : unitBallPressureCompactInterior) :
    unitBallHarmonicForceGradient F x =
      classicalGradient (unitBallHarmonicForcePressureRepresentative F) x.1 := rfl

theorem unitBallHarmonicForceGradient_norm_le (F : unitBallGradientFreeForce) :
    ‖unitBallHarmonicForceGradient F‖ ≤ unitBallPressureGradientConstant * ‖F‖ :=
  unitBallHarmonicForceGradientMap_norm_le F

theorem unitBallHarmonicForceGradient_opNorm_le :
    ‖unitBallHarmonicForceGradient‖ ≤ unitBallPressureGradientConstant :=
  ContinuousLinearMap.opNorm_le_bound _ unitBallPressureGradientConstant_nonneg
    unitBallHarmonicForceGradient_norm_le

/-- The actual force pressure is represented by the constructed C² function. -/
theorem unitBallHarmonicForcePressureRepresentative_pressure_ae (F : unitBallGradientFreeForce) :
    unitBallPressureFunction F.1 =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))]
      unitBallHarmonicForcePressureRepresentative F :=
  unitBallHarmonicForcePressureRepresentative_ae F

/-- The representative is genuinely harmonic by the true Stokes gradient-test equation. -/
theorem unitBallHarmonicForcePressureRepresentative_weaklyHarmonic
    (F : unitBallGradientFreeForce) :
    WeaklyHarmonicOn (vec3Ball 0 (1 / 4)) (unitBallHarmonicForcePressureRepresentative F) :=
  localWeaklyHarmonicOn_congr_ae (unitBallHarmonicForcePressureRepresentative_pressure_ae F)
    (localWeaklyHarmonicOn_restrict (vec3Ball_mono (by norm_num))
      (unitBallStokesPressure_weaklyHarmonic F.1 F.property))

/-- The canonical gradient is the literal weak derivative of the true pressure class. -/
theorem unitBallHarmonicForcePressureRepresentative_derivative_pairing
    (F : unitBallGradientFreeForce) (i : Fin 3)
    (ψ : WeakTestFunction (vec3Ball 0 (1 / 4))) :
    (∫ x in vec3Ball 0 (1 / 4),
      classicalGradient (unitBallHarmonicForcePressureRepresentative F) x i * ψ x) =
      -(∫ x in vec3Ball 0 (1 / 4), unitBallPressureFunction F.1 x *
        spatialDeriv ψ.toFun i x) := by
  have h := hasWeakGradientOn_of_contDiffOn (isOpen_vec3Ball 0 (1 / 4))
    ((unitBallHarmonicForcePressureRepresentative_contDiff F).of_le (by norm_num))
    i ψ.toFun ψ.contDiff ψ.hasCompactSupport ψ.tsupport_subset
  change (∫ x in vec3Ball 0 (1 / 4), unitBallHarmonicForcePressureRepresentative F x *
    spatialDeriv ψ.toFun i x) =
      -(∫ x in vec3Ball 0 (1 / 4),
        classicalGradient (unitBallHarmonicForcePressureRepresentative F) x i * ψ x) at h
  have hp : (∫ x in vec3Ball 0 (1 / 4), unitBallPressureFunction F.1 x *
      spatialDeriv ψ.toFun i x) =
      ∫ x in vec3Ball 0 (1 / 4), unitBallHarmonicForcePressureRepresentative F x *
        spatialDeriv ψ.toFun i x := by
    apply integral_congr_ae
    filter_upwards [unitBallHarmonicForcePressureRepresentative_pressure_ae F] with x hx
    rw [hx]
  rw [← hp] at h
  linarith

/-- The true pressure gradient is itself distributionally divergence-free. -/
theorem unitBallHarmonicForcePressureRepresentative_gradient_divergenceFree
    (F : unitBallGradientFreeForce) (ψ : WeakTestFunction (vec3Ball 0 (1 / 4))) :
    (∫ x in vec3Ball 0 (1 / 4), ∑ i : Fin 3,
      classicalGradient (unitBallHarmonicForcePressureRepresentative F) x i *
        spatialDeriv ψ.toFun i x) = 0 :=
  classicalGradient_weakly_divergenceFree_of_weaklyHarmonic
    (isOpen_vec3Ball 0 (1 / 4))
    ((unitBallHarmonicForcePressureRepresentative_contDiff F).of_le (by norm_num))
    (unitBallHarmonicForcePressureRepresentative_weaklyHarmonic F)
    ψ.toFun ψ.contDiff ψ.hasCompactSupport ψ.tsupport_subset

end FluidSingularSets
