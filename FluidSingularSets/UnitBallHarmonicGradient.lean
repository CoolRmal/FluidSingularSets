-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StokesVectorForceLinear
public import FluidSingularSets.StokesVectorPressureBounds
public import FluidSingularSets.UnitBallPressureProjection
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Canonical bounded interior harmonic pressure gradient

The source space is genuine Hilbert L² with Euclidean vector values. The
divergence-free subspace is the closed intersection of actual scalar-gradient
test kernels. The constructed pressure has a genuine C² representative, whose
gradient is uniquely determined on the interior. True pressure linearity and
the proved Weyl bounds make that gradient a bounded linear operator.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual Hilbert space of Euclidean vector L² sources on the unit ball. -/
abbrev UnitBallVectorL2 := Lp L2Vec3 2 (volume.restrict (vec3Ball (0 : Vec3) 1))

/-- Actual Euclidean vector coordinates as a continuous linear map. -/
def unitBallVectorCoordinates : UnitBallVectorL2 →L[ℝ]
    Lp Vec3 2 (volume.restrict (vec3Ball 0 1)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).toContinuousLinearMap.compLpL
    2 (volume.restrict (vec3Ball 0 1))

theorem unitBallVectorCoordinates_norm_le (u : UnitBallVectorL2) :
    ‖unitBallVectorCoordinates u‖ ≤ ‖u‖ := by
  have hL : ‖(PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin 3 ↦ ℝ)).toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    rw [one_mul]
    apply pi_norm_le_iff_of_nonneg (norm_nonneg v) |>.mpr
    intro i
    exact PiLp.norm_apply_le v i
  have hc : ‖unitBallVectorCoordinates‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans hL
  exact ((unitBallVectorCoordinates).le_opNorm u).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg u))

/-- The actual force of a genuine Hilbert vector source. -/
def unitBallHilbertVectorForce : UnitBallVectorL2 →L[ℝ] StokesEnergyForce (vec3Ball 0 1) :=
  (stokesVectorForceL (vec3Ball 0 1)).comp unitBallVectorCoordinates

@[simp]
theorem unitBallHilbertVectorForce_apply (u : UnitBallVectorL2) :
    unitBallHilbertVectorForce u = stokesVectorForce (vec3Ball 0 1)
      (unitBallVectorCoordinates u) := by
  simp only [unitBallHilbertVectorForce, ContinuousLinearMap.comp_apply,
    stokesVectorForceL_apply]

/-- The actual weak divergence-free Hilbert source space. -/
def unitBallDivergenceFreeL2 : ClosedSubmodule ℝ UnitBallVectorL2 where
  toSubmodule :=
    { carrier := {u | ∀ ψ : WeakTestFunction (vec3Ball 0 1),
        unitBallHilbertVectorForce u (stokesEnergyTest (stokesScalarGradientTest ψ)) = 0}
      zero_mem' := by
        intro ψ
        rw [map_zero]
        rfl
      add_mem' := by
        intro u v hu hv ψ
        simp only [map_add, add_apply, hu ψ, hv ψ, add_zero]
      smul_mem' := by
        intro c u hu ψ
        simp only [map_smul, smul_apply, hu ψ, smul_zero] }
  isClosed' := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro ψ
    exact isClosed_eq (((ContinuousLinearMap.apply ℝ ℝ
      (stokesEnergyTest (stokesScalarGradientTest ψ))).continuous).comp
        unitBallHilbertVectorForce.continuous) continuous_const

/-- The genuine closed kernels are exactly the literal distributional divergence condition. -/
theorem unitBallDivergenceFreeL2_mem_iff (u : UnitBallVectorL2) :
    u ∈ unitBallDivergenceFreeL2 ↔
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball 0 1 →
          (∫ x in vec3Ball 0 1, ∑ i : Fin 3,
            unitBallVectorCoordinates u x i * spatialDeriv ψ i x) = 0 := by
  change (∀ ψ : WeakTestFunction (vec3Ball 0 1),
    unitBallHilbertVectorForce u (stokesEnergyTest (stokesScalarGradientTest ψ)) = 0) ↔ _
  constructor
  · intro hu ψ hψ hc hs
    let Ψ : WeakTestFunction (vec3Ball 0 1) := ⟨ψ, hψ, hc, hs⟩
    have h := hu Ψ
    rw [unitBallHilbertVectorForce_apply, stokesVectorForce_test
      (isOpen_vec3Ball 0 1).measurableSet volume_vec3Ball_lt_top.ne] at h
    exact h
  · intro hu Ψ
    rw [unitBallHilbertVectorForce_apply, stokesVectorForce_test
      (isOpen_vec3Ball 0 1).measurableSet volume_vec3Ball_lt_top.ne]
    exact hu Ψ Ψ.contDiff Ψ.hasCompactSupport Ψ.tsupport_subset

/-- The genuine pressure class depends continuously and linearly on the true source. -/
def unitBallHarmonicPressureClassL : unitBallDivergenceFreeL2 →L[ℝ]
    Lp ℝ 2 (volume.restrict (vec3Ball 0 1)) :=
  (unitBallMeanZeroL2.toSubmodule.subtypeL).comp
    (unitBallStokesPressureL.comp
      (unitBallHilbertVectorForce.comp unitBallDivergenceFreeL2.toSubmodule.subtypeL))

theorem unitBallHarmonicPressure_exists (u : unitBallDivergenceFreeL2) :
    ∃ H : Vec3 → ℝ, ContDiffOn ℝ (2 : ℕ∞) H (vec3Ball 0 (1 / 4)) ∧
      unitBallHarmonicPressureClassL u =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))] H := by
  exact exists_unitBallStokesPressure_C2_representative (unitBallHilbertVectorForce u.1)
    u.property

/-- A chosen actual C² representative; its interior derivatives are uniquely determined. -/
def unitBallHarmonicPressureRepresentative (u : unitBallDivergenceFreeL2) : Vec3 → ℝ :=
  Classical.choose (unitBallHarmonicPressure_exists u)

theorem unitBallHarmonicPressureRepresentative_contDiff (u : unitBallDivergenceFreeL2) :
    ContDiffOn ℝ (2 : ℕ∞) (unitBallHarmonicPressureRepresentative u) (vec3Ball 0 (1 / 4)) :=
  (Classical.choose_spec (unitBallHarmonicPressure_exists u)).1

theorem unitBallHarmonicPressureRepresentative_ae (u : unitBallDivergenceFreeL2) :
    unitBallHarmonicPressureClassL u =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))]
      unitBallHarmonicPressureRepresentative u :=
  (Classical.choose_spec (unitBallHarmonicPressure_exists u)).2

/-- True pressure linearity identifies the actual chosen representatives under addition. -/
theorem unitBallHarmonicPressureRepresentative_add (u v : unitBallDivergenceFreeL2) :
    EqOn (unitBallHarmonicPressureRepresentative (u + v))
      (unitBallHarmonicPressureRepresentative u + unitBallHarmonicPressureRepresentative v)
      (vec3Ball 0 (1 / 4)) := by
  have hc : unitBallHarmonicPressureClassL (u + v) =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))]
      (fun x ↦ unitBallHarmonicPressureClassL u x + unitBallHarmonicPressureClassL v x) := by
    rw [map_add]
    exact ae_restrict_of_ae_restrict_of_subset (vec3Ball_mono (by norm_num : (1 / 4 : ℝ) ≤ 1))
      (Lp.coeFn_add _ _)
  have he := (unitBallHarmonicPressureRepresentative_ae (u + v)).symm.trans
    (hc.trans ((unitBallHarmonicPressureRepresentative_ae u).add
      (unitBallHarmonicPressureRepresentative_ae v)))
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq he (isOpen_vec3Ball 0 (1 / 4))
    (unitBallHarmonicPressureRepresentative_contDiff (u + v)).continuousOn
    ((unitBallHarmonicPressureRepresentative_contDiff u).continuousOn.add
      (unitBallHarmonicPressureRepresentative_contDiff v).continuousOn)

/-- True pressure linearity identifies the actual representatives under real scaling. -/
theorem unitBallHarmonicPressureRepresentative_smul (c : ℝ) (u : unitBallDivergenceFreeL2) :
    EqOn (unitBallHarmonicPressureRepresentative (c • u))
      (c • unitBallHarmonicPressureRepresentative u) (vec3Ball 0 (1 / 4)) := by
  have hc : unitBallHarmonicPressureClassL (c • u) =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))]
      (fun x ↦ c • unitBallHarmonicPressureClassL u x) := by
    rw [map_smul]
    exact ae_restrict_of_ae_restrict_of_subset (vec3Ball_mono (by norm_num : (1 / 4 : ℝ) ≤ 1))
      (Lp.coeFn_smul c _)
  have he := (unitBallHarmonicPressureRepresentative_ae (c • u)).symm.trans
    (hc.trans ((unitBallHarmonicPressureRepresentative_ae u).const_smul c))
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq he (isOpen_vec3Ball 0 (1 / 4))
    (unitBallHarmonicPressureRepresentative_contDiff (c • u)).continuousOn
    ((unitBallHarmonicPressureRepresentative_contDiff u).continuousOn.const_smul c)

/-- The fixed genuinely compact inner ball on which the gradient is continuous. -/
def unitBallPressureCompactInterior : Set Vec3 := closure (vec3Ball 0 (1 / 16))

instance unitBallPressureCompactInterior_compactSpace :
    CompactSpace unitBallPressureCompactInterior :=
  isCompact_iff_compactSpace.mp (isCompact_closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 16))

theorem unitBallPressureCompactInterior_subset :
    unitBallPressureCompactInterior ⊆ vec3Ball 0 (1 / 4) := by
  rw [unitBallPressureCompactInterior, closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 16)]
  intro x hx
  change vec3EuclideanNorm (x - 0) ≤ 1 / 16 at hx
  change vec3EuclideanNorm (x - 0) < 1 / 4
  exact hx.trans_lt (by norm_num : (1 / 16 : ℝ) < 1 / 4)

/-- The actual continuous gradient on the fixed compact inner ball. -/
def unitBallHarmonicGradientMap (u : unitBallDivergenceFreeL2) :
    C(unitBallPressureCompactInterior, Vec3) where
  toFun := fun x ↦ classicalGradient (unitBallHarmonicPressureRepresentative u) x.1
  continuous_toFun := by
    have h := (unitBallHarmonicPressureRepresentative_contDiff u).continuousOn_fderiv_of_isOpen
      (isOpen_vec3Ball 0 (1 / 4)) (by norm_num)
    apply continuous_pi
    intro i
    exact continuousOn_iff_continuous_domRestrict.mp
      ((h.clm_apply (g := fun _ ↦ basisVec i) continuousOn_const).mono
        unitBallPressureCompactInterior_subset)

theorem unitBallHarmonicGradientMap_add (u v : unitBallDivergenceFreeL2) :
    unitBallHarmonicGradientMap (u + v) = unitBallHarmonicGradientMap u +
      unitBallHarmonicGradientMap v := by
  ext x i
  have he := classicalGradient_eqOn_of_eqOn (isOpen_vec3Ball 0 (1 / 4))
    (unitBallHarmonicPressureRepresentative_add u v)
      (unitBallPressureCompactInterior_subset x.property)
  have hx := unitBallPressureCompactInterior_subset x.property
  have hu := ((unitBallHarmonicPressureRepresentative_contDiff u).differentiableOn
    (by norm_num)).differentiableAt ((isOpen_vec3Ball 0 (1 / 4)).mem_nhds hx)
  have hv := ((unitBallHarmonicPressureRepresentative_contDiff v).differentiableOn
    (by norm_num)).differentiableAt ((isOpen_vec3Ball 0 (1 / 4)).mem_nhds hx)
  change spatialDeriv (unitBallHarmonicPressureRepresentative (u + v)) i x.1 = _
  rw [show spatialDeriv (unitBallHarmonicPressureRepresentative (u + v)) i x.1 =
    spatialDeriv (unitBallHarmonicPressureRepresentative u +
      unitBallHarmonicPressureRepresentative v) i x.1 from congrArg (fun g : Vec3 ↦ g i) he]
  simp only [spatialDeriv, fderiv_add hu hv, add_apply]
  rfl

theorem unitBallHarmonicGradientMap_smul (c : ℝ) (u : unitBallDivergenceFreeL2) :
    unitBallHarmonicGradientMap (c • u) = c • unitBallHarmonicGradientMap u := by
  ext x i
  have he := classicalGradient_eqOn_of_eqOn (isOpen_vec3Ball 0 (1 / 4))
    (unitBallHarmonicPressureRepresentative_smul c u)
      (unitBallPressureCompactInterior_subset x.property)
  have hx := unitBallPressureCompactInterior_subset x.property
  have hu := ((unitBallHarmonicPressureRepresentative_contDiff u).differentiableOn
    (by norm_num)).differentiableAt ((isOpen_vec3Ball 0 (1 / 4)).mem_nhds hx)
  change spatialDeriv (unitBallHarmonicPressureRepresentative (c • u)) i x.1 = _
  rw [show spatialDeriv (unitBallHarmonicPressureRepresentative (c • u)) i x.1 =
    spatialDeriv (c • unitBallHarmonicPressureRepresentative u) i x.1 from
      congrArg (fun g : Vec3 ↦ g i) he]
  simp only [spatialDeriv, fderiv_const_smul hu, smul_apply, smul_eq_mul]
  rfl

theorem unitBallHarmonicGradientMap_norm_le (u : unitBallDivergenceFreeL2) :
    ‖unitBallHarmonicGradientMap u‖ ≤ stokesVectorPressureGradientConstant * ‖u‖ := by
  have hb := unitBallPressure_representative_derivative_bounds
    (unitBallHilbertVectorForce u.1)
    (unitBallStokesPressure_weaklyHarmonic _ u.property)
    (unitBallHarmonicPressureRepresentative u) (unitBallHarmonicPressureRepresentative_contDiff u)
    (unitBallHarmonicPressureRepresentative_ae u)
  have hf := stokesVectorForce_norm_le (isOpen_vec3Ball 0 1).measurableSet
    volume_vec3Ball_lt_top.ne (unitBallVectorCoordinates u.1)
  rw [← unitBallHilbertVectorForce_apply] at hf
  apply (ContinuousMap.norm_le _
    (mul_nonneg stokesVectorPressureGradientConstant_nonneg (norm_nonneg u))).mpr
  intro x
  have h := (CKN.space_norm_le_euclideanNorm
    (classicalGradient (unitBallHarmonicPressureRepresentative u) x.1)).trans
      (hb.1 x.1 (unitBallPressureCompactInterior_subset x.property))
  change ‖classicalGradient (unitBallHarmonicPressureRepresentative u) x.1‖ ≤ _
  refine h.trans ((mul_le_mul_of_nonneg_left hf unitBallPressureGradientConstant_nonneg).trans ?_)
  change unitBallPressureGradientConstant *
    (3 * (stokesTestPoincareConstant (vec3Ball 0 1)).toReal *
      ‖unitBallVectorCoordinates u.1‖) ≤ _
  simpa only [stokesVectorPressureGradientConstant, mul_assoc, ClosedSubmodule.norm_coe] using
    mul_le_mul_of_nonneg_left (unitBallVectorCoordinates_norm_le u.1)
      stokesVectorPressureGradientConstant_nonneg

/-- The actual bounded linear interior harmonic-pressure gradient. -/
def unitBallHarmonicGradient : unitBallDivergenceFreeL2 →L[ℝ]
    C(unitBallPressureCompactInterior, Vec3) :=
  ({ toFun := unitBallHarmonicGradientMap
     map_add' := unitBallHarmonicGradientMap_add
     map_smul' := unitBallHarmonicGradientMap_smul } :
       unitBallDivergenceFreeL2 →ₗ[ℝ] C(unitBallPressureCompactInterior, Vec3)).mkContinuous
    stokesVectorPressureGradientConstant unitBallHarmonicGradientMap_norm_le

end FluidSingularSets
