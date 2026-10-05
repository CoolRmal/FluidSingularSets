-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallPressureProjection
public import FluidSingularSets.StokesNonlinearPressure
public import CKN.Setting.ScalingQuantities
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Affine transport of the genuine ball Stokes pressure

The affine change of variables is constructed on actual restricted spatial L²
classes. Its Jacobian and norm bound are proved from Haar measure, rather than
assumed as pressure or regularity estimates. These maps transport the genuine
unit-ball pressure construction to spatial balls of arbitrary positive radius.
-/

@[expose] public section

open CKN MeasureTheory MeasureTheory.Measure Set
open CKN.Foundation.Parabolic
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Native coordinates on the ball of center `x` and radius `r`. -/
def ballCoordinates (x : Vec3) (r : ℝ) : Vec3 → Vec3 := fun y ↦ r⁻¹ • (y - x)

/-- The positive-radius affine map is a genuine measurable embedding. -/
theorem ballAffine_measurableEmbedding (x : Vec3) {r : ℝ} (hr : 0 < r) :
    MeasurableEmbedding (CKN.spatialAffine r x) := by
  have h : CKN.spatialAffine r x = (fun y : Vec3 ↦ x + y) ∘
      (fun y : Vec3 ↦ (isUnit_iff_ne_zero.mpr hr.ne').unit • y) := by
    funext y
    simp [CKN.spatialAffine, Units.smul_def]
  rw [h]
  exact (Homeomorph.addLeft x).measurableEmbedding.comp
    (Homeomorph.smul (isUnit_iff_ne_zero.mpr hr.ne').unit).measurableEmbedding

/-- The inverse coordinate map is a genuine measurable embedding. -/
theorem ballCoordinates_measurableEmbedding (x : Vec3) {r : ℝ} (hr : 0 < r) :
    MeasurableEmbedding (ballCoordinates x r) := by
  have h : ballCoordinates x r =
      CKN.spatialAffine r⁻¹ (-(r⁻¹ • x)) := by
    funext y
    simp [ballCoordinates, CKN.spatialAffine, smul_sub]
    abel
  rw [h]
  exact ballAffine_measurableEmbedding _ (inv_pos.mpr hr)

@[simp]
theorem ballCoordinates_affine (x y : Vec3) {r : ℝ} (hr : 0 < r) :
    ballCoordinates x r (CKN.spatialAffine r x y) = y := by
  simp [ballCoordinates, CKN.spatialAffine, smul_smul, hr.ne']

@[simp]
theorem ballAffine_coordinates (x y : Vec3) {r : ℝ} (hr : 0 < r) :
    CKN.spatialAffine r x (ballCoordinates x r y) = y := by
  simp [ballCoordinates, CKN.spatialAffine, smul_smul, hr.ne']

/-- Affine scaling maps the unit spatial ball exactly onto the intended ball. -/
theorem ballAffine_preimage (x : Vec3) {r : ℝ} (hr : 0 < r) :
    CKN.spatialAffine r x ⁻¹' vec3Ball x r = vec3Ball 0 1 := by
  ext y
  simp only [mem_preimage, mem_vec3Ball, CKN.spatialAffine, add_sub_cancel_left,
    sub_zero, vec3EuclideanNorm_smul, abs_of_pos hr]
  exact mul_lt_iff_lt_one_right hr

/-- The inverse scaling has the reciprocal unit-ball preimage. -/
theorem ballCoordinates_preimage (x : Vec3) {r : ℝ} (hr : 0 < r) :
    ballCoordinates x r ⁻¹' vec3Ball 0 1 = vec3Ball x r := by
  ext y
  simp only [mem_preimage, mem_vec3Ball, ballCoordinates, sub_zero,
    vec3EuclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
  rw [inv_mul_lt_iff₀ hr]
  simp

/-- The genuine spatial Haar Jacobian for the affine coordinate change. -/
theorem map_ballAffine_volume (x : Vec3) {r : ℝ} (hr : 0 < r) :
    Measure.map (CKN.spatialAffine r x) (volume : Measure Vec3) =
      ENNReal.ofReal (r⁻¹ ^ 3) • volume := by
  have h : CKN.spatialAffine r x = (fun y : Vec3 ↦ x + y) ∘
      (fun y : Vec3 ↦ r • y) := rfl
  rw [h, ← Measure.map_map (measurable_const_add x) (measurable_const_smul r)]
  rw [Measure.map_addHaar_smul (μ := (volume : Measure Vec3)) hr.ne', Measure.map_smul]
  rw [MeasureTheory.map_add_left_eq_self]
  · congr 1
    rw [Module.finrank_fin_fun, abs_of_pos (inv_pos.mpr (pow_pos hr 3)), ← inv_pow]
  · exact (measurable_const_add x).aemeasurable

/-- The affine Jacobian holds on the actual restricted spatial balls. -/
theorem map_ballAffine_restrict (x : Vec3) {r : ℝ} (hr : 0 < r) :
    Measure.map (CKN.spatialAffine r x) (volume.restrict (vec3Ball 0 1)) =
      ENNReal.ofReal (r⁻¹ ^ 3) • volume.restrict (vec3Ball x r) := by
  have h := Measure.restrict_map (μ := (volume : Measure Vec3))
    (ballAffine_measurableEmbedding x hr).measurable (vec3Ball_measurable x r)
  rw [map_ballAffine_volume x hr, Measure.restrict_smul, ballAffine_preimage x hr] at h
  exact h.symm

/-- The inverse coordinate map has the physical spatial volume Jacobian. -/
theorem map_ballCoordinates_volume (x : Vec3) {r : ℝ} (hr : 0 < r) :
    Measure.map (ballCoordinates x r) (volume : Measure Vec3) =
      ENNReal.ofReal (r ^ 3) • volume := by
  have h : ballCoordinates x r = CKN.spatialAffine r⁻¹ (-(r⁻¹ • x)) := by
    funext y
    simp [ballCoordinates, CKN.spatialAffine, smul_sub]
    abel
  rw [h, map_ballAffine_volume _ (inv_pos.mpr hr), inv_inv]

/-- The inverse Jacobian holds on the actual physical spatial ball. -/
theorem map_ballCoordinates_restrict (x : Vec3) {r : ℝ} (hr : 0 < r) :
    Measure.map (ballCoordinates x r) (volume.restrict (vec3Ball x r)) =
      ENNReal.ofReal (r ^ 3) • volume.restrict (vec3Ball 0 1) := by
  have h := Measure.restrict_map (μ := (volume : Measure Vec3))
    (ballCoordinates_measurableEmbedding x hr).measurable (vec3Ball_measurable 0 1)
  rw [map_ballCoordinates_volume x hr, Measure.restrict_smul,
    ballCoordinates_preimage x hr] at h
  exact h.symm

/-- The affine spatial coordinate change as a genuine homeomorphism. -/
def ballAffineHomeomorph (x : Vec3) {r : ℝ} (hr : 0 < r) : Vec3 ≃ₜ Vec3 where
  toFun := CKN.spatialAffine r x
  invFun := ballCoordinates x r
  left_inv := fun y ↦ ballCoordinates_affine x y hr
  right_inv := fun y ↦ ballAffine_coordinates x y hr
  continuous_toFun := by unfold CKN.spatialAffine; fun_prop
  continuous_invFun := by unfold ballCoordinates; fun_prop

/-- Pullback of an actual physical compact smooth test to the actual unit ball. -/
def ballTestPullback (x : Vec3) {r : ℝ} (hr : 0 < r)
    (φ : WeakTestFunction (vec3Ball x r)) : WeakTestFunction (vec3Ball 0 1) where
  toFun := φ.toFun ∘ CKN.spatialAffine r x
  contDiff := φ.contDiff.comp (by unfold CKN.spatialAffine; fun_prop)
  hasCompactSupport := φ.hasCompactSupport.comp_homeomorph (ballAffineHomeomorph x hr)
  tsupport_subset := by
    change tsupport (φ.toFun ∘ ballAffineHomeomorph x hr) ⊆ _
    rw [tsupport_comp_eq_preimage φ.toFun (ballAffineHomeomorph x hr)]
    intro y hy
    have h := φ.tsupport_subset hy
    exact (Set.ext_iff.mp (ballAffine_preimage x hr) y).mp h

/-- The true chain rule for each coordinate of the transported compact test. -/
theorem ballTestPullback_partialDeriv (x : Vec3) {r : ℝ} (hr : 0 < r)
    (φ : WeakTestFunction (vec3Ball x r)) (i : Fin 3) (y : Vec3) :
    (ballTestPullback x hr φ).partialDeriv i y =
      r * φ.partialDeriv i (CKN.spatialAffine r x y) := by
  have ha := ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul r).const_add x
  have hφ := (φ.contDiff.differentiable (by simp)).differentiableAt
    (x := CKN.spatialAffine r x y) |>.hasFDerivAt
  have h := (hφ.comp y ha).fderiv
  change (fderiv ℝ (φ.toFun ∘ CKN.spatialAffine r x) y) (basisVec i) = _
  rw [h]
  simp [CKN.spatialAffine, WeakTestFunction.partialDeriv]

section L2Transport

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual affine pullback of physical L² data to unit coordinates. -/
def ballL2Pullback (x : Vec3) {r : ℝ} (hr : 0 < r) :
    Lp E 2 (volume.restrict (vec3Ball x r)) →L[ℝ]
      Lp E 2 (volume.restrict (vec3Ball 0 1)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (CKN.spatialAffine r x)
    ⟨(ballAffine_measurableEmbedding x hr).measurable, rfl⟩).toContinuousLinearMap.comp
      (Lp.LpToLpOfMeasureLeSMul (c := ENNReal.ofReal (r⁻¹ ^ 3)) ENNReal.ofReal_ne_top
        (map_ballAffine_restrict x hr).le)

/-- The actual inverse-coordinate pullback of unit L² data to the physical ball. -/
def ballL2Pushforward (x : Vec3) {r : ℝ} (hr : 0 < r) :
    Lp E 2 (volume.restrict (vec3Ball 0 1)) →L[ℝ]
      Lp E 2 (volume.restrict (vec3Ball x r)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (ballCoordinates x r)
    ⟨(ballCoordinates_measurableEmbedding x hr).measurable, rfl⟩).toContinuousLinearMap.comp
      (Lp.LpToLpOfMeasureLeSMul (c := ENNReal.ofReal (r ^ 3)) ENNReal.ofReal_ne_top
        (map_ballCoordinates_restrict x hr).le)

/-- The affine L² class is represented by the literal composition almost everywhere. -/
theorem ballL2Pullback_ae (x : Vec3) {r : ℝ} (hr : 0 < r)
    (f : Lp E 2 (volume.restrict (vec3Ball x r))) :
    ballL2Pullback E x hr f =ᵐ[volume.restrict (vec3Ball 0 1)]
      fun y ↦ f (CKN.spatialAffine r x y) := by
  have hc := Lp.coeFn_compMeasurePreserving
    (Lp.LpToLpOfMeasureLeSMul (c := ENNReal.ofReal (r⁻¹ ^ 3)) ENNReal.ofReal_ne_top
      (map_ballAffine_restrict x hr).le f)
    (show MeasurePreserving (CKN.spatialAffine r x)
      (volume.restrict (vec3Ball 0 1))
      (Measure.map (CKN.spatialAffine r x) (volume.restrict (vec3Ball 0 1))) from
      ⟨(ballAffine_measurableEmbedding x hr).measurable, rfl⟩)
  have he := (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
    (map_ballAffine_restrict x hr).le f).comp_tendsto
      (tendsto_ae_map (ballAffine_measurableEmbedding x hr).measurable.aemeasurable)
  exact hc.trans he

/-- The physical L² class is represented by literal inverse coordinates almost everywhere. -/
theorem ballL2Pushforward_ae (x : Vec3) {r : ℝ} (hr : 0 < r)
    (f : Lp E 2 (volume.restrict (vec3Ball 0 1))) :
    ballL2Pushforward E x hr f =ᵐ[volume.restrict (vec3Ball x r)]
      fun y ↦ f (ballCoordinates x r y) := by
  have hc := Lp.coeFn_compMeasurePreserving
    (Lp.LpToLpOfMeasureLeSMul (c := ENNReal.ofReal (r ^ 3)) ENNReal.ofReal_ne_top
      (map_ballCoordinates_restrict x hr).le f)
    (show MeasurePreserving (ballCoordinates x r) (volume.restrict (vec3Ball x r))
      (Measure.map (ballCoordinates x r) (volume.restrict (vec3Ball x r))) from
      ⟨(ballCoordinates_measurableEmbedding x hr).measurable, rfl⟩)
  have he := (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
    (map_ballCoordinates_restrict x hr).le f).comp_tendsto
      (tendsto_ae_map (ballCoordinates_measurableEmbedding x hr).measurable.aemeasurable)
  exact hc.trans he

/-- The true affine L² operator has the expected square-root Jacobian bound. -/
theorem ballL2Pullback_norm_le (x : Vec3) {r : ℝ} (hr : 0 < r) :
    ‖ballL2Pullback E x hr‖ ≤ (r⁻¹ ^ 3) ^ (1 / 2 : ℝ) := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h := Lp.norm_LpToLpOfMeasureLeSMul_le (E := E) (p := 2)
    ENNReal.ofReal_ne_top (map_ballAffine_restrict x hr).le
  have h' : ‖Lp.LpToLpOfMeasureLeSMul (E := E) (p := 2)
      ENNReal.ofReal_ne_top (map_ballAffine_restrict x hr).le‖ ≤
        (r⁻¹ ^ 3) ^ (1 / 2 : ℝ) := by
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ r⁻¹ ^ 3 by positivity),
      ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using h
  exact (mul_le_mul_of_nonneg_right
    (LinearIsometry.norm_toContinuousLinearMap_le _) (norm_nonneg _)).trans
      (by simpa only [one_mul] using h')

/-- The inverse-coordinate L² operator has the physical square-root Jacobian bound. -/
theorem ballL2Pushforward_norm_le (x : Vec3) {r : ℝ} (hr : 0 < r) :
    ‖ballL2Pushforward E x hr‖ ≤ (r ^ 3) ^ (1 / 2 : ℝ) := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h := Lp.norm_LpToLpOfMeasureLeSMul_le (E := E) (p := 2)
    ENNReal.ofReal_ne_top (map_ballCoordinates_restrict x hr).le
  have h' : ‖Lp.LpToLpOfMeasureLeSMul (E := E) (p := 2)
      ENNReal.ofReal_ne_top (map_ballCoordinates_restrict x hr).le‖ ≤
        (r ^ 3) ^ (1 / 2 : ℝ) := by
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ r ^ 3 by positivity),
      ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using h
  exact (mul_le_mul_of_nonneg_right
    (LinearIsometry.norm_toContinuousLinearMap_le _) (norm_nonneg _)).trans
      (by simpa only [one_mul] using h')

/-- The affine L² norm has the exact square-root spatial Jacobian. -/
theorem ballL2Pullback_norm (x : Vec3) {r : ℝ} (hr : 0 < r)
    (f : Lp E 2 (volume.restrict (vec3Ball x r))) :
    ‖ballL2Pullback E x hr f‖ = (r⁻¹ ^ 3) ^ (1 / 2 : ℝ) * ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (ballL2Pullback_ae E x hr f)]
  change (eLpNorm ((f : Vec3 → E) ∘ CKN.spatialAffine r x) 2
    (volume.restrict (vec3Ball 0 1))).toReal = _
  rw [← (ballAffine_measurableEmbedding x hr).eLpNorm_map_measure,
    map_ballAffine_restrict x hr]
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num) _ _ (Lp.aestronglyMeasurable f)]
  rw [smul_eq_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  simp only [ENNReal.toReal_ofReal (show 0 ≤ r⁻¹ ^ 3 by positivity),
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, Lp.norm_def]

/-- The physical L² norm has the exact square-root spatial Jacobian. -/
theorem ballL2Pushforward_norm (x : Vec3) {r : ℝ} (hr : 0 < r)
    (f : Lp E 2 (volume.restrict (vec3Ball 0 1))) :
    ‖ballL2Pushforward E x hr f‖ = (r ^ 3) ^ (1 / 2 : ℝ) * ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (ballL2Pushforward_ae E x hr f)]
  change (eLpNorm ((f : Vec3 → E) ∘ ballCoordinates x r) 2
    (volume.restrict (vec3Ball x r))).toReal = _
  rw [← (ballCoordinates_measurableEmbedding x hr).eLpNorm_map_measure,
    map_ballCoordinates_restrict x hr]
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num) _ _ (Lp.aestronglyMeasurable f)]
  rw [smul_eq_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  simp only [ENNReal.toReal_ofReal (show 0 ≤ r ^ 3 by positivity),
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, Lp.norm_def]

/-- The two actual affine L² transports are inverse in physical coordinates. -/
theorem ballL2Pushforward_pullback (x : Vec3) {r : ℝ} (hr : 0 < r)
    (f : Lp E 2 (volume.restrict (vec3Ball x r))) :
    ballL2Pushforward E x hr (ballL2Pullback E x hr f) = f := by
  apply Lp.ext
  have he := (Measure.absolutelyContinuous_of_le_smul
    (map_ballCoordinates_restrict x hr).le).ae_eq (ballL2Pullback_ae E x hr f)
  have h := he.comp_tendsto
    (tendsto_ae_map (ballCoordinates_measurableEmbedding x hr).measurable.aemeasurable)
  filter_upwards [ballL2Pushforward_ae E x hr (ballL2Pullback E x hr f), h] with y hy he
  simp only [Function.comp_apply] at he
  rw [hy, he, ballAffine_coordinates x y hr]

/-- The two actual affine L² transports are inverse in unit coordinates. -/
theorem ballL2Pullback_pushforward (x : Vec3) {r : ℝ} (hr : 0 < r)
    (f : Lp E 2 (volume.restrict (vec3Ball 0 1))) :
    ballL2Pullback E x hr (ballL2Pushforward E x hr f) = f := by
  apply Lp.ext
  have he := (Measure.absolutelyContinuous_of_le_smul
    (map_ballAffine_restrict x hr).le).ae_eq (ballL2Pushforward_ae E x hr f)
  have h := he.comp_tendsto
    (tendsto_ae_map (ballAffine_measurableEmbedding x hr).measurable.aemeasurable)
  filter_upwards [ballL2Pullback_ae E x hr (ballL2Pushforward E x hr f), h] with y hy he
  simp only [Function.comp_apply] at he
  rw [hy, he, ballCoordinates_affine x y hr]

/-- The reciprocal square-root Jacobian factors exactly cancel. -/
theorem ballL2Jacobian_cancel {r : ℝ} (hr : 0 < r) :
    (r ^ 3) ^ (1 / 2 : ℝ) * (r⁻¹ ^ 3) ^ (1 / 2 : ℝ) = 1 := by
  rw [inv_pow, Real.inv_rpow (by positivity),
    mul_inv_cancel₀ (Real.rpow_pos_of_pos (pow_pos hr 3) _).ne']

/-- Normalized affine transport is an actual linear isometry of spatial L² classes. -/
def ballL2Isometry (x : Vec3) {r : ℝ} (hr : 0 < r) :
    Lp E 2 (volume.restrict (vec3Ball x r)) ≃ₗᵢ[ℝ]
      Lp E 2 (volume.restrict (vec3Ball 0 1)) where
  toLinearEquiv :=
    { toLinearMap := (r ^ 3) ^ (1 / 2 : ℝ) • (ballL2Pullback E x hr).toLinearMap
      invFun := fun f ↦ (r⁻¹ ^ 3) ^ (1 / 2 : ℝ) • ballL2Pushforward E x hr f
      left_inv := by
        intro f
        change (r⁻¹ ^ 3) ^ (1 / 2 : ℝ) • ballL2Pushforward E x hr
          ((r ^ 3) ^ (1 / 2 : ℝ) • ballL2Pullback E x hr f) = f
        rw [map_smul, smul_smul, ballL2Pushforward_pullback E x hr,
          mul_comm, ballL2Jacobian_cancel hr, one_smul]
      right_inv := by
        intro f
        change (r ^ 3) ^ (1 / 2 : ℝ) • ballL2Pullback E x hr
          ((r⁻¹ ^ 3) ^ (1 / 2 : ℝ) • ballL2Pushforward E x hr f) = f
        rw [map_smul, smul_smul, ballL2Pullback_pushforward E x hr,
          ballL2Jacobian_cancel hr, one_smul] }
  norm_map' := by
    intro f
    change ‖(r ^ 3) ^ (1 / 2 : ℝ) • ballL2Pullback E x hr f‖ = ‖f‖
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
      ballL2Pullback_norm E x hr, ← mul_assoc, ballL2Jacobian_cancel hr, one_mul]

@[simp]
theorem ballL2Isometry_apply (x : Vec3) {r : ℝ} (hr : 0 < r)
    (f : Lp E 2 (volume.restrict (vec3Ball x r))) :
    ballL2Isometry E x hr f =
      (r ^ 3) ^ (1 / 2 : ℝ) • ballL2Pullback E x hr f := rfl

@[simp]
theorem ballL2Isometry_symm_apply (x : Vec3) {r : ℝ} (hr : 0 < r)
    (f : Lp E 2 (volume.restrict (vec3Ball 0 1))) :
    (ballL2Isometry E x hr).symm f =
      (r⁻¹ ^ 3) ^ (1 / 2 : ℝ) • ballL2Pushforward E x hr f := rfl

/-- The normalized affine isometry has its literal scaled composition representative. -/
theorem ballL2Isometry_ae (x : Vec3) {r : ℝ} (hr : 0 < r)
    (f : Lp E 2 (volume.restrict (vec3Ball x r))) :
    ballL2Isometry E x hr f =ᵐ[volume.restrict (vec3Ball 0 1)]
      fun y ↦ (r ^ 3) ^ (1 / 2 : ℝ) • f (CKN.spatialAffine r x y) := by
  exact (Lp.coeFn_smul _ (ballL2Pullback E x hr f)).trans
    ((ballL2Pullback_ae E x hr f).fun_comp (fun a ↦ (r ^ 3) ^ (1 / 2 : ℝ) • a))

/-- The inverse isometry has its literal scaled physical-coordinate representative. -/
theorem ballL2Isometry_symm_ae (x : Vec3) {r : ℝ} (hr : 0 < r)
    (f : Lp E 2 (volume.restrict (vec3Ball 0 1))) :
    (ballL2Isometry E x hr).symm f =ᵐ[volume.restrict (vec3Ball x r)]
      fun y ↦ (r⁻¹ ^ 3) ^ (1 / 2 : ℝ) • f (ballCoordinates x r y) := by
  exact (Lp.coeFn_smul _ (ballL2Pushforward E x hr f)).trans
    ((ballL2Pushforward_ae E x hr f).fun_comp (fun a ↦ (r⁻¹ ^ 3) ^ (1 / 2 : ℝ) • a))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Affine normalized transport commutes with actual pointwise continuous linear maps. -/
theorem ballL2Isometry_compLpL (x : Vec3) {r : ℝ} (hr : 0 < r)
    (L : E →L[ℝ] F) (f : Lp E 2 (volume.restrict (vec3Ball x r))) :
    ballL2Isometry F x hr (L.compLpL 2 (volume.restrict (vec3Ball x r)) f) =
      L.compLpL 2 (volume.restrict (vec3Ball 0 1)) (ballL2Isometry E x hr f) := by
  apply Lp.ext
  have he := (Measure.absolutelyContinuous_of_le_smul
    (map_ballAffine_restrict x hr).le).ae_eq
      (L.coeFn_compLpL (p := 2) (μ := volume.restrict (vec3Ball x r)) f)
  have h := he.comp_tendsto
    (tendsto_ae_map (ballAffine_measurableEmbedding x hr).measurable.aemeasurable)
  filter_upwards [ballL2Isometry_ae F x hr (L.compLpL 2 _ f), h,
    L.coeFn_compLpL (p := 2) (μ := volume.restrict (vec3Ball 0 1))
      (ballL2Isometry E x hr f), ballL2Isometry_ae E x hr f] with y hy he hl hf
  simp only [Function.comp_apply] at he
  rw [hy, he, hl, hf, map_smul]

end L2Transport

/-- The literal scalar integral transforms by the reciprocal spatial Jacobian. -/
theorem ballL2Pullback_integral (x : Vec3) {r : ℝ} (hr : 0 < r)
    (f : Lp ℝ 2 (volume.restrict (vec3Ball x r))) :
    (∫ y in vec3Ball 0 1, ballL2Pullback ℝ x hr f y) =
      r⁻¹ ^ 3 * ∫ y in vec3Ball x r, f y := by
  rw [integral_congr_ae (ballL2Pullback_ae ℝ x hr f)]
  change (∫ y, f (CKN.spatialAffine r x y) ∂volume.restrict (vec3Ball 0 1)) = _
  rw [← (ballAffine_measurableEmbedding x hr).integral_map,
    map_ballAffine_restrict x hr, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (show 0 ≤ r⁻¹ ^ 3 by positivity), smul_eq_mul]

/-- The physical scalar integral transforms by the actual spatial volume Jacobian. -/
theorem ballL2Pushforward_integral (x : Vec3) {r : ℝ} (hr : 0 < r)
    (f : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) :
    (∫ y in vec3Ball x r, ballL2Pushforward ℝ x hr f y) =
      r ^ 3 * ∫ y in vec3Ball 0 1, f y := by
  rw [integral_congr_ae (ballL2Pushforward_ae ℝ x hr f)]
  change (∫ y, f (ballCoordinates x r y) ∂volume.restrict (vec3Ball x r)) = _
  rw [← (ballCoordinates_measurableEmbedding x hr).integral_map,
    map_ballCoordinates_restrict x hr, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (show 0 ≤ r ^ 3 by positivity), smul_eq_mul]

/-- Inverse-coordinate transport of an actual compact unit-ball test. -/
def ballTestPushforward (x : Vec3) {r : ℝ} (hr : 0 < r)
    (φ : WeakTestFunction (vec3Ball 0 1)) : WeakTestFunction (vec3Ball x r) where
  toFun := φ.toFun ∘ ballCoordinates x r
  contDiff := φ.contDiff.comp (by unfold ballCoordinates; fun_prop)
  hasCompactSupport := φ.hasCompactSupport.comp_homeomorph (ballAffineHomeomorph x hr).symm
  tsupport_subset := by
    change tsupport (φ.toFun ∘ (ballAffineHomeomorph x hr).symm) ⊆ _
    rw [tsupport_comp_eq_preimage φ.toFun (ballAffineHomeomorph x hr).symm]
    intro y hy
    have h := φ.tsupport_subset hy
    exact (Set.ext_iff.mp (ballCoordinates_preimage x hr) y).mp h

/-- The genuine inverse-coordinate chain rule on a compact test. -/
theorem ballTestPushforward_partialDeriv (x : Vec3) {r : ℝ} (hr : 0 < r)
    (φ : WeakTestFunction (vec3Ball 0 1)) (i : Fin 3) (y : Vec3) :
    (ballTestPushforward x hr φ).partialDeriv i y =
      r⁻¹ * φ.partialDeriv i (ballCoordinates x r y) := by
  have ha := ((hasFDerivAt_id (𝕜 := ℝ) y).sub_const x).const_smul r⁻¹
  have hφ := (φ.contDiff.differentiable (by simp)).differentiableAt
    (x := ballCoordinates x r y) |>.hasFDerivAt
  have h := (hφ.comp y ha).fderiv
  change (fderiv ℝ (φ.toFun ∘ ballCoordinates x r) y) (basisVec i) = _
  rw [h]
  simp [ballCoordinates, WeakTestFunction.partialDeriv]

/-- Actual test-gradient classes transform by the genuine spatial chain rule. -/
theorem ballL2Pullback_stokesTestGradient (x : Vec3) {r : ℝ} (hr : 0 < r)
    (φ : StokesVectorTest (vec3Ball x r)) :
    ballL2Pullback StokesGradientMatrix x hr (stokesTestGradientL2 φ) =
      r⁻¹ • stokesTestGradientL2 (fun i ↦ ballTestPullback x hr (φ i)) := by
  apply Lp.ext
  have he := (Measure.absolutelyContinuous_of_le_smul
    (map_ballAffine_restrict x hr).le).ae_eq (stokesTestGradient_memLp φ).coeFn_toLp
  have h := he.comp_tendsto
    (tendsto_ae_map (ballAffine_measurableEmbedding x hr).measurable.aemeasurable)
  filter_upwards [ballL2Pullback_ae StokesGradientMatrix x hr (stokesTestGradientL2 φ), h,
    Lp.coeFn_smul r⁻¹ (stokesTestGradientL2 (fun i ↦ ballTestPullback x hr (φ i))),
    (stokesTestGradient_memLp (fun i ↦ ballTestPullback x hr (φ i))).coeFn_toLp]
      with y hy he hs ht
  simp only [Function.comp_apply] at he
  change stokesTestGradientL2 φ (CKN.spatialAffine r x y) = _ at he
  change stokesTestGradientL2 (fun i ↦ ballTestPullback x hr (φ i)) y = _ at ht
  simp only [Pi.smul_apply] at hs
  rw [hy, he, hs, ht]
  apply PiLp.ext
  intro ij
  simp [stokesTestGradient, ballTestPullback_partialDeriv, hr.ne']

/-- The true inverse-coordinate chain rule on test-gradient classes. -/
theorem ballL2Pushforward_stokesTestGradient (x : Vec3) {r : ℝ} (hr : 0 < r)
    (φ : StokesVectorTest (vec3Ball 0 1)) :
    ballL2Pushforward StokesGradientMatrix x hr (stokesTestGradientL2 φ) =
      r • stokesTestGradientL2 (fun i ↦ ballTestPushforward x hr (φ i)) := by
  apply Lp.ext
  have he := (Measure.absolutelyContinuous_of_le_smul
    (map_ballCoordinates_restrict x hr).le).ae_eq (stokesTestGradient_memLp φ).coeFn_toLp
  have h := he.comp_tendsto
    (tendsto_ae_map (ballCoordinates_measurableEmbedding x hr).measurable.aemeasurable)
  filter_upwards [ballL2Pushforward_ae StokesGradientMatrix x hr (stokesTestGradientL2 φ), h,
    Lp.coeFn_smul r (stokesTestGradientL2 (fun i ↦ ballTestPushforward x hr (φ i))),
    (stokesTestGradient_memLp (fun i ↦ ballTestPushforward x hr (φ i))).coeFn_toLp]
      with y hy he hs ht
  simp only [Function.comp_apply] at he
  change stokesTestGradientL2 φ (ballCoordinates x r y) = _ at he
  change stokesTestGradientL2 (fun i ↦ ballTestPushforward x hr (φ i)) y = _ at ht
  simp only [Pi.smul_apply] at hs
  rw [hy, he, hs, ht]
  apply PiLp.ext
  intro ij
  simp [stokesTestGradient, ballTestPushforward_partialDeriv, hr.ne']

private theorem continuousLinearMap_closedSpan_mem
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : A →L[ℝ] B) (K : ClosedSubmodule ℝ B) (S : Set A)
    (hL : ∀ a ∈ S, L a ∈ K) {v : A}
    (hv : v ∈ (Submodule.span ℝ S).closure) : L v ∈ K := by
  have h : (Submodule.span ℝ S).closure ≤ K.comap L := by
    exact Submodule.closure_le.mpr (Submodule.span_le.mpr hL)
  exact h hv

/-- A genuine continuous gradient-class map preserves the energy completion once
it preserves the actual smooth compact test generators. -/
theorem stokesGradientEnergy_map_mem {U V : Set Vec3}
    (L : StokesGradientL2 U →L[ℝ] StokesGradientL2 V)
    (hL : ∀ φ : StokesVectorTest U, L (stokesTestGradientL2 φ) ∈
      stokesGradientEnergySpace V) (v : stokesGradientEnergySpace U) :
    L v.val ∈ stokesGradientEnergySpace V := by
  apply continuousLinearMap_closedSpan_mem L (stokesGradientEnergySpace V)
    (range (stokesTestGradientL2 (U := U))) _ v.property
  rintro _ ⟨φ, rfl⟩
  exact hL φ

/-- Affine pullback preserves the actual closure of zero-boundary test gradients. -/
theorem ballL2Pullback_energy_mem (x : Vec3) {r : ℝ} (hr : 0 < r)
    (v : stokesGradientEnergySpace (vec3Ball x r)) :
    ballL2Pullback StokesGradientMatrix x hr v.val ∈
      stokesGradientEnergySpace (vec3Ball 0 1) := by
  apply stokesGradientEnergy_map_mem _ _ v
  intro φ
  rw [ballL2Pullback_stokesTestGradient x hr φ]
  exact (stokesGradientEnergySpace (vec3Ball 0 1)).smul_mem _
    (stokesTestGradientL2_mem _)

/-- Inverse-coordinate transport preserves the actual zero-boundary energy completion. -/
theorem ballL2Pushforward_energy_mem (x : Vec3) {r : ℝ} (hr : 0 < r)
    (v : stokesGradientEnergySpace (vec3Ball 0 1)) :
    ballL2Pushforward StokesGradientMatrix x hr v.val ∈
      stokesGradientEnergySpace (vec3Ball x r) := by
  apply stokesGradientEnergy_map_mem _ _ v
  intro φ
  rw [ballL2Pushforward_stokesTestGradient x hr φ]
  exact (stokesGradientEnergySpace (vec3Ball x r)).smul_mem _
    (stokesTestGradientL2_mem _)

local instance ballEnergySeminormedAddCommGroup (U : Set Vec3) :
    SeminormedAddCommGroup (stokesGradientEnergySpace U) :=
  (inferInstance : NormedAddCommGroup (stokesGradientEnergySpace U)).toSeminormedAddCommGroup

local instance ballEnergyNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (stokesGradientEnergySpace U) :=
  InnerProductSpace.toNormedSpace

local instance ballSolenoidalSeminormedAddCommGroup (U : Set Vec3) :
    SeminormedAddCommGroup (stokesSolenoidalEnergySpace U) :=
  (inferInstance : NormedAddCommGroup (stokesSolenoidalEnergySpace U)).toSeminormedAddCommGroup

local instance ballSolenoidalNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (stokesSolenoidalEnergySpace U) :=
  InnerProductSpace.toNormedSpace

/-- Normalized affine transport gives a genuine isometry of the zero-boundary energy spaces. -/
def ballEnergyIsometry (x : Vec3) {r : ℝ} (hr : 0 < r) :
    stokesGradientEnergySpace (vec3Ball x r) ≃ₗᵢ[ℝ]
      stokesGradientEnergySpace (vec3Ball 0 1) where
  toFun v := ⟨ballL2Isometry StokesGradientMatrix x hr v.val,
    (stokesGradientEnergySpace (vec3Ball 0 1)).smul_mem _
      (ballL2Pullback_energy_mem x hr v)⟩
  invFun v := ⟨(ballL2Isometry StokesGradientMatrix x hr).symm v.val,
    (stokesGradientEnergySpace (vec3Ball x r)).smul_mem _
      (ballL2Pushforward_energy_mem x hr v)⟩
  left_inv v := by apply Subtype.ext; exact (ballL2Isometry _ x hr).symm_apply_apply v.val
  right_inv v := by apply Subtype.ext; exact (ballL2Isometry _ x hr).apply_symm_apply v.val
  map_add' u v := by apply Subtype.ext; exact (ballL2Isometry _ x hr).map_add u.val v.val
  map_smul' c v := by apply Subtype.ext; exact (ballL2Isometry _ x hr).map_smul c v.val
  norm_map' v := (ballL2Isometry StokesGradientMatrix x hr).norm_map v.val

/-- Genuine divergence commutes with normalized affine energy transport. -/
theorem ballEnergyIsometry_divergence (x : Vec3) {r : ℝ} (hr : 0 < r)
    (v : stokesGradientEnergySpace (vec3Ball x r)) :
    stokesEnergyDivergence (vec3Ball 0 1) (ballEnergyIsometry x hr v) =
      ballL2Isometry ℝ x hr (stokesEnergyDivergence (vec3Ball x r) v) := by
  exact (ballL2Isometry_compLpL StokesGradientMatrix x hr stokesMatrixTrace v.val).symm

/-- Genuine divergence also commutes with inverse normalized energy transport. -/
theorem ballEnergyIsometry_symm_divergence (x : Vec3) {r : ℝ} (hr : 0 < r)
    (v : stokesGradientEnergySpace (vec3Ball 0 1)) :
    stokesEnergyDivergence (vec3Ball x r) ((ballEnergyIsometry x hr).symm v) =
      (ballL2Isometry ℝ x hr).symm (stokesEnergyDivergence (vec3Ball 0 1) v) := by
  apply (ballL2Isometry ℝ x hr).injective
  rw [← ballEnergyIsometry_divergence, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]

/-- The actual divergence-free energy kernels are carried isometrically to one another. -/
def ballSolenoidalIsometry (x : Vec3) {r : ℝ} (hr : 0 < r) :
    stokesSolenoidalEnergySpace (vec3Ball x r) ≃ₗᵢ[ℝ]
      stokesSolenoidalEnergySpace (vec3Ball 0 1) where
  toFun v := ⟨ballEnergyIsometry x hr v.val, by
    change stokesEnergyDivergence (vec3Ball 0 1) (ballEnergyIsometry x hr v.val) = 0
    have hv : stokesEnergyDivergence (vec3Ball x r) v.val = 0 := v.property
    rw [ballEnergyIsometry_divergence, hv, map_zero]⟩
  invFun v := ⟨(ballEnergyIsometry x hr).symm v.val, by
    change stokesEnergyDivergence (vec3Ball x r)
      ((ballEnergyIsometry x hr).symm v.val) = 0
    have hv : stokesEnergyDivergence (vec3Ball 0 1) v.val = 0 := v.property
    rw [ballEnergyIsometry_symm_divergence, hv, map_zero]⟩
  left_inv v := by apply Subtype.ext; exact (ballEnergyIsometry x hr).symm_apply_apply v.val
  right_inv v := by apply Subtype.ext; exact (ballEnergyIsometry x hr).apply_symm_apply v.val
  map_add' u v := by apply Subtype.ext; exact (ballEnergyIsometry x hr).map_add u.val v.val
  map_smul' c v := by apply Subtype.ext; exact (ballEnergyIsometry x hr).map_smul c v.val
  norm_map' v := (ballEnergyIsometry x hr).norm_map v.val

local instance ballStokesForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup (stokesGradientEnergySpace U →L[ℝ] ℝ))

local instance ballStokesForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ (stokesGradientEnergySpace U →L[ℝ] ℝ))

/-- Pullback of a genuine physical-ball energy force through the proved energy isometry. -/
def ballStokesForcePullback (x : Vec3) {r : ℝ} (hr : 0 < r) :
    StokesEnergyForce (vec3Ball x r) →L[ℝ] StokesEnergyForce (vec3Ball 0 1) :=
  realDualPrecompose (ballEnergyIsometry x hr).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem ballStokesForcePullback_apply (x : Vec3) {r : ℝ} (hr : 0 < r)
    (F : StokesEnergyForce (vec3Ball x r)) (v : stokesGradientEnergySpace (vec3Ball 0 1)) :
    ballStokesForcePullback x hr F v = F ((ballEnergyIsometry x hr).symm v) := rfl

/-- Force transport preserves the actual energy-dual norm bound. -/
theorem ballStokesForcePullback_norm_le (x : Vec3) {r : ℝ} (hr : 0 < r)
    (F : StokesEnergyForce (vec3Ball x r)) : ‖ballStokesForcePullback x hr F‖ ≤ ‖F‖ := by
  refine (ballStokesForcePullback x hr F).opNorm_le_bound (norm_nonneg F) ?_
  intro v
  simpa only [ballStokesForcePullback_apply, (ballEnergyIsometry x hr).symm.norm_map] using
    F.le_opNorm ((ballEnergyIsometry x hr).symm v)

/-- The actual variational Stokes solution is preserved by normalized affine transport. -/
theorem ballEnergyIsometry_stokesEnergySolution (x : Vec3) {r : ℝ} (hr : 0 < r)
    (F : StokesEnergyForce (vec3Ball x r)) :
    ballEnergyIsometry x hr (stokesEnergySolution F).val =
      (stokesEnergySolution (ballStokesForcePullback x hr F)).val := by
  have h : ballSolenoidalIsometry x hr (stokesEnergySolution F) =
      stokesEnergySolution (ballStokesForcePullback x hr F) := by
    apply stokesEnergySolution_unique
    intro v
    rw [(ballSolenoidalIsometry x hr).inner_map_eq_flip]
    rw [stokesEnergySolution_firstVariation]
    rfl
  exact congrArg Subtype.val h

/-- The genuine mean-zero spatial pressure operator on an arbitrary positive-radius ball. -/
def ballStokesPressureL (x : Vec3) {r : ℝ} (hr : 0 < r) :
    StokesEnergyForce (vec3Ball x r) →L[ℝ] Lp ℝ 2 (volume.restrict (vec3Ball x r)) :=
  (ballL2Isometry ℝ x hr).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (unitBallMeanZeroL2.toSubmodule.subtypeL.comp
      (unitBallStokesPressureL.comp (ballStokesForcePullback x hr)))

@[simp]
theorem ballStokesPressureL_apply (x : Vec3) {r : ℝ} (hr : 0 < r)
    (F : StokesEnergyForce (vec3Ball x r)) :
    ballStokesPressureL x hr F = (ballL2Isometry ℝ x hr).symm
      (unitBallStokesPressure (ballStokesForcePullback x hr F) :
        Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) := rfl

/-- The true arbitrary-ball pressure estimate is uniform in the center and radius. -/
theorem ballStokesPressureL_norm_le (x : Vec3) {r : ℝ} (hr : 0 < r)
    (F : StokesEnergyForce (vec3Ball x r)) : ‖ballStokesPressureL x hr F‖ ≤ 4 * ‖F‖ := by
  rw [ballStokesPressureL_apply, (ballL2Isometry ℝ x hr).symm.norm_map]
  exact (unitBallStokesPressure_norm _).trans
    (mul_le_mul_of_nonneg_left (ballStokesForcePullback_norm_le x hr F) (by norm_num))

/-- The transported pressure satisfies the true physical-ball variational residual identity. -/
theorem ballStokesPressureL_pairing (x : Vec3) {r : ℝ} (hr : 0 < r)
    (F : StokesEnergyForce (vec3Ball x r))
    (v : stokesGradientEnergySpace (vec3Ball x r)) :
    -(inner ℝ (ballStokesPressureL x hr F) (stokesEnergyDivergence (vec3Ball x r) v)) =
      stokesEnergyResidual F v := by
  have h := unitBallStokesPressure_pairing (ballStokesForcePullback x hr F)
    (ballEnergyIsometry x hr v)
  rw [ballEnergyIsometry_divergence] at h
  rw [ballStokesPressureL_apply]
  rw [← (ballL2Isometry ℝ x hr).inner_map_map,
    (ballL2Isometry ℝ x hr).apply_symm_apply]
  rw [h]
  change F ((ballEnergyIsometry x hr).symm (ballEnergyIsometry x hr v)) -
    inner ℝ (stokesEnergySolution (ballStokesForcePullback x hr F)).val
      (ballEnergyIsometry x hr v) = F v - inner ℝ (stokesEnergySolution F).val v
  rw [(ballEnergyIsometry x hr).symm_apply_apply,
    ← ballEnergyIsometry_stokesEnergySolution x hr F,
    (ballEnergyIsometry x hr).inner_map_map]

/-- The pressure on the physical ball has literal zero spatial integral. -/
theorem ballStokesPressureL_integral_zero (x : Vec3) {r : ℝ} (hr : 0 < r)
    (F : StokesEnergyForce (vec3Ball x r)) :
    (∫ y in vec3Ball x r, ballStokesPressureL x hr F y) = 0 := by
  rw [ballStokesPressureL_apply, ballL2Isometry_symm_apply]
  rw [integral_congr_ae (Lp.coeFn_smul _ _)]
  simp only [Pi.smul_apply]
  rw [integral_smul,
    ballL2Pushforward_integral x hr, unitBallStokesPressure_integral_zero,
    mul_zero, smul_zero]

/-- Every actual compact smooth physical test satisfies the genuine Stokes equation. -/
theorem ballStokesPressureL_test (x : Vec3) {r : ℝ} (hr : 0 < r)
    (F : StokesEnergyForce (vec3Ball x r)) (φ : StokesVectorTest (vec3Ball x r)) :
    Integrable (fun y ↦ ballStokesPressureL x hr F y *
      ∑ i : Fin 3, (φ i).partialDeriv i y) (volume.restrict (vec3Ball x r)) ∧
    inner ℝ (stokesEnergySolution F : stokesGradientEnergySpace (vec3Ball x r))
      (stokesEnergyTest φ) -
        (∫ y in vec3Ball x r, ballStokesPressureL x hr F y *
          ∑ i : Fin 3, (φ i).partialDeriv i y) = F (stokesEnergyTest φ) := by
  let p : Lp ℝ 2 (volume.restrict (vec3Ball x r)) := ballStokesPressureL x hr F
  have hprod : (fun y ↦ inner ℝ (p y)
      (stokesEnergyDivergence (vec3Ball x r) (stokesEnergyTest φ) y))
        =ᵐ[volume.restrict (vec3Ball x r)]
          (fun y ↦ p y * ∑ i : Fin 3, (φ i).partialDeriv i y) := by
    filter_upwards [stokesEnergyDivergence_test_ae φ] with y hy
    rw [hy]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  refine ⟨(L2.integrable_inner (𝕜 := ℝ) p
    (stokesEnergyDivergence (vec3Ball x r) (stokesEnergyTest φ))).congr hprod, ?_⟩
  have hpair := ballStokesPressureL_pairing x hr F (stokesEnergyTest φ)
  rw [L2.inner_def, integral_congr_ae hprod] at hpair
  change -(∫ y in vec3Ball x r, p y * ∑ i : Fin 3, (φ i).partialDeriv i y) =
    F (stokesEnergyTest φ) -
      inner ℝ (stokesEnergySolution F : stokesGradientEnergySpace (vec3Ball x r))
        (stokesEnergyTest φ) at hpair
  linarith

end FluidSingularSets
