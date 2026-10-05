-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.SuitableBallPressureHarmonic

/-!
# Actual bounded centered-pressure restriction

Restriction to a smaller spatial ball and subtraction of its literal spatial
average form a genuine bounded linear map on L² pressure classes. The actual
representative and the norm bound imply time measurability and moment formulas
for centered pressure without assuming measurability of chosen spatial means.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual constant-one spatial L² class on any finite ball. -/
def ballConstantOneL2 (x : Vec3) (r : ℝ) : Lp ℝ 2 (volume.restrict (vec3Ball x r)) := by
  let : IsFiniteMeasure (volume.restrict (vec3Ball x r)) :=
    isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  exact (memLp_const (1 : ℝ)).toLp (fun _ ↦ 1)

/-- The actual constant class has its literal constant representative almost everywhere. -/
theorem ballConstantOneL2_ae (x : Vec3) (r : ℝ) :
    ballConstantOneL2 x r =ᵐ[volume.restrict (vec3Ball x r)] fun _ ↦ (1 : ℝ) := by
  let : IsFiniteMeasure (volume.restrict (vec3Ball x r)) :=
    isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  unfold ballConstantOneL2
  exact (memLp_const (1 : ℝ)).coeFn_toLp

/-- Literal spatial integration as a genuine bounded Hilbert functional. -/
def ballL2IntegralL (x : Vec3) (r : ℝ) :
    Lp ℝ 2 (volume.restrict (vec3Ball x r)) →L[ℝ] ℝ :=
  innerSL ℝ (ballConstantOneL2 x r)

/-- The bounded integral functional equals the true restricted spatial integral. -/
theorem ballL2IntegralL_apply (x : Vec3) (r : ℝ)
    (f : Lp ℝ 2 (volume.restrict (vec3Ball x r))) :
    ballL2IntegralL x r f = ∫ y in vec3Ball x r, f y := by
  change inner ℝ (ballConstantOneL2 x r) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ballConstantOneL2_ae x r] with y hy
  simp [hy, RCLike.inner_apply]

/-- Subtract the literal spatial mean by a genuine continuous linear map. -/
def ballRemoveMeanL (x : Vec3) (r : ℝ) :
    Lp ℝ 2 (volume.restrict (vec3Ball x r)) →L[ℝ]
      Lp ℝ 2 (volume.restrict (vec3Ball x r)) :=
  ContinuousLinearMap.id ℝ _ - (volume (vec3Ball x r)).toReal⁻¹ •
    (ballL2IntegralL x r).smulRight (ballConstantOneL2 x r)

/-- The actual mean-removal map has its literal Hilbert-space formula. -/
theorem ballRemoveMeanL_apply (x : Vec3) (r : ℝ)
    (f : Lp ℝ 2 (volume.restrict (vec3Ball x r))) :
    ballRemoveMeanL x r f = f -
      ((volume (vec3Ball x r)).toReal⁻¹ * ballL2IntegralL x r f) • ballConstantOneL2 x r := by
  simp [ballRemoveMeanL, smul_smul]

/-- Mean removal is represented by subtraction of the actual restricted spatial average. -/
theorem ballRemoveMeanL_ae (x : Vec3) (r : ℝ)
    (f : Lp ℝ 2 (volume.restrict (vec3Ball x r))) :
    ballRemoveMeanL x r f =ᵐ[volume.restrict (vec3Ball x r)]
      fun y ↦ f y - average (volume.restrict (vec3Ball x r)) f := by
  have hav : average (volume.restrict (vec3Ball x r)) f =
      (volume (vec3Ball x r)).toReal⁻¹ * ballL2IntegralL x r f := by
    rw [average_eq, ballL2IntegralL_apply]
    simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
  rw [ballRemoveMeanL_apply]
  filter_upwards [Lp.coeFn_sub f
    (((volume (vec3Ball x r)).toReal⁻¹ * ballL2IntegralL x r f) • ballConstantOneL2 x r),
    Lp.coeFn_smul ((volume (vec3Ball x r)).toReal⁻¹ * ballL2IntegralL x r f)
      (ballConstantOneL2 x r), ballConstantOneL2_ae x r] with y hy hs h1
  simp only [Pi.sub_apply, Pi.smul_apply] at hy hs
  rw [hy, hs, h1, smul_eq_mul, mul_one, hav]

/-- True mean removal has the uniform L² norm bound two. -/
theorem ballRemoveMeanL_norm_apply_le (x : Vec3) {r : ℝ} (hr : 0 < r)
    (f : Lp ℝ 2 (volume.restrict (vec3Ball x r))) :
    ‖ballRemoveMeanL x r f‖ ≤ 2 * ‖f‖ := by
  let : IsFiniteMeasure (volume.restrict (vec3Ball x r)) :=
    isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  have hm : (volume.restrict (vec3Ball x r)) univ ≠ 0 := by
    simpa only [Measure.restrict_apply_univ] using (volume_vec3Ball_pos hr).ne'
  have hb := centered_eLpNorm_le_two hm (Lp.aestronglyMeasurable f)
    (show (2 : ℝ).HolderConjugate 2 by constructor <;> norm_num)
  norm_num only [ENNReal.ofReal_ofNat] at hb
  have hn := ENNReal.toReal_mono
    (show 2 * eLpNorm f 2 (volume.restrict (vec3Ball x r)) ≠ ∞ by finiteness [Lp.memLp f]) hb
  rw [Lp.norm_def, eLpNorm_congr_ae (ballRemoveMeanL_ae x r f), Lp.norm_def]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using hn

/-- Actual spatial mean removal is a uniformly bounded operator. -/
theorem ballRemoveMeanL_norm_le (x : Vec3) {r : ℝ} (hr : 0 < r) :
    ‖ballRemoveMeanL x r‖ ≤ 2 :=
  (ballRemoveMeanL x r).opNorm_le_bound (by norm_num)
    (ballRemoveMeanL_norm_apply_le x hr)

/-- Restrict actual spatial L² classes to the smaller concentric ball. -/
def ballRestrictL2 (x : Vec3) {R r : ℝ} (hrR : r ≤ R) :
    Lp ℝ 2 (volume.restrict (vec3Ball x R)) →L[ℝ]
      Lp ℝ 2 (volume.restrict (vec3Ball x r)) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa only [one_smul] using Measure.restrict_mono (vec3Ball_mono hrR) le_rfl)

/-- The actual restriction has the unchanged pressure representative almost everywhere. -/
theorem ballRestrictL2_ae (x : Vec3) {R r : ℝ} (hrR : r ≤ R)
    (f : Lp ℝ 2 (volume.restrict (vec3Ball x R))) :
    ballRestrictL2 x hrR f =ᵐ[volume.restrict (vec3Ball x r)] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp) _ f

/-- Actual restricted L² classes satisfy the contraction bound. -/
theorem ballRestrictL2_norm_le (x : Vec3) {R r : ℝ} (hrR : r ≤ R) :
    ‖ballRestrictL2 x hrR‖ ≤ 1 := by
  have hb := Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℝ) (p := 2) (c := 1)
    (by simp) (show volume.restrict (vec3Ball x r) ≤
      1 • volume.restrict (vec3Ball x R) by
        simpa only [one_smul] using Measure.restrict_mono (vec3Ball_mono hrR) le_rfl)
  simpa only [ballRestrictL2, ENNReal.toReal_one, Real.one_rpow] using hb

/-- The actual smaller-ball centered pressure is a genuine bounded linear image. -/
def ballCenteredPressureL (x : Vec3) {R r : ℝ} (hrR : r ≤ R) :
    Lp ℝ 2 (volume.restrict (vec3Ball x R)) →L[ℝ]
      Lp ℝ 2 (volume.restrict (vec3Ball x r)) :=
  (ballRemoveMeanL x r).comp (ballRestrictL2 x hrR)

/-- Actual centered restriction has its literal smaller-ball average representative. -/
theorem ballCenteredPressureL_ae (x : Vec3) {R r : ℝ} (hrR : r ≤ R)
    (f : Lp ℝ 2 (volume.restrict (vec3Ball x R))) :
    ballCenteredPressureL x hrR f =ᵐ[volume.restrict (vec3Ball x r)]
      fun y ↦ f y - average (volume.restrict (vec3Ball x r)) f := by
  have hae := ballRestrictL2_ae x hrR f
  have hav := average_congr hae
  filter_upwards [ballRemoveMeanL_ae x r (ballRestrictL2 x hrR f), hae] with y hy hf
  change ballCenteredPressureL x hrR f y = _ at hy
  rw [hy, hf, hav]

/-- True centered restriction has the uniform L² operator bound two. -/
theorem ballCenteredPressureL_norm_le (x : Vec3) {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ‖ballCenteredPressureL x hrR‖ ≤ 2 := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (ballRemoveMeanL_norm_le x hr) (ballRestrictL2_norm_le x hrR)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num))

/-- The norm of the actual centered class is exactly the literal centered pressure seminorm. -/
theorem ballCenteredPressureL_enorm (x : Vec3) {R r : ℝ} (hrR : r ≤ R)
    (f : Lp ℝ 2 (volume.restrict (vec3Ball x R))) :
    ‖ballCenteredPressureL x hrR f‖ₑ =
      eLpNorm (fun y ↦ f y - average (volume.restrict (vec3Ball x r)) f) 2
        (volume.restrict (vec3Ball x r)) := by
  rw [Lp.enorm_def, eLpNorm_congr_ae (ballCenteredPressureL_ae x hrR f)]

/-- Actual centered spatial pressure classes preserve time measurability. -/
theorem ballCenteredPressureL_aestronglyMeasurable
    (x : Vec3) {R r : ℝ} (hrR : r ≤ R) {ν : Measure ℝ}
    {P : ℝ → Lp ℝ 2 (volume.restrict (vec3Ball x R))}
    (hP : AEStronglyMeasurable P ν) :
    AEStronglyMeasurable (fun t ↦ ballCenteredPressureL x hrR (P t)) ν :=
  (ballCenteredPressureL x hrR).continuous.comp_aestronglyMeasurable hP

/-- The literal centered spatial seminorm is measurable in time without chosen mean data. -/
theorem ballCenteredPressureL_seminorm_aemeasurable
    (x : Vec3) {R r : ℝ} (hrR : r ≤ R) {ν : Measure ℝ}
    {P : ℝ → Lp ℝ 2 (volume.restrict (vec3Ball x R))}
    (hP : AEStronglyMeasurable P ν) :
    AEMeasurable (fun t ↦ eLpNorm
      (fun y ↦ P t y - average (volume.restrict (vec3Ball x r)) (P t)) 2
        (volume.restrict (vec3Ball x r))) ν := by
  have hm := (ballCenteredPressureL_aestronglyMeasurable x hrR hP).enorm
  exact hm.congr (.of_forall fun t ↦ ballCenteredPressureL_enorm x hrR (P t))

/-- The actual centered curve time L¹ norm equals the literal spatial oscillation moment. -/
theorem ballCenteredPressureL_eLpNorm_one_eq
    (x : Vec3) {R r : ℝ} (hrR : r ≤ R) {ν : Measure ℝ}
    {P : ℝ → Lp ℝ 2 (volume.restrict (vec3Ball x R))}
    (hP : AEStronglyMeasurable P ν) :
    eLpNorm (fun t ↦ ballCenteredPressureL x hrR (P t)) 1 ν =
      ∫⁻ t, eLpNorm (fun y ↦ P t y - average (volume.restrict (vec3Ball x r)) (P t)) 2
        (volume.restrict (vec3Ball x r)) ∂ν := by
  rw [eLpNorm_one_eq_lintegral_enorm (ballCenteredPressureL_aestronglyMeasurable x hrR hP)]
  exact lintegral_congr (fun t ↦ ballCenteredPressureL_enorm x hrR (P t))

/-- The actual centered curve time L² norm equals its literal square oscillation moment. -/
theorem ballCenteredPressureL_eLpNorm_two_eq
    (x : Vec3) {R r : ℝ} (hrR : r ≤ R) {ν : Measure ℝ}
    {P : ℝ → Lp ℝ 2 (volume.restrict (vec3Ball x R))}
    (hP : AEStronglyMeasurable P ν) :
    eLpNorm (fun t ↦ ballCenteredPressureL x hrR (P t)) 2 ν =
      (∫⁻ t, eLpNorm (fun y ↦ P t y - average (volume.restrict (vec3Ball x r)) (P t)) 2
        (volume.restrict (vec3Ball x r)) ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (ballCenteredPressureL_aestronglyMeasurable x hrR hP)]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  simp_rw [ballCenteredPressureL_enorm]

/-- Actual centered restriction preserves every finite or infinite time Lᵖ class. -/
theorem ballCenteredPressureL_memLp
    (x : Vec3) {R r : ℝ} (hrR : r ≤ R) {ν : Measure ℝ} {a : ℝ≥0∞}
    {P : ℝ → Lp ℝ 2 (volume.restrict (vec3Ball x R))} (hP : MemLp P a ν) :
    MemLp (fun t ↦ ballCenteredPressureL x hrR (P t)) a ν :=
  (ballCenteredPressureL x hrR).comp_memLp' hP

/-- The centered pressure class has the actual uniform extended norm bound two. -/
theorem ballCenteredPressureL_enorm_le_two
    (x : Vec3) {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (f : Lp ℝ 2 (volume.restrict (vec3Ball x R))) :
    ‖ballCenteredPressureL x hrR f‖ₑ ≤ 2 * ‖f‖ₑ := by
  have hb : ‖ballCenteredPressureL x hrR f‖ ≤ 2 * ‖f‖ :=
    ((ballCenteredPressureL x hrR).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (ballCenteredPressureL_norm_le x hr hrR) (norm_nonneg f))
  have he := ENNReal.ofReal_le_ofReal hb
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat, ofReal_norm] using he

/-- Actual centered restriction satisfies the norm-two bound in every time exponent. -/
theorem ballCenteredPressureL_eLpNorm_le_two
    (x : Vec3) {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R) {ν : Measure ℝ} (a : ℝ≥0∞)
    {P : ℝ → Lp ℝ 2 (volume.restrict (vec3Ball x R))}
    (hP : AEStronglyMeasurable P ν) :
    eLpNorm (fun t ↦ ballCenteredPressureL x hrR (P t)) a ν ≤ 2 * eLpNorm P a ν := by
  have hb := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (c := 2)
    (ballCenteredPressureL_aestronglyMeasurable x hrR hP)
    (.of_forall fun t ↦ ballCenteredPressureL_enorm_le_two x hr hrR (P t)) a
  simpa only [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_ofNat] using hb

/-- The centered class has its genuine zero spatial integral. -/
theorem ballCenteredPressureL_integral_zero
    (x : Vec3) {R r : ℝ} (hrR : r ≤ R)
    (f : Lp ℝ 2 (volume.restrict (vec3Ball x R))) :
    (∫ y in vec3Ball x r, ballCenteredPressureL x hrR f y) = 0 := by
  let : IsFiniteMeasure (volume.restrict (vec3Ball x r)) :=
    isFiniteMeasure_restrict.mpr volume_vec3Ball_lt_top.ne
  rw [integral_congr_ae (ballCenteredPressureL_ae x hrR f)]
  exact integral_sub_average _ _

end FluidSingularSets
