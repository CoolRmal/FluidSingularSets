-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.HarmonicTimeSmoothApprox
public import FluidSingularSets.HarmonicJointSmoothApprox
public import FluidSingularSets.UnitBallHarmonicForceHessian
public import FluidSingularSets.UnitBallHarmonicHessian
public import FluidSingularSets.StrongOperatorCurveLimits
public import FluidSingularSets.SuitableVelocityTimeBound
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Genuine smooth approximation of the suitable harmonic correction

The integration constant is recovered in the original energy-dual force space.
Time approximation therefore retains all pressure-value, gradient and Hessian
identities, rather than choosing an independent representative for each image.
-/

@[expose] public section

open MeasureTheory Set Filter CKN TopologicalSpace
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology BigOperators ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A true weak Banach-valued time derivative fixes one actual averaged
integration constant in the full Banach space. -/
theorem weakTimeDerivative_ae_averagedTimePrimitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b c : ℝ} (hab : a < b) (hc : c ∈ Ioo a b)
    {f g : ℝ → E} (hf : IntegrableOn f (Ioo a b) volume)
    (hg : IntegrableOn g (Ioo a b) volume)
    (hw : HasWeakTimeDerivativeOn (Ioo a b) f g) :
    f =ᵐ[volume.restrict (Ioo a b)] averagedTimePrimitive f g a b c := by
  let J := Ioo a b
  let P := averagedTimePrimitive f g a b c
  have hg₀ : Integrable (J.indicator g) volume :=
    hg.integrable_indicator measurableSet_Ioo
  have hP : Continuous P := continuous_const.add (hg₀.continuous_primitive c)
  have hR : IntegrableOn (fun t ↦ f t - P t) J volume :=
    hf.sub (hP.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
  have hzero : ∀ᵐ t ∂volume, t ∈ J → f t - P t = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      hR.locallyIntegrableOn
    intro η hη hηc hηs
    have hi : IntegrableOn (fun t ↦ η t • (f t - P t)) J volume :=
      hR.smul_of_top_right
        ((hη.continuous.memLp_top_of_hasCompactSupport hηc volume).mono_measure
          Measure.restrict_le_self)
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := J) (fun t ht ↦ by
        have hηt : η t = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ ht (hηs h))
        simp only [hηt, zero_smul])]
    apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
    intro L
    rw [← L.integral_comp_comm hi]
    have heq := weakTimeDerivative_scalar_ae_primitive hab hc hf hg hw L
    have hz : (fun t ↦ L (η t • (f t - P t))) =ᵐ[volume.restrict J] fun _ ↦ 0 := by
      filter_upwards [heq] with t ht
      simp only [map_smul, map_sub, P, averagedTimePrimitive,
        averagedTimePrimitiveConstant, map_add] at ht ⊢
      rw [ht]
      simp
    rw [integral_congr_ae hz, integral_zero]
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mpr hzero] with t ht
  exact sub_eq_zero.mp ht

/-- The genuine averaged force primitive is globally continuous, including the
time endpoints where the suitable field was originally only an AE class. -/
theorem averagedTimePrimitive_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b c : ℝ} {f g : ℝ → E} (hg : IntegrableOn g (Ioo a b) volume) :
    Continuous (averagedTimePrimitive f g a b c) :=
  continuous_const.add ((hg.integrable_indicator measurableSet_Ioo).continuous_primitive c)

local instance suitableSmoothForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance suitableSmoothForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The actual suitable velocity force agrees with its one continuous force
primitive, so every bounded linear pressure operator uses the same representative. -/
theorem suitable_unitBall_velocityForce_ae_primitive
    {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    unitBallVelocityForceCurve u =ᵐ[volume.restrict (Ioo (t₀ - 4) (t₀ + 4))]
      averagedTimePrimitive (unitBallVelocityForceCurve u)
        (unitBallMomentumForceCurve u Du p) (t₀ - 4) (t₀ + 4) t₀ := by
  obtain ⟨hf, hg⟩ := suitable_unitBall_momentumForces_integrable hsol hdom
  exact weakTimeDerivative_ae_averagedTimePrimitive (by linarith)
    ⟨by linarith, by linarith⟩ hf hg
    (suitable_unitBall_momentum_hasWeakTimeDerivativeOn hsol hdom)

def pressureCompactValueInclusion :
    C(unitBallPressureCompactInterior, unitBallPressureValueCompactInterior) where
  toFun x := ⟨x.1, subset_closure (vec3Ball_mono
    (by norm_num : (1 / 8 : ℝ) ≤ 1 / 5)
    (unitBallPressureCompactInterior_subset_eighth x.property))⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The canonical pressure values restricted to the actual compact test interior. -/
def harmonicCompactPressureValues : StokesEnergyForce (vec3Ball 0 1) →L[ℝ]
    C(unitBallPressureCompactInterior, ℝ) :=
  (ContinuousMap.compCLM ℝ ℝ pressureCompactValueInclusion).comp
    unitBallHarmonicForcePressureValuesExtended

@[simp]
theorem harmonicCompactPressureValues_apply (F : StokesEnergyForce (vec3Ball 0 1))
    (x : unitBallPressureCompactInterior) :
    harmonicCompactPressureValues F x = harmonicSpatialPressureRepresentative F x := rfl

def smoothCompactPressureMap {ε : ℝ} (hε : 0 < ε)
    (F : StokesEnergyForce (vec3Ball 0 1)) : C(unitBallPressureCompactInterior, ℝ) where
  toFun x := harmonicSpatialSmoothPressureKernel hε x.1 F
  continuous_toFun :=
    ((harmonicSpatialSmoothPressureKernel_contDiff hε).continuous.comp
      continuous_subtype_val).clm_apply continuous_const

private theorem smoothCompactPressureMap_error_le {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ 1 / 100) (F : StokesEnergyForce (vec3Ball 0 1)) :
    ‖smoothCompactPressureMap hε F - harmonicCompactPressureValues F‖ ≤
      3 * unitBallPressureGradientConstant * ε * ‖F‖ := by
  have hc := unitBallPressureGradientConstant_nonneg
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change |harmonicSpatialSmoothPressureKernel hε x.1 F -
    harmonicSpatialPressureRepresentative F x| ≤ _
  rw [harmonicSpatialSmoothPressureKernel_apply]
  convert harmonicSpatialSmoothPressure_error_le F hε hsmall x using 1
  ring

/-- Spatially smoothed pressure values form a genuine bounded linear force operator. -/
def harmonicSmoothCompactPressureValues {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ 1 / 100) : StokesEnergyForce (vec3Ball 0 1) →L[ℝ]
    C(unitBallPressureCompactInterior, ℝ) :=
  ({ toFun := smoothCompactPressureMap hε
     map_add' := fun F G ↦ by
       ext x
       exact (harmonicSpatialSmoothPressureKernel hε x.1).map_add F G
     map_smul' := fun c F ↦ by
       ext x
       exact (harmonicSpatialSmoothPressureKernel hε x.1).map_smul c F } :
    StokesEnergyForce (vec3Ball 0 1) →ₗ[ℝ] C(unitBallPressureCompactInterior, ℝ))
    |>.mkContinuous (‖harmonicCompactPressureValues‖ +
      3 * unitBallPressureGradientConstant / 100) (fun F ↦ by
      have he := smoothCompactPressureMap_error_le hε hsmall F
      have hb := harmonicCompactPressureValues.le_opNorm F
      have hc : 0 ≤ 3 * unitBallPressureGradientConstant :=
        mul_nonneg (by norm_num) unitBallPressureGradientConstant_nonneg
      have hr := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsmall hc) (norm_nonneg F)
      have ht := norm_add_le
        (smoothCompactPressureMap hε F - harmonicCompactPressureValues F)
        (harmonicCompactPressureValues F)
      simp only [sub_add_cancel] at ht
      calc
        _ ≤ (3 * unitBallPressureGradientConstant / 100) * ‖F‖ +
            ‖harmonicCompactPressureValues‖ * ‖F‖ := by
          exact ht.trans (add_le_add (he.trans (by nlinarith [hr])) hb)
        _ = _ := by ring)

@[simp]
theorem harmonicSmoothCompactPressureValues_apply {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ 1 / 100) (F : StokesEnergyForce (vec3Ball 0 1))
    (x : unitBallPressureCompactInterior) :
    harmonicSmoothCompactPressureValues hε hsmall F x =
      harmonicSpatialSmoothPressure F hε x :=
  harmonicSpatialSmoothPressureKernel_apply hε x.1 F

theorem harmonicSmoothCompactPressureValues_opNorm_le {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ 1 / 100) :
    ‖harmonicSmoothCompactPressureValues hε hsmall‖ ≤
      ‖harmonicCompactPressureValues‖ + 3 * unitBallPressureGradientConstant / 100 := by
  unfold harmonicSmoothCompactPressureValues
  have hc := unitBallPressureGradientConstant_nonneg
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- The real pressure-smoothing operators converge on every actual force. -/
theorem harmonicSmoothCompactPressureValues_tendsto
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n)
    (hsmall : ∀ n, ε n ≤ 1 / 100) (F : StokesEnergyForce (vec3Ball 0 1)) :
    Tendsto (fun n ↦ harmonicSmoothCompactPressureValues (hpos n) (hsmall n) F)
      atTop (𝓝 (harmonicCompactPressureValues F)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr : Tendsto (fun n ↦ 3 * unitBallPressureGradientConstant * ε n * ‖F‖)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (tendsto_const_nhds.mul hε).mul_const ‖F‖
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr
    (fun _ ↦ norm_nonneg _) (fun n ↦
      smoothCompactPressureMap_error_le (hpos n) (hsmall n) F)

/-- Strong time `L¹` force approximation gives genuine strong compact pressure
convergence after simultaneous spatial smoothing. -/
theorem harmonicSmoothCompactPressureValues_strong_one
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n)
    (hsmall : ∀ n, ε n ≤ 1 / 100)
    {g : ℝ → StokesEnergyForce (vec3Ball 0 1)}
    {gs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1)}
    (hg : MemLp g 1 volume) (hgs : ∀ n, MemLp (gs n) 1 volume)
    (hconv : Tendsto (fun n ↦ eLpNorm (gs n - g) 1 volume) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun t ↦
      harmonicSmoothCompactPressureValues (hpos n) (hsmall n) (gs n t) -
        harmonicCompactPressureValues (g t)) 1 volume) atTop (𝓝 0) :=
  tendsto_eLpNorm_moving_operator_curve_one
    (fun n ↦ harmonicSmoothCompactPressureValues_opNorm_le (hpos n) (hsmall n))
    (harmonicSmoothCompactPressureValues_tendsto hε hpos hsmall) hg hgs hconv

/-- The pressure convergence also holds in the genuine spatial `L²` classes on
every finite measure of the compact interior, not only in the uniform norm. -/
theorem harmonicSmoothCompactPressureValues_strong_spatialLp_one
    (μ : Measure unitBallPressureCompactInterior) [IsFiniteMeasure μ]
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n)
    (hsmall : ∀ n, ε n ≤ 1 / 100)
    {g : ℝ → StokesEnergyForce (vec3Ball 0 1)}
    {gs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1)}
    (hg : MemLp g 1 volume) (hgs : ∀ n, MemLp (gs n) 1 volume)
    (hconv : Tendsto (fun n ↦ eLpNorm (gs n - g) 1 volume) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun t ↦
      ContinuousMap.toLp 2 μ ℝ
        (harmonicSmoothCompactPressureValues (hpos n) (hsmall n) (gs n t)) -
      ContinuousMap.toLp 2 μ ℝ (harmonicCompactPressureValues (g t))) 1 volume)
      atTop (𝓝 0) := by
  let L := ContinuousMap.toLp (E := ℝ) 2 μ ℝ
  have hf := hg.continuousLinearMap_comp harmonicCompactPressureValues
  have hfs (n : ℕ) := (hgs n).continuousLinearMap_comp
    (harmonicSmoothCompactPressureValues (hpos n) (hsmall n))
  have hc := harmonicSmoothCompactPressureValues_strong_one hε hpos hsmall hg hgs hconv
  have hc' : Tendsto (fun n ↦ eLpNorm
      ((fun t ↦ harmonicCompactPressureValues (g t)) -
        fun t ↦ harmonicSmoothCompactPressureValues (hpos n) (hsmall n) (gs n t))
      1 volume) atTop (𝓝 0) := by
    convert hc using 1
    funext n
    exact eLpNorm_sub_comm _ _ _ _
  have hl := tendsto_eLpNorm_operator_sub L hf hfs hc'
  convert hl using 1
  funext n
  exact eLpNorm_sub_comm _ _ _ _

/-- These spatial classes represent the literal actual smoothed pressure values. -/
theorem harmonicSmoothCompactPressureValues_toLp_coe
    (μ : Measure unitBallPressureCompactInterior) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 100)
    (F : StokesEnergyForce (vec3Ball 0 1)) :
    ContinuousMap.toLp 2 μ ℝ (harmonicSmoothCompactPressureValues hε hsmall F)
      =ᵐ[μ] fun x ↦ harmonicSpatialSmoothPressure F hε x := by
  exact (ContinuousMap.coeFn_toLp μ _).trans (Eventually.of_forall fun x ↦
    harmonicSmoothCompactPressureValues_apply hε hsmall F x)

/-- Uniform force convergence and a common true force bound give simultaneous
uniform gradient convergence on the compact spatial and time sets. -/
theorem harmonicJointSmoothGradient_tendstoUniformly
    {a b : ℝ} {f : ℝ → StokesEnergyForce (vec3Ball 0 1)}
    {fs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1)}
    (hf : TendstoUniformly fs f atTop)
    {C : ℝ} (_hC : 0 ≤ C) (hbound : ∀ n t, t ∈ Icc a b → ‖fs n t‖ ≤ C)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n, 0 < ε n)
    (hsmall : ∀ n, ε n ≤ 1 / 100) :
    TendstoUniformly
      (fun n (z : unitBallPressureCompactInterior × Icc a b) ↦
        harmonicJointSmoothGradient (hpos n) (fs n) (z.1.1, z.2.1))
      (fun z ↦ unitBallHarmonicForceGradientExtended (f z.2.1) z.1) atTop := by
  have himage := unitBallHarmonicForceGradientExtended.uniformContinuous.comp_tendstoUniformly hf
  have herr : Tendsto (fun n ↦ 9 * unitBallPressureHessianConstant * C * ε n)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hε
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  filter_upwards [(Metric.tendstoUniformly_iff.mp himage) (δ / 2) (by positivity),
    (tendsto_order.mp herr).2 (δ / 2) (by positivity)] with n hn he z
  have hs := harmonicJointSmoothGradient_error_le (hpos n) (hsmall n) (fs n) z.1 z.2.1
  have hconst : 0 ≤ 9 * unitBallPressureHessianConstant :=
    mul_nonneg (by norm_num) unitBallPressureHessianConstant_nonneg
  have hs' : ‖harmonicJointSmoothGradient (hpos n) (fs n) (z.1.1, z.2.1) -
      unitBallHarmonicForceGradientExtended (fs n z.2.1) z.1‖ < δ / 2 :=
    (hs.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbound n z.2.1 z.2.2) hconst) (hpos n).le)).trans_lt he
  have ht := (unitBallHarmonicForceGradientExtended (f z.2.1) -
    unitBallHarmonicForceGradientExtended (fs n z.2.1)).norm_coe_le_norm z.1
  have ht' : ‖unitBallHarmonicForceGradientExtended (f z.2.1) z.1 -
      unitBallHarmonicForceGradientExtended (fs n z.2.1) z.1‖ < δ / 2 :=
    ht.trans_lt (by simpa only [dist_eq_norm, Function.comp_def] using hn z.2.1)
  rw [dist_eq_norm, norm_sub_rev]
  calc
    _ ≤ ‖harmonicJointSmoothGradient (hpos n) (fs n) (z.1.1, z.2.1) -
        unitBallHarmonicForceGradientExtended (fs n z.2.1) z.1‖ +
      ‖unitBallHarmonicForceGradientExtended (fs n z.2.1) z.1 -
        unitBallHarmonicForceGradientExtended (f z.2.1) z.1‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < δ := by rw [norm_sub_rev] at ht'; linarith

/-- A fixed explicit spatial mollifier scale tending to zero within the harmonic region. -/
def suitableHarmonicSmoothRadius (n : ℕ) : ℝ := 1 / (100 * ((n : ℝ) + 1))

theorem suitableHarmonicSmoothRadius_pos (n : ℕ) : 0 < suitableHarmonicSmoothRadius n := by
  unfold suitableHarmonicSmoothRadius
  positivity

theorem suitableHarmonicSmoothRadius_le (n : ℕ) : suitableHarmonicSmoothRadius n ≤ 1 / 100 := by
  unfold suitableHarmonicSmoothRadius
  apply one_div_le_one_div_of_le (by norm_num)
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem suitableHarmonicSmoothRadius_tendsto :
    Tendsto suitableHarmonicSmoothRadius atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  convert h.div_const 100 using 1
  · funext n
    simp only [suitableHarmonicSmoothRadius, div_eq_mul_inv, mul_inv_rev, one_mul]
  · norm_num

/-- Genuine suitable data gives smooth time primitives in the full force space,
with the true averaged constant, a common force bound and strong derivative convergence. -/
theorem exists_suitable_unitBall_force_smooth_sequence
    {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    ∃ gs fs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1),
      (∀ n, ContDiff ℝ ∞ (gs n) ∧ ContDiff ℝ ∞ (fs n) ∧
        HasCompactSupport (gs n) ∧
        tsupport (gs n) ⊆ meanApproxTimeSet (t₀ - 4) (t₀ + 4) ∧
        MemLp (gs n) 1 volume ∧ (∀ t, HasDerivAt (fs n) (gs n t) t)) ∧
      unitBallVelocityForceCurve u =ᵐ[volume.restrict (Ioo (t₀ - 4) (t₀ + 4))]
        averagedTimePrimitive (unitBallVelocityForceCurve u)
          (unitBallMomentumForceCurve u Du p) (t₀ - 4) (t₀ + 4) t₀ ∧
      Tendsto (fun n ↦ eLpNorm
        ((Ioo (t₀ - 4) (t₀ + 4)).indicator (unitBallMomentumForceCurve u Du p) - gs n)
        1 volume) atTop (𝓝 0) ∧
      TendstoUniformly fs
        (averagedTimePrimitive (unitBallVelocityForceCurve u)
          (unitBallMomentumForceCurve u Du p) (t₀ - 4) (t₀ + 4) t₀) atTop ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n t, t ∈ Icc (t₀ - 4) (t₀ + 4) → ‖fs n t‖ ≤ C := by
  obtain ⟨_, hg⟩ := suitable_unitBall_momentumForces_integrable hsol hdom
  obtain ⟨gs, fs, hsm, hconv, _, hunif, hbound⟩ :=
    exists_smooth_time_primitive_sequence (by linarith : t₀ - 4 < t₀ + 4)
      (by simp : (1 : ℝ≥0∞) ≤ 1) (by simp : (1 : ℝ≥0∞) ≠ ⊤)
      (memLp_one_iff_integrable.mpr hg)
      (averagedTimePrimitiveConstant (unitBallVelocityForceCurve u)
        (unitBallMomentumForceCurve u Du p) (t₀ - 4) (t₀ + 4) t₀) t₀
  exact ⟨gs, fs, hsm, suitable_unitBall_velocityForce_ae_primitive hsol hdom,
    hconv, hunif, hbound⟩

/-- The physical correction has the negative sign of the velocity-force primitive. -/
def unitBallJointHarmonicApproxGradient
    (fs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1)) (n : ℕ) : Vec3 × ℝ → Vec3 :=
  harmonicJointSmoothGradient (suitableHarmonicSmoothRadius_pos n) (fun t ↦ -fs n t)

/-- The genuine time derivative pressure of the physical smooth correction. -/
def unitBallJointHarmonicApproxPressure
    (gs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1)) (n : ℕ) : Vec3 × ℝ → ℝ :=
  harmonicJointSmoothPressure (suitableHarmonicSmoothRadius_pos n) (fun t ↦ -gs n t)

/-- Actual suitable weak solution data supplies jointly smooth correction fields,
the exact time-gradient identity and harmonicity, uniform correction convergence,
and strong time `L¹` convergence of the true compact pressure values. -/
theorem exists_suitable_unitBall_harmonic_joint_smooth_sequence
    {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    ∃ gs fs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1),
      (∀ n, ContDiff ℝ ∞ (gs n) ∧ ContDiff ℝ ∞ (fs n) ∧
        HasCompactSupport (gs n) ∧
        tsupport (gs n) ⊆ meanApproxTimeSet (t₀ - 4) (t₀ + 4) ∧
        MemLp (gs n) 1 volume ∧ (∀ t, HasDerivAt (fs n) (gs n t) t)) ∧
      unitBallVelocityForceCurve u =ᵐ[volume.restrict (Ioo (t₀ - 4) (t₀ + 4))]
        averagedTimePrimitive (unitBallVelocityForceCurve u)
          (unitBallMomentumForceCurve u Du p) (t₀ - 4) (t₀ + 4) t₀ ∧
      Tendsto (fun n ↦ eLpNorm
        ((Ioo (t₀ - 4) (t₀ + 4)).indicator (unitBallMomentumForceCurve u Du p) - gs n)
        1 volume) atTop (𝓝 0) ∧
      TendstoUniformly fs
        (averagedTimePrimitive (unitBallVelocityForceCurve u)
          (unitBallMomentumForceCurve u Du p) (t₀ - 4) (t₀ + 4) t₀) atTop ∧
      (∃ C : ℝ, 0 < C ∧ ∀ n t, t ∈ Icc (t₀ - 4) (t₀ + 4) → ‖fs n t‖ ≤ C) ∧
      (∀ n, ContDiff ℝ ∞ (unitBallJointHarmonicApproxGradient fs n) ∧
        ContDiff ℝ ∞ (unitBallJointHarmonicApproxPressure gs n) ∧
        (∀ z i, timePartial (fun w ↦ unitBallJointHarmonicApproxGradient fs n w i) z =
          spatialPartial (unitBallJointHarmonicApproxPressure gs n) i z) ∧
        (∀ z, z.1 ∈ vec3Ball 0 (1 / 12) →
          (∑ i : Fin 3, spatialPartial
            (fun w ↦ unitBallJointHarmonicApproxGradient fs n w i) i z) = 0) ∧
        (∀ z i, z.1 ∈ vec3Ball 0 (1 / 12) →
          (∑ j : Fin 3, spatialSecondPartial
            (fun w ↦ unitBallJointHarmonicApproxGradient fs n w i) j j z) = 0)) ∧
      TendstoUniformly
        (fun n (z : unitBallPressureCompactInterior × Icc (t₀ - 4) (t₀ + 4)) ↦
          unitBallJointHarmonicApproxGradient fs n (z.1.1, z.2.1))
        (fun z ↦ unitBallHarmonicTimePrimitive u Du p t₀ z.2.1 z.1) atTop ∧
      Tendsto (fun n ↦ eLpNorm (fun t ↦
        harmonicSmoothCompactPressureValues (suitableHarmonicSmoothRadius_pos n)
          (suitableHarmonicSmoothRadius_le n) (-gs n t) -
        harmonicCompactPressureValues
          (-((Ioo (t₀ - 4) (t₀ + 4)).indicator (unitBallMomentumForceCurve u Du p) t)))
        1 volume) atTop (𝓝 0) := by
  obtain ⟨gs, fs, hsm, hAE, hconv, hunif, C, hC, hbound⟩ :=
    exists_suitable_unitBall_force_smooth_sequence hsol hdom
  refine ⟨gs, fs, hsm, hAE, hconv, hunif, ⟨C, hC, hbound⟩, ?_, ?_, ?_⟩
  · intro n
    refine ⟨harmonicJointSmoothGradient_contDiff _ (hsm n).2.1.neg,
      harmonicJointSmoothPressure_contDiff _ (hsm n).1.neg, ?_, ?_, ?_⟩
    · intro z i
      exact harmonicJointSmoothGradient_timePartial _ (fun t ↦ ((hsm n).2.2.2.2.2 t).neg) z i
    · intro z hz
      exact harmonicJointSmoothGradient_divergence _ (suitableHarmonicSmoothRadius_le n)
        _ z hz
    · intro z i hz
      exact harmonicJointSmoothGradient_spatialSecondPartial _
        (suitableHarmonicSmoothRadius_le n) _ i z hz
  · have hneg : TendstoUniformly (fun n t ↦ -fs n t)
        (fun t ↦ -averagedTimePrimitive (unitBallVelocityForceCurve u)
          (unitBallMomentumForceCurve u Du p) (t₀ - 4) (t₀ + 4) t₀ t) atTop := by
      apply Metric.tendstoUniformly_iff.mpr
      intro δ hδ
      filter_upwards [(Metric.tendstoUniformly_iff.mp hunif) δ hδ] with n hn t
      simpa only [dist_neg_neg] using hn t
    have h := harmonicJointSmoothGradient_tendstoUniformly hneg hC.le
      (fun n t ht ↦ by simpa only [norm_neg] using hbound n t ht)
      suitableHarmonicSmoothRadius_tendsto suitableHarmonicSmoothRadius_pos
      suitableHarmonicSmoothRadius_le
    simpa only [unitBallJointHarmonicApproxGradient, unitBallHarmonicTimePrimitive,
      map_neg] using h
  · obtain ⟨_, hg⟩ := suitable_unitBall_momentumForces_integrable hsol hdom
    have hg₀ : MemLp ((Ioo (t₀ - 4) (t₀ + 4)).indicator
        (unitBallMomentumForceCurve u Du p)) 1 volume :=
      memLp_one_iff_integrable.mpr (hg.integrable_indicator measurableSet_Ioo)
    have hnegconv : Tendsto (fun n ↦ eLpNorm
        ((fun t ↦ -gs n t) - fun t ↦
          -((Ioo (t₀ - 4) (t₀ + 4)).indicator (unitBallMomentumForceCurve u Du p) t))
        1 volume) atTop (𝓝 0) := by
      convert hconv using 1
      funext n
      congr 1
      funext t
      simp only [Pi.sub_apply]
      abel
    exact harmonicSmoothCompactPressureValues_strong_one suitableHarmonicSmoothRadius_tendsto
      suitableHarmonicSmoothRadius_pos suitableHarmonicSmoothRadius_le
      hg₀.neg (fun n ↦ (hsm n).2.2.2.2.1.neg) hnegconv

end FluidSingularSets
