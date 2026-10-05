-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.MeanMotionBound
public import FluidSingularSets.WeightedVelocityPoincare

/-!
# Genuine normalized smooth spatial weights

The proved CKN mollified ball cutoff has positive mass on every positive-radius
ball. Normalizing that mass produces smooth compactly supported weights with
universal radius bounds, exact normalization, and a dimensionless weight budget
of at most `64` on the ball of twice the radius.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The genuine positive spatial mass of the CKN cutoff. -/
def normalizedWeightedCutoffMass (x₀ : Vec3) {R : ℝ} (hR : 0 < R) : ℝ :=
  ∫ x in vec3Ball x₀ R, mollifiedBallCutoff x₀ hR x

/-- The normalized smooth spatial weight used by both mean-motion and Poincaré estimates. -/
def normalizedWeightedCutoff (x₀ : Vec3) {R : ℝ} (hR : 0 < R) : Vec3 → ℝ :=
  fun x ↦ (normalizedWeightedCutoffMass x₀ hR)⁻¹ * mollifiedBallCutoff x₀ hR x

private theorem cutoff_tsupport_subset_ball (x₀ : Vec3) {R : ℝ} (hR : 0 < R) :
    tsupport (mollifiedBallCutoff x₀ hR) ⊆ vec3Ball x₀ R := by
  have hs := mollifiedBallCutoff_tsupport_subset_outer x₀ hR
  rw [euclideanBall_eq_vec3Ball (by positivity : 0 < 3 * R / 4)] at hs
  exact hs.trans (vec3Ball_mono (by linarith))

private theorem cutoff_integrable (x₀ : Vec3) {R : ℝ} (hR : 0 < R) :
    Integrable (mollifiedBallCutoff x₀ hR) volume :=
  (mollifiedBallCutoff_smooth x₀ hR).continuous.integrable_of_hasCompactSupport
    (mollifiedBallCutoff_hasCompactSupport x₀ hR)

private theorem real_volume_vec3Ball (x₀ : Vec3) {R : ℝ} (hR : 0 ≤ R) :
    (volume (vec3Ball x₀ R)).toReal = meanMotionBallVolume * R ^ 3 := by
  rw [volume_vec3Ball_eq, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hR,
    ENNReal.toReal_ofReal (by have h := Real.pi_pos; positivity)]
  unfold meanMotionBallVolume
  ring

/-- The cutoff is one on a ball of half the radius, so its mass has a universal lower bound. -/
theorem normalizedWeightedCutoffMass_lower (x₀ : Vec3) {R : ℝ} (hR : 0 < R) :
    meanMotionBallVolume * R ^ 3 / 8 ≤ normalizedWeightedCutoffMass x₀ hR := by
  have hone : ∀ x ∈ vec3Ball x₀ (R / 2), mollifiedBallCutoff x₀ hR x = 1 := by
    intro x hx
    apply mollifiedBallCutoff_eq_one_on_inner x₀ hR
    rw [euclideanBall_eq_vec3Ball (by positivity : 0 < 13 * R / 20)]
    exact vec3Ball_mono (by linarith) hx
  have hinner : (∫ x in vec3Ball x₀ (R / 2), mollifiedBallCutoff x₀ hR x) =
      (volume (vec3Ball x₀ (R / 2))).toReal := by
    rw [setIntegral_congr_fun (isOpen_vec3Ball _ _).measurableSet hone,
      setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  have hmono := setIntegral_mono_set (s := vec3Ball x₀ (R / 2)) (t := vec3Ball x₀ R)
    (cutoff_integrable x₀ hR).integrableOn
    (Eventually.of_forall (mollifiedBallCutoff_nonneg x₀ hR))
    (vec3Ball_mono (x := x₀) (by linarith : R / 2 ≤ R)).eventuallySubset
  rw [hinner, real_volume_vec3Ball x₀ (by positivity : 0 ≤ R / 2)] at hmono
  exact (show meanMotionBallVolume * R ^ 3 / 8 = meanMotionBallVolume * (R / 2) ^ 3
    by ring).le.trans hmono

theorem normalizedWeightedCutoffMass_pos (x₀ : Vec3) {R : ℝ} (hR : 0 < R) :
    0 < normalizedWeightedCutoffMass x₀ hR := by
  have hpos : 0 < meanMotionBallVolume * R ^ 3 / 8 := by
    have hV := meanMotionBallVolume_pos
    positivity
  exact hpos.trans_le (normalizedWeightedCutoffMass_lower x₀ hR)

theorem normalizedWeightedCutoff_smooth (x₀ : Vec3) {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ (⊤ : ℕ∞) (normalizedWeightedCutoff x₀ hR) :=
  contDiff_const.mul (mollifiedBallCutoff_smooth x₀ hR)

theorem normalizedWeightedCutoff_hasCompactSupport (x₀ : Vec3) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (normalizedWeightedCutoff x₀ hR) := by
  exact HasCompactSupport.of_support_subset_isCompact
    (mollifiedBallCutoff_hasCompactSupport x₀ hR).isCompact
    (fun x hx ↦ by
      apply subset_tsupport (mollifiedBallCutoff x₀ hR)
      intro hzero
      exact hx (by simp only [normalizedWeightedCutoff, hzero, mul_zero]))

theorem normalizedWeightedCutoff_tsupport_subset (x₀ : Vec3) {R : ℝ} (hR : 0 < R) :
    tsupport (normalizedWeightedCutoff x₀ hR) ⊆ vec3Ball x₀ R := by
  exact (tsupport_mul_subset_right (f := fun _ : Vec3 ↦
    (normalizedWeightedCutoffMass x₀ hR)⁻¹)).trans (cutoff_tsupport_subset_ball x₀ hR)

theorem normalizedWeightedCutoff_nonneg (x₀ : Vec3) {R : ℝ} (hR : 0 < R) (x : Vec3) :
    0 ≤ normalizedWeightedCutoff x₀ hR x :=
  mul_nonneg (inv_nonneg.mpr (normalizedWeightedCutoffMass_pos x₀ hR).le)
    (mollifiedBallCutoff_nonneg x₀ hR x)

/-- The chosen weight is exactly normalized on its defining spatial ball. -/
theorem normalizedWeightedCutoff_integral_eq_one (x₀ : Vec3) {R : ℝ} (hR : 0 < R) :
    (∫ x in vec3Ball x₀ R, normalizedWeightedCutoff x₀ hR x) = 1 := by
  change (∫ x in vec3Ball x₀ R,
    (normalizedWeightedCutoffMass x₀ hR)⁻¹ * mollifiedBallCutoff x₀ hR x) = 1
  rw [integral_const_mul]
  exact inv_mul_cancel₀ (normalizedWeightedCutoffMass_pos x₀ hR).ne'

/-- Normalization holds on every larger spatial ball as well. -/
theorem normalizedWeightedCutoff_integral_larger_eq_one
    (x₀ : Vec3) {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S) :
    (∫ x in vec3Ball x₀ S, normalizedWeightedCutoff x₀ hR x) = 1 := by
  have hzero (x : Vec3) (hx : x ∉ vec3Ball x₀ R) : normalizedWeightedCutoff x₀ hR x = 0 := by
    by_contra hne
    exact hx (normalizedWeightedCutoff_tsupport_subset x₀ hR
      (subset_tsupport (normalizedWeightedCutoff x₀ hR) hne))
  have hsmall := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hzero
  have hlarge := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
    (fun x hx ↦ hzero x (fun h ↦ hx (vec3Ball_mono hRS h)))
  rw [hlarge, ← hsmall]
  exact normalizedWeightedCutoff_integral_eq_one x₀ hR

/-- The exact inverse mass is a uniform pointwise bound for the normalized weight. -/
theorem normalizedWeightedCutoff_norm_le_inv_mass
    (x₀ : Vec3) {R : ℝ} (hR : 0 < R) (x : Vec3) :
    ‖normalizedWeightedCutoff x₀ hR x‖ ≤ (normalizedWeightedCutoffMass x₀ hR)⁻¹ := by
  rw [Real.norm_of_nonneg (normalizedWeightedCutoff_nonneg x₀ hR x)]
  exact (mul_le_mul_of_nonneg_left (mollifiedBallCutoff_le_one x₀ hR x)
    (inv_nonneg.mpr (normalizedWeightedCutoffMass_pos x₀ hR).le)).trans_eq (mul_one _)

/-- The universal `R^-3` bound follows from the positive inner-ball mass. -/
theorem normalizedWeightedCutoff_inv_mass_le
    (x₀ : Vec3) {R : ℝ} (hR : 0 < R) :
    (normalizedWeightedCutoffMass x₀ hR)⁻¹ ≤
      (8 / meanMotionBallVolume) * R ^ (-3 : ℝ) := by
  have hV := meanMotionBallVolume_pos
  have hlower : 0 < meanMotionBallVolume * R ^ 3 / 8 := by positivity
  calc
    _ ≤ (meanMotionBallVolume * R ^ 3 / 8)⁻¹ :=
      (inv_le_inv₀ (normalizedWeightedCutoffMass_pos x₀ hR) hlower).2
        (normalizedWeightedCutoffMass_lower x₀ hR)
    _ = _ := by
      rw [Real.rpow_neg hR.le]
      simp only [Real.rpow_ofNat]
      field_simp [hR.ne', hV.ne']

private theorem cutoff_gradient_constant_nonneg : 0 ≤ cutoffGradientConstant := by
  have h := mollifiedBallCutoff_gradient_bound (0 : Vec3) (ρ := 1) (by norm_num) 0
  norm_num only [div_one] at h
  exact (vecEuclideanNorm_nonneg _).trans h

/-- One universal constant controls both the normalized weight and its gradient. -/
def normalizedWeightedCutoffScaleConstant : ℝ :=
  (8 / meanMotionBallVolume) * (1 + cutoffGradientConstant)

theorem normalizedWeightedCutoffScaleConstant_pos : 0 < normalizedWeightedCutoffScaleConstant := by
  unfold normalizedWeightedCutoffScaleConstant
  have hV := meanMotionBallVolume_pos
  have hgrad := cutoff_gradient_constant_nonneg
  positivity

theorem normalizedWeightedCutoff_norm_le
    (x₀ : Vec3) {R : ℝ} (hR : 0 < R) (x : Vec3) :
    ‖normalizedWeightedCutoff x₀ hR x‖ ≤ normalizedWeightedCutoffScaleConstant *
      R ^ (-3 : ℝ) := by
  have hcoeff : 8 / meanMotionBallVolume ≤ normalizedWeightedCutoffScaleConstant := by
    unfold normalizedWeightedCutoffScaleConstant
    have hV := meanMotionBallVolume_pos
    have hgrad := cutoff_gradient_constant_nonneg
    nlinarith [div_pos (by norm_num : (0 : ℝ) < 8) hV]
  exact ((normalizedWeightedCutoff_norm_le_inv_mass x₀ hR x).trans
    (normalizedWeightedCutoff_inv_mass_le x₀ hR)).trans
      (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hR.le _))

theorem normalizedWeightedCutoff_spatialDeriv
    (x₀ : Vec3) {R : ℝ} (hR : 0 < R) (x : Vec3) (i : Fin 3) :
    spatialDeriv (normalizedWeightedCutoff x₀ hR) i x =
      (normalizedWeightedCutoffMass x₀ hR)⁻¹ *
        spatialDeriv (mollifiedBallCutoff x₀ hR) i x := by
  unfold normalizedWeightedCutoff spatialDeriv
  rw [fderiv_const_mul ((mollifiedBallCutoff_smooth x₀ hR).differentiable (by simp) x)]
  rfl

/-- The actual gradient of the normalized weight has a universal `R^-4` bound. -/
theorem normalizedWeightedCutoff_spatialDeriv_norm_le
    (x₀ : Vec3) {R : ℝ} (hR : 0 < R) (x : Vec3) (i : Fin 3) :
    ‖spatialDeriv (normalizedWeightedCutoff x₀ hR) i x‖ ≤
      normalizedWeightedCutoffScaleConstant * R ^ (-4 : ℝ) := by
  have hgrad := cutoff_gradient_constant_nonneg
  have hV := meanMotionBallVolume_pos
  have hmi := (normalizedWeightedCutoffMass_pos x₀ hR).le
  have hη : ‖spatialDeriv (mollifiedBallCutoff x₀ hR) i x‖ ≤
      cutoffGradientConstant / R := by
    have hh := (abs_apply_le_vecEuclideanNorm
      (classicalGradient (mollifiedBallCutoff x₀ hR) x) i).trans
      (mollifiedBallCutoff_gradient_bound x₀ hR x)
    simpa only [Real.norm_eq_abs, spatialDeriv, classicalGradient_apply] using hh
  have hcoeff : (8 / meanMotionBallVolume) * cutoffGradientConstant ≤
      normalizedWeightedCutoffScaleConstant := by
    unfold normalizedWeightedCutoffScaleConstant
    nlinarith [div_pos (by norm_num : (0 : ℝ) < 8) hV]
  rw [normalizedWeightedCutoff_spatialDeriv, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hmi)]
  calc
    _ ≤ (normalizedWeightedCutoffMass x₀ hR)⁻¹ * (cutoffGradientConstant / R) :=
      mul_le_mul_of_nonneg_left hη (inv_nonneg.mpr hmi)
    _ ≤ ((8 / meanMotionBallVolume) * R ^ (-3 : ℝ)) * (cutoffGradientConstant / R) :=
      mul_le_mul_of_nonneg_right (normalizedWeightedCutoff_inv_mass_le x₀ hR) (by positivity)
    _ = ((8 / meanMotionBallVolume) * cutoffGradientConstant) * R ^ (-4 : ℝ) := by
      simp only [div_eq_mul_inv]
      rw [← Real.rpow_neg_one R]
      calc
        _ = ((8 / meanMotionBallVolume) * cutoffGradientConstant) *
            (R ^ (-3 : ℝ) * R ^ (-1 : ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hR]; norm_num [div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hR.le _)

/-- The inverse-mass weight bound has a uniform dimensionless budget on the
outer ball, which is the input needed by weighted Sobolev-Poincaré. -/
theorem normalizedWeightedCutoff_weight_budget
    (x₀ : Vec3) {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal ((normalizedWeightedCutoffMass x₀ hR)⁻¹) *
      volume (vec3Ball x₀ (2 * R)) ≤ (64 : ℝ≥0∞) := by
  have hV := meanMotionBallVolume_pos
  have hmi := (normalizedWeightedCutoffMass_pos x₀ hR).le
  have hreal : (normalizedWeightedCutoffMass x₀ hR)⁻¹ *
      (meanMotionBallVolume * (2 * R) ^ 3) ≤ 64 := by
    calc
      _ ≤ ((8 / meanMotionBallVolume) * R ^ (-3 : ℝ)) *
          (meanMotionBallVolume * (2 * R) ^ 3) :=
        mul_le_mul_of_nonneg_right (normalizedWeightedCutoff_inv_mass_le x₀ hR) (by positivity)
      _ = _ := by
        rw [Real.rpow_neg hR.le]
        simp only [Real.rpow_ofNat]
        field_simp [hR.ne', hV.ne']
        ring
  have hvolume : volume (vec3Ball x₀ (2 * R)) =
      ENNReal.ofReal (meanMotionBallVolume * (2 * R) ^ 3) := by
    rw [volume_vec3Ball_eq, ← ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * R),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * R) ^ 3)]
    congr 1
    unfold meanMotionBallVolume
    ring
  rw [hvolume, ← ENNReal.ofReal_mul (inv_nonneg.mpr hmi)]
  exact (ENNReal.ofReal_le_ofReal hreal).trans_eq (by norm_num)

/-- Every exponent has the standard volume-scaled seminorm estimate. -/
theorem normalizedWeightedCutoff_eLpNorm_le
    (x₀ : Vec3) {R : ℝ} (hR : 0 < R) (a : ℝ≥0∞) (B : Set Vec3) :
    eLpNorm (normalizedWeightedCutoff x₀ hR) a (volume.restrict B) ≤
      ENNReal.ofReal (normalizedWeightedCutoffScaleConstant * R ^ (-3 : ℝ)) *
        (volume B) ^ a.toReal⁻¹ := by
  simpa only [Measure.restrict_apply_univ, mul_comm] using
    eLpNorm_le_of_ae_bound (p := a) (μ := volume.restrict B)
      (normalizedWeightedCutoff_smooth x₀ hR).continuous.aestronglyMeasurable
      (Eventually.of_forall (normalizedWeightedCutoff_norm_le x₀ hR))

/-- The corresponding seminorm estimate for every spatial derivative. -/
theorem normalizedWeightedCutoff_spatialDeriv_eLpNorm_le
    (x₀ : Vec3) {R : ℝ} (hR : 0 < R) (i : Fin 3) (a : ℝ≥0∞) (B : Set Vec3) :
    eLpNorm (spatialDeriv (normalizedWeightedCutoff x₀ hR) i) a (volume.restrict B) ≤
      ENNReal.ofReal (normalizedWeightedCutoffScaleConstant * R ^ (-4 : ℝ)) *
        (volume B) ^ a.toReal⁻¹ := by
  have hd := (contDiff_spatialDeriv_smooth (normalizedWeightedCutoff_smooth x₀ hR) i).continuous
  simpa only [Measure.restrict_apply_univ, mul_comm] using
    eLpNorm_le_of_ae_bound (p := a) (μ := volume.restrict B) hd.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ normalizedWeightedCutoff_spatialDeriv_norm_le x₀ hR x i)

/-- The actual weight belongs to every exponent on every finite spatial box. -/
theorem normalizedWeightedCutoff_memLp
    (x₀ : Vec3) {R : ℝ} (hR : 0 < R) (a : ℝ≥0∞)
    {B : Set Vec3} (hB : volume B < ∞) :
    MemLp (normalizedWeightedCutoff x₀ hR) a (volume.restrict B) := by
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hB.ne
  exact MemLp.of_bound (normalizedWeightedCutoff_smooth x₀ hR).continuous.aestronglyMeasurable
    (normalizedWeightedCutoffScaleConstant * R ^ (-3 : ℝ))
    (Eventually.of_forall (normalizedWeightedCutoff_norm_le x₀ hR))

theorem normalizedWeightedCutoff_spatialDeriv_memLp
    (x₀ : Vec3) {R : ℝ} (hR : 0 < R) (i : Fin 3) (a : ℝ≥0∞)
    {B : Set Vec3} (hB : volume B < ∞) :
    MemLp (spatialDeriv (normalizedWeightedCutoff x₀ hR) i) a (volume.restrict B) := by
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hB.ne
  have hd := (contDiff_spatialDeriv_smooth (normalizedWeightedCutoff_smooth x₀ hR) i).continuous
  exact MemLp.of_bound hd.aestronglyMeasurable
    (normalizedWeightedCutoffScaleConstant * R ^ (-4 : ℝ))
    (Eventually.of_forall fun x ↦ normalizedWeightedCutoff_spatialDeriv_norm_le x₀ hR x i)

/-- The weighted velocity mean is identical on the defining ball and any
larger ball, because the weight has its actual compact support in the smaller ball. -/
theorem normalizedWeightedCutoff_weightedVelocityMean_larger
    (x₀ : Vec3) {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S)
    (u : ParabolicPoint → Vec3) (i : Fin 3) (t : ℝ) :
    weightedVelocityMean (vec3Ball x₀ S) (normalizedWeightedCutoff x₀ hR) u i t =
      weightedVelocityMean (vec3Ball x₀ R) (normalizedWeightedCutoff x₀ hR) u i t := by
  have hzero (x : Vec3) (hx : x ∉ vec3Ball x₀ R) :
      u (x, t) i * normalizedWeightedCutoff x₀ hR x = 0 := by
    have hχzero : normalizedWeightedCutoff x₀ hR x = 0 := by
      by_contra hne
      exact hx (normalizedWeightedCutoff_tsupport_subset x₀ hR
        (subset_tsupport (normalizedWeightedCutoff x₀ hR) hne))
    rw [hχzero, mul_zero]
  unfold weightedVelocityMean
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx ↦ hzero x (fun h ↦ hx (vec3Ball_mono hRS h))),
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero]

/-- The actual suitable velocity satisfies the mixed fluctuation estimate
with the chosen normalized weight and the universal dimensionless budget `64`. -/
theorem suitable_normalizedWeightedCutoff_mixed_sobolevPoincare
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    (x₀ : Vec3) {R : ℝ} (hR : 0 < R) (J : Set ℝ)
    (hbox : localBox Ω I (vec3Ball x₀ (2 * R)) J) :
    (∫⁻ t in J, eLpNorm (fun x ↦ vec3EuclideanNorm (fun i : Fin 3 ↦
      u (x, t) i - weightedVelocityMean (vec3Ball x₀ R)
        (normalizedWeightedCutoff x₀ hR) u i t)) 6
          (volume.restrict (vec3Ball x₀ (2 * R))) ^ (2 : ℝ)) ≤
      weightedVelocityEuclideanPoincareConstant 64 ^ (2 : ℝ) *
        ∫⁻ z in spaceTimeSet (vec3Ball x₀ (2 * R)) J, ‖D z‖ₑ ^ (2 : ℝ) := by
  have h2R : 0 < 2 * R := by positivity
  have hball := euclideanBall_eq_vec3Ball (x₀ := x₀) h2R
  have hχInt : IntegrableOn (normalizedWeightedCutoff x₀ hR)
      (euclideanBall x₀ (2 * R)) := by
    rw [hball]
    exact (memLp_one_iff_integrable.mp
      (normalizedWeightedCutoff_memLp x₀ hR 1 volume_vec3Ball_lt_top))
  have hnormal : (∫ x in euclideanBall x₀ (2 * R), normalizedWeightedCutoff x₀ hR x) = 1 := by
    rw [hball]
    exact normalizedWeightedCutoff_integral_larger_eq_one x₀ hR (by linarith)
  have hbudget : ENNReal.ofReal ((normalizedWeightedCutoffMass x₀ hR)⁻¹) *
      volume (euclideanBall x₀ (2 * R)) ≤ ENNReal.ofReal (64 : ℝ) := by
    rw [hball]
    simpa only [ENNReal.ofReal_ofNat] using normalizedWeightedCutoff_weight_budget x₀ hR
  have hmain := suitable_integrated_weightedVelocity_euclidean_sobolevPoincare
    hsol x₀ h2R J (by simpa only [hball] using hbox)
    ((normalizedWeightedCutoffMass x₀ hR)⁻¹) 64 (by norm_num) hχInt hnormal
    (Eventually.of_forall (normalizedWeightedCutoff_norm_le_inv_mass x₀ hR)) hbudget
  rw [hball] at hmain
  have hmean (i : Fin 3) (t : ℝ) :
      (∫ y in vec3Ball x₀ (2 * R), u (y, t) i * normalizedWeightedCutoff x₀ hR y) =
        weightedVelocityMean (vec3Ball x₀ R) (normalizedWeightedCutoff x₀ hR) u i t :=
    normalizedWeightedCutoff_weightedVelocityMean_larger x₀ hR (by linarith) u i t
  have hpre : parabolicHomeomorph.symm ⁻¹' spaceTimeSet (vec3Ball x₀ (2 * R)) J =
      vec3Ball x₀ (2 * R) ×ˢ J := by ext w; rfl
  have hcharge := parabolicHomeomorphSymm_measurePreserving.setLIntegral_comp_preimage_emb
    parabolicHomeomorph.symm.measurableEmbedding
    (fun z ↦ ‖D z‖ₑ ^ (2 : ℝ)) (spaceTimeSet (vec3Ball x₀ (2 * R)) J)
  rw [hpre] at hcharge
  rw [← hcharge]
  simpa only [hmean, parabolicHomeomorph_symm_apply] using hmain

/-- Genuine normalized weights at every radius meet both quantitative APIs
with one universal scale constant and the fixed Poincaré budget `64`. -/
theorem exists_normalized_scaled_weight (x₀ : Vec3) {R : ℝ} (hR : 0 < R) :
    ∃ (χ : Vec3 → ℝ) (L : ℝ), ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ vec3Ball x₀ R ∧
      (∀ x, 0 ≤ χ x) ∧
      (∫ x in vec3Ball x₀ R, χ x) = 1 ∧
      (∫ x in vec3Ball x₀ (2 * R), χ x) = 1 ∧
      (∀ x, ‖χ x‖ ≤ L) ∧
      ENNReal.ofReal L * volume (vec3Ball x₀ (2 * R)) ≤ (64 : ℝ≥0∞) ∧
      (∀ x, ‖χ x‖ ≤ normalizedWeightedCutoffScaleConstant * R ^ (-3 : ℝ)) ∧
      ∀ x i, ‖spatialDeriv χ i x‖ ≤
        normalizedWeightedCutoffScaleConstant * R ^ (-4 : ℝ) := by
  exact ⟨normalizedWeightedCutoff x₀ hR, (normalizedWeightedCutoffMass x₀ hR)⁻¹,
    normalizedWeightedCutoff_smooth x₀ hR,
    normalizedWeightedCutoff_hasCompactSupport x₀ hR,
    normalizedWeightedCutoff_tsupport_subset x₀ hR,
    normalizedWeightedCutoff_nonneg x₀ hR,
    normalizedWeightedCutoff_integral_eq_one x₀ hR,
    normalizedWeightedCutoff_integral_larger_eq_one x₀ hR (by linarith),
    normalizedWeightedCutoff_norm_le_inv_mass x₀ hR,
    normalizedWeightedCutoff_weight_budget x₀ hR,
    normalizedWeightedCutoff_norm_le x₀ hR,
    normalizedWeightedCutoff_spatialDeriv_norm_le x₀ hR⟩

end FluidSingularSets
