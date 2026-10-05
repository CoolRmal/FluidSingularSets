-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.MixedPressure
public import CKN.Foundation.Parabolic.Vec3Norm

/-!
# Cubic velocity decay from mean subtraction

The small-ball cubic velocity mass splits into its spatial oscillation and its
spatial mean. Jensen's inequality makes the mean contribution decay with the
volume ratio. The oscillation is controlled by the proved mixed-gradient estimate.

The Euclidean averaging argument adapts the CKN proofs of Scott Armstrong and
Vlad Vicol, distributed under the Apache 2.0 license.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Jensen controls the cubic Euclidean norm of the actual spatial mean. -/
theorem euclideanMeanCubicBound
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {u : Vec3 → Vec3}
    (hu : IntegrableOn u (vec3Ball x₀ ρ) volume)
    (hu3 : IntegrableOn (fun x ↦ vec3EuclideanNorm (u x) ^ (3 : ℕ))
      (vec3Ball x₀ ρ) volume) :
    ENNReal.ofReal (vec3EuclideanNorm (average (volume.restrict (vec3Ball x₀ ρ)) u)) ^
        (3 : ℕ) ≤
      (volume (vec3Ball x₀ ρ))⁻¹ *
        ∫⁻ x in vec3Ball x₀ ρ, ENNReal.ofReal (vec3EuclideanNorm (u x)) ^ (3 : ℕ) := by
  let B := vec3Ball x₀ ρ
  let L := (PiLp.continuousLinearEquiv (2 : ℝ≥0∞) ℝ
    (fun _ : Fin 3 ↦ ℝ)).symm
  have hLint : IntegrableOn (fun x ↦ L (u x)) B volume :=
    L.toContinuousLinearMap.integrable_comp hu
  have hL3 : IntegrableOn (fun x ↦ ‖L (u x)‖ ^ (3 : ℝ)) B volume := by
    simpa only [vec3EuclideanNorm_eq_l2,
      show (L : Vec3 → L2Vec3) = WithLp.toLp 2 by rfl, Real.rpow_ofNat] using hu3
  have h := setAverage_norm_rpow_le (p := (3 : ℝ)) (by norm_num)
    (volume_vec3Ball_pos hρ) volume_vec3Ball_lt_top hLint hL3
  have hmap : L (average (volume.restrict B) u) =
      average (volume.restrict B) (fun x ↦ L (u x)) := by
    rw [average_eq, average_eq, map_smul, L.integral_comp_comm]
  rw [← hmap] at h
  have hreal : vec3EuclideanNorm (average (volume.restrict B) u) ^ (3 : ℕ) ≤
      (volume B).toReal⁻¹ * ∫ x in B, vec3EuclideanNorm (u x) ^ (3 : ℕ) := by
    simpa only [vec3EuclideanNorm_eq_l2,
      show (L : Vec3 → L2Vec3) = WithLp.toLp 2 by rfl, Real.rpow_ofNat,
      average_eq, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ] using h
  have hmass : ENNReal.ofReal (∫ x in B, vec3EuclideanNorm (u x) ^ (3 : ℕ)) =
      ∫⁻ x in B, ENNReal.ofReal (vec3EuclideanNorm (u x)) ^ (3 : ℕ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hu3
      (Eventually.of_forall (fun x ↦ pow_nonneg (vec3EuclideanNorm_nonneg _) 3))]
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _)]
  have hrealpos : 0 < (volume B).toReal :=
    ENNReal.toReal_pos (volume_vec3Ball_pos hρ).ne' volume_vec3Ball_lt_top.ne
  have hb := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _),
    ENNReal.ofReal_mul (inv_nonneg.mpr (le_of_lt hrealpos)),
    ENNReal.ofReal_inv_of_pos hrealpos,
    ENNReal.ofReal_toReal volume_vec3Ball_lt_top.ne, hmass] at hb
  exact hb

/-- A velocity slice splits into oscillation on the large ball and a mean
contribution weighted by the exact small-ball volume ratio. -/
theorem velocitySliceMeanSplit
    {x₀ : Vec3} {ρ r : ℝ} (hρ : 0 < ρ) (hrρ : r ≤ ρ)
    {u : Vec3 → Vec3} (hu : IntegrableOn u (vec3Ball x₀ ρ) volume)
    (hu3 : IntegrableOn (fun x ↦ vec3EuclideanNorm (u x) ^ (3 : ℕ))
      (vec3Ball x₀ ρ) volume) :
    (∫⁻ x in vec3Ball x₀ r, ENNReal.ofReal (vec3EuclideanNorm (u x)) ^ (3 : ℕ)) ≤
      4 * (∫⁻ x in vec3Ball x₀ ρ, ENNReal.ofReal (vec3EuclideanNorm
        (u x - average (volume.restrict (vec3Ball x₀ ρ)) u)) ^ (3 : ℕ)) +
      4 * volume (vec3Ball x₀ r) * (volume (vec3Ball x₀ ρ))⁻¹ *
        ∫⁻ x in vec3Ball x₀ ρ, ENNReal.ofReal (vec3EuclideanNorm (u x)) ^ (3 : ℕ) := by
  let B := vec3Ball x₀ ρ
  let b := vec3Ball x₀ r
  let c := average (volume.restrict B) u
  have hsub : b ⊆ B := vec3Ball_mono hrρ
  have hcent : AEMeasurable (fun x ↦ ENNReal.ofReal (vec3EuclideanNorm (u x - c)) ^
      (3 : ℕ)) (volume.restrict b) := by
    have hmc := Continuous.comp_aestronglyMeasurable
      CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm
        ((hu.mono_set hsub).aestronglyMeasurable.sub
          (aestronglyMeasurable_const (b := c)))
    exact hmc.aemeasurable.ennreal_ofReal.pow_const 3
  have hpoint (x : Vec3) : ENNReal.ofReal (vec3EuclideanNorm (u x)) ^ (3 : ℕ) ≤
      4 * (ENNReal.ofReal (vec3EuclideanNorm (u x - c)) ^ (3 : ℕ) +
        ENNReal.ofReal (vec3EuclideanNorm c) ^ (3 : ℕ)) := by
    have ht : vec3EuclideanNorm (u x) ≤
        vec3EuclideanNorm (u x - c) + vec3EuclideanNorm c := by
      simpa only [sub_add_cancel] using vec3EuclideanNorm_add_le (u x - c) c
    have he := ENNReal.ofReal_le_ofReal ht
    rw [ENNReal.ofReal_add (vec3EuclideanNorm_nonneg _) (vec3EuclideanNorm_nonneg _)] at he
    apply (pow_le_pow_left' he 3).trans
    have hs := ENNReal.rpow_add_le_mul_rpow_add_rpow
      (ENNReal.ofReal (vec3EuclideanNorm (u x - c)))
      (ENNReal.ofReal (vec3EuclideanNorm c)) (by norm_num : (1 : ℝ) ≤ 3)
    norm_num only [ENNReal.rpow_ofNat] at hs
    exact hs
  have hm := euclideanMeanCubicBound hρ hu hu3
  calc
    _ ≤ ∫⁻ x in b, 4 *
        (ENNReal.ofReal (vec3EuclideanNorm (u x - c)) ^ (3 : ℕ) +
          ENNReal.ofReal (vec3EuclideanNorm c) ^ (3 : ℕ)) := lintegral_mono hpoint
    _ = 4 * (∫⁻ x in b, ENNReal.ofReal (vec3EuclideanNorm (u x - c)) ^ (3 : ℕ)) +
        4 * volume b * ENNReal.ofReal (vec3EuclideanNorm c) ^ (3 : ℕ) := by
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left' hcent,
        lintegral_const]
      simp only [Measure.restrict_apply_univ]
      ring
    _ ≤ _ := by
      apply add_le_add
      · gcongr
      · have hmul := mul_le_mul' (le_refl (4 * volume b)) hm
        simpa only [mul_assoc] using hmul

/-- The exact volume ratio of concentric three-dimensional balls. -/
theorem velocityBallVolumeRatio {x₀ : Vec3} {r ρ : ℝ} (hr : 0 ≤ r) (hρ : 0 < ρ) :
    volume (vec3Ball x₀ r) * (volume (vec3Ball x₀ ρ))⁻¹ =
      ENNReal.ofReal ((r / ρ) ^ (3 : ℕ)) := by
  have hc : 0 < Real.pi * 4 / 3 := by positivity
  rw [volume_vec3Ball_eq, volume_vec3Ball_eq,
    ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_pow hρ.le,
    ← ENNReal.ofReal_mul (pow_nonneg hr 3),
    ← ENNReal.ofReal_mul (pow_nonneg hρ.le 3),
    ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (mul_pos (pow_pos hρ 3) hc)]
  congr 1
  field_simp

/-- Integrating the spatial mean split preserves any smaller time window. -/
theorem velocityTimeWindowMeanSplit
    {x₀ : Vec3} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r) (hrρ : r ≤ ρ)
    {u : ParabolicPoint → Vec3} {J T : Set ℝ} (hJT : J ⊆ T)
    (hu : Integrable u
      ((volume.restrict (vec3Ball x₀ ρ)).prod (volume.restrict T)))
    (hu3 : Integrable (fun w ↦ vec3EuclideanNorm (u w) ^ (3 : ℕ))
      ((volume.restrict (vec3Ball x₀ ρ)).prod (volume.restrict T))) :
    (∫⁻ s in J, ∫⁻ x in vec3Ball x₀ r,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ)) ≤
      4 * (∫⁻ s in T, ∫⁻ x in vec3Ball x₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (meanFreeVec u x₀ ρ s x)) ^ (3 : ℝ)) +
      4 * ENNReal.ofReal ((r / ρ) ^ (3 : ℕ)) *
        ∫⁻ s in T, ∫⁻ x in vec3Ball x₀ ρ,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ) := by
  have hpoint : ∀ᵐ s ∂volume.restrict J,
      (∫⁻ x in vec3Ball x₀ r,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ)) ≤
      4 * (∫⁻ x in vec3Ball x₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (meanFreeVec u x₀ ρ s x)) ^ (3 : ℝ)) +
      4 * ENNReal.ofReal ((r / ρ) ^ (3 : ℕ)) *
        ∫⁻ x in vec3Ball x₀ ρ,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hJT hu.prod_left_ae,
      ae_restrict_of_ae_restrict_of_subset hJT hu3.prod_left_ae] with s hs hs3
    have h := velocitySliceMeanSplit hρ hrρ hs hs3
    have heq := meanFreeVec_eq_sub_spatialAverage hs
    simp_rw [heq]
    simpa only [ENNReal.rpow_ofNat, mul_assoc,
      velocityBallVolumeRatio hr hρ] using h
  have hmeas : AEMeasurable (fun w ↦ ENNReal.ofReal (vec3EuclideanNorm (u w)) ^
      (3 : ℝ)) ((volume.restrict (vec3Ball x₀ ρ)).prod (volume.restrict T)) := by
    simp_rw [ENNReal.rpow_ofNat, ← ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _)]
    exact hu3.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have htime := hmeas.lintegral_prod_left'
  have htimeJ := htime.mono_measure (Measure.restrict_mono hJT le_rfl)
  calc
    _ ≤ ∫⁻ s in J,
        (4 * (∫⁻ x in vec3Ball x₀ ρ,
          ENNReal.ofReal (vec3EuclideanNorm (meanFreeVec u x₀ ρ s x)) ^ (3 : ℝ)) +
        4 * ENNReal.ofReal ((r / ρ) ^ (3 : ℕ)) *
          ∫⁻ x in vec3Ball x₀ ρ,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ)) :=
      lintegral_mono_ae hpoint
    _ ≤ _ := by
      have hsplit := lintegral_add_right'
        (fun s ↦ 4 * (∫⁻ x in vec3Ball x₀ ρ,
          ENNReal.ofReal (vec3EuclideanNorm (meanFreeVec u x₀ ρ s x)) ^ (3 : ℝ)))
        (htimeJ.const_mul (4 * ENNReal.ofReal ((r / ρ) ^ (3 : ℕ))))
      rw [hsplit,
        lintegral_const_mul' _ _ (by norm_num),
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)]
      gcongr

/-- The genuine suitable velocity has cubic small-scale decay with a mixed
gradient source and the spatial mean's decaying volume contribution. -/
theorem suitableVelocityTimeWindowMixedMassDecay
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hrρ : r ≤ ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 (4 * ρ)) ⊆ spaceTimeSet Ω I)
    {J : Set ℝ} (hJ : J ⊆ Ioc (z.2 - ρ ^ 2) z.2) :
    (∫⁻ s in J, ∫⁻ x in vec3Ball z.1 r,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ)) ≤
      4 * criticalVectorCubicOscillationConstant *
        timeSliceEnergyEssSup z.1 z.2 (2 * ρ) (fun w ↦ vec3EuclideanNorm (u w)) ^
          (1 / 2 : ℝ) *
        (∫⁻ s in Ioc (z.2 - (2 * ρ) ^ 2) z.2,
          eLpNorm (fun x ↦ Du (x, s)) (12 / 7)
            (volume.restrict (vec3Ball z.1 (2 * ρ))) ^ (2 : ℝ)) +
      4 * ENNReal.ofReal ((r / ρ) ^ (3 : ℕ)) *
        ∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, ∫⁻ x in vec3Ball z.1 ρ,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ) := by
  let B := vec3Ball z.1 ρ
  let T := Ioc (z.2 - ρ ^ 2) z.2
  have hsubρ : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I :=
    (closure_mono (parabolicCylinder_mono hρ.le (by linarith only [hρ]))).trans hsub
  have hu : Integrable u ((volume.restrict B).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict]
    exact tsai_integrable_velocity_on_cylinder hsol hρ hsubρ
  have hu3 : Integrable (fun w ↦ vec3EuclideanNorm (u w) ^ (3 : ℕ))
      ((volume.restrict B).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict]
    exact tsai_integrable_velocity_cube_on_cylinder hsol hρ hsubρ
  have hmean := velocityTimeWindowMeanSplit hρ hr.le hrρ hJ hu hu3
  apply hmean.trans
  have hosc := suitableCubicOscillationMass hsol hρ hsub
  exact add_le_add (by simpa only [mul_assoc] using mul_le_mul' (le_refl 4) hosc) le_rfl

/-- The genuine harmonic-pressure decay integrates over every smaller time
window, including symmetric windows contained in a shifted backward cylinder. -/
theorem suitablePressureTimeWindowDecay
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    {J : Set ℝ} (hJ : J ⊆ Ioc (z.2 - ρ ^ 2) z.2) :
    (∫ s in J, r⁻¹ ^ 2 * ∫ x in vec3Ball z.1 r,
        |p (x, s)| ^ (3 / 2 : ℝ)) ≤
      lin34AbsoluteConstant * ((ρ / r) ^ 2 * pressureChat u z ρ +
        (r / ρ) * pressureD p z ρ) := by
  let T := Ioc (z.2 - ρ ^ 2) z.2
  let F := fun s ↦ r⁻¹ ^ 2 * ∫ x in vec3Ball z.1 r, |p (x, s)| ^ (3 / 2 : ℝ)
  let H := fun s ↦ lin34AbsoluteConstant *
    ((ρ / r) ^ 2 * lin34G u z ρ s + (r / ρ) * lin34H p z ρ s)
  have hrρ : r ≤ ρ := by linarith only [hhalf, hρ]
  have hp := lin34_integrableOn_pressure_pow_cylinder hsol hρ hsub
  have hprod : Integrable (fun w ↦ |p w| ^ (3 / 2 : ℝ))
      ((volume.restrict (vec3Ball z.1 ρ)).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict]
    exact hp
  have hsmallprod : Integrable (fun w ↦ |p w| ^ (3 / 2 : ℝ))
      ((volume.restrict (vec3Ball z.1 r)).prod (volume.restrict T)) := by
    apply hprod.mono_measure
    exact Measure.prod_mono
      (Measure.restrict_mono (vec3Ball_mono hrρ) le_rfl) le_rfl
  have hF : Integrable F (volume.restrict T) := hsmallprod.integral_prod_right.const_mul _
  have hH : Integrable H (volume.restrict T) :=
    (((lin34G_integrable hsol hρ hsub).const_mul _).add
      ((lin34H_integrable hsol hρ hsub).const_mul _)).const_mul _
  have hforce : ∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun w ↦ ∑ i : Fin 3, (0 : Vec3) i * spatialPartial ψ i w)
          (tsupport ψ) volume ∧
        (∫ w in spaceTimeSet Ω I, ∑ i : Fin 3, (0 : Vec3) i * spatialPartial ψ i w) = 0 :=
    by intro ψ hψ; simp
  have hpoint := ((CKN.pressure_lin34_of_sws q hsol hρ hr hhalf hsub).1 hforce).1
  have hC : 0 ≤ lin34AbsoluteConstant :=
    (lin34PointwiseConstant_nonneg lin34CZConstant_nonneg).trans (le_max_left _ _)
  have hHnonneg : ∀ s, 0 ≤ H s := by
    intro s
    dsimp [H, lin34G, lin34H, lin34VelocitySlice, lin34PressureSlice]
    apply mul_nonneg hC
    apply add_nonneg
    · exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
        (integral_nonneg (fun _ ↦ pow_nonneg (vec3EuclideanNorm_nonneg _) 3)))
    · exact mul_nonneg (div_nonneg hr.le hρ.le) (mul_nonneg (sq_nonneg _)
        (integral_nonneg (fun _ ↦ by positivity)))
  calc
    _ ≤ ∫ s in J, H s := integral_mono_ae (hF.mono_measure
        (Measure.restrict_mono hJ le_rfl))
      (hH.mono_measure (Measure.restrict_mono hJ le_rfl))
      (ae_restrict_of_ae_restrict_of_subset hJ hpoint)
    _ ≤ ∫ s in T, H s := setIntegral_mono_set hH
      (Eventually.of_forall hHnonneg) (Eventually.of_forall (fun s hs ↦ hJ hs))
    _ = _ := by
      dsimp [H]
      rw [integral_const_mul, integral_add
        ((lin34G_integrable hsol hρ hsub).const_mul _)
        ((lin34H_integrable hsol hρ hsub).const_mul _),
        integral_const_mul, integral_const_mul,
        ← lin34_pressureChat_eq_integral hsol hρ hsub,
        ← lin34_pressureD_eq_integral hsol hρ hsub]

end FluidSingularSets
