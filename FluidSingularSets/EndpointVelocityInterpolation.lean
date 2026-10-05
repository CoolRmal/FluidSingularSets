-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StokesPressureTimeIntegrability
public import FluidSingularSets.WeightedVelocityPoincare
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Genuine endpoint velocity interpolation

Actual spatial L² and L⁶ seminorms interpolate to L³. Time Hölder gives
exact powers 3/4 of the slice square-energy bound and mixed L²/L⁶ cost,
with power 1/4 of the time-window measure. Joint measurability and finite
energy/cost imply actual spacetime cubic integrability.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Genuine `L²`/`L⁶` interpolation of any strongly measurable spatial velocity. -/
theorem eLpNorm_interpolate_three {μ : Measure Vec3} {E : Type*} [NormedAddCommGroup E]
    {u : Vec3 → E}
    (hu : AEStronglyMeasurable u μ) :
    eLpNorm u 3 μ ≤ eLpNorm u 2 μ ^ (1 / 2 : ℝ) * eLpNorm u 6 μ ^ (1 / 2 : ℝ) := by
  let a : Vec3 → ℝ := fun x ↦ ‖u x‖ ^ (1 / 2 : ℝ)
  let b : Vec3 → ℝ := fun x ↦ ‖u x‖ ^ (1 / 2 : ℝ)
  have ha : AEStronglyMeasurable a μ := by
    exact (Real.continuous_rpow_const (q := (1 / 2 : ℝ)) (by norm_num)).comp_aestronglyMeasurable
      hu.norm
  have hb : AEStronglyMeasurable b μ := by
    exact (Real.continuous_rpow_const (q := (1 / 2 : ℝ)) (by norm_num)).comp_aestronglyMeasurable
      hu.norm
  let : ENNReal.HolderTriple 4 12 3 := by
    have h : Real.HolderTriple 4 12 3 := by rw [Real.holderTriple_iff]; norm_num
    simpa only [ENNReal.ofReal_ofNat] using h.ennrealOfReal
  have hholder : eLpNorm (fun x ↦ a x * b x) 3 μ ≤ eLpNorm a 4 μ * eLpNorm b 12 μ := by
    simpa only [ENNReal.coe_one, one_mul] using
      eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 4) (q := 12) (r := 3)
        (fun x y : ℝ ↦ x * y) 1 continuous_mul ha hb
        (ae_of_all _ (fun x ↦ by simp only [norm_mul, NNReal.coe_one, one_mul, le_refl]))
  have hprod : (fun x ↦ a x * b x) = fun x ↦ ‖u x‖ := by
    funext x
    change ‖u x‖ ^ (1 / 2 : ℝ) * ‖u x‖ ^ (1 / 2 : ℝ) = ‖u x‖
    by_cases hz : ‖u x‖ = 0
    · simp only [hz, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), mul_zero]
    · rw [← Real.rpow_add (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))]
      norm_num
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  have h42 : (4 : ℝ≥0∞) * 2⁻¹ = 2 := by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
  have h126 : (12 : ℝ≥0∞) * 2⁻¹ = 6 := by
    rw [show (12 : ℝ≥0∞) = 6 * 2 by norm_num, mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
  have hpow2 : eLpNorm a 4 μ = eLpNorm u 2 μ ^ (1 / 2 : ℝ) := by
    have h := eLpNorm_norm_rpow u hu (by norm_num : (0 : ℝ) < 1 / 2) (p := 4)
    rw [hhalf, h42] at h
    exact h
  have hpow6 : eLpNorm b 12 μ = eLpNorm u 6 μ ^ (1 / 2 : ℝ) := by
    have h := eLpNorm_norm_rpow u hu (by norm_num : (0 : ℝ) < 1 / 2) (p := 12)
    rw [hhalf, h126] at h
    exact h
  rw [hprod, hpow2, hpow6, eLpNorm_norm u hu] at hholder
  exact hholder

/-- The spatial endpoint estimate has the exact cubic exponents. -/
theorem eLpNorm_interpolate_three_cubic {E : Type*} [NormedAddCommGroup E]
    {μ : Measure Vec3} {u : Vec3 → E} (hu : AEStronglyMeasurable u μ) :
    eLpNorm u 3 μ ^ (3 : ℝ) ≤
      eLpNorm u 2 μ ^ (3 / 2 : ℝ) * eLpNorm u 6 μ ^ (3 / 2 : ℝ) := by
  have h := ENNReal.rpow_le_rpow (eLpNorm_interpolate_three hu)
    (by norm_num : (0 : ℝ) ≤ 3)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at h
  norm_num only [show (1 / 2 : ℝ) * 3 = 3 / 2 by norm_num] at h
  exact h

/-- Actual joint measurability gives measurability of the literal endpoint mixed density. -/
theorem aemeasurable_spatial_six_square {E : Type*} [NormedAddCommGroup E]
    {B : Set Vec3} {J : Set ℝ} {F : ParabolicPoint → E}
    (hF : AEStronglyMeasurable F (volume.restrict (B ×ˢ J))) :
    AEMeasurable (fun t ↦ eLpNorm (fun x ↦ F (x, t)) 6 (volume.restrict B) ^ (2 : ℝ))
      (volume.restrict J) := by
  have hp : AEStronglyMeasurable F ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hF
  have hm := ((hp.enorm.pow_const (6 : ℝ)).lintegral_prod_left').pow_const (1 / 3 : ℝ)
  apply hm.congr
  filter_upwards [hp.prodMk_right] with t ht
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) ht]
  norm_num only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_mul]
  norm_num

/-- Genuine time Hölder for the endpoint mixed density, with the exact time exponent. -/
theorem lintegral_spatial_six_threeHalves_le {E : Type*} [NormedAddCommGroup E]
    {B : Set Vec3} {J : Set ℝ} {F : ParabolicPoint → E}
    (hF : AEStronglyMeasurable F (volume.restrict (B ×ˢ J))) :
    (∫⁻ t in J, eLpNorm (fun x ↦ F (x, t)) 6 (volume.restrict B) ^ (3 / 2 : ℝ)) ≤
      (∫⁻ t in J, eLpNorm (fun x ↦ F (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (3 / 4 : ℝ) * volume J ^ (1 / 4 : ℝ) := by
  have h := ENNReal.lintegral_mul_norm_pow_le
    (aemeasurable_spatial_six_square hF) (aemeasurable_const (b := (1 : ℝ≥0∞)))
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (3 / 4 : ℝ) + 1 / 4 = 1)
  simpa only [ENNReal.one_rpow, mul_one, ← ENNReal.rpow_mul,
    show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num, lintegral_const,
    Measure.restrict_apply_univ, one_mul] using h

/-- Fubini identifies the literal cubic moment with actual spatial cubic seminorms. -/
theorem lintegral_spatial_three_cubic_eq {E : Type*} [NormedAddCommGroup E]
    {B : Set Vec3} {J : Set ℝ} {F : ParabolicPoint → E}
    (hF : AEStronglyMeasurable F (volume.restrict (B ×ˢ J))) :
    (∫⁻ t in J, eLpNorm (fun x ↦ F (x, t)) 3 (volume.restrict B) ^ (3 : ℝ)) =
      ∫⁻ z : ParabolicPoint in B ×ˢ J, ‖F z‖ₑ ^ (3 : ℝ) := by
  have hp : AEStronglyMeasurable F ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hF
  rw [show (volume : Measure ParabolicPoint).restrict (B ×ˢ J) =
    (volume.restrict B).prod (volume.restrict J) by
    rw [Measure.prod_restrict, volume_parabolicPoint_eq_prod]]
  change (∫⁻ t in J, eLpNorm (fun x ↦ F (x, t)) 3 (volume.restrict B) ^ (3 : ℝ)) =
    ∫⁻ z : Vec3 × ℝ, ‖F z‖ₑ ^ (3 : ℝ) ∂(volume.restrict B).prod (volume.restrict J)
  rw [lintegral_prod_symm _ (hp.enorm.pow_const (3 : ℝ))]
  apply lintegral_congr_ae
  filter_upwards [hp.prodMk_right] with t ht
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) ht]
  norm_num only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_mul]
  norm_num

/-- Actual finite slice square energy and mixed endpoint cost control the full cubic moment. -/
theorem endpoint_velocity_cubic_lintegral_le {E : Type*} [NormedAddCommGroup E]
    {B : Set Vec3} {J : Set ℝ} {F : ParabolicPoint → E} {M : ℝ≥0∞}
    (hF : AEStronglyMeasurable F (volume.restrict (B ×ˢ J))) (hM : M < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖F (x, t)‖ₑ ^ (2 : ℝ)) ≤ M) :
    (∫⁻ z : ParabolicPoint in B ×ˢ J, ‖F z‖ₑ ^ (3 : ℝ)) ≤
      M ^ (3 / 4 : ℝ) * volume J ^ (1 / 4 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ F (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
          (3 / 4 : ℝ) := by
  have hp : AEStronglyMeasurable F ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hF
  have hpoint : ∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x ↦ F (x, t)) 3 (volume.restrict B) ^ (3 : ℝ) ≤
        M ^ (3 / 4 : ℝ) *
          eLpNorm (fun x ↦ F (x, t)) 6 (volume.restrict B) ^ (3 / 2 : ℝ) := by
    filter_upwards [hp.prodMk_right, henergy] with t ht hEt
    have heq := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) ht
    norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at heq
    have h2 : eLpNorm (fun x ↦ F (x, t)) 2 (volume.restrict B) ^ (3 / 2 : ℝ) ≤
        M ^ (3 / 4 : ℝ) := by
      have hpow := ENNReal.rpow_le_rpow
        (heq.trans_le (by simpa only [ENNReal.rpow_ofNat] using hEt))
        (by norm_num : (0 : ℝ) ≤ 3 / 4)
      rw [← ENNReal.rpow_ofNat, ← ENNReal.rpow_mul] at hpow
      norm_num only [show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num] at hpow
      exact hpow
    exact (eLpNorm_interpolate_three_cubic ht).trans (mul_le_mul' h2 le_rfl)
  calc
    _ = ∫⁻ t in J, eLpNorm (fun x ↦ F (x, t)) 3 (volume.restrict B) ^ (3 : ℝ) :=
      (lintegral_spatial_three_cubic_eq hF).symm
    _ ≤ ∫⁻ t in J, M ^ (3 / 4 : ℝ) *
        eLpNorm (fun x ↦ F (x, t)) 6 (volume.restrict B) ^ (3 / 2 : ℝ) :=
      lintegral_mono_ae hpoint
    _ = M ^ (3 / 4 : ℝ) *
        ∫⁻ t in J, eLpNorm (fun x ↦ F (x, t)) 6 (volume.restrict B) ^ (3 / 2 : ℝ) :=
      lintegral_const_mul' _ _ (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hM.ne).ne
    _ ≤ M ^ (3 / 4 : ℝ) *
        ((∫⁻ t in J, eLpNorm (fun x ↦ F (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
          (3 / 4 : ℝ) * volume J ^ (1 / 4 : ℝ)) :=
      mul_le_mul_right (lintegral_spatial_six_threeHalves_le hF) _
    _ = _ := by ring

/-- Finite actual energy and mixed endpoint cost give genuine joint cubic membership. -/
theorem endpoint_velocity_memLp_three {E : Type*} [NormedAddCommGroup E]
    {B : Set Vec3} {J : Set ℝ} {F : ParabolicPoint → E} {M : ℝ≥0∞}
    (hF : AEStronglyMeasurable F (volume.restrict (B ×ˢ J))) (hM : M < ∞)
    (hJ : volume J < ∞)
    (hX : (∫⁻ t in J, eLpNorm (fun x ↦ F (x, t)) 6
      (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖F (x, t)‖ₑ ^ (2 : ℝ)) ≤ M) :
    MemLp F 3 (volume.restrict (B ×ˢ J)) := by
  have hmass := (endpoint_velocity_cubic_lintegral_le hF hM henergy).trans_lt
    (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hM.ne)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hJ.ne))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hX.ne))
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hF]
  norm_num only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hmass.ne

/-- The actual real cubic density is integrable, derived from the endpoint data. -/
theorem endpoint_velocity_cubic_integrable {E : Type*} [NormedAddCommGroup E]
    {B : Set Vec3} {J : Set ℝ} {F : ParabolicPoint → E} {M : ℝ≥0∞}
    (hF : AEStronglyMeasurable F (volume.restrict (B ×ˢ J))) (hM : M < ∞)
    (hJ : volume J < ∞)
    (hX : (∫⁻ t in J, eLpNorm (fun x ↦ F (x, t)) 6
      (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖F (x, t)‖ₑ ^ (2 : ℝ)) ≤ M) :
    Integrable (fun z ↦ ‖F z‖ ^ (3 : ℕ)) (volume.restrict (B ×ˢ J)) :=
  (endpoint_velocity_memLp_three hF hM hJ hX henergy).integrable_norm_pow (by norm_num)

/-- The literal real spacetime cubic integral has the exact endpoint bound, with constant one. -/
theorem endpoint_velocity_cubic_integral_le {E : Type*} [NormedAddCommGroup E]
    {B : Set Vec3} {J : Set ℝ} {F : ParabolicPoint → E} {M : ℝ≥0∞}
    (hF : AEStronglyMeasurable F (volume.restrict (B ×ˢ J))) (hM : M < ∞)
    (hJ : volume J < ∞)
    (hX : (∫⁻ t in J, eLpNorm (fun x ↦ F (x, t)) 6
      (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖F (x, t)‖ₑ ^ (2 : ℝ)) ≤ M) :
    (∫ z : ParabolicPoint in B ×ˢ J, ‖F z‖ ^ (3 : ℕ)) ≤
      M.toReal ^ (3 / 4 : ℝ) * (volume J).toReal ^ (1 / 4 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ F (x, t)) 6
          (volume.restrict B) ^ (2 : ℝ)).toReal ^ (3 / 4 : ℝ) := by
  have hbound := endpoint_velocity_cubic_lintegral_le hF hM henergy
  have hR : M ^ (3 / 4 : ℝ) * volume J ^ (1 / 4 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ F (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (3 / 4 : ℝ) ≠ ∞ := by finiteness [hM.ne, hJ.ne, hX.ne]
  have hreal := ENNReal.toReal_mono hR hbound
  change (∫ z : ParabolicPoint, ‖F z‖ ^ (3 : ℕ) ∂volume.restrict (B ×ˢ J)) ≤ _
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun z ↦ pow_nonneg (norm_nonneg (F z)) 3)) (hF.norm.pow 3)]
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simpa only [ENNReal.rpow_ofNat, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow] using hreal

/-- The true Euclidean square energy is controlled by the native coordinate norm energy. -/
theorem lintegral_euclidean_velocity_sq_le_nine {μ : Measure Vec3} {u : Vec3 → Vec3}
    (hu : AEStronglyMeasurable u μ) :
    (∫⁻ x, ‖vec3EuclideanNorm (u x)‖ₑ ^ (2 : ℝ) ∂μ) ≤
      9 * ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂μ := by
  have hv := CKN.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hu
  have hE := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hv
  have hN := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hu
  norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat] at hE hN
  have h := ENNReal.rpow_le_rpow (eLpNorm_vec3EuclideanNorm_le_three hu 2)
    (by norm_num : (0 : ℝ) ≤ 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hE, hN,
    show (3 : ℝ≥0∞) ^ (2 : ℝ) = 9 by norm_num] at h
  exact h

private theorem endpoint_unitBall_subset_double :
    euclideanBall (0 : Vec3) 1 ⊆ euclideanBall 0 2 := by
  intro x hx
  change euclideanSqDist x 0 < (2 : ℝ) ^ 2
  change euclideanSqDist x 0 < (1 : ℝ) ^ 2 at hx
  norm_num at hx ⊢
  exact hx.trans (by norm_num)

private theorem endpoint_sobolevConstant_ne_top : localSobolevConstant ≠ ∞ := by
  unfold localSobolevConstant
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top

section Suitable

variable {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
  {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

/-- Actual suitable S1 data give a finite genuine Euclidean slice energy supremum. -/
theorem suitable_unitBall_euclidean_sliceEnergy_essSup_lt_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    essSup (fun t ↦ ∫⁻ x in euclideanBall 0 2,
      ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ (2 : ℝ)) (volume.restrict J) < ∞ := by
  let M := essSup (fun t ↦ ∫⁻ x in euclideanBall 0 2, ‖u (x, t)‖ₑ ^ (2 : ℝ))
    (volume.restrict J)
  have hM : M < ∞ := hsol.toData.essSup_sliceEnergy_lt_top hbox
  have hpoint : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in euclideanBall 0 2, ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ (2 : ℝ)) ≤ 9 * M := by
    filter_upwards [slice_memLp_ae_of_sws hsol hbox,
      ENNReal.ae_le_essSup (μ := volume.restrict J)
        (fun t ↦ ∫⁻ x in euclideanBall 0 2, ‖u (x, t)‖ₑ ^ (2 : ℝ))] with t ht hMt
    exact (lintegral_euclidean_velocity_sq_le_nine ht.1.aestronglyMeasurable).trans
      (mul_le_mul_right hMt 9)
  exact (essSup_le_of_ae_le (9 * M) hpoint).trans_lt
    (ENNReal.mul_lt_top (by norm_num) hM)

/-- Genuine suitable energy and weak Sobolev slices bound the actual endpoint mixed cost. -/
theorem suitable_unitBall_endpoint_mixed_lintegral_le
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    (∫⁻ t in J, eLpNorm (fun x ↦ vec3EuclideanNorm (u (x, t))) 6
      (volume.restrict (euclideanBall 0 1)) ^ (2 : ℝ)) ≤
      2 * (9 * localSobolevConstant) ^ 2 *
        ((∫⁻ z in euclideanBall 0 2 ×ˢ J, ‖Du z‖ₑ ^ (2 : ℝ)) +
          1024 * (essSup (fun t ↦ ∫⁻ x in euclideanBall 0 2,
            ‖u (x, t)‖ₑ ^ (2 : ℝ)) (volume.restrict J)) * volume J) := by
  let M := essSup (fun t ↦ ∫⁻ x in euclideanBall 0 2, ‖u (x, t)‖ₑ ^ (2 : ℝ))
    (volume.restrict J)
  have hM : M < ∞ := hsol.toData.essSup_sliceEnergy_lt_top hbox
  have hw : ∀ᵐ t ∂volume.restrict J, ∀ j : Fin 3,
      HasWeakGradientOn (euclideanBall 0 2)
        (fun x ↦ u (x, t) j) (fun x ↦ Du (x, t) j) :=
    ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)
  have hpoint : ∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x ↦ vec3EuclideanNorm (u (x, t))) 6
          (volume.restrict (euclideanBall 0 1)) ^ (2 : ℝ) ≤
        2 * (9 * localSobolevConstant) ^ 2 *
          (eLpNorm (fun x ↦ Du (x, t)) 2
            (volume.restrict (euclideanBall 0 2)) ^ 2 + 1024 * M) := by
    filter_upwards [slice_memLp_ae_of_sws hsol hbox, hw,
      ENNReal.ae_le_essSup (μ := volume.restrict J)
        (fun t ↦ ∫⁻ x in euclideanBall 0 2, ‖u (x, t)‖ₑ ^ (2 : ℝ))] with t ht hwt hMt
    have hui := ht.1.mono_measure
      (Measure.restrict_mono endpoint_unitBall_subset_double le_rfl)
    have h6 := (eLpNorm_vec3EuclideanNorm_le_three hui.aestronglyMeasurable 6).trans
      (mul_le_mul_right (unitBallH1Vector_sobolev ht.1 ht.2 hwt) 3)
    have h6' : eLpNorm (fun x ↦ vec3EuclideanNorm (u (x, t))) 6
        (volume.restrict (euclideanBall 0 1)) ≤
          (9 * localSobolevConstant) *
            (eLpNorm (fun x ↦ Du (x, t)) 2 (volume.restrict (euclideanBall 0 2)) +
              32 * eLpNorm (fun x ↦ u (x, t)) 2 (volume.restrict (euclideanBall 0 2))) := by
      convert h6 using 1; ring
    have heq := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0))
      (by norm_num) ht.1.aestronglyMeasurable
    norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at heq
    have h2 : eLpNorm (fun x ↦ u (x, t)) 2 (volume.restrict (euclideanBall 0 2)) ^ 2 ≤ M :=
      heq.trans_le (by simpa only [M, ENNReal.rpow_ofNat] using hMt)
    have hadd := ENNReal.rpow_add_le_mul_rpow_add_rpow
      (eLpNorm (fun x ↦ Du (x, t)) 2 (volume.restrict (euclideanBall 0 2)))
      (32 * eLpNorm (fun x ↦ u (x, t)) 2 (volume.restrict (euclideanBall 0 2)))
      (by norm_num : (1 : ℝ) ≤ 2)
    norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one,
      ENNReal.rpow_ofNat, mul_pow, show (32 : ℝ≥0∞) ^ 2 = 1024 by norm_num] at hadd
    have hadd' := hadd.trans
      (mul_le_mul_right (add_le_add le_rfl (mul_le_mul_right h2 1024)) 2)
    have hsq := pow_le_pow_left' h6' 2
    rw [mul_pow] at hsq
    norm_num only [ENNReal.rpow_ofNat]
    exact (hsq.trans (mul_le_mul_right hadd' _)).trans_eq (by ring)
  calc
    _ ≤ ∫⁻ t in J, 2 * (9 * localSobolevConstant) ^ 2 *
        (eLpNorm (fun x ↦ Du (x, t)) 2
          (volume.restrict (euclideanBall 0 2)) ^ 2 + 1024 * M) :=
      lintegral_mono_ae hpoint
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by
          exact ENNReal.mul_ne_top (by norm_num)
            (ENNReal.pow_ne_top (ENNReal.mul_ne_top (by norm_num)
              endpoint_sobolevConstant_ne_top))),
        lintegral_add_right _ measurable_const, lintegral_const,
        lintegral_spatial_two_sq_eq (hsol.toData.aestronglyMeasurable_gradient hbox)]
      simp only [M, Measure.restrict_apply_univ, mul_assoc]

/-- The endpoint mixed cost is finite for actual suitable data, with no mixed-norm premise. -/
theorem suitable_unitBall_endpoint_mixed_lintegral_lt_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    (∫⁻ t in J, eLpNorm (fun x ↦ vec3EuclideanNorm (u (x, t))) 6
      (volume.restrict (euclideanBall 0 1)) ^ (2 : ℝ)) < ∞ := by
  apply (suitable_unitBall_endpoint_mixed_lintegral_le hsol hbox).trans_lt
  have hM := hsol.toData.essSup_sliceEnergy_lt_top hbox
  have hD : (∫⁻ z in euclideanBall 0 2 ×ˢ J, ‖Du z‖ₑ ^ (2 : ℝ)) < ∞ :=
    (lintegral_mono (fun _ ↦ le_add_left le_rfl)).trans_lt
      (hsol.toData.energy_lintegral_lt_top hbox)
  have hJ : volume J < ∞ :=
    (measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top
  exact ENNReal.mul_lt_top
    (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top (ENNReal.mul_ne_top (by norm_num)
        endpoint_sobolevConstant_ne_top))))
    (ENNReal.add_lt_top.mpr ⟨hD,
      ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hM) hJ⟩)

/-- The exact cubic bound for actual suitable velocity, with its true Euclidean energy and cost. -/
theorem suitable_unitBall_endpoint_cubic_integral_le
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (euclideanBall 0 2) J) :
    (∫ z : ParabolicPoint in euclideanBall 0 1 ×ˢ J,
      vec3EuclideanNorm (u z) ^ (3 : ℕ)) ≤
      (essSup (fun t ↦ ∫⁻ x in euclideanBall 0 2,
        ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ (2 : ℝ))
          (volume.restrict J)).toReal ^ (3 / 4 : ℝ) *
        (volume J).toReal ^ (1 / 4 : ℝ) *
          (∫⁻ t in J, eLpNorm (fun x ↦ vec3EuclideanNorm (u (x, t))) 6
            (volume.restrict (euclideanBall 0 1)) ^ (2 : ℝ)).toReal ^ (3 / 4 : ℝ) := by
  have hu := (hsol.toData.aestronglyMeasurable_velocity hbox).mono_measure
    (Measure.restrict_mono (Set.prod_mono endpoint_unitBall_subset_double Subset.rfl) le_rfl)
  have hE := CKN.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hu
  have hM := suitable_unitBall_euclidean_sliceEnergy_essSup_lt_top hsol hbox
  have hJ : volume J < ∞ :=
    (measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top
  have henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in euclideanBall 0 1, ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ (2 : ℝ)) ≤
        essSup (fun t ↦ ∫⁻ x in euclideanBall 0 2,
          ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ (2 : ℝ)) (volume.restrict J) := by
    filter_upwards [ENNReal.ae_le_essSup (μ := volume.restrict J)
      (fun t ↦ ∫⁻ x in euclideanBall 0 2,
        ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ (2 : ℝ))] with t ht
    exact (lintegral_mono_set endpoint_unitBall_subset_double).trans ht
  have h := endpoint_velocity_cubic_integral_le hE hM hJ
    (suitable_unitBall_endpoint_mixed_lintegral_lt_top hsol hbox) henergy
  simpa only [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)] using h

end Suitable

end FluidSingularSets
