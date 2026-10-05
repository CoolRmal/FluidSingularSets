-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.EndpointVelocityInterpolation
public import FluidSingularSets.ProjectedEnergyAlgebra

/-!
# Genuine endpoint convection estimates for projected cutoff energy

Spatial Hölder pairs the actual velocity L⁶ norm with the corrected velocity
L^(12/5) norm. True L²/L⁶ interpolation and time Hölder give the endpoint
convection estimate directly from finite slice energy and mixed norms.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- Actual spatial L²/L⁶ interpolation at the convection exponent, with constant one. -/
theorem eLpNorm_interpolate_twelveFifths {μ : Measure Vec3} {E : Type*}
    [NormedAddCommGroup E] {v : Vec3 → E} (hv : AEStronglyMeasurable v μ) :
    eLpNorm v (ENNReal.ofReal (12 / 5 : ℝ)) μ ≤
      eLpNorm v 2 μ ^ (3 / 4 : ℝ) * eLpNorm v 6 μ ^ (1 / 4 : ℝ) := by
  let a : Vec3 → ℝ := fun x ↦ ‖v x‖ ^ (3 / 4 : ℝ)
  let b : Vec3 → ℝ := fun x ↦ ‖v x‖ ^ (1 / 4 : ℝ)
  have ha : AEStronglyMeasurable a μ :=
    (Real.continuous_rpow_const (q := (3 / 4 : ℝ)) (by norm_num)).comp_aestronglyMeasurable
      hv.norm
  have hb : AEStronglyMeasurable b μ :=
    (Real.continuous_rpow_const (q := (1 / 4 : ℝ)) (by norm_num)).comp_aestronglyMeasurable
      hv.norm
  let : ENNReal.HolderTriple (ENNReal.ofReal (8 / 3 : ℝ)) 24
      (ENNReal.ofReal (12 / 5 : ℝ)) := by
    have h : Real.HolderTriple (8 / 3 : ℝ) 24 (12 / 5 : ℝ) := by
      rw [Real.holderTriple_iff]
      norm_num
    simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h.ennrealOfReal
  have hh : eLpNorm (fun x ↦ a x * b x) (ENNReal.ofReal (12 / 5 : ℝ)) μ ≤
      eLpNorm a (ENNReal.ofReal (8 / 3 : ℝ)) μ * eLpNorm b 24 μ := by
    simpa only [ENNReal.coe_one, one_mul] using
      eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
        (p := ENNReal.ofReal (8 / 3 : ℝ)) (q := 24) (r := ENNReal.ofReal (12 / 5 : ℝ))
        (fun x y : ℝ ↦ x * y) 1 continuous_mul ha hb
        (ae_of_all _ (fun x ↦ by simp only [norm_mul, NNReal.coe_one, one_mul, le_refl]))
  have heq : (fun x ↦ a x * b x) = fun x ↦ ‖v x‖ := by
    funext x
    change ‖v x‖ ^ (3 / 4 : ℝ) * ‖v x‖ ^ (1 / 4 : ℝ) = ‖v x‖
    by_cases hz : ‖v x‖ = 0
    · simp only [hz, Real.zero_rpow (by norm_num : (3 / 4 : ℝ) ≠ 0),
        Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0), mul_zero]
    · rw [← Real.rpow_add (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))]
      norm_num
  have hp2 : ENNReal.ofReal (8 / 3 : ℝ) * ENNReal.ofReal (3 / 4 : ℝ) = 2 := by
    rw [← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hp6 : (24 : ℝ≥0∞) * ENNReal.ofReal (1 / 4 : ℝ) = 6 := by
    rw [← ENNReal.ofReal_ofNat 24, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hpa : eLpNorm a (ENNReal.ofReal (8 / 3 : ℝ)) μ =
      eLpNorm v 2 μ ^ (3 / 4 : ℝ) := by
    have h := eLpNorm_norm_rpow v hv (by norm_num : (0 : ℝ) < 3 / 4)
      (p := ENNReal.ofReal (8 / 3 : ℝ))
    rw [hp2] at h
    exact h
  have hpb : eLpNorm b 24 μ = eLpNorm v 6 μ ^ (1 / 4 : ℝ) := by
    have h := eLpNorm_norm_rpow v hv (by norm_num : (0 : ℝ) < 1 / 4) (p := 24)
    rw [hp6] at h
    exact h
  rw [heq, hpa, hpb, eLpNorm_norm v hv] at hh
  exact hh

/-- The exact squared interpolation estimate required by the true convection density. -/
theorem eLpNorm_interpolate_twelveFifths_squared {μ : Measure Vec3} {E : Type*}
    [NormedAddCommGroup E] {v : Vec3 → E} (hv : AEStronglyMeasurable v μ) :
    eLpNorm v (ENNReal.ofReal (12 / 5 : ℝ)) μ ^ (2 : ℝ) ≤
      eLpNorm v 2 μ ^ (3 / 2 : ℝ) * eLpNorm v 6 μ ^ (1 / 2 : ℝ) := by
  have h := ENNReal.rpow_le_rpow (eLpNorm_interpolate_twelveFifths hv)
    (by norm_num : (0 : ℝ) ≤ 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at h
  norm_num only [show (3 / 4 : ℝ) * 2 = 3 / 2 by norm_num,
    show (1 / 4 : ℝ) * 2 = 1 / 2 by norm_num] at h
  exact h

/-- Spatial Hölder bounds the literal mixed convection moment by actual endpoint norms. -/
theorem lintegral_spatial_convection_le {μ : Measure Vec3} {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {u : Vec3 → E} {v : Vec3 → F}
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ) :
    (∫⁻ x, ‖u x‖ₑ * ‖v x‖ₑ ^ (2 : ℝ) ∂μ) ≤
      eLpNorm u 6 μ * eLpNorm v (ENNReal.ofReal (12 / 5 : ℝ)) μ ^ (2 : ℝ) := by
  let b : Vec3 → ℝ := fun x ↦ ‖v x‖ ^ (2 : ℝ)
  have hb : AEStronglyMeasurable b μ :=
    (Real.continuous_rpow_const (q := (2 : ℝ)) (by norm_num)).comp_aestronglyMeasurable hv.norm
  let : ENNReal.HolderTriple 6 (ENNReal.ofReal (6 / 5 : ℝ)) 1 := by
    have h : Real.HolderTriple 6 (6 / 5 : ℝ) 1 := by rw [Real.holderTriple_iff]; norm_num
    simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h.ennrealOfReal
  have hh : eLpNorm (fun x ↦ ‖u x‖ * b x) 1 μ ≤
      eLpNorm (fun x ↦ ‖u x‖) 6 μ * eLpNorm b (ENNReal.ofReal (6 / 5 : ℝ)) μ := by
    simpa only [ENNReal.coe_one, one_mul] using
      eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
        (p := 6) (q := ENNReal.ofReal (6 / 5 : ℝ)) (r := 1)
        (fun x y : ℝ ↦ x * y) 1 continuous_mul hu.norm hb
        (ae_of_all _ (fun x ↦ by simp only [norm_mul, NNReal.coe_one, one_mul, le_refl]))
  have hp : ENNReal.ofReal (6 / 5 : ℝ) * ENNReal.ofReal (2 : ℝ) =
      ENNReal.ofReal (12 / 5 : ℝ) := by
    rw [← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have he := eLpNorm_norm_rpow v hv (by norm_num : (0 : ℝ) < 2)
    (p := ENNReal.ofReal (6 / 5 : ℝ))
  rw [hp] at he
  rw [he, eLpNorm_norm u hu] at hh
  rw [eLpNorm_one_eq_lintegral_enorm (f := fun x ↦ ‖u x‖ * b x) (hu.norm.mul hb)] at hh
  simpa only [b, enorm_mul, Real.rpow_two, enorm_pow, enorm_norm,
    ENNReal.rpow_ofNat] using hh

/-- Actual time Hölder has the exact three endpoint factors needed by convection. -/
theorem lintegral_endpoint_mixed_norm_product_le {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {B : Set Vec3} {J : Set ℝ} {U : ParabolicPoint → E} {V : ParabolicPoint → F}
    (hU : AEStronglyMeasurable U (volume.restrict (B ×ˢ J)))
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J))) :
    (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) *
      eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (1 / 2 : ℝ)) ≤
      (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 4 : ℝ) * volume J ^ (1 / 4 : ℝ) := by
  have hUm := aemeasurable_spatial_six_square hU
  have hVm := aemeasurable_spatial_six_square hV
  have hVn : AEMeasurable (fun t ↦ eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B))
      (volume.restrict J) := by
    have h := hVm.pow_const (1 / 2 : ℝ)
    simpa only [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
      ENNReal.rpow_one] using h
  have hfirst := ENNReal.lintegral_mul_norm_pow_le hUm hVn
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hsecond := ENNReal.lintegral_mul_norm_pow_le hVm (aemeasurable_const (b := (1 : ℝ≥0∞)))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    ENNReal.rpow_one] at hfirst
  simp only [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    ENNReal.rpow_one, ENNReal.one_rpow, mul_one, lintegral_const,
    Measure.restrict_apply_univ, one_mul] at hsecond
  have hp := ENNReal.rpow_le_rpow hsecond (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at hp
  norm_num only [show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num] at hp
  exact hfirst.trans (by simpa only [mul_assoc] using mul_le_mul' le_rfl hp)

/-- Finite true slice energy and actual mixed endpoint costs control the convection moment. -/
theorem endpoint_convection_lintegral_le {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {B : Set Vec3} {J : Set ℝ} {U : ParabolicPoint → E} {V : ParabolicPoint → F}
    {M : ℝ≥0∞} (hU : AEStronglyMeasurable U (volume.restrict (B ×ˢ J)))
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J))) (hM : M < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖V (x, t)‖ₑ ^ (2 : ℝ)) ≤ M) :
    (∫⁻ z : ParabolicPoint in B ×ˢ J, ‖U z‖ₑ * ‖V z‖ₑ ^ (2 : ℝ)) ≤
      M ^ (3 / 4 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 4 : ℝ) * volume J ^ (1 / 4 : ℝ) := by
  have hUp : AEStronglyMeasurable U ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hU
  have hVp : AEStronglyMeasurable V ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hV
  have hpoint : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖U (x, t)‖ₑ * ‖V (x, t)‖ₑ ^ (2 : ℝ)) ≤
        M ^ (3 / 4 : ℝ) * (eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) *
          eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (1 / 2 : ℝ)) := by
    filter_upwards [hUp.prodMk_right, hVp.prodMk_right, henergy] with t hu hv ht
    have heq := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hv
    norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at heq
    have h2 : eLpNorm (fun x ↦ V (x, t)) 2 (volume.restrict B) ^ (3 / 2 : ℝ) ≤
        M ^ (3 / 4 : ℝ) := by
      have h := ENNReal.rpow_le_rpow
        (heq.trans_le (by simpa only [ENNReal.rpow_ofNat] using ht))
        (by norm_num : (0 : ℝ) ≤ 3 / 4)
      rw [← ENNReal.rpow_ofNat, ← ENNReal.rpow_mul] at h
      norm_num only [show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num] at h
      exact h
    apply (lintegral_spatial_convection_le hu hv).trans
    have hs := mul_le_mul' (le_refl (eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B)))
      (eLpNorm_interpolate_twelveFifths_squared hv)
    exact hs.trans (by
      have h := mul_le_mul' (le_refl (eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B)))
        (mul_le_mul' h2 (le_refl
          (eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (1 / 2 : ℝ))))
      simpa only [mul_left_comm, mul_assoc] using h)
  rw [show (volume : Measure ParabolicPoint).restrict (B ×ˢ J) =
      (volume.restrict B).prod (volume.restrict J) by
    rw [Measure.prod_restrict, volume_parabolicPoint_eq_prod]]
  change (∫⁻ z : Vec3 × ℝ, ‖U z‖ₑ * ‖V z‖ₑ ^ (2 : ℝ)
    ∂(volume.restrict B).prod (volume.restrict J)) ≤ _
  have hfm : AEMeasurable (fun z : Vec3 × ℝ ↦ ‖U z‖ₑ * ‖V z‖ₑ ^ (2 : ℝ))
      ((volume.restrict B).prod (volume.restrict J)) :=
    hUp.enorm.mul (hVp.enorm.pow_const (2 : ℝ))
  rw [lintegral_prod_symm _ hfm]
  apply (lintegral_mono_ae hpoint).trans
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hM.ne).ne]
  exact (mul_le_mul' (le_refl (M ^ (3 / 4 : ℝ)))
    (lintegral_endpoint_mixed_norm_product_le hU hV)).trans_eq
    (by ring)

/-- Actual finite endpoint data implies genuine integrability of the convection density. -/
theorem endpoint_convection_integrable {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {B : Set Vec3} {J : Set ℝ} {U : ParabolicPoint → E} {V : ParabolicPoint → F}
    {M : ℝ≥0∞} (hU : AEStronglyMeasurable U (volume.restrict (B ×ˢ J)))
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J))) (hM : M < ∞)
    (hJ : volume J < ∞)
    (hXu : (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (hXv : (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖V (x, t)‖ₑ ^ (2 : ℝ)) ≤ M) :
    Integrable (fun z ↦ ‖U z‖ * ‖V z‖ ^ (2 : ℕ)) (volume.restrict (B ×ˢ J)) := by
  have hm := (endpoint_convection_lintegral_le hU hV hM henergy).trans_lt
    (show M ^ (3 / 4 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 4 : ℝ) * volume J ^ (1 / 4 : ℝ) < ∞ by
      finiteness [hM.ne, hXu.ne, hXv.ne, hJ.ne])
  apply memLp_one_iff_integrable.mp
  have hreal : AEStronglyMeasurable
      (fun z : ParabolicPoint ↦ ‖U z‖ * ‖V z‖ ^ (2 : ℕ))
      (volume.restrict (B ×ˢ J)) := hU.norm.mul (hV.norm.pow 2)
  rw [memLp_iff, eLpNorm_one_eq_lintegral_enorm hreal]
  simpa only [enorm_mul, enorm_norm, enorm_pow, ENNReal.rpow_ofNat] using hm

/-- The genuine real convection moment has the exact endpoint powers and constant one. -/
theorem endpoint_convection_integral_le {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {B : Set Vec3} {J : Set ℝ} {U : ParabolicPoint → E} {V : ParabolicPoint → F}
    {M : ℝ≥0∞} (hU : AEStronglyMeasurable U (volume.restrict (B ×ˢ J)))
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J))) (hM : M < ∞)
    (hJ : volume J < ∞)
    (hXu : (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (hXv : (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖V (x, t)‖ₑ ^ (2 : ℝ)) ≤ M) :
    (∫ z : ParabolicPoint in B ×ˢ J, ‖U z‖ * ‖V z‖ ^ (2 : ℕ)) ≤
      M.toReal ^ (3 / 4 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)).toReal ^
        (1 / 2 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)).toReal ^
        (1 / 4 : ℝ) * (volume J).toReal ^ (1 / 4 : ℝ) := by
  have hb := endpoint_convection_lintegral_le hU hV hM henergy
  have hfinite : M ^ (3 / 4 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 4 : ℝ) * volume J ^ (1 / 4 : ℝ) ≠ ∞ := by
    finiteness [hM.ne, hXu.ne, hXv.ne, hJ.ne]
  have hr := ENNReal.toReal_mono hfinite hb
  change (∫ z : ParabolicPoint, ‖U z‖ * ‖V z‖ ^ (2 : ℕ)
    ∂volume.restrict (B ×ˢ J)) ≤ _
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun z ↦ mul_nonneg (norm_nonneg _) (sq_nonneg _)))
    (hU.norm.mul (hV.norm.pow 2))]
  simp only [ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm]
  simpa only [ENNReal.rpow_ofNat, ENNReal.toReal_mul, ← ENNReal.toReal_rpow] using hr

/-- The literal projected coordinate convection is bounded by its actual mixed norm density. -/
theorem projected_convection_polynomial_abs_le (U V G : Vec3) :
    |∑ i : Fin 3, ∑ j : Fin 3, (V i * V i) * U j * G j| ≤
      9 * ‖U‖ * ‖V‖ ^ 2 * ‖G‖ := by
  calc
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |(V i * V i) * U j * G j| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖U‖ * ‖V‖ ^ 2 * ‖G‖ := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      have hv : |V i| ≤ ‖V‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm V i
      have hu : |U j| ≤ ‖U‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm U j
      have hg : |G j| ≤ ‖G‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm G j
      simp only [abs_mul]
      calc
        _ ≤ (‖V‖ * ‖V‖) * ‖U‖ * ‖G‖ := by gcongr
        _ = _ := by ring
    _ = _ := by simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring

/-- The actual cutoff-weighted coordinate convection is integrable and obeys endpoint control. -/
theorem projected_cutoff_convection_integrable_and_bound
    {B : Set Vec3} {J : Set ℝ} {U V G : ParabolicPoint → Vec3}
    {M : ℝ≥0∞} {L : ℝ}
    (hU : AEStronglyMeasurable U (volume.restrict (B ×ˢ J)))
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J)))
    (hG : AEStronglyMeasurable G (volume.restrict (B ×ˢ J)))
    (hM : M < ∞) (hJ : volume J < ∞) (hL : 0 ≤ L)
    (hXu : (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (hXv : (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖V (x, t)‖ₑ ^ (2 : ℝ)) ≤ M)
    (hcutoff : ∀ᵐ z ∂volume.restrict (B ×ˢ J), ‖G z‖ ≤ L) :
    Integrable (fun z ↦ ∑ i : Fin 3, ∑ j : Fin 3,
      (V z i * V z i) * U z j * G z j) (volume.restrict (B ×ˢ J)) ∧
    |∫ z : ParabolicPoint in B ×ˢ J, ∑ i : Fin 3, ∑ j : Fin 3,
      (V z i * V z i) * U z j * G z j| ≤
      (9 * L) * (M.toReal ^ (3 / 4 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^
          (2 : ℝ)).toReal ^ (1 / 2 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^
          (2 : ℝ)).toReal ^ (1 / 4 : ℝ) *
        (volume J).toReal ^ (1 / 4 : ℝ)) := by
  have hd := endpoint_convection_integrable hU hV hM hJ hXu hXv henergy
  have hp : AEStronglyMeasurable (fun z : ParabolicPoint ↦ ∑ i : Fin 3,
      ∑ j : Fin 3, (V z i * V z i) * U z j * G z j)
      (volume.restrict (B ×ˢ J)) := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro i _
    apply Finset.aestronglyMeasurable_fun_sum
    intro j _
    exact (((continuous_apply i).comp_aestronglyMeasurable hV).mul
      ((continuous_apply i).comp_aestronglyMeasurable hV)).mul
        ((continuous_apply j).comp_aestronglyMeasurable hU) |>.mul
        ((continuous_apply j).comp_aestronglyMeasurable hG)
  have hdom : ∀ᵐ z ∂volume.restrict (B ×ˢ J),
      ‖∑ i : Fin 3, ∑ j : Fin 3, (V z i * V z i) * U z j * G z j‖ ≤
        (9 * L) * (‖U z‖ * ‖V z‖ ^ 2) := by
    filter_upwards [hcutoff] with z hz
    rw [Real.norm_eq_abs]
    exact (projected_convection_polynomial_abs_le (U z) (V z) (G z)).trans
      ((mul_le_mul_of_nonneg_left hz (by positivity)).trans_eq (by ring))
  have hi := (hd.const_mul (9 * L)).mono' hp hdom
  refine ⟨hi, ?_⟩
  apply abs_integral_le_integral_abs.trans
  have hab := integral_mono_ae hi.norm (hd.const_mul (9 * L)) hdom
  rw [integral_const_mul] at hab
  exact hab.trans (mul_le_mul_of_nonneg_left
    (endpoint_convection_integral_le hU hV hM hJ hXu hXv henergy) (by positivity))

end FluidSingularSets
