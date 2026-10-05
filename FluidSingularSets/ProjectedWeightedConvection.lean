-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedCutoffSobolev

/-!
# Sharp convection control for the sixth-power cutoff

The fifth-power convection weight is estimated using the unweighted slice L²
energy and the L⁶ norm of the actual cubed-cutoff velocity. This preserves the
weighted norm needed for the projected energy absorption.
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

/-- Genuine cross interpolation separates the unweighted and weighted velocity factors. -/
theorem eLpNorm_cross_twelveFifths {μ : Measure Vec3} {v w : Vec3 → Vec3}
    (hv : AEStronglyMeasurable v μ) (hw : AEStronglyMeasurable w μ) :
    eLpNorm (fun x ↦ ‖v x‖ ^ (3 / 4 : ℝ) * ‖w x‖ ^ (1 / 4 : ℝ))
      (ENNReal.ofReal (12 / 5 : ℝ)) μ ≤
        eLpNorm v 2 μ ^ (3 / 4 : ℝ) * eLpNorm w 6 μ ^ (1 / 4 : ℝ) := by
  let a : Vec3 → ℝ := fun x ↦ ‖v x‖ ^ (3 / 4 : ℝ)
  let b : Vec3 → ℝ := fun x ↦ ‖w x‖ ^ (1 / 4 : ℝ)
  have ha : AEStronglyMeasurable a μ :=
    (Real.continuous_rpow_const (q := (3 / 4 : ℝ)) (by norm_num)).comp_aestronglyMeasurable
      hv.norm
  have hb : AEStronglyMeasurable b μ :=
    (Real.continuous_rpow_const (q := (1 / 4 : ℝ)) (by norm_num)).comp_aestronglyMeasurable
      hw.norm
  let : ENNReal.HolderTriple (ENNReal.ofReal (8 / 3 : ℝ)) 24
      (ENNReal.ofReal (12 / 5 : ℝ)) := by
    have h : Real.HolderTriple (8 / 3 : ℝ) 24 (12 / 5 : ℝ) := by
      rw [Real.holderTriple_iff]
      norm_num
    simpa only [ENNReal.ofReal_ofNat] using h.ennrealOfReal
  have hh : eLpNorm (fun x ↦ a x * b x) (ENNReal.ofReal (12 / 5 : ℝ)) μ ≤
      eLpNorm a (ENNReal.ofReal (8 / 3 : ℝ)) μ * eLpNorm b 24 μ := by
    simpa only [ENNReal.coe_one, one_mul] using
      eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
        (p := ENNReal.ofReal (8 / 3 : ℝ)) (q := 24) (r := ENNReal.ofReal (12 / 5 : ℝ))
        (fun x y : ℝ ↦ x * y) 1 continuous_mul ha hb
        (ae_of_all _ (fun x ↦ by simp only [norm_mul, NNReal.coe_one, one_mul, le_refl]))
  have hp2 : ENNReal.ofReal (8 / 3 : ℝ) * ENNReal.ofReal (3 / 4 : ℝ) = 2 := by
    rw [← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hp6 : (24 : ℝ≥0∞) * ENNReal.ofReal (1 / 4 : ℝ) = 6 := by
    rw [← ENNReal.ofReal_ofNat 24, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hpa := eLpNorm_norm_rpow v hv (by norm_num : (0 : ℝ) < 3 / 4)
    (p := ENNReal.ofReal (8 / 3 : ℝ))
  have hpb := eLpNorm_norm_rpow w hw (by norm_num : (0 : ℝ) < 1 / 4) (p := 24)
  rw [hp2] at hpa
  rw [hp6] at hpb
  rwa [hpa, hpb] at hh

/-- Actual spatial Hölder uses unweighted L² velocity and weighted L⁶ velocity. -/
theorem lintegral_cross_convection_le {μ : Measure Vec3} {u v w : Vec3 → Vec3}
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
    (hw : AEStronglyMeasurable w μ) :
    (∫⁻ x, ‖u x‖ₑ * (‖v x‖ₑ ^ (3 / 2 : ℝ) * ‖w x‖ₑ ^ (1 / 2 : ℝ)) ∂μ) ≤
      eLpNorm u 6 μ * (eLpNorm v 2 μ ^ (3 / 2 : ℝ) *
        eLpNorm w 6 μ ^ (1 / 2 : ℝ)) := by
  let f : Vec3 → ℝ := fun x ↦ ‖v x‖ ^ (3 / 4 : ℝ) * ‖w x‖ ^ (1 / 4 : ℝ)
  have hf : AEStronglyMeasurable f μ :=
    ((Real.continuous_rpow_const (q := (3 / 4 : ℝ)) (by norm_num)).comp_aestronglyMeasurable
      hv.norm).mul
      ((Real.continuous_rpow_const (q := (1 / 4 : ℝ)) (by norm_num)).comp_aestronglyMeasurable
        hw.norm)
  have hh := lintegral_spatial_convection_le hu hf
  have hs := ENNReal.rpow_le_rpow (eLpNorm_cross_twelveFifths hv hw)
    (by norm_num : (0 : ℝ) ≤ 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at hs
  norm_num only [show (3 / 4 : ℝ) * 2 = 3 / 2 by norm_num,
    show (1 / 4 : ℝ) * 2 = 1 / 2 by norm_num] at hs
  have heq : (fun x ↦ ‖u x‖ₑ * ‖f x‖ₑ ^ (2 : ℝ)) =
      (fun x ↦ ‖u x‖ₑ * (‖v x‖ₑ ^ (3 / 2 : ℝ) * ‖w x‖ₑ ^ (1 / 2 : ℝ))) := by
    funext x
    simp only [f, enorm_mul]
    rw [Real.enorm_rpow_of_nonneg (norm_nonneg (v x)) (by norm_num),
      Real.enorm_rpow_of_nonneg (norm_nonneg (w x)) (by norm_num)]
    simp only [enorm_norm]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    norm_num
  rw [heq] at hh
  exact hh.trans (mul_le_mul' (le_refl _) hs)

/-- The actual fifth-power weight is dominated by the cubed-velocity interpolation factors. -/
theorem fifth_cutoff_weight_convection_le (v : Vec3) {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ENNReal.ofReal a ^ 5 * ‖v‖ₑ ^ (2 : ℝ) ≤
      ‖v‖ₑ ^ (3 / 2 : ℝ) * ‖a ^ (3 : ℕ) • v‖ₑ ^ (1 / 2 : ℝ) := by
  have hb : ENNReal.ofReal a ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal ha1
  have hp := ENNReal.rpow_le_rpow_of_exponent_ge hb (by norm_num : (3 / 2 : ℝ) ≤ 5)
  norm_num only [ENNReal.rpow_ofNat] at hp
  have hw : ‖a ^ (3 : ℕ) • v‖ₑ ^ (1 / 2 : ℝ) =
      ENNReal.ofReal a ^ (3 / 2 : ℝ) * ‖v‖ₑ ^ (1 / 2 : ℝ) := by
    rw [enorm_smul, enorm_pow, Real.enorm_of_nonneg ha,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast _ 3,
      ← ENNReal.rpow_mul]
    norm_num
  rw [hw]
  calc
    _ ≤ ENNReal.ofReal a ^ (3 / 2 : ℝ) * ‖v‖ₑ ^ (2 : ℝ) := mul_le_mul' hp (le_refl _)
    _ = ENNReal.ofReal a ^ (3 / 2 : ℝ) *
        (‖v‖ₑ ^ (3 / 2 : ℝ) * ‖v‖ₑ ^ (1 / 2 : ℝ)) := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num
    _ = _ := by ring

/-- The literal weighted convection moment has the sharp actual spatial endpoint estimate. -/
theorem lintegral_fifth_weighted_convection_le {μ : Measure Vec3}
    {u v : Vec3 → Vec3} {φ : Vec3 → ℝ}
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
    (hφ : AEStronglyMeasurable φ μ) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    (∫⁻ x, ENNReal.ofReal (φ x) ^ 5 * ‖u x‖ₑ * ‖v x‖ₑ ^ (2 : ℝ) ∂μ) ≤
      eLpNorm u 6 μ * (eLpNorm v 2 μ ^ (3 / 2 : ℝ) *
        eLpNorm (fun x ↦ φ x ^ 3 • v x) 6 μ ^ (1 / 2 : ℝ)) := by
  apply (lintegral_mono (fun x ↦ ?_)).trans
    (lintegral_cross_convection_le hu hv ((hφ.pow 3).smul hv))
  calc
    _ = ‖u x‖ₑ * (ENNReal.ofReal (φ x) ^ 5 * ‖v x‖ₑ ^ (2 : ℝ)) := by ring
    _ ≤ _ := mul_le_mul' (le_refl _) (fifth_cutoff_weight_convection_le (v x) (hb x).1 (hb x).2)

/-- Genuine time Hölder gives the sharp mixed bound for the actual sixth-power cutoff. -/
theorem fifth_weighted_endpoint_convection_lintegral_le
    {B : Set Vec3} {J : Set ℝ} {U V : ParabolicPoint → Vec3} {Φ : ParabolicPoint → ℝ}
    {M : ℝ≥0∞} (hU : AEStronglyMeasurable U (volume.restrict (B ×ˢ J)))
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J)))
    (hΦ : AEStronglyMeasurable Φ (volume.restrict (B ×ˢ J)))
    (hb : ∀ z, 0 ≤ Φ z ∧ Φ z ≤ 1) (hM : M < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖V (x, t)‖ₑ ^ (2 : ℝ)) ≤ M) :
    (∫⁻ z : ParabolicPoint in B ×ˢ J,
      ENNReal.ofReal (Φ z) ^ 5 * ‖U z‖ₑ * ‖V z‖ₑ ^ (2 : ℝ)) ≤
      M ^ (3 / 4 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ Φ (x, t) ^ 3 • V (x, t)) 6
          (volume.restrict B) ^ (2 : ℝ)) ^ (1 / 4 : ℝ) * volume J ^ (1 / 4 : ℝ) := by
  have hUp : AEStronglyMeasurable U ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hU
  have hVp : AEStronglyMeasurable V ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hV
  have hΦp : AEStronglyMeasurable Φ ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hΦ
  have hpoint : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ENNReal.ofReal (Φ (x, t)) ^ 5 * ‖U (x, t)‖ₑ * ‖V (x, t)‖ₑ ^
        (2 : ℝ)) ≤ M ^ (3 / 4 : ℝ) *
          (eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) *
            eLpNorm (fun x ↦ Φ (x, t) ^ 3 • V (x, t)) 6 (volume.restrict B) ^
              (1 / 2 : ℝ)) := by
    filter_upwards [hUp.prodMk_right, hVp.prodMk_right, hΦp.prodMk_right, henergy]
      with t hut hvt hφt hEt
    have heq := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hvt
    norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at heq
    have h2 : eLpNorm (fun x ↦ V (x, t)) 2 (volume.restrict B) ^ (3 / 2 : ℝ) ≤
        M ^ (3 / 4 : ℝ) := by
      have hh := ENNReal.rpow_le_rpow
        (heq.trans_le (by simpa only [ENNReal.rpow_ofNat] using hEt))
        (by norm_num : (0 : ℝ) ≤ 3 / 4)
      rw [← ENNReal.rpow_ofNat, ← ENNReal.rpow_mul] at hh
      norm_num only [show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num] at hh
      exact hh
    apply (lintegral_fifth_weighted_convection_le hut hvt hφt (fun x ↦ hb (x, t))).trans
    have hh := mul_le_mul' (le_refl (eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B)))
      (mul_le_mul' h2 (le_refl
        (eLpNorm (fun x ↦ Φ (x, t) ^ 3 • V (x, t)) 6 (volume.restrict B) ^ (1 / 2 : ℝ))))
    simpa only [mul_left_comm, mul_assoc] using hh
  rw [show (volume : Measure ParabolicPoint).restrict (B ×ˢ J) =
      (volume.restrict B).prod (volume.restrict J) by
    rw [Measure.prod_restrict, volume_parabolicPoint_eq_prod]]
  change (∫⁻ z : Vec3 × ℝ, ENNReal.ofReal (Φ z) ^ 5 * ‖U z‖ₑ * ‖V z‖ₑ ^ (2 : ℝ)
    ∂(volume.restrict B).prod (volume.restrict J)) ≤ _
  have hfm : AEMeasurable (fun z : Vec3 × ℝ ↦ ENNReal.ofReal (Φ z) ^ 5 * ‖U z‖ₑ *
      ‖V z‖ₑ ^ (2 : ℝ)) ((volume.restrict B).prod (volume.restrict J)) :=
    ((hΦp.aemeasurable.ennreal_ofReal.pow_const 5).mul hUp.enorm).mul
      (hVp.enorm.pow_const (2 : ℝ))
  rw [lintegral_prod_symm _ hfm]
  apply (lintegral_mono_ae hpoint).trans
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hM.ne).ne]
  have hW : AEStronglyMeasurable (fun z : ParabolicPoint ↦ Φ z ^ 3 • V z)
      (volume.restrict (B ×ˢ J)) := (hΦ.pow 3).smul hV
  exact (mul_le_mul' (le_refl (M ^ (3 / 4 : ℝ)))
    (lintegral_endpoint_mixed_norm_product_le hU hW)).trans_eq (by ring)

/-- Finite sharp endpoint data implies true integrability of the fifth-weighted density. -/
theorem fifth_weighted_convection_integrable
    {B : Set Vec3} {J : Set ℝ} {U V : ParabolicPoint → Vec3} {Φ : ParabolicPoint → ℝ}
    {M : ℝ≥0∞} (hU : AEStronglyMeasurable U (volume.restrict (B ×ˢ J)))
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J)))
    (hΦ : AEStronglyMeasurable Φ (volume.restrict (B ×ˢ J)))
    (hb : ∀ z, 0 ≤ Φ z ∧ Φ z ≤ 1) (hM : M < ∞) (hJ : volume J < ∞)
    (hXu : (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (hXw : (∫⁻ t in J, eLpNorm (fun x ↦ Φ (x, t) ^ 3 • V (x, t)) 6
      (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖V (x, t)‖ₑ ^ (2 : ℝ)) ≤ M) :
    Integrable (fun z ↦ Φ z ^ 5 * ‖U z‖ * ‖V z‖ ^ (2 : ℕ))
      (volume.restrict (B ×ˢ J)) := by
  have hf := (fifth_weighted_endpoint_convection_lintegral_le hU hV hΦ hb hM henergy).trans_lt
    (show M ^ (3 / 4 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ Φ (x, t) ^ 3 • V (x, t)) 6
        (volume.restrict B) ^ (2 : ℝ)) ^ (1 / 4 : ℝ) * volume J ^ (1 / 4 : ℝ) < ∞ by
      finiteness [hM.ne, hXu.ne, hXw.ne, hJ.ne])
  have hm : AEStronglyMeasurable
      (fun z : ParabolicPoint ↦ Φ z ^ 5 * ‖U z‖ * ‖V z‖ ^ (2 : ℕ))
      (volume.restrict (B ×ˢ J)) := ((hΦ.pow 5).mul hU.norm).mul (hV.norm.pow 2)
  have hnorm (z : ParabolicPoint) : ‖Φ z‖ₑ = ENNReal.ofReal (Φ z) :=
    Real.enorm_of_nonneg (hb z).1
  apply memLp_one_iff_integrable.mp
  rw [memLp_iff, eLpNorm_one_eq_lintegral_enorm hm]
  simpa only [enorm_mul, enorm_pow, enorm_norm, hnorm, ENNReal.rpow_ofNat] using hf

/-- The literal real fifth-weighted convection moment has the sharp endpoint bound. -/
theorem fifth_weighted_convection_integral_le
    {B : Set Vec3} {J : Set ℝ} {U V : ParabolicPoint → Vec3} {Φ : ParabolicPoint → ℝ}
    {M : ℝ≥0∞} (hU : AEStronglyMeasurable U (volume.restrict (B ×ˢ J)))
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J)))
    (hΦ : AEStronglyMeasurable Φ (volume.restrict (B ×ˢ J)))
    (hb : ∀ z, 0 ≤ Φ z ∧ Φ z ≤ 1) (hM : M < ∞) (hJ : volume J < ∞)
    (hXu : (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (hXw : (∫⁻ t in J, eLpNorm (fun x ↦ Φ (x, t) ^ 3 • V (x, t)) 6
      (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖V (x, t)‖ₑ ^ (2 : ℝ)) ≤ M) :
    (∫ z : ParabolicPoint in B ×ˢ J, Φ z ^ 5 * ‖U z‖ * ‖V z‖ ^ (2 : ℕ)) ≤
      M.toReal ^ (3 / 4 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^
          (2 : ℝ)).toReal ^ (1 / 2 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ Φ (x, t) ^ 3 • V (x, t)) 6
          (volume.restrict B) ^ (2 : ℝ)).toReal ^ (1 / 4 : ℝ) *
        (volume J).toReal ^ (1 / 4 : ℝ) := by
  have hs := fifth_weighted_endpoint_convection_lintegral_le hU hV hΦ hb hM henergy
  have hfinite : M ^ (3 / 4 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ Φ (x, t) ^ 3 • V (x, t)) 6
        (volume.restrict B) ^ (2 : ℝ)) ^ (1 / 4 : ℝ) * volume J ^ (1 / 4 : ℝ) ≠ ∞ := by
    finiteness [hM.ne, hXu.ne, hXw.ne, hJ.ne]
  have hr := ENNReal.toReal_mono hfinite hs
  have hm : AEStronglyMeasurable
      (fun z : ParabolicPoint ↦ Φ z ^ 5 * ‖U z‖ * ‖V z‖ ^ (2 : ℕ))
      (volume.restrict (B ×ˢ J)) := ((hΦ.pow 5).mul hU.norm).mul (hV.norm.pow 2)
  have heq : (∫ z : ParabolicPoint in B ×ˢ J, Φ z ^ 5 * ‖U z‖ * ‖V z‖ ^ (2 : ℕ)) =
      (∫⁻ z : ParabolicPoint in B ×ˢ J,
        ENNReal.ofReal (Φ z) ^ 5 * ‖U z‖ₑ * ‖V z‖ₑ ^ (2 : ℝ)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (fun z ↦ by positivity [(hb z).1])) hm]
    congr 1
    apply lintegral_congr
    intro z
    rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (hb z).1 _) (norm_nonneg _)),
      ENNReal.ofReal_mul (pow_nonneg (hb z).1 _),
      ENNReal.ofReal_pow (hb z).1, ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [ofReal_norm, ENNReal.rpow_ofNat]
  rw [heq]
  simpa only [ENNReal.rpow_ofNat, ENNReal.toReal_mul, ← ENNReal.toReal_rpow] using hr

/-- The actual spatial derivative of the sixth-power space-time cutoff. -/
theorem spatialPartial_cutoff_sixth {Φ : Vec3 × ℝ → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin 3) (z : Vec3 × ℝ) :
    spatialPartial (fun w ↦ Φ w ^ (6 : ℕ)) i z =
      6 * Φ z ^ 5 * spatialPartial Φ i z := by
  have hs : DifferentiableAt ℝ (fun x : Vec3 ↦ Φ (x, z.2)) z.1 :=
    (hΦ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) |>.differentiableAt
  simp only [spatialPartial, fderiv_fun_pow 6 hs, Nat.cast_ofNat,
    nsmul_eq_mul, Nat.reduceSub, smul_apply, smul_eq_mul, Prod.mk.eta]

/-- The true projected convection polynomial with a sixth-power cutoff has its gap factor. -/
theorem sixth_cutoff_convection_polynomial_abs_le
    {Φ : Vec3 × ℝ → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hb : ∀ z, 0 ≤ Φ z ∧ Φ z ≤ 1) {L : ℝ} (_hL : 0 ≤ L)
    (hgrad : ∀ z, ‖fun j : Fin 3 ↦ spatialPartial Φ j z‖ ≤ L)
    (U V : Vec3) (z : ParabolicPoint) :
    |∑ i : Fin 3, ∑ j : Fin 3, (V i * V i) * U j *
      spatialPartial (fun w ↦ Φ w ^ (6 : ℕ)) j z| ≤
        (54 * L) * (Φ z ^ 5 * ‖U‖ * ‖V‖ ^ 2) := by
  have hg : (fun j : Fin 3 ↦ spatialPartial (fun w ↦ Φ w ^ (6 : ℕ)) j z) =
      (6 * Φ z ^ 5) • (fun j : Fin 3 ↦ spatialPartial Φ j z) := by
    ext j
    exact spatialPartial_cutoff_sixth hΦ j z
  apply (projected_convection_polynomial_abs_le U V _).trans
  rw [hg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity [(hb z).1])]
  calc
    _ ≤ 9 * ‖U‖ * ‖V‖ ^ 2 * ((6 * Φ z ^ 5) * L) := by
      gcongr
      · positivity [(hb z).1]
      · exact hgrad z
    _ = _ := by ring

/-- The true Euclidean convection term equals its literal coordinate polynomial. -/
theorem projected_energy_convection_eq_coordinate_sum (U V G : Vec3) :
    vec3EuclideanNorm V ^ 2 * (∑ j : Fin 3, U j * G j) =
      ∑ i : Fin 3, ∑ j : Fin 3, (V i * V i) * U j * G j := by
  rw [vec3EuclideanNorm, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))]
  simp only [Finset.sum_mul, Finset.mul_sum, pow_two, mul_assoc]
  rw [Finset.sum_comm]

/-- The actual projected sixth-cutoff convection integral has sharp weighted endpoint control. -/
theorem sixth_cutoff_convection_integrable_and_bound
    {B : Set Vec3} {J : Set ℝ} {U V : ParabolicPoint → Vec3} {Φ : Vec3 × ℝ → ℝ}
    {M : ℝ≥0∞} {L : ℝ}
    (hU : AEStronglyMeasurable U (volume.restrict (B ×ˢ J)))
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J)))
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hb : ∀ z, 0 ≤ Φ z ∧ Φ z ≤ 1)
    (hL : 0 ≤ L) (hgrad : ∀ z, ‖fun j : Fin 3 ↦ spatialPartial Φ j z‖ ≤ L)
    (hM : M < ∞) (hJ : volume J < ∞)
    (hXu : (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (hXw : (∫⁻ t in J, eLpNorm (fun x ↦ Φ (x, t) ^ 3 • V (x, t)) 6
      (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖V (x, t)‖ₑ ^ (2 : ℝ)) ≤ M) :
    Integrable (fun z ↦ vec3EuclideanNorm (V z) ^ 2 *
      (∑ j : Fin 3, U z j * spatialPartial (fun w ↦ Φ w ^ (6 : ℕ)) j z))
        (volume.restrict (B ×ˢ J)) ∧
    |∫ z : ParabolicPoint in B ×ˢ J, vec3EuclideanNorm (V z) ^ 2 *
      (∑ j : Fin 3, U z j * spatialPartial (fun w ↦ Φ w ^ (6 : ℕ)) j z)| ≤
        (54 * L) * (M.toReal ^ (3 / 4 : ℝ) *
          (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^
            (2 : ℝ)).toReal ^ (1 / 2 : ℝ) *
          (∫⁻ t in J, eLpNorm (fun x ↦ Φ (x, t) ^ 3 • V (x, t)) 6
            (volume.restrict B) ^ (2 : ℝ)).toReal ^ (1 / 4 : ℝ) *
          (volume J).toReal ^ (1 / 4 : ℝ)) := by
  have hφm : AEStronglyMeasurable Φ (volume.restrict (B ×ˢ J)) :=
    hΦ.continuous.aestronglyMeasurable
  have hd := fifth_weighted_convection_integrable hU hV hφm hb hM hJ hXu hXw henergy
  have hp : AEStronglyMeasurable (fun z : ParabolicPoint ↦
      vec3EuclideanNorm (V z) ^ 2 *
        (∑ j : Fin 3, U z j * spatialPartial (fun w ↦ Φ w ^ (6 : ℕ)) j z))
      (volume.restrict (B ×ˢ J)) := by
    apply ((CKN.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hV).pow 2).mul
    apply Finset.aestronglyMeasurable_fun_sum
    intro j _
    exact ((continuous_apply j).comp_aestronglyMeasurable hU).mul
      (spatialPartial_contDiff (hΦ.pow 6) j).continuous.aestronglyMeasurable
  have hdom : ∀ᵐ z ∂volume.restrict (B ×ˢ J),
      ‖vec3EuclideanNorm (V z) ^ 2 *
        (∑ j : Fin 3, U z j * spatialPartial (fun w ↦ Φ w ^ (6 : ℕ)) j z)‖ ≤
      (54 * L) * (Φ z ^ 5 * ‖U z‖ * ‖V z‖ ^ (2 : ℕ)) := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs, projected_energy_convection_eq_coordinate_sum]
    exact sixth_cutoff_convection_polynomial_abs_le hΦ hb hL hgrad (U z) (V z) z
  have hi := (hd.const_mul (54 * L)).mono' hp hdom
  refine ⟨hi, ?_⟩
  apply abs_integral_le_integral_abs.trans
  have hab := integral_mono_ae hi.norm (hd.const_mul (54 * L)) hdom
  rw [integral_const_mul] at hab
  exact hab.trans (mul_le_mul_of_nonneg_left
    (fifth_weighted_convection_integral_le hU hV hφm hb hM hJ hXu hXw henergy)
    (by positivity))

end FluidSingularSets
