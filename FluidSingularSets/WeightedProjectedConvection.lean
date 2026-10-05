-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedCutoffMixedEnergy

/-!
# Convection controlled by the actual weighted energy

The fifth cutoff power factors exactly into one third of the unweighted
velocity and five thirds of the cubed-cutoff velocity. Genuine spatial and
time Hölder bounds therefore use the weighted slice energy supremum.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Genuine spatial Hölder separates the weighted square energy and weighted L⁶ norm. -/
theorem lintegral_weighted_cross_convection_le {μ : Measure Vec3}
    {U V W : Vec3 → Vec3}
    (hU : AEStronglyMeasurable U μ) (hV : AEStronglyMeasurable V μ)
    (hW : AEStronglyMeasurable W μ) :
    (∫⁻ x, ‖U x‖ₑ * ‖V x‖ₑ ^ (1 / 3 : ℝ) * ‖W x‖ₑ ^ (5 / 3 : ℝ) ∂μ) ≤
      eLpNorm U 6 μ * eLpNorm V 6 μ ^ (1 / 3 : ℝ) *
        eLpNorm W 2 μ ^ (3 / 2 : ℝ) * eLpNorm W 6 μ ^ (1 / 6 : ℝ) := by
  let F : Fin 4 → Vec3 → ℝ≥0∞ :=
    ![fun x ↦ ‖U x‖ₑ ^ (6 : ℝ), fun x ↦ ‖V x‖ₑ ^ (6 : ℝ),
      fun x ↦ ‖W x‖ₑ ^ (2 : ℝ), fun x ↦ ‖W x‖ₑ ^ (6 : ℝ)]
  let a : Fin 4 → ℝ := ![1 / 6, 1 / 18, 3 / 4, 1 / 36]
  have hm : ∀ i ∈ (Finset.univ : Finset (Fin 4)), AEMeasurable (F i) μ := by
    intro i _
    fin_cases i
    · exact hU.enorm.pow_const _
    · exact hV.enorm.pow_const _
    · exact hW.enorm.pow_const _
    · exact hW.enorm.pow_const _
  have ha : ∑ i ∈ (Finset.univ : Finset (Fin 4)), a i = 1 := by
    norm_num [Fin.sum_univ_four, a]
  have hapos : ∀ i ∈ (Finset.univ : Finset (Fin 4)), 0 ≤ a i := by
    intro i _
    fin_cases i <;> norm_num [a]
  have hh := ENNReal.lintegral_prod_norm_pow_le Finset.univ hm ha hapos
  simp only [Fin.prod_univ_four] at hh
  norm_num [F, a, ← ENNReal.rpow_mul] at hh
  simp_rw [← ENNReal.rpow_natCast _ 6, ← ENNReal.rpow_natCast _ 2,
    ← ENNReal.rpow_mul] at hh
  norm_num only [ENNReal.rpow_one] at hh
  have he : (fun x ↦ ‖U x‖ₑ * ‖V x‖ₑ ^ (1 / 3 : ℝ) *
      ‖W x‖ₑ ^ (3 / 2 : ℝ) * ‖W x‖ₑ ^ (1 / 6 : ℝ)) =
      fun x ↦ ‖U x‖ₑ * ‖V x‖ₑ ^ (1 / 3 : ℝ) * ‖W x‖ₑ ^ (5 / 3 : ℝ) := by
    funext x
    rw [mul_assoc (_ * _) (_ ^ _) (_ ^ _),
      ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  rw [he] at hh
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hU,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hV,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hW,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hW]
  norm_num only [ENNReal.toReal_ofNat, ← ENNReal.rpow_mul]
  exact hh

/-- Genuine time Hölder gives the three endpoint norms and the exact time-length power. -/
theorem lintegral_weighted_endpoint_norm_product_le
    {B : Set Vec3} {J : Set ℝ} {U V W : ParabolicPoint → Vec3}
    (hU : AEStronglyMeasurable U (volume.restrict (B ×ˢ J)))
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J)))
    (hW : AEStronglyMeasurable W (volume.restrict (B ×ˢ J))) :
    (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) *
      eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (1 / 3 : ℝ) *
      eLpNorm (fun x ↦ W (x, t)) 6 (volume.restrict B) ^ (1 / 6 : ℝ)) ≤
      (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 6 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ W (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 12 : ℝ) * volume J ^ (1 / 4 : ℝ) := by
  let F : Fin 4 → ℝ → ℝ≥0∞ :=
    ![fun t ↦ eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ),
      fun t ↦ eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ),
      fun t ↦ eLpNorm (fun x ↦ W (x, t)) 6 (volume.restrict B) ^ (2 : ℝ), fun _ ↦ 1]
  let a : Fin 4 → ℝ := ![1 / 2, 1 / 6, 1 / 12, 1 / 4]
  have hm : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      AEMeasurable (F i) (volume.restrict J) := by
    intro i _
    fin_cases i
    · exact aemeasurable_spatial_six_square hU
    · exact aemeasurable_spatial_six_square hV
    · exact aemeasurable_spatial_six_square hW
    · exact aemeasurable_const
  have ha : ∑ i ∈ (Finset.univ : Finset (Fin 4)), a i = 1 := by
    norm_num [Fin.sum_univ_four, a]
  have hapos : ∀ i ∈ (Finset.univ : Finset (Fin 4)), 0 ≤ a i := by
    intro i _
    fin_cases i <;> norm_num [a]
  have hh := ENNReal.lintegral_prod_norm_pow_le Finset.univ hm ha hapos
  simp only [Fin.prod_univ_four] at hh
  norm_num [F, a, ← ENNReal.rpow_mul, lintegral_const, Measure.restrict_apply_univ] at hh
  simp_rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul] at hh
  norm_num only [ENNReal.rpow_one] at hh
  exact hh

/-- The fifth cutoff power has the exact weighted factorization for the endpoint proof. -/
theorem fifth_cutoff_weight_convection_eq (v : Vec3) {a : ℝ} (ha : 0 ≤ a) :
    ENNReal.ofReal a ^ 5 * ‖v‖ₑ ^ (2 : ℝ) =
      ‖v‖ₑ ^ (1 / 3 : ℝ) * ‖a ^ (3 : ℕ) • v‖ₑ ^ (5 / 3 : ℝ) := by
  rw [enorm_smul, enorm_pow, Real.enorm_of_nonneg ha,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast _ 3,
    ← ENNReal.rpow_mul]
  norm_num only [show (3 : ℝ) * (5 / 3) = 5 by norm_num, ENNReal.rpow_ofNat]
  calc
    _ = ENNReal.ofReal a ^ 5 * (‖v‖ₑ ^ (1 / 3 : ℝ) * ‖v‖ₑ ^ (5 / 3 : ℝ)) := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num
    _ = _ := by ring

/-- The actual fifth-power convection is controlled by the weighted slice energy supremum. -/
theorem fifth_weighted_sliceEnergy_convection_lintegral_le
    {B : Set Vec3} {J : Set ℝ} {U V : ParabolicPoint → Vec3} {Φ : ParabolicPoint → ℝ}
    {M : ℝ≥0∞} (hU : AEStronglyMeasurable U (volume.restrict (B ×ˢ J)))
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J)))
    (hΦ : AEStronglyMeasurable Φ (volume.restrict (B ×ˢ J)))
    (hb : ∀ z, 0 ≤ Φ z) (hM : M < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖Φ (x, t) ^ 3 • V (x, t)‖ₑ ^ (2 : ℝ)) ≤ M) :
    (∫⁻ z : ParabolicPoint in B ×ˢ J,
      ENNReal.ofReal (Φ z) ^ 5 * ‖U z‖ₑ * ‖V z‖ₑ ^ (2 : ℝ)) ≤
      M ^ (3 / 4 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
          (1 / 6 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ Φ (x, t) ^ 3 • V (x, t)) 6
          (volume.restrict B) ^ (2 : ℝ)) ^ (1 / 12 : ℝ) * volume J ^ (1 / 4 : ℝ) := by
  let W : ParabolicPoint → Vec3 := fun z ↦ Φ z ^ 3 • V z
  have hW : AEStronglyMeasurable W (volume.restrict (B ×ˢ J)) := (hΦ.pow 3).smul hV
  have hUp : AEStronglyMeasurable U ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hU
  have hVp : AEStronglyMeasurable V ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hV
  have hWp : AEStronglyMeasurable W ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hW
  have hpoint : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ENNReal.ofReal (Φ (x, t)) ^ 5 * ‖U (x, t)‖ₑ *
        ‖V (x, t)‖ₑ ^ (2 : ℝ)) ≤ M ^ (3 / 4 : ℝ) *
          (eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) *
            eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (1 / 3 : ℝ) *
            eLpNorm (fun x ↦ W (x, t)) 6 (volume.restrict B) ^ (1 / 6 : ℝ)) := by
    filter_upwards [hUp.prodMk_right, hVp.prodMk_right, hWp.prodMk_right, henergy]
      with t hut hvt hwt hEt
    have heq := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hwt
    norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at heq
    have h2 : eLpNorm (fun x ↦ W (x, t)) 2 (volume.restrict B) ^ (3 / 2 : ℝ) ≤
        M ^ (3 / 4 : ℝ) := by
      have hh := ENNReal.rpow_le_rpow
        (heq.trans_le (by simpa only [ENNReal.rpow_ofNat, W] using hEt))
        (by norm_num : (0 : ℝ) ≤ 3 / 4)
      rw [← ENNReal.rpow_ofNat, ← ENNReal.rpow_mul] at hh
      norm_num only [show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num] at hh
      exact hh
    have he : (fun x ↦ ENNReal.ofReal (Φ (x, t)) ^ 5 * ‖U (x, t)‖ₑ *
        ‖V (x, t)‖ₑ ^ (2 : ℝ)) =
        fun x ↦ ‖U (x, t)‖ₑ * ‖V (x, t)‖ₑ ^ (1 / 3 : ℝ) *
          ‖W (x, t)‖ₑ ^ (5 / 3 : ℝ) := by
      funext x
      rw [show ENNReal.ofReal (Φ (x, t)) ^ 5 * ‖U (x, t)‖ₑ *
        ‖V (x, t)‖ₑ ^ (2 : ℝ) = ‖U (x, t)‖ₑ *
          (ENNReal.ofReal (Φ (x, t)) ^ 5 * ‖V (x, t)‖ₑ ^ (2 : ℝ)) by ring,
        fifth_cutoff_weight_convection_eq _ (hb (x, t))]
      simp only [W, mul_assoc]
    rw [he]
    exact (lintegral_weighted_cross_convection_le hut hvt hwt).trans
      (by
        have hh := mul_le_mul'
          (mul_le_mul' (le_refl
            (eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) *
              eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (1 / 3 : ℝ))) h2)
          (le_refl (eLpNorm (fun x ↦ W (x, t)) 6 (volume.restrict B) ^ (1 / 6 : ℝ)))
        simpa only [mul_left_comm, mul_comm, mul_assoc] using hh)
  have hΦp : AEStronglyMeasurable Φ ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hΦ
  have hfm : AEMeasurable (fun z : Vec3 × ℝ ↦ ENNReal.ofReal (Φ z) ^ 5 * ‖U z‖ₑ *
      ‖V z‖ₑ ^ (2 : ℝ)) ((volume.restrict B).prod (volume.restrict J)) :=
    ((hΦp.aemeasurable.ennreal_ofReal.pow_const 5).mul hUp.enorm).mul
      (hVp.enorm.pow_const (2 : ℝ))
  rw [show (volume : Measure ParabolicPoint).restrict (B ×ˢ J) =
      (volume.restrict B).prod (volume.restrict J) by
    rw [Measure.prod_restrict, volume_parabolicPoint_eq_prod]]
  change (∫⁻ z : Vec3 × ℝ,
    ENNReal.ofReal (Φ z) ^ 5 * ‖U z‖ₑ * ‖V z‖ₑ ^ (2 : ℝ)
    ∂(volume.restrict B).prod (volume.restrict J)) ≤ _
  rw [lintegral_prod_symm _ hfm]
  apply (lintegral_mono_ae hpoint).trans
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hM.ne).ne]
  exact (mul_le_mul' (le_refl (M ^ (3 / 4 : ℝ)))
    (lintegral_weighted_endpoint_norm_product_le hU hV hW)).trans_eq (by ring)

/-- The actual weighted square supremum and mixed square cost give energy exponent five sixths. -/
theorem fifth_weighted_mixedEnergy_convection_lintegral_le
    {B : Set Vec3} {J : Set ℝ} {U V : ParabolicPoint → Vec3} {Φ : ParabolicPoint → ℝ}
    {M : ℝ≥0∞} (hU : AEStronglyMeasurable U (volume.restrict (B ×ˢ J)))
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J)))
    (hΦ : AEStronglyMeasurable Φ (volume.restrict (B ×ˢ J)))
    (hb : ∀ z, 0 ≤ Φ z) (hM : M < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖Φ (x, t) ^ 3 • V (x, t)‖ₑ ^ (2 : ℝ)) ≤ M) :
    let XW := ∫⁻ t in J, eLpNorm (fun x ↦ Φ (x, t) ^ 3 • V (x, t)) 6
      (volume.restrict B) ^ (2 : ℝ)
    (∫⁻ z : ParabolicPoint in B ×ˢ J,
      ENNReal.ofReal (Φ z) ^ 5 * ‖U z‖ₑ * ‖V z‖ₑ ^ (2 : ℝ)) ≤
      (M + XW) ^ (5 / 6 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
          (1 / 6 : ℝ) * volume J ^ (1 / 4 : ℝ) := by
  let XW := ∫⁻ t in J, eLpNorm (fun x ↦ Φ (x, t) ^ 3 • V (x, t)) 6
    (volume.restrict B) ^ (2 : ℝ)
  have hE : M ^ (3 / 4 : ℝ) * XW ^ (1 / 12 : ℝ) ≤ (M + XW) ^ (5 / 6 : ℝ) := by
    have hh := mul_le_mul'
      (ENNReal.rpow_le_rpow (self_le_add_right M XW)
        (by norm_num : (0 : ℝ) ≤ 3 / 4))
      (ENNReal.rpow_le_rpow (show XW ≤ M + XW by
        simpa only [add_comm] using self_le_add_right XW M)
        (by norm_num : (0 : ℝ) ≤ 1 / 12))
    apply hh.trans_eq
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hh := fifth_weighted_sliceEnergy_convection_lintegral_le hU hV hΦ hb hM henergy
  apply hh.trans
  calc
    _ = (M ^ (3 / 4 : ℝ) * XW ^ (1 / 12 : ℝ)) *
        ((∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
          (1 / 6 : ℝ) * volume J ^ (1 / 4 : ℝ)) := by ring
    _ ≤ _ := (mul_le_mul' hE le_rfl).trans_eq (by ring)

/-- Finite true weighted endpoint data make the literal convection density integrable. -/
theorem fifth_weighted_sliceEnergy_convection_integrable
    {B : Set Vec3} {J : Set ℝ} {U V : ParabolicPoint → Vec3} {Φ : ParabolicPoint → ℝ}
    {M : ℝ≥0∞} (hU : AEStronglyMeasurable U (volume.restrict (B ×ˢ J)))
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J)))
    (hΦ : AEStronglyMeasurable Φ (volume.restrict (B ×ˢ J)))
    (hb : ∀ z, 0 ≤ Φ z) (hM : M < ∞) (hJ : volume J < ∞)
    (hXu : (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (hXv : (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (hXw : (∫⁻ t in J, eLpNorm (fun x ↦ Φ (x, t) ^ 3 • V (x, t)) 6
      (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖Φ (x, t) ^ 3 • V (x, t)‖ₑ ^ (2 : ℝ)) ≤ M) :
    Integrable (fun z ↦ Φ z ^ 5 * ‖U z‖ * ‖V z‖ ^ (2 : ℕ))
      (volume.restrict (B ×ˢ J)) := by
  have hf := (fifth_weighted_sliceEnergy_convection_lintegral_le hU hV hΦ hb hM henergy).trans_lt
    (show M ^ (3 / 4 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 6 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ Φ (x, t) ^ 3 • V (x, t)) 6
        (volume.restrict B) ^ (2 : ℝ)) ^ (1 / 12 : ℝ) * volume J ^ (1 / 4 : ℝ) < ∞ by
      finiteness [hM.ne, hXu.ne, hXv.ne, hXw.ne, hJ.ne])
  have hm : AEStronglyMeasurable
      (fun z : ParabolicPoint ↦ Φ z ^ 5 * ‖U z‖ * ‖V z‖ ^ (2 : ℕ))
      (volume.restrict (B ×ˢ J)) := ((hΦ.pow 5).mul hU.norm).mul (hV.norm.pow 2)
  have hn (z : ParabolicPoint) : ‖Φ z‖ₑ = ENNReal.ofReal (Φ z) :=
    Real.enorm_of_nonneg (hb z)
  apply memLp_one_iff_integrable.mp
  rw [memLp_iff, eLpNorm_one_eq_lintegral_enorm hm]
  simpa only [enorm_mul, enorm_pow, enorm_norm, hn, ENNReal.rpow_ofNat] using hf

/-- The literal real weighted convection moment has the true five-sixths energy bound. -/
theorem fifth_weighted_mixedEnergy_convection_integral_le
    {B : Set Vec3} {J : Set ℝ} {U V : ParabolicPoint → Vec3} {Φ : ParabolicPoint → ℝ}
    {M : ℝ≥0∞} (hU : AEStronglyMeasurable U (volume.restrict (B ×ˢ J)))
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J)))
    (hΦ : AEStronglyMeasurable Φ (volume.restrict (B ×ˢ J)))
    (hb : ∀ z, 0 ≤ Φ z) (hM : M < ∞) (hJ : volume J < ∞)
    (hXu : (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (hXv : (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (hXw : (∫⁻ t in J, eLpNorm (fun x ↦ Φ (x, t) ^ 3 • V (x, t)) 6
      (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖Φ (x, t) ^ 3 • V (x, t)‖ₑ ^ (2 : ℝ)) ≤ M) :
    let XW := ∫⁻ t in J, eLpNorm (fun x ↦ Φ (x, t) ^ 3 • V (x, t)) 6
      (volume.restrict B) ^ (2 : ℝ)
    (∫ z : ParabolicPoint in B ×ˢ J, Φ z ^ 5 * ‖U z‖ * ‖V z‖ ^ (2 : ℕ)) ≤
      (M + XW).toReal ^ (5 / 6 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^
          (2 : ℝ)).toReal ^ (1 / 2 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^
          (2 : ℝ)).toReal ^ (1 / 6 : ℝ) * (volume J).toReal ^ (1 / 4 : ℝ) := by
  let XW := ∫⁻ t in J, eLpNorm (fun x ↦ Φ (x, t) ^ 3 • V (x, t)) 6
    (volume.restrict B) ^ (2 : ℝ)
  have hs := fifth_weighted_mixedEnergy_convection_lintegral_le hU hV hΦ hb hM henergy
  have hfinite : (M + XW) ^ (5 / 6 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 6 : ℝ) * volume J ^ (1 / 4 : ℝ) ≠ ∞ := by
    finiteness [hM.ne, hXu.ne, hXv.ne, hXw.ne, hJ.ne]
  have hr := ENNReal.toReal_mono hfinite hs
  have hm : AEStronglyMeasurable
      (fun z : ParabolicPoint ↦ Φ z ^ 5 * ‖U z‖ * ‖V z‖ ^ (2 : ℕ))
      (volume.restrict (B ×ˢ J)) := ((hΦ.pow 5).mul hU.norm).mul (hV.norm.pow 2)
  have heq : (∫ z : ParabolicPoint in B ×ˢ J, Φ z ^ 5 * ‖U z‖ * ‖V z‖ ^ (2 : ℕ)) =
      (∫⁻ z : ParabolicPoint in B ×ˢ J,
        ENNReal.ofReal (Φ z) ^ 5 * ‖U z‖ₑ * ‖V z‖ₑ ^ (2 : ℝ)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (fun z ↦ by positivity [hb z])) hm]
    congr 1
    apply lintegral_congr
    intro z
    rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (hb z) _) (norm_nonneg _)),
      ENNReal.ofReal_mul (pow_nonneg (hb z) _),
      ENNReal.ofReal_pow (hb z), ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [ofReal_norm, ENNReal.rpow_ofNat]
  rw [heq]
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] using hr

end FluidSingularSets
