-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.WeightedProjectedConvection

/-!
# Genuine time weighted endpoint convection

The sixth root of a nonnegative time weight gives an actual cubed cutoff
velocity equal to the square-root weighted velocity. Its fifth power dominates
the literal time weighted convection when the time weight is at most one.
Thus the proved endpoint Hölder estimate uses precisely the tested energy.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual sixth root produces precisely the square-root time weighted velocity. -/
theorem sixth_root_cutoff_cube_smul_eq (v : Vec3) {a θ : ℝ} (hθ : 0 ≤ θ) :
    (θ ^ (1 / 6 : ℝ) * a) ^ (3 : ℕ) • v = Real.sqrt θ • (a ^ (3 : ℕ) • v) := by
  rw [mul_pow, ← Real.rpow_mul_natCast hθ (1 / 6 : ℝ) 3]
  norm_num only [show (1 / 6 : ℝ) * (3 : ℕ) = 1 / 2 by norm_num]
  rw [← Real.sqrt_eq_rpow, mul_smul]

/-- A genuine unit time weight is dominated by the fifth power of its sixth root. -/
theorem time_weighted_fifth_cutoff_le {a θ : ℝ} (ha : 0 ≤ a)
    (hθ : 0 ≤ θ ∧ θ ≤ 1) :
    ENNReal.ofReal θ * ENNReal.ofReal a ^ 5 ≤
      ENNReal.ofReal (θ ^ (1 / 6 : ℝ) * a) ^ 5 := by
  rw [← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_mul hθ.1,
    ← ENNReal.ofReal_pow (mul_nonneg (Real.rpow_nonneg hθ.1 _) ha)]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_pow, ← Real.rpow_mul_natCast hθ.1 (1 / 6 : ℝ) 5]
  norm_num only [show (1 / 6 : ℝ) * (5 : ℕ) = 5 / 6 by norm_num]
  exact mul_le_mul_of_nonneg_right
    (Real.self_le_rpow_of_le_one hθ.1 hθ.2 (by norm_num : (5 / 6 : ℝ) ≤ 1))
    (pow_nonneg ha _)

/-- Endpoint Hölder uses the actual square-root time weighted slice energy and mixed cost. -/
theorem time_weighted_fifth_mixedEnergy_convection_lintegral_le
    {B : Set Vec3} {J : Set ℝ} {U V : ParabolicPoint → Vec3}
    {Φ Θ : ParabolicPoint → ℝ} {M : ℝ≥0∞}
    (hU : AEStronglyMeasurable U (volume.restrict (B ×ˢ J)))
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J)))
    (hΦ : AEStronglyMeasurable Φ (volume.restrict (B ×ˢ J)))
    (hΘ : AEStronglyMeasurable Θ (volume.restrict (B ×ˢ J)))
    (hb : ∀ z, 0 ≤ Φ z) (hθ : ∀ z, 0 ≤ Θ z ∧ Θ z ≤ 1) (hM : M < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖Real.sqrt (Θ (x, t)) • (Φ (x, t) ^ 3 • V (x, t))‖ₑ ^
        (2 : ℝ)) ≤ M) :
    let XW := ∫⁻ t in J, eLpNorm
      (fun x ↦ Real.sqrt (Θ (x, t)) • (Φ (x, t) ^ 3 • V (x, t))) 6
      (volume.restrict B) ^ (2 : ℝ)
    (∫⁻ z : ParabolicPoint in B ×ˢ J,
      ENNReal.ofReal (Θ z) * ENNReal.ofReal (Φ z) ^ 5 * ‖U z‖ₑ * ‖V z‖ₑ ^
        (2 : ℝ)) ≤
      (M + XW) ^ (5 / 6 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
          (1 / 6 : ℝ) * volume J ^ (1 / 4 : ℝ) := by
  let Ψ : ParabolicPoint → ℝ := fun z ↦ Θ z ^ (1 / 6 : ℝ) * Φ z
  have hp : Continuous (fun s : ℝ ↦ s ^ (1 / 6 : ℝ)) :=
    Real.continuous_rpow_const (by norm_num)
  have hΨ : AEStronglyMeasurable Ψ (volume.restrict (B ×ˢ J)) :=
    (hp.comp_aestronglyMeasurable hΘ).mul hΦ
  have hΨ0 (z : ParabolicPoint) : 0 ≤ Ψ z :=
    mul_nonneg (Real.rpow_nonneg (hθ z).1 _) (hb z)
  have heq (z : ParabolicPoint) : Ψ z ^ 3 • V z =
      Real.sqrt (Θ z) • (Φ z ^ 3 • V z) :=
    sixth_root_cutoff_cube_smul_eq (V z) (hθ z).1
  have hE : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖Ψ (x, t) ^ 3 • V (x, t)‖ₑ ^ (2 : ℝ)) ≤ M := by
    simpa only [heq] using henergy
  have hh := fifth_weighted_mixedEnergy_convection_lintegral_le
    hU hV hΨ hΨ0 hM hE
  dsimp only at hh ⊢
  simp_rw [heq] at hh
  apply (lintegral_mono fun z ↦ ?_).trans hh
  exact mul_le_mul' (mul_le_mul' (time_weighted_fifth_cutoff_le (hb z) (hθ z))
    (le_refl ‖U z‖ₑ)) (le_refl (‖V z‖ₑ ^ (2 : ℝ)))

/-- Finite genuine weighted endpoint moments make the literal time weighted density integrable. -/
theorem time_weighted_fifth_convection_integrable
    {B : Set Vec3} {J : Set ℝ} {U V : ParabolicPoint → Vec3}
    {Φ Θ : ParabolicPoint → ℝ} {M : ℝ≥0∞}
    (hU : AEStronglyMeasurable U (volume.restrict (B ×ˢ J)))
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J)))
    (hΦ : AEStronglyMeasurable Φ (volume.restrict (B ×ˢ J)))
    (hΘ : AEStronglyMeasurable Θ (volume.restrict (B ×ˢ J)))
    (hb : ∀ z, 0 ≤ Φ z) (hθ : ∀ z, 0 ≤ Θ z ∧ Θ z ≤ 1) (hM : M < ∞)
    (hJ : volume J < ∞)
    (hXu : (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (hXv : (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (hXw : (∫⁻ t in J, eLpNorm
      (fun x ↦ Real.sqrt (Θ (x, t)) • (Φ (x, t) ^ 3 • V (x, t))) 6
      (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖Real.sqrt (Θ (x, t)) • (Φ (x, t) ^ 3 • V (x, t))‖ₑ ^
        (2 : ℝ)) ≤ M) :
    Integrable (fun z : ParabolicPoint ↦ Θ z * Φ z ^ 5 * ‖U z‖ * ‖V z‖ ^ (2 : ℕ))
      (volume.restrict (B ×ˢ J)) := by
  have hf := (time_weighted_fifth_mixedEnergy_convection_lintegral_le
    hU hV hΦ hΘ hb hθ hM henergy).trans_lt
      (show (M + ∫⁻ t in J, eLpNorm
        (fun x ↦ Real.sqrt (Θ (x, t)) • (Φ (x, t) ^ 3 • V (x, t))) 6
        (volume.restrict B) ^ (2 : ℝ)) ^ (5 / 6 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
          (1 / 6 : ℝ) * volume J ^ (1 / 4 : ℝ) < ∞ by
        finiteness [hM.ne, hXu.ne, hXv.ne, hXw.ne, hJ.ne])
  have hm : AEStronglyMeasurable
      (fun z : ParabolicPoint ↦ Θ z * Φ z ^ 5 * ‖U z‖ * ‖V z‖ ^ (2 : ℕ))
      (volume.restrict (B ×ˢ J)) := ((hΘ.mul (hΦ.pow 5)).mul hU.norm).mul (hV.norm.pow 2)
  apply memLp_one_iff_integrable.mp
  rw [memLp_iff, eLpNorm_one_eq_lintegral_enorm hm]
  simpa only [enorm_mul, enorm_pow, enorm_norm, Real.enorm_of_nonneg (hb _),
    Real.enorm_of_nonneg (hθ _).1, ENNReal.rpow_ofNat] using hf

/-- The literal real time weighted convection has the tested five-sixths energy bound. -/
theorem time_weighted_fifth_mixedEnergy_convection_integral_le
    {B : Set Vec3} {J : Set ℝ} {U V : ParabolicPoint → Vec3}
    {Φ Θ : ParabolicPoint → ℝ} {M : ℝ≥0∞}
    (hU : AEStronglyMeasurable U (volume.restrict (B ×ˢ J)))
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J)))
    (hΦ : AEStronglyMeasurable Φ (volume.restrict (B ×ˢ J)))
    (hΘ : AEStronglyMeasurable Θ (volume.restrict (B ×ˢ J)))
    (hb : ∀ z, 0 ≤ Φ z) (hθ : ∀ z, 0 ≤ Θ z ∧ Θ z ≤ 1) (hM : M < ∞)
    (hJ : volume J < ∞)
    (hXu : (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (hXv : (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (hXw : (∫⁻ t in J, eLpNorm
      (fun x ↦ Real.sqrt (Θ (x, t)) • (Φ (x, t) ^ 3 • V (x, t))) 6
      (volume.restrict B) ^ (2 : ℝ)) < ∞)
    (henergy : ∀ᵐ t ∂volume.restrict J,
      (∫⁻ x in B, ‖Real.sqrt (Θ (x, t)) • (Φ (x, t) ^ 3 • V (x, t))‖ₑ ^
        (2 : ℝ)) ≤ M) :
    let XW := ∫⁻ t in J, eLpNorm
      (fun x ↦ Real.sqrt (Θ (x, t)) • (Φ (x, t) ^ 3 • V (x, t))) 6
      (volume.restrict B) ^ (2 : ℝ)
    (∫ z : ParabolicPoint in B ×ˢ J, Θ z * Φ z ^ 5 * ‖U z‖ * ‖V z‖ ^ (2 : ℕ)) ≤
      (M + XW).toReal ^ (5 / 6 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^
          (2 : ℝ)).toReal ^ (1 / 2 : ℝ) *
        (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^
          (2 : ℝ)).toReal ^ (1 / 6 : ℝ) * (volume J).toReal ^ (1 / 4 : ℝ) := by
  let XW := ∫⁻ t in J, eLpNorm
    (fun x ↦ Real.sqrt (Θ (x, t)) • (Φ (x, t) ^ 3 • V (x, t))) 6
    (volume.restrict B) ^ (2 : ℝ)
  have hs := time_weighted_fifth_mixedEnergy_convection_lintegral_le
    hU hV hΦ hΘ hb hθ hM henergy
  have hfinite : (M + XW) ^ (5 / 6 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ U (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ) *
      (∫⁻ t in J, eLpNorm (fun x ↦ V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ)) ^
        (1 / 6 : ℝ) * volume J ^ (1 / 4 : ℝ) ≠ ∞ := by
    finiteness [hM.ne, hXu.ne, hXv.ne, hXw.ne, hJ.ne]
  have hr := ENNReal.toReal_mono hfinite hs
  have hm : AEStronglyMeasurable
      (fun z : ParabolicPoint ↦ Θ z * Φ z ^ 5 * ‖U z‖ * ‖V z‖ ^ (2 : ℕ))
      (volume.restrict (B ×ˢ J)) := ((hΘ.mul (hΦ.pow 5)).mul hU.norm).mul (hV.norm.pow 2)
  have heq : (∫ z : ParabolicPoint in B ×ˢ J, Θ z * Φ z ^ 5 * ‖U z‖ * ‖V z‖ ^ (2 : ℕ)) =
      (∫⁻ z : ParabolicPoint in B ×ˢ J, ENNReal.ofReal (Θ z) *
        ENNReal.ofReal (Φ z) ^ 5 * ‖U z‖ₑ * ‖V z‖ₑ ^ (2 : ℝ)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun z ↦ by positivity [(hb z), (hθ z).1]) hm]
    congr 1
    apply lintegral_congr
    intro z
    rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (hθ z).1 (pow_nonneg (hb z) _))
      (norm_nonneg _)), ENNReal.ofReal_mul (mul_nonneg (hθ z).1 (pow_nonneg (hb z) _)),
      ENNReal.ofReal_mul (hθ z).1, ENNReal.ofReal_pow (hb z),
      ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [ofReal_norm, ENNReal.rpow_ofNat]
  rw [heq]
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] using hr

end FluidSingularSets
