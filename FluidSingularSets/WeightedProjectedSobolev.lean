-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.WeightedProjectedConvection

/-!
# Genuine weighted Sobolev control with the unweighted cutoff error

The actual weak cutoff product estimate controls its mixed L²/L⁶ cost by the
sixth-weighted gradient square integral and the unweighted velocity square
integral. The latter bound follows from the actual cutoff being between zero
and one, without comparing it to the cubed-cutoff energy.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual weak weighted Sobolev estimate retains an unweighted cutoff error. -/
theorem integrated_cutoff_cube_sobolev_unweighted_error
    {B : Set Vec3} {J : Set ℝ} (hB : IsOpen B)
    {V : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3} {φ : Vec3 → ℝ}
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J)))
    (hD : AEStronglyMeasurable D (volume.restrict (B ×ˢ J)))
    (hslices : ∀ᵐ t ∂volume.restrict J,
      MemLp (fun x ↦ V (x, t)) 2 (volume.restrict B) ∧
      MemLp (fun x ↦ D (x, t)) 2 (volume.restrict B) ∧
      ∀ i : Fin 3, HasWeakGradientOn B (fun x ↦ V (x, t) i) (fun x ↦ D (x, t) i))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ B)
    (hunit : tsupport φ ⊆ euclideanBall 0 1) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L) :
    (∫⁻ t in J, eLpNorm (fun x ↦ φ x ^ 3 • V (x, t)) 6
      (volume.restrict B) ^ (2 : ℝ)) ≤
      2 * (3 * localSobolevConstant) ^ 2 *
        ((∫⁻ z : ParabolicPoint in B ×ˢ J, ‖φ z.1 ^ 3 • D z‖ₑ ^ (2 : ℝ)) +
          ENNReal.ofReal (3 * L + 32) ^ 2 *
            ∫⁻ z : ParabolicPoint in B ×ˢ J, ‖V z‖ₑ ^ (2 : ℝ)) := by
  have herror : (∫⁻ z : ParabolicPoint in B ×ˢ J, ‖φ z.1 ^ 2 • V z‖ₑ ^ (2 : ℝ)) ≤
      ∫⁻ z : ParabolicPoint in B ×ˢ J, ‖V z‖ₑ ^ (2 : ℝ) :=
    lintegral_mono fun z ↦ ENNReal.rpow_le_rpow
      (cutoff_power_smul_enorm_le (V z) (hb z.1).1 (hb z.1).2 2) (by norm_num)
  exact (integrated_cutoff_cube_vector_sobolev hB hV hD hslices
    hφ hc hs hunit hb hL hgrad).trans
      (mul_le_mul' le_rfl (add_le_add le_rfl (mul_le_mul' le_rfl herror)))

/-- A cutoff gradient budget at least one gives an explicit quadratic unweighted error. -/
theorem integrated_cutoff_cube_sobolev_quadratic_error
    {B : Set Vec3} {J : Set ℝ} (hB : IsOpen B)
    {V : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3} {φ : Vec3 → ℝ}
    (hV : AEStronglyMeasurable V (volume.restrict (B ×ˢ J)))
    (hD : AEStronglyMeasurable D (volume.restrict (B ×ˢ J)))
    (hslices : ∀ᵐ t ∂volume.restrict J,
      MemLp (fun x ↦ V (x, t)) 2 (volume.restrict B) ∧
      MemLp (fun x ↦ D (x, t)) 2 (volume.restrict B) ∧
      ∀ i : Fin 3, HasWeakGradientOn B (fun x ↦ V (x, t) i) (fun x ↦ D (x, t) i))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ B)
    (hunit : tsupport φ ⊆ euclideanBall 0 1) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 1 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L) :
    (∫⁻ t in J, eLpNorm (fun x ↦ φ x ^ 3 • V (x, t)) 6
      (volume.restrict B) ^ (2 : ℝ)) ≤
      2 * (3 * localSobolevConstant) ^ 2 *
        ((∫⁻ z : ParabolicPoint in B ×ˢ J, ‖φ z.1 ^ 3 • D z‖ₑ ^ (2 : ℝ)) +
          1225 * ENNReal.ofReal L ^ 2 *
            ∫⁻ z : ParabolicPoint in B ×ˢ J, ‖V z‖ₑ ^ (2 : ℝ)) := by
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hnum : ENNReal.ofReal (3 * L + 32) ^ 2 ≤ 1225 * ENNReal.ofReal L ^ 2 := by
    have hh := pow_le_pow_left'
      (ENNReal.ofReal_le_ofReal (show 3 * L + 32 ≤ 35 * L by linarith)) 2
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 35), mul_pow] at hh
    norm_num only [ENNReal.ofReal_ofNat, Nat.cast_ofNat, Nat.reducePow] at hh
    convert hh using 1
  exact (integrated_cutoff_cube_sobolev_unweighted_error hB hV hD hslices
    hφ hc hs hunit hb hL0 hgrad).trans
      (mul_le_mul' le_rfl (add_le_add le_rfl (mul_le_mul' hnum le_rfl)))

/-- Actual suitable weak gradients supply the weighted mixed estimate and quadratic error. -/
theorem suitable_integrated_cutoff_cube_sobolev_quadratic_error
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    {B : Set Vec3} (hB : IsOpen B) (hbox : localBox Ω I B J) {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ B)
    (hunit : tsupport φ ⊆ euclideanBall 0 1) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 1 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L) :
    (∫⁻ t in J, eLpNorm (fun x ↦ φ x ^ 3 • u (x, t)) 6
      (volume.restrict B) ^ (2 : ℝ)) ≤
      2 * (3 * localSobolevConstant) ^ 2 *
        ((∫⁻ z : ParabolicPoint in B ×ˢ J, ‖φ z.1 ^ 3 • D z‖ₑ ^ (2 : ℝ)) +
          1225 * ENNReal.ofReal L ^ 2 *
            ∫⁻ z : ParabolicPoint in B ×ˢ J, ‖u z‖ₑ ^ (2 : ℝ)) := by
  apply integrated_cutoff_cube_sobolev_quadratic_error hB
    (hsol.toData.aestronglyMeasurable_velocity hbox)
    (hsol.toData.aestronglyMeasurable_gradient hbox) _ hφ hc hs hunit hb hL hgrad
  have hw := ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)
  filter_upwards [slice_memLp_ae_of_sws hsol hbox, hw] with t ht hwt
  exact ⟨ht.1, ht.2, hwt⟩

end FluidSingularSets
