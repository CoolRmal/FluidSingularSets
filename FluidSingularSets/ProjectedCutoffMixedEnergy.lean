-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedWeightedConvection

/-!
# Actual mixed energy of the cubed cutoff velocity

Tonelli integrates the genuine weak Sobolev estimate on spatial slices. The
weighted mixed L²/L⁶ norm is controlled by the actual weighted gradient and
velocity square moments, including the explicit cutoff derivative coefficient.
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

/-- Actual joint square data gives a measurable spatial square-moment curve. -/
theorem aemeasurable_spatial_square_moment {E : Type*} [NormedAddCommGroup E]
    {B : Set Vec3} {J : Set ℝ} {F : ParabolicPoint → E}
    (hF : AEStronglyMeasurable F (volume.restrict (B ×ˢ J))) :
    AEMeasurable (fun t ↦ ∫⁻ x in B, ‖F (x, t)‖ₑ ^ (2 : ℝ)) (volume.restrict J) := by
  have hp : AEStronglyMeasurable F ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hF
  exact (hp.enorm.pow_const (2 : ℝ)).lintegral_prod_left'

/-- Tonelli identifies the actual iterated spatial square moment with the joint moment. -/
theorem lintegral_spatial_square_moment_eq_joint {E : Type*} [NormedAddCommGroup E]
    {B : Set Vec3} {J : Set ℝ} {F : ParabolicPoint → E}
    (hF : AEStronglyMeasurable F (volume.restrict (B ×ˢ J))) :
    (∫⁻ t in J, ∫⁻ x in B, ‖F (x, t)‖ₑ ^ (2 : ℝ)) =
      ∫⁻ z : ParabolicPoint in B ×ˢ J, ‖F z‖ₑ ^ (2 : ℝ) := by
  have hp : AEStronglyMeasurable F ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hF
  rw [show (volume : Measure ParabolicPoint).restrict (B ×ˢ J) =
      (volume.restrict B).prod (volume.restrict J) by
    rw [Measure.prod_restrict, volume_parabolicPoint_eq_prod]]
  change _ = ∫⁻ z : Vec3 × ℝ, ‖F z‖ₑ ^ (2 : ℝ)
    ∂(volume.restrict B).prod (volume.restrict J)
  rw [lintegral_prod_symm _ (hp.enorm.pow_const (2 : ℝ))]

/-- The genuine weak Sobolev coefficient is finite. -/
theorem cutoff_mixed_sobolev_coefficient_ne_top :
    2 * (3 * localSobolevConstant) ^ 2 ≠ ∞ := by
  unfold localSobolevConstant
  finiteness

/-- Integrating the true weak cutoff estimate gives actual weighted mixed energy control. -/
theorem integrated_cutoff_cube_vector_sobolev
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
            ∫⁻ z : ParabolicPoint in B ×ˢ J, ‖φ z.1 ^ 2 • V z‖ₑ ^ (2 : ℝ)) := by
  have hDw : AEStronglyMeasurable (fun z : ParabolicPoint ↦ φ z.1 ^ 3 • D z)
      (volume.restrict (B ×ˢ J)) :=
    ((hφ.pow 3).continuous.comp continuous_fst).aestronglyMeasurable.smul hD
  have hVw : AEStronglyMeasurable (fun z : ParabolicPoint ↦ φ z.1 ^ 2 • V z)
      (volume.restrict (B ×ˢ J)) :=
    ((hφ.pow 2).continuous.comp continuous_fst).aestronglyMeasurable.smul hV
  have hpoint : ∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x ↦ φ x ^ 3 • V (x, t)) 6 (volume.restrict B) ^ (2 : ℝ) ≤
        2 * (3 * localSobolevConstant) ^ 2 *
          ((∫⁻ x in B, ‖φ x ^ 3 • D (x, t)‖ₑ ^ (2 : ℝ)) +
            ENNReal.ofReal (3 * L + 32) ^ 2 * ∫⁻ x in B, ‖φ x ^ 2 • V (x, t)‖ₑ ^
              (2 : ℝ)) := by
    filter_upwards [hslices] with t ht
    exact cutoff_cube_vector_sobolev_six_squared hB ht.1 ht.2.1 ht.2.2
      hφ hc hs hunit hb hL hgrad
  have hmV : AEMeasurable (fun t ↦ ENNReal.ofReal (3 * L + 32) ^ 2 *
      ∫⁻ x in B, ‖φ x ^ 2 • V (x, t)‖ₑ ^ (2 : ℝ)) (volume.restrict J) :=
    aemeasurable_const.mul (aemeasurable_spatial_square_moment hVw)
  have hDmom : (∫⁻ t in J, ∫⁻ x in B, ‖φ x ^ 3 • D (x, t)‖ₑ ^ (2 : ℝ)) =
      ∫⁻ z : ParabolicPoint in B ×ˢ J, ‖φ z.1 ^ 3 • D z‖ₑ ^ (2 : ℝ) :=
    lintegral_spatial_square_moment_eq_joint hDw
  have hVmom : (∫⁻ t in J, ∫⁻ x in B, ‖φ x ^ 2 • V (x, t)‖ₑ ^ (2 : ℝ)) =
      ∫⁻ z : ParabolicPoint in B ×ˢ J, ‖φ z.1 ^ 2 • V z‖ₑ ^ (2 : ℝ) :=
    lintegral_spatial_square_moment_eq_joint hVw
  apply (lintegral_mono_ae hpoint).trans_eq
  rw [lintegral_const_mul' _ _ cutoff_mixed_sobolev_coefficient_ne_top,
    lintegral_add_right' _ hmV, lintegral_const_mul' _ _ (by finiteness), hDmom, hVmom]

/-- Suitability supplies the genuine joint data and weak slices of the weighted mixed estimate. -/
theorem suitable_integrated_cutoff_cube_sobolev
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    {B : Set Vec3} (hB : IsOpen B) (hbox : localBox Ω I B J) {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ B)
    (hunit : tsupport φ ⊆ euclideanBall 0 1) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L) :
    (∫⁻ t in J, eLpNorm (fun x ↦ φ x ^ 3 • u (x, t)) 6
      (volume.restrict B) ^ (2 : ℝ)) ≤
      2 * (3 * localSobolevConstant) ^ 2 *
        ((∫⁻ z : ParabolicPoint in B ×ˢ J, ‖φ z.1 ^ 3 • D z‖ₑ ^ (2 : ℝ)) +
          ENNReal.ofReal (3 * L + 32) ^ 2 *
            ∫⁻ z : ParabolicPoint in B ×ˢ J, ‖φ z.1 ^ 2 • u z‖ₑ ^ (2 : ℝ)) := by
  apply integrated_cutoff_cube_vector_sobolev hB
    (hsol.toData.aestronglyMeasurable_velocity hbox)
    (hsol.toData.aestronglyMeasurable_gradient hbox) _ hφ hc hs hunit hb hL hgrad
  have hw := ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)
  filter_upwards [slice_memLp_ae_of_sws hsol hbox, hw] with t ht hwt
  exact ⟨ht.1, ht.2, hwt⟩

/-- A genuine cutoff between zero and one decreases every actual vector norm. -/
theorem cutoff_power_smul_enorm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    ‖a ^ n • v‖ₑ ≤ ‖v‖ₑ := by
  rw [enorm_smul, Real.enorm_of_nonneg (pow_nonneg ha n)]
  have hb : ENNReal.ofReal (a ^ n) ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal (pow_le_one₀ ha ha1 : a ^ n ≤ 1)
  exact (mul_le_mul' hb (le_refl _)).trans_eq (one_mul _)

/-- Actual suitable finite energy makes the genuine cubed-cutoff mixed norm finite. -/
theorem suitable_integrated_cutoff_cube_sobolev_lt_top
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    {B : Set Vec3} (hB : IsOpen B) (hbox : localBox Ω I B J) {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ B)
    (hunit : tsupport φ ⊆ euclideanBall 0 1) (hb : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {L : ℝ} (hL : 0 ≤ L) (hgrad : ∀ x, ‖classicalGradient φ x‖ ≤ L) :
    (∫⁻ t in J, eLpNorm (fun x ↦ φ x ^ 3 • u (x, t)) 6
      (volume.restrict B) ^ (2 : ℝ)) < ∞ := by
  have hDE : (∫⁻ z : ParabolicPoint in B ×ˢ J, ‖D z‖ₑ ^ (2 : ℝ)) < ∞ :=
    (lintegral_mono (fun _ ↦ le_add_left le_rfl)).trans_lt
      (hsol.toData.energy_lintegral_lt_top hbox)
  have hUE : (∫⁻ z : ParabolicPoint in B ×ˢ J, ‖u z‖ₑ ^ (2 : ℝ)) < ∞ :=
    (lintegral_mono (fun _ ↦ le_add_right le_rfl)).trans_lt
      (hsol.toData.energy_lintegral_lt_top hbox)
  have hDw : (∫⁻ z : ParabolicPoint in B ×ˢ J, ‖φ z.1 ^ 3 • D z‖ₑ ^ (2 : ℝ)) < ∞ :=
    (lintegral_mono (fun z ↦ ENNReal.rpow_le_rpow
      (cutoff_power_smul_enorm_le (D z) (hb z.1).1 (hb z.1).2 3) (by norm_num))).trans_lt hDE
  have hUw : (∫⁻ z : ParabolicPoint in B ×ˢ J, ‖φ z.1 ^ 2 • u z‖ₑ ^ (2 : ℝ)) < ∞ :=
    (lintegral_mono (fun z ↦ ENNReal.rpow_le_rpow
      (cutoff_power_smul_enorm_le (u z) (hb z.1).1 (hb z.1).2 2) (by norm_num))).trans_lt hUE
  apply (suitable_integrated_cutoff_cube_sobolev hsol hB hbox hφ hc hs hunit hb hL hgrad).trans_lt
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr cutoff_mixed_sobolev_coefficient_ne_top)
    (ENNReal.add_lt_top.mpr ⟨hDw, ENNReal.mul_lt_top (by finiteness) hUw⟩)

/-- The actual canonical cutoff gives an explicit radius-gap mixed energy estimate. -/
theorem suitable_canonical_cutoff_mixed_energy
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p f)
    {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hρσ : ρ < σ) (hσ : σ ≤ 1)
    (hbox : localBox Ω I (euclideanBall 0 σ) J) :
    (∫⁻ t in J, eLpNorm (fun x ↦ canonicalBallCutoff 0 ρ σ x ^ 3 • u (x, t)) 6
      (volume.restrict (euclideanBall 0 σ)) ^ (2 : ℝ)) ≤
      2 * (3 * localSobolevConstant) ^ 2 *
        ((∫⁻ z : ParabolicPoint in euclideanBall 0 σ ×ˢ J,
            ‖canonicalBallCutoff 0 ρ σ z.1 ^ 3 • D z‖ₑ ^ (2 : ℝ)) +
          ENNReal.ofReal (96 / (σ - ρ) + 32) ^ 2 *
            ∫⁻ z : ParabolicPoint in euclideanBall 0 σ ×ˢ J,
              ‖canonicalBallCutoff 0 ρ σ z.1 ^ 2 • u z‖ₑ ^ (2 : ℝ)) := by
  have hs := canonicalBallCutoff_tsupport_subset_outer (x₀ := (0 : Vec3)) hρ hρσ
  have hunit : tsupport (canonicalBallCutoff (0 : Vec3) ρ σ) ⊆ euclideanBall 0 1 := by
    apply hs.trans
    intro x hx
    change euclideanSqDist x 0 < σ ^ 2 at hx
    change euclideanSqDist x 0 < 1 ^ (2 : ℕ)
    exact hx.trans_le (pow_le_pow_left₀ (hρ.trans hρσ.le) hσ 2)
  have hgrad (x : Vec3) :
      ‖classicalGradient (canonicalBallCutoff (0 : Vec3) ρ σ) x‖ ≤ 32 / (σ - ρ) :=
    (pi_norm_le_vecEuclideanNorm _).trans (canonicalBallCutoff_gradient_bound hρ hρσ x)
  rw [show (96 : ℝ) / (σ - ρ) = 3 * (32 / (σ - ρ)) by ring]
  exact suitable_integrated_cutoff_cube_sobolev hsol (isOpen_euclideanBall _ _) hbox
    (canonicalBallCutoff_smooth _ hρ hρσ) (canonicalBallCutoff_hasCompactSupport hρ hρσ)
    hs hunit (fun x ↦ ⟨canonicalBallCutoff_nonneg _ _ _ x,
      canonicalBallCutoff_le_one _ _ _ x⟩) (by positivity [sub_pos.mpr hρσ]) hgrad

end FluidSingularSets
