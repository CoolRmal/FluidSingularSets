-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.BallH1MixedEnergy
public import FluidSingularSets.ProjectedGaussianHeatError
public import FluidSingularSets.FullBallGradientMomentFinite

/-!
# Actual projected cubic and quartic pressure sources

Actual suitable weak gradients, the actual projected slice energy, and the
actual coordinate dissipation discharge every input of same-ball parabolic
Sobolev. The resulting cubic and quartic sources use the literal projected
energy of the fixed native unit-ball Stokes projection.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

section Suitable

variable {Ω : Set Vec3} {I : Set ℝ} {q c r : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

private theorem projected_pressure_source_time_subset (hr : 0 < r) (hrhalf : r < 1 / 2) :
    Ioo (0 - r ^ 2) 0 ⊆ Ioo (-1) 0 := by
  intro t ht
  have hh : r ^ 2 < 1 / 4 := by nlinarith
  exact ⟨by linarith [ht.1], ht.2⟩

private theorem projected_pressure_source_data
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0))
    (hc : c ∈ Ioo (-1) 0) (hr : 0 < r) (hrhalf : r < 1 / 2) :
    let V := fullBallProjectedVelocityAmbient u D p (-1) 0 c
    let G := fullBallProjectedVelocityDerivativeAmbient u D p (-1) 0 c
    let J := Ioo (0 - r ^ 2) 0
    AEStronglyMeasurable V (volume.restrict (vec3Ball 0 r ×ˢ J)) ∧
    AEStronglyMeasurable G (volume.restrict (vec3Ball 0 r ×ˢ J)) ∧
    (∀ᵐ t ∂volume.restrict J,
      MemLp (fun x ↦ V (x, t)) 2 (volume.restrict (vec3Ball 0 r)) ∧
      MemLp (fun x ↦ G (x, t)) 2 (volume.restrict (vec3Ball 0 r)) ∧
      ∀ j : Fin 3, HasWeakGradientOn (vec3Ball 0 r)
        (fun x ↦ V (x, t) j) (fun x ↦ G (x, t) j)) ∧
    (∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x ↦ V (x, t)) 2 (volume.restrict (vec3Ball 0 r)) ^ 2 ≤
        fullBallProjectedIterationSliceEnergy u D p (-1) 0 c r 0) := by
  let V := fullBallProjectedVelocityAmbient u D p (-1) 0 c
  let G := fullBallProjectedVelocityDerivativeAmbient u D p (-1) 0 c
  let J := Ioo (0 - r ^ 2) 0
  have hJ : J ⊆ Ioo (-1) 0 := projected_pressure_source_time_subset hr hrhalf
  have hmeasure : volume.restrict (vec3Ball 0 r ×ˢ J) ≤
      volume.restrict (vec3Ball 0 r ×ˢ Ioo (-1) 0) :=
    Measure.restrict_mono (Set.prod_mono Subset.rfl hJ) le_rfl
  have hj := fullBallProjectedVelocityAmbient_joint_memLp_two
    (B := vec3Ball 0 r) hsol hbox (by norm_num) hc hr (by linarith) subset_closure
  have hV := hj.1.aestronglyMeasurable.mono_measure hmeasure
  have hG := hj.2.aestronglyMeasurable.mono_measure hmeasure
  have hw := (fullBallProjectedVelocityAmbient_weak_gradient_slices_ae
    u D p (-1) 0 c hsol hbox hr (by linarith) (isOpen_vec3Ball 0 r)
      subset_closure).filter_mono
      (ae_mono (Measure.restrict_mono hJ le_rfl))
  have hprod : AEStronglyMeasurable V
      ((volume.restrict (vec3Ball 0 r)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict, ← volume_parabolicPoint_eq_prod]
    exact hV
  refine ⟨hV, hG, hw, ?_⟩
  filter_upwards [hprod.prodMk_right,
    fullBallProjectedIteration_native_square_le_sliceEnergy_ae u D p (-1) 0 c r 0]
      with t ht hEt
  have heq := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) ht
  norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at heq
  exact heq.trans_le (by simpa only [ENNReal.rpow_ofNat] using hEt)

/-- Actual projected same-cylinder energy controls the genuine mixed L²-L⁶ cost. -/
theorem suitable_fullBall_projected_iteration_six_square_le_energy
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0))
    (hc : c ∈ Ioo (-1) 0) (hr : 0 < r) (hrhalf : r < 1 / 2) :
    (∫⁻ t in Ioo (-r ^ 2) 0, eLpNorm
      (fun x ↦ fullBallProjectedVelocityAmbient u D p (-1) 0 c (x, t)) 6
        (volume.restrict (vec3Ball 0 r)) ^ 2) ≤
      2 * fullUnitBallH1Coefficient ^ 2 *
        (fullBallProjectedIterationSliceEnergy u D p (-1) 0 c r 0 +
          fullBallProjectedIterationDissipation u D p (-1) 0 c r 0) := by
  obtain ⟨hV, hG, hw, hM⟩ := projected_pressure_source_data hsol hbox hc hr hrhalf
  have h := ballH1Vector_backward_six_square_le hr hG hw hM
  have hd : (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (0 - r ^ 2) 0,
      ‖fullBallProjectedVelocityDerivativeAmbient u D p (-1) 0 c z‖ₑ ^ (2 : ℝ)) ≤
      fullBallProjectedIterationDissipation u D p (-1) 0 c r 0 :=
    lintegral_mono fun z ↦ gradient_enorm_square_le_coordinate _
  have hh := h.trans (mul_le_mul' le_rfl (add_le_add hd le_rfl))
  simpa only [zero_sub, add_comm] using hh

/-- Actual projected quartic sources use the genuine same-cylinder energy. -/
theorem suitable_fullBall_projected_iteration_four_square_le_energy
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0))
    (hc : c ∈ Ioo (-1) 0) (hr : 0 < r) (hrhalf : r < 1 / 2) :
    (∫⁻ t in Ioo (-r ^ 2) 0, eLpNorm
      (fun x ↦ fullBallProjectedVelocityAmbient u D p (-1) 0 c (x, t)) 4
        (volume.restrict (vec3Ball 0 r)) ^ 2) ≤
      ballH1ParabolicInterpolationConstant * ENNReal.ofReal r ^ (1 / 2 : ℝ) *
        (fullBallProjectedIterationSliceEnergy u D p (-1) 0 c r 0 +
          fullBallProjectedIterationDissipation u D p (-1) 0 c r 0) := by
  obtain ⟨hV, hG, hw, hM⟩ := projected_pressure_source_data hsol hbox hc hr hrhalf
  have hMf := suitable_fullBall_projected_iteration_sliceEnergy_lt_top hsol hbox hc hr hrhalf
  have h := ballH1Vector_backward_four_square_le_energy hr hV hG hw hMf hM
  have hd : (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (0 - r ^ 2) 0,
      ‖fullBallProjectedVelocityDerivativeAmbient u D p (-1) 0 c z‖ₑ ^ (2 : ℝ)) ≤
      fullBallProjectedIterationDissipation u D p (-1) 0 c r 0 :=
    lintegral_mono fun z ↦ gradient_enorm_square_le_coordinate _
  have hh := h.trans (mul_le_mul' le_rfl (add_le_add le_rfl hd))
  simpa only [zero_sub] using hh

/-- Actual projected cubic sources use the genuine same-cylinder energy. -/
theorem suitable_fullBall_projected_iteration_cubic_le_energy
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0))
    (hc : c ∈ Ioo (-1) 0) (hr : 0 < r) (hrhalf : r < 1 / 2) :
    (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (-r ^ 2) 0,
      ‖fullBallProjectedVelocityAmbient u D p (-1) 0 c z‖ₑ ^ (3 : ℝ)) ≤
      ballH1ParabolicInterpolationConstant * ENNReal.ofReal r ^ (1 / 2 : ℝ) *
        (fullBallProjectedIterationSliceEnergy u D p (-1) 0 c r 0 +
          fullBallProjectedIterationDissipation u D p (-1) 0 c r 0) ^ (3 / 2 : ℝ) := by
  obtain ⟨hV, hG, hw, hM⟩ := projected_pressure_source_data hsol hbox hc hr hrhalf
  have hMf := suitable_fullBall_projected_iteration_sliceEnergy_lt_top hsol hbox hc hr hrhalf
  have h := ballH1Vector_backward_cubic_le_energy hr hV hG hw hMf hM
  have hd : (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (0 - r ^ 2) 0,
      ‖fullBallProjectedVelocityDerivativeAmbient u D p (-1) 0 c z‖ₑ ^ (2 : ℝ)) ≤
      fullBallProjectedIterationDissipation u D p (-1) 0 c r 0 :=
    lintegral_mono fun z ↦ gradient_enorm_square_le_coordinate _
  have hh := h.trans
    (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (add_le_add le_rfl hd) (by norm_num)))
  simpa only [zero_sub] using hh

private theorem radius_energy_four_identity (hr : 0 < r) (E : ℝ≥0∞) :
    ENNReal.ofReal r ^ (1 / 2 : ℝ) * E =
      ENNReal.ofReal r ^ (3 / 2 : ℝ) * (ENNReal.ofReal r⁻¹ * E) := by
  have h0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  rw [ENNReal.ofReal_inv_of_pos hr, ← mul_assoc, ← ENNReal.rpow_neg_one,
    ← ENNReal.rpow_add (3 / 2) (-1) h0 ENNReal.ofReal_ne_top]
  norm_num

private theorem radius_energy_cubic_identity (hr : 0 < r) (E : ℝ≥0∞) :
    ENNReal.ofReal r ^ (1 / 2 : ℝ) * E ^ (3 / 2 : ℝ) =
      ENNReal.ofReal r ^ 2 * (ENNReal.ofReal r⁻¹ * E) ^ (3 / 2 : ℝ) := by
  have h0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_inv_of_pos hr,
    ← mul_assoc, ENNReal.inv_rpow, ← ENNReal.rpow_neg, ← ENNReal.rpow_ofNat,
    ← ENNReal.rpow_add 2 (-(3 / 2)) h0 ENNReal.ofReal_ne_top]
  norm_num

/-- Actual projected quartic pressure sources have the normalized radius power. -/
theorem suitable_fullBall_projected_iteration_four_square_le_normalized_energy
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0))
    (hc : c ∈ Ioo (-1) 0) (hr : 0 < r) (hrhalf : r < 1 / 2) :
    (∫⁻ t in Ioo (-r ^ 2) 0, eLpNorm
      (fun x ↦ fullBallProjectedVelocityAmbient u D p (-1) 0 c (x, t)) 4
        (volume.restrict (vec3Ball 0 r)) ^ 2) ≤
      ballH1ParabolicInterpolationConstant * ENNReal.ofReal r ^ (3 / 2 : ℝ) *
        fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c r 0 := by
  have h := suitable_fullBall_projected_iteration_four_square_le_energy hsol hbox hc hr hrhalf
  unfold fullBallNormalizedProjectedIterationEnergy
  rw [mul_assoc, ← radius_energy_four_identity hr, ← mul_assoc]
  exact h

/-- Actual projected cubic sources have the normalized parabolic radius square. -/
theorem suitable_fullBall_projected_iteration_cubic_le_normalized_energy
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0))
    (hc : c ∈ Ioo (-1) 0) (hr : 0 < r) (hrhalf : r < 1 / 2) :
    (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (-r ^ 2) 0,
      ‖fullBallProjectedVelocityAmbient u D p (-1) 0 c z‖ₑ ^ (3 : ℝ)) ≤
      ballH1ParabolicInterpolationConstant * ENNReal.ofReal r ^ 2 *
        fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c r 0 ^ (3 / 2 : ℝ) := by
  have h := suitable_fullBall_projected_iteration_cubic_le_energy hsol hbox hc hr hrhalf
  unfold fullBallNormalizedProjectedIterationEnergy
  rw [mul_assoc, ← radius_energy_cubic_identity hr, ← mul_assoc]
  exact h

/-- The literal Euclidean cubic projected source satisfies the genuine normalized energy bound. -/
theorem suitable_fullBall_projected_iteration_euclidean_cubic_le_normalized_energy
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0))
    (hc : c ∈ Ioo (-1) 0) (hr : 0 < r) (hrhalf : r < 1 / 2) :
    (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (-r ^ 2) 0, ENNReal.ofReal
      (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p (-1) 0 c z) ^ 3)) ≤
      27 * ballH1ParabolicInterpolationConstant * ENNReal.ofReal r ^ 2 *
        fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c r 0 ^ (3 / 2 : ℝ) := by
  have hp (z : ParabolicPoint) : ENNReal.ofReal
      (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p (-1) 0 c z) ^ 3) ≤
      27 * ‖fullBallProjectedVelocityAmbient u D p (-1) 0 c z‖ₑ ^ (3 : ℝ) := by
    have hh := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀
      (vec3EuclideanNorm_nonneg (fullBallProjectedVelocityAmbient u D p (-1) 0 c z))
      (euclideanNorm_le_three_mul_space_norm
        (fullBallProjectedVelocityAmbient u D p (-1) 0 c z)) 3)
    rw [mul_pow, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 ^ 3)] at hh
    simpa only [show (3 : ℝ) ^ 3 = 27 by norm_num, ENNReal.ofReal_ofNat,
      ENNReal.rpow_ofNat, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)] using hh
  calc
    _ ≤ ∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (-r ^ 2) 0,
        27 * ‖fullBallProjectedVelocityAmbient u D p (-1) 0 c z‖ₑ ^ (3 : ℝ) :=
      lintegral_mono hp
    _ = 27 * ∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (-r ^ 2) 0,
        ‖fullBallProjectedVelocityAmbient u D p (-1) 0 c z‖ₑ ^ (3 : ℝ) :=
      lintegral_const_mul' _ _ (by norm_num)
    _ ≤ _ := (mul_le_mul' le_rfl
      (suitable_fullBall_projected_iteration_cubic_le_normalized_energy
        hsol hbox hc hr hrhalf)).trans_eq (by ring)

end Suitable

end FluidSingularSets
