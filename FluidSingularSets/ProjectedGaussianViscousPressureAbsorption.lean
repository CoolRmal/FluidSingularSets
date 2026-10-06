-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedGaussianConvectivePressureAbsorption
public import FluidSingularSets.FullBallRadiusCaccioppoli

/-!
# Actual normalized harmonic viscous pressure absorption

The true harmonic spatial oscillation supplies radius power five halves.
The time measure and slice energy supply three further halves. Their product
leaves the square radius ratio, and Young absorption retains the genuine
original full-box gradient energy as the only forcing term.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The finite universal coefficient of the actual viscous Gaussian flux. -/
def projectedGaussianViscousPressureConstant : ℝ :=
  12 * (fullBallHarmonicOscillationConstant (1 / 2)).toReal *
    projectedGaussianConvectivePressureConstant

/-- The genuine viscous Gaussian coefficient is nonnegative. -/
theorem projectedGaussianViscousPressureConstant_nonneg :
    0 ≤ projectedGaussianViscousPressureConstant := by
  unfold projectedGaussianViscousPressureConstant
  exact mul_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
    projectedGaussianConvectivePressureConstant_nonneg

section Suitable

variable {Ω : Set Vec3} {I : Set ℝ} {q c r ρ δ : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

/-- Actual harmonic decay bounds the literal viscous Gaussian flux by the two true energies. -/
theorem suitable_fullBall_gaussian_viscous_pressure_iteration_bound
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r ≤ ρ) (hδ : 0 < δ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    let G := fullBallJointProjectedPressureTest u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ
    ‖∫ t in Ioo (-ρ ^ 2) 0, ∫ x in vec3Ball 0 ρ,
      ((unitBallViscousPressureCurve D t).val x -
        average (volume.restrict (vec3Ball 0 ρ)) (unitBallViscousPressureCurve D t).val) *
          G (x, t)‖ₑ ≤
      ENNReal.ofReal (projectedGaussianViscousPressureConstant * (ρ / r) ^ 2) *
        coordinateCylinderMass D 1 ^ (1 / 2 : ℝ) *
          fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0 ^ (1 / 2 : ℝ) := by
  dsimp only
  have hb := (suitable_fullBall_projected_gaussian_viscous_pressure_pairing
    hsol hbox hc hr hρ hρhalf hscale hδ hχ hbχ).2
  have ht : Ioo (-ρ ^ 2) 0 ⊆ Ioo (-1) 0 := by
    intro t htt
    have hs : ρ ^ 2 < 1 / 4 := by nlinarith
    exact ⟨by linarith only [htt.1, hs], htt.2⟩
  have hp := suitable_unitBallViscousOscillationTwoMoment_subset_le_coordinate_energy
    hsol hbox ht hρ hρhalf.le (by norm_num : (1 / 2 : ℝ) < 1)
  have hp' : unitBallViscousOscillationTwoMoment D ρ (Ioo (-ρ ^ 2) 0) ≤
      12 * fullBallHarmonicOscillationConstant (1 / 2) * ENNReal.ofReal ρ ^ (5 / 2 : ℝ) *
        coordinateCylinderMass D 1 ^ (1 / 2 : ℝ) := by
    simpa only [coordinateCylinderMass, one_pow] using hp
  have hm : fullBallProjectedIterationSliceEnergy u D p (-1) 0 c ρ 0 ≤
      ENNReal.ofReal ρ * fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0 :=
    (fullBallProjectedIterationSliceEnergy_le_radius_energy u D p (-1) 0 c 0 hρ).trans
      (mul_le_mul' le_rfl le_self_add)
  have hmr := ENNReal.rpow_le_rpow hm (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at hmr
  have htime : volume (Ioo (-ρ ^ 2) 0) ^ (1 / 2 : ℝ) = ENNReal.ofReal ρ := by
    rw [Real.volume_Ioo, sub_neg_eq_add, zero_add, ENNReal.ofReal_pow hρ.le,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hC : 0 ≤ projectedGaussianPressureFluxConstant r := by
    change 0 ≤ projectedGaussianConvectivePressureConstant / r ^ 2
    exact div_nonneg projectedGaussianConvectivePressureConstant_nonneg (sq_nonneg _)
  have hOsc : fullBallHarmonicOscillationConstant (1 / 2) ≠ ⊤ := by
    unfold fullBallHarmonicOscillationConstant
    finiteness [(volume_vec3Ball_lt_top (x := 0) (r := 1)).ne]
  have hcoeff : 12 * fullBallHarmonicOscillationConstant (1 / 2) *
      ENNReal.ofReal ρ ^ (5 / 2 : ℝ) * ENNReal.ofReal ρ *
      ENNReal.ofReal (projectedGaussianPressureFluxConstant r) *
      ENNReal.ofReal ρ ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (projectedGaussianViscousPressureConstant * (ρ / r) ^ 2) := by
    have hadd := ENNReal.rpow_add_of_nonneg (x := ENNReal.ofReal ρ)
      (5 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num)
    norm_num only [show (5 / 2 + 1 / 2 : ℝ) = 3 by norm_num, ENNReal.rpow_ofNat] at hadd
    have he : ENNReal.ofReal ρ ^ (5 / 2 : ℝ) * ENNReal.ofReal ρ *
        ENNReal.ofReal (projectedGaussianPressureFluxConstant r) *
        ENNReal.ofReal ρ ^ (1 / 2 : ℝ) =
          ENNReal.ofReal (projectedGaussianPressureFluxConstant r) * ENNReal.ofReal ρ ^ 4 := by
      calc
        _ = ENNReal.ofReal (projectedGaussianPressureFluxConstant r) * ENNReal.ofReal ρ *
            (ENNReal.ofReal ρ ^ (5 / 2 : ℝ) * ENNReal.ofReal ρ ^ (1 / 2 : ℝ)) := by ring
        _ = _ := by rw [← hadd]; ring
    have hpack : 12 * fullBallHarmonicOscillationConstant (1 / 2) *
        ENNReal.ofReal (projectedGaussianPressureFluxConstant r) * ENNReal.ofReal ρ ^ 4 =
          ENNReal.ofReal (projectedGaussianViscousPressureConstant * ρ ^ 4 / r ^ 2) := by
      have heq : projectedGaussianViscousPressureConstant * ρ ^ 4 / r ^ 2 =
          (12 * (fullBallHarmonicOscillationConstant (1 / 2)).toReal) *
            projectedGaussianPressureFluxConstant r * ρ ^ 4 := by
        unfold projectedGaussianViscousPressureConstant projectedGaussianPressureFluxConstant
          projectedGaussianConvectivePressureConstant
        ring
      rw [heq, ENNReal.ofReal_mul (mul_nonneg
          (mul_nonneg (by norm_num) ENNReal.toReal_nonneg) hC),
        ENNReal.ofReal_mul (mul_nonneg (by norm_num) ENNReal.toReal_nonneg),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
        ENNReal.ofReal_toReal hOsc, ENNReal.ofReal_pow hρ.le]
    calc
      _ = 12 * fullBallHarmonicOscillationConstant (1 / 2) *
          (ENNReal.ofReal ρ ^ (5 / 2 : ℝ) * ENNReal.ofReal ρ *
            ENNReal.ofReal (projectedGaussianPressureFluxConstant r) *
              ENNReal.ofReal ρ ^ (1 / 2 : ℝ)) := by ring
      _ = 12 * fullBallHarmonicOscillationConstant (1 / 2) *
          ENNReal.ofReal (projectedGaussianPressureFluxConstant r) *
            ENNReal.ofReal ρ ^ 4 := by rw [he]; ring
      _ = _ := hpack
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        have hρsq : ρ ^ 2 ≤ 1 := by nlinarith
        have hcst : 0 ≤ projectedGaussianViscousPressureConstant * (ρ / r) ^ 2 := by
          exact mul_nonneg projectedGaussianViscousPressureConstant_nonneg (sq_nonneg _)
        have heq : projectedGaussianViscousPressureConstant * ρ ^ 4 / r ^ 2 =
            projectedGaussianViscousPressureConstant * (ρ / r) ^ 2 * ρ ^ 2 := by
          field_simp [hr.ne']
        rw [heq]
        exact (mul_le_mul_of_nonneg_left hρsq hcst).trans_eq (mul_one _))
  apply hb.trans
  rw [htime]
  calc
    _ ≤ (12 * fullBallHarmonicOscillationConstant (1 / 2) *
        ENNReal.ofReal ρ ^ (5 / 2 : ℝ) * coordinateCylinderMass D 1 ^ (1 / 2 : ℝ)) *
        ENNReal.ofReal ρ * (ENNReal.ofReal (projectedGaussianPressureFluxConstant r) *
          (ENNReal.ofReal ρ ^ (1 / 2 : ℝ) *
            fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0 ^ (1 / 2 : ℝ))) :=
      mul_le_mul' (mul_le_mul' hp' le_rfl) (mul_le_mul' le_rfl hmr)
    _ ≤ _ := by
      convert mul_le_mul' (mul_le_mul' hcoeff le_rfl) le_rfl using 1
      ring

/-- True viscous pressure Young absorption leaves only the original coordinate-gradient source. -/
theorem suitable_fullBall_gaussian_viscous_pressure_iteration_absorption
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r ≤ ρ) (hδ : 0 < δ)
    {χ : ℝ → ℝ} (hχ : Continuous χ) (hbχ : ∀ t, ‖χ t‖ ≤ 1)
    {κ : ℝ} (hκ : 0 < κ) :
    let G := fullBallJointProjectedPressureTest u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ
    ‖∫ t in Ioo (-ρ ^ 2) 0, ∫ x in vec3Ball 0 ρ,
      ((unitBallViscousPressureCurve D t).val x -
        average (volume.restrict (vec3Ball 0 ρ)) (unitBallViscousPressureCurve D t).val) *
          G (x, t)‖ ≤
      κ * (fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0).toReal +
        projectedGaussianViscousPressureConstant ^ 2 * (ρ / r) ^ 4 / κ *
          (coordinateCylinderMass D 1).toReal := by
  dsimp only
  have hK := projectedGaussianViscousPressureConstant_nonneg
  have hC : 0 ≤ projectedGaussianViscousPressureConstant * (ρ / r) ^ 2 := by positivity
  have hI := suitable_fullBall_endpoint_iteration_quantity_lt_top hsol hbox hc hρ hρhalf
  have hD := suitable_coordinateCylinderMass_unit_lt_top hsol hbox
  have hh := ENNReal.toReal_mono (by
    finiteness [hI.ne, hD.ne])
    (suitable_fullBall_gaussian_viscous_pressure_iteration_bound
      hsol hbox hc hr hρ hρhalf hscale hδ hχ hbχ)
  simp only [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
    ← ENNReal.toReal_rpow] at hh
  have hy := half_energy_absorption
    (a := projectedGaussianViscousPressureConstant * (ρ / r) ^ 2 *
      (coordinateCylinderMass D 1).toReal ^ (1 / 2 : ℝ))
    (mul_nonneg hC (Real.rpow_nonneg ENNReal.toReal_nonneg (1 / 2)))
    (ENNReal.toReal_nonneg : 0 ≤
      (fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0).toReal) hκ
  apply hh.trans (hy.trans_eq ?_)
  have hsq : ((coordinateCylinderMass D 1).toReal ^ (1 / 2 : ℝ)) ^ 2 =
      (coordinateCylinderMass D 1).toReal := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
    norm_num
  rw [mul_pow, mul_pow, ← pow_mul, hsq]
  ring

end Suitable

end FluidSingularSets
