-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedGaussianSourceEnergy

/-!
# Genuine harmonic Gaussian Young absorption

The exact squared-radius-over-inner-radius coefficient is retained until the
linear corrected-velocity moment is absorbed. Only then is the outer radius
bounded by one, giving the squared radius ratio in the endpoint fourth-power cost.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- The genuine coefficient of the quadratic projected harmonic source. -/
def projectedGaussianHarmonicQuadraticConstant : ℝ :=
  9000 * fullBallProjectedHarmonicHessianVelocityConstant (1 / 2) *
    (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (1 / 3 : ℝ)

/-- The genuine coefficient of the linear projected harmonic source. -/
def projectedGaussianHarmonicLinearConstant : ℝ :=
  9000 * fullBallProjectedHarmonicHessianVelocityConstant (1 / 2) *
    fullBallProjectedHarmonicVelocityConstant (1 / 2) *
      (volume (vec3Ball (0 : Vec3) 1)).toReal ^ (7 / 6 : ℝ)

theorem projectedGaussianHarmonicQuadraticConstant_nonneg :
    0 ≤ projectedGaussianHarmonicQuadraticConstant := by
  unfold projectedGaussianHarmonicQuadraticConstant
  exact mul_nonneg (mul_nonneg (by norm_num)
    (fullBallProjectedHarmonicHessianVelocityConstant_nonneg (by norm_num)))
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)

theorem projectedGaussianHarmonicLinearConstant_nonneg :
    0 ≤ projectedGaussianHarmonicLinearConstant := by
  unfold projectedGaussianHarmonicLinearConstant
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (fullBallProjectedHarmonicHessianVelocityConstant_nonneg (by norm_num)))
      (fullBallProjectedHarmonicVelocityConstant_nonneg (by norm_num)))
        (Real.rpow_nonneg ENNReal.toReal_nonneg _)

/-- Honest finite extended-real data give the exact real harmonic cost formula. -/
theorem projectedGaussianHarmonicEnergyCost_toReal
    {r ρ : ℝ} (hr : 0 < r) {E X : ℝ≥0∞} (hE : E ≠ ⊤) (hX : X ≠ ⊤) :
    (projectedGaussianHarmonicEnergyCost r ρ E X).toReal = ρ ^ 2 / r *
      (projectedGaussianHarmonicQuadraticConstant * E.toReal * X.toReal ^ (1 / 2 : ℝ) +
        projectedGaussianHarmonicLinearConstant * E.toReal ^ (1 / 2 : ℝ) * X.toReal) := by
  have hW : volume (vec3Ball (0 : Vec3) 1) ≠ ⊤ := volume_vec3Ball_lt_top.ne
  have hCH : 0 ≤ fullBallProjectedHarmonicVelocityConstant (1 / 2) :=
    fullBallProjectedHarmonicVelocityConstant_nonneg (by norm_num)
  have hCD : 0 ≤ fullBallProjectedHarmonicHessianVelocityConstant (1 / 2) :=
    fullBallProjectedHarmonicHessianVelocityConstant_nonneg (by norm_num)
  have hC : 0 ≤ 9000 * fullBallProjectedHarmonicHessianVelocityConstant (1 / 2) * ρ ^ 2 / r :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCD) (sq_nonneg _)) hr.le
  have hA : volume (vec3Ball (0 : Vec3) 1) ^ (1 / 3 : ℝ) * E * X ^ (1 / 2 : ℝ) ≠ ⊤ := by
    finiteness [hW, hE, hX]
  have hB : ENNReal.ofReal (fullBallProjectedHarmonicVelocityConstant (1 / 2)) *
      volume (vec3Ball (0 : Vec3) 1) ^ (7 / 6 : ℝ) * E ^ (1 / 2 : ℝ) * X ≠ ⊤ := by
    finiteness [hW, hE, hX]
  unfold projectedGaussianHarmonicEnergyCost
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, ENNReal.toReal_add hA hB]
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hCH]
  unfold projectedGaussianHarmonicQuadraticConstant projectedGaussianHarmonicLinearConstant
  ring

/-- Young absorption preserves the squared radius ratio in the genuine source fourth power. -/
theorem projectedGaussianHarmonicEnergyCost_young
    {r ρ η : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (hscale : r ≤ ρ) (hη : 0 < η) {E X : ℝ≥0∞} (hE : E ≠ ⊤) (hX : X ≠ ⊤) :
    (projectedGaussianHarmonicEnergyCost r ρ E X).toReal ≤
      projectedGaussianHarmonicQuadraticConstant * (ρ / r) ^ 2 * E.toReal *
        X.toReal ^ (1 / 2 : ℝ) + η * E.toReal +
          projectedGaussianHarmonicLinearConstant ^ 2 / (4 * η) *
            (ρ / r) ^ 2 * X.toReal ^ 2 := by
  let A := projectedGaussianHarmonicQuadraticConstant
  let B := projectedGaussianHarmonicLinearConstant
  have hA : 0 ≤ A := projectedGaussianHarmonicQuadraticConstant_nonneg
  have hB : 0 ≤ B := projectedGaussianHarmonicLinearConstant_nonneg
  have hρone : ρ ≤ 1 := by linarith
  have hrone : r ≤ 1 := hscale.trans hρone
  have hRad : ρ ^ 2 / r ≤ (ρ / r) ^ 2 := by
    have he : ρ ^ 2 / r = (ρ / r) ^ 2 * r := by field_simp [hr.ne']
    rw [he]
    exact (mul_le_mul_of_nonneg_left hrone (sq_nonneg _)).trans_eq (mul_one _)
  have hFirst : ρ ^ 2 / r * (A * E.toReal * X.toReal ^ (1 / 2 : ℝ)) ≤
      A * (ρ / r) ^ 2 * E.toReal * X.toReal ^ (1 / 2 : ℝ) :=
    (mul_le_mul_of_nonneg_right hRad (by positivity)).trans_eq (by ring)
  have hy := projected_viscous_pressure_young
    (E := E.toReal) (M := X.toReal ^ 2) (T := (ρ / r) ^ 2) (C := B * ρ)
    ENNReal.toReal_nonneg (sq_nonneg _) (sq_nonneg _) hη
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (div_nonneg hρ.le hr.le),
    Real.sqrt_sq_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, Real.sqrt_eq_rpow] at hy
  have hSecond : ρ ^ 2 / r * (B * E.toReal ^ (1 / 2 : ℝ) * X.toReal) ≤
      η * E.toReal + B ^ 2 / (4 * η) * (ρ / r) ^ 2 * X.toReal ^ 2 := by
    calc
      _ = B * ρ * E.toReal ^ (1 / 2 : ℝ) * (ρ / r) * X.toReal := by ring
      _ ≤ η * E.toReal + (B * ρ) ^ 2 * (ρ / r) ^ 2 * X.toReal ^ 2 / (4 * η) := hy
      _ ≤ _ := by
        apply add_le_add le_rfl
        rw [mul_pow]
        have hs : ρ ^ 2 ≤ 1 := by nlinarith only [hρ.le, hρone]
        calc
          _ ≤ B ^ 2 * 1 * (ρ / r) ^ 2 * X.toReal ^ 2 / (4 * η) := by gcongr
          _ = _ := by ring
  rw [projectedGaussianHarmonicEnergyCost_toReal hr hE hX, mul_add]
  exact (add_le_add hFirst hSecond).trans_eq (by dsimp [A, B]; ring)

/-- Actual suitable data yield the genuine absorbed Gaussian Hessian integral bound. -/
theorem suitable_fullBall_projected_gaussian_harmonic_young_bound
    {Ω : Set Vec3} {I : Set ℝ} {q c r ρ δ η : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r ≤ ρ)
    (hδ : 0 < δ) (hη : 0 < η) {χ : ℝ → ℝ} (hχ : Continuous χ)
    (hbχ : ∀ t, ‖χ t‖ ≤ 1) :
    let E := (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0).toReal
    let X := (projectedGaussianOriginalSixMoment u).toReal
    ‖∫ z : ParabolicPoint, fullBallJointHarmonicError u D p (-1) 0 c
      (projectedGaussianTest r ρ δ hρ) χ z‖ ≤
      projectedGaussianHarmonicQuadraticConstant * (ρ / r) ^ 2 * E * X ^ (1 / 2 : ℝ) +
        η * E + projectedGaussianHarmonicLinearConstant ^ 2 / (4 * η) * (ρ / r) ^ 2 * X ^ 2 :=
  (suitable_fullBall_projected_gaussian_harmonic_energy_bound_real
    hsol hbox hc hr hρ hρhalf hδ hχ hbχ).trans
      (projectedGaussianHarmonicEnergyCost_young hr hρ hρhalf hscale hη
        (suitable_fullBall_normalized_projected_iteration_energy_lt_top
          hsol hbox hc hρ hρhalf).ne
        (suitable_projectedGaussianOriginalSixMoment_lt_top hsol hbox).ne)

end FluidSingularSets
