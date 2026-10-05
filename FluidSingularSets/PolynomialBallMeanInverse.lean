-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.BallBoundaryApproximation
public import CKN.Foundation.Parabolic.Integration.Average

/-!
# Actual mean-zero polynomial divergence inversion on the ball

Compact interior approximations identify the algebraic obstruction constant
with the actual ball average. Consequently every polynomial with zero ball
integral is the divergence of a genuine smooth vector field vanishing on the
sphere. No uniform inverse norm is assumed.
-/

@[expose] public section

open CKN MvPolynomial MeasureTheory Set
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- Continuous actual functions are integrable on the fixed ball. -/
theorem continuous_integrableOn_unitBall {F : Vec3 → ℝ} (hF : Continuous F) :
    Integrable F (volume.restrict (vec3Ball 0 1)) := by
  apply (hF.continuousOn.integrableOn_compact weightedClosedUnitBall_isCompact).mono_set
  intro x hx
  exact (ballBoundaryWeight_pos_of_mem_unitBall hx).le

/-- The literal actual spatial mean of a polynomial on the unit ball. -/
def unitBallPolynomialMean (f : BallPolynomial) : ℝ :=
  (volume (vec3Ball 0 1)).toReal⁻¹ * ∫ x in vec3Ball 0 1, ballPolynomialEval f x

theorem polynomialBallDivergenceField_component (v : BallPolynomial) (i : Fin 3) :
    (fun x ↦ polynomialBallDivergenceField v x i) =
      fun x ↦ ballBoundaryWeight 0 1 x * (-spatialDeriv (ballPolynomialEval v) i x) := by
  funext x
  simp [polynomialBallDivergenceField, weightedBallGradient]

/-- The actual divergence of every polynomial candidate has zero ball integral. -/
theorem polynomialBallDivergenceField_integral_divergence_zero (v : BallPolynomial) :
    (∫ x in vec3Ball 0 1,
      ∑ i : Fin 3, spatialDeriv (fun y ↦ polynomialBallDivergenceField v y i) i x) = 0 := by
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _hi
    rw [polynomialBallDivergenceField_component]
    exact weightedBallBoundary_derivative_integral_eq_zero
      (contDiff_spatialDeriv_smooth (ballPolynomialEval_contDiff v) i).neg i
  · intro i _hi
    exact continuous_integrableOn_unitBall
      (contDiff_spatialDeriv_smooth
        (contDiff_pi.mp (polynomialBallDivergenceField_contDiff v) i) i).continuous

/-- Any polynomial field equation forces its constant to be the actual ball average. -/
theorem polynomialBallDivergenceField_constant_eq_mean {f v : BallPolynomial} {c : ℝ}
    (hdiv : ∀ x : Vec3, (∑ i : Fin 3,
      spatialDeriv (fun y ↦ polynomialBallDivergenceField v y i) i x) =
        ballPolynomialEval f x - c) : c = unitBallPolynomialMean f := by
  have hi : (∫ x in vec3Ball 0 1, ballPolynomialEval f x - c) = 0 := by
    calc
      _ = ∫ x in vec3Ball 0 1,
          ∑ i : Fin 3, spatialDeriv (fun y ↦ polynomialBallDivergenceField v y i) i x := by
            apply integral_congr_ae
            exact .of_forall (fun x ↦ (hdiv x).symm)
      _ = 0 := polynomialBallDivergenceField_integral_divergence_zero v
  rw [integral_sub (continuous_integrableOn_unitBall (ballPolynomialEval_contDiff f).continuous)
    (continuous_integrableOn_unitBall continuous_const)] at hi
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul] at hi
  have hV : 0 < (volume (vec3Ball (0 : Vec3) 1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (volume_vec3Ball_pos (by norm_num)))
      volume_vec3Ball_lt_top.ne
  unfold unitBallPolynomialMean
  field_simp
  nlinarith

/-- Genuine actual polynomial divergence inversion with the actual spatial mean. -/
theorem exists_polynomial_divergence_field_mean (f : BallPolynomial) :
    ∃ v : BallPolynomial,
      (∀ x : Vec3, (∑ i : Fin 3,
        spatialDeriv (fun y ↦ polynomialBallDivergenceField v y i) i x) =
          ballPolynomialEval f x - unitBallPolynomialMean f) ∧
      ContDiff ℝ (⊤ : ℕ∞) (polynomialBallDivergenceField v) ∧
      (∀ x : Vec3, vec3EuclideanNorm x = 1 → polynomialBallDivergenceField v x = 0) := by
  obtain ⟨v, c, hdiv, hsmooth, hzero⟩ := exists_polynomial_divergence_field f
  have hc := polynomialBallDivergenceField_constant_eq_mean hdiv
  exact ⟨v, by simpa only [← hc] using hdiv, hsmooth, hzero⟩

/-- Mean-zero polynomial data have an actual smooth zero-boundary divergence inverse. -/
theorem exists_meanZero_polynomial_divergence_field {f : BallPolynomial}
    (hf : (∫ x in vec3Ball 0 1, ballPolynomialEval f x) = 0) :
    ∃ v : BallPolynomial,
      (∀ x : Vec3, (∑ i : Fin 3,
        spatialDeriv (fun y ↦ polynomialBallDivergenceField v y i) i x) =
          ballPolynomialEval f x) ∧
      ContDiff ℝ (⊤ : ℕ∞) (polynomialBallDivergenceField v) ∧
      (∀ x : Vec3, vec3EuclideanNorm x = 1 → polynomialBallDivergenceField v x = 0) := by
  obtain ⟨v, hdiv, hsmooth, hzero⟩ := exists_polynomial_divergence_field_mean f
  exact ⟨v, by simpa [unitBallPolynomialMean, hf] using hdiv, hsmooth, hzero⟩

end FluidSingularSets
