-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.DenseHilbertLifts
public import FluidSingularSets.PolynomialBallMeanDensity
public import FluidSingularSets.PolynomialBallRellich

/-!
# The actual bounded ball divergence inverse

Mean-zero coordinate polynomials are dense in the actual mean-zero ball L²
space. Their genuine zero-boundary energy inverses satisfy a degree-independent
bound. Kernel-orthogonal linear extension therefore constructs a bounded
right inverse on all mean-zero square-integrable ball data.
-/

@[expose] public section

open MeasureTheory Set CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Actual polynomial data have genuine energy inverses with a universal
linear norm bound. Both the datum and its zero mean are literal ball functions. -/
theorem exists_unitBall_polynomial_energy_lift (p : BallPolynomial) :
    ∃ v : stokesGradientEnergySpace (vec3Ball 0 1),
      unitBallMeanZeroDivergence v = meanZeroUnitBallPolynomialL2 p ∧
        ‖v‖ ≤ 2 * ‖meanZeroUnitBallPolynomialL2 p‖ := by
  let f := p - MvPolynomial.C (unitBallPolynomialMean p)
  obtain ⟨v, hv, hnorm⟩ := exists_meanZero_polynomial_stokesEnergy_inverse_bound
    (meanZeroUnitBallPolynomial_integral p)
  have hnorm' : ‖polynomialBallDivergenceEnergy v‖ ≤ 2 * ‖unitBallPolynomialL2 f‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    calc
      _ ≤ 3 * ‖unitBallPolynomialL2 f‖ ^ 2 := hnorm
      _ ≤ (2 * ‖unitBallPolynomialL2 f‖) ^ 2 := by nlinarith [sq_nonneg ‖unitBallPolynomialL2 f‖]
  refine ⟨polynomialBallDivergenceEnergy v, ?_, ?_⟩
  · apply Subtype.ext
    change stokesEnergyDivergence (vec3Ball 0 1) (polynomialBallDivergenceEnergy v) = _
    rw [meanZeroUnitBallPolynomialL2_coe]
    exact hv
  · change ‖polynomialBallDivergenceEnergy v‖ ≤
      2 * ‖(meanZeroUnitBallPolynomialL2 p : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))‖
    rw [meanZeroUnitBallPolynomialL2_coe]
    exact hnorm'

/-- The actual divergence has a bounded continuous linear right inverse on
all genuine mean-zero square-integrable ball data. -/
theorem exists_unitBall_energy_divergence_rightInverse :
    ∃ T : unitBallMeanZeroL2 →L[ℝ] stokesGradientEnergySpace (vec3Ball 0 1),
      unitBallMeanZeroDivergence.comp T = ContinuousLinearMap.id ℝ unitBallMeanZeroL2 ∧
        ‖T‖ ≤ 2 := by
  apply exists_bounded_rightInverse_of_dense_lifts unitBallMeanZeroDivergence
    meanZeroUnitBallPolynomialL2.range
    (by exact meanZeroUnitBallPolynomialL2_denseRange) (by norm_num)
  rintro ⟨g, p, rfl⟩
  exact exists_unitBall_polynomial_energy_lift p

/-- The actual bounded right inverse, chosen from the proved construction. -/
def unitBallEnergyDivergenceRightInverse :
    unitBallMeanZeroL2 →L[ℝ] stokesGradientEnergySpace (vec3Ball 0 1) :=
  exists_unitBall_energy_divergence_rightInverse.choose

/-- The constructed inverse solves the literal completed divergence equation. -/
theorem unitBallEnergyDivergenceRightInverse_apply (g : unitBallMeanZeroL2) :
    unitBallMeanZeroDivergence (unitBallEnergyDivergenceRightInverse g) = g := by
  have h := congrArg (fun A ↦ A g)
    exists_unitBall_energy_divergence_rightInverse.choose_spec.1
  exact h

/-- The inverse's actual operator norm is uniformly bounded. -/
theorem unitBallEnergyDivergenceRightInverse_norm :
    ‖unitBallEnergyDivergenceRightInverse‖ ≤ 2 :=
  exists_unitBall_energy_divergence_rightInverse.choose_spec.2

end FluidSingularSets
