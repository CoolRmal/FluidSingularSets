-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallProjectedTimeEnergy
public import FluidSingularSets.FullBallProjectedSignedErrors
public import FluidSingularSets.ProjectedCylinderCutoff

/-!
# Literal cutoff right hand side for full-ball projected energy

Actual spatial and time derivatives of a separated sixth-power test identify
all four true error families: the time ramp, spatial Laplacian, convection,
and pressure and harmonic pairings. This is the exact density used by the
source-derived local energy inequality.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The literal separated sixth-power space-time test. -/
def fullBallSeparatedCutoffTest (φ : Vec3 → ℝ) (θ : ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  φ z.1 ^ 6 * θ z.2

/-- The actual separated test has its literal spatial first derivative. -/
theorem fullBallSeparatedCutoffTest_spatialPartial {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (θ : ℝ → ℝ) (j : Fin 3) (z : Vec3 × ℝ) :
    spatialPartial (fullBallSeparatedCutoffTest φ θ) j z =
      spatialDeriv (fun x ↦ φ x ^ 6) j z.1 * θ z.2 :=
  spatialPartial_mul_time ((hφ.comp contDiff_fst).pow 6) j z

/-- The actual separated test has its literal spatial second derivative. -/
theorem fullBallSeparatedCutoffTest_spatialSecondPartial {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (θ : ℝ → ℝ) (i j : Fin 3) (z : Vec3 × ℝ) :
    spatialSecondPartial (fullBallSeparatedCutoffTest φ θ) i j z =
      mixedSecond (fun x ↦ φ x ^ 6) j i z.1 * θ z.2 :=
  spatialSecondPartial_mul_time ((hφ.comp contDiff_fst).pow 6) i j z

/-- The actual separated test has its literal time derivative. -/
theorem fullBallSeparatedCutoffTest_timePartial (φ : Vec3 → ℝ)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (z : Vec3 × ℝ) :
    timePartial (fullBallSeparatedCutoffTest φ θ) z = φ z.1 ^ 6 * deriv θ z.2 := by
  exact ((hθ.differentiable (by simp)).differentiableAt.hasDerivAt.const_mul
    (φ z.1 ^ 6)).deriv

/-- The exact projected cutoff right hand side is its true derivative and pairing families. -/
theorem fullBallProjectedRhsDensity_separated_cutoff
    (ρ : ℝ) (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (z : fullBallCompactInterior ρ × ℝ) :
    fullBallProjectedRhsDensity ρ u D p a b c (fullBallSeparatedCutoffTest φ θ) z =
      vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c (z.1.1, z.2)) ^ 2 *
        φ z.1.1 ^ 6 * deriv θ z.2 +
      vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c (z.1.1, z.2)) ^ 2 *
        spatialLaplacian (fun x ↦ φ x ^ 6) z.1.1 * θ z.2 +
      vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c (z.1.1, z.2)) ^ 2 *
        (∑ j : Fin 3, u (z.1.1, z.2) j *
          spatialDeriv (fun x ↦ φ x ^ 6) j z.1.1) * θ z.2 +
      2 * (p (z.1.1, z.2) - fullBallProjectedMomentumPressure u D p z.2 z.1.1) *
        (∑ j : Fin 3, fullBallProjectedVelocityAmbient u D p a b c (z.1.1, z.2) j *
          spatialDeriv (fun x ↦ φ x ^ 6) j z.1.1) * θ z.2 +
      2 * (∑ i : Fin 3, ∑ j : Fin 3, u (z.1.1, z.2) j *
        fullBallProjectedHarmonicDerivativeAmbient u D p a b c (z.1.1, z.2) i j *
          fullBallProjectedVelocityAmbient u D p a b c (z.1.1, z.2) i) *
        φ z.1.1 ^ 6 * θ z.2 := by
  let w : Vec3 × ℝ := (z.1.1, z.2)
  let U := u ((z.1.1, z.2) : ParabolicPoint)
  let H := fullBallProjectedHarmonicGradientAmbient u D p a b c (z.1.1, z.2)
  let W := D ((z.1.1, z.2) : ParabolicPoint)
  let B := fullBallProjectedHarmonicDerivativeAmbient u D p a b c (z.1.1, z.2)
  let P := p ((z.1.1, z.2) : ParabolicPoint) -
    fullBallProjectedMomentumPressure u D p z.2 z.1.1
  have hG : (fun j ↦ spatialPartial (fullBallSeparatedCutoffTest φ θ) j w) =
      (fun j ↦ spatialDeriv (fun x ↦ φ x ^ 6) j z.1.1 * θ z.2) := by
    funext j
    exact fullBallSeparatedCutoffTest_spatialPartial hφ θ j w
  have hΛ : (∑ j, spatialSecondPartial (fullBallSeparatedCutoffTest φ θ) j j w) =
      spatialLaplacian (fun x ↦ φ x ^ 6) z.1.1 * θ z.2 := by
    simp_rw [fullBallSeparatedCutoffTest_spatialSecondPartial hφ]
    exact (Finset.sum_mul _ _ _).symm
  have hτ := fullBallSeparatedCutoffTest_timePartial φ hθ w
  change 2 * projectedGradientSquare (W + B) * (φ z.1.1 ^ 6 * θ z.2) -
    projectedEnergyDeficitPolynomial U H
      (fun j ↦ spatialPartial (fullBallSeparatedCutoffTest φ θ) j w) W B P
      (φ z.1.1 ^ 6 * θ z.2) (timePartial (fullBallSeparatedCutoffTest φ θ) w)
      (∑ j, spatialSecondPartial (fullBallSeparatedCutoffTest φ θ) j j w) =
    vec3EuclideanNorm (U + H) ^ 2 * φ z.1.1 ^ 6 * deriv θ z.2 +
    vec3EuclideanNorm (U + H) ^ 2 * spatialLaplacian (fun x ↦ φ x ^ 6) z.1.1 * θ z.2 +
    vec3EuclideanNorm (U + H) ^ 2 *
      (∑ j : Fin 3, U j * spatialDeriv (fun x ↦ φ x ^ 6) j z.1.1) * θ z.2 +
    2 * P * (∑ j : Fin 3, (U + H) j *
      spatialDeriv (fun x ↦ φ x ^ 6) j z.1.1) * θ z.2 +
    2 * (∑ i : Fin 3, ∑ j : Fin 3, U j * B i j * (U + H) i) * φ z.1.1 ^ 6 * θ z.2
  rw [hG, hΛ, hτ]
  simp only [projectedEnergyDeficitPolynomial, Pi.add_apply, Fin.sum_univ_three]
  ring

end FluidSingularSets
