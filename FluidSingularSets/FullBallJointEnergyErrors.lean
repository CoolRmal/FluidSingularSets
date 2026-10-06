-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallJointPressureTest
public import FluidSingularSets.FullBallNativeEnergyRhs
public import FluidSingularSets.FullBallCutoffSourceErrors

/-!
# Genuine error families for joint projected-energy tests

The backward heat operator is retained as one signed error, preserving its
cancellation. The other actual error families are the convective flux,
mean-canceling pressure flux, and harmonic Hessian term.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The true signed backward heat-operator error, before taking any absolute value. -/
def fullBallJointHeatError
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 × ℝ → ℝ) (χ : ℝ → ℝ)
    (z : ParabolicPoint) : ℝ :=
  vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z) ^ 2 *
    (timePartial ψ z + ∑ j, spatialSecondPartial ψ j j z) * χ z.2

/-- The true joint-test convection with the original advecting velocity. -/
def fullBallJointConvectionError
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 × ℝ → ℝ) (χ : ℝ → ℝ)
    (z : ParabolicPoint) : ℝ :=
  vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p a b c z) ^ 2 *
    (∑ j : Fin 3, u z j * spatialPartial ψ j z) * χ z.2

/-- The true projected pressure paired against the actual joint spatial gradient. -/
def fullBallJointPressureError
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 × ℝ → ℝ) (χ : ℝ → ℝ)
    (z : ParabolicPoint) : ℝ :=
  (p z - fullBallProjectedMomentumPressure u D p z.2 z.1) *
    fullBallJointProjectedPressureTest u D p a b c ψ χ z

/-- The nine literal harmonic Hessian errors of the joint test. -/
def fullBallJointHarmonicError
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 × ℝ → ℝ) (χ : ℝ → ℝ)
    (z : ParabolicPoint) : ℝ :=
  (∑ i : Fin 3, ∑ j : Fin 3, u z j *
    fullBallProjectedHarmonicDerivativeAmbient u D p a b c z i j *
      fullBallProjectedVelocityAmbient u D p a b c z i) * ψ z * χ z.2

/-- The genuine native RHS is exactly the four actual joint-test error families. -/
theorem fullBallNativeProjectedRhsDensity_joint_errors_eq
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 × ℝ → ℝ) (χ : ℝ → ℝ)
    (z : ParabolicPoint) :
    fullBallNativeProjectedRhsDensity u D p a b c ψ z * χ z.2 =
      fullBallJointHeatError u D p a b c ψ χ z +
      fullBallJointConvectionError u D p a b c ψ χ z +
      2 * fullBallJointPressureError u D p a b c ψ χ z +
      2 * fullBallJointHarmonicError u D p a b c ψ χ z := by
  simp only [fullBallNativeProjectedRhsDensity, fullBallJointHeatError,
    fullBallJointConvectionError, fullBallJointPressureError, fullBallJointHarmonicError,
    fullBallJointProjectedPressureTest, projectedEnergyDeficitPolynomial,
    fullBallProjectedVelocityAmbient, fullBallProjectedVelocityDerivativeAmbient,
    Fin.sum_univ_three, Pi.add_apply]
  ring

/-- Each genuine joint-test error vanishes off the actual test support. -/
theorem fullBallJointEnergyErrors_zero_off_tsupport
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c : ℝ) (ψ : Vec3 × ℝ → ℝ) (χ : ℝ → ℝ)
    (z : Vec3 × ℝ) (hz : z ∉ tsupport ψ) :
    fullBallJointHeatError u D p a b c ψ χ z = 0 ∧
      fullBallJointConvectionError u D p a b c ψ χ z = 0 ∧
      fullBallJointPressureError u D p a b c ψ χ z = 0 ∧
      fullBallJointHarmonicError u D p a b c ψ χ z = 0 := by
  have hψ := image_eq_zero_of_notMem_tsupport hz
  have hτ := timePartial_eq_zero_off_tsupport hz
  have hG (j : Fin 3) := spatialPartial_eq_zero_off_tsupport hz j
  have hΛ (j : Fin 3) := spatialSecondPartial_eq_zero_off_tsupport hz j j
  simp only [fullBallJointHeatError, fullBallJointConvectionError,
    fullBallJointPressureError, fullBallJointHarmonicError, fullBallJointProjectedPressureTest,
    hψ, hτ, hG, hΛ, mul_zero, zero_mul, add_zero, Finset.sum_const_zero, and_self]

end FluidSingularSets
