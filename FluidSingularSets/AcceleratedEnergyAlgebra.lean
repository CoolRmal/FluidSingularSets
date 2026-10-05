-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import CKN.Foundation.Parabolic.Basic
public import Mathlib.Tactic

/-!
# Exact relative energy algebra in an accelerated frame

This pointwise identity expands the actual energy density after subtracting a
moving mean and adding its affine acceleration pressure. The correction is twice
the weak momentum density tested against the mean times the scalar test, plus
terms canceled by the genuine divergence and integration-by-parts identities.
The cancellation of their integrals is an analytic step, separate from this algebra.
-/

@[expose] public section

open CKN.Foundation.Parabolic

noncomputable section

namespace FluidSingularSets

/-- Literal pointwise local energy density with the scalar test derivatives supplied. -/
def frameEnergyPolynomial (U F G : Vec3) (p ψ τ Λ : ℝ) : ℝ :=
  vec3EuclideanNorm U ^ 2 * (τ + Λ) +
    (vec3EuclideanNorm U ^ 2 + 2 * p) * (∑ i, U i * G i) +
      2 * (∑ i, F i * U i) * ψ

/-- Literal weak momentum density tested against `M ψ` after the moving-coordinate
chain rule, where `A` is the acceleration and `D` the actual spatial gradient array. -/
def frameRelativeMomentumPolynomial (U M A F G : Vec3) (D : Fin 3 → Vec3)
    (p ψ τ : ℝ) : ℝ :=
  -(∑ i, U i * (A i * ψ + M i * (τ - ∑ j, M j * G j))) -
    (∑ i, ∑ j, U i * U j * M i * G j) +
      (∑ i, ∑ j, D i j * M i * G j) - p * (∑ i, M i * G i) -
        (∑ i, F i * M i) * ψ

private theorem energyPolynomial_vec3Norm_sq (U : Vec3) :
    vec3EuclideanNorm U ^ 2 = ∑ i, U i ^ 2 := by
  rw [vec3EuclideanNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]

/-- The exact relative-energy correction, with the CKN sign convention for momentum.
It holds for arbitrary vectors, arrays and scalar test values, including a force. -/
theorem accelerated_relative_energy_expansion (U M A F G Y : Vec3)
    (D : Fin 3 → Vec3) (p ψ τ Λ : ℝ) :
    frameEnergyPolynomial (U - M) F G (p + ∑ i, A i * Y i) ψ τ Λ -
      frameEnergyPolynomial U F G p ψ (τ - ∑ i, M i * G i) Λ =
      2 * frameRelativeMomentumPolynomial U M A F G D p ψ τ +
        vec3EuclideanNorm M ^ 2 * (τ + Λ + ∑ i, (U i - M i) * G i) +
          2 * (∑ i, U i * A i) * ψ -
            2 * (∑ i, ∑ j, D i j * M i * G j) -
              2 * (∑ i, U i * M i) * Λ +
                2 * (∑ i, A i * Y i) * (∑ i, (U i - M i) * G i) := by
  simp only [frameEnergyPolynomial, frameRelativeMomentumPolynomial,
    energyPolynomial_vec3Norm_sq, Pi.sub_apply, Fin.sum_univ_three]
  ring

end FluidSingularSets
