-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.AcceleratedEnergyAlgebra

/-!
# Exact spatial harmonic-correction energy algebra

The projected velocity is the actual sum `u + h`. Expanding its local energy
polynomial separates the original energy, twice the original momentum tested
against `h * ψ`, and the literal correction terms. Their analytic cancellation
requires the genuine harmonic-gradient, divergence and time-evolution identities;
no such cancellation is asserted merely from this polynomial equality.
-/

@[expose] public section

open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The actual squared coordinate gradient density. -/
def projectedGradientSquare (D : Fin 3 → Vec3) : ℝ := ∑ i, ∑ j, (D i j) ^ 2

/-- The original unforced tested local energy deficit. -/
def originalEnergyDeficitPolynomial (U G : Vec3) (D : Fin 3 → Vec3)
    (p ψ τ Λ : ℝ) : ℝ :=
  2 * projectedGradientSquare D * ψ - frameEnergyPolynomial U 0 G p ψ τ Λ

/-- Actual original momentum tested against a space-dependent correction `H * ψ`.
`A` and `B` are its time and spatial derivatives. -/
def harmonicCorrectionMomentumPolynomial (U H A G : Vec3) (D B : Fin 3 → Vec3)
    (p ψ τ : ℝ) : ℝ :=
  -(∑ i, U i * (A i * ψ + H i * τ)) -
    (∑ i, ∑ j, U i * U j * (B i j * ψ + H i * G j)) +
      (∑ i, ∑ j, D i j * (B i j * ψ + H i * G j)) -
        p * ((∑ i, B i i) * ψ + ∑ i, H i * G i)

/-- The projected tested energy deficit, with genuine advecting velocity `U`,
projected pressure `P`, and the actual spatial correction gradient `B`. -/
def projectedEnergyDeficitPolynomial (U H G : Vec3) (D B : Fin 3 → Vec3)
    (P ψ τ Λ : ℝ) : ℝ :=
  2 * projectedGradientSquare (D + B) * ψ -
    vec3EuclideanNorm (U + H) ^ 2 * (τ + Λ) -
      vec3EuclideanNorm (U + H) ^ 2 * (∑ i, U i * G i) -
        2 * P * (∑ i, (U i + H i) * G i) -
          2 * (∑ i, ∑ j, U j * B i j * (U i + H i)) * ψ

private theorem projectedEnergyNorm_sq (U : Vec3) :
    vec3EuclideanNorm U ^ 2 = ∑ i, U i ^ 2 := by
  rw [vec3EuclideanNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]

/-- The exact projected-energy expansion, valid before imposing any analytic equations. -/
theorem projected_relative_energy_expansion (U H A G : Vec3)
    (D B : Fin 3 → Vec3) (p P ψ τ Λ : ℝ) :
    projectedEnergyDeficitPolynomial U H G D B P ψ τ Λ -
      originalEnergyDeficitPolynomial U G D p ψ τ Λ -
        2 * harmonicCorrectionMomentumPolynomial U H A G D B p ψ τ =
      2 * (∑ i, ∑ j, D i j * B i j) * ψ +
        2 * projectedGradientSquare B * ψ -
          2 * (∑ i, U i * H i) * Λ -
            vec3EuclideanNorm H ^ 2 * (τ + Λ + ∑ i, U i * G i) +
              2 * (p - P) * (∑ i, (U i + H i) * G i) +
                2 * (∑ i, U i * A i) * ψ -
                  2 * (∑ i, ∑ j, U j * B i j * H i) * ψ -
                    2 * (∑ i, ∑ j, D i j * H i * G j) +
                      2 * p * (∑ i, B i i) * ψ := by
  simp only [projectedEnergyDeficitPolynomial, originalEnergyDeficitPolynomial,
    harmonicCorrectionMomentumPolynomial, frameEnergyPolynomial, projectedGradientSquare,
    projectedEnergyNorm_sq, Pi.add_apply, Pi.zero_apply, Fin.sum_univ_three]
  ring

end FluidSingularSets
