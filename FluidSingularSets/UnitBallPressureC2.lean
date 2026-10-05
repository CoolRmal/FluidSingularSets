-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallPressureHarmonic
public import FluidSingularSets.HarmonicC2

/-!
# Genuine C² representatives of the constructed unit-ball Stokes pressure

The pressure is the actual bounded-divergence-inverse construction. Its
gradient-test equation supplies distributional harmonicity, and two genuine
Weyl steps supply interior C² regularity. Literal divergence-free vector
source data discharge the gradient-test condition.
-/

@[expose] public section

open CKN MeasureTheory Set
open CKN.Foundation.Parabolic CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- Actual gradient-free Stokes forces yield a genuine interior C² pressure representative. -/
theorem exists_unitBallStokesPressure_C2_representative
    (F : StokesEnergyForce (vec3Ball 0 1))
    (hF : ∀ ψ : WeakTestFunction (vec3Ball 0 1),
      F (stokesEnergyTest (stokesScalarGradientTest ψ)) = 0) :
    ∃ H : Vec3 → ℝ, ContDiffOn ℝ (2 : ℕ∞) H (vec3Ball 0 (1 / 4)) ∧
      unitBallPressureFunction F =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))] H := by
  have hmem := unitBallPressureFunction_memLp_threeHalves F
  have hweak := unitBallStokesPressure_weaklyHarmonic F hF
  rw [← euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1)] at hmem hweak
  obtain ⟨H, hH, hae⟩ := exists_weaklyHarmonic_C2_representative
    (by norm_num : (0 : ℝ) < 1) hmem hweak
  rw [euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1 / 4)] at hH hae
  exact ⟨H, hH, hae⟩

/-- Literal divergence-free vector data yield the actual interior C² Stokes pressure. -/
theorem exists_unitBallStokesPressure_C2_representative_of_vector_source
    (u : Vec3 → Vec3) (F : StokesEnergyForce (vec3Ball 0 1))
    (hforce : ∀ φ : StokesVectorTest (vec3Ball 0 1), F (stokesEnergyTest φ) =
      ∫ x in vec3Ball 0 1, ∑ i : Fin 3, u x i * φ i x)
    (hdiv : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball 0 1 →
        (∫ x in vec3Ball 0 1, ∑ i : Fin 3, u x i * spatialDeriv ψ i x) = 0) :
    ∃ H : Vec3 → ℝ, ContDiffOn ℝ (2 : ℕ∞) H (vec3Ball 0 (1 / 4)) ∧
      unitBallPressureFunction F =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))] H := by
  have hmem := unitBallPressureFunction_memLp_threeHalves F
  have hweak := unitBallStokesPressure_weaklyHarmonic_of_vector_source u F hforce hdiv
  rw [← euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1)] at hmem hweak
  obtain ⟨H, hH, hae⟩ := exists_weaklyHarmonic_C2_representative
    (by norm_num : (0 : ℝ) < 1) hmem hweak
  rw [euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1 / 4)] at hH hae
  exact ⟨H, hH, hae⟩

end FluidSingularSets
