-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StokesVectorPressureC2
public import FluidSingularSets.UnitBallPressureBounds

/-!
# Actual harmonic pressure gradient and Hessian bounds from L² vector data

The source functional is genuinely constructed from the energy velocity map.
The bounds combine its proved norm estimate with the two actual Weyl estimates
for the constructed pressure, with constants independent of the vector data.
-/

@[expose] public section

open CKN MeasureTheory Set
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The true unit-ball vector-source to interior-pressure-gradient constant. -/
def stokesVectorPressureGradientConstant : ℝ :=
  unitBallPressureGradientConstant *
    (3 * (stokesTestPoincareConstant (vec3Ball (0 : Vec3) 1)).toReal)

theorem stokesVectorPressureGradientConstant_nonneg :
    0 ≤ stokesVectorPressureGradientConstant :=
  mul_nonneg unitBallPressureGradientConstant_nonneg
    (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)

/-- The true unit-ball vector-source to interior-pressure-Hessian constant. -/
def stokesVectorPressureHessianConstant : ℝ :=
  unitBallPressureHessianConstant *
    (3 * (stokesTestPoincareConstant (vec3Ball (0 : Vec3) 1)).toReal)

theorem stokesVectorPressureHessianConstant_nonneg :
    0 ≤ stokesVectorPressureHessianConstant :=
  mul_nonneg unitBallPressureHessianConstant_nonneg
    (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)

/-- Genuine divergence-free L² vector data give actual bounded pressure derivatives. -/
theorem exists_stokesVectorPressure_C2_and_derivative_bounds
    (u : Lp Vec3 2 (volume.restrict (vec3Ball 0 1)))
    (hdiv : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball 0 1 →
        (∫ x in vec3Ball 0 1, ∑ i : Fin 3, u x i * spatialDeriv ψ i x) = 0) :
    ∃ H : Vec3 → ℝ, ContDiffOn ℝ (2 : ℕ∞) H (vec3Ball 0 (1 / 4)) ∧
      unitBallPressureFunction (stokesVectorForce (vec3Ball 0 1) u)
        =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))] H ∧
      (∀ x ∈ vec3Ball 0 (1 / 4), vec3EuclideanNorm (classicalGradient H x) ≤
        stokesVectorPressureGradientConstant * ‖u‖) ∧
      (∀ x ∈ vec3Ball 0 (1 / 8), ∀ i j : Fin 3,
        |mixedSecond H i j x| ≤ stokesVectorPressureHessianConstant * ‖u‖) := by
  obtain ⟨H, hH, hae⟩ := exists_stokesVectorPressure_C2_representative u hdiv
  have hb := unitBallPressure_representative_derivative_bounds
    (stokesVectorForce (vec3Ball 0 1) u) (stokesVectorPressure_weaklyHarmonic u hdiv) H hH hae
  have hforce := stokesVectorForce_norm_le (isOpen_vec3Ball 0 1).measurableSet
    volume_vec3Ball_lt_top.ne u
  refine ⟨H, hH, hae, ?_, ?_⟩
  · intro x hx
    exact (hb.1 x hx).trans (by
      have ht := mul_le_mul_of_nonneg_left hforce unitBallPressureGradientConstant_nonneg
      simpa only [stokesVectorPressureGradientConstant, mul_assoc] using ht)
  · intro x hx i j
    exact (hb.2 x hx i j).trans (by
      have ht := mul_le_mul_of_nonneg_left hforce unitBallPressureHessianConstant_nonneg
      simpa only [stokesVectorPressureHessianConstant, mul_assoc] using ht)

end FluidSingularSets
