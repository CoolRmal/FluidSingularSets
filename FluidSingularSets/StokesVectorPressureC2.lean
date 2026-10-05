-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallPressureC2
public import FluidSingularSets.StokesVectorForce

/-!
# Actual harmonic Stokes pressure for square-integrable vector source data

The force is constructed from the genuine energy-space velocity reconstruction.
Its true compact-test equation discharges the source identification premise in
the harmonicity and C² regularity theorems.
-/

@[expose] public section

open CKN MeasureTheory Set
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- Actual divergence-free L² vector data give a genuinely harmonic constructed pressure. -/
theorem stokesVectorPressure_weaklyHarmonic
    (u : Lp Vec3 2 (volume.restrict (vec3Ball 0 1)))
    (hdiv : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball 0 1 →
        (∫ x in vec3Ball 0 1, ∑ i : Fin 3, u x i * spatialDeriv ψ i x) = 0) :
    WeaklyHarmonicOn (vec3Ball 0 1)
      (unitBallPressureFunction (stokesVectorForce (vec3Ball 0 1) u)) :=
  unitBallStokesPressure_weaklyHarmonic_of_vector_source u
    (stokesVectorForce (vec3Ball 0 1) u)
    (stokesVectorForce_test (isOpen_vec3Ball 0 1).measurableSet
      volume_vec3Ball_lt_top.ne u) hdiv

/-- The actual L² vector force has a genuine interior C² pressure representative. -/
theorem exists_stokesVectorPressure_C2_representative
    (u : Lp Vec3 2 (volume.restrict (vec3Ball 0 1)))
    (hdiv : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball 0 1 →
        (∫ x in vec3Ball 0 1, ∑ i : Fin 3, u x i * spatialDeriv ψ i x) = 0) :
    ∃ H : Vec3 → ℝ, ContDiffOn ℝ (2 : ℕ∞) H (vec3Ball 0 (1 / 4)) ∧
      unitBallPressureFunction (stokesVectorForce (vec3Ball 0 1) u)
        =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))] H :=
  exists_unitBallStokesPressure_C2_representative_of_vector_source u
    (stokesVectorForce (vec3Ball 0 1) u)
    (stokesVectorForce_test (isOpen_vec3Ball 0 1).measurableSet
      volume_vec3Ball_lt_top.ne u) hdiv

end FluidSingularSets
