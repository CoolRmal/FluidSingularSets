-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.BallStokesUnitCompatibility

/-!
# Actual endpoint moments of the native unit-ball pressure curves

The proved physical-to-unit compatibility transfers genuine endpoint mixed
velocity and weak-gradient bounds to the mean-zero pressure curves used by
the actual projected local energy inequality.
-/

@[expose] public section

open CKN MeasureTheory Set
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The physical and native unit convective curves have exactly the same time seminorms. -/
theorem unitBallConvectivePressureCurve_eLpNorm_eq_physical
    {ν : Measure ℝ} [SFinite ν] {u : ParabolicPoint → Vec3}
    (hu : AEStronglyMeasurable u ((volume.restrict (vec3Ball 0 1)).prod ν)) (a : ℝ≥0∞) :
    eLpNorm (unitBallConvectivePressureCurve u) a ν =
      eLpNorm (ballConvectivePressureCurve 0 (r := 1) zero_lt_one u) a ν := by
  apply eLpNorm_congr_norm_ae (unitBallConvectivePressureCurve_aestronglyMeasurable hu)
    (ballConvectivePressureCurve_aestronglyMeasurable 0 zero_lt_one hu)
  exact .of_forall fun t ↦ by
    rw [ballConvectivePressureCurve_zero_one]
    rfl

/-- The physical and native unit viscous curves have exactly the same time seminorms. -/
theorem unitBallViscousPressureCurve_eLpNorm_eq_physical
    {ν : Measure ℝ} [SFinite ν] {D : ParabolicPoint → Fin 3 → Vec3}
    (hD : AEStronglyMeasurable D ((volume.restrict (vec3Ball 0 1)).prod ν)) (a : ℝ≥0∞) :
    eLpNorm (unitBallViscousPressureCurve D) a ν =
      eLpNorm (ballViscousPressureCurve 0 (r := 1) zero_lt_one D) a ν := by
  apply eLpNorm_congr_norm_ae (unitBallViscousPressureCurve_aestronglyMeasurable hD)
    (ballViscousPressureCurve_aestronglyMeasurable 0 zero_lt_one hD)
  exact .of_forall fun t ↦ by
    rw [ballViscousPressureCurve_zero_one]
    rfl

/-- The native convective pressure has the true endpoint spatial velocity bound. -/
theorem unitBallConvectivePressureCurve_enorm_le_six
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : MemLp (fun y ↦ u (y, t)) 6 (volume.restrict (vec3Ball 0 1))) :
    ‖unitBallConvectivePressureCurve u t‖ₑ ≤
      12 * volume (vec3Ball 0 1) ^ (1 / 6 : ℝ) *
        eLpNorm (fun y ↦ u (y, t)) 6 (volume.restrict (vec3Ball 0 1)) ^ 2 := by
  have hb := ballConvectivePressureCurve_enorm_le_six 0 zero_lt_one u t hu
  rw [ballConvectivePressureCurve_zero_one] at hb
  exact hb

/-- The genuine native pressure time L¹ bound follows from the actual endpoint velocity cost. -/
theorem unitBallConvectivePressureCurve_eLpNorm_one_le_six_moment
    {ν : Measure ℝ} [SFinite ν] {u : ParabolicPoint → Vec3}
    (hu : AEStronglyMeasurable u ((volume.restrict (vec3Ball 0 1)).prod ν))
    (hus : ∀ᵐ t ∂ν, MemLp (fun y ↦ u (y, t)) 6 (volume.restrict (vec3Ball 0 1))) :
    eLpNorm (unitBallConvectivePressureCurve u) 1 ν ≤
      12 * volume (vec3Ball 0 1) ^ (1 / 6 : ℝ) *
        ∫⁻ t, eLpNorm (fun y ↦ u (y, t)) 6 (volume.restrict (vec3Ball 0 1)) ^ 2 ∂ν := by
  rw [unitBallConvectivePressureCurve_eLpNorm_eq_physical hu]
  exact ballConvectivePressureCurve_eLpNorm_one_le_six_moment 0 zero_lt_one hu hus

/-- Finite actual endpoint velocity cost gives the native convective pressure time L¹ class. -/
theorem unitBallConvectivePressureCurve_memLp_one_of_six_moment
    {ν : Measure ℝ} [SFinite ν] {u : ParabolicPoint → Vec3}
    (hu : AEStronglyMeasurable u ((volume.restrict (vec3Ball 0 1)).prod ν))
    (hus : ∀ᵐ t ∂ν, MemLp (fun y ↦ u (y, t)) 6 (volume.restrict (vec3Ball 0 1)))
    (hfin : (∫⁻ t, eLpNorm (fun y ↦ u (y, t)) 6
      (volume.restrict (vec3Ball 0 1)) ^ 2 ∂ν) < ⊤) :
    MemLp (unitBallConvectivePressureCurve u) 1 ν := by
  rw [memLp_iff, unitBallConvectivePressureCurve_eLpNorm_eq_physical hu]
  exact ballConvectivePressureCurve_memLp_one_of_six_moment 0 zero_lt_one hu hus hfin

/-- The genuine native viscous pressure time L² bound follows from actual gradient energy. -/
theorem unitBallViscousPressureCurve_eLpNorm_two_le_gradient_moment
    {ν : Measure ℝ} [SFinite ν] {D : ParabolicPoint → Fin 3 → Vec3}
    (hD : AEStronglyMeasurable D ((volume.restrict (vec3Ball 0 1)).prod ν))
    (hDs : ∀ᵐ t ∂ν, MemLp (fun y ↦ D (y, t)) 2 (volume.restrict (vec3Ball 0 1))) :
    eLpNorm (unitBallViscousPressureCurve D) 2 ν ≤
      12 * (∫⁻ t, eLpNorm (fun y ↦ D (y, t)) 2 (volume.restrict (vec3Ball 0 1)) ^ 2 ∂ν)
        ^ (1 / 2 : ℝ) := by
  rw [unitBallViscousPressureCurve_eLpNorm_eq_physical hD]
  exact ballViscousPressureCurve_eLpNorm_two_le_gradient_moment 0 zero_lt_one hD hDs

/-- Finite actual gradient energy gives the native viscous pressure time L² class. -/
theorem unitBallViscousPressureCurve_memLp_two_of_gradient_moment
    {ν : Measure ℝ} [SFinite ν] {D : ParabolicPoint → Fin 3 → Vec3}
    (hD : AEStronglyMeasurable D ((volume.restrict (vec3Ball 0 1)).prod ν))
    (hDs : ∀ᵐ t ∂ν, MemLp (fun y ↦ D (y, t)) 2 (volume.restrict (vec3Ball 0 1)))
    (hfin : (∫⁻ t, eLpNorm (fun y ↦ D (y, t)) 2
      (volume.restrict (vec3Ball 0 1)) ^ 2 ∂ν) < ⊤) :
    MemLp (unitBallViscousPressureCurve D) 2 ν := by
  rw [memLp_iff]
  exact (unitBallViscousPressureCurve_eLpNorm_two_le_gradient_moment hD hDs).trans_lt
    (by finiteness [hfin.ne])

end FluidSingularSets
