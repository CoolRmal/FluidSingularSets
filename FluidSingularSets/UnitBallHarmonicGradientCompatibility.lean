-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallHarmonicForceExtension

/-!
# Exact compatibility of the source and energy-force pressure gradients

The two canonical C² representatives belong to the same actual Stokes
pressure class. Continuity identifies them pointwise on the open interior,
so their true gradients agree. This connects the spatial source operators
with the energy-dual operator used to transport time derivatives.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

local instance harmonicGradientCompatibilityForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance harmonicGradientCompatibilityForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The literal vector source force belongs to the actual gradient-test annihilator. -/
def unitBallDivergenceFreeL2Force : unitBallDivergenceFreeL2 →L[ℝ] unitBallGradientFreeForce :=
  (unitBallHilbertVectorForce.comp unitBallDivergenceFreeL2.toSubmodule.subtypeL).codRestrict
    unitBallGradientFreeForce.toSubmodule (fun u ↦ u.property)

@[simp]
theorem unitBallDivergenceFreeL2Force_apply (u : unitBallDivergenceFreeL2) :
    (unitBallDivergenceFreeL2Force u : StokesEnergyForce (vec3Ball 0 1)) =
      unitBallHilbertVectorForce u.1 := rfl

/-- The actual source and force representatives agree on the entire open interior. -/
theorem unitBallHarmonicForcePressureRepresentative_eq_source
    (u : unitBallDivergenceFreeL2) :
    EqOn (unitBallHarmonicForcePressureRepresentative (unitBallDivergenceFreeL2Force u))
      (unitBallHarmonicPressureRepresentative u) (vec3Ball 0 (1 / 4)) := by
  have hf := unitBallHarmonicForcePressureRepresentative_pressure_ae
    (unitBallDivergenceFreeL2Force u)
  have hu := unitBallHarmonicPressureRepresentative_ae u
  change unitBallPressureFunction (unitBallHilbertVectorForce u.1)
    =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))]
      unitBallHarmonicForcePressureRepresentative (unitBallDivergenceFreeL2Force u) at hf
  change unitBallPressureFunction (unitBallHilbertVectorForce u.1)
    =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))] unitBallHarmonicPressureRepresentative u at hu
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq (hf.symm.trans hu)
    (isOpen_vec3Ball 0 (1 / 4))
    (unitBallHarmonicForcePressureRepresentative_contDiff
      (unitBallDivergenceFreeL2Force u)).continuousOn
    (unitBallHarmonicPressureRepresentative_contDiff u).continuousOn

/-- The force-domain gradient is exactly the already constructed source-domain gradient. -/
theorem unitBallHarmonicForceGradient_of_source (u : unitBallDivergenceFreeL2) :
    unitBallHarmonicForceGradient (unitBallDivergenceFreeL2Force u) =
      unitBallHarmonicGradient u := by
  ext x i
  change classicalGradient
    (unitBallHarmonicForcePressureRepresentative (unitBallDivergenceFreeL2Force u)) x.1 i =
      classicalGradient (unitBallHarmonicPressureRepresentative u) x.1 i
  exact congrArg (fun v : Vec3 ↦ v i)
    (classicalGradient_eqOn_of_eqOn (isOpen_vec3Ball 0 (1 / 4))
      (unitBallHarmonicForcePressureRepresentative_eq_source u)
      (unitBallPressureCompactInterior_subset x.property))

/-- The all-force extension fixes the true harmonic pressure gradient of the actual source. -/
theorem unitBallHarmonicForceGradientExtended_of_source (u : unitBallDivergenceFreeL2) :
    unitBallHarmonicForceGradientExtended (unitBallHilbertVectorForce u.1) =
      unitBallHarmonicGradient u := by
  change unitBallHarmonicForceGradientExtended
    (unitBallDivergenceFreeL2Force u : StokesEnergyForce (vec3Ball 0 1)) = _
  rw [unitBallHarmonicForceGradientExtended_of_gradientFree]
  exact unitBallHarmonicForceGradient_of_source u

end FluidSingularSets
