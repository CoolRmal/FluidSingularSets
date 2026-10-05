-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.BallCenteredPressureOperator

/-!
# Genuine unit-ball compatibility of physical Stokes pressures

At center zero and radius one, the actual affine L² isometry, energy isometry,
and force pullback are identities. Consequently the transported physical-ball
pressure is the original constructed unit-ball pressure. This identifies the
actual convective and viscous time curves used by the two proof interfaces.
-/

@[expose] public section

open CKN MeasureTheory Set
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual normalized affine L² map is identity at the unit ball. -/
theorem ballL2Isometry_zero_one (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E 2 (volume.restrict (vec3Ball 0 1))) :
    ballL2Isometry E 0 (r := 1) zero_lt_one f = f := by
  apply Lp.ext
  have he := ballL2Isometry_ae E 0 (r := 1) zero_lt_one f
  simpa only [one_pow, Real.one_rpow, one_smul, CKN.spatialAffine, zero_add] using he

/-- Its actual inverse L² map is also identity at the unit ball. -/
theorem ballL2Isometry_symm_zero_one (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E 2 (volume.restrict (vec3Ball 0 1))) :
    (ballL2Isometry E 0 (r := 1) zero_lt_one).symm f = f := by
  have he := ballL2Isometry_zero_one E
    ((ballL2Isometry E 0 (r := 1) zero_lt_one).symm f)
  rw [(ballL2Isometry E 0 (r := 1) zero_lt_one).apply_symm_apply] at he
  exact he.symm

/-- The genuine energy-space affine isometry is identity at unit radius. -/
theorem ballEnergyIsometry_zero_one
    (v : stokesGradientEnergySpace (vec3Ball 0 1)) :
    ballEnergyIsometry 0 (r := 1) zero_lt_one v = v := by
  apply Subtype.ext
  exact ballL2Isometry_zero_one StokesGradientMatrix v.val

/-- The genuine inverse energy-space isometry is identity at unit radius. -/
theorem ballEnergyIsometry_symm_zero_one
    (v : stokesGradientEnergySpace (vec3Ball 0 1)) :
    (ballEnergyIsometry 0 (r := 1) zero_lt_one).symm v = v := by
  apply Subtype.ext
  exact ballL2Isometry_symm_zero_one StokesGradientMatrix v.val

/-- The actual pulled-back force equals the original force at the unit ball. -/
theorem ballStokesForcePullback_zero_one (F : StokesEnergyForce (vec3Ball 0 1)) :
    ballStokesForcePullback 0 (r := 1) zero_lt_one F = F := by
  ext v
  change F ((ballEnergyIsometry 0 (r := 1) zero_lt_one).symm v) = F v
  rw [ballEnergyIsometry_symm_zero_one]

/-- The genuine physical pressure is the original unit pressure at center zero and radius one. -/
theorem ballStokesPressureL_zero_one (F : StokesEnergyForce (vec3Ball 0 1)) :
    ballStokesPressureL 0 (r := 1) zero_lt_one F =
      (unitBallStokesPressure F : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) := by
  rw [ballStokesPressureL_apply, ballStokesForcePullback_zero_one,
    ballL2Isometry_symm_zero_one]

/-- The actual transported tensor pressure agrees with the native tensor pressure. -/
theorem ballTensorPressureL_zero_one (T : StokesGradientL2 (vec3Ball 0 1)) :
    ballTensorPressureL 0 (r := 1) zero_lt_one T =
      (unitBallTensorPressureL T : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) :=
  ballStokesPressureL_zero_one (stokesTensorForce T)

/-- The actual physical nonlinear pressure agrees with the original unit nonlinear pressure. -/
theorem ballNonlinearPressure_zero_one (u : Vec3 → Vec3)
    (hu : MemLp u 4 (volume.restrict (vec3Ball 0 1))) :
    ballNonlinearPressure 0 (r := 1) zero_lt_one u hu =
      (unitBallNonlinearPressure u hu : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) :=
  ballTensorPressureL_zero_one (stokesConvectiveTensorL2 u hu)

/-- The actual physical viscous pressure agrees with the original unit viscous pressure. -/
theorem ballRawViscousPressure_zero_one (D : Vec3 → Fin 3 → Vec3)
    (hD : MemLp D 2 (volume.restrict (vec3Ball 0 1))) :
    ballRawViscousPressure 0 (r := 1) zero_lt_one D hD =
      (unitBallRawViscousPressure D hD : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) :=
  ballTensorPressureL_zero_one (-stokesRawGradientL2 D hD)

/-- The physical vector-source pressure agrees with the actual unit source pressure. -/
theorem ballVectorPressureL_zero_one (u : Lp Vec3 2 (volume.restrict (vec3Ball 0 1))) :
    ballVectorPressureL 0 (r := 1) zero_lt_one u =
      (unitBallStokesPressure (stokesVectorForce (vec3Ball 0 1) u) :
        Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) :=
  ballStokesPressureL_zero_one (stokesVectorForce (vec3Ball 0 1) u)

/-- At every time the physical convective curve is exactly the native unit curve. -/
theorem ballConvectivePressureCurve_zero_one (u : ParabolicPoint → Vec3) (t : ℝ) :
    ballConvectivePressureCurve 0 (r := 1) zero_lt_one u t =
      (unitBallConvectivePressureCurve u t : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) :=
  ballTensorPressureL_zero_one _

/-- At every time the physical viscous curve is exactly the native unit curve. -/
theorem ballViscousPressureCurve_zero_one (D : ParabolicPoint → Fin 3 → Vec3) (t : ℝ) :
    ballViscousPressureCurve 0 (r := 1) zero_lt_one D t =
      (unitBallViscousPressureCurve D t : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) :=
  ballTensorPressureL_zero_one _

end FluidSingularSets
