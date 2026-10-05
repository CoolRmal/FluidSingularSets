-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallStokesPressure
public import FluidSingularSets.StokesPressureProjection

/-!
# The genuine bounded ball pressure operator

The mean-zero pressure is unique by the actual divergence right inverse.
Its genuine pairings prove linearity and a uniform operator bound. The
operator fixes the pressure of every actual mean-zero L² gradient source.
-/

@[expose] public section

open MeasureTheory Set CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual mean-zero pressure is unique among genuine variational pressures. -/
theorem unitBallStokesPressure_unique (F : StokesEnergyForce (vec3Ball 0 1))
    (p : unitBallMeanZeroL2)
    (hp : ∀ v : stokesGradientEnergySpace (vec3Ball 0 1),
      -(inner ℝ (p : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))
        (stokesEnergyDivergence (vec3Ball 0 1) v)) = stokesEnergyResidual F v) :
    p = unitBallStokesPressure F := by
  apply (InnerProductSpace.toDual ℝ unitBallMeanZeroL2).injective
  ext g
  let v := unitBallEnergyDivergenceRightInverse g
  have h := hp v
  have h' := unitBallStokesPressure_pairing F v
  change -(inner ℝ p (unitBallMeanZeroDivergence v)) = _ at h
  change -(inner ℝ (unitBallStokesPressure F) (unitBallMeanZeroDivergence v)) = _ at h'
  rw [unitBallEnergyDivergenceRightInverse_apply] at h h'
  change inner ℝ p g = inner ℝ (unitBallStokesPressure F) g
  linarith

/-- The genuine pressure respects addition of actual energy forces. -/
theorem unitBallStokesPressure_add (F G : StokesEnergyForce (vec3Ball 0 1)) :
    unitBallStokesPressure (F + G) = unitBallStokesPressure F + unitBallStokesPressure G := by
  symm
  apply unitBallStokesPressure_unique
  intro v
  change -(inner ℝ ((unitBallStokesPressure F :
    Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) + unitBallStokesPressure G)
      (stokesEnergyDivergence (vec3Ball 0 1) v)) = _
  rw [inner_add_left, neg_add, unitBallStokesPressure_pairing,
    unitBallStokesPressure_pairing]
  simp only [← stokesPressureProjection_apply, map_add, add_apply]

/-- The genuine pressure respects real scalar multiplication. -/
theorem unitBallStokesPressure_smul (c : ℝ) (F : StokesEnergyForce (vec3Ball 0 1)) :
    unitBallStokesPressure (c • F) = c • unitBallStokesPressure F := by
  symm
  apply unitBallStokesPressure_unique
  intro v
  change -(inner ℝ (c • (unitBallStokesPressure F :
    Lp ℝ 2 (volume.restrict (vec3Ball 0 1))))
      (stokesEnergyDivergence (vec3Ball 0 1) v)) = _
  rw [real_inner_smul_left, ← mul_neg, unitBallStokesPressure_pairing]
  simp only [← stokesPressureProjection_apply, map_smul, smul_apply, smul_eq_mul]

/-- The constructed mean-zero pressure is an actual continuous linear operator. -/
def unitBallStokesPressureL :
    StokesEnergyForce (vec3Ball 0 1) →L[ℝ] unitBallMeanZeroL2 :=
  -((realHilbertRieszInverse unitBallMeanZeroL2).comp
    ((realDualPrecompose (E := stokesGradientEnergySpace (vec3Ball 0 1))
      (K := unitBallMeanZeroL2) unitBallEnergyDivergenceRightInverse).comp
        (stokesPressureProjection (vec3Ball 0 1))))

@[simp]
theorem unitBallStokesPressureL_apply (F : StokesEnergyForce (vec3Ball 0 1)) :
    unitBallStokesPressureL F = unitBallStokesPressure F := rfl

/-- The actual continuous ball pressure operator satisfies its universal bound. -/
theorem unitBallStokesPressureL_bound (F : StokesEnergyForce (vec3Ball 0 1)) :
    ‖unitBallStokesPressureL F‖ ≤ 4 * ‖F‖ :=
  unitBallStokesPressure_norm F

/-- The actual operator recovers every mean-zero pressure from its genuine gradient. -/
theorem unitBallStokesPressure_pressureGradient (p : unitBallMeanZeroL2) :
    unitBallStokesPressure (stokesL2PressureGradient
      (p : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))) = p := by
  symm
  apply unitBallStokesPressure_unique
  intro v
  rw [← stokesPressureProjection_apply, stokesPressureProjection_pressureGradient]
  rfl

end FluidSingularSets
