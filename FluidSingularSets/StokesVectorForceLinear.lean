-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StokesVectorForce
public import FluidSingularSets.RealHilbertDual

/-!
# Continuous linear construction of the actual vector Stokes force

The literal component pairings are real linear in the genuine L² source.
Their proved norm estimate bundles the actual construction as a continuous
linear map on every measurable finite-volume domain.
-/

@[expose] public section

open CKN MeasureTheory Set
open CKN.Foundation.Parabolic
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual vector source construction respects addition. -/
theorem stokesVectorForce_add (U : Set Vec3) (u v : Lp Vec3 2 (volume.restrict U)) :
    stokesVectorForce U (u + v) = stokesVectorForce U u + stokesVectorForce U v := by
  ext w
  simp only [stokesVectorForce_apply, map_add, inner_add_left, Finset.sum_add_distrib,
    add_apply]

/-- The actual vector source construction respects real scalar multiplication. -/
theorem stokesVectorForce_smul (U : Set Vec3) (c : ℝ)
    (u : Lp Vec3 2 (volume.restrict U)) :
    stokesVectorForce U (c • u) = c • stokesVectorForce U u := by
  ext w
  simp only [stokesVectorForce_apply, map_smul, real_inner_smul_left, smul_apply,
    smul_eq_mul, Finset.mul_sum]

/-- The actual source construction as a genuine linear map. -/
def stokesVectorForceLinear (U : Set Vec3) :
    Lp Vec3 2 (volume.restrict U) →ₗ[ℝ] StokesEnergyForce U where
  toFun := stokesVectorForce U
  map_add' := stokesVectorForce_add U
  map_smul' := stokesVectorForce_smul U

/-- The actual source construction as a genuine bounded linear map. -/
def stokesVectorForceL (U : Set Vec3) :
    Lp Vec3 2 (volume.restrict U) →L[ℝ] StokesEnergyForce U :=
  ∑ i : Fin 3,
    (realDualPrecompose ((stokesVelocityComponent U i).comp (stokesEnergyVelocity U))).comp
      ((realHilbertRiesz (Lp ℝ 2 (volume.restrict U))).comp (stokesVelocityComponent U i))

@[simp]
theorem stokesVectorForceL_apply (U : Set Vec3) (u : Lp Vec3 2 (volume.restrict U)) :
    stokesVectorForceL U u = stokesVectorForce U u := by
  ext v
  simp only [stokesVectorForceL, sum_apply, ContinuousLinearMap.comp_apply,
    realDualPrecompose_apply, realHilbertRiesz_apply, stokesVectorForce_apply]

end FluidSingularSets
