-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StokesPressureRecovery
public import FluidSingularSets.RealHilbertDual

/-!
# The actual variational pressure projection

Riesz representation makes the Stokes gradient solution a continuous linear
operator on the actual energy dual. Subtracting its gradient pairing defines
the genuine residual projection. It is bounded, idempotent, and fixes the
actual distributional gradients of spatial L² pressures.
-/

@[expose] public section

open MeasureTheory Set CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The genuine variational Stokes solution is a continuous linear operator. -/
def stokesEnergySolutionL (U : Set Vec3) :
    StokesEnergyForce U →L[ℝ] stokesSolenoidalEnergySpace U :=
  (realHilbertRieszInverse (stokesSolenoidalEnergySpace U)).comp
    (realDualPrecompose (E := stokesGradientEnergySpace U)
      (K := stokesSolenoidalEnergySpace U) (stokesSolenoidalEnergySpace U).toSubmodule.subtypeL)

@[simp]
theorem stokesEnergySolutionL_apply {U : Set Vec3} (F : StokesEnergyForce U) :
    stokesEnergySolutionL U F = stokesEnergySolution F := rfl

/-- The variational solution respects addition. -/
theorem stokesEnergySolution_add {U : Set Vec3} (F G : StokesEnergyForce U) :
    stokesEnergySolution (F + G) = stokesEnergySolution F + stokesEnergySolution G :=
  (stokesEnergySolutionL U).map_add F G

/-- The variational solution respects real scalar multiplication. -/
theorem stokesEnergySolution_smul {U : Set Vec3} (c : ℝ) (F : StokesEnergyForce U) :
    stokesEnergySolution (c • F) = c • stokesEnergySolution F :=
  (stokesEnergySolutionL U).map_smul c F

/-- The variational pressure residual as a genuine continuous linear projection. -/
def stokesPressureProjection (U : Set Vec3) :
    StokesEnergyForce U →L[ℝ] StokesEnergyForce U :=
  ContinuousLinearMap.id ℝ (StokesEnergyForce U) -
    (realHilbertRiesz (stokesGradientEnergySpace U)).comp
      ((stokesSolenoidalEnergySpace U).toSubmodule.subtypeL.comp (stokesEnergySolutionL U))

@[simp]
theorem stokesPressureProjection_apply {U : Set Vec3} (F : StokesEnergyForce U) :
    stokesPressureProjection U F = stokesEnergyResidual F := by
  ext v
  rfl

/-- The genuine residual projection satisfies its uniform pointwise operator bound. -/
theorem stokesPressureProjection_bound (U : Set Vec3) (F : StokesEnergyForce U) :
    ‖stokesPressureProjection U F‖ ≤ 2 * ‖F‖ :=
  stokesEnergyResidual_norm_le F

/-- A force vanishing on every divergence-free energy element has zero Stokes velocity. -/
theorem stokesEnergySolution_eq_zero_of_kernel_annihilation
    {U : Set Vec3} (F : StokesEnergyForce U)
    (hF : ∀ v : stokesSolenoidalEnergySpace U, F v = 0) :
    stokesEnergySolution F = 0 := by
  apply (stokesEnergySolution_unique F 0 ?_).symm
  intro v
  rw [inner_zero_left, hF v]

/-- The residual projection fixes every genuine functional annihilating the kernel. -/
theorem stokesPressureProjection_eq_self_of_kernel_annihilation
    {U : Set Vec3} (F : StokesEnergyForce U)
    (hF : ∀ v : stokesSolenoidalEnergySpace U, F v = 0) :
    stokesPressureProjection U F = F := by
  rw [stokesPressureProjection_apply, stokesEnergyResidual,
    stokesEnergySolution_eq_zero_of_kernel_annihilation F hF]
  simp

/-- The actual pressure residual projection is idempotent. -/
theorem stokesPressureProjection_idempotent {U : Set Vec3} (F : StokesEnergyForce U) :
    stokesPressureProjection U (stokesPressureProjection U F) =
      stokesPressureProjection U F := by
  apply stokesPressureProjection_eq_self_of_kernel_annihilation
  intro v
  rw [stokesPressureProjection_apply]
  exact stokesEnergyResidual_eq_zero_of_divergence_eq_zero F v v.2

/-- The literal distributional gradient of an actual spatial L² pressure. -/
def stokesL2PressureGradient {U : Set Vec3} (p : Lp ℝ 2 (volume.restrict U)) :
    StokesEnergyForce U := -((innerSL ℝ p).comp (stokesEnergyDivergence U))

/-- The true pressure gradient pairing is minus the actual pressure-divergence integral. -/
theorem stokesL2PressureGradient_test {U : Set Vec3}
    (p : Lp ℝ 2 (volume.restrict U)) (φ : StokesVectorTest U) :
    stokesL2PressureGradient p (stokesEnergyTest φ) =
      -(∫ x in U, p x * ∑ i : Fin 3, (φ i).partialDeriv i x) := by
  change -(inner ℝ p (stokesEnergyDivergence U (stokesEnergyTest φ))) = _
  rw [L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [stokesEnergyDivergence_test_ae φ] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The genuine projection fixes every actual pressure gradient. -/
theorem stokesPressureProjection_pressureGradient {U : Set Vec3}
    (p : Lp ℝ 2 (volume.restrict U)) :
    stokesPressureProjection U (stokesL2PressureGradient p) = stokesL2PressureGradient p := by
  apply stokesPressureProjection_eq_self_of_kernel_annihilation
  intro v
  change -(inner ℝ p (stokesEnergyDivergence U v)) = 0
  have hv : stokesEnergyDivergence U v = 0 := v.2
  rw [hv, inner_zero_right, neg_zero]

end FluidSingularSets
