-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallHarmonicForceGradient

/-!
# Canonical extension of the true harmonic pressure gradient

Riesz representation identifies the completed energy dual with the genuine
energy Hilbert space. Orthogonal projection onto the actual scalar-gradient
annihilator therefore gives a norm-contracting projection of forces. It fixes
every genuine annihilating force and extends the proved interior gradient
operator to the whole energy dual, for transport of weak time derivatives.
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

local instance harmonicForceExtensionForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance harmonicForceExtensionForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The actual energy vectors whose Riesz forces annihilate compact scalar gradients. -/
def unitBallGradientFreeEnergy : ClosedSubmodule ℝ (stokesGradientEnergySpace (vec3Ball 0 1)) where
  toSubmodule :=
    { carrier := {v | ∀ ψ : WeakTestFunction (vec3Ball 0 1),
        realHilbertRiesz (stokesGradientEnergySpace (vec3Ball 0 1)) v
          (stokesEnergyTest (stokesScalarGradientTest ψ)) = 0}
      zero_mem' := by
        intro ψ
        rw [map_zero]
        rfl
      add_mem' := by
        intro u v hu hv ψ
        simp only [map_add, add_apply, hu ψ, hv ψ, add_zero]
      smul_mem' := by
        intro c u hu ψ
        simp only [map_smul, smul_apply, hu ψ, smul_zero] }
  isClosed' := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro ψ
    exact isClosed_eq (((ContinuousLinearMap.apply ℝ ℝ
      (stokesEnergyTest (stokesScalarGradientTest ψ))).continuous).comp
        (realHilbertRiesz (stokesGradientEnergySpace (vec3Ball 0 1))).continuous) continuous_const

/-- Genuine Riesz force of an actual gradient-annihilating completed energy vector. -/
def unitBallGradientFreeEnergyForce : unitBallGradientFreeEnergy →L[ℝ]
    unitBallGradientFreeForce :=
  ((realHilbertRiesz (stokesGradientEnergySpace (vec3Ball 0 1))).comp
    unitBallGradientFreeEnergy.toSubmodule.subtypeL).codRestrict
      unitBallGradientFreeForce.toSubmodule (fun v ↦ v.property)

@[simp]
theorem unitBallGradientFreeEnergyForce_apply (v : unitBallGradientFreeEnergy) :
    (unitBallGradientFreeEnergyForce v : StokesEnergyForce (vec3Ball 0 1)) =
      realHilbertRiesz (stokesGradientEnergySpace (vec3Ball 0 1)) v.1 := rfl

/-- The canonical actual orthogonal projection of forces onto the harmonic-pressure domain. -/
def unitBallGradientFreeForceProjection : StokesEnergyForce (vec3Ball 0 1) →L[ℝ]
    unitBallGradientFreeForce :=
  unitBallGradientFreeEnergyForce.comp
    (unitBallGradientFreeEnergy.toSubmodule.orthogonalProjectionOnto.comp
      (realHilbertRieszInverse (stokesGradientEnergySpace (vec3Ball 0 1))))

/-- Riesz representation preserves the actual compact-gradient annihilation equations. -/
theorem unitBallGradientFreeForce_rieszInverse_mem (F : unitBallGradientFreeForce) :
    realHilbertRieszInverse (stokesGradientEnergySpace (vec3Ball 0 1)) F.1 ∈
      unitBallGradientFreeEnergy := by
  intro ψ
  rw [realHilbertRiesz_apply, realHilbertRieszInverse_apply]
  simpa only [InnerProductSpace.toDual_symm_apply] using F.property ψ

/-- The actual force projection fixes every force in the true annihilator. -/
theorem unitBallGradientFreeForceProjection_of_gradientFree (F : unitBallGradientFreeForce) :
    unitBallGradientFreeForceProjection F.1 = F := by
  let v : unitBallGradientFreeEnergy :=
    ⟨realHilbertRieszInverse (stokesGradientEnergySpace (vec3Ball 0 1)) F.1,
      unitBallGradientFreeForce_rieszInverse_mem F⟩
  have hp := unitBallGradientFreeEnergy.toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self
    (⟨v.1, v.property⟩ : unitBallGradientFreeEnergy.toSubmodule)
  change unitBallGradientFreeEnergy.toSubmodule.orthogonalProjectionOnto v.1 = v at hp
  apply Subtype.ext
  change realHilbertRiesz (stokesGradientEnergySpace (vec3Ball 0 1))
    (unitBallGradientFreeEnergy.toSubmodule.orthogonalProjectionOnto v.1).1 = F.1
  rw [hp]
  ext w
  change inner ℝ ((InnerProductSpace.toDual ℝ
    (stokesGradientEnergySpace (vec3Ball 0 1))).symm F.1) w = F.1 w
  exact InnerProductSpace.toDual_symm_apply

/-- The true force projection contracts the actual energy-dual norm. -/
theorem unitBallGradientFreeForceProjection_norm_le (F : StokesEnergyForce (vec3Ball 0 1)) :
    ‖unitBallGradientFreeForceProjection F‖ ≤ ‖F‖ := by
  change ‖(InnerProductSpace.toDual ℝ (stokesGradientEnergySpace (vec3Ball 0 1)))
    (unitBallGradientFreeEnergy.toSubmodule.orthogonalProjectionOnto
      ((InnerProductSpace.toDual ℝ (stokesGradientEnergySpace (vec3Ball 0 1))).symm F)).1‖ ≤ ‖F‖
  rw [(InnerProductSpace.toDual ℝ (stokesGradientEnergySpace (vec3Ball 0 1))).norm_map]
  exact (unitBallGradientFreeEnergy.toSubmodule.norm_orthogonalProjectionOnto_apply_le _).trans
    ((InnerProductSpace.toDual ℝ (stokesGradientEnergySpace (vec3Ball 0 1))).symm.norm_map F).le

/-- Genuine interior harmonic pressure gradient after canonical force projection. -/
def unitBallHarmonicForceGradientExtended : StokesEnergyForce (vec3Ball 0 1) →L[ℝ]
    C(unitBallPressureCompactInterior, Vec3) :=
  unitBallHarmonicForceGradient.comp unitBallGradientFreeForceProjection

/-- On genuine gradient-annihilating forces the extension is exactly the true pressure gradient. -/
theorem unitBallHarmonicForceGradientExtended_of_gradientFree (F : unitBallGradientFreeForce) :
    unitBallHarmonicForceGradientExtended F.1 = unitBallHarmonicForceGradient F := by
  simp only [unitBallHarmonicForceGradientExtended, ContinuousLinearMap.comp_apply,
    unitBallGradientFreeForceProjection_of_gradientFree]

/-- The actual extended operator retains the universal energy-dual gradient bound. -/
theorem unitBallHarmonicForceGradientExtended_norm_le (F : StokesEnergyForce (vec3Ball 0 1)) :
    ‖unitBallHarmonicForceGradientExtended F‖ ≤ unitBallPressureGradientConstant * ‖F‖ :=
  (unitBallHarmonicForceGradient_norm_le _).trans
    (mul_le_mul_of_nonneg_left (unitBallGradientFreeForceProjection_norm_le F)
      unitBallPressureGradientConstant_nonneg)

theorem unitBallHarmonicForceGradientExtended_opNorm_le :
    ‖unitBallHarmonicForceGradientExtended‖ ≤ unitBallPressureGradientConstant :=
  ContinuousLinearMap.opNorm_le_bound _ unitBallPressureGradientConstant_nonneg
    unitBallHarmonicForceGradientExtended_norm_le

end FluidSingularSets
