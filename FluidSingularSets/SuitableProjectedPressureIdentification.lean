-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.SuitableProjectedLocalEnergy

/-!
# Actual projected pressure identification

The pressure in the actual nonsmooth energy inequality equals the nonlinear
and viscous Stokes pressures plus the literal original spatial average. The
identification uses actual centered pressure classes and the proved gradient
annihilation of the momentum derivative.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

local instance projectedPressureIdentificationForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- Genuine gradient-annihilating forces have their literal pressure representative. -/
theorem harmonicSpatialPressureRepresentative_ae_of_gradientFree
    (F : StokesEnergyForce (vec3Ball 0 1)) (hF : F ∈ unitBallGradientFreeForce) :
    harmonicSpatialPressureRepresentative F =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))]
      (unitBallStokesPressure F : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) := by
  let G : unitBallGradientFreeForce := ⟨F, hF⟩
  have he : unitBallGradientFreeForceProjection F = G :=
    unitBallGradientFreeForceProjection_of_gradientFree G
  unfold harmonicSpatialPressureRepresentative
  rw [he]
  exact (unitBallHarmonicForcePressureRepresentative_pressure_ae G).symm

/-- The actual momentum pressure difference is the literal two Stokes pressures plus mean. -/
theorem unitBall_projected_pressure_identification_ae
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t : ℝ)
    (hp : MemLp (centeredPressureSlice p 0 1 t) 2 (volume.restrict (vec3Ball 0 1)))
    (hG : unitBallMomentumForceCurve u Du p t ∈ unitBallGradientFreeForce) :
    (fun x ↦ p (x, t) -
      harmonicSpatialPressureRepresentative (-unitBallMomentumForceCurve u Du p t) x)
      =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))]
    (fun x ↦ (unitBallConvectivePressureCurve u t :
        Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x +
      (unitBallViscousPressureCurve Du t : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x +
        average (volume.restrict (vec3Ball 0 1)) (fun y ↦ p (y, t))) := by
  let P0 := (unitBallActualPressureCurve p t : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))
  let P1 := (unitBallConvectivePressureCurve u t : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))
  let P2 := (unitBallViscousPressureCurve Du t : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))
  have hpress : (unitBallStokesPressure (-unitBallMomentumForceCurve u Du p t) :
      Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) = P0 - P1 - P2 := by
    exact congrArg Subtype.val (unitBallMomentumForceCurve_negative_pressure u Du p t)
  have hrep := harmonicSpatialPressureRepresentative_ae_of_gradientFree
    (-unitBallMomentumForceCurve u Du p t) (unitBallGradientFreeForce.neg_mem hG)
  rw [hpress] at hrep
  have hsub : vec3Ball (0 : Vec3) (1 / 4) ⊆ vec3Ball 0 1 := vec3Ball_mono (by norm_num)
  have h0 := ae_restrict_of_ae_restrict_of_subset hsub (unitBallActualPressureCurve_ae hp)
  have h1 := ae_restrict_of_ae_restrict_of_subset hsub (Lp.coeFn_sub P0 P1)
  have h2 := ae_restrict_of_ae_restrict_of_subset hsub (Lp.coeFn_sub (P0 - P1) P2)
  filter_upwards [hrep, h0, h1, h2] with x hx h0x h1x h2x
  change P0 x = p (x, t) - average (volume.restrict (vec3Ball 0 1))
    (fun y ↦ p (y, t)) at h0x
  change (P0 - P1) x = P0 x - P1 x at h1x
  change (P0 - P1 - P2) x = (P0 - P1) x - P2 x at h2x
  have he : harmonicSpatialPressureRepresentative
      (-unitBallMomentumForceCurve u Du p t) x = P0 x - P1 x - P2 x :=
    hx.trans (h2x.trans (congrArg (fun a : ℝ ↦ a - P2 x) h1x))
  change p (x, t) - harmonicSpatialPressureRepresentative
    (-unitBallMomentumForceCurve u Du p t) x = P1 x + P2 x + _
  linear_combination -h0x - he

/-- Actual suitable solutions identify the projected pressure on one common full time set. -/
theorem suitable_unitBall_projected_pressure_identification_ae
    {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      (fun x ↦ p (x, t) -
        harmonicSpatialPressureRepresentative (-unitBallMomentumForceCurve u Du p t) x)
        =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))]
      (fun x ↦ (unitBallConvectivePressureCurve u t :
          Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x +
        (unitBallViscousPressureCurve Du t : Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) x +
          average (volume.restrict (vec3Ball 0 1)) (fun y ↦ p (y, t))) := by
  obtain ⟨_, _, _, _, hp, _⟩ := exists_suitable_pressure_energy_dual hsol
    ((0, t₀) : ParabolicPoint) (by norm_num : (0 : ℝ) < 1)
    (by simpa only [mul_one] using hdom)
  have hpa : ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      MemLp (centeredPressureSlice p 0 1 t) 2 (volume.restrict (vec3Ball 0 1)) := by
    simpa only [Prod.fst, Prod.snd, mul_one, show (2 : ℝ) ^ 2 = 4 by norm_num] using hp
  filter_upwards [hpa, suitable_unitBall_momentumForce_gradientFree_ae hsol hdom]
    with t hpt hGt
  exact unitBall_projected_pressure_identification_ae u Du p t hpt hGt

end FluidSingularSets
