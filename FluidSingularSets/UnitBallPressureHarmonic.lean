-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallStokesPressure
public import FluidSingularSets.StokesGradientTest
public import CKN.Foundation.Harmonic.InteriorSmooth
public import CKN.Foundation.Parabolic.BallBasics

/-!
# Harmonicity of the actual constructed ball pressure

The pressure comes from the proved bounded ball divergence inverse and
the actual variational Stokes residual. Compact gradient testing proves
its distributional harmonicity for genuine divergence-free vector data.
-/

@[expose] public section

open CKN MeasureTheory Set
open CKN.Foundation.Parabolic CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The literal spatial representative of the genuinely constructed Stokes pressure. -/
def unitBallPressureFunction (F : StokesEnergyForce (vec3Ball 0 1)) : Vec3 → ℝ :=
  (unitBallStokesPressure F : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))

/-- The actual physical pressure satisfies the true completed variational Stokes equation. -/
theorem unitBallStokesPressure_variational (F : StokesEnergyForce (vec3Ball 0 1))
    (v : stokesGradientEnergySpace (vec3Ball 0 1)) :
    inner ℝ (stokesEnergySolution F : stokesGradientEnergySpace (vec3Ball 0 1)) v -
      inner ℝ (unitBallStokesPressure F : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))
        (stokesEnergyDivergence (vec3Ball 0 1) v) = F v := by
  have h := unitBallStokesPressure_pairing F v
  change -(inner ℝ (unitBallStokesPressure F : Lp ℝ 2
    (volume.restrict (vec3Ball 0 1))) (stokesEnergyDivergence (vec3Ball 0 1) v)) =
      F v - inner ℝ (stokesEnergySolution F : stokesGradientEnergySpace (vec3Ball 0 1)) v at h
  linarith

/-- Gradient-free actual forces produce a genuinely weakly harmonic constructed pressure. -/
theorem unitBallStokesPressure_weaklyHarmonic (F : StokesEnergyForce (vec3Ball 0 1))
    (hF : ∀ ψ : WeakTestFunction (vec3Ball 0 1),
      F (stokesEnergyTest (stokesScalarGradientTest ψ)) = 0) :
    WeaklyHarmonicOn (vec3Ball 0 1) (unitBallPressureFunction F) :=
  stokesPressure_weaklyHarmonic_of_gradient_tests F (unitBallStokesPressure F)
    (unitBallStokesPressure_variational F) hF

/-- Literal divergence-free vector source data produce the actual harmonic ball pressure. -/
theorem unitBallStokesPressure_weaklyHarmonic_of_vector_source
    (u : Vec3 → Vec3) (F : StokesEnergyForce (vec3Ball 0 1))
    (hforce : ∀ φ : StokesVectorTest (vec3Ball 0 1), F (stokesEnergyTest φ) =
      ∫ x in vec3Ball 0 1, ∑ i : Fin 3, u x i * φ i x)
    (hdiv : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball 0 1 →
        (∫ x in vec3Ball 0 1, ∑ i : Fin 3, u x i * spatialDeriv ψ i x) = 0) :
    WeaklyHarmonicOn (vec3Ball 0 1) (unitBallPressureFunction F) :=
  stokesPressure_weaklyHarmonic_of_divergenceFree_source u F (unitBallStokesPressure F)
    (unitBallStokesPressure_variational F) hforce hdiv

/-- Genuine lower-exponent pressure integrability for CKN's Weyl theorem. -/
theorem unitBallPressureFunction_memLp_threeHalves (F : StokesEnergyForce (vec3Ball 0 1)) :
    MemLp (unitBallPressureFunction F) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball 0 1)) :=
  (Lp.memLp (unitBallStokesPressure F : Lp ℝ 2
    (volume.restrict (vec3Ball 0 1)))).mono_exponent
    (by norm_num)

/-- The actual constructed pressure has a true interior C¹ representative. -/
theorem exists_unitBallStokesPressure_C1_representative
    (F : StokesEnergyForce (vec3Ball 0 1))
    (hF : ∀ ψ : WeakTestFunction (vec3Ball 0 1),
      F (stokesEnergyTest (stokesScalarGradientTest ψ)) = 0) :
    ∃ H : Vec3 → ℝ, ContDiffOn ℝ (1 : ℕ∞) H (vec3Ball 0 (1 / 2)) ∧
      unitBallPressureFunction F =ᵐ[volume.restrict (vec3Ball 0 (1 / 2))] H := by
  have hmem := unitBallPressureFunction_memLp_threeHalves F
  have hweak := unitBallStokesPressure_weaklyHarmonic F hF
  rw [← euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1)] at hmem hweak
  obtain ⟨H, hH, hae, _hval, _hgrad⟩ := weakly_harmonic_interior_smooth
    (by norm_num : (0 : ℝ) < 1) hmem hweak
  rw [euclideanBall_eq_vec3Ball (by norm_num : (0 : ℝ) < 1 / 2)] at hH hae
  exact ⟨H, hH, hae⟩

end FluidSingularSets
