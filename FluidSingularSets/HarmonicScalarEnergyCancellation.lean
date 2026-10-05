-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.SmoothHarmonicMomentum
public import FluidSingularSets.SmoothProjectedPressureCancellation

/-!
# Genuine scalar harmonic energy correction cancellations

The tested spatial cross terms vanish by the actual suitable weak gradient.
The smooth square correction vanishes after including its true time derivative.
All constituent densities are proved integrable before these exact integral
identities are combined. These are the scalar building blocks of the projected
local energy inequality.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The true integral of a three-term linear combination of integrable scalar fields. -/
theorem integral_three_scalar_terms {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {F G H : A → ℝ} (hF : Integrable F μ) (hG : Integrable G μ)
    (hH : Integrable H μ) (a b c : ℝ) :
    (∫ x, a * F x - b * G x - c * H x ∂μ) =
      a * (∫ x, F x ∂μ) - b * (∫ x, G x ∂μ) - c * (∫ x, H x ∂μ) := by
  have hFG : (∫ x, a * F x - b * G x ∂μ) =
      (∫ x, a * F x ∂μ) - (∫ x, b * G x ∂μ) :=
    integral_sub (hF.const_mul a) (hG.const_mul b)
  calc
    _ = (∫ x, a * F x - b * G x ∂μ) - (∫ x, c * H x ∂μ) :=
      integral_sub ((hF.const_mul a).sub (hG.const_mul b)) (hH.const_mul c)
    _ = _ := by rw [hFG, integral_const_mul, integral_const_mul, integral_const_mul]

/-- The true integral of a four-term linear combination of integrable scalar fields. -/
theorem integral_four_scalar_terms {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {F G H K : A → ℝ} (hF : Integrable F μ) (hG : Integrable G μ)
    (hH : Integrable H μ) (hK : Integrable K μ) (a b c d : ℝ) :
    (∫ x, a * F x - b * G x - c * H x - d * K x ∂μ) =
      a * (∫ x, F x ∂μ) - b * (∫ x, G x ∂μ) - c * (∫ x, H x ∂μ) -
        d * (∫ x, K x ∂μ) := by
  calc
    _ = (∫ x, a * F x - b * G x - c * H x ∂μ) - (∫ x, d * K x ∂μ) :=
      integral_sub (((hF.const_mul a).sub (hG.const_mul b)).sub (hH.const_mul c))
        (hK.const_mul d)
    _ = _ := by rw [integral_three_scalar_terms hF hG hH, integral_const_mul]

/-- The actual harmonic spatial cross correction has zero compact-test integral. -/
theorem suitable_harmonic_spatial_energy_correction_zero
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {H ψ : Vec3 × ℝ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hh : ∀ z ∈ tsupport ψ, (∑ j : Fin 3, spatialSecondPartial H j j z) = 0)
    (i : Fin 3) :
    Integrable (fun z : Vec3 × ℝ ↦
      2 * (∑ j : Fin 3, Du z i j * spatialPartial H j z) * ψ z -
        2 * u z i * H z * (∑ j : Fin 3, spatialSecondPartial ψ j j z) -
          2 * (∑ j : Fin 3, Du z i j * H z * spatialPartial ψ j z)) volume ∧
      (∫ z : Vec3 × ℝ,
        2 * (∑ j : Fin 3, Du z i j * spatialPartial H j z) * ψ z -
          2 * u z i * H z * (∑ j : Fin 3, spatialSecondPartial ψ j j z) -
            2 * (∑ j : Fin 3, Du z i j * H z * spatialPartial ψ j z)) = 0 := by
  let A : Vec3 × ℝ → ℝ := fun z ↦
    (∑ j : Fin 3, Du z i j * spatialPartial H j z) * ψ z
  let B : Vec3 × ℝ → ℝ := fun z ↦
    u z i * H z * (∑ j : Fin 3, spatialSecondPartial ψ j j z)
  let C : Vec3 × ℝ → ℝ := fun z ↦
    ∑ j : Fin 3, Du z i j * H z * spatialPartial ψ j z
  let D : Vec3 × ℝ → ℝ := fun z ↦
    ∑ j : Fin 3, u z i * spatialPartial H j z * spatialPartial ψ j z
  have hgrad := suitable_harmonic_gradient_cross_pairing hsol hH hψ hh i
  have hlap := suitable_smooth_cross_laplacian_pairing hsol hH hψ i
  have hA : Integrable A volume := hgrad.1
  have hB : Integrable B volume := hlap.1
  have hC : Integrable C volume := hlap.2.1
  have hpairA : (∫ z, A z) = -(∫ z, D z) := hgrad.2.2
  have hpairB : (∫ z, B z) = -(∫ z, C z) - (∫ z, D z) := hlap.2.2.2
  have hfun : (fun z : Vec3 × ℝ ↦
      2 * (∑ j : Fin 3, Du z i j * spatialPartial H j z) * ψ z -
        2 * u z i * H z * (∑ j : Fin 3, spatialSecondPartial ψ j j z) -
          2 * (∑ j : Fin 3, Du z i j * H z * spatialPartial ψ j z)) =
      fun z ↦ 2 * A z - 2 * B z - 2 * C z := by
    funext z
    dsimp [A, B, C]
    ring
  rw [hfun]
  refine ⟨((hA.const_mul 2).sub (hB.const_mul 2)).sub (hC.const_mul 2), ?_⟩
  calc
    _ = 2 * (∫ z, A z) - 2 * (∫ z, B z) - 2 * (∫ z, C z) :=
      integral_three_scalar_terms hA hB hC 2 2 2
    _ = 0 := by linarith only [hpairA, hpairB]

/-- Genuine harmonic square and time integration by parts give zero scalar correction. -/
theorem smooth_harmonic_square_energy_correction_zero
    {H ψ : Vec3 × ℝ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ)
    (hh : ∀ z ∈ tsupport ψ, (∑ j : Fin 3, spatialSecondPartial H j j z) = 0) :
    Integrable (fun z : Vec3 × ℝ ↦
      2 * (∑ j : Fin 3, spatialPartial H j z ^ 2) * ψ z -
        H z ^ 2 * timePartial ψ z -
          H z ^ 2 * (∑ j : Fin 3, spatialSecondPartial ψ j j z) -
            2 * H z * timePartial H z * ψ z) volume ∧
      (∫ z : Vec3 × ℝ,
        2 * (∑ j : Fin 3, spatialPartial H j z ^ 2) * ψ z -
          H z ^ 2 * timePartial ψ z -
            H z ^ 2 * (∑ j : Fin 3, spatialSecondPartial ψ j j z) -
              2 * H z * timePartial H z * ψ z) = 0 := by
  let A : Vec3 × ℝ → ℝ := fun z ↦ (∑ j : Fin 3, spatialPartial H j z ^ 2) * ψ z
  let B : Vec3 × ℝ → ℝ := fun z ↦ H z ^ 2 * timePartial ψ z
  let C : Vec3 × ℝ → ℝ := fun z ↦ H z ^ 2 *
    (∑ j : Fin 3, spatialSecondPartial ψ j j z)
  let D : Vec3 × ℝ → ℝ := fun z ↦ H z * timePartial H z * ψ z
  have hInts := smooth_square_test_integrable hH hψ hcψ
  have hA : Integrable A volume := by
    have hAj (j : Fin 3) : Integrable
        (fun z : Vec3 × ℝ ↦ spatialPartial H j z ^ 2 * ψ z) volume := hInts.2.2.2 j
    have hsum := integrable_finsetSum Finset.univ fun j _ ↦ hAj j
    simpa only [A, Finset.sum_mul] using hsum
  have hB : Integrable B volume := hInts.1
  have hC : Integrable C volume := by
    have hsum := integrable_finsetSum Finset.univ fun j _ ↦ hInts.2.2.1 j
    simpa only [C, Finset.mul_sum] using hsum
  have hD : Integrable D volume := hInts.2.1
  have hpairB : (∫ z, B z) = -2 * (∫ z, D z) :=
    smooth_square_time_pairing hH hψ hcψ
  have hpairC : (∫ z, C z) = 2 * (∫ z, A z) :=
    smooth_harmonic_square_laplacian_pairing hH hψ hcψ hh
  have hfun : (fun z : Vec3 × ℝ ↦
      2 * (∑ j : Fin 3, spatialPartial H j z ^ 2) * ψ z -
        H z ^ 2 * timePartial ψ z -
          H z ^ 2 * (∑ j : Fin 3, spatialSecondPartial ψ j j z) -
            2 * H z * timePartial H z * ψ z) =
      fun z ↦ 2 * A z - B z - C z - 2 * D z := by
    funext z
    dsimp [A, B, C, D]
    ring
  rw [hfun]
  refine ⟨(((hA.const_mul 2).sub hB).sub hC).sub (hD.const_mul 2), ?_⟩
  have heq := integral_four_scalar_terms hA hB hC hD 2 1 1 2
  simp only [one_mul] at heq
  refine heq.trans ?_
  linarith only [hpairB, hpairC]

end FluidSingularSets
