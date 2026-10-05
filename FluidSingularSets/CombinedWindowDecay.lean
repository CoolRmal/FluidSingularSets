-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.SymmetricMixedDecay

/-!
# Genuine combined velocity-pressure decay on arbitrary time windows

The mean-subtracted velocity bound and the harmonic-pressure decomposition give
one scale estimate with an actual mixed-gradient source and one universal constant.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The real mixed-gradient source of the cubic oscillation estimate. -/
def mixedOscillationSource (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) (ρ : ℝ) : ℝ :=
  criticalVectorCubicOscillationConstant.toReal *
    (timeSliceEnergyEssSup z.1 z.2 (2 * ρ)
      (fun w ↦ vec3EuclideanNorm (u w))).toReal ^ (1 / 2 : ℝ) *
    (∫⁻ s in Ioc (z.2 - (2 * ρ) ^ 2) z.2,
      eLpNorm (fun x ↦ Du (x, s)) (12 / 7)
        (volume.restrict (vec3Ball z.1 (2 * ρ))) ^ (2 : ℝ)).toReal

/-- The source is nonnegative at every radius. -/
theorem mixedOscillationSource_nonneg (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) (ρ : ℝ) :
    0 ≤ mixedOscillationSource u Du z ρ := by
  unfold mixedOscillationSource
  positivity

/-- The genuine pressure source bound is a real inequality with finite gradient
mass, rather than an extended-real statement with a potentially infinite right side. -/
theorem suitablePressureChatMixedBound_real
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 (4 * ρ)) ⊆ spaceTimeSet Ω I) :
    pressureChat u z ρ ≤ ρ⁻¹ ^ 2 * mixedOscillationSource u Du z ρ := by
  have hsub₂ : closure (parabolicCylinder z.1 z.2 (2 * ρ)) ⊆ spaceTimeSet Ω I :=
    (closure_mono (parabolicCylinder_mono (by positivity)
      (by linarith only [hρ]))).trans hsub
  have hE : timeSliceEnergyEssSup z.1 z.2 (2 * ρ)
      (fun w ↦ vec3EuclideanNorm (u w)) ≠ ⊤ :=
    (sws_timeSliceEnergyEssSup_lt_top hsol (by positivity) hsub₂).ne
  have hM := (suitableMixedGradientCylinderData hsol (by positivity) hsub₂).2.ne
  have hfinite : ENNReal.ofReal (ρ⁻¹ ^ 2) * criticalVectorCubicOscillationConstant *
      timeSliceEnergyEssSup z.1 z.2 (2 * ρ) (fun w ↦ vec3EuclideanNorm (u w)) ^
        (1 / 2 : ℝ) *
      (∫⁻ s in Ioc (z.2 - (2 * ρ) ^ 2) z.2,
        eLpNorm (fun x ↦ Du (x, s)) (12 / 7)
          (volume.restrict (vec3Ball z.1 (2 * ρ))) ^ (2 : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top criticalVectorCubicOscillationConstant_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hE)) hM
  have hChat : 0 ≤ pressureChat u z ρ := by
    unfold pressureChat
    exact mul_nonneg (sq_nonneg _)
      (integral_nonneg (fun _ ↦ pow_nonneg (vec3EuclideanNorm_nonneg _) 3))
  have h := ENNReal.toReal_mono hfinite (suitablePressureChatMixedBound hsol hρ hsub)
  simpa only [mixedOscillationSource, ENNReal.toReal_mul, ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hChat, ENNReal.toReal_ofReal (sq_nonneg _), mul_assoc] using h

/-- The universal coefficient in combined cubic velocity-pressure decay. -/
def combinedWindowDecayConstant : ℝ := 4 + lin34AbsoluteConstant

/-- The combined coefficient is strictly positive and independent of the solution. -/
theorem combinedWindowDecayConstant_pos : 0 < combinedWindowDecayConstant := by
  have hC : 0 ≤ lin34AbsoluteConstant :=
    (lin34PointwiseConstant_nonneg lin34CZConstant_nonneg).trans (le_max_left _ _)
  unfold combinedWindowDecayConstant
  linarith

/-- The genuine velocity-pressure decomposition on every smaller time window,
with explicit mean decay and the actual mixed-gradient source. -/
theorem suitableCombinedTimeWindowDecay
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 (4 * ρ)) ⊆ spaceTimeSet Ω I)
    {J : Set ℝ} (hJ : J ⊆ Ioc (z.2 - ρ ^ 2) z.2) :
    r⁻¹ ^ 2 * ((∫ s in J, ∫ x in vec3Ball z.1 r,
      vec3EuclideanNorm (u (x, s)) ^ (3 : ℕ)) +
      ∫ s in J, ∫ x in vec3Ball z.1 r, |p (x, s)| ^ (3 / 2 : ℝ)) ≤
    combinedWindowDecayConstant *
      ((r / ρ) * ρ⁻¹ ^ 2 * ((∫ s in Ioc (z.2 - ρ ^ 2) z.2,
        ∫ x in vec3Ball z.1 ρ, vec3EuclideanNorm (u (x, s)) ^ (3 : ℕ)) +
        ∫ s in Ioc (z.2 - ρ ^ 2) z.2,
          ∫ x in vec3Ball z.1 ρ, |p (x, s)| ^ (3 / 2 : ℝ)) +
      r⁻¹ ^ 2 * mixedOscillationSource u Du z ρ) := by
  have hrρ : r ≤ ρ := by linarith only [hhalf, hρ]
  have hsubρ : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I :=
    (closure_mono (parabolicCylinder_mono hρ.le (by linarith only [hρ]))).trans hsub
  have hvel : (∫ s in J, ∫ x in vec3Ball z.1 r,
      vec3EuclideanNorm (u (x, s)) ^ (3 : ℕ)) ≤
      4 * mixedOscillationSource u Du z ρ +
      4 * (r / ρ) ^ (3 : ℕ) * ∫ s in Ioc (z.2 - ρ ^ 2) z.2,
        ∫ x in vec3Ball z.1 ρ, vec3EuclideanNorm (u (x, s)) ^ (3 : ℕ) := by
    simpa only [mixedOscillationSource, mul_assoc] using
      suitableVelocityTimeWindowMixedMassDecay_real hsol hρ hr hrρ hsub hJ
  have hpres := suitablePressureTimeWindowDecay hsol hρ hr hhalf hsubρ hJ
  rw [integral_const_mul] at hpres
  have hC : 0 ≤ lin34AbsoluteConstant :=
    (lin34PointwiseConstant_nonneg lin34CZConstant_nonneg).trans (le_max_left _ _)
  have hD : pressureD p z ρ = ρ⁻¹ ^ 2 *
      ∫ s in Ioc (z.2 - ρ ^ 2) z.2,
        ∫ x in vec3Ball z.1 ρ, |p (x, s)| ^ (3 / 2 : ℝ) := by
    rw [lin34_pressureD_eq_integral hsol hρ hsubρ]
    exact integral_const_mul _ _
  have hpres' : r⁻¹ ^ 2 * (∫ s in J, ∫ x in vec3Ball z.1 r,
        |p (x, s)| ^ (3 / 2 : ℝ)) ≤
      lin34AbsoluteConstant *
        ((ρ / r) ^ 2 * (ρ⁻¹ ^ 2 * mixedOscillationSource u Du z ρ) +
        (r / ρ) * (ρ⁻¹ ^ 2 * ∫ s in Ioc (z.2 - ρ ^ 2) z.2,
          ∫ x in vec3Ball z.1 ρ, |p (x, s)| ^ (3 / 2 : ℝ))) := by
    rw [← hD]
    apply hpres.trans
    apply mul_le_mul_of_nonneg_left _ hC
    exact add_le_add (mul_le_mul_of_nonneg_left
      (suitablePressureChatMixedBound_real hsol hρ hsub) (sq_nonneg _)) le_rfl
  have hscale₁ : r⁻¹ ^ 2 * (r / ρ) ^ 3 = (r / ρ) * ρ⁻¹ ^ 2 := by
    field_simp
  have hscale₂ : (ρ / r) ^ 2 * ρ⁻¹ ^ 2 = r⁻¹ ^ 2 := by
    field_simp
  have hV : 0 ≤ ∫ s in Ioc (z.2 - ρ ^ 2) z.2,
      ∫ x in vec3Ball z.1 ρ, vec3EuclideanNorm (u (x, s)) ^ (3 : ℕ) :=
    integral_nonneg (fun _ ↦ integral_nonneg
      (fun _ ↦ pow_nonneg (vec3EuclideanNorm_nonneg _) 3))
  have hP : 0 ≤ ∫ s in Ioc (z.2 - ρ ^ 2) z.2,
      ∫ x in vec3Ball z.1 ρ, |p (x, s)| ^ (3 / 2 : ℝ) :=
    integral_nonneg (fun _ ↦ integral_nonneg (fun _ ↦ by positivity))
  have hratio : 0 ≤ r / ρ := div_nonneg hr.le hρ.le
  have hvel' : r⁻¹ ^ 2 * (∫ s in J, ∫ x in vec3Ball z.1 r,
      vec3EuclideanNorm (u (x, s)) ^ (3 : ℕ)) ≤
      4 * r⁻¹ ^ 2 * mixedOscillationSource u Du z ρ +
      4 * (r / ρ) * ρ⁻¹ ^ 2 * ∫ s in Ioc (z.2 - ρ ^ 2) z.2,
        ∫ x in vec3Ball z.1 ρ, vec3EuclideanNorm (u (x, s)) ^ (3 : ℕ) := by
    apply (mul_le_mul_of_nonneg_left hvel (sq_nonneg r⁻¹)).trans_eq
    calc
      _ = 4 * r⁻¹ ^ 2 * mixedOscillationSource u Du z ρ +
          4 * (r⁻¹ ^ 2 * (r / ρ) ^ 3) *
          (∫ s in Ioc (z.2 - ρ ^ 2) z.2,
            ∫ x in vec3Ball z.1 ρ, vec3EuclideanNorm (u (x, s)) ^ (3 : ℕ)) := by ring
      _ = _ := by rw [hscale₁]; ring
  rw [← mul_assoc ((ρ / r) ^ 2) (ρ⁻¹ ^ 2) (mixedOscillationSource u Du z ρ),
    hscale₂] at hpres'
  have hbound := add_le_add hvel' hpres'
  unfold combinedWindowDecayConstant
  have hextra₁ : 0 ≤ lin34AbsoluteConstant * (r / ρ) * ρ⁻¹ ^ 2 *
      (∫ s in Ioc (z.2 - ρ ^ 2) z.2,
        ∫ x in vec3Ball z.1 ρ, vec3EuclideanNorm (u (x, s)) ^ (3 : ℕ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hratio) (sq_nonneg _)) hV
  have hextra₂ : 0 ≤ 4 * (r / ρ) * ρ⁻¹ ^ 2 *
      (∫ s in Ioc (z.2 - ρ ^ 2) z.2,
        ∫ x in vec3Ball z.1 ρ, |p (x, s)| ^ (3 / 2 : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hratio) (sq_nonneg _)) hP
  nlinarith only [hbound, hextra₁, hextra₂]

end FluidSingularSets
