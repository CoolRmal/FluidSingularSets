-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallPressureProjection
public import FluidSingularSets.StokesEnergyVelocity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Genuine weak time derivatives and local pressure projection

Weak time differentiation is defined by actual compactly supported scalar
Bochner tests. A bounded linear operator preserves this identity. Scalar
pairings against a genuine dense test family suffice for the full energy-dual
identity. Applying the actual mean-zero ball pressure operator to a momentum
balance yields the genuine pressure-correction time derivative.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

-- Fix the canonical operator-space instance before elaborating the generalized integral.
local instance weakTimeForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The actual distributional time derivative of a vector-valued function. -/
def HasWeakTimeDerivativeOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Set ℝ) (f g : ℝ → E) : Prop :=
  ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → tsupport η ⊆ I →
    (∫ t in I, deriv η t • f t) = -(∫ t in I, η t • g t)

/-- Compact continuous scalar multiplication preserves genuine integrability. -/
theorem integrable_smul_compact_time_test {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {I : Set ℝ} {f : ℝ → E}
    (hf : IntegrableOn f I volume) {η : ℝ → ℝ}
    (hη : Continuous η) (hηc : HasCompactSupport η) :
    IntegrableOn (fun t ↦ η t • f t) I volume := by
  obtain ⟨C, hC⟩ := hηc.exists_bound_of_continuous hη
  exact hf.bdd_smul C hη.aestronglyMeasurable (ae_of_all _ hC)

/-- The actual weak derivative commutes with any genuine bounded linear map. -/
theorem HasWeakTimeDerivativeOn.continuousLinearMap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {I : Set ℝ} {f g : ℝ → E} (h : HasWeakTimeDerivativeOn I f g)
    (hf : IntegrableOn f I volume) (hg : IntegrableOn g I volume) (L : E →L[ℝ] F) :
    HasWeakTimeDerivativeOn I (fun t ↦ L (f t)) (fun t ↦ L (g t)) := by
  intro η hη hηc hηs
  have hft := integrable_smul_compact_time_test hf
    (hη.continuous_deriv (by simp)) hηc.deriv
  have hgt := integrable_smul_compact_time_test hg hη.continuous hηc
  calc
    (∫ t in I, deriv η t • L (f t)) = L (∫ t in I, deriv η t • f t) := by
      simpa only [map_smul] using L.integral_comp_comm hft
    _ = L (-(∫ t in I, η t • g t)) := congrArg L (h η hη hηc hηs)
    _ = -(∫ t in I, η t • L (g t)) := by
      rw [map_neg]
      congr 1
      simpa only [map_smul] using (L.integral_comp_comm hgt).symm

/-- True AE equality changes neither tested weak derivative integral. -/
theorem HasWeakTimeDerivativeOn.congr_ae {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {I : Set ℝ} {f g f' g' : ℝ → E}
    (h : HasWeakTimeDerivativeOn I f g)
    (hf : f =ᵐ[volume.restrict I] f') (hg : g =ᵐ[volume.restrict I] g') :
    HasWeakTimeDerivativeOn I f' g' := by
  intro η hη hηc hηs
  calc
    (∫ t in I, deriv η t • f' t) = (∫ t in I, deriv η t • f t) := by
      apply integral_congr_ae
      filter_upwards [hf] with t ht
      rw [ht]
    _ = -(∫ t in I, η t • g t) := h η hη hηc hηs
    _ = -(∫ t in I, η t • g' t) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hg] with t ht
      rw [ht]

/-- Genuine scalar weak time pairings on an actual dense family imply the complete
energy-dual weak derivative identity. No full-dual derivative premise is needed. -/
theorem hasWeakTimeDerivativeOn_of_dense_pairings
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {j : A → E} (hj : DenseRange j) {I : Set ℝ} {f g : ℝ → E →L[ℝ] ℝ}
    (hf : IntegrableOn f I volume) (hg : IntegrableOn g I volume)
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ I → ∀ a : A,
        (∫ t in I, deriv η t * f t (j a)) = -(∫ t in I, η t * g t (j a))) :
    HasWeakTimeDerivativeOn I f g := by
  intro η hη hηc hηs
  have hft := integrable_smul_compact_time_test hf
    (hη.continuous_deriv (by simp)) hηc.deriv
  have hgt := integrable_smul_compact_time_test hg hη.continuous hηc
  have heq := hj.equalizer
    (∫ t in I, deriv η t • f t).continuous
    (-(∫ t in I, η t • g t)).continuous (by
      funext a
      simp only [Function.comp_apply, ContinuousLinearMap.integral_apply hft,
        ContinuousLinearMap.integral_apply hgt, smul_apply, smul_eq_mul, neg_apply]
      exact hweak η hη hηc hηs a)
  exact ContinuousLinearMap.ext fun v ↦ congrFun heq v

/-- The genuine compact smooth ball tests suffice for the energy-dual evolution. -/
theorem hasWeakTimeDerivativeOn_stokes_of_compact_pairings
    {U : Set Vec3} {I : Set ℝ} {f g : ℝ → StokesEnergyForce U}
    (hf : IntegrableOn f I volume) (hg : IntegrableOn g I volume)
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ I → ∀ φ : StokesVectorTest U,
        (∫ t in I, deriv η t * f t (stokesEnergyTest φ)) =
          -(∫ t in I, η t * g t (stokesEnergyTest φ))) :
    HasWeakTimeDerivativeOn I f g := by
  apply hasWeakTimeDerivativeOn_of_dense_pairings (stokesSmoothEnergy_dense U) hf hg
  intro η hη hηc hηs φ
  exact hweak η hη hηc hηs (stokesSmoothToWeak φ)

/-- Applying the actual Stokes pressure to a true energy-dual momentum balance
identifies the actual pressure correction derivative, with the physical sign. -/
theorem weakTimeDerivative_projected_ball_pressure
    {I : Set ℝ} {F A B : ℝ → StokesEnergyForce (vec3Ball 0 1)}
    {p : ℝ → unitBallMeanZeroL2}
    (h : HasWeakTimeDerivativeOn I F (fun t ↦ A t + B t -
      stokesL2PressureGradient (p t : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))))
    (hF : IntegrableOn F I volume)
    (hbalance : IntegrableOn (fun t ↦ A t + B t -
      stokesL2PressureGradient (p t : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))) I volume) :
    HasWeakTimeDerivativeOn I (fun t ↦ -unitBallStokesPressure (F t))
      (fun t ↦ p t - unitBallStokesPressure (A t) - unitBallStokesPressure (B t)) := by
  have hmap := h.continuousLinearMap hF hbalance (-unitBallStokesPressureL)
  apply hmap.congr_ae
  · exact ae_of_all _ fun t ↦ rfl
  · apply ae_of_all
    intro t
    simp only [neg_apply, map_sub, map_add, unitBallStokesPressureL_apply,
      unitBallStokesPressure_pressureGradient]
    abel

end FluidSingularSets
