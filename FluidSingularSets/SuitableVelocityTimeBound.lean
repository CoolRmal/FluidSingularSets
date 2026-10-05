-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.HarmonicTimeSmoothApprox

/-!
# Actual uniform time bounds from suitable slice energy

The original S1 slice-energy supremum controls the genuine conditional spatial
L² classes. Their strong measurability comes from the actual joint velocity.
Bounded Stokes operators then give genuine uniform time bounds for the velocity
force, harmonic pressure class, and continuous harmonic-gradient correction.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual L² slice class is bounded by the square root of its literal energy,
including the exceptional zero branch of the conditional class. -/
theorem actualSliceLp_enorm_two_le_sliceEnergy
    {A T E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    {μ : Measure A} (F : A × T → E) (t : T) :
    ‖actualSliceLp (μ := μ) (p := 2) F t‖ₑ ≤
      (∫⁻ x, ‖F (x, t)‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  by_cases ht : MemLp (fun x ↦ F (x, t)) 2 μ
  · rw [actualSliceLp_enorm F t ht,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        ht.aestronglyMeasurable]
    norm_num only [ENNReal.toReal_ofNat]
    exact le_rfl
  · simp only [actualSliceLp, dite_eq_right ht, enorm_zero]
    exact bot_le

/-- Joint actual measurability and the genuine slice-energy supremum control the
uniform time seminorm of the actual spatial L² class curve. -/
theorem actualSliceLp_eLpNorm_top_le_sliceEnergy
    {A T E : Type*} [MeasurableSpace A] [MeasurableSpace T]
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure A} [SFinite μ] [IsSeparable μ] {ν : Measure T} [SFinite ν]
    {F : A × T → E} (hF : AEStronglyMeasurable F (μ.prod ν)) :
    eLpNorm (actualSliceLp (μ := μ) (p := 2) F) ⊤ ν ≤
      (essSup (fun t ↦ ∫⁻ x, ‖F (x, t)‖ₑ ^ (2 : ℝ) ∂μ) ν) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_exponent_top (aestronglyMeasurable_actualSliceLp hF (by norm_num))]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  filter_upwards [ENNReal.ae_le_essSup
    (fun t ↦ ∫⁻ x, ‖F (x, t)‖ₑ ^ (2 : ℝ) ∂μ)] with t ht
  exact (actualSliceLp_enorm_two_le_sliceEnergy F t).trans
    (ENNReal.rpow_le_rpow ht (by norm_num))

/-- Actual finite S1 slice energy gives the true time `L∞` class membership. -/
theorem actualSliceLp_memLp_top_of_sliceEnergy
    {A T E : Type*} [MeasurableSpace A] [MeasurableSpace T]
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure A} [SFinite μ] [IsSeparable μ] {ν : Measure T} [SFinite ν]
    {F : A × T → E} (hF : AEStronglyMeasurable F (μ.prod ν))
    (henergy : essSup (fun t ↦ ∫⁻ x, ‖F (x, t)‖ₑ ^ (2 : ℝ) ∂μ) ν < ⊤) :
    MemLp (actualSliceLp (μ := μ) (p := 2) F) ⊤ ν :=
  (actualSliceLp_eLpNorm_top_le_sliceEnergy hF).trans_lt
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) henergy.ne)

local instance suitableVelocityTimeBoundForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance suitableVelocityTimeBoundForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

section Suitable

variable {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
  {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

/-- Literal suitable S1 data controls the actual uniform time velocity-class norm. -/
theorem suitable_velocityCurve_eLpNorm_top_le
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    eLpNorm (unitBallVelocityCurve u) ⊤ (volume.restrict J) ≤
      (essSup (fun t ↦ ∫⁻ x in vec3Ball 0 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
        (volume.restrict J)) ^ (1 / 2 : ℝ) := by
  have hprod : AEStronglyMeasurable u
      ((volume.restrict (vec3Ball 0 1)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict,
      ← CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    exact hsol.toData.aestronglyMeasurable_velocity hbox
  exact actualSliceLp_eLpNorm_top_le_sliceEnergy hprod

/-- The actual spatial velocity class is time `L∞`, directly from suitable S1. -/
theorem suitable_velocityCurve_memLp_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    MemLp (unitBallVelocityCurve u) ⊤ (volume.restrict J) :=
  (suitable_velocityCurve_eLpNorm_top_le hsol hbox).trans_lt
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (hsol.toData.essSup_sliceEnergy_lt_top hbox).ne)

/-- The true completed velocity force in weak momentum is uniformly bounded in time. -/
theorem suitable_velocityForceCurve_memLp_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    MemLp (unitBallVelocityForceCurve u) ⊤ (volume.restrict J) :=
  (suitable_velocityCurve_memLp_top hsol hbox).continuousLinearMap_comp
    (stokesVectorForceL (vec3Ball 0 1))

/-- The true Euclidean Hilbert velocity class has the same genuine time bound. -/
theorem suitable_hilbertVelocityCurve_memLp_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    MemLp (unitBallHilbertVelocityCurve u) ⊤ (volume.restrict J) :=
  (suitable_velocityCurve_memLp_top hsol hbox).continuousLinearMap_comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).symm.toContinuousLinearMap.compLpL
      2 (volume.restrict (vec3Ball 0 1)))

/-- The genuine harmonic pressure class is uniformly time bounded in spatial L². -/
theorem suitable_harmonicPressureCurve_memLp_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    MemLp (unitBallHarmonicPressureCurve u) ⊤ (volume.restrict J) := by
  change MemLp (fun t ↦ -unitBallStokesPressure (unitBallVelocityForceCurve u t))
    ⊤ (volume.restrict J)
  exact ((suitable_velocityForceCurve_memLp_top hsol hbox).continuousLinearMap_comp
    unitBallStokesPressureL).neg

/-- The genuine continuous spatial harmonic-gradient correction is time `L∞`. -/
theorem suitable_harmonicGradientTimeCurve_memLp_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    MemLp (unitBallHarmonicGradientTimeCurve u) ⊤ (volume.restrict J) := by
  change MemLp (fun t ↦ -unitBallHarmonicForceGradientExtended (unitBallVelocityForceCurve u t))
    ⊤ (volume.restrict J)
  exact ((suitable_velocityForceCurve_memLp_top hsol hbox).continuousLinearMap_comp
    unitBallHarmonicForceGradientExtended).neg

/-- The actual spatial-source harmonic-gradient class is genuinely uniform in time. -/
theorem suitable_sourceHarmonicGradient_memLp_top
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    MemLp (fun t ↦ -unitBallHarmonicGradientExtended (unitBallHilbertVelocityCurve u t))
      ⊤ (volume.restrict J) :=
  ((suitable_hilbertVelocityCurve_memLp_top hsol hbox).continuousLinearMap_comp
    unitBallHarmonicGradientExtended).neg

end Suitable

private theorem suitableVelocityTimeBound_localBox
    {Ω : Set Vec3} {I : Set ℝ} {t₀ : ℝ}
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    localBox Ω I (vec3Ball 0 1) (Ioo (t₀ - 4) (t₀ + 4)) := by
  have hb := CKN.Core.Endgame.localBox_of_parabolic_ball
    (z₀ := ((0, t₀) : ParabolicPoint)) (by norm_num : (0 : ℝ) < 2)
    ((Metric.ball_subset_ball (by norm_num : (2 : ℝ) * 2 ≤ 8)).trans hdom)
  have hB : localBox Ω I (vec3Ball 0 2) (Ioo (t₀ - 4) (t₀ + 4)) := by
    simpa only [Prod.fst, Prod.snd, show (2 : ℝ) ^ 2 = 4 by norm_num] using hb
  have hsub : vec3Ball (0 : Vec3) 1 ⊆ vec3Ball 0 2 := vec3Ball_mono (by norm_num)
  refine ⟨isOpen_vec3Ball 0 1, ?_, ?_, hB.2.2.2⟩
  · exact hB.2.1.of_isClosed_subset isClosed_closure (closure_mono hsub)
  · exact (closure_mono hsub).trans hB.2.2.1

/-- The actual continuous harmonic representative is uniformly time bounded,
with its membership derived from the true suitable velocity-force class. -/
theorem suitable_harmonicTimePrimitive_memLp_top
    {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    MemLp (unitBallHarmonicTimePrimitive u Du p t₀) ⊤
      (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) :=
  (memLp_congr_ae (suitable_unitBall_harmonicTimePrimitive_data hsol hdom).2.2.1).mp
    (suitable_harmonicGradientTimeCurve_memLp_top hsol
      (suitableVelocityTimeBound_localBox hdom))

/-- On a genuine interior suitable cylinder, the exact velocity and both actual
harmonic pressure/gradient correction classes are all uniformly time bounded. -/
theorem suitable_unitBall_velocity_and_harmonic_memLp_top
    {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    MemLp (unitBallVelocityCurve u) ⊤ (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ∧
      MemLp (unitBallVelocityForceCurve u) ⊤
        (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ∧
      MemLp (unitBallHarmonicPressureCurve u) ⊤
        (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ∧
      MemLp (unitBallHarmonicGradientTimeCurve u) ⊤
        (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) ∧
      MemLp (unitBallHarmonicTimePrimitive u Du p t₀) ⊤
        (volume.restrict (Ioo (t₀ - 4) (t₀ + 4))) := by
  have hbox := suitableVelocityTimeBound_localBox hdom
  exact ⟨suitable_velocityCurve_memLp_top hsol hbox,
    suitable_velocityForceCurve_memLp_top hsol hbox,
    suitable_harmonicPressureCurve_memLp_top hsol hbox,
    suitable_harmonicGradientTimeCurve_memLp_top hsol hbox,
    suitable_harmonicTimePrimitive_memLp_top hsol hdom⟩

end FluidSingularSets
