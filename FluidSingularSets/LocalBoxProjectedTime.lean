-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.LocalBoxEnergyForces
public import FluidSingularSets.SuitableHarmonicSmoothApprox
public import FluidSingularSets.SuitableBallPressureHarmonic

/-!
# Actual projected time evolution on arbitrary local intervals

The original suitable momentum equation gives the full energy-dual evolution
on a local unit ball. Its genuine force primitive and harmonic correction use
the original interval, including its endpoint traces.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal Topology ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

local instance localBoxProjectedTimeForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance localBoxProjectedTimeForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The single true averaged force primitive on the original local interval. -/
def localBoxForcePrimitive (u : ParabolicPoint → Vec3)
    (D : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ) (a b c : ℝ) :
    ℝ → StokesEnergyForce (vec3Ball 0 1) :=
  averagedTimePrimitive (unitBallVelocityForceCurve u) (unitBallMomentumForceCurve u D p) a b c

/-- The physical negative harmonic correction of the actual force primitive. -/
def localBoxHarmonicTimePrimitive (u : ParabolicPoint → Vec3)
    (D : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ) (a b c t : ℝ) :
    C(unitBallPressureCompactInterior, Vec3) :=
  -unitBallHarmonicForceGradientExtended (localBoxForcePrimitive u D p a b c t)

section Suitable

variable {Ω : Set Vec3} {I J : Set ℝ} {q a b c : ℝ}
  {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

/-- All actual velocity and momentum force terms are Bochner integrable on the
original local interval. -/
theorem suitable_unitBall_momentumForces_integrable_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    IntegrableOn (unitBallVelocityForceCurve u) J volume ∧
      IntegrableOn (unitBallMomentumForceCurve u Du p) J volume := by
  obtain ⟨hF, hC, hV⟩ := suitable_energyForceCurves_integrable_localBox hsol hbox
  have hP := suitable_pressure_energy_force_memLp_localBox (by norm_num) hsol hbox
  let : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr
    ((measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top).ne
  exact ⟨hF, (hC.add hV).sub (hP.integrable (by norm_num))⟩

/-- The genuine full momentum evolution uses the supplied local interval. -/
theorem suitable_unitBall_momentum_hasWeakTimeDerivativeOn_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) :
    HasWeakTimeDerivativeOn (Ioo a b) (unitBallVelocityForceCurve u)
      (unitBallMomentumForceCurve u Du p) := by
  obtain ⟨hF, hG⟩ := suitable_unitBall_momentumForces_integrable_localBox hsol hbox
  apply suitable_energyDual_hasWeakTimeDerivativeOn_of_literal_pairings hsol hbox hF hG
  have hpAE := (suitable_centered_pressure_energy_dual_localBox (by norm_num) hsol hbox).1
  intro φ
  constructor
  · filter_upwards [slice_memLp_ae_of_sws hsol hbox] with t ht
    exact unitBallVelocityForceCurve_weightedMean_pair u t ht.1 φ
  · filter_upwards [suitable_unitBall_memLp_four_ae_localBox hsol hbox,
      slice_memLp_ae_of_sws hsol hbox, hpAE] with t hut hDt hpt
    exact unitBallMomentumForceCurve_weightedFlux_pair u Du p t hut hDt.2 hpt φ

/-- Actual suitable divergence identifies the Hilbert velocity source on the
entire original local interval. -/
theorem suitable_unitBall_hilbertVelocity_divergenceFree_ae_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    ∀ᵐ t ∂volume.restrict J,
      unitBallHilbertVelocityCurve u t ∈ unitBallDivergenceFreeL2 := by
  filter_upwards [slice_memLp_ae_of_sws hsol hbox,
    suitable_ball_divergenceFree_slices_ae hsol 0 1 hbox] with t ht hdiv
  apply (unitBallDivergenceFreeL2_mem_iff _).mpr
  intro ψ hψ hψc hψB
  rw [unitBallHilbertVelocityCurve_coordinates]
  calc
    _ = ∫ x in vec3Ball 0 1, ∑ i : Fin 3,
        u (x, t) i * spatialDeriv ψ i x := by
      apply integral_congr_ae
      filter_upwards [actualSliceLp_ae u t ht.1] with x hx
      change unitBallVelocityCurve u t x = u (x, t) at hx
      rw [hx]
    _ = 0 := hdiv ψ hψ hψc hψB

/-- Every true compact-gradient kernel contains the actual velocity force. -/
theorem suitable_unitBall_velocityForce_gradientFree_ae_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    ∀ᵐ t ∂volume.restrict J,
      unitBallVelocityForceCurve u t ∈ unitBallGradientFreeForce := by
  filter_upwards [suitable_unitBall_hilbertVelocity_divergenceFree_ae_localBox hsol hbox]
    with t ht
  intro ψ
  rw [← unitBallHilbertVelocityCurve_force]
  exact ht ψ

/-- The actual time momentum derivative preserves the genuine gradient-free
force space on the original open interval. -/
theorem suitable_unitBall_momentumForce_gradientFree_ae_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      unitBallMomentumForceCurve u Du p t ∈ unitBallGradientFreeForce := by
  obtain ⟨hF, hG⟩ := suitable_unitBall_momentumForces_integrable_localBox hsol hbox
  exact hasWeakTimeDerivativeOn_gradientFree_ae isOpen_Ioo
    (suitable_unitBall_momentum_hasWeakTimeDerivativeOn_localBox hsol hbox) hF hG
    (suitable_unitBall_velocityForce_gradientFree_ae_localBox hsol hbox)

/-- The actual harmonic correction is the same genuine spatial-source field
on almost every original time slice. -/
theorem suitable_unitBall_harmonicGradientTime_eq_source_ae_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    unitBallHarmonicGradientTimeCurve u =ᵐ[volume.restrict J]
      fun t ↦ -unitBallHarmonicGradientExtended (unitBallHilbertVelocityCurve u t) := by
  filter_upwards [suitable_unitBall_hilbertVelocity_divergenceFree_ae_localBox hsol hbox]
    with t ht
  let v : unitBallDivergenceFreeL2 := ⟨unitBallHilbertVelocityCurve u t, ht⟩
  change -unitBallHarmonicForceGradientExtended (unitBallVelocityForceCurve u t) = _
  rw [← unitBallHilbertVelocityCurve_force]
  rw [unitBallHarmonicForceGradientExtended_of_source v,
    unitBallHarmonicGradientExtended_of_divergenceFree v]

/-- The original suitable force agrees with its genuine continuous force
primitive; the anchor may be any interior point of the original interval. -/
theorem suitable_unitBall_velocityForce_ae_primitive_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b) :
    unitBallVelocityForceCurve u =ᵐ[volume.restrict (Ioo a b)]
      localBoxForcePrimitive u Du p a b c := by
  obtain ⟨hf, hg⟩ := suitable_unitBall_momentumForces_integrable_localBox hsol hbox
  exact weakTimeDerivative_ae_averagedTimePrimitive hab hc hf hg
    (suitable_unitBall_momentum_hasWeakTimeDerivativeOn_localBox hsol hbox)

/-- The actual harmonic correction has its genuine continuous AC primitive,
true derivative, and exact differences at all time endpoints. -/
theorem suitable_localBox_harmonicTimePrimitive_data
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b) :
    Continuous (localBoxHarmonicTimePrimitive u Du p a b c) ∧
      AbsolutelyContinuousOnInterval (localBoxHarmonicTimePrimitive u Du p a b c) a b ∧
      unitBallHarmonicGradientTimeCurve u =ᵐ[volume.restrict (Ioo a b)]
        localBoxHarmonicTimePrimitive u Du p a b c ∧
      (∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt
        (localBoxHarmonicTimePrimitive u Du p a b c)
          (unitBallHarmonicGradientTimeDerivative u Du p t) t) ∧
      ∀ s t : ℝ, localBoxHarmonicTimePrimitive u Du p a b c t -
        localBoxHarmonicTimePrimitive u Du p a b c s =
          ∫ v in s..t, (Ioo a b).indicator (unitBallHarmonicGradientTimeDerivative u Du p) v := by
  obtain ⟨hf, hg⟩ := suitable_unitBall_momentumForces_integrable_localBox hsol hbox
  exact operator_averagedTimePrimitive_data (-unitBallHarmonicForceGradientExtended)
    hab hc hf hg (suitable_unitBall_momentum_hasWeakTimeDerivativeOn_localBox hsol hbox)

/-- Genuine suitable force evolution constructs the actual smooth time force
sequence, with the original interval and true force constant. -/
theorem exists_suitable_unitBall_force_smooth_sequence_localBox
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b) :
    ∃ gs fs : ℕ → ℝ → StokesEnergyForce (vec3Ball 0 1),
      (∀ n, ContDiff ℝ ∞ (gs n) ∧ ContDiff ℝ ∞ (fs n) ∧
        HasCompactSupport (gs n) ∧ tsupport (gs n) ⊆ meanApproxTimeSet a b ∧
        MemLp (gs n) 1 volume ∧ (∀ t, HasDerivAt (fs n) (gs n t) t)) ∧
      unitBallVelocityForceCurve u =ᵐ[volume.restrict (Ioo a b)]
        localBoxForcePrimitive u Du p a b c ∧
      Tendsto (fun n ↦ eLpNorm ((Ioo a b).indicator (unitBallMomentumForceCurve u Du p) - gs n)
        1 volume) atTop (𝓝 0) ∧
      TendstoUniformly fs (localBoxForcePrimitive u Du p a b c) atTop ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n t, t ∈ Icc a b → ‖fs n t‖ ≤ C := by
  obtain ⟨_, hg⟩ := suitable_unitBall_momentumForces_integrable_localBox hsol hbox
  obtain ⟨gs, fs, hsm, hconv, _, hunif, hbound⟩ :=
    exists_smooth_time_primitive_sequence hab (by simp : (1 : ℝ≥0∞) ≤ 1)
      (by simp : (1 : ℝ≥0∞) ≠ ⊤) (memLp_one_iff_integrable.mpr hg)
      (averagedTimePrimitiveConstant (unitBallVelocityForceCurve u)
        (unitBallMomentumForceCurve u Du p) a b c) c
  exact ⟨gs, fs, hsm, suitable_unitBall_velocityForce_ae_primitive_localBox hsol hbox hab hc,
    hconv, hunif, hbound⟩

end Suitable

end FluidSingularSets
