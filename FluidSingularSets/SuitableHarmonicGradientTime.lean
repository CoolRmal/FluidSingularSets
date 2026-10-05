-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.SuitableProjectedPressureTime
public import FluidSingularSets.UnitBallHarmonicGradientCompatibility
public import FluidSingularSets.UnitBallHarmonicGradientPairing
public import FluidSingularSets.WeakDerivativeGradientFree
public import FluidSingularSets.WeakContinuousTimePrimitive
public import CKN.Foundation.Measure.SliceDistribution

/-!
# Actual suitable harmonic-gradient time evolution

The genuine suitable momentum forces have a weak time derivative. The proved
bounded harmonic-gradient operator transports that derivative into continuous
fields on the compact interior ball. Suitable divergence and actual L² slices
identify the transported field with the canonical source pressure gradient on
one common set of full time measure.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

local instance suitableHarmonicGradientTimeForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance suitableHarmonicGradientTimeForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- The genuine suitable velocity class with the Euclidean Hilbert norm. -/
def unitBallHilbertVelocityCurve (u : ParabolicPoint → Vec3) (t : ℝ) : UnitBallVectorL2 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).symm.toContinuousLinearMap.compLpL
    2 (volume.restrict (vec3Ball 0 1)) (unitBallVelocityCurve u t)

/-- The actual coordinate class of the Hilbert velocity is the original velocity class. -/
theorem unitBallHilbertVelocityCurve_coordinates (u : ParabolicPoint → Vec3) (t : ℝ) :
    unitBallVectorCoordinates (unitBallHilbertVelocityCurve u t) =
      unitBallVelocityCurve u t := by
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)
  apply Lp.ext
  filter_upwards [L.toContinuousLinearMap.coeFn_compLpL
    (unitBallHilbertVelocityCurve u t),
    L.symm.toContinuousLinearMap.coeFn_compLpL (unitBallVelocityCurve u t)] with x h₁ h₂
  change unitBallVectorCoordinates (unitBallHilbertVelocityCurve u t) x = _ at h₁
  change unitBallHilbertVelocityCurve u t x = _ at h₂
  rw [h₁, h₂]
  exact L.apply_symm_apply _

/-- The Hilbert and coordinate constructions yield exactly the same genuine vector force. -/
theorem unitBallHilbertVelocityCurve_force (u : ParabolicPoint → Vec3) (t : ℝ) :
    unitBallHilbertVectorForce (unitBallHilbertVelocityCurve u t) =
      unitBallVelocityForceCurve u t := by
  rw [unitBallHilbertVectorForce_apply, unitBallHilbertVelocityCurve_coordinates]
  exact (stokesVectorForceL_apply _ _).symm

/-- The actual negative harmonic correction, in the bounded force formulation. -/
def unitBallHarmonicGradientTimeCurve (u : ParabolicPoint → Vec3) (t : ℝ) :
    C(unitBallPressureCompactInterior, Vec3) :=
  -unitBallHarmonicForceGradientExtended (unitBallVelocityForceCurve u t)

/-- The true transported suitable momentum derivative of the harmonic correction. -/
def unitBallHarmonicGradientTimeDerivative (u : ParabolicPoint → Vec3)
    (D : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ) (t : ℝ) :
    C(unitBallPressureCompactInterior, Vec3) :=
  -unitBallHarmonicForceGradientExtended (unitBallMomentumForceCurve u D p t)

section Suitable

variable {Ω : Set Vec3} {I : Set ℝ} {q t₀ : ℝ}
  {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

private theorem harmonicGradientTime_localBox
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

/-- One actual full-measure time set gives every compact spatial divergence test. -/
theorem suitable_unitBall_divergenceFree_slices_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball 0 1 →
          (∫ x in vec3Ball 0 1, ∑ i : Fin 3,
            u (x, t) i * spatialDeriv ψ i x) = 0 := by
  have hbox := harmonicGradientTime_localBox hdom
  have hBΩ : vec3Ball (0 : Vec3) 1 ⊆ Ω := subset_closure.trans hbox.2.2.1
  have hJI : Ioo (t₀ - 4) (t₀ + 4) ⊆ I :=
    subset_closure.trans hbox.2.2.2.2.2
  have hloc : ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)), ∀ i : Fin 3,
      LocallyIntegrableOn (fun x ↦ u (x, t) i) (vec3Ball 0 1) volume := by
    filter_upwards [slice_memLp_ae_of_sws hsol hbox] with t ht i
    exact locallyIntegrableOn_of_locallyIntegrable_restrict
      ((ht.1.eval i).locallyIntegrable (by norm_num))
  apply ae_slice_divergence_zero_of_forall_test (isOpen_vec3Ball 0 1) hloc
  intro ψ hψ hψc hψB
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hJI
    (divfree_slice_weak_of_suitable hsol ψ hψ hψc (hψB.trans hBΩ))] with t ht
  have hz (x : Vec3) (hx : x ∉ tsupport ψ) :
      (∑ i : Fin 3, u (x, t) i * (fderiv ℝ ψ x) (basisVec i)) = 0 := by
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]
    simp only [zero_apply, mul_zero, Finset.sum_const_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx ↦ hz x (fun h ↦ hx (hψB h))),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ hz x (fun h ↦ hx (hBΩ (hψB h))))]
  exact ht

/-- The actual Hilbert velocity slices lie in the genuine divergence-free source space. -/
theorem suitable_unitBall_hilbertVelocity_divergenceFree_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      unitBallHilbertVelocityCurve u t ∈ unitBallDivergenceFreeL2 := by
  have hbox := harmonicGradientTime_localBox hdom
  filter_upwards [slice_memLp_ae_of_sws hsol hbox,
    suitable_unitBall_divergenceFree_slices_ae hsol hdom] with t ht hdiv
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

/-- Suitable divergence places the actual velocity force in every genuine gradient-test kernel. -/
theorem suitable_unitBall_velocityForce_gradientFree_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      unitBallVelocityForceCurve u t ∈ unitBallGradientFreeForce := by
  filter_upwards [suitable_unitBall_hilbertVelocity_divergenceFree_ae hsol hdom] with t ht
  intro ψ
  rw [← unitBallHilbertVelocityCurve_force]
  exact ht ψ

/-- The actual transported harmonic field agrees almost everywhere with the canonical
spatial-source harmonic correction, with no compatibility premise. -/
theorem suitable_unitBall_harmonicGradientTime_eq_source_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    unitBallHarmonicGradientTimeCurve u =ᵐ[volume.restrict (Ioo (t₀ - 4) (t₀ + 4))]
      fun t ↦ -unitBallHarmonicGradientExtended (unitBallHilbertVelocityCurve u t) := by
  filter_upwards [suitable_unitBall_hilbertVelocity_divergenceFree_ae hsol hdom] with t ht
  let v : unitBallDivergenceFreeL2 := ⟨unitBallHilbertVelocityCurve u t, ht⟩
  change -unitBallHarmonicForceGradientExtended (unitBallVelocityForceCurve u t) = _
  rw [← unitBallHilbertVelocityCurve_force]
  rw [unitBallHarmonicForceGradientExtended_of_source v,
    unitBallHarmonicGradientExtended_of_divergenceFree v]

/-- Both genuine continuous-field time curves are actually Bochner integrable. -/
theorem suitable_unitBall_harmonicGradientTime_integrable
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    IntegrableOn (unitBallHarmonicGradientTimeCurve u) (Ioo (t₀ - 4) (t₀ + 4)) volume ∧
      IntegrableOn (unitBallHarmonicGradientTimeDerivative u Du p)
        (Ioo (t₀ - 4) (t₀ + 4)) volume := by
  obtain ⟨hF, hG⟩ := suitable_unitBall_momentumForces_integrable hsol hdom
  exact ⟨(unitBallHarmonicForceGradientExtended.integrable_comp hF).neg,
    (unitBallHarmonicForceGradientExtended.integrable_comp hG).neg⟩

/-- The actual suitable momentum derivative transports to the genuine harmonic correction. -/
theorem suitable_unitBall_harmonicGradientTime_hasWeakTimeDerivativeOn
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    HasWeakTimeDerivativeOn (Ioo (t₀ - 4) (t₀ + 4))
      (unitBallHarmonicGradientTimeCurve u) (unitBallHarmonicGradientTimeDerivative u Du p) := by
  obtain ⟨hF, hG⟩ := suitable_unitBall_momentumForces_integrable hsol hdom
  have h := suitable_unitBall_momentum_hasWeakTimeDerivativeOn hsol hdom
  exact h.continuousLinearMap hF hG (-unitBallHarmonicForceGradientExtended)

/-- Genuine time differentiation preserves every actual compact-gradient kernel. -/
theorem suitable_unitBall_momentumForce_gradientFree_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
      unitBallMomentumForceCurve u Du p t ∈ unitBallGradientFreeForce := by
  obtain ⟨hF, hG⟩ := suitable_unitBall_momentumForces_integrable hsol hdom
  exact hasWeakTimeDerivativeOn_gradientFree_ae isOpen_Ioo
    (suitable_unitBall_momentum_hasWeakTimeDerivativeOn hsol hdom) hF hG
    (suitable_unitBall_velocityForce_gradientFree_ae hsol hdom)

/-- The negative actual momentum projection is the literal physical pressure combination. -/
theorem unitBallMomentumForceCurve_negative_pressure
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (t : ℝ) :
    unitBallStokesPressure (-unitBallMomentumForceCurve u D p t) =
      unitBallActualPressureCurve p t - unitBallConvectivePressureCurve u t -
        unitBallViscousPressureCurve D t := by
  change unitBallStokesPressureL (-unitBallMomentumForceCurve u D p t) = _
  rw [unitBallMomentumForceCurve, map_neg, map_sub, map_add,
    ← unitBallConvectivePressureCurve_eq_projection,
    ← unitBallViscousPressureCurve_eq_projection, unitBallStokesPressureL_apply,
    unitBallStokesPressure_pressureEnergyForce]
  abel

/-- The true derivative field is the actual C² pressure gradient of the physical
centered-pressure difference on almost every time slice. -/
theorem suitable_unitBall_harmonicGradientTimeDerivative_pressure_ae
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    ∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)), ∃ H : Vec3 → ℝ,
      ContDiffOn ℝ (2 : ℕ∞) H (vec3Ball 0 (1 / 4)) ∧
      ((unitBallActualPressureCurve p t - unitBallConvectivePressureCurve u t -
          unitBallViscousPressureCurve Du t : unitBallMeanZeroL2) :
        Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))
          =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))] H ∧
      ∀ x : unitBallPressureCompactInterior,
        unitBallHarmonicGradientTimeDerivative u Du p t x = classicalGradient H x.1 := by
  filter_upwards [suitable_unitBall_momentumForce_gradientFree_ae hsol hdom] with t ht
  let g : unitBallGradientFreeForce :=
    ⟨-unitBallMomentumForceCurve u Du p t,
      unitBallGradientFreeForce.toSubmodule.neg_mem ht⟩
  refine ⟨unitBallHarmonicForcePressureRepresentative g,
    unitBallHarmonicForcePressureRepresentative_contDiff g, ?_, ?_⟩
  · have h := unitBallHarmonicForcePressureRepresentative_pressure_ae g
    change ((unitBallStokesPressure (-unitBallMomentumForceCurve u Du p t) :
      unitBallMeanZeroL2) : Lp ℝ 2 (volume.restrict (vec3Ball 0 1)))
        =ᵐ[volume.restrict (vec3Ball 0 (1 / 4))] _ at h
    rw [unitBallMomentumForceCurve_negative_pressure] at h
    exact h
  · intro x
    change -unitBallHarmonicForceGradientExtended (unitBallMomentumForceCurve u Du p t) x = _
    have hneg := congrArg (fun f : C(unitBallPressureCompactInterior, Vec3) ↦ f x)
      (map_neg unitBallHarmonicForceGradientExtended (unitBallMomentumForceCurve u Du p t))
    change unitBallHarmonicForceGradientExtended
      (-unitBallMomentumForceCurve u Du p t) x =
        -unitBallHarmonicForceGradientExtended (unitBallMomentumForceCurve u Du p t) x at hneg
    rw [← hneg]
    exact congrArg (fun f : C(unitBallPressureCompactInterior, Vec3) ↦ f x)
      (unitBallHarmonicForceGradientExtended_of_gradientFree g)

/-- The actual suitable harmonic correction has a genuine continuous absolutely continuous
time representative with its true Banach derivative and every exact primitive difference. -/
theorem exists_suitable_unitBall_harmonicGradientTime_continuous_representative
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hdom : Metric.ball (α := ParabolicPoint) (0, t₀) 8 ⊆ spaceTimeSet Ω I) :
    ∃ m : ℝ → C(unitBallPressureCompactInterior, Vec3), Continuous m ∧
      AbsolutelyContinuousOnInterval m (t₀ - 4) (t₀ + 4) ∧
      unitBallHarmonicGradientTimeCurve u
        =ᵐ[volume.restrict (Ioo (t₀ - 4) (t₀ + 4))] m ∧
      (∀ᵐ t ∂volume.restrict (Ioo (t₀ - 4) (t₀ + 4)),
        HasDerivAt m (unitBallHarmonicGradientTimeDerivative u Du p t) t) ∧
      ∀ s t : ℝ, m t - m s = ∫ v in s..t,
        (Ioo (t₀ - 4) (t₀ + 4)).indicator
          (unitBallHarmonicGradientTimeDerivative u Du p) v := by
  obtain ⟨hf, hg⟩ := suitable_unitBall_harmonicGradientTime_integrable hsol hdom
  exact exists_continuousMap_absolutelyContinuous_of_weakTimeDerivative (by linarith) hf hg
    (suitable_unitBall_harmonicGradientTime_hasWeakTimeDerivativeOn hsol hdom)

end Suitable

end FluidSingularSets
