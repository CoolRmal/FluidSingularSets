-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.UnitBallHarmonicForceExtension
public import FluidSingularSets.WeakTimePressure
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Genuine time derivatives preserve the closed gradient annihilator

The complement of the actual force projection is a bounded linear map.
Applied to a true weak time equation, it has zero source curve. Vector-valued
distributional uniqueness then makes its derivative zero almost everywhere.
Thus the actual derivative force belongs to the gradient annihilator; this
membership is proved rather than required as another evolution hypothesis.
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

local instance weakDerivativeGradientFreeForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

local instance weakDerivativeGradientFreeForceNormedSpace (U : Set Vec3) :
    NormedSpace ℝ (StokesEnergyForce U) :=
  inferInstanceAs (NormedSpace ℝ ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- A true weak time derivative of an AE zero Banach curve is AE zero on any open interval. -/
theorem HasWeakTimeDerivativeOn.derivative_ae_zero_of_ae_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {I : Set ℝ} {f g : ℝ → E} (hI : IsOpen I)
    (h : HasWeakTimeDerivativeOn I f g) (hg : IntegrableOn g I volume)
    (hfzero : f =ᵐ[volume.restrict I] 0) : g =ᵐ[volume.restrict I] 0 := by
  have hz := hI.ae_eq_zero_of_integral_contDiff_smul_eq_zero hg.locallyIntegrableOn
    (fun η hη hηc hηs ↦ by
      have hleft : (∫ t in I, deriv η t • f t) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [hfzero] with t ht
        simp only [Pi.zero_apply] at ht
        simp only [ht, smul_zero, Pi.zero_apply]
      have hright : (∫ t in I, η t • g t) = 0 := by
        have ht := h η hη hηc hηs
        rw [hleft] at ht
        exact neg_eq_zero.mp ht.symm
      have hout : ∀ t ∉ I, η t • g t = 0 := by
        intro t ht
        have hηzero : η t = 0 := image_eq_zero_of_notMem_tsupport
          (fun hm ↦ ht (hηs hm))
        rw [hηzero, zero_smul]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero hout).symm.trans hright)
  exact (ae_restrict_iff' hI.measurableSet).mpr hz

/-- The actual orthogonal force projection, regarded as an endomorphism of the full dual. -/
def unitBallGradientFreeForceProjectionL : StokesEnergyForce (vec3Ball 0 1) →L[ℝ]
    StokesEnergyForce (vec3Ball 0 1) :=
  unitBallGradientFreeForce.toSubmodule.subtypeL.comp unitBallGradientFreeForceProjection

/-- The force endomorphism genuinely fixes the true gradient annihilator. -/
theorem unitBallGradientFreeForceProjectionL_of_gradientFree (F : unitBallGradientFreeForce) :
    unitBallGradientFreeForceProjectionL F.1 = F.1 :=
  congrArg (fun v : unitBallGradientFreeForce ↦ v.1)
    (unitBallGradientFreeForceProjection_of_gradientFree F)

/-- A genuine energy-dual weak time derivative preserves actual gradient annihilation AE. -/
theorem hasWeakTimeDerivativeOn_gradientFree_ae
    {I : Set ℝ} {F G : ℝ → StokesEnergyForce (vec3Ball 0 1)} (hI : IsOpen I)
    (h : HasWeakTimeDerivativeOn I F G)
    (hf : IntegrableOn F I volume) (hg : IntegrableOn G I volume)
    (hF : ∀ᵐ t ∂volume.restrict I, F t ∈ unitBallGradientFreeForce) :
    ∀ᵐ t ∂volume.restrict I, G t ∈ unitBallGradientFreeForce := by
  let L : StokesEnergyForce (vec3Ball 0 1) →L[ℝ] StokesEnergyForce (vec3Ball 0 1) :=
    ContinuousLinearMap.id ℝ _ - unitBallGradientFreeForceProjectionL
  have hzero : (fun t ↦ L (F t)) =ᵐ[volume.restrict I] 0 := by
    filter_upwards [hF] with t ht
    change F t - unitBallGradientFreeForceProjectionL (F t) = 0
    exact sub_eq_zero.mpr
      (unitBallGradientFreeForceProjectionL_of_gradientFree ⟨F t, ht⟩).symm
  have hGzero := (h.continuousLinearMap hf hg L).derivative_ae_zero_of_ae_zero
    hI (L.integrable_comp hg) hzero
  filter_upwards [hGzero] with t ht
  change G t - unitBallGradientFreeForceProjectionL (G t) = 0 at ht
  rw [sub_eq_zero.mp ht]
  exact (unitBallGradientFreeForceProjection (G t)).property

/-- The true derivative has an actual force-domain representative, and the extended
gradient is its true harmonic-pressure gradient, without a membership premise on the RHS. -/
theorem hasWeakTimeDerivativeOn_harmonicForceGradient_actual_derivative_ae
    {I : Set ℝ} {F G : ℝ → StokesEnergyForce (vec3Ball 0 1)} (hI : IsOpen I)
    (h : HasWeakTimeDerivativeOn I F G)
    (hf : IntegrableOn F I volume) (hg : IntegrableOn G I volume)
    (hF : ∀ᵐ t ∂volume.restrict I, F t ∈ unitBallGradientFreeForce) :
    ∀ᵐ t ∂volume.restrict I, ∃ g : unitBallGradientFreeForce,
      g.1 = G t ∧ unitBallHarmonicForceGradientExtended (G t) =
        unitBallHarmonicForceGradient g := by
  filter_upwards [hasWeakTimeDerivativeOn_gradientFree_ae hI h hf hg hF] with t ht
  exact ⟨⟨G t, ht⟩, rfl, unitBallHarmonicForceGradientExtended_of_gradientFree ⟨G t, ht⟩⟩

end FluidSingularSets
