-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.WeightedMeanMotion
public import FluidSingularSets.WeakTimePressure

/-!
# Actual suitable momentum as an energy-dual time derivative

The genuine scalar spatial tests of the suitable momentum equation are summed
componentwise. Whenever actual integrable energy forces have these literal
pairings, density of compact smooth Stokes tests gives the complete Bochner
weak derivative. No energy-dual evolution identity is assumed.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

local instance momentumTimeForceNormedAddCommGroup (U : Set Vec3) :
    NormedAddCommGroup (StokesEnergyForce U) :=
  inferInstanceAs (NormedAddCommGroup ((stokesGradientEnergySpace U) →L[ℝ] ℝ))

/-- Each true spatial weighted velocity mean is integrable in the actual time box. -/
theorem suitable_weightedVelocityMean_integrableOn
    {Ω B : Set Vec3} {I : Set ℝ} {a b q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I B (Ioo a b))
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (i : Fin 3) :
    IntegrableOn (weightedVelocityMean B χ u i) (Ioo a b) volume := by
  have hmean := (suitable_weighted_momentum_terms_integrable hsol hbox hχ hχc i).1
  have hprod : (volume : Measure ParabolicPoint).restrict (spaceTimeSet B (Ioo a b)) =
      (volume.restrict B).prod (volume.restrict (Ioo a b)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
    rfl
  rw [hprod] at hmean
  exact hmean.integral_prod_right

/-- Literal actual compact-test force pairings and genuine Bochner integrability
turn the suitable momentum equation into its complete energy-dual evolution. -/
theorem suitable_energyDual_hasWeakTimeDerivativeOn_of_literal_pairings
    {Ω B : Set Vec3} {I : Set ℝ} {a b q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p (fun _ ↦ 0))
    (hbox : localBox Ω I B (Ioo a b))
    {F G : ℝ → StokesEnergyForce B}
    (hF : IntegrableOn F (Ioo a b) volume) (hG : IntegrableOn G (Ioo a b) volume)
    (hpair : ∀ φ : StokesVectorTest B,
      (fun t ↦ F t (stokesEnergyTest φ)) =ᵐ[volume.restrict (Ioo a b)]
        (fun t ↦ ∑ i : Fin 3, weightedVelocityMean B (φ i).toFun u i t) ∧
      (fun t ↦ G t (stokesEnergyTest φ)) =ᵐ[volume.restrict (Ioo a b)]
        (fun t ↦ ∑ i : Fin 3, ∫ x in B,
          weightedMomentumFlux (φ i).toFun u Du p i (x, t))) :
    HasWeakTimeDerivativeOn (Ioo a b) F G := by
  apply hasWeakTimeDerivativeOn_stokes_of_compact_pairings hF hG
  intro η hη hηc hηs φ
  have hmean (i : Fin 3) := suitable_weightedVelocityMean_integrableOn hsol hbox
    (φ i).contDiff (φ i).hasCompactSupport i
  have hflux (i : Fin 3) := suitable_weighted_mean_hasWeakDerivOn hsol hbox
    (φ i).contDiff (φ i).hasCompactSupport (φ i).tsupport_subset i
  have hmeanTest (i : Fin 3) : IntegrableOn
      (fun t ↦ deriv η t * weightedVelocityMean B (φ i).toFun u i t)
      (Ioo a b) volume := by
    simpa only [smul_eq_mul] using integrable_smul_compact_time_test (hmean i)
      (hη.continuous_deriv (by simp)) hηc.deriv
  have hfluxTest (i : Fin 3) : IntegrableOn
      (fun t ↦ η t * ∫ x in B, weightedMomentumFlux (φ i).toFun u Du p i (x, t))
      (Ioo a b) volume := by
    simpa only [smul_eq_mul] using integrable_smul_compact_time_test (hflux i).2.1
      hη.continuous hηc
  calc
    _ = ∫ t in Ioo a b, deriv η t *
        ∑ i : Fin 3, weightedVelocityMean B (φ i).toFun u i t := by
      apply integral_congr_ae
      filter_upwards [(hpair φ).1] with t ht
      rw [ht]
    _ = ∑ i : Fin 3, ∫ t in Ioo a b,
        deriv η t * weightedVelocityMean B (φ i).toFun u i t := by
      simp_rw [Finset.mul_sum]
      exact integral_finsetSum Finset.univ (fun i _ ↦ hmeanTest i)
    _ = ∑ i : Fin 3, -(∫ t in Ioo a b, η t *
        ∫ x in B, weightedMomentumFlux (φ i).toFun u Du p i (x, t)) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [mul_comm] using (hflux i).2.2 η ⟨hη, hηc, hηs⟩
    _ = -(∫ t in Ioo a b, η t *
        ∑ i : Fin 3, ∫ x in B, weightedMomentumFlux (φ i).toFun u Du p i (x, t)) := by
      rw [Finset.sum_neg_distrib]
      congr 1
      simp_rw [Finset.mul_sum]
      exact (integral_finsetSum Finset.univ (fun i _ ↦ hfluxTest i)).symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [(hpair φ).2] with t ht
      rw [ht]

end FluidSingularSets
