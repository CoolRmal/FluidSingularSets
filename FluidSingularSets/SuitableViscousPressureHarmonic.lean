-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StokesTensorPressurePoisson
public import FluidSingularSets.StokesPressureCurves
public import FluidSingularSets.SuitableHarmonicGradientTime
public import CKN.Foundation.Measure.SliceDistribution

/-!
# Genuine harmonic viscous pressure of suitable solutions

One actual full-measure time set contains every compact spatial divergence
test in an arbitrary local box. Together with the original S1 weak gradients,
this proves harmonicity of the actual viscous-pressure curve. No future-time
buffer or harmonicity assumption is required.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration CKN.Foundation.Heat
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Actual suitable divergence holds on one common full time set in every local box. -/
theorem suitable_divergenceFree_slices_ae_localBox
    {Ω U : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I U J) :
    ∀ᵐ t ∂volume.restrict J, ∀ ψ : WeakTestFunction U,
      (∫ x in U, ∑ i : Fin 3, u (x, t) i * spatialDeriv ψ.toFun i x) = 0 := by
  have hUΩ : U ⊆ Ω := subset_closure.trans hbox.2.2.1
  have hJI : J ⊆ I := subset_closure.trans hbox.2.2.2.2.2
  have hloc : ∀ᵐ t ∂volume.restrict J, ∀ i : Fin 3,
      LocallyIntegrableOn (fun x ↦ u (x, t) i) U volume := by
    filter_upwards [slice_memLp_ae_of_sws hsol hbox] with t ht i
    exact locallyIntegrableOn_of_locallyIntegrable_restrict
      ((ht.1.eval i).locallyIntegrable (by norm_num))
  have hdiv : ∀ᵐ t ∂volume.restrict J,
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        (∫ x in U, ∑ i : Fin 3, u (x, t) i * spatialDeriv ψ i x) = 0 := by
    apply ae_slice_divergence_zero_of_forall_test hbox.1 hloc
    intro ψ hψ hψc hψU
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hJI
      (divfree_slice_weak_of_suitable hsol ψ hψ hψc (hψU.trans hUΩ))] with t ht
    have hz (x : Vec3) (hx : x ∉ tsupport ψ) :
        (∑ i : Fin 3, u (x, t) i * (fderiv ℝ ψ x) (basisVec i)) = 0 := by
      rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]
      simp only [zero_apply, mul_zero, Finset.sum_const_zero]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ hz x (fun h ↦ hx (hψU h))),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦ hz x (fun h ↦ hx (hUΩ (hψU h))))]
    exact ht
  exact hdiv.mono fun _ ht ψ ↦ ht ψ.toFun ψ.contDiff ψ.hasCompactSupport ψ.tsupport_subset

/-- The actual suitable viscous-pressure curve is genuinely harmonic at almost every time. -/
theorem suitable_unitBall_viscousPressureCurve_weaklyHarmonic_ae
    {Ω : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball 0 1) J) :
    ∀ᵐ t ∂volume.restrict J,
      WeaklyHarmonicOn (vec3Ball 0 1) (unitBallViscousPressureCurve Du t :
        Lp ℝ 2 (volume.restrict (vec3Ball 0 1))) := by
  have hw := ae_all_iff.mpr (hsol.toData.hasWeakGradientOn_slice hbox)
  filter_upwards [slice_memLp_ae_of_sws hsol hbox, hw,
    suitable_divergenceFree_slices_ae_localBox hsol hbox] with t ht hwt hdiv
  rw [unitBallViscousPressureCurve_eq Du t ht.2]
  exact unitBallRawViscousPressure_weaklyHarmonic
    (fun x ↦ u (x, t)) (fun x ↦ Du (x, t)) ht.1 ht.2 hwt hdiv

end FluidSingularSets
