-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallScaledEndpointSequence
public import FluidSingularSets.EndpointRecurrenceSmallness
public import FluidSingularSets.ProjectedGradientCriterion

/-!
# Actual velocity-only endpoint regularity at the native origin

The genuine projected Caccioppoli and pressure estimates bound the literal
shrinking-scale sequence. The proved scalar trap keeps it below the CKN
budget, including the true reciprocal interpolation factor. The actual
harmonic correction vanishes in the original normalized gradient criterion.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A positive universal velocity source threshold gives genuine regularity at the native origin. -/
theorem exists_native_endpoint_origin_regular_threshold (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (D : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ),
        IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0) →
        localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0) →
        velocityCylinderSixMoment u 1 ≤ ENNReal.ofReal ε →
        CKN.IsRegularPoint Ω I u (0, 0) := by
  obtain ⟨H, hH, hreg⟩ := exists_projected_energy_regularity_budget q hq
  have hC : 0 ≤ projectedGaussianRecurrenceUniversalConstant :=
    (by norm_num : (0 : ℝ) ≤ 1).trans projectedGaussianRecurrenceUniversalConstant_ge_one
  obtain ⟨θ, T, ε, hθ, hθquarter, _hT, hTH, hε, _, htrap⟩ :=
    exists_endpoint_recurrence_smallness hC fullBallScaledInitialIterationConstant_nonneg
      fullBallScaledDissipationSourceConstant_nonneg hH
  refine ⟨ε, hε, ?_⟩
  intro Ω I u D p hsol hbox hsmall
  let x := (velocityCylinderSixMoment u 1).toReal
  have hx : 0 ≤ x := ENNReal.toReal_nonneg
  have hxε : x ≤ ε := ENNReal.toReal_le_of_le_ofReal hε.le hsmall
  have hbound : ∀ n : ℕ, fullBallScaledEndpointSequence u D p θ n ≤ T :=
    htrap x hx hxε (fullBallScaledEndpointSequence u D p θ)
      (fullBallScaledEndpointSequence_nonneg u D p θ)
      (suitable_fullBall_scaled_endpoint_sequence_initial hsol hbox)
      (suitable_fullBall_scaled_endpoint_sequence_step hsol hbox hθ hθquarter)
  let us := rescaleVelocity (3 / 4) (0, 0) u
  let Ds := rescaleGradient (3 / 4) (0, 0) D
  let ps := rescalePressure (3 / 4) (0, 0) p
  have hs := suitable_unforced_rescale hsol (0, 0) (by norm_num : (0 : ℝ) < 3 / 4)
  have hb := localBox_rescaled_subunit_backwardCylinder hbox
    (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num)
  have he : ∀ n : ℕ, fullBallNormalizedProjectedIterationEnergy us Ds ps
      (-1) 0 (-(1 / 2)) ((1 / 4) * θ ^ n) 0 ≤ ENNReal.ofReal T := by
    intro n
    exact (suitable_fullBall_scaled_endpoint_sequence_energy_le hsol hbox hθ hθquarter n).trans
      (ENNReal.ofReal_le_ofReal (hbound n))
  have hbudget : θ⁻¹ * T ≤ H := by
    have hh := mul_le_mul_of_nonneg_left hTH (inv_nonneg.mpr hθ.le)
    simpa [hθ.ne', ← mul_assoc] using hh
  have hregular : CKN.IsRegularPoint (rescaledSpace (3 / 4) 0 Ω)
      (rescaledTime (3 / 4) 0 I) us (0, 0) := by
    apply hreg _ _ us Ds ps hs hb
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono inf_le_left]
        with r hr hrr
    have hh := fullBallNormalizedProjectedIterationEnergy_le_of_geometric_bounds
      us Ds ps (-1) 0 (-(1 / 2)) hθ (by linarith) (by norm_num) he hr hrr.le
    exact hh.trans (ENNReal.ofReal_le_ofReal hbudget)
  have hh := isRegularPoint_of_rescaled (by norm_num : (0 : ℝ) < 3 / 4)
    (0, 0) (0, 0) hregular
  simpa [CKN.scalingParabolic, parabolicTranslate, parabolicScale] using hh

end FluidSingularSets
