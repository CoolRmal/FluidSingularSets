-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.BallCenteredPressureOperator
public import FluidSingularSets.ProjectedCutoffErrors

/-!
# Literal centered pressure pairings with actual mixed energy classes

The genuine bounded mean-removal operator identifies the true oscillation
moment and preserves the literal centered integral against each spatial flux.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A genuine centered time L¹ pressure pairs with the actual time L∞ spatial L² flux. -/
theorem pressureCurve_centered_pairing_one_top_integrable_and_bound
    {x : Vec3} {R r : ℝ} (hrR : r ≤ R) {ν : Measure ℝ}
    {P : ℝ → Lp ℝ 2 (volume.restrict (vec3Ball x R))} {G : Vec3 × ℝ → ℝ}
    (hP : MemLp P 1 ν)
    (hGs : ∀ᵐ t ∂ν, MemLp (fun y ↦ G (y, t)) 2 (volume.restrict (vec3Ball x r)))
    (hGc : MemLp (actualSliceLp (μ := volume.restrict (vec3Ball x r)) (p := 2) G) ⊤ ν) :
    Integrable (fun t ↦ ∫ y in vec3Ball x r,
      (P t y - average (volume.restrict (vec3Ball x r)) (P t)) * G (y, t)) ν ∧
      ‖∫ t, (∫ y in vec3Ball x r,
        (P t y - average (volume.restrict (vec3Ball x r)) (P t)) * G (y, t)) ∂ν‖ₑ ≤
        (∫⁻ t, eLpNorm (fun y ↦ P t y -
          average (volume.restrict (vec3Ball x r)) (P t)) 2
            (volume.restrict (vec3Ball x r)) ∂ν) *
          eLpNorm (actualSliceLp (μ := volume.restrict (vec3Ball x r)) (p := 2) G) ⊤ ν := by
  have heq (t : ℝ) : (∫ y in vec3Ball x r,
      ballCenteredPressureL x hrR (P t) y * G (y, t)) =
      ∫ y in vec3Ball x r,
        (P t y - average (volume.restrict (vec3Ball x r)) (P t)) * G (y, t) := by
    apply integral_congr_ae
    filter_upwards [ballCenteredPressureL_ae x hrR (P t)] with y hy
    rw [hy]
  have hb := pressureCurve_pairing_one_top_integrable_and_bound
    (ballCenteredPressureL_memLp x hrR hP) hGs hGc
  simp_rw [heq] at hb
  rw [ballCenteredPressureL_eLpNorm_one_eq x hrR hP.aestronglyMeasurable] at hb
  exact hb

/-- Genuine centered time L² pressure gains the square root of the actual time measure. -/
theorem pressureCurve_centered_pairing_two_top_integrable_and_bound
    {x : Vec3} {R r : ℝ} (hrR : r ≤ R) {ν : Measure ℝ} [IsFiniteMeasure ν]
    {P : ℝ → Lp ℝ 2 (volume.restrict (vec3Ball x R))} {G : Vec3 × ℝ → ℝ}
    (hP : MemLp P 2 ν)
    (hGs : ∀ᵐ t ∂ν, MemLp (fun y ↦ G (y, t)) 2 (volume.restrict (vec3Ball x r)))
    (hGc : MemLp (actualSliceLp (μ := volume.restrict (vec3Ball x r)) (p := 2) G) ⊤ ν) :
    Integrable (fun t ↦ ∫ y in vec3Ball x r,
      (P t y - average (volume.restrict (vec3Ball x r)) (P t)) * G (y, t)) ν ∧
      ‖∫ t, (∫ y in vec3Ball x r,
        (P t y - average (volume.restrict (vec3Ball x r)) (P t)) * G (y, t)) ∂ν‖ₑ ≤
        (∫⁻ t, eLpNorm (fun y ↦ P t y -
          average (volume.restrict (vec3Ball x r)) (P t)) 2
            (volume.restrict (vec3Ball x r)) ^ 2 ∂ν) ^ (1 / 2 : ℝ) *
          ν Set.univ ^ (1 / 2 : ℝ) *
          eLpNorm (actualSliceLp (μ := volume.restrict (vec3Ball x r)) (p := 2) G) ⊤ ν := by
  have heq (t : ℝ) : (∫ y in vec3Ball x r,
      ballCenteredPressureL x hrR (P t) y * G (y, t)) =
      ∫ y in vec3Ball x r,
        (P t y - average (volume.restrict (vec3Ball x r)) (P t)) * G (y, t) := by
    apply integral_congr_ae
    filter_upwards [ballCenteredPressureL_ae x hrR (P t)] with y hy
    rw [hy]
  have hb := pressureCurve_pairing_two_top_integrable_and_bound
    (ballCenteredPressureL_memLp x hrR hP) hGs hGc
  simp_rw [heq] at hb
  rw [ballCenteredPressureL_eLpNorm_two_eq x hrR hP.aestronglyMeasurable] at hb
  exact hb

end FluidSingularSets
