-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallGeneralEnergyComparison
public import FluidSingularSets.ProjectedGaussianHeatError
public import FluidSingularSets.TerminalSliceEnergyExhaustion

/-!
# Genuine Gaussian extraction of inner projected energy

A uniform literal tested RHS bound controls actual inner slice energy and
coordinate dissipation. The lower Gaussian bound is applied on each strict
terminal truncation; countable exhaustion then gives the full cylinder.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual tested Gaussian RHS bounds the genuine inner normalized projected energy. -/
theorem suitable_fullBall_gaussian_energy_bound_of_rhs
    {Ω : Set Vec3} {I : Set ℝ} {q c r ρ A : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r < ρ / 4)
    (hA : 0 ≤ A)
    (hR : ∀ δ : ℝ, 0 < δ → δ < r ^ 2 → ∀ t h : ℝ, 0 < h →
      (∫ z, fullBallProjectedRhsDensity ρ u D p (-1) 0 c
        (projectedGaussianTest r ρ δ hρ) z * backwardTimeCutoff t h z.2
          ∂(fullBallInteriorMeasure ρ).prod (volume.restrict (Ioo (-1) 0))) ≤ A) :
    fullBallProjectedIterationSliceEnergy u D p (-1) 0 c r 0 ≤
        ENNReal.ofReal (2000 * r * A) ∧
      fullBallProjectedIterationDissipation u D p (-1) 0 c r 0 ≤
        ENNReal.ofReal (1000 * r * A) ∧
      fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c r 0 ≤
        ENNReal.ofReal (3000 * A) := by
  have hrone : r < 1 := by linarith
  have hball : vec3Ball 0 r ⊆ fullBallCompactInterior ρ :=
    (vec3Ball_mono (by linarith : r ≤ ρ)).trans subset_closure
  have htrunc (δ : ℝ) (hδ : 0 < δ) (hδlt : δ < r ^ 2) :
      essSup (fun t ↦ ∫⁻ x in vec3Ball 0 r, ENNReal.ofReal
        (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p (-1) 0 c (x, t)) ^ 2))
          (volume.restrict (Ioo (-r ^ 2) (-δ))) ≤ ENNReal.ofReal (2000 * r * A) ∧
        (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (-r ^ 2) (-δ), ENNReal.ofReal
          (projectedGradientSquare
            (fullBallProjectedVelocityDerivativeAmbient u D p (-1) 0 c z))) ≤
              ENNReal.ofReal (1000 * r * A) := by
    obtain ⟨hψ, hnψ, hsupp⟩ := projectedGaussianTest_admissible hr hρ hρhalf hδ
    have hψ' : projectedGaussianTest r ρ δ hρ ∈ spaceTimeTestFunction (V := ℝ) Ω I := by
      refine ⟨hψ.1, hψ.2.1, hψ.2.2.trans ?_⟩
      exact Set.prod_mono (subset_closure.trans hbox.2.2.1)
        (subset_closure.trans hbox.2.2.2.2.2)
    have ht : Ioo (-r ^ 2) (-δ) ⊆ Ioo (-1) 0 := by
      intro t htt
      have hrsq : r ^ 2 < 1 := by nlinarith
      exact ⟨by linarith only [htt.1, hrsq], by linarith only [htt.2, hδ]⟩
    have hlower (z : ParabolicPoint) (hz : z ∈ vec3Ball 0 r ×ˢ Ioo (-r ^ 2) (-δ)) :
        1 ≤ (2000 * r) * projectedGaussianTest r ρ δ hρ z := by
      have hcz : z ∈ parabolicCylinder 0 0 r := mem_parabolicCylinder.mpr
        ⟨hz.1, by simpa only [zero_sub, zero_add] using hz.2.1,
          by linarith only [hz.2.2, hδ]⟩
      have h := projectedGaussianTest_lower_inner hr hρ hscale hδ hcz hz.2.2.le
      have hp : 0 < 2000 * r := by positivity
      have hb := (div_le_iff₀ hp).mp h
      nlinarith only [hb]
    have hb := suitable_fullBall_general_tested_energy_dissipation_bound
      hsol hbox (by norm_num) hc hρ (by linarith) hψ' hnψ hsupp (hR δ hδ hδlt)
    have hm := suitable_fullBall_general_slice_energy_comparison
      hsol hbox (by norm_num) hc hρ (by linarith) (vec3Ball_measurable 0 r) hball
      measurableSet_Ioo ht hψ' hnψ hsupp (by positivity : 0 ≤ 2000 * r) hlower
    have hd := fullBall_general_dissipation_comparison ρ u D p (-1) 0 c
      (vec3Ball_measurable 0 r) hball measurableSet_Ioo ht
      (by positivity : 0 ≤ 2000 * r) hlower
    refine ⟨hm.trans ((mul_le_mul' le_rfl hb.1).trans_eq ?_),
      hd.trans ((mul_le_mul' le_rfl hb.2).trans_eq ?_)⟩
    · rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2000 * r)]
    · rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2000 * r)]
      congr 1
      ring
  have hM : fullBallProjectedIterationSliceEnergy u D p (-1) 0 c r 0 ≤
      ENNReal.ofReal (2000 * r * A) := by
    unfold fullBallProjectedIterationSliceEnergy
    simp only [zero_sub]
    apply essSup_Ioo_le_of_terminal_truncations (by nlinarith [sq_pos_of_pos hr])
    intro δ hδ hδlt
    simpa only [zero_sub, sub_neg_eq_add, zero_add] using
      (htrunc δ hδ (by simpa using hδlt)).1
  have hD : fullBallProjectedIterationDissipation u D p (-1) 0 c r 0 ≤
      ENNReal.ofReal (1000 * r * A) := by
    unfold fullBallProjectedIterationDissipation
    simp only [zero_sub]
    exact lintegral_parabolic_cylinder_le_of_terminal_truncations hr
      (fun δ hδ hδlt ↦ (htrunc δ hδ hδlt).2)
  refine ⟨hM, hD, ?_⟩
  unfold fullBallNormalizedProjectedIterationEnergy
  apply (mul_le_mul' le_rfl (add_le_add hM hD)).trans_eq
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 2000 * r * A)
      (by positivity : 0 ≤ 1000 * r * A),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ r⁻¹)]
  congr 1
  field_simp [hr.ne']
  ring

end FluidSingularSets
