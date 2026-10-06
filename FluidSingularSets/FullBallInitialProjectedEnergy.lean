-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallInitialTestedEnergy
public import FluidSingularSets.ProjectedPlateauEnergy
public import FluidSingularSets.TerminalSliceEnergyExhaustion
public import FluidSingularSets.FullBallPressureOscillationDecay

/-!
# Genuine initial full-cylinder projected energy

The canonical test at radius three quarters bounds the actual projected energy
on the quarter cylinder. Countable terminal exhaustion retains the original
time interval and removes every terminal cap with one common source budget.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The actual unit-data budget for the initial projected cylinder. -/
def fullBallInitialProjectedBudget
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3) : ℝ :=
  let X := (velocityCylinderSixMoment u 1).toReal
  (3 / 4) * (coordinateCylinderMass D 1).toReal +
    fullCylinderEndpointForcingConstant / (1 - (3 / 4 : ℝ)) ^ 12 * (X + X ^ 2 + X ^ 4)

theorem fullBallInitialProjectedBudget_nonneg
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3) :
    0 ≤ fullBallInitialProjectedBudget u D := by
  unfold fullBallInitialProjectedBudget
  exact add_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
    (mul_nonneg (div_nonneg fullCylinderEndpointForcingConstant_nonneg (by positivity))
      (by positivity))

/-- Every actual terminal-truncated quarter cylinder has the common projected energy bound. -/
theorem suitable_fullBall_initial_projected_truncated_bounds
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0))
    {δ : ℝ} (hδ : 0 < δ) :
    essSup (fun t ↦ ∫⁻ x in vec3Ball 0 (1 / 4), ENNReal.ofReal
      (vec3EuclideanNorm (fullBallProjectedVelocityAmbient u D p (-1) 0 (-(1 / 2))
        (x, t)) ^ 2)) (volume.restrict (Ioo (-((1 / 4 : ℝ) ^ 2)) (-δ))) ≤
      ENNReal.ofReal (fullBallInitialProjectedBudget u D) ∧
    (∫⁻ z : ParabolicPoint in vec3Ball 0 (1 / 4) ×ˢ Ioo (-((1 / 4 : ℝ) ^ 2)) (-δ),
      ENNReal.ofReal (projectedGradientSquare
        (fullBallProjectedVelocityDerivativeAmbient u D p (-1) 0 (-(1 / 2)) z))) ≤
      ENNReal.ofReal (fullBallInitialProjectedBudget u D / 2) := by
  let φ := fullBallCanonicalSpatialCutoff (3 / 4)
  let θ := fullBallCanonicalTimeCutoff (3 / 4) δ
  let ρ := fullBallCanonicalPressureRadius (3 / 4)
  let M := fullBallTimeWeightedProjectedEnergySup u D p (-1) 0 (-(1 / 2))
    (vec3Ball 0 ρ) φ θ
  let N := fullBallTimeWeightedProjectedDissipation ρ u D p (-1) 0 (-(1 / 2)) φ θ
  have hr : (3 / 4 : ℝ) ≤ 3 / 4 := le_rfl
  have hrone : (3 / 4 : ℝ) < 1 := by norm_num
  obtain ⟨hM, hN, hMN⟩ := suitable_fullBall_canonical_tested_projected_energy
    hsol hbox hr hrone hδ
  have hA := fullBallInitialProjectedBudget_nonneg u D
  have hMB : M ≤ ENNReal.ofReal (fullBallInitialProjectedBudget u D) := by
    apply (ENNReal.le_ofReal_iff_toReal_le hM.ne hA).mpr
    change M.toReal + 2 * N.toReal ≤ fullBallInitialProjectedBudget u D at hMN
    linarith [ENNReal.toReal_nonneg (a := N)]
  have hNB : N ≤ ENNReal.ofReal (fullBallInitialProjectedBudget u D / 2) := by
    apply (ENNReal.le_ofReal_iff_toReal_le hN.ne (div_nonneg hA (by norm_num))).mpr
    change M.toReal + 2 * N.toReal ≤ fullBallInitialProjectedBudget u D at hMN
    linarith [ENNReal.toReal_nonneg (a := M)]
  have hball : vec3Ball 0 (1 / 4 : ℝ) ⊆ vec3Ball 0 ρ :=
    vec3Ball_mono (by norm_num [ρ, fullBallCanonicalPressureRadius])
  have htime : Ioo (-((1 / 4 : ℝ) ^ 2)) (-δ) ⊆ Ioo (-1 : ℝ) 0 := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2]
  have hplateau (z : ParabolicPoint)
      (hz : z ∈ vec3Ball 0 (1 / 4 : ℝ) ×ˢ Ioo (-((1 / 4 : ℝ) ^ 2)) (-δ)) :
      φ z.1 ^ 6 * θ z.2 = 1 := by
    apply fullBallCanonical_test_eq_one hr hrone hδ
    exact ⟨vec3Ball_mono (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4) hz.1,
      by nlinarith [hz.2.1], hz.2.2⟩
  have hθ : ∀ t, 0 ≤ θ t := fun t ↦
    ((fullBallCanonical_time_data hr hrone hδ).2.2.1 t).1
  refine ⟨(fullBall_projected_sliceEnergy_le_tested_plateau u D p (-1) 0 (-(1 / 2))
    (-((1 / 4 : ℝ) ^ 2)) (-δ) hθ hball htime hplateau).trans hMB, ?_⟩
  exact (fullBall_projected_dissipation_le_tested_plateau ρ u D p (-1) 0 (-(1 / 2))
    (-((1 / 4 : ℝ) ^ 2)) (-δ) (vec3Ball_measurable 0 ρ)
    (fullBallCanonical_spatial_support hr hrone) (fullBallCanonical_ball_subset_compact _)
    hθ hball htime hplateau).trans hNB

/-- Actual suitability bounds full projected slice energy and dissipation at radius one quarter. -/
theorem suitable_fullBall_initial_projected_energy_bounds
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0)) :
    fullBallProjectedIterationSliceEnergy u D p (-1) 0 (-(1 / 2)) (1 / 4) 0 ≤
      ENNReal.ofReal (fullBallInitialProjectedBudget u D) ∧
    fullBallProjectedIterationDissipation u D p (-1) 0 (-(1 / 2)) (1 / 4) 0 ≤
      ENNReal.ofReal (fullBallInitialProjectedBudget u D / 2) := by
  constructor
  · simp only [fullBallProjectedIterationSliceEnergy, zero_sub]
    apply essSup_Ioo_le_of_terminal_truncations (by norm_num)
    intro δ hδ _
    simpa only [zero_sub] using (suitable_fullBall_initial_projected_truncated_bounds
      hsol hbox hδ).1
  · simp only [fullBallProjectedIterationDissipation, zero_sub]
    apply lintegral_parabolic_cylinder_le_of_terminal_truncations (by norm_num)
    intro δ hδ _
    exact (suitable_fullBall_initial_projected_truncated_bounds hsol hbox hδ).2

/-- The true normalized initial projected energy has an explicit finite unit-data budget. -/
theorem suitable_fullBall_initial_normalized_projected_energy_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0)) :
    fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 (-(1 / 2)) (1 / 4) 0 ≤
      ENNReal.ofReal (6 * fullBallInitialProjectedBudget u D) := by
  obtain ⟨hM, hN⟩ := suitable_fullBall_initial_projected_energy_bounds hsol hbox
  have hA := fullBallInitialProjectedBudget_nonneg u D
  unfold fullBallNormalizedProjectedIterationEnergy
  calc
    _ ≤ ENNReal.ofReal ((1 / 4 : ℝ)⁻¹) *
        (ENNReal.ofReal (fullBallInitialProjectedBudget u D) +
          ENNReal.ofReal (fullBallInitialProjectedBudget u D / 2)) :=
      mul_le_mul' le_rfl (add_le_add hM hN)
    _ = _ := by
      rw [← ENNReal.ofReal_add hA (div_nonneg hA (by norm_num)),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ (1 / 4 : ℝ)⁻¹)]
      congr 1
      ring

end FluidSingularSets
