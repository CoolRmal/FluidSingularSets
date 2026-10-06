-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallGaussianEnergyStep
public import FluidSingularSets.ProjectedGaussianScalarRecurrence
public import FluidSingularSets.FullBallNonlinearPressureReal

/-!
# Genuine suitable-solution endpoint iteration step

The actual projected Gaussian energy estimate and the actual nonlinear-pressure
contraction combine into one universal scale recurrence for the literal
iteration quantity. All finiteness and energy estimates come from suitable
weak-solution data.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A finite iteration quantity is the sum of its real energy and pressure powers. -/
theorem fullBallEndpointIterationQuantity_toReal_of_ne_top
    (u : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (a b c r τ : ℝ)
    (hI : fullBallEndpointIterationQuantity u D p a b c r τ ≠ ⊤) :
    (fullBallEndpointIterationQuantity u D p a b c r τ).toReal =
      (fullBallNormalizedProjectedIterationEnergy u D p a b c r τ).toReal +
        (fullBallNormalizedConvectiveOscillation u r τ).toReal ^ (3 / 2 : ℝ) := by
  unfold fullBallEndpointIterationQuantity at hI ⊢
  have hf := ENNReal.add_ne_top.mp hI
  rw [ENNReal.toReal_add hf.1 hf.2, ← ENNReal.toReal_rpow]

/-- Actual suitable data give the universal projected energy and nonlinear-pressure recurrence. -/
theorem suitable_fullBall_endpoint_iteration_step
    {Ω : Set Vec3} {I : Set ℝ} {q c r ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) (hc : c ∈ Ioo (-1) 0)
    (hr : 0 < r) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (hscale : r < ρ / 4) :
    let Y := (fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0).toReal
    let X := (fullBallOriginalEndpointSixSquareMoment u).toReal
    (fullBallEndpointIterationQuantity u D p (-1) 0 c r 0).toReal ≤
      (1 / 8 + projectedGaussianRecurrenceUniversalConstant * (r / ρ) ^ (3 / 2 : ℝ) +
        projectedGaussianRecurrenceUniversalConstant * X ^ (1 / 2 : ℝ) * (ρ / r) ^ 2) * Y +
      projectedGaussianRecurrenceUniversalConstant * (ρ / r) ^ 6 *
        (Y ^ (3 / 2 : ℝ) + X ^ (3 / 2 : ℝ) + X ^ 2 +
          (coordinateCylinderMass D 1).toReal) := by
  dsimp only
  have hrhalf : r < 1 / 2 := by linarith
  have hrρ : r ≤ ρ := by linarith
  have hIr := suitable_fullBall_endpoint_iteration_quantity_lt_top hsol hbox hc hr hrhalf
  have hIρ := suitable_fullBall_endpoint_iteration_quantity_lt_top hsol hbox hc hρ hρhalf
  have hEY : (fullBallNormalizedProjectedIterationEnergy u D p (-1) 0 c ρ 0).toReal ≤
      (fullBallEndpointIterationQuantity u D p (-1) 0 c ρ 0).toReal :=
    ENNReal.toReal_mono hIρ.ne le_self_add
  have hInner := (fullBallEndpointIterationQuantity_toReal_of_ne_top
    u D p (-1) 0 c r 0 hIr.ne).le
  have hEnergy := suitable_fullBall_gaussian_projected_energy_step_toReal
    hsol hbox hc hr hρ hρhalf hscale
      projectedGaussianAbsorptionParameter_pos projectedGaussianAbsorptionParameter_pos
  have hs : 0 < r / ρ := div_pos hr hρ
  have hshalf : r / ρ ≤ 1 / 2 := (div_le_iff₀ hρ).mpr (by linarith)
  have hPressure :=
    suitable_fullBall_normalized_convective_oscillation_power_decay_iteration_toReal
      hsol hbox hc hρ hρhalf hs hshalf
  have hprod : ρ * (r / ρ) = r := by field_simp [hρ.ne']
  rw [hprod] at hPressure
  exact projectedGaussian_recurrence_from_costs hr hρ hrρ
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg hEY hInner hEnergy hPressure

end FluidSingularSets
