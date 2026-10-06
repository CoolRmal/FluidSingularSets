-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallNonlinearPressureDecay
public import FluidSingularSets.FullBallIterationPressureAlgebra

/-!
# Real-valued actual nonlinear-pressure iteration

Actual suitable data supply the finiteness needed to convert the genuine
normalized pressure contraction to real coefficients. No pressure, energy,
or velocity integrability conclusion is assumed.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

section Suitable

variable {Ω : Set Vec3} {I : Set ℝ} {q c r s : ℝ}
  {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
  {p : ParabolicPoint → ℝ}

/-- Genuine suitable data give the real normalized nonlinear-pressure contraction. -/
theorem suitable_fullBall_normalized_convective_oscillation_power_decay_iteration_toReal
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0))
    (hc : c ∈ Ioo (-1) 0) (hr : 0 < r) (hrhalf : r < 1 / 2)
    (hs : 0 < s) (hshalf : s ≤ 1 / 2) :
    (fullBallNormalizedConvectiveOscillation u (r * s) 0).toReal ^ (3 / 2 : ℝ) ≤
      fullBallNonlinearPressurePowerSourceConstant.toReal * s ^ (-9 / 4 : ℝ) *
        ((fullBallEndpointIterationQuantity u D p (-1) 0 c r 0).toReal ^ (3 / 2 : ℝ) +
          (fullBallOriginalEndpointSixSquareMoment u).toReal ^ (3 / 2 : ℝ)) +
      fullBallNonlinearPressurePowerContractionConstant.toReal * s ^ (3 / 2 : ℝ) *
        (fullBallEndpointIterationQuantity u D p (-1) 0 c r 0).toReal := by
  let E := fullBallEndpointIterationQuantity u D p (-1) 0 c r 0
  let X := fullBallOriginalEndpointSixSquareMoment u
  have hE : E ≠ ⊤ :=
    (suitable_fullBall_endpoint_iteration_quantity_lt_top hsol hbox hc hr hrhalf).ne
  have hX : X ≠ ⊤ :=
    (suitable_fullBall_original_endpoint_six_square_moment_lt_top hsol hbox).ne
  have hEr : E ^ (3 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hE
  have hXr : X ^ (3 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hX
  have hsr : ENNReal.ofReal s ^ (-9 / 4 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.mpr hs).ne'
      ENNReal.ofReal_ne_top
  have hsc : ENNReal.ofReal s ^ (3 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hsource : fullBallNonlinearPressurePowerSourceConstant *
      ENNReal.ofReal s ^ (-9 / 4 : ℝ) * (E ^ (3 / 2 : ℝ) + X ^ (3 / 2 : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top fullBallNonlinearPressurePowerSourceConstant_ne_top hsr)
      (ENNReal.add_ne_top.mpr ⟨hEr, hXr⟩)
  have hcontract : fullBallNonlinearPressurePowerContractionConstant *
      ENNReal.ofReal s ^ (3 / 2 : ℝ) * E ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top fullBallNonlinearPressurePowerContractionConstant_ne_top hsc) hE
  have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hsource, hcontract⟩)
    (suitable_fullBall_normalized_convective_oscillation_power_decay_iteration
      hsol hbox hc hr hrhalf hs hshalf)
  rw [ENNReal.toReal_add hsource hcontract] at hh
  simp only [ENNReal.toReal_mul] at hh
  rw [ENNReal.toReal_add hEr hXr] at hh
  simpa only [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hs.le] using hh

/-- The initial genuine centered nonlinear-pressure source bound also holds in real form. -/
theorem suitable_fullBall_initial_convective_oscillation_le_source_toReal
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1) 0)) :
    (fullBallNormalizedConvectiveOscillation u (1 / 4) 0).toReal ≤
      fullBallInitialConvectiveOscillationConstant.toReal *
        (fullBallOriginalEndpointSixSquareMoment u).toReal := by
  have hX := (suitable_fullBall_original_endpoint_six_square_moment_lt_top hsol hbox).ne
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_ne_top fullBallInitialConvectiveOscillationConstant_ne_top hX)
    (suitable_fullBall_initial_convective_oscillation_le_source hsol hbox)
  simpa only [ENNReal.toReal_mul] using hh

end Suitable

end FluidSingularSets
