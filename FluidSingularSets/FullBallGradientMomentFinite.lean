-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallVelocityMomentFinite
public import FluidSingularSets.FullBallProjectedGradientControl

/-!
# Genuine full-ball original coordinate-gradient energy

The actual suitable gradient square moment is finite. Its literal sum of nine
coordinate squares lies between the matrix norm square and nine times that
norm square, so the original dissipation used in radius iteration is finite.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- The literal matrix norm square is bounded by the actual coordinate square density. -/
theorem gradient_enorm_square_le_coordinate (D : Fin 3 → Vec3) :
    ‖D‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (projectedGradientSquare D) := by
  have hh := ENNReal.ofReal_le_ofReal (norm_sq_le_projectedGradientSquare D)
  simpa only [ENNReal.rpow_ofNat, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _)] using hh

/-- Actual suitable energy makes the original full-ball gradient norm moment finite. -/
theorem suitable_fullBall_gradient_norm_moment_lt_top
    {Ω : Set Vec3} {I : Set ℝ} {q a b : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) :
    (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b, ‖D z‖ₑ ^ (2 : ℝ)) < ⊤ :=
  (lintegral_mono fun _ ↦ le_add_left le_rfl).trans_lt
    (hsol.toData.energy_lintegral_lt_top hbox)

/-- The genuine coordinate-gradient energy is finite on every original suitable full ball. -/
theorem suitable_fullBall_gradient_coordinate_moment_lt_top
    {Ω : Set Vec3} {I : Set ℝ} {q a b : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) :
    (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b,
      ENNReal.ofReal (projectedGradientSquare (D z))) < ⊤ := by
  calc
    _ ≤ ∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b, 9 * ‖D z‖ₑ ^ (2 : ℝ) :=
      lintegral_mono fun z ↦ projectedGradientSquare_enorm_le_nine (D z)
    _ = 9 * ∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo a b, ‖D z‖ₑ ^ (2 : ℝ) :=
      lintegral_const_mul' _ _ (by norm_num)
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num)
      (suitable_fullBall_gradient_norm_moment_lt_top hsol hbox)

end FluidSingularSets
