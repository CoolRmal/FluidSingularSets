-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallEndpointCoefficientBounds
public import FluidSingularSets.TruncatedCylinderExhaustion

/-!
# Actual endpoint Caccioppoli on the entire original cylinder

The genuine suitable-solution estimate on terminal truncations passes to the
full cylinder by countable monotone exhaustion. The energy and source below
are the literal coordinate-gradient mass and velocity mixed moment.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Actual unnormalized coordinate-gradient mass of a centered backward cylinder. -/
def coordinateCylinderMass (D : ParabolicPoint → Fin 3 → Vec3) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) 0,
    ENNReal.ofReal (projectedGradientSquare (D z))

/-- Actual squared L²-time/L⁶-space velocity moment on the same cylinder. -/
def velocityCylinderSixMoment (u : ParabolicPoint → Vec3) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (-(r ^ 2)) 0, eLpNorm (fun x ↦ u (x, t)) 6
    (volume.restrict (vec3Ball 0 r)) ^ 2

/-- The genuine unit-cylinder forcing coefficient, independent of the terminal cap. -/
def fullCylinderEndpointForcingConstant : ℝ :=
  fullBallCanonicalEndpointForcingConstant (1 / 32) (-1) 0

/-- The actual coefficient is nonnegative. -/
theorem fullCylinderEndpointForcingConstant_nonneg :
    0 ≤ fullCylinderEndpointForcingConstant :=
  fullBallCanonicalEndpointForcingConstant_nonneg (by norm_num)

/-- Actual suitability gives the full inner-cylinder endpoint estimate. -/
theorem suitable_fullBall_cylinder_caccioppoli
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0))
    {r : ℝ} (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) :
    let X := (velocityCylinderSixMoment u 1).toReal
    coordinateCylinderMass D r < ⊤ ∧
      (coordinateCylinderMass D r).toReal ≤ (3 / 4) * (coordinateCylinderMass D 1).toReal +
        fullCylinderEndpointForcingConstant / (1 - r) ^ 12 * (X + X ^ 2 + X ^ 4) := by
  let A : ℝ := (3 / 4) * (coordinateCylinderMass D 1).toReal +
    fullCylinderEndpointForcingConstant / (1 - r) ^ 12 *
      ((velocityCylinderSixMoment u 1).toReal + (velocityCylinderSixMoment u 1).toReal ^ 2 +
        (velocityCylinderSixMoment u 1).toReal ^ 4)
  have hA : 0 ≤ A := by
    unfold A
    exact add_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
      (mul_nonneg (div_nonneg fullCylinderEndpointForcingConstant_nonneg (by positivity))
        (by positivity))
  have hbound : coordinateCylinderMass D r ≤ ENNReal.ofReal A := by
    apply lintegral_parabolic_cylinder_le_of_terminal_truncations (by linarith)
    intro δ hδ _
    obtain ⟨hfin, hest⟩ := suitable_fullBall_canonical_truncated_gap12 hsol hbox hr hrone hδ
    apply (ENNReal.le_ofReal_iff_toReal_le hfin.ne hA).mpr
    simpa only [A, coordinateCylinderMass, velocityCylinderSixMoment,
      fullCylinderEndpointForcingConstant, one_pow] using hest
  refine ⟨hbound.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  exact ENNReal.toReal_le_of_le_ofReal hA hbound

end FluidSingularSets
