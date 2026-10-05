-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallDissipationTransport

/-!
# Actual original gradient controlled by the genuine tested dissipation

The literal compact-subtype tested dissipation controls the original solution
on every measurable spacetime patch where the actual separated test is one.
The harmonic correction is bounded by the genuine endpoint source moment.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A true unit plateau transfers the compact tested dissipation to the original gradient. -/
theorem suitable_fullBall_original_gradient_le_tested_dissipation
    {Ω : Set Vec3} {I : Set ℝ} {q a b c ρ : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {A : Set ParabolicPoint} {B : Set Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo a b)) (hab : a < b) (hc : c ∈ Ioo a b)
    (hρ : 0 < ρ) (hρone : ρ < 1) (hA : MeasurableSet A) (hB : IsOpen B)
    (hBK : B ⊆ fullBallCompactInterior ρ) (hAB : A ⊆ B ×ˢ Ioo a b)
    {φ : Vec3 → ℝ} {θ : ℝ → ℝ} (hs : tsupport φ ⊆ B) (hθ : ∀ t, 0 ≤ θ t)
    (hψone : ∀ z ∈ A, φ z.1 ^ 6 * θ z.2 = 1) :
    (∫⁻ z in A, ENNReal.ofReal (projectedGradientSquare (D z))) ≤
      2 * fullBallTimeWeightedProjectedDissipation ρ u D p a b c φ θ +
      18 * fullBallProjectedHarmonicSquareCoefficient ρ *
        ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
          (volume.restrict (vec3Ball 0 1)) ^ 2 := by
  have he := fullBall_original_gradient_le_actual_tested_projected_and_source
    hsol hbox hab hc hρ hρone hA hB hBK hAB hψone
  have htest : (∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
      ENNReal.ofReal (projectedGradientSquare
        (fullBallProjectedVelocityDerivativeAmbient u D p a b c z)) *
          ENNReal.ofReal (φ z.1 ^ 6 * θ z.2)) =
      fullBallTimeWeightedProjectedDissipation ρ u D p a b c φ θ := by
    calc
      _ = ∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b,
          ENNReal.ofReal (projectedGradientSquare
            (fullBallProjectedVelocityDerivativeAmbient u D p a b c z)) *
              ENNReal.ofReal (φ z.1 ^ 6) * ENNReal.ofReal (θ z.2) := by
        apply lintegral_congr
        intro z
        rw [ENNReal.ofReal_mul' (hθ z.2)]
        ring
      _ = _ := (fullBallTimeWeightedProjectedDissipation_eq_native
        ρ u D p a b c hB.measurableSet hs hBK hθ).symm
  exact he.trans_eq (congrArg (fun v : ℝ≥0∞ ↦ 2 * v +
    18 * fullBallProjectedHarmonicSquareCoefficient ρ *
      ∫⁻ t in Ioo a b, eLpNorm (fun x ↦ u (x, t)) 6
        (volume.restrict (vec3Ball 0 1)) ^ 2) htest)

end FluidSingularSets
