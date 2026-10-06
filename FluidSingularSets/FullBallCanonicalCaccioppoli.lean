-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.FullBallTestedCaccioppoli
public import FluidSingularSets.FullBallCanonicalCutoffData
public import FluidSingularSets.FullBallGradientMomentFinite

/-!
# Genuine unit-cylinder Caccioppoli bound with canonical cutoffs

The actual cutoff data discharge every test hypothesis in the suitable energy
estimate. Choosing the viscous Young parameter to be one thirty-second gives
three-quarter contraction against the literal original coordinate gradient.
The endpoint source coefficients have no dependence on the terminal cap.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- The actual canonical linear source coefficient, including original-gradient transfer. -/
def fullBallCanonicalLinearSourceCoefficient (r : ℝ) : ℝ :=
  4 * fullBallEndpointQuadraticCost (fullBallCanonicalPressureRadius r)
    (64 / (1 - r)) (4 * canonicalBallCutoffSixthLaplacianConstant / (1 - r) ^ 2)
      (32 / (1 - r)) (1 / 32) +
  2 * (fullBallProjectedVelocitySliceCoefficient (fullBallCanonicalPressureRadius r)).toReal ^ 2 +
  18 * (fullBallProjectedHarmonicSquareCoefficient (fullBallCanonicalPressureRadius r)).toReal

/-- The actual canonical squared-source coefficient from pressure/Hessian absorption. -/
def fullBallCanonicalQuadraticSourceCoefficient (r : ℝ) : ℝ :=
  32 * fullBallEndpointPressureCost (fullBallCanonicalPressureRadius r) (64 / (1 - r)) ^ 2

/-- The actual canonical fourth-source coefficient from sharp convection absorption. -/
def fullBallCanonicalFourthSourceCoefficient (r : ℝ) : ℝ :=
  131072 * fullBallEndpointConvectionCost (fullBallCanonicalPressureRadius r)
    (64 / (1 - r)) (-1) 0 ^ 6

/-- Every actual suitable unit box has a genuine terminal-independent truncated energy bound. -/
theorem suitable_fullBall_canonical_truncated_caccioppoli
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {D : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u D p (fun _ ↦ 0))
    (hbox : localBox Ω I (vec3Ball 0 1) (Ioo (-1 : ℝ) 0))
    {r δ : ℝ} (hr : (3 / 4 : ℝ) ≤ r) (hrone : r < 1) (hδ : 0 < δ) :
    let X := (∫⁻ t in Ioo (-1 : ℝ) 0, eLpNorm (fun x ↦ u (x, t)) 6
      (volume.restrict (vec3Ball 0 1)) ^ 2).toReal
    (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) (-δ),
      ENNReal.ofReal (projectedGradientSquare (D z))) < ⊤ ∧
    (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) (-δ),
      ENNReal.ofReal (projectedGradientSquare (D z))).toReal ≤
      (3 / 4) * (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo (-1 : ℝ) 0,
        ENNReal.ofReal (projectedGradientSquare (D z))).toReal +
      fullBallCanonicalLinearSourceCoefficient r * X +
      fullBallCanonicalQuadraticSourceCoefficient r * X ^ 2 +
      fullBallCanonicalFourthSourceCoefficient r * X ^ 4 := by
  obtain ⟨hr0, hrR, hR0, hRρ, hρ0, hρone, _hw⟩ := fullBallCanonical_radii hr hrone
  obtain ⟨hφ, hcφ, hbφ, _hs⟩ := fullBallCanonical_spatial_data hr hrone
  obtain ⟨hθ, hcθ, hbθ, _hts, _hdt, hdθ⟩ := fullBallCanonical_time_data hr hrone hδ
  have hsubset : (vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) (-δ) : Set ParabolicPoint) ⊆
      vec3Ball 0 (fullBallCanonicalPressureRadius r) ×ˢ Ioo (-1 : ℝ) 0 := by
    intro z hz
    refine ⟨vec3Ball_mono (hrR.trans hRρ).le hz.1, ?_, ?_⟩
    · nlinarith [hz.2.1, mul_pos hr0 (sub_pos.mpr hrone)]
    · linarith [hz.2.2]
  have hplateau (z : ParabolicPoint)
      (hz : z ∈ vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) (-δ)) :
      fullBallCanonicalSpatialCutoff r z.1 ^ 6 * fullBallCanonicalTimeCutoff r δ z.2 = 1 :=
    fullBallCanonical_test_eq_one hr hrone hδ hz
  have hψ : fullBallSeparatedCutoffTest (fullBallCanonicalSpatialCutoff r)
      (fullBallCanonicalTimeCutoff r δ) ∈ spaceTimeTestFunction (V := ℝ) Ω I :=
    fullBallCanonical_test_admissible hbox hr hrone hδ
  have hsupport := fullBallCanonical_test_support_compact hr hrone hδ
  have hsupportB := fullBallCanonical_test_support hr hrone hδ
  have hh := suitable_fullBall_tested_original_gradient_caccioppoli
    hsol hbox (by norm_num : (-1 : ℝ) < 0) (c := -(1 / 2)) (by constructor <;> norm_num)
    hρ0 hρone (isOpen_vec3Ball 0 _) (fullBallCanonical_ball_subset_compact r)
    hφ hcφ (fullBallCanonical_spatial_support hr hrone) hbφ
    (L := 64 / (1 - r)) (by positivity) (fullBallCanonical_gradient_bound hr hrone)
    (Λ := 4 * canonicalBallCutoffSixthLaplacianConstant / (1 - r) ^ 2)
    (by positivity [canonicalBallCutoffSixthLaplacianConstant_nonneg])
    (fun x ↦ by simpa only [Real.norm_eq_abs] using fullBallCanonical_laplacian_bound hr hrone x)
    hθ hcθ hbθ (T := 32 / (1 - r)) (by positivity) hdθ
    hψ hsupport hsupportB ((isOpen_vec3Ball 0 r).measurableSet.prod measurableSet_Ioo)
    hsubset hplateau (δ := 1 / 32) (by norm_num)
  dsimp only at hh ⊢
  have hE : (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo (-1 : ℝ) 0,
      ‖D z‖ₑ ^ (2 : ℝ)).toReal ≤
      (∫⁻ z : ParabolicPoint in vec3Ball 0 1 ×ˢ Ioo (-1 : ℝ) 0,
        ENNReal.ofReal (projectedGradientSquare (D z))).toReal :=
    ENNReal.toReal_mono (suitable_fullBall_gradient_coordinate_moment_lt_top hsol hbox).ne
      (lintegral_mono fun z ↦ gradient_enorm_square_le_coordinate (D z))
  refine ⟨hh.1, hh.2.trans ?_⟩
  dsimp only [fullBallCanonicalLinearSourceCoefficient,
    fullBallCanonicalQuadraticSourceCoefficient, fullBallCanonicalFourthSourceCoefficient]
  norm_num only [show (24 : ℝ) * (1 / 32) = 3 / 4 by norm_num]
  gcongr

end FluidSingularSets
