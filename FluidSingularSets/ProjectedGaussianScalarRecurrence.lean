-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedGaussianRecurrenceCoefficients

/-!
# Universal real Gaussian energy and pressure recurrence

This is scalar coefficient algebra for the independently proved genuine energy
and pressure bounds. Its inputs retain the literal fixed costs; no analytic
criterion or PDE estimate is assumed here as a replacement for their proofs.
-/

@[expose] public section

open scoped ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

namespace FluidSingularSets

/-- The true nonpressure cost is monotone in its nonnegative outer energy. -/
theorem projectedGaussianNonpressureEnergyCost_mono_energy
    {r ρ η E Y X : ℝ} (hη : 0 < η) (hE : 0 ≤ E) (hX : 0 ≤ X) (hEY : E ≤ Y) :
    projectedGaussianNonpressureEnergyCost r ρ η E X ≤
      projectedGaussianNonpressureEnergyCost r ρ η Y X := by
  have hH := projectedGaussianHeatConstant_nonneg
  have hC := projectedGaussianNonpressureCubicConstant_nonneg
  have hM := projectedGaussianNonpressureMixedConstant_nonneg
  unfold projectedGaussianNonpressureEnergyCost
  gcongr

/-- The literal fixed Gaussian costs coarsen to one universal scale recurrence. -/
theorem projectedGaussian_fixed_costs_le_universal_recurrence
    {r ρ Y X D : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hscale : r ≤ ρ)
    (hY : 0 ≤ Y) (hX : 0 ≤ X) (hD : 0 ≤ D) :
    3000 * (projectedGaussianNonpressureEnergyCost r ρ
      projectedGaussianAbsorptionParameter Y X +
        2 * projectedGaussianPressureYoungCost r ρ projectedGaussianAbsorptionParameter Y D) +
      fullBallNonlinearPressurePowerSourceConstant.toReal * (r / ρ) ^ (-9 / 4 : ℝ) *
        (Y ^ (3 / 2 : ℝ) + X ^ (3 / 2 : ℝ)) +
      fullBallNonlinearPressurePowerContractionConstant.toReal * (r / ρ) ^ (3 / 2 : ℝ) * Y ≤
    (1 / 8 + projectedGaussianRecurrenceUniversalConstant * (r / ρ) ^ (3 / 2 : ℝ) +
      projectedGaussianRecurrenceUniversalConstant * X ^ (1 / 2 : ℝ) * (ρ / r) ^ 2) * Y +
      projectedGaussianRecurrenceUniversalConstant * (ρ / r) ^ 6 *
        (Y ^ (3 / 2 : ℝ) + X ^ (3 / 2 : ℝ) + X ^ 2 + D) := by
  let s := r / ρ
  let t := ρ / r
  let H := 3000 * projectedGaussianHeatConstant
  let N := 3000 * projectedGaussianNonpressureCubicConstant
  let M := 3000 * projectedGaussianNonpressureMixedConstant
  let A := 1500 * projectedGaussianHarmonicLinearConstant ^ 2 /
    projectedGaussianAbsorptionParameter
  let P := 6000 * projectedGaussianConvectivePressureConstant ^ 3 /
    projectedGaussianAbsorptionParameter ^ 2
  let V := 6000 * projectedGaussianViscousPressureConstant ^ 2 /
    projectedGaussianAbsorptionParameter
  let S := fullBallNonlinearPressurePowerSourceConstant.toReal
  let L := fullBallNonlinearPressurePowerContractionConstant.toReal
  let U := projectedGaussianRecurrenceUniversalConstant
  have hH : 0 ≤ H := mul_nonneg (by norm_num) projectedGaussianHeatConstant_nonneg
  have hN : 0 ≤ N := mul_nonneg (by norm_num) projectedGaussianNonpressureCubicConstant_nonneg
  have hM : 0 ≤ M := mul_nonneg (by norm_num) projectedGaussianNonpressureMixedConstant_nonneg
  have hκ := projectedGaussianAbsorptionParameter_pos
  have hK := projectedGaussianConvectivePressureConstant_nonneg
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hS : 0 ≤ S := ENNReal.toReal_nonneg
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hU : U = 1 + (H + L) + M + (N + P) + A + V + S := by
    dsimp [U, H, L, M, N, P, A, V, S, projectedGaussianRecurrenceUniversalConstant]
  have hHLU : H + L ≤ U := by linarith
  have hMU : M ≤ U := by linarith
  have hNPSU : N + P + S ≤ U := by linarith
  have hSU : S ≤ U := by linarith
  have hAU : A ≤ U := by linarith
  have hVU : V ≤ U := by linarith
  have hs : 0 < s := div_pos hr hρ
  have hsone : s ≤ 1 := (div_le_one hρ).mpr hscale
  have htone : 1 ≤ t := (one_le_div hr).mpr hscale
  have hsPow : s ^ 2 ≤ s ^ (3 / 2 : ℝ) := by
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_ge hs hsone (by norm_num : (3 / 2 : ℝ) ≤ 2)
  have htTwo : t ^ 2 ≤ t ^ 6 := by
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_le htone (by norm_num : (2 : ℝ) ≤ 6)
  have htFour : t ^ 4 ≤ t ^ 6 := by
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_le htone (by norm_num : (4 : ℝ) ≤ 6)
  have htFrac : t ^ (9 / 4 : ℝ) ≤ t ^ 6 := by
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_le htone (by norm_num : (9 / 4 : ℝ) ≤ 6)
  have hNeg : (r / ρ) ^ (-9 / 4 : ℝ) = t ^ (9 / 4 : ℝ) := by
    rw [neg_div, Real.rpow_neg_eq_inv_rpow, inv_div]
  calc
    _ = (1 / 8 : ℝ) * Y + H * s ^ 2 * Y + N * t ^ 2 * Y ^ (3 / 2 : ℝ) +
        M * t ^ 2 * Y * X ^ (1 / 2 : ℝ) + A * t ^ 2 * X ^ 2 +
        P * t ^ 6 * Y ^ (3 / 2 : ℝ) + V * t ^ 4 * D +
        S * t ^ (9 / 4 : ℝ) * (Y ^ (3 / 2 : ℝ) + X ^ (3 / 2 : ℝ)) +
        L * s ^ (3 / 2 : ℝ) * Y := by
      rw [hNeg]
      dsimp [projectedGaussianNonpressureEnergyCost, projectedGaussianPressureYoungCost,
        H, N, M, A, P, V, S, L, s, t, projectedGaussianAbsorptionParameter]
      ring
    _ ≤ (1 / 8 : ℝ) * Y + H * s ^ (3 / 2 : ℝ) * Y +
        N * t ^ 6 * Y ^ (3 / 2 : ℝ) + M * t ^ 2 * Y * X ^ (1 / 2 : ℝ) +
        A * t ^ 6 * X ^ 2 + P * t ^ 6 * Y ^ (3 / 2 : ℝ) + V * t ^ 6 * D +
        S * t ^ 6 * (Y ^ (3 / 2 : ℝ) + X ^ (3 / 2 : ℝ)) +
        L * s ^ (3 / 2 : ℝ) * Y := by
      gcongr
    _ = (1 / 8 : ℝ) * Y + (H + L) * s ^ (3 / 2 : ℝ) * Y +
        M * t ^ 2 * Y * X ^ (1 / 2 : ℝ) + (N + P + S) * t ^ 6 * Y ^ (3 / 2 : ℝ) +
        S * t ^ 6 * X ^ (3 / 2 : ℝ) + A * t ^ 6 * X ^ 2 + V * t ^ 6 * D := by ring
    _ ≤ (1 / 8 : ℝ) * Y + U * s ^ (3 / 2 : ℝ) * Y +
        U * t ^ 2 * Y * X ^ (1 / 2 : ℝ) + U * t ^ 6 * Y ^ (3 / 2 : ℝ) +
        U * t ^ 6 * X ^ (3 / 2 : ℝ) + U * t ^ 6 * X ^ 2 + U * t ^ 6 * D := by
      gcongr
    _ = _ := by dsimp [U, s, t]; ring

/-- Literal scalar energy and pressure costs imply the single universal Gaussian recurrence. -/
theorem projectedGaussian_recurrence_from_costs
    {r ρ Einner Pinner Iinner Eouter Youter X D : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hscale : r ≤ ρ)
    (hE : 0 ≤ Eouter) (hY : 0 ≤ Youter) (hX : 0 ≤ X) (hD : 0 ≤ D)
    (hEY : Eouter ≤ Youter) (hInner : Iinner ≤ Einner + Pinner)
    (hEnergy : Einner ≤ 3000 *
      (projectedGaussianNonpressureEnergyCost r ρ projectedGaussianAbsorptionParameter Eouter X +
        2 * projectedGaussianPressureYoungCost r ρ projectedGaussianAbsorptionParameter Youter D))
    (hPressure : Pinner ≤
      fullBallNonlinearPressurePowerSourceConstant.toReal * (r / ρ) ^ (-9 / 4 : ℝ) *
        (Youter ^ (3 / 2 : ℝ) + X ^ (3 / 2 : ℝ)) +
      fullBallNonlinearPressurePowerContractionConstant.toReal * (r / ρ) ^ (3 / 2 : ℝ) * Youter) :
    Iinner ≤
      (1 / 8 + projectedGaussianRecurrenceUniversalConstant * (r / ρ) ^ (3 / 2 : ℝ) +
        projectedGaussianRecurrenceUniversalConstant * X ^ (1 / 2 : ℝ) * (ρ / r) ^ 2) * Youter +
      projectedGaussianRecurrenceUniversalConstant * (ρ / r) ^ 6 *
        (Youter ^ (3 / 2 : ℝ) + X ^ (3 / 2 : ℝ) + X ^ 2 + D) := by
  have hCost : 3000 *
      (projectedGaussianNonpressureEnergyCost r ρ projectedGaussianAbsorptionParameter Eouter X +
        2 * projectedGaussianPressureYoungCost r ρ projectedGaussianAbsorptionParameter Youter D) ≤
      3000 *
        (projectedGaussianNonpressureEnergyCost r ρ projectedGaussianAbsorptionParameter Youter X +
          2 * projectedGaussianPressureYoungCost r ρ
            projectedGaussianAbsorptionParameter Youter D) :=
    mul_le_mul_of_nonneg_left
    (add_le_add
      (projectedGaussianNonpressureEnergyCost_mono_energy
        projectedGaussianAbsorptionParameter_pos hE hX hEY) le_rfl)
      (by norm_num : (0 : ℝ) ≤ 3000)
  exact (hInner.trans (add_le_add (hEnergy.trans hCost) hPressure)).trans
    (by simpa only [add_assoc] using
      projectedGaussian_fixed_costs_le_universal_recurrence hr hρ hscale hY hX hD)

end FluidSingularSets
