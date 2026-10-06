-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedCaccioppoliAlgebra

/-!
# Genuine pressure absorption for the shrinking-scale iteration

Young exponents three halves and three absorb the nonlinear pressure energy
factor I^(7/6) into a small linear energy term and a true I^(3/2) remainder.
-/

@[expose] public section

open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- Scaled Young absorption with energy exponent two thirds. -/
theorem twoThirds_energy_absorption {a Y δ : ℝ}
    (ha : 0 ≤ a) (hY : 0 ≤ Y) (hδ : 0 < δ) :
    a * Y ^ (2 / 3 : ℝ) ≤ δ * Y + a ^ 3 / δ ^ 2 := by
  let u := (δ * Y) ^ (2 / 3 : ℝ)
  let v := a / δ ^ (2 / 3 : ℝ)
  have hp : Real.HolderConjugate (3 / 2) 3 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := Real.young_inequality_of_nonneg
    (Real.rpow_nonneg (mul_nonneg hδ.le hY) (2 / 3)) (div_nonneg ha
      (Real.rpow_nonneg hδ.le (2 / 3))) hp
  have hprod : u * v = a * Y ^ (2 / 3 : ℝ) := by
    dsimp [u, v]
    rw [Real.mul_rpow hδ.le hY]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hδ (2 / 3))]
  have hu : u ^ (3 / 2 : ℝ) = δ * Y := by
    dsimp [u]
    rw [← Real.rpow_mul (mul_nonneg hδ.le hY)]
    norm_num
  have hv : v ^ (3 : ℝ) = a ^ 3 / δ ^ 2 := by
    dsimp [v]
    rw [Real.div_rpow ha (Real.rpow_nonneg hδ.le (2 / 3)), ← Real.rpow_mul hδ.le]
    norm_num
  change u * v ≤ u ^ (3 / 2 : ℝ) / (3 / 2) + v ^ (3 : ℝ) / 3 at h
  rw [hprod, hu, hv] at h
  have hfirst := mul_nonneg hδ.le hY
  have hlast : 0 ≤ a ^ 3 / δ ^ 2 := by positivity
  nlinarith

/-- The true pressure exponent seven sixths produces an energy remainder of three halves. -/
theorem sevenSixths_pressure_iteration_absorption {C Y δ : ℝ}
    (hC : 0 ≤ C) (hY : 0 ≤ Y) (hδ : 0 < δ) :
    C * Y ^ (7 / 6 : ℝ) ≤ δ * Y + C ^ 3 / δ ^ 2 * Y ^ (3 / 2 : ℝ) := by
  have h := twoThirds_energy_absorption
    (mul_nonneg hC (Real.rpow_nonneg hY (1 / 2))) hY hδ
  have he : (Y ^ (1 / 2 : ℝ)) ^ 3 = Y ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY]
    norm_num
  have hp : C * Y ^ (1 / 2 : ℝ) * Y ^ (2 / 3 : ℝ) = C * Y ^ (7 / 6 : ℝ) := by
    rw [mul_assoc, ← Real.rpow_add' hY (by norm_num : (1 / 2 + 2 / 3 : ℝ) ≠ 0)]
    norm_num
  rw [hp, mul_pow, he] at h
  convert h using 1
  ring

end FluidSingularSets
