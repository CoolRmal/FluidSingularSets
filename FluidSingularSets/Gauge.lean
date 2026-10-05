module

public import FluidSingularSets.Geometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Properties of the logarithmic Hausdorff gauge -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace FluidSingularSets

@[simp]
theorem logSquaredGauge_zero : logSquaredGauge 0 = 0 := by
  simp [logSquaredGauge, (Real.exp_pos (-2)).le]

@[simp]
theorem logSquaredGauge_top : logSquaredGauge ∞ = ∞ := by
  simp [logSquaredGauge]

/-- The globally extended gauge agrees exactly with the requested gauge at small radii. -/
theorem logSquaredGauge_of_small {d : ℝ≥0∞} (hd : d ≠ ∞)
    (hsmall : d.toReal ≤ Real.exp (-2)) :
    logSquaredGauge d = ENNReal.ofReal (d.toReal * (Real.log (1 / d.toReal)) ^ 2) := by
  simp [logSquaredGauge, hd, hsmall]

/-- At small radii the logarithmic gauge dominates the ordinary linear gauge.
Consequently ordinary CKN Hausdorff nullity alone cannot supply the stronger conclusion. -/
theorem le_logSquaredGauge {d : ℝ≥0∞} (hd : d ≠ ∞)
    (hsmall : d.toReal ≤ Real.exp (-2)) : d ≤ logSquaredGauge d := by
  rw [logSquaredGauge_of_small hd hsmall]
  conv_lhs => rw [← ENNReal.ofReal_toReal hd]
  apply ENNReal.ofReal_le_ofReal
  by_cases hzero : d.toReal = 0
  · simp [hzero]
  have hpos : 0 < d.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
  have hlog : Real.log d.toReal ≤ -2 := by
    simpa using Real.log_le_log hpos hsmall
  rw [one_div, Real.log_inv]
  have hsquare : 1 ≤ (-Real.log d.toReal) ^ 2 := by nlinarith
  nlinarith [ENNReal.toReal_nonneg (a := d)]

/-- The unextended small-radius formula tends to zero at zero. -/
theorem tendsto_smallLogSquaredGauge :
    Tendsto (fun r : ℝ ↦ r * (Real.log (1 / r)) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_log_mul_rpow_nhdsGT_zero (show 0 < (1 / 2 : ℝ) by norm_num)).pow 2
  have hzero : Tendsto (fun r : ℝ ↦ (Real.log r * r ^ (1 / 2 : ℝ)) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by simpa using h
  apply hzero.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hsquare : (r ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hr)]
    norm_num
  simp only [one_div, Real.log_inv, neg_sq, mul_pow]
  simp only [one_div] at hsquare
  rw [hsquare]
  ring

end FluidSingularSets
