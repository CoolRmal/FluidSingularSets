module

public import FluidSingularSets.MassRatioTrace
public import FluidSingularSets.MixedGradient

/-!
# Algebra of the dissipation trace cost

These identities connect the concrete mixed-gradient box cost to the mass-ratio
trace. The zero-dissipation convention is preserved by real division by zero.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace FluidSingularSets

/-- The mass-ratio trace integrand is exactly the weighted dissipation cost. -/
theorem trace_cost_mass_ratio_identity {m n r F e : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hr : 0 < r) (hF : 0 < F) :
    (Real.sqrt (m * r / F) * e) * Real.sqrt (m / n) =
      m * e / Real.sqrt ((n / r) * F) := by
  rcases eq_or_lt_of_le hn with rfl | hnpos
  · simp
  have hR := (Real.sqrt_pos.2 hr).ne'
  have hN := (Real.sqrt_pos.2 hnpos).ne'
  have hFs := (Real.sqrt_pos.2 hF).ne'
  rw [Real.sqrt_div (mul_nonneg hm hr.le), Real.sqrt_mul hm,
    Real.sqrt_div hm, Real.sqrt_mul (div_nonneg hn hr.le), Real.sqrt_div hn]
  field_simp
  rw [Real.sq_sqrt hm]
  ring

/-- Replacing the spatial integral by its average accounts for the exact side-length
factor in the box mixed-gradient cost. -/
theorem box_mixed_gradient_average_identity {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T] (μ : Measure X) (τ : Measure T)
    (f : T → X → ℝ≥0∞) {r : ℝ≥0∞} (hr₀ : r ≠ 0) (hrTop : r ≠ ∞)
    (hvol : μ Set.univ = r ^ (3 : ℕ)) :
    r ^ (-3 / 2 : ℝ) * (∫⁻ t, (∫⁻ x, f t x ∂μ) ^ (7 / 6 : ℝ) ∂τ) =
      r ^ (2 : ℕ) * (∫⁻ t, (⨍⁻ x, f t x ∂μ) ^ (7 / 6 : ℝ) ∂τ) := by
  have hpow : (r ^ (3 : ℕ)) ^ (7 / 6 : ℝ) = r ^ (7 / 2 : ℝ) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    norm_num
  simp only [laverage_eq, hvol]
  simp_rw [ENNReal.div_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 7 / 6),
    hpow, ENNReal.div_eq_inv_mul, ← ENNReal.rpow_neg]
  rw [lintegral_const_mul']
  · rw [← ENNReal.rpow_natCast r 2, ← mul_assoc,
      ← ENNReal.rpow_add _ _ hr₀ hrTop]
    norm_num
  · exact ENNReal.rpow_ne_top_of_ne_zero hr₀ hrTop

end FluidSingularSets
