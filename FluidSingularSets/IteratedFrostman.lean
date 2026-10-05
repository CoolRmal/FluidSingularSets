module

public import FluidSingularSets.GaugeFrostmanConstruction
public import FluidSingularSets.LogGaugeRegularity

/-!
# Frostman measures for every finite logarithmic gauge

The actual compact-set construction applies to every finite logarithmic depth.
Its local monotonicity and doubling hypotheses follow from the proved gauge calculus.
-/

@[expose] public section

open MeasureTheory Set CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

noncomputable section

namespace FluidSingularSets

/-- All finite-radius values of the logarithmic gauges are finite. -/
theorem iteratedLogGauge_ne_top (k : ℕ) {d : ℝ≥0∞} (hd : d ≠ ∞) :
    iteratedLogGauge k d ≠ ∞ := by
  simp only [iteratedLogGauge, hd, ↓reduceIte]
  exact ENNReal.ofReal_ne_top

/-- Every fixed finite-depth gauge satisfies all local Frostman regularity conditions. -/
theorem exists_iteratedLogGauge_frostman_radius (k : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      MonotoneOn (iteratedLogGauge k) (Icc 0 (ENNReal.ofReal ρ)) ∧
      iteratedLogGauge k (ENNReal.ofReal ρ) ≠ ∞ ∧
      ∀ r : ℝ, 0 < r → 2 * r ≤ ρ →
        iteratedLogGauge k (ENNReal.ofReal (2 * r)) ≤
          2 * iteratedLogGauge k (ENNReal.ofReal r) := by
  obtain ⟨ρ₁, hρ₁, hmono⟩ := exists_small_radius_monotone_iteratedLogGauge k
  obtain ⟨ρ₂, hρ₂, hdouble⟩ := exists_small_radius_doubling_iteratedLogGauge k
  let ρ := min ρ₁ ρ₂
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  refine ⟨ρ, hρ, ?_, iteratedLogGauge_ne_top k ENNReal.ofReal_ne_top, ?_⟩
  · apply monotoneOn_gauge_of_monotoneOn_ofReal _ ρ hρ.le
    exact hmono.mono (Icc_subset_Icc le_rfl (min_le_left _ _))
  · intro r hr hsmall
    exact hdouble r hr (hsmall.trans (min_le_right _ _))

/-- Positive compact Hausdorff measure for any finite logarithmic gauge produces
a supported probability measure with the actual small-ball growth estimate. -/
theorem exists_iteratedLogGauge_frostman_measure (k : ℕ) (K : Set ParabolicPoint)
    (hK : IsCompact K)
    (hpos : 0 < (Measure.mkMetric (iteratedLogGauge k) : Measure ParabolicPoint) K) :
    ∃ (μ : Measure ParabolicPoint) (C : ℝ≥0∞) (r₀ : ℝ),
      IsFiniteMeasure μ ∧ μ ≠ 0 ∧ μ Kᶜ = 0 ∧ μ K = 1 ∧ C ≠ ∞ ∧ 0 < r₀ ∧
        ∀ (z : ParabolicPoint) (r : ℝ), 0 < r → r < r₀ →
          μ (Metric.ball z r) ≤ C * iteratedLogGauge k (ENNReal.ofReal r) := by
  obtain ⟨ρ, hρ, hmono, hfinite, hdouble⟩ := exists_iteratedLogGauge_frostman_radius k
  exact exists_parabolic_gauge_frostman_measure (iteratedLogGauge k) K hK hpos
    ρ hρ (iteratedLogGauge_zero k) hmono hfinite hdouble

end FluidSingularSets
