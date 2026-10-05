module

public import FluidSingularSets.IteratedLogSeries
public import FluidSingularSets.WeightedActivity

/-! # Persistent activity for all finite iterated logarithmic gauges -/

@[expose] public section

open Finset Filter

namespace FluidSingularSets

/-- At every finite logarithmic depth, persistent activity has infinite weighted cost.
The finite shift ensures that all logarithmic denominator factors are positive. -/
theorem persistent_activity_iteratedLog_tendsto_sum_atTop
    (k : ℕ) (G e : ℕ → ℝ) {ε C : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C) (hG : ∀ n, ε ≤ G n) (he : ∀ n, 0 ≤ e n)
    (hrec : ∀ n, G (n + 1) ≤ G n / 4 + C * Real.sqrt (G n) * e n) :
    ∃ N : ℕ, Tendsto (fun M ↦ ∑ n ∈ range M,
      reciprocalLogWeight k (n + N : ℕ) * e n / Real.sqrt (G n)) atTop atTop := by
  obtain ⟨N, hpositive, hanti, hdiverge⟩ :=
    exists_positive_antitone_nonsummable_reciprocalLogWeight_tail k
  refine ⟨N, ?_⟩
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n ↦
    div_nonneg (mul_nonneg (hpositive n).le (he n)) (Real.sqrt_nonneg (G n)))).1
  exact persistent_activity_weighted_not_summable G e
    (fun n ↦ reciprocalLogWeight k (n + N : ℕ)) hε hC hG he
    (fun n ↦ (hpositive n).le) hanti hdiverge hrec

end FluidSingularSets
