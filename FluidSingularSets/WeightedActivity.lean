module

public import FluidSingularSets.PersistentActivity

/-!
# Divergent weights for persistent activity

This extends the scalar activity argument to every decreasing nonnegative nonsummable weight.
Iterated logarithmic gauges use the reciprocal products of successive logarithms as weights.
-/

@[expose] public section

open Finset

namespace FluidSingularSets

/-- A negative drift requires nonsummable compensation for every decreasing divergent weight. -/
theorem not_summable_weighted_compensation_of_drift (L b w : ℕ → ℝ) {a : ℝ}
    (ha : 0 < a) (hL : ∀ n, 0 ≤ L n) (hb : ∀ n, 0 ≤ b n)
    (hw : ∀ n, 0 ≤ w n) (hanti : Antitone w) (hdiverge : ¬ Summable w)
    (hdrift : ∀ n, L (n + 1) - L n ≤ -a + b n) :
    ¬ Summable (fun n ↦ w n * b n) := by
  intro hsum
  have hpartial : ∀ N, a * ∑ n ∈ range N, w n ≤
      (∑' n, w n * b n) + w 0 * L 0 := by
    intro N
    have hlower := weighted_increments_lower_bound L w hL hw hanti N
    have hupper : (∑ n ∈ range N, w n * (L (n + 1) - L n)) ≤
        -a * (∑ n ∈ range N, w n) + ∑ n ∈ range N, w n * b n := by
      calc
        _ ≤ ∑ n ∈ range N, w n * (-a + b n) :=
          sum_le_sum fun n _ ↦ mul_le_mul_of_nonneg_left (hdrift n) (hw n)
        _ = _ := by simp_rw [mul_add]; rw [sum_add_distrib, ← sum_mul]; ring
    have hbound := hsum.sum_le_tsum (range N) (fun n _ ↦ mul_nonneg (hw n) (hb n))
    linarith
  apply hdiverge
  apply summable_of_sum_range_le hw
    (c := ((∑' n, w n * b n) + w 0 * L 0) / a)
  intro N
  apply (le_div_iff₀ ha).2
  nlinarith [hpartial N]

/-- The recurrence forces infinite activity cost against every decreasing divergent weight. -/
theorem persistent_activity_weighted_not_summable (G e w : ℕ → ℝ) {ε C : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C) (hG : ∀ n, ε ≤ G n) (he : ∀ n, 0 ≤ e n)
    (hw : ∀ n, 0 ≤ w n) (hanti : Antitone w) (hdiverge : ¬ Summable w)
    (hrec : ∀ n, G (n + 1) ≤ G n / 4 + C * Real.sqrt (G n) * e n) :
    ¬ Summable (fun n ↦ w n * e n / Real.sqrt (G n)) := by
  have hpos : ∀ n, 0 < G n := fun n ↦ hε.trans_le (hG n)
  let L : ℕ → ℝ := fun n ↦ Real.log (G n / ε)
  let b : ℕ → ℝ := fun n ↦ C * e n / Real.sqrt (G n)
  have hL : ∀ n, 0 ≤ L n := fun n ↦ Real.log_nonneg ((one_le_div hε).2 (hG n))
  have hb : ∀ n, 0 ≤ b n := fun n ↦
    div_nonneg (mul_nonneg hC (he n)) (Real.sqrt_nonneg (G n))
  have hdrift : ∀ n, L (n + 1) - L n ≤ -(3 / 4 : ℝ) + b n := by
    intro n
    dsimp [L, b]
    rw [Real.log_div (hpos (n + 1)).ne' hε.ne', Real.log_div (hpos n).ne' hε.ne']
    linarith [log_increment_le_of_recurrence (hpos n) (hpos (n + 1)) (hrec n)]
  have hnonsum := not_summable_weighted_compensation_of_drift L b w
    (by norm_num : (0 : ℝ) < 3 / 4) hL hb hw hanti hdiverge hdrift
  intro hsum
  apply hnonsum
  convert hsum.mul_left C using 1
  ext n
  dsimp [b]
  ring

end FluidSingularSets
