module

public import FluidSingularSets.FrostmanCellGrowth
public import FluidSingularSets.IteratedScaling
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# The actual dyadic logarithmic scale weights

The reciprocal square root of the dyadic gauge factor is exactly the iterated harmonic
weight at `n * log 2` once the finitely many logarithms exceed one. Affine comparison
proves divergence along every positive integer step. A sufficiently late initial level
also gives positivity and monotonicity at every term, beyond any requested cutoff.
-/

@[expose] public section

open Set Finset Filter CKN.Foundation.Euclidean
open scoped Topology

noncomputable section

namespace FluidSingularSets

/-- The scalar weight appearing in the concrete dyadic trace cost. -/
def dyadicReciprocalLogWeight (k : ℕ) (n : ℤ) : ℝ :=
  1 / Real.sqrt (dyadicLogFactor k n)

/-- The integer logarithmic scale of a dyadic side is exact. -/
theorem log_inverse_dyadicScale (n : ℤ) :
    Real.log (1 / dyadicScale n) = (n : ℝ) * Real.log 2 := by
  rw [one_div, Real.log_inv, dyadicScale, Real.log_zpow]
  push_cast
  ring

/-- The dyadic trace weight is positive at every level, including before the log cutoff. -/
theorem dyadicReciprocalLogWeight_pos (k : ℕ) (n : ℤ) :
    0 < dyadicReciprocalLogWeight k n := by
  unfold dyadicReciprocalLogWeight
  exact one_div_pos.2 (Real.sqrt_pos.2 (zero_lt_one.trans_le (one_le_dyadicLogFactor k n)))

/-- Once the logarithms exceed one, the dyadic weight is the literal iterated harmonic
weight with one fewer logarithmic factor than the gauge. -/
theorem dyadicReciprocalLogWeight_eq_reciprocalLogWeight
    (K : ℕ) (n : ℤ)
    (hlog : ∀ i ∈ range (K + 1), 1 ≤ logIterate (i + 1) (1 / dyadicScale n)) :
    dyadicReciprocalLogWeight (K + 1) n = reciprocalLogWeight K ((n : ℝ) * Real.log 2) := by
  have hsqrt : Real.sqrt (dyadicLogFactor (K + 1) n) =
      ∏ i ∈ range (K + 1), logIterate i ((n : ℝ) * Real.log 2) := by
    unfold dyadicLogFactor
    rw [Real.sqrt_prod _ (fun i _ ↦ sq_nonneg _)]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Real.sqrt_sq (zero_le_one.trans (le_max_left _ _)), max_eq_right (hlog i hi),
      ← logIterate_apply_log, log_inverse_dyadicScale]
  rw [dyadicReciprocalLogWeight, one_div, hsqrt, reciprocalLogWeight_eq_inv_prod]

/-- Positive affine changes preserve divergence of each iterated harmonic series. -/
theorem not_summable_reciprocalLogWeight_affine (K : ℕ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ¬ Summable (fun j : ℕ ↦ reciprocalLogWeight K (a * j + b)) := by
  intro hsum
  obtain ⟨A, _hA, hpositive, _hanti⟩ := reciprocalLogWeight_positive_antitone_tail K
  have hnat : Tendsto (fun j : ℕ ↦ (j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hcomp := hnat.eventually (eventually_reciprocalLogWeight_affine_comparable K ha b)
  have htail := hnat.eventually (eventually_ge_atTop A)
  let c := a⁻¹ / 2
  have hc : 0 < c := by dsimp [c]; positivity
  apply not_summable_reciprocalLogWeight K
  apply (hsum.mul_left c⁻¹).of_norm_bounded_eventually_nat
  filter_upwards [hcomp, htail] with j hj hAj
  rw [Real.norm_of_nonneg (hpositive _ hAj).le]
  have h := (le_div_iff₀ hc).2 (by simpa only [mul_comm] using hj.1)
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- The arithmetic progression of actual integer dyadic levels. -/
def dyadicLogLevel (N M : ℤ) (j : ℕ) : ℤ := N + M * (j : ℤ)

/-- Nonnegative refinement never crosses below the initial level. -/
theorem dyadicLogLevel_ge_initial (N : ℤ) {M : ℤ} (hM : 0 ≤ M) (j : ℕ) :
    N ≤ dyadicLogLevel N M j := by
  exact le_add_of_nonneg_right (mul_nonneg hM (Int.natCast_nonneg j))

/-- Nonnegative refinement gives a monotone level sequence. -/
theorem dyadicLogLevel_monotone (N : ℤ) {M : ℤ} (hM : 0 ≤ M) :
    Monotone (dyadicLogLevel N M) := by
  intro i j hij
  have hijInt : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hijInt hM)

/-- The integer grid progression and its real affine logarithmic argument agree exactly. -/
theorem dyadicLogLevel_argument (N M : ℤ) (j : ℕ) :
    (dyadicLogLevel N M j : ℝ) * Real.log 2 =
      ((M : ℝ) * Real.log 2) * (j : ℝ) + (N : ℝ) * Real.log 2 := by
  unfold dyadicLogLevel
  push_cast
  ring

/-- Every sufficiently late arithmetic progression of dyadic levels has positive,
antitone, nonsummable weights, and retains an arbitrary requested initial cutoff. -/
theorem exists_positive_antitone_nonsummable_dyadicLogWeight_tail
    (K : ℕ) {M : ℤ} (hM : 0 < M) (N₀ : ℤ) :
    ∃ N : ℤ, N₀ ≤ N ∧
      (∀ j, 0 < dyadicReciprocalLogWeight (K + 1) (dyadicLogLevel N M j)) ∧
      Antitone (fun j ↦ dyadicReciprocalLogWeight (K + 1) (dyadicLogLevel N M j)) ∧
      (¬ Summable (fun j ↦ dyadicReciprocalLogWeight (K + 1) (dyadicLogLevel N M j))) ∧
      (∀ j, dyadicReciprocalLogWeight (K + 1) (dyadicLogLevel N M j) =
        reciprocalLogWeight K ((dyadicLogLevel N M j : ℝ) * Real.log 2)) := by
  obtain ⟨n₀, hcut⟩ := exists_dyadicLogFactor_frostman_cutoff (K + 1)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  let N := max N₀ n₀
  have hlevels (j : ℕ) : n₀ ≤ dyadicLogLevel N M j := by
    have hNj : N ≤ dyadicLogLevel N M j := by
      exact dyadicLogLevel_ge_initial N hM.le j
    exact (le_max_right _ _).trans hNj
  have heq (j : ℕ) : dyadicReciprocalLogWeight (K + 1) (dyadicLogLevel N M j) =
      reciprocalLogWeight K ((dyadicLogLevel N M j : ℝ) * Real.log 2) := by
    apply dyadicReciprocalLogWeight_eq_reciprocalLogWeight
    intro i hi
    exact (hcut _ (hlevels j)).2.2.1 (i + 1) (by simpa using mem_range.1 hi)
  refine ⟨N, le_max_left _ _, fun j ↦ dyadicReciprocalLogWeight_pos _ _, ?_, ?_, heq⟩
  · intro i j hij
    have hlevel : dyadicLogLevel N M i ≤ dyadicLogLevel N M j := by
      exact dyadicLogLevel_monotone N hM.le hij
    have hfactor := dyadicLogFactor_le_of_log_positive (K + 1) hlevel
      (fun m hm ↦ zero_lt_one.trans_le ((hcut _ (hlevels i)).2.2.1 m hm))
    unfold dyadicReciprocalLogWeight
    exact one_div_le_one_div_of_le
      (Real.sqrt_pos.2 (zero_lt_one.trans_le (one_le_dyadicLogFactor _ _)))
      (Real.sqrt_le_sqrt hfactor)
  · intro hsum
    have ha : 0 < (M : ℝ) * Real.log 2 :=
      mul_pos (by exact_mod_cast hM) (Real.log_pos (by norm_num))
    apply not_summable_reciprocalLogWeight_affine K ha ((N : ℝ) * Real.log 2)
    simpa only [heq, dyadicLogLevel_argument] using hsum

end FluidSingularSets
