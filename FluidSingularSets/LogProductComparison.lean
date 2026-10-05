module

public import FluidSingularSets.IteratedGauge

/-!
# Comparing the successive product with repeated last logarithms

The successive product is the stronger gauge near zero. In particular it dominates
the literal expression obtained by repeating the deepest logarithm in every factor.
-/

@[expose] public section

open Finset Filter
open scoped Topology

namespace FluidSingularSets

/-- Later iterates are smaller while all intervening logarithms are nonnegative. -/
theorem logIterate_succ_le_of_depth_le {x : ℝ} {i j : ℕ} (hij : i ≤ j)
    (hlog : ∀ n ≤ j, 0 ≤ logIterate (n + 1) x) :
    logIterate (j + 1) x ≤ logIterate (i + 1) x := by
  induction j with
  | zero =>
    have hi : i = 0 := Nat.eq_zero_of_le_zero hij
    subst i
    exact le_rfl
  | succ j ih =>
    by_cases hi : i ≤ j
    · have hstep : logIterate (j + 1 + 1) x ≤ logIterate (j + 1) x :=
        Real.log_le_self (hlog j (Nat.le_succ _))
      exact hstep.trans (ih hi (fun n hn ↦ hlog n (hn.trans (Nat.le_succ _))))
    · have heq : i = j + 1 := by omega
      subst i
      exact le_rfl

/-- Repeating the deepest logarithm `k` times is eventually dominated by the successive product.
-/
theorem eventually_repeatedLastLog_le_product (k : ℕ) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      r * (logIterate k (1 / r)) ^ (2 * k) ≤
        r * ∏ i ∈ range k, (logIterate (i + 1) (1 / r)) ^ 2 := by
  cases k with
  | zero => simp
  | succ k =>
    filter_upwards [self_mem_nhdsWithin, eventually_small_logIterates (k + 1)]
      with r hr hlog
    have hnonneg : ∀ n ≤ k, 0 ≤ logIterate (n + 1) (1 / r) := by
      intro n hn
      exact zero_le_one.trans (hlog n (mem_range.2 (by omega)))
    have hprod :
        (∏ i ∈ range (k + 1), (logIterate (k + 1) (1 / r)) ^ 2) ≤
          ∏ i ∈ range (k + 1), (logIterate (i + 1) (1 / r)) ^ 2 := by
      apply prod_le_prod₀ (fun _ _ ↦ sq_nonneg _)
      intro i hi
      have hile : i ≤ k := Nat.le_of_lt_succ (mem_range.1 hi)
      have hle := logIterate_succ_le_of_depth_le hile hnonneg
      nlinarith [hnonneg i hile, hnonneg k le_rfl]
    have hpowers : (logIterate (k + 1) (1 / r)) ^ (2 * (k + 1)) ≤
        ∏ i ∈ range (k + 1), (logIterate (i + 1) (1 / r)) ^ 2 := by
      simpa only [prod_const, card_range, ← pow_mul] using hprod
    exact mul_le_mul_of_nonneg_left hpowers hr.le

end FluidSingularSets
