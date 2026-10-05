module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/-!
# Persistent activity across scales

The analytic scale recurrence from the logarithmic Hausdorff manuscript implies divergence of
the harmonic-weighted dissipation cost. These lemmas isolate its scalar sequence argument.
-/

@[expose] public section

open Finset Filter

namespace FluidSingularSets

/-- Decreasing nonnegative weights bound the weighted increments of a nonnegative sequence
from below by its initial contribution. -/
theorem weighted_increments_lower_bound (L w : ℕ → ℝ)
    (hL : ∀ n, 0 ≤ L n) (hw : ∀ n, 0 ≤ w n) (hanti : Antitone w) (N : ℕ) :
    -(w 0 * L 0) ≤ ∑ n ∈ range N, w n * (L (n + 1) - L n) := by
  have hstrong : ∀ N, w N * L N - w 0 * L 0 ≤
      ∑ n ∈ range N, w n * (L (n + 1) - L n) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ]
      have hweight : w (N + 1) * L (N + 1) ≤ w N * L (N + 1) :=
        mul_le_mul_of_nonneg_right (hanti (Nat.le_succ N)) (hL (N + 1))
      linarith
  have hnonneg : 0 ≤ w N * L N := mul_nonneg (hw N) (hL N)
  linarith [hstrong N]

/-- A contraction recurrence produces a negative logarithmic drift unless its dissipation
cost compensates. The constant `3/4` suffices for the divergence argument. -/
theorem log_increment_le_of_recurrence {G H C e : ℝ}
    (hG : 0 < G) (hH : 0 < H) (hrec : H ≤ G / 4 + C * Real.sqrt G * e) :
    Real.log H - Real.log G ≤ -(3 / 4 : ℝ) + C * e / Real.sqrt G := by
  have hsqrt : 0 < Real.sqrt G := Real.sqrt_pos.2 hG
  have hsq : (Real.sqrt G) ^ 2 = G := Real.sq_sqrt hG.le
  have hquot : H / G - 1 ≤ -(3 / 4 : ℝ) + C * e / Real.sqrt G := by
    have heq : C * Real.sqrt G * e / G = C * e / Real.sqrt G := by
      apply (div_eq_div_iff hG.ne' hsqrt.ne').2
      calc
        C * Real.sqrt G * e * Real.sqrt G = C * e * (Real.sqrt G) ^ 2 := by ring
        _ = C * e * G := by rw [hsq]
    calc
      _ ≤ (G / 4 + C * Real.sqrt G * e) / G - 1 :=
        sub_le_sub_right (div_le_div_of_nonneg_right hrec hG.le) 1
      _ = _ := by
        rw [add_div, heq]
        have hquarter : G / 4 / G = (1 / 4 : ℝ) := by field_simp
        rw [hquarter]
        ring
  calc
    Real.log H - Real.log G = Real.log (H / G) :=
      (Real.log_div hH.ne' hG.ne').symm
    _ ≤ H / G - 1 := Real.log_le_sub_one_of_pos (div_pos hH hG)
    _ ≤ -(3 / 4 : ℝ) + C * e / Real.sqrt G := hquot

/-- A nonnegative activity sequence cannot sustain a negative constant drift if its
harmonic-weighted compensating costs are summable. -/
theorem not_summable_weighted_cost_of_drift (L b : ℕ → ℝ) {a : ℝ}
    (ha : 0 < a) (hL : ∀ n, 0 ≤ L n) (hb : ∀ n, 0 ≤ b n)
    (hdrift : ∀ n, L (n + 1) - L n ≤ -a + b n) :
    ¬ Summable (fun n ↦ b n / ((n : ℝ) + 1)) := by
  intro hsum
  let w : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hw : ∀ n, 0 ≤ w n := fun n ↦ by dsimp [w]; positivity
  have hanti : Antitone w := by
    intro m n hmn
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hpartial : ∀ N, a * ∑ n ∈ range N, w n ≤
      (∑' n, b n / ((n : ℝ) + 1)) + L 0 := by
    intro N
    have hlower := weighted_increments_lower_bound L w hL hw hanti N
    have hupper : (∑ n ∈ range N, w n * (L (n + 1) - L n)) ≤
        -a * (∑ n ∈ range N, w n) + ∑ n ∈ range N, b n / ((n : ℝ) + 1) := by
      calc
        _ ≤ ∑ n ∈ range N, w n * (-a + b n) :=
          sum_le_sum fun n _ ↦ mul_le_mul_of_nonneg_left (hdrift n) (hw n)
        _ = _ := by
          simp_rw [mul_add]
          rw [sum_add_distrib, ← sum_mul]
          congr 1
          · ring
          · apply sum_congr rfl
            intro n _
            dsimp [w]
            ring
    have hbound := hsum.sum_le_tsum (range N) (fun n _ ↦ div_nonneg (hb n) (by positivity))
    have hzero : w 0 = 1 := by simp [w]
    rw [hzero, one_mul] at hlower
    linarith
  have hharmonic : Summable w := summable_of_sum_range_le
      (c := ((∑' n, b n / ((n : ℝ) + 1)) + L 0) / a) hw (fun N ↦ by
    apply (le_div_iff₀ ha).2
    nlinarith [hpartial N])
  have hharmonic' : Summable (fun n : ℕ ↦ 1 / (n : ℝ)) := by
    apply (summable_nat_add_iff 1).1
    simpa [w, Nat.cast_add, Nat.cast_one] using hharmonic
  exact Real.not_summable_one_div_natCast hharmonic'

/-- Persistent positive activity under the scale recurrence forces nonsummability of its
harmonic-weighted dissipation cost. -/
theorem persistent_activity_not_summable (G e : ℕ → ℝ) {ε C : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C) (hG : ∀ n, ε ≤ G n) (he : ∀ n, 0 ≤ e n)
    (hrec : ∀ n, G (n + 1) ≤ G n / 4 + C * Real.sqrt (G n) * e n) :
    ¬ Summable (fun n ↦ e n / (((n : ℝ) + 1) * Real.sqrt (G n))) := by
  have hpos : ∀ n, 0 < G n := fun n ↦ hε.trans_le (hG n)
  let L : ℕ → ℝ := fun n ↦ Real.log (G n / ε)
  let b : ℕ → ℝ := fun n ↦ C * e n / Real.sqrt (G n)
  have hL : ∀ n, 0 ≤ L n := by
    intro n
    apply Real.log_nonneg
    exact (one_le_div hε).2 (hG n)
  have hb : ∀ n, 0 ≤ b n := fun n ↦
    div_nonneg (mul_nonneg hC (he n)) (Real.sqrt_nonneg (G n))
  have hdrift : ∀ n, L (n + 1) - L n ≤ -(3 / 4 : ℝ) + b n := by
    intro n
    dsimp [L, b]
    rw [Real.log_div (hpos (n + 1)).ne' hε.ne', Real.log_div (hpos n).ne' hε.ne']
    linarith [log_increment_le_of_recurrence (hpos n) (hpos (n + 1)) (hrec n)]
  have hnonsum := not_summable_weighted_cost_of_drift L b
    (by norm_num : (0 : ℝ) < 3 / 4) hL hb hdrift
  intro hsum
  apply hnonsum
  convert hsum.mul_left C using 1
  ext n
  dsimp [b]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The finite partial sums of the persistent-activity cost tend to positive infinity. -/
theorem persistent_activity_tendsto_sum_atTop (G e : ℕ → ℝ) {ε C : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C) (hG : ∀ n, ε ≤ G n) (he : ∀ n, 0 ≤ e n)
    (hrec : ∀ n, G (n + 1) ≤ G n / 4 + C * Real.sqrt (G n) * e n) :
    Tendsto (fun N ↦ ∑ n ∈ range N, e n / (((n : ℝ) + 1) * Real.sqrt (G n)))
      atTop atTop := by
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n ↦
    div_nonneg (he n) (mul_nonneg (by positivity) (Real.sqrt_nonneg (G n))))).1
  exact persistent_activity_not_summable G e hε hC hG he hrec

/-- The manuscript's series, starting at scale index two, is not summable. -/
theorem persistent_activity_tail_not_summable (G e : ℕ → ℝ) {ε C : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C) (hG : ∀ n, ε ≤ G n) (he : ∀ n, 0 ≤ e n)
    (hrec : ∀ n, G (n + 1) ≤ G n / 4 + C * Real.sqrt (G n) * e n) :
    ¬ Summable (fun n ↦ e (n + 2) / (((n : ℝ) + 2) * Real.sqrt (G (n + 2)))) := by
  have hnonsum := persistent_activity_not_summable (fun n ↦ G (n + 2))
    (fun n ↦ e (n + 2)) hε hC (fun n ↦ hG (n + 2)) (fun n ↦ he (n + 2))
    (fun n ↦ by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec (n + 2))
  intro hsum
  apply hnonsum
  apply Summable.of_nonneg_of_le (fun n ↦ div_nonneg (he (n + 2))
    (mul_nonneg (by positivity) (Real.sqrt_nonneg (G (n + 2))))) _ (hsum.mul_left 2)
  intro n
  have hs : 0 < Real.sqrt (G (n + 2)) := Real.sqrt_pos.2 (hε.trans_le (hG (n + 2)))
  have hd₁ : 0 < ((n : ℝ) + 1) * Real.sqrt (G (n + 2)) := by positivity
  have hd₂ : 0 < ((n : ℝ) + 2) * Real.sqrt (G (n + 2)) := by positivity
  have hden : ((n : ℝ) + 2) * Real.sqrt (G (n + 2)) ≤
      2 * (((n : ℝ) + 1) * Real.sqrt (G (n + 2))) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  change e (n + 2) / (((n : ℝ) + 1) * Real.sqrt (G (n + 2))) ≤
    2 * (e (n + 2) / (((n : ℝ) + 2) * Real.sqrt (G (n + 2))))
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hd₁ hd₂).2
  nlinarith [mul_le_mul_of_nonneg_left hden (he (n + 2))]

/-- The manuscript's harmonic-weighted series from index two tends to positive infinity. -/
theorem persistent_activity_tail_tendsto_sum_atTop (G e : ℕ → ℝ) {ε C : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C) (hG : ∀ n, ε ≤ G n) (he : ∀ n, 0 ≤ e n)
    (hrec : ∀ n, G (n + 1) ≤ G n / 4 + C * Real.sqrt (G n) * e n) :
    Tendsto (fun N ↦ ∑ n ∈ range N,
      e (n + 2) / (((n : ℝ) + 2) * Real.sqrt (G (n + 2)))) atTop atTop := by
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n ↦
    div_nonneg (he (n + 2)) (mul_nonneg (by positivity)
      (Real.sqrt_nonneg (G (n + 2)))))).1
  exact persistent_activity_tail_not_summable G e hε hC hG he hrec

end FluidSingularSets
