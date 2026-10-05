-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.IteratedGauge
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Divergence of every finite iterated logarithmic harmonic series

With `k` additional logarithms, the reciprocal weight is
`1 / (x * log x * ... * logIterate k x)`. Every such weight is positive and decreasing
on a sufficiently late tail, but its natural-number series diverges. The proof uses
logarithmic change of variables for nonintegrability and the integral test for divergence.
-/

@[expose] public section

open MeasureTheory Set Filter Finset
open scoped ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- A reciprocal harmonic weight with `k` additional iterated logarithmic factors. -/
def reciprocalLogWeight : ℕ → ℝ → ℝ
  | 0, x => x⁻¹
  | k + 1, x => x⁻¹ * reciprocalLogWeight k (Real.log x)

@[simp] theorem reciprocalLogWeight_zero (x : ℝ) : reciprocalLogWeight 0 x = x⁻¹ := rfl

@[simp] theorem reciprocalLogWeight_succ (k : ℕ) (x : ℝ) :
    reciprocalLogWeight (k + 1) x = x⁻¹ * reciprocalLogWeight k (Real.log x) := rfl

/-- Applying the logarithm before the iteration increases the iteration count by one. -/
theorem logIterate_apply_log (k : ℕ) (x : ℝ) :
    logIterate k (Real.log x) = logIterate (k + 1) x := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [logIterate_succ, ih]

/-- The recursive weight is exactly the reciprocal of the finite logarithmic product. -/
theorem reciprocalLogWeight_eq_inv_prod (k : ℕ) (x : ℝ) :
    reciprocalLogWeight k x = (∏ i ∈ range (k + 1), logIterate i x)⁻¹ := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [reciprocalLogWeight_succ, ih]
    simp only [logIterate_apply_log]
    rw [prod_range_succ' (fun i ↦ logIterate i x) (k + 1), logIterate_zero, mul_inv_rev]

/-- No finite iterated logarithmic reciprocal weight is integrable on an infinite ray. -/
theorem not_integrableOn_Ioi_reciprocalLogWeight (k : ℕ) (a : ℝ) :
    ¬ IntegrableOn (reciprocalLogWeight k) (Ioi a) := by
  induction k generalizing a with
  | zero =>
    change ¬ IntegrableOn (fun x : ℝ ↦ x⁻¹) (Ioi a)
    exact not_integrableOn_Ioi_inv
  | succ k ih =>
    intro h
    let b : ℝ := max a 1
    have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have htail : IntegrableOn (reciprocalLogWeight (k + 1)) (Ioi b) :=
      h.mono_set (Set.Ioi_subset_Ioi (le_max_left _ _))
    apply ih (Real.log b)
    apply (integrableOn_comp_log_Ioi (reciprocalLogWeight k) hb).1
    change IntegrableOn (fun x ↦ x⁻¹ * reciprocalLogWeight k (Real.log x)) (Ioi b) at htail
    simpa only [smul_eq_mul] using htail

/-- Every fixed reciprocal logarithmic weight is positive and antitone after a real cutoff. -/
theorem reciprocalLogWeight_positive_antitone_tail (k : ℕ) :
    ∃ a : ℝ, 0 < a ∧ (∀ x ∈ Ici a, 0 < reciprocalLogWeight k x) ∧
      AntitoneOn (reciprocalLogWeight k) (Ici a) := by
  induction k with
  | zero =>
    refine ⟨1, zero_lt_one, ?_, ?_⟩
    · intro x hx
      exact inv_pos.mpr (zero_lt_one.trans_le hx)
    · intro x hx y hy hxy
      exact inv_anti₀ (zero_lt_one.trans_le hx) hxy
  | succ k ih =>
    obtain ⟨a, ha, hpositive, hantitone⟩ := ih
    refine ⟨Real.exp a, Real.exp_pos a, ?_, ?_⟩
    · intro x hx
      have hxpos := (Real.exp_pos a).trans_le hx
      have hlog : a ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).2 hx
      exact mul_pos (inv_pos.mpr hxpos) (hpositive _ hlog)
    · intro x hx y hy hxy
      have hxpos := (Real.exp_pos a).trans_le hx
      have hypos := (Real.exp_pos a).trans_le hy
      have hlogx : a ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).2 hx
      have hlogy : a ≤ Real.log y := (Real.le_log_iff_exp_le hypos).2 hy
      exact mul_le_mul (inv_anti₀ hxpos hxy)
        (hantitone hlogx hlogy (Real.log_le_log hxpos hxy))
        (hpositive _ hlogy).le (inv_pos.mpr hxpos).le

/-- The series with any fixed finite number of logarithmic denominator factors diverges. -/
theorem not_summable_reciprocalLogWeight (k : ℕ) :
    ¬ Summable (fun n : ℕ ↦ reciprocalLogWeight k n) := by
  intro hsum
  obtain ⟨a, ha, hpositive, hantitone⟩ := reciprocalLogWeight_positive_antitone_tail k
  obtain ⟨N, hN⟩ := exists_nat_gt a
  have hantiN : AntitoneOn (reciprocalLogWeight k) (Ici (N : ℝ)) :=
    hantitone.mono (Ici_subset_Ici.mpr hN.le)
  apply not_integrableOn_Ioi_reciprocalLogWeight k N
  apply hantiN.integrableOn_Ioi_of_summable_comp_add ((summable_nat_add_iff N).2 hsum)
  intro x hx
  exact (hpositive x (hN.le.trans hx.le)).le

/-- Removing any finite prefix preserves divergence. -/
theorem not_summable_reciprocalLogWeight_shift (k N : ℕ) :
    ¬ Summable (fun n : ℕ ↦ reciprocalLogWeight k (n + N : ℕ)) := by
  intro hsum
  exact not_summable_reciprocalLogWeight k ((summable_nat_add_iff N).1 hsum)

/-- Each logarithmic denominator depth has a positive, decreasing, nonsummable natural tail. -/
theorem exists_positive_antitone_nonsummable_reciprocalLogWeight_tail (k : ℕ) :
    ∃ N : ℕ, (∀ n : ℕ, 0 < reciprocalLogWeight k (n + N : ℕ)) ∧
      Antitone (fun n : ℕ ↦ reciprocalLogWeight k (n + N : ℕ)) ∧
      ¬ Summable (fun n : ℕ ↦ reciprocalLogWeight k (n + N : ℕ)) := by
  obtain ⟨a, ha, hpositive, hantitone⟩ := reciprocalLogWeight_positive_antitone_tail k
  obtain ⟨N, hN⟩ := exists_nat_gt a
  refine ⟨N, ?_, ?_, not_summable_reciprocalLogWeight_shift k N⟩
  · intro n
    apply hpositive
    exact hN.le.trans (by exact_mod_cast Nat.le_add_left N n)
  · intro m n hmn
    apply hantitone
    · exact hN.le.trans (by exact_mod_cast Nat.le_add_left N m)
    · exact hN.le.trans (by exact_mod_cast Nat.le_add_left N n)
    · exact_mod_cast Nat.add_le_add_right hmn N

end FluidSingularSets
