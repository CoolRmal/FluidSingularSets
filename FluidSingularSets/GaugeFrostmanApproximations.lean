-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import FluidSingularSets.GaugeFrostman
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Coarse-node bounds for the finite gauge measures

A finite leaf measure assigns to a set at most the sum of the capacities of
the coarse nodes that contain its positive-mass atoms. The estimate groups the
actual terminal masses by prefixes and uses their proved conservation law.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- Group terminal atoms by their coarse prefix. Only coarse nodes meeting the
set need be counted, and each contributes at most its prescribed capacity. -/
theorem gaugeTreeAtomicMeasure_apply_le_nodes {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] {b : ℕ} (cap : List (Fin b) → ℝ≥0)
    (k t : ℕ) (v : List (Fin b)) (m : ℝ≥0)
    (hm : m ≤ gaugeTreeCapacity cap v (k + t))
    (points : (Fin (k + t) → Fin b) → X) (A : Set X) (P : Finset (Fin k → Fin b))
    (hcover : ∀ (p : Fin k → Fin b) (q : Fin t → Fin b),
      gaugeTreeNodeMass cap v (k + t) m (List.ofFn p ++ List.ofFn q) ≠ 0 →
        points (Fin.append p q) ∈ A → p ∈ P) :
    gaugeTreeAtomicMeasure cap (k + t) v m points A ≤
      ∑ p ∈ P, (cap (v ++ List.ofFn p) : ℝ≥0∞) := by
  classical
  let row (p : Fin k → Fin b) : ℝ≥0∞ := ∑ q : Fin t → Fin b,
    (gaugeTreeNodeMass cap v (k + t) m (List.ofFn p ++ List.ofFn q) : ℝ≥0∞) *
      Measure.dirac (points (Fin.append p q)) A
  have hrowzero : ∀ p, p ∉ P → row p = 0 := by
    intro p hp
    apply Finset.sum_eq_zero
    intro q _
    by_cases hmass : gaugeTreeNodeMass cap v (k + t) m (List.ofFn p ++ List.ofFn q) = 0
    · simp only [hmass, ENNReal.coe_zero, zero_mul]
    · have hpoint : points (Fin.append p q) ∉ A := fun ha => hp (hcover p q hmass ha)
      rw [Measure.dirac_apply, indicator_of_notMem hpoint, mul_zero]
  have hrowbound (p : Fin k → Fin b) : row p ≤ (cap (v ++ List.ofFn p) : ℝ≥0∞) := by
    calc
      row p ≤ ∑ q : Fin t → Fin b,
          (gaugeTreeNodeMass cap v (k + t) m (List.ofFn p ++ List.ofFn q) : ℝ≥0∞) := by
        apply Finset.sum_le_sum
        intro q _
        have hdirac : Measure.dirac (points (Fin.append p q)) A ≤ 1 := by
          simpa only [Measure.dirac_apply_of_mem (mem_univ _)] using
            (measure_mono (subset_univ A) : Measure.dirac (points (Fin.append p q)) A ≤
              Measure.dirac (points (Fin.append p q)) univ)
        exact (mul_le_mul_of_nonneg_left hdirac zero_le).trans_eq (mul_one _)
      _ ≤ (cap (v ++ List.ofFn p) : ℝ≥0∞) := by
        rw [← ENNReal.ofNNReal_finsetSum]
        have hmass := sum_gaugeTreeNodeMass_descendants_le_node cap (List.ofFn p) t v m
          (by simpa only [List.length_ofFn] using hm)
        simp only [List.length_ofFn] at hmass
        exact_mod_cast hmass
  have hatomic : gaugeTreeAtomicMeasure cap (k + t) v m points A = ∑ p, row p := by
    rw [gaugeTreeAtomicMeasure, Measure.finsetSum_apply,
      ← (Fin.appendEquiv (α := Fin b) k t).sum_comp]
    simp only [Fintype.sum_prod_type]
    change (∑ p : Fin k → Fin b, ∑ q : Fin t → Fin b,
      (gaugeTreeNodeMass cap v (k + t) m (List.ofFn (Fin.append p q)) : ℝ≥0∞) •
        Measure.dirac (points (Fin.append p q)) A) = ∑ p, row p
    simp only [List.ofFn_fin_append, smul_eq_mul, row]
  rw [hatomic]
  calc
    (∑ p, row p) = ∑ p ∈ P, row p :=
      (Finset.sum_subset (Finset.subset_univ P) fun p _ hp => hrowzero p hp).symm
    _ ≤ ∑ p ∈ P, (cap (v ++ List.ofFn p) : ℝ≥0∞) :=
      Finset.sum_le_sum fun p _ => hrowbound p

end FluidSingularSets
