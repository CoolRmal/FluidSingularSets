-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.SymmetricCellMixedComparison
public import FluidSingularSets.DyadicLogWeights

/-!
# Exact dyadic cylinder and adjacent-cell sequences

The activity radius is thirty-two times the selected cell side. The dyadic
side bounds therefore determine the cell level exactly. Positive integer
refinement supplies an injective sequence of actual adjacent-grid cells.
-/

@[expose] public section

open MeasureTheory Set CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The radius used for activity is five dyadic levels above the trace cell. -/
def dyadicActivityRadius (N : ℤ) (M j : ℕ) : ℝ :=
  dyadicScale (dyadicLogLevel N (M : ℤ) j - 5)

/-- Subtracting a natural number of levels multiplies the side by its exact power of two. -/
theorem dyadicScale_sub_nat (n : ℤ) (a : ℕ) :
    dyadicScale (n - (a : ℤ)) = (2 : ℝ) ^ a * dyadicScale n := by
  unfold dyadicScale
  have hneg : -(n - (a : ℤ)) = (a : ℤ) + -n := by ring
  rw [hneg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]

/-- Adding the fixed natural refinement multiplies the radius by the dyadic contraction. -/
theorem dyadicScale_add_nat (n : ℤ) (a : ℕ) :
    dyadicScale (n + (a : ℤ)) = (1 / 2 : ℝ) ^ a * dyadicScale n := by
  unfold dyadicScale
  rw [neg_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [zpow_neg, zpow_natCast, div_pow, one_pow]
  ring

/-- Every radius of the activity sequence is positive. -/
theorem dyadicActivityRadius_pos (N : ℤ) (M j : ℕ) : 0 < dyadicActivityRadius N M j :=
  dyadicScale_pos _

/-- The radius corresponds exactly to the level progression initialized five levels earlier. -/
theorem dyadicActivityRadius_eq_shiftedLevel (N : ℤ) (M j : ℕ) :
    dyadicActivityRadius N M j = dyadicScale (dyadicLogLevel (N - 5) (M : ℤ) j) := by
  unfold dyadicActivityRadius dyadicLogLevel
  congr 1
  ring

/-- The cylinder radius is exactly thirty-two times the intended trace-cell side. -/
theorem dyadicActivityRadius_eq_thirtyTwo_side (N : ℤ) (M j : ℕ) :
    dyadicActivityRadius N M j = 32 * dyadicScale (dyadicLogLevel N (M : ℤ) j) := by
  unfold dyadicActivityRadius
  convert dyadicScale_sub_nat (dyadicLogLevel N (M : ℤ) j) 5 using 1; norm_num

/-- The exact recurrence scale agrees with the analytic contraction scale. -/
theorem dyadicActivityRadius_succ (N : ℤ) (M j : ℕ) :
    dyadicActivityRadius N M (j + 1) = (1 / 2 : ℝ) ^ M * dyadicActivityRadius N M j := by
  have hlevel : dyadicLogLevel N (M : ℤ) (j + 1) - 5 =
      (dyadicLogLevel N (M : ℤ) j - 5) + M := by
    unfold dyadicLogLevel
    push_cast
    ring
  unfold dyadicActivityRadius
  rw [hlevel, dyadicScale_add_nat]

/-- Natural refinement makes the activity radii nonincreasing. -/
theorem dyadicActivityRadius_antitone (N : ℤ) (M : ℕ) :
    Antitone (dyadicActivityRadius N M) := by
  intro i j hij
  exact dyadicScale_antitone (sub_le_sub_right
    (dyadicLogLevel_monotone N (Int.natCast_nonneg M) hij) 5)

/-- Every activity radius stays below the initial five-level-enlarged side. -/
theorem dyadicActivityRadius_le_initial (N : ℤ) (M j : ℕ) :
    dyadicActivityRadius N M j ≤ dyadicScale (N - 5) := by
  have h := dyadicActivityRadius_antitone N M (Nat.zero_le j)
  simpa only [dyadicActivityRadius, dyadicLogLevel, Nat.cast_zero, mul_zero, add_zero] using h

/-- Choosing the initial cell level five levels beyond a requested radius cutoff
keeps every activity cylinder below that cutoff radius. -/
theorem dyadicActivityRadius_le_of_initial_level {N n₀ : ℤ}
    (hn : n₀ + 5 ≤ N) (M j : ℕ) :
    dyadicActivityRadius N M j ≤ dyadicScale n₀ := by
  exact (dyadicActivityRadius_le_initial N M j).trans
    (dyadicScale_antitone (by omega : n₀ ≤ N - 5))

/-- The dyadic adjacency side range pins down the integer cell level exactly. -/
theorem dyadicScale_level_eq_of_activity_bounds {n m : ℤ} {r : ℝ}
    (hr : r = 32 * dyadicScale n)
    (hlo : r / 32 ≤ dyadicScale m) (hhi : dyadicScale m < r / 16) : m = n := by
  have hlo' : dyadicScale n ≤ dyadicScale m := by rw [hr] at hlo; linarith only [hlo]
  have hhi' : dyadicScale m < dyadicScale (n - 1) := by
    have hprev : dyadicScale (n - 1) = 2 * dyadicScale n := by
      convert dyadicScale_sub_nat n 1 using 1; norm_num
    rw [hprev]
    rw [hr] at hhi
    linarith only [hhi]
  have hneglo := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 hlo'
  have hneghi := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 hhi'
  omega

/-- Adjacency provides a cell at the prescribed progression level, together
with the actual mixed-cost comparison and the containing-center geometry. -/
theorem exists_dyadicActivity_cell
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint)
    (N : ℤ) (M j : ℕ) :
    ∃ (g : ParabolicGridShift) (Q : ParabolicDyadicIndex),
      Q.scale = dyadicLogLevel N (M : ℤ) j ∧
        dyadicActivityRadius N M j / 32 ≤ dyadicScale Q.scale ∧
        dyadicScale Q.scale < dyadicActivityRadius N M j / 16 ∧
        z ∈ shiftedParabolicDyadicCell g Q ∧
        rawSymmetricL3Cylinder z (dyadicActivityRadius N M j / 512) ⊆
          shiftedParabolicDyadicCell g Q ∧
        ENNReal.ofReal
            (rawSymmetricMixedGradientActivity Du z (dyadicActivityRadius N M j / 512)) ≤
          512 * dyadicMixedGradientActivity g Du Q := by
  obtain ⟨g, Q, hlo, hhi, hz, hsub, hcost⟩ := exists_adjacent_cell_mixedGradient_comparison
    Du z (dyadicActivityRadius_pos N M j)
  refine ⟨g, Q, ?_, hlo, hhi, hz, hsub, hcost⟩
  exact dyadicScale_level_eq_of_activity_bounds
    (dyadicActivityRadius_eq_thirtyTwo_side N M j) hlo hhi

/-- Positive-step activity radii admit an injective chosen sequence of actual
cells, with precisely the logarithmic-weight levels used by the trace argument. -/
theorem exists_injective_dyadicActivity_cells
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint)
    (N : ℤ) {M : ℕ} (hM : 0 < M) :
    ∃ P : ℕ → ParabolicGridShift × ParabolicDyadicIndex,
      (∀ j, (P j).2.scale = dyadicLogLevel N (M : ℤ) j ∧
        dyadicActivityRadius N M j / 32 ≤ dyadicScale (P j).2.scale ∧
        dyadicScale (P j).2.scale < dyadicActivityRadius N M j / 16 ∧
        z ∈ shiftedParabolicDyadicCell (P j).1 (P j).2 ∧
        rawSymmetricL3Cylinder z (dyadicActivityRadius N M j / 512) ⊆
          shiftedParabolicDyadicCell (P j).1 (P j).2 ∧
        ENNReal.ofReal
            (rawSymmetricMixedGradientActivity Du z (dyadicActivityRadius N M j / 512)) ≤
          512 * dyadicMixedGradientActivity (P j).1 Du (P j).2) ∧ Function.Injective P := by
  classical
  have hex (j : ℕ) := exists_dyadicActivity_cell Du z N M j
  choose g Q hlevel hlo hhi hz hsub hcost using hex
  let P : ℕ → ParabolicGridShift × ParabolicDyadicIndex := fun j ↦ (g j, Q j)
  refine ⟨P, fun j ↦ ⟨hlevel j, hlo j, hhi j, hz j, hsub j, hcost j⟩, ?_⟩
  intro i j hij
  have hlevels := congrArg (fun p : ParabolicGridShift × ParabolicDyadicIndex ↦ p.2.scale) hij
  change (Q i).scale = (Q j).scale at hlevels
  rw [hlevel i, hlevel j] at hlevels
  unfold dyadicLogLevel at hlevels
  have hcast : (i : ℤ) = (j : ℤ) :=
    mul_left_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hM)) (add_left_cancel hlevels)
  exact_mod_cast hcast

end FluidSingularSets
