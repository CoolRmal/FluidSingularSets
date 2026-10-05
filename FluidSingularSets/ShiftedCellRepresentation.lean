module

public import FluidSingularSets.ParabolicFrostmanGeometry

/-!
# Unique representation of actual shifted parabolic cells

The volume fixes the level, and the partition fixes the spatial and temporal
corners. Thus a cell-indexed dissipation coefficient also defines a unique
coefficient on the measurable sets used by the mass-ratio stopping argument.
-/

@[expose] public section

open MeasureTheory Set CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

noncomputable section

namespace FluidSingularSets

/-- Distinct actual parabolic cell indices represent distinct sets. -/
theorem shiftedParabolicDyadicCell_injective (g : ParabolicGridShift) :
    Function.Injective (shiftedParabolicDyadicCell g) := by
  intro Q R hcell
  have hvol := congrArg (fun A : Set ParabolicPoint ↦ (volume A).toReal) hcell
  rw [volume_shiftedParabolicDyadicCell, volume_shiftedParabolicDyadicCell,
    ENNReal.toReal_ofReal (pow_nonneg (dyadicScale_pos Q.scale).le _),
    ENNReal.toReal_ofReal (pow_nonneg (dyadicScale_pos R.scale).le _)] at hvol
  have hs : dyadicScale Q.scale = dyadicScale R.scale :=
    (pow_left_inj₀ (dyadicScale_pos Q.scale).le (dyadicScale_pos R.scale).le
      (by norm_num : (5 : ℕ) ≠ 0)).1 hvol
  have hn : Q.scale = R.scale := by
    have hneg := zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1) hs
    exact neg_injective hneg
  obtain ⟨z, hz⟩ := shiftedParabolicDyadicCell_nonempty g Q
  exact shiftedParabolicDyadicIndex_unique_at_scale g hn hz (hcell ▸ hz)

/-- Cube containment forces the containing cell to have a coarser or equal level. -/
theorem shiftedParabolicDyadicCell_scale_le_of_subset (g : ParabolicGridShift)
    (Q R : ParabolicDyadicIndex)
    (hsub : shiftedParabolicDyadicCell g Q ⊆ shiftedParabolicDyadicCell g R) :
    R.scale ≤ Q.scale := by
  have hv := measure_mono (μ := (volume : Measure ParabolicPoint)) hsub
  rw [volume_shiftedParabolicDyadicCell, volume_shiftedParabolicDyadicCell] at hv
  have hp : dyadicScale Q.scale ^ (5 : ℕ) ≤ dyadicScale R.scale ^ (5 : ℕ) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
    simpa only [ENNReal.toReal_ofReal (pow_nonneg (dyadicScale_pos _).le _)] using h
  have hs : dyadicScale Q.scale ≤ dyadicScale R.scale :=
    le_of_pow_le_pow_left₀ (by norm_num) (dyadicScale_pos _).le hp
  have h := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 hs
  omega

/-- The measurable sets represented by one actual shifted parabolic grid. -/
def shiftedParabolicGrid (g : ParabolicGridShift) : Set (Set ParabolicPoint) :=
  Set.range (shiftedParabolicDyadicCell g)

/-- The unique index of an actual cell, with a harmless default outside the grid. -/
def shiftedCellRepresentation (g : ParabolicGridShift) (A : Set ParabolicPoint) :
    ParabolicDyadicIndex := by
  classical
  exact if hA : A ∈ shiftedParabolicGrid g then hA.choose else ⟨0, 0, 0⟩

/-- The chosen index reconstructs every actual cell. -/
theorem shiftedCellRepresentation_cell {g : ParabolicGridShift} {A : Set ParabolicPoint}
    (hA : A ∈ shiftedParabolicGrid g) :
    shiftedParabolicDyadicCell g (shiftedCellRepresentation g A) = A := by
  simp only [shiftedCellRepresentation, dite_eq_left hA]
  exact hA.choose_spec

/-- The chosen representation agrees with the original defining index. -/
theorem shiftedCellRepresentation_eq (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) :
    shiftedCellRepresentation g (shiftedParabolicDyadicCell g Q) = Q := by
  apply shiftedParabolicDyadicCell_injective g
  exact shiftedCellRepresentation_cell ⟨Q, rfl⟩

end FluidSingularSets
