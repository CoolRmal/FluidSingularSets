module

public import FluidSingularSets.ParabolicRefinement

/-!
# Unique representation of actual shifted spatial cubes

The volume determines the level, and the partition determines the corner. This
lets a coefficient indexed by cubes use its actual level and containing time cell.
-/

@[expose] public section

open MeasureTheory Set CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

noncomputable section

namespace FluidSingularSets

/-- The spatial cube uniquely determines its grid index. -/
theorem shiftedDyadicCube_index_injective (g : ParabolicGridShift) :
    Function.Injective (fun Q : DyadicIndex ↦ shiftedDyadicCube g Q.scale Q.corner) := by
  intro Q R hQR
  change shiftedDyadicCube g Q.scale Q.corner = shiftedDyadicCube g R.scale R.corner at hQR
  have hv := congrArg (fun A : Set Vec3 ↦ volume A) hQR
  rw [volume_shiftedDyadicCube, volume_shiftedDyadicCube,
    ← ENNReal.ofReal_pow (dyadicScale_pos Q.scale).le,
    ← ENNReal.ofReal_pow (dyadicScale_pos R.scale).le] at hv
  have hp : dyadicScale Q.scale ^ (3 : ℕ) = dyadicScale R.scale ^ (3 : ℕ) := by
    have h := congrArg ENNReal.toReal hv
    simpa only [ENNReal.toReal_ofReal (pow_nonneg (dyadicScale_pos _).le _)] using h
  have hside : dyadicScale Q.scale = dyadicScale R.scale :=
    (pow_left_inj₀ (dyadicScale_pos _).le (dyadicScale_pos _).le (by norm_num)).1 hp
  have hn : Q.scale = R.scale := by
    have h := zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1) hside
    omega
  obtain ⟨x, hx⟩ := shiftedDyadicCube_nonempty g Q.scale Q.corner
  have hxR : x ∈ shiftedDyadicCube g R.scale R.corner := hQR ▸ hx
  have hc : Q.corner = R.corner := shiftedDyadicCorner_unique g R.scale (hn ▸ hx) hxR
  cases Q
  cases R
  cases hn
  cases hc
  rfl

/-- Cube containment forces the containing cube to be at a coarser or equal level. -/
theorem shiftedDyadicCube_scale_le_of_subset (g : ParabolicGridShift)
    (Q R : DyadicIndex)
    (hsub : shiftedDyadicCube g Q.scale Q.corner ⊆ shiftedDyadicCube g R.scale R.corner) :
    R.scale ≤ Q.scale := by
  have hv := measure_mono (μ := (volume : Measure Vec3)) hsub
  rw [volume_shiftedDyadicCube, volume_shiftedDyadicCube,
    ← ENNReal.ofReal_pow (dyadicScale_pos Q.scale).le,
    ← ENNReal.ofReal_pow (dyadicScale_pos R.scale).le] at hv
  have hp : dyadicScale Q.scale ^ (3 : ℕ) ≤ dyadicScale R.scale ^ (3 : ℕ) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
    simpa only [ENNReal.toReal_ofReal (pow_nonneg (dyadicScale_pos _).le _)] using h
  have hside : dyadicScale Q.scale ≤ dyadicScale R.scale :=
    le_of_pow_le_pow_left₀ (by norm_num) (dyadicScale_pos _).le hp
  have h := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 hside
  omega

/-- All actual cubes in one fixed coherent shifted grid. -/
def shiftedSpatialGrid (g : ParabolicGridShift) : Set (Set Vec3) :=
  {A | ∃ Q : DyadicIndex, A = shiftedDyadicCube g Q.scale Q.corner}

/-- The unique index of an actual cube; a harmless default is used outside the grid. -/
def shiftedSpatialRepresentation (g : ParabolicGridShift) (A : Set Vec3) : DyadicIndex := by
  classical
  exact if hA : A ∈ shiftedSpatialGrid g then hA.choose else ⟨0, 0⟩

/-- Reconstructing an actual cube from its chosen index recovers the original cube. -/
theorem shiftedSpatialRepresentation_cube {g : ParabolicGridShift} {A : Set Vec3}
    (hA : A ∈ shiftedSpatialGrid g) :
    shiftedDyadicCube g (shiftedSpatialRepresentation g A).scale
      (shiftedSpatialRepresentation g A).corner = A := by
  simp only [shiftedSpatialRepresentation, dite_eq_left hA]
  exact hA.choose_spec.symm

/-- The chosen representation agrees with every actual cube's defining index. -/
theorem shiftedSpatialRepresentation_eq (g : ParabolicGridShift) (Q : DyadicIndex) :
    shiftedSpatialRepresentation g (shiftedDyadicCube g Q.scale Q.corner) = Q := by
  apply shiftedDyadicCube_index_injective g
  exact shiftedSpatialRepresentation_cube ⟨Q, rfl⟩

end FluidSingularSets
