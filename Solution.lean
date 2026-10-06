module

public import FluidSingularSets.CKNBridge
public import FluidSingularSets.Geometry
public import FluidSingularSets.IteratedGauge
public import FluidSingularSets.CKNBaseline
public import FluidSingularSets.SuitableGaugeNullity
public import FluidSingularSets.CompactBoxCriterion
public import FluidSingularSets.UniformEndpointVelocityCriterion

/-!
# Proof assembly for the singular-set refinements

The CKN dependency provides the same `CKNChallenge` solution class as the standalone Challenge
and proves the ordinary CKN theorem for it. The finite logarithmic gauge family follows
from the actual suitable recurrence and Frostman trace. Genuine projected endpoint
regularity supplies the uniform criterion and compact charge bound for box counting.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace FluidSingularSets

/-- Every finite family of successive logarithmic factors has zero parabolic Hausdorff
measure on the interior singular set of an unforced suitable weak solution. -/
theorem singularSet_iteratedLogHausdorffMeasure_zero
    (k : ℕ) (Ω : Set Space) (I : Set ℝ)
    (data : CKNChallenge.LocalWeakNSESolution Ω I 3) (hforce : data.f = 0) :
    iteratedLogHausdorffMeasure k (CKNChallenge.singularSet Ω I data.u) = 0 := by
  exact suitable_singularSet_iteratedLogHausdorffMeasure_zero k data hforce

/-- The interior singular set of every unforced local suitable weak solution has zero
parabolic Hausdorff measure for the gauge `r(log(1/r))²`.
The force exponent is fixed at three because the force is identically zero. -/
theorem singularSet_logSquaredHausdorffMeasure_zero
    (Ω : Set Space) (I : Set ℝ) (data : CKNChallenge.LocalWeakNSESolution Ω I 3)
    (hforce : data.f = 0) :
    logSquaredHausdorffMeasure (CKNChallenge.singularSet Ω I data.u) = 0 := by
  rw [← iteratedLogHausdorffMeasure_one_eq]
  exact singularSet_iteratedLogHausdorffMeasure_zero 1 Ω I data hforce

/-- On every compact interior patch, the singular set of an unforced local suitable weak
solution has upper parabolic box dimension at most `25/23`. -/
theorem singularSet_upperBoxDimension_le
    (Ω : Set Space) (I : Set ℝ) (data : CKNChallenge.LocalWeakNSESolution Ω I 3)
    (hforce : data.f = 0) (K : Set SpaceTime)
    (hK : IsCompact K) (hinterior : K ⊆ Ω ×ˢ I) :
    upperParabolicBoxDimension (CKNChallenge.singularSet Ω I data.u ∩ K) ≤
      ENNReal.ofReal (25 / 23 : ℝ) := by
  obtain ⟨κ, hκ, hcriterion⟩ :=
    exists_uniform_velocity_only_interior_criterion 3 (by norm_num)
  exact suitable_compact_singularSet_upperBoxDimension_le_of_velocity_criterion
    hκ hcriterion data hforce hK hinterior

end FluidSingularSets
