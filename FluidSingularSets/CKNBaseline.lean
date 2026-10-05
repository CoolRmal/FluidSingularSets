-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.CKNBridge
public import FluidSingularSets.IteratedGauge

/-!
# The CKN baseline in the iterated gauge representation

The independent CKN interface writes parabolic Hausdorff measure in ordinary coordinates
by pushing forward the snowflaked product measure. The gauge family instead lifts the set
to those product coordinates. These representations agree on every set, without a
measurability restriction. Consequently the existing CKN theorem establishes the member
with zero logarithmic factors for actual suitable weak solutions.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- Lifting the measured set and pushing forward parabolic measure give the same value. -/
theorem iteratedLogHausdorffMeasure_zero_eq_CKN (E : Set SpaceTime) :
    iteratedLogHausdorffMeasure 0 E = CKNChallenge.parabolicHausdorffMeasure 1 E := by
  rw [iteratedLogHausdorffMeasure_zero_eq]
  unfold CKNChallenge.parabolicHausdorffMeasure
  rw [MeasurableEquiv.map_apply]
  congr 1
  change toParabolic '' E =
    (fun z : ParabolicSpaceTime ↦ (z.1, z.2.ofSnowflaking)) ⁻¹' E
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change w ∈ E
    exact hw
  · intro hz
    refine ⟨(z.1, z.2.ofSnowflaking), hz, ?_⟩
    exact Prod.ext rfl (Metric.Snowflaking.toSnowflaking_ofSnowflaking z.2)

/-- Suitable weak solutions satisfy the zero-factor member of the iterated gauge family. -/
theorem suitableWeakSolution_iteratedLogHausdorffMeasure_zero_factors
    (q : ℝ≥0) (hq : 5 / 2 < q) (Ω : Set Space) (I : Set ℝ)
    (sol : CKNChallenge.LocalWeakNSESolution Ω I q) :
    iteratedLogHausdorffMeasure 0 (CKNChallenge.singularSet Ω I sol.u) = 0 := by
  rw [iteratedLogHausdorffMeasure_zero_eq_CKN]
  exact CKNChallenge.caffarelliKohnNirenberg q hq Ω I sol

end FluidSingularSets
