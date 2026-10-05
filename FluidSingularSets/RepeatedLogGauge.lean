-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.LogProductComparison
public import FluidSingularSets.SuitableGaugeNullity

/-!
# Nullity for the literal repeated deepest logarithm

Repeating the deepest logarithm in every factor gives the gauge
`r * (logIterate k (1/r))^(2*k)`. The proved successive-product gauge
is stronger near zero, so its nullity also proves this literal variant.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The literal deepest logarithm repeated in all `k` squared factors.
The infinite-diameter value is top; finite diameters use the exact real formula. -/
def repeatedLastLogGauge (k : ℕ) (d : ℝ≥0∞) : ℝ≥0∞ :=
  if d = ∞ then ∞ else
    ENNReal.ofReal (d.toReal * (logIterate k (1 / d.toReal)) ^ (2 * k))

/-- The corresponding actual parabolic gauge Hausdorff measure. -/
def repeatedLastLogHausdorffMeasure (k : ℕ) (E : Set SpaceTime) : ℝ≥0∞ :=
  (Measure.mkMetric (repeatedLastLogGauge k) : Measure ParabolicSpaceTime)
    (toParabolic '' E)

/-- The literal repeated deepest-log gauge is dominated by the proved successive product
throughout a neighborhood of diameter zero. -/
theorem eventually_repeatedLastLogGauge_le (k : ℕ) :
    repeatedLastLogGauge k ≤ᶠ[𝓝 (0 : ℝ≥0∞)] iteratedLogGauge k := by
  have hreal : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ENNReal.ofReal (r * (logIterate k (1 / r)) ^ (2 * k)) ≤
        iteratedLogGauge k (ENNReal.ofReal r) := by
    filter_upwards [eventually_repeatedLastLog_le_product k,
      eventually_iteratedLogGauge_eq k] with r hr heq
    exact (ENNReal.ofReal_le_ofReal hr).trans_eq heq.symm
  have hconditional := eventually_nhdsWithin_iff.mp hreal
  have htoreal : Tendsto ENNReal.toReal (𝓝 (0 : ℝ≥0∞)) (𝓝 (0 : ℝ)) := by
    simpa using ENNReal.tendsto_toReal ENNReal.zero_ne_top
  filter_upwards [htoreal.eventually hconditional,
    eventually_ne_nhds ENNReal.zero_ne_top] with d hd hdtop
  by_cases hd0 : d = 0
  · simp [hd0, repeatedLastLogGauge]
  have hpos : 0 < d.toReal := ENNReal.toReal_pos hd0 hdtop
  have h := hd hpos
  simpa only [repeatedLastLogGauge, hdtop, ↓reduceIte, ENNReal.ofReal_toReal hdtop] using h

/-- The literal variant's Hausdorff measure is bounded by the stronger product measure. -/
theorem repeatedLastLogHausdorffMeasure_le (k : ℕ) (E : Set SpaceTime) :
    repeatedLastLogHausdorffMeasure k E ≤ iteratedLogHausdorffMeasure k E :=
  Measure.mkMetric_mono (eventually_repeatedLastLogGauge_le k) (toParabolic '' E)

/-- Every suitable unforced solution also has zero singular-set measure for the
literal expression repeating `L_k` in each of the `k` squared factors. -/
theorem suitable_singularSet_repeatedLastLogHausdorffMeasure_zero
    (k : ℕ) {Ω : Set Space} {I : Set ℝ}
    (data : CKNChallenge.LocalWeakNSESolution Ω I 3) (hforce : data.f = 0) :
    repeatedLastLogHausdorffMeasure k (CKNChallenge.singularSet Ω I data.u) = 0 := by
  apply le_antisymm _ bot_le
  exact (repeatedLastLogHausdorffMeasure_le k _).trans_eq
    (suitable_singularSet_iteratedLogHausdorffMeasure_zero k data hforce)

end FluidSingularSets
