module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Topology.MetricSpace.Snowflaking

/-!
# Parabolic gauges and upper box dimension

Space-time is measured using the maximum of Euclidean spatial distance and the square root of
time distance. The box dimension uses the infimum of polynomial covering exponents, avoiding
the nonextended real `limsup` convention for unbounded covering growth.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace FluidSingularSets

/-- Three-dimensional Euclidean space. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Time equipped with square-root distance. -/
abbrev ParabolicTime :=
  Metric.Snowflaking ℝ (1 / 2 : ℝ) (by norm_num) (by norm_num)

instance : MeasurableSpace ParabolicTime := borel ParabolicTime
instance : BorelSpace ParabolicTime := ⟨rfl⟩

/-- Ordinary coordinates, with the parabolic metric used after lifting the time coordinate. -/
abbrev SpaceTime := Space × ℝ

/-- The product metric here is `max ‖x-y‖ |t-s|^(1/2)`. -/
abbrev ParabolicSpaceTime := Space × ParabolicTime

/-- Passage from ordinary space-time coordinates to parabolic metric coordinates. -/
def toParabolic : SpaceTime → ParabolicSpaceTime :=
  fun z ↦ (z.1, Metric.Snowflaking.toSnowflaking z.2)

/-- The small-radius gauge `r(log(1/r))²`, extended constantly after `exp(-2)`.
The value at zero is zero, and the value at infinite diameter is infinite. The extension does
not affect the Hausdorff measure because the construction only uses arbitrarily small covers. -/
def logSquaredGauge (d : ℝ≥0∞) : ℝ≥0∞ :=
  if d = ∞ then ∞ else
    ENNReal.ofReal (if d.toReal ≤ Real.exp (-2) then
      d.toReal * (Real.log (1 / d.toReal)) ^ 2 else 4 * Real.exp (-2))

/-- Hausdorff measure for the logarithmic gauge and parabolic diameter.
This uses Mathlib's metric Hausdorff measure constructor on the lifted set. -/
def logSquaredHausdorffMeasure (E : Set SpaceTime) : ℝ≥0∞ :=
  (Measure.mkMetric logSquaredGauge : Measure ParabolicSpaceTime) (toParabolic '' E)

/-- Parabolic covering number, using arbitrary centers and closed radius-`r` balls.
The value is extended nonnegative so noncoverable sets retain the value infinity. -/
def parabolicCoveringNumber (E : Set SpaceTime) (r : ℝ≥0) : ℕ∞ :=
  Metric.externalCoveringNumber r (toParabolic '' E)

/-- Upper parabolic box dimension is the infimum of nonnegative exponents `s` such that
`N(E,r) ≤ C r^(-s)` for all sufficiently small positive radii and some finite positive `C`.
For bounded sets this agrees with the usual logarithmic `limsup` definition. The infimum of
an empty set of exponents is infinity; the empty set has dimension zero. -/
def upperParabolicBoxDimension (E : Set SpaceTime) : ℝ≥0∞ :=
  ⨅ (s : ℝ) (_ : 0 ≤ s)
    (_ : ∃ C : ℝ, 0 < C ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r < r₀ →
        (parabolicCoveringNumber E r.toNNReal).toENNReal ≤
          ENNReal.ofReal (C * r ^ (-s))), ENNReal.ofReal s

end FluidSingularSets
