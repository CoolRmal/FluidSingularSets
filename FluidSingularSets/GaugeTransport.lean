module

public import FluidSingularSets.CKNBaseline

/-!
# Transport of every gauge between the CKN and independent parabolic carriers

The bridge is an isometric equivalence, so arbitrary gauge Hausdorff measures
agree on every set, including nonmeasurable sets. This lets the geometric measure
construction use the native CKN cells and the target use its independent metric.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace FluidSingularSets

/-- An isometric equivalence preserves gauge Hausdorff measure on every set. -/
theorem gaugeMeasure_isometryEquiv_image {X Y : Type*}
    [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (h : ℝ≥0∞ → ℝ≥0∞) (e : X ≃ᵢ Y) (E : Set X) :
    (Measure.mkMetric h : Measure Y) (e '' E) = (Measure.mkMetric h : Measure X) E := by
  simp only [← OuterMeasure.coe_mkMetric, ← OuterMeasure.comap_apply]
  rw [OuterMeasure.isometryEquiv_comap_mkMetric]

/-- Every iterated gauge agrees exactly with its native CKN parabolic representation. -/
theorem iteratedLogHausdorffMeasure_raw_image (k : ℕ)
    (E : Set CKN.Foundation.Parabolic.ParabolicPoint) :
    iteratedLogHausdorffMeasure k (CKNChallenge.parabolicToEuclideanHomeomorph '' E) =
      (Measure.mkMetric (iteratedLogGauge k) :
        Measure CKN.Foundation.Parabolic.ParabolicPoint) E := by
  change (Measure.mkMetric (iteratedLogGauge k) : Measure ParabolicSpaceTime)
    (toParabolic '' (CKNChallenge.parabolicToEuclideanHomeomorph '' E)) = _
  have heq : (fun z ↦ toParabolic (CKNChallenge.parabolicToEuclideanHomeomorph z)) =
      CKNChallenge.rawParabolicIsometry := by
    funext z
    rfl
  rw [image_image, heq]
  exact gaugeMeasure_isometryEquiv_image _ CKNChallenge.rawParabolicIsometry E

end FluidSingularSets
