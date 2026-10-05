module

public import FluidSingularSets.CompactGaugeNullity
public import FluidSingularSets.RawSingularPersistence
public import FluidSingularSets.GaugeTransport
public import FluidSingularSets.CompactLocalization

/-!
# Gauge nullity of the actual suitable weak solution singular set

The actual solution supplies uniform positive activity at singular points. Compact
localized singular sets therefore have zero native parabolic gauge measure. Exact
isometric transport and a countable compact interior cover give the physical result.
-/

@[expose] public section

open Set MeasureTheory CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology

noncomputable section

namespace FluidSingularSets

/-- Every compact interior localization of the actual unforced suitable singular set has
zero gauge measure at every positive finite depth. -/
theorem suitable_compact_singularSet_iteratedLogHausdorffMeasure_succ_zero
    (k : ℕ) {Ω : Set Space} {I : Set ℝ}
    (sol : CKNChallenge.LocalWeakNSESolution Ω I 3) (hf : sol.f = 0)
    {K : Set SpaceTime} (hK : IsCompact K) (hKsub : K ⊆ Ω ×ˢ I) :
    iteratedLogHausdorffMeasure (k + 1) (CKNChallenge.singularSet Ω I sol.u ∩ K) = 0 := by
  obtain ⟨hsol, hcompact, hdomain, ε, hε, hpersistent⟩ :=
    exists_raw_compact_singular_persistence sol hf hK hKsub
  have hnull := compact_persistent_set_iteratedLogGauge_null
    hsol k hcompact hdomain hε hpersistent
  have himage : CKNChallenge.parabolicToEuclideanHomeomorph ''
      rawCompactSingularSet Ω I sol.u K = CKNChallenge.singularSet Ω I sol.u ∩ K := by
    exact CKNChallenge.parabolicToEuclideanHomeomorph.toEquiv.image_symm_image _
  rw [← iteratedLogHausdorffMeasure_raw_image, himage] at hnull
  exact hnull

/-- The singular set of an actual unforced suitable weak solution has zero measure for
every positive finite-depth iterated logarithmic gauge. -/
theorem suitable_singularSet_iteratedLogHausdorffMeasure_succ_zero
    (k : ℕ) {Ω : Set Space} {I : Set ℝ}
    (sol : CKNChallenge.LocalWeakNSESolution Ω I 3) (hf : sol.f = 0) :
    iteratedLogHausdorffMeasure (k + 1) (CKNChallenge.singularSet Ω I sol.u) = 0 := by
  change (Measure.mkMetric (iteratedLogGauge (k + 1)) : Measure ParabolicSpaceTime)
    (toParabolic '' CKNChallenge.singularSet Ω I sol.u) = 0
  apply measure_image_zero_of_compact_localizations
    (Measure.mkMetric (iteratedLogGauge (k + 1)) : Measure ParabolicSpaceTime)
    toParabolic (sol.isOpenSpace.prod sol.isOpenTime)
    (fun _ hz ↦ hz.1)
  intro K hK hKsub
  exact suitable_compact_singularSet_iteratedLogHausdorffMeasure_succ_zero k sol hf hK hKsub

/-- The zero-factor CKN theorem and the positive-depth result give the entire finite family. -/
theorem suitable_singularSet_iteratedLogHausdorffMeasure_zero
    (k : ℕ) {Ω : Set Space} {I : Set ℝ}
    (sol : CKNChallenge.LocalWeakNSESolution Ω I 3) (hf : sol.f = 0) :
    iteratedLogHausdorffMeasure k (CKNChallenge.singularSet Ω I sol.u) = 0 := by
  cases k with
  | zero =>
    exact suitableWeakSolution_iteratedLogHausdorffMeasure_zero_factors
      3 (by norm_num) Ω I sol
  | succ k => exact suitable_singularSet_iteratedLogHausdorffMeasure_succ_zero k sol hf

/-- In particular, the actual singular set has zero Hausdorff measure for the
requested radius-times-logarithmic-square gauge in the parabolic metric. -/
theorem suitable_singularSet_logSquaredHausdorffMeasure_zero
    {Ω : Set Space} {I : Set ℝ}
    (sol : CKNChallenge.LocalWeakNSESolution Ω I 3) (hf : sol.f = 0) :
    logSquaredHausdorffMeasure (CKNChallenge.singularSet Ω I sol.u) = 0 := by
  rw [← iteratedLogHausdorffMeasure_one_eq]
  exact suitable_singularSet_iteratedLogHausdorffMeasure_succ_zero 0 sol hf

end FluidSingularSets
