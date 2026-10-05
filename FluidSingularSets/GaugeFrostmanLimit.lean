-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import FluidSingularSets.GaugeFrostman
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Sequences

/-!
# Compactness for the finite gauge capacity construction

Uniform eventual bounds on open sets pass from the finite probability measures
to a probability measure on a compact set. Pushing forward from the compact
subtype gives an ambient measure supported on that set, with the same ball bounds.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- All eventual open-set bounds pass simultaneously to a subsequential limit.
The family of open sets need not be countable. -/
theorem exists_probabilityMeasure_of_eventual_open_bounds {X I : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [SecondCountableTopology X] (seq : ℕ → ProbabilityMeasure X)
    (U : I → Set X) (B : I → ℝ≥0∞) (hopen : ∀ i, IsOpen (U i))
    (hbound : ∀ i, ∀ᶠ n in atTop, (seq n : Measure X) (U i) ≤ B i) :
    ∃ μ : ProbabilityMeasure X, ∀ i, (μ : Measure X) (U i) ≤ B i := by
  obtain ⟨μ, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq seq
  refine ⟨μ, fun i => ?_⟩
  have hb : ∀ᶠ n in atTop, ((seq ∘ φ) n : Measure X) (U i) ≤ B i :=
    hφ.tendsto_atTop.eventually (hbound i)
  exact (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim (hopen i)).trans
    (liminf_le_of_frequently_le' hb.frequently)

/-- Finite approximations on a compact subtype yield a supported ambient
probability measure with the same small-radius gauge bounds. -/
theorem exists_supported_probabilityMeasure_of_eventual_ball_bounds {X : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (K : Set X) (hK : IsCompact K) (seq : ℕ → ProbabilityMeasure K)
    (h : ℝ≥0∞ → ℝ≥0∞) (C : ℝ≥0∞) (r₀ : ℝ)
    (hbound : ∀ (x : X) (r : ℝ), 0 < r → r < r₀ →
      ∀ᶠ n in atTop, (seq n : Measure K) (Subtype.val ⁻¹' Metric.ball x r) ≤
        C * h (ENNReal.ofReal r)) :
    ∃ μ : ProbabilityMeasure X, (μ : Measure X) Kᶜ = 0 ∧
      ∀ (x : X) (r : ℝ), 0 < r → r < r₀ →
        (μ : Measure X) (Metric.ball x r) ≤ C * h (ENNReal.ofReal r) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let I := X × {r : ℝ // 0 < r ∧ r < r₀}
  let U : I → Set K := fun i => Subtype.val ⁻¹' Metric.ball i.1 i.2.1
  let B : I → ℝ≥0∞ := fun i => C * h (ENNReal.ofReal i.2.1)
  obtain ⟨ν, hν⟩ := exists_probabilityMeasure_of_eventual_open_bounds seq U B
    (fun _ => Metric.isOpen_ball.preimage continuous_subtype_val)
    (fun i => hbound i.1 i.2.1 i.2.2.1 i.2.2.2)
  refine ⟨ν.map Subtype.val, ?_, fun x r hr hr₀ => ?_⟩
  · rw [ν.map_apply' measurable_subtype_coe.aemeasurable hK.measurableSet.compl]
    have hpreimage : (Subtype.val : K → X) ⁻¹' Kᶜ = ∅ := by
      ext x
      simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false]
      exact not_not.mpr x.property
    rw [hpreimage, measure_empty]
  · rw [ν.map_apply' measurable_subtype_coe.aemeasurable measurableSet_ball]
    exact hν (x, ⟨r, hr, hr₀⟩)

/-- The limit is an actual finite, nonzero measure supported on the compact set.
This is the compactness step; the finite capacity and geometry estimates supply
the sequence and its uniform ball bounds. -/
theorem exists_supported_finite_measure_of_eventual_ball_bounds {X : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (K : Set X) (hK : IsCompact K) (seq : ℕ → ProbabilityMeasure K)
    (h : ℝ≥0∞ → ℝ≥0∞) (C : ℝ≥0∞) (r₀ : ℝ)
    (hbound : ∀ (x : X) (r : ℝ), 0 < r → r < r₀ →
      ∀ᶠ n in atTop, (seq n : Measure K) (Subtype.val ⁻¹' Metric.ball x r) ≤
        C * h (ENNReal.ofReal r)) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ μ ≠ 0 ∧ μ Kᶜ = 0 ∧
      ∀ (x : X) (r : ℝ), 0 < r → r < r₀ →
        μ (Metric.ball x r) ≤ C * h (ENNReal.ofReal r) := by
  obtain ⟨μ, hsupport, hgrowth⟩ :=
    exists_supported_probabilityMeasure_of_eventual_ball_bounds K hK seq h C r₀ hbound
  exact ⟨μ, inferInstance, IsProbabilityMeasure.ne_zero _, hsupport, hgrowth⟩

end FluidSingularSets
