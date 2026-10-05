module

public import FluidSingularSets.WeightedActivity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# A finite trace cannot support persistent activity

The scalar scale recurrence forces a divergent cost at every persistent point. Tonelli's
theorem turns a finite integrated cost into pointwise summability almost everywhere, so the
set of persistent points is null. This is the contradiction step used after constructing
the dissipation trace; it does not assert that Navier–Stokes data already satisfy that trace.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FluidSingularSets

/-- A finite integrated weighted trace gives zero mass to all points where the activity
recurrence remains bounded below. No measurability assumption on the persistent set is needed.
-/
theorem persistent_activity_trace_null {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (E : Set X) (G e : ℕ → X → ℝ) (w : ℕ → ℝ) {ε C : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C)
    (hw : ∀ n, 0 ≤ w n) (hanti : Antitone w) (hdiverge : ¬ Summable w)
    (hmeas : ∀ n, AEMeasurable (fun x ↦
      ENNReal.ofReal (w n * e n x / Real.sqrt (G n x))) μ)
    (htrace : (∑' n, ∫⁻ x, ENNReal.ofReal (w n * e n x / Real.sqrt (G n x)) ∂μ) ≠ ∞)
    (hG : ∀ x ∈ E, ∀ n, ε ≤ G n x) (he : ∀ x ∈ E, ∀ n, 0 ≤ e n x)
    (hrec : ∀ x ∈ E, ∀ n,
      G (n + 1) x ≤ G n x / 4 + C * Real.sqrt (G n x) * e n x) :
    μ E = 0 := by
  have hint : (∫⁻ x, ∑' n,
      ENNReal.ofReal (w n * e n x / Real.sqrt (G n x)) ∂μ) ≠ ∞ := by
    rwa [lintegral_tsum hmeas]
  have hfinite := ae_lt_top' (AEMeasurable.tsum hmeas) hint
  have hnot : ∀ᵐ x ∂μ, x ∉ E := by
    filter_upwards [hfinite] with x hx
    intro hxE
    have hpos (n : ℕ) : 0 ≤ w n * e n x / Real.sqrt (G n x) :=
      div_nonneg (mul_nonneg (hw n) (he x hxE n)) (Real.sqrt_nonneg _)
    have hsum : Summable (fun n ↦ w n * e n x / Real.sqrt (G n x)) := by
      have hnnsum := ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hx.ne
      simpa only [Real.coe_toNNReal _ (hpos _)] using hnnsum
    exact persistent_activity_weighted_not_summable (fun n ↦ G n x) (fun n ↦ e n x)
      w hε hC (hG x hxE) (he x hxE) hw hanti hdiverge (hrec x hxE) hsum
  simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hnot

end FluidSingularSets
