module

public import FluidSingularSets.ConcreteMassRatioTrace
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Almost everywhere finite actual cell costs

Tonelli's theorem turns the summable concrete mass-ratio trace into a summable
series of cell costs at almost every point of the Frostman measure. This uses
only measurable cell indicators, so the singular set needs no extra activity
measurability assumption in the contradiction argument.
-/

@[expose] public section

open MeasureTheory Set CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

noncomputable section

namespace FluidSingularSets

/-- Summable integrated nonnegative cell costs are pointwise summable almost everywhere. -/
theorem ae_summable_cell_costs {X J : Type*} [MeasurableSpace X] [Countable J]
    (μ : Measure X) [IsFiniteMeasure μ] (A : J → Set X) (a : J → ℝ)
    (hA : ∀ j, MeasurableSet (A j)) (ha : ∀ j, 0 ≤ a j)
    (hsum : Summable (fun j ↦ (μ (A j)).toReal * a j)) :
    ∀ᵐ x ∂μ, Summable (fun j ↦ (A j).indicator (fun _ ↦ a j) x) := by
  classical
  let f : J → X → ℝ≥0∞ := fun j ↦ (A j).indicator (fun _ ↦ ENNReal.ofReal (a j))
  have hf (j : J) : Measurable (f j) := measurable_const.indicator (hA j)
  have hint (j : J) : (∫⁻ x, f j x ∂μ) = ENNReal.ofReal ((μ (A j)).toReal * a j) := by
    dsimp only [f]
    rw [lintegral_indicator (hA j), setLIntegral_const,
      ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (measure_ne_top μ (A j)), mul_comm]
  have hfinite : (∫⁻ x, ∑' j, f j x ∂μ) ≠ ⊤ := by
    rw [lintegral_tsum (fun j ↦ (hf j).aemeasurable)]
    simp_rw [hint]
    exact hsum.tsum_ofReal_ne_top
  filter_upwards [ae_lt_top' (Measurable.tsum hf).aemeasurable hfinite] with x hx
  have hpos (j : J) : 0 ≤ (A j).indicator (fun _ ↦ a j) x := by
    exact Set.indicator_nonneg (fun _ _ ↦ ha j) x
  have heq (j : J) : f j x = ENNReal.ofReal ((A j).indicator (fun _ ↦ a j) x) := by
    by_cases hxA : x ∈ A j <;> simp [f, hxA]
  simp_rw [heq] at hx
  have hs := ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hx.ne
  simpa only [Real.coe_toNNReal _ (hpos _)] using hs

/-- The pointwise cost of one actual cell, with zero cost at zero dissipation. -/
def dyadicGradientTraceCost {E : Type*} [NormedAddCommGroup E]
    (k : ℕ) (g : ParabolicGridShift) (D : ParabolicPoint → E)
    (Q : ParabolicDyadicIndex) : ℝ :=
  (dyadicMixedGradientActivity g D Q).toReal /
    Real.sqrt (((∫⁻ z in shiftedParabolicDyadicCell g Q, ‖D z‖ₑ ^ (2 : ℕ)).toReal /
      dyadicScale Q.scale) * dyadicLogFactor k Q.scale)

/-- Genuine Frostman growth and finite gradient energy give a finite actual cell
trace at almost every Frostman point, simultaneously in all sixteen grids. -/
theorem exists_frostman_ae_summable_gradient_trace
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure ParabolicPoint) [IsFiniteMeasure μ] (k : ℕ)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {r₀ ρ : ℝ} (hr₀ : 0 < r₀) (hρ : 0 < ρ)
    (hgrowth : ∀ z r, 0 < r → r < r₀ →
      μ (Metric.ball z r) ≤ C * iteratedLogGauge k (ENNReal.ofReal r))
    (hdouble : ∀ r, 0 < r → 2 * r ≤ ρ →
      iteratedLogGauge k (ENNReal.ofReal (2 * r)) ≤
        2 * iteratedLogGauge k (ENNReal.ofReal r))
    (D : ParabolicPoint → E) (hD : AEStronglyMeasurable D volume)
    (hfinite : (∫⁻ z, ‖D z‖ₑ ^ (2 : ℕ)) < ⊤) :
    ∃ n₀ : ParabolicGridShift → ℤ, ∀ᵐ z ∂μ,
      Summable (fun P : Σ g, {Q : ParabolicDyadicIndex // n₀ g ≤ Q.scale} ↦
        (shiftedParabolicDyadicCell P.1 P.2).indicator
          (fun _ ↦ dyadicGradientTraceCost k P.1 D P.2) z) := by
  classical
  have hex (g : ParabolicGridShift) := exists_frostman_gradient_mass_ratio_trace
    μ k hC hr₀ hρ hgrowth hdouble g D hD hfinite
  choose n₀ hn₀ using hex
  have hae (g : ParabolicGridShift) : ∀ᵐ z ∂μ,
      Summable (fun Q : {Q : ParabolicDyadicIndex // n₀ g ≤ Q.scale} ↦
        (shiftedParabolicDyadicCell g Q).indicator
          (fun _ ↦ dyadicGradientTraceCost k g D Q) z) := by
    apply ae_summable_cell_costs μ
      (fun Q : {Q : ParabolicDyadicIndex // n₀ g ≤ Q.scale} ↦
        shiftedParabolicDyadicCell g Q)
      (fun Q ↦ dyadicGradientTraceCost k g D Q)
      (fun Q ↦ shiftedParabolicDyadicCell_measurable g Q)
      (fun _ ↦ div_nonneg ENNReal.toReal_nonneg (Real.sqrt_nonneg _))
    simpa only [dyadicGradientTraceCost, mul_div_assoc] using hn₀ g
  refine ⟨n₀, ?_⟩
  filter_upwards [ae_all_iff.2 hae] with z hz
  apply (summable_sigma_of_nonneg (fun P ↦ ?_)).2
  · exact ⟨hz, summable_of_hasFiniteSupport (Set.toFinite _)⟩
  · exact Set.indicator_nonneg (fun _ _ ↦
      div_nonneg ENNReal.toReal_nonneg (Real.sqrt_nonneg _)) z

end FluidSingularSets
