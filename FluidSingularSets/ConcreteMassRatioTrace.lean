module

public import FluidSingularSets.ConcreteTraceAE
public import FluidSingularSets.ShiftedCellRepresentation
public import FluidSingularSets.TraceCost

/-!
# The actual gradient mass-ratio trace

The genuine Frostman descendant estimate is transferred from cell indices to
measurable sets and inserted into the stopping argument. The resulting full
trace is summable for every globally finite gradient dissipation, including
cells of zero mass. No trace estimate is included among the hypotheses.
-/

@[expose] public section

open MeasureTheory Set Finset CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

noncomputable section

namespace FluidSingularSets

/-- A finite indexed descendant estimate controls the actual mass-ratio sum. -/
theorem finite_shifted_mass_ratio_trace
    (μ ν : Measure ParabolicPoint) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (g : ParabolicGridShift) (b : ParabolicDyadicIndex → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (P : Finset ParabolicDyadicIndex) (hb : ∀ Q ∈ P, 0 ≤ b Q)
    (hcar : ∀ R ∈ P, ∀ T : Finset ParabolicDyadicIndex, T ⊆ P →
      (∀ Q ∈ T, shiftedParabolicDyadicCell g Q ⊆ shiftedParabolicDyadicCell g R) →
      (∑ Q ∈ T, b Q) ≤ K * (ν (shiftedParabolicDyadicCell g R)).toReal) :
    (∑ Q ∈ P, b Q * Real.sqrt ((μ (shiftedParabolicDyadicCell g Q)).toReal /
      (ν (shiftedParabolicDyadicCell g Q)).toReal)) ≤
      2 * K * Real.sqrt ((μ univ).toReal * (ν univ).toReal) := by
  classical
  let S := P.image (shiftedParabolicDyadicCell g)
  let β : Set ParabolicPoint → ℝ := fun A ↦ b (shiftedCellRepresentation g A)
  have hS (A : Set ParabolicPoint) (hA : A ∈ S) :
      ∃ Q ∈ P, shiftedParabolicDyadicCell g Q = A := mem_image.1 hA
  have hβQ (Q : ParabolicDyadicIndex) : β (shiftedParabolicDyadicCell g Q) = b Q := by
    simp only [β, shiftedCellRepresentation_eq]
  have hsetcar (A : Set ParabolicPoint) (hA : A ∈ S) :
      (∑ B ∈ S.filter (fun B ↦ B ⊆ A), β B) ≤ K * (ν A).toReal := by
    obtain ⟨R, hR, rfl⟩ := hS A hA
    let T := P.filter (fun Q ↦ shiftedParabolicDyadicCell g Q ⊆
      shiftedParabolicDyadicCell g R)
    have himage : T.image (shiftedParabolicDyadicCell g) =
        S.filter (fun B ↦ B ⊆ shiftedParabolicDyadicCell g R) := by
      ext B
      simp only [T, S, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨Q, ⟨hQ, hsub⟩, rfl⟩
        exact ⟨⟨Q, hQ, rfl⟩, hsub⟩
      · rintro ⟨⟨Q, hQ, rfl⟩, hsub⟩
        exact ⟨Q, ⟨hQ, hsub⟩, rfl⟩
    rw [← himage, sum_image]
    · simp only [hβQ]
      exact hcar R hR T (filter_subset _ _) (fun Q hQ ↦ (mem_filter.1 hQ).2)
    · exact fun Q _ R _ h ↦ shiftedParabolicDyadicCell_injective g h
  have htrace := finite_laminar_mass_ratio_trace_allow_zero μ ν S β
    (fun A hA ↦ by obtain ⟨Q, _, rfl⟩ := hS A hA
                   exact shiftedParabolicDyadicCell_measurable g Q)
    (fun A hA B hB ↦ by
      obtain ⟨Q, _, rfl⟩ := hS A hA
      obtain ⟨R, _, rfl⟩ := hS B hB
      exact shiftedParabolicDyadicCell_nested_or_disjoint g Q R)
    (fun A hA ↦ by obtain ⟨Q, hQ, rfl⟩ := hS A hA
                   rw [hβQ]; exact hb Q hQ) hK hsetcar
  dsimp only [S] at htrace
  rw [sum_image] at htrace
  · simpa only [hβQ] using htrace
  · exact fun Q _ R _ h ↦ shiftedParabolicDyadicCell_injective g h

/-- The actual fine-cell trace has finite total mass under genuine Frostman growth. -/
theorem exists_frostman_gradient_mass_ratio_trace
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure ParabolicPoint) [IsFiniteMeasure μ] (k : ℕ)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {r₀ ρ : ℝ} (hr₀ : 0 < r₀) (hρ : 0 < ρ)
    (hgrowth : ∀ z r, 0 < r → r < r₀ →
      μ (Metric.ball z r) ≤ C * iteratedLogGauge k (ENNReal.ofReal r))
    (hdouble : ∀ r, 0 < r → 2 * r ≤ ρ →
      iteratedLogGauge k (ENNReal.ofReal (2 * r)) ≤
        2 * iteratedLogGauge k (ENNReal.ofReal r))
    (g : ParabolicGridShift) (D : ParabolicPoint → E)
    (hD : AEStronglyMeasurable D volume)
    (hfinite : (∫⁻ z, ‖D z‖ₑ ^ (2 : ℕ)) < ⊤) :
    ∃ n₀ : ℤ, Summable (fun Q : {Q : ParabolicDyadicIndex // n₀ ≤ Q.scale} ↦
      (μ (shiftedParabolicDyadicCell g Q)).toReal *
        (dyadicMixedGradientActivity g D Q).toReal /
        Real.sqrt (((∫⁻ z in shiftedParabolicDyadicCell g Q, ‖D z‖ₑ ^ (2 : ℕ)).toReal /
          dyadicScale Q.val.scale) * dyadicLogFactor k Q.val.scale)) := by
  classical
  obtain ⟨n₀, K, hK, hcar⟩ := exists_frostman_gradient_trace_carleson_real μ k hC hr₀ hρ
    hgrowth hdouble g D hD
  let ν := volume.withDensity (fun z : ParabolicPoint ↦ ‖D z‖ₑ ^ (2 : ℕ))
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfinite.ne
  let b : ParabolicDyadicIndex → ℝ := fun Q ↦
    Real.sqrt ((μ (shiftedParabolicDyadicCell g Q)).toReal * dyadicScale Q.scale /
      dyadicLogFactor k Q.scale) * (dyadicMixedGradientActivity g D Q).toReal
  have hb (Q : ParabolicDyadicIndex) : 0 ≤ b Q :=
    mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg
  have hν (Q : ParabolicDyadicIndex) : ν (shiftedParabolicDyadicCell g Q) =
      ∫⁻ z in shiftedParabolicDyadicCell g Q, ‖D z‖ₑ ^ (2 : ℕ) :=
    withDensity_apply _ (shiftedParabolicDyadicCell_measurable g Q)
  have hbound (P : Finset {Q : ParabolicDyadicIndex // n₀ ≤ Q.scale}) :
      (∑ Q ∈ P, b Q * Real.sqrt ((μ (shiftedParabolicDyadicCell g Q)).toReal /
        (ν (shiftedParabolicDyadicCell g Q)).toReal)) ≤
        2 * K * Real.sqrt ((μ univ).toReal * (ν univ).toReal) := by
    let T := P.image Subtype.val
    have hT (Q : ParabolicDyadicIndex) (hQ : Q ∈ T) : n₀ ≤ Q.scale := by
      obtain ⟨R, _, rfl⟩ := mem_image.1 hQ
      exact R.property
    have h := finite_shifted_mass_ratio_trace μ ν g b hK T (fun Q _ ↦ hb Q)
      (fun R hR U _ hU ↦ by
        simpa only [b, hν] using hcar R (hT R hR) U hU
          (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hfinite))
    dsimp only [T] at h
    rw [sum_image] at h
    · exact h
    · exact fun Q _ R _ h ↦ Subtype.ext h
  have hsum := summable_of_sum_le
    (fun Q : {Q : ParabolicDyadicIndex // n₀ ≤ Q.scale} ↦
      mul_nonneg (hb Q) (Real.sqrt_nonneg _)) hbound
  refine ⟨n₀, hsum.congr (fun Q ↦ ?_)⟩
  rw [hν]
  exact trace_cost_mass_ratio_identity ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (dyadicScale_pos _) (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_dyadicLogFactor k Q.val.scale))

end FluidSingularSets
