module

public import FluidSingularSets.ConcreteTraceCarleson

/-!
# Almost everywhere representatives for the concrete gradient trace

Null-set changes of the joint gradient preserve every dyadic mixed integral. A gradient
known only on an interior measurable patch can therefore be extended by zero, replaced
by a measurable representative, and used in the concrete Carleson theorem. The final
conversion supplies real finite sums for the mass-ratio stopping argument.
-/

@[expose] public section

open MeasureTheory Set Finset CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

noncomputable section

namespace FluidSingularSets

/-- Joint null-set changes preserve every actual dyadic mixed-gradient activity. -/
theorem dyadicMixedGradientActivity_congr_ae {E : Type*} [NormedAddCommGroup E]
    {D D' : ParabolicPoint → E} (hDD' : D =ᵐ[volume] D')
    (g : ParabolicGridShift) (Q : ParabolicDyadicIndex) :
    dyadicMixedGradientActivity g D Q = dyadicMixedGradientActivity g D' Q := by
  change (fun z : Vec3 × ℝ ↦ D z) =ᵐ[(volume : Measure (Vec3 × ℝ))]
    (fun z : Vec3 × ℝ ↦ D' z) at hDD'
  rw [Measure.volume_eq_prod] at hDD'
  have hmp := Measure.measurePreserving_swap
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure Vec3))
  have hswap := hmp.quasiMeasurePreserving.ae_eq_comp hDD'
  have hslices := Measure.ae_ae_of_ae_prod hswap
  unfold dyadicMixedGradientActivity dyadicMixedActivity
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hslices] with t ht
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae ht] with x hx
  exact congrArg (fun v : E ↦ ‖v‖ₑ ^ (12 / 7 : ℝ)) hx

/-- Agreement on a cell suffices to preserve its actual mixed activity. -/
theorem dyadicMixedGradientActivity_congr_on_cell {E : Type*} [NormedAddCommGroup E]
    {D D' : ParabolicPoint → E} (g : ParabolicGridShift) (Q : ParabolicDyadicIndex)
    (hDD' : Set.EqOn D D' (shiftedParabolicDyadicCell g Q)) :
    dyadicMixedGradientActivity g D Q = dyadicMixedGradientActivity g D' Q := by
  unfold dyadicMixedGradientActivity dyadicMixedActivity
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ico
  intro t ht
  dsimp only
  congr 1
  apply setLIntegral_congr_fun (shiftedDyadicCube_measurable g Q.scale Q.corner)
  intro x hx
  dsimp only
  rw [hDD' (show (x, t) ∈ shiftedParabolicDyadicCell g Q from ⟨hx, ht⟩)]

/-- Joint null-set changes preserve dissipation on every measurable patch. -/
theorem gradient_dissipation_congr_ae {E : Type*} [NormedAddCommGroup E]
    {D D' : ParabolicPoint → E} (hDD' : D =ᵐ[volume] D') (A : Set ParabolicPoint) :
    (∫⁻ z in A, ‖D z‖ₑ ^ (2 : ℕ)) = ∫⁻ z in A, ‖D' z‖ₑ ^ (2 : ℕ) := by
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hDD'] with z hz
  rw [hz]

/-- A locally almost everywhere measurable gradient has a globally measurable zero
extension representative. All contained mixed masses and dissipations are preserved. -/
theorem exists_localized_measurable_gradient
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (D : ParabolicPoint → E) {S : Set ParabolicPoint} (hS : MeasurableSet S)
    (hD : AEStronglyMeasurable D (volume.restrict S)) :
    ∃ D' : ParabolicPoint → E, Measurable D' ∧ D' =ᵐ[volume] S.indicator D ∧
      (∀ g Q, dyadicMixedGradientActivity g D' Q =
        dyadicMixedGradientActivity g (S.indicator D) Q) ∧
      (∀ g Q, shiftedParabolicDyadicCell g Q ⊆ S →
        dyadicMixedGradientActivity g D' Q = dyadicMixedGradientActivity g D Q) ∧
      (∀ A : Set ParabolicPoint, MeasurableSet A → A ⊆ S →
        (∫⁻ z in A, ‖D' z‖ₑ ^ (2 : ℕ)) = ∫⁻ z in A, ‖D z‖ₑ ^ (2 : ℕ)) := by
  have hzero : AEStronglyMeasurable (S.indicator D) volume :=
    (aestronglyMeasurable_indicator_iff hS).2 hD
  let D' := hzero.mk (S.indicator D)
  have hDD' : D' =ᵐ[volume] S.indicator D := hzero.ae_eq_mk.symm
  refine ⟨D', hzero.stronglyMeasurable_mk.measurable, hDD', ?_, ?_, ?_⟩
  · intro g Q
    exact dyadicMixedGradientActivity_congr_ae hDD' g Q
  · intro g Q hQ
    exact (dyadicMixedGradientActivity_congr_ae hDD' g Q).trans
      (dyadicMixedGradientActivity_congr_on_cell g Q
        (fun z hz ↦ Set.indicator_of_mem (hQ hz) D))
  · intro A hA hAS
    calc
      _ = ∫⁻ z in A, ‖S.indicator D z‖ₑ ^ (2 : ℕ) :=
        gradient_dissipation_congr_ae hDD' A
      _ = _ := by
        apply setLIntegral_congr_fun hA
        intro z hz
        dsimp only
        rw [Set.indicator_of_mem (hAS hz) D]

/-- Almost everywhere strong measurability suffices for the concrete extended trace
estimate; its descendants and root dissipation are the original gradient's quantities. -/
theorem exists_frostman_gradient_trace_carleson_of_aestronglyMeasurable
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure ParabolicPoint) [IsFiniteMeasure μ] (k : ℕ)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {r₀ ρ : ℝ} (hr₀ : 0 < r₀) (hρ : 0 < ρ)
    (hgrowth : ∀ z r, 0 < r → r < r₀ →
      μ (Metric.ball z r) ≤ C * iteratedLogGauge k (ENNReal.ofReal r))
    (hdouble : ∀ r, 0 < r → 2 * r ≤ ρ →
      iteratedLogGauge k (ENNReal.ofReal (2 * r)) ≤
        2 * iteratedLogGauge k (ENNReal.ofReal r))
    (g : ParabolicGridShift) (D : ParabolicPoint → E)
    (hD : AEStronglyMeasurable D volume) :
    ∃ n₀ : ℤ, ∀ R : ParabolicDyadicIndex, n₀ ≤ R.scale →
      ∀ P : Finset ParabolicDyadicIndex,
        (∀ Q ∈ P, shiftedParabolicDyadicCell g Q ⊆ shiftedParabolicDyadicCell g R) →
        (∫⁻ z in shiftedParabolicDyadicCell g R, ‖D z‖ₑ ^ (2 : ℕ)) < ⊤ →
        (∑ Q ∈ P, ENNReal.ofReal
          (Real.sqrt ((μ (shiftedParabolicDyadicCell g Q)).toReal * dyadicScale Q.scale /
            dyadicLogFactor k Q.scale)) * dyadicMixedGradientActivity g D Q) ≤
          ENNReal.ofReal (2 * Real.sqrt (4 * C.toReal)) * (64 : ℝ≥0∞) ^ (7 / 6 : ℝ) *
            maximalStrongConstant (7 / 6) *
              ∫⁻ z in shiftedParabolicDyadicCell g R, ‖D z‖ₑ ^ (2 : ℕ) := by
  let D' := hD.mk D
  have hDD' : D =ᵐ[volume] D' := hD.ae_eq_mk
  have hmix (Q : ParabolicDyadicIndex) := dyadicMixedGradientActivity_congr_ae hDD' g Q
  have hmass (R : ParabolicDyadicIndex) :=
    gradient_dissipation_congr_ae hDD' (shiftedParabolicDyadicCell g R)
  obtain ⟨n₀, hbound⟩ := exists_frostman_gradient_trace_carleson μ k hC hr₀ hρ hgrowth
    hdouble g D' hD.stronglyMeasurable_mk.measurable
  refine ⟨n₀, fun R hR P hP hfinite ↦ ?_⟩
  have h := hbound R hR P hP (by simpa only [← hmass] using hfinite)
  simpa only [← hmix, ← hmass] using h

/-- A finite universal coefficient for the gradient trace embedding. -/
def frostmanGradientTraceConstant (C : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * Real.sqrt (4 * C.toReal)) * (64 : ℝ≥0∞) ^ (7 / 6 : ℝ) *
    maximalStrongConstant (7 / 6)

/-- The trace coefficient is finite, even for zero Frostman mass. -/
theorem frostmanGradientTraceConstant_ne_top (C : ℝ≥0∞) :
    frostmanGradientTraceConstant C ≠ ⊤ := by
  unfold frostmanGradientTraceConstant
  rw [mul_assoc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (carleson_maximal_constant_ne_top (by norm_num : (1 : ℝ) < 7 / 6))

/-- Genuine Frostman growth gives the real finite descendant bound required by the
mass-ratio stopping theorem, with the original almost everywhere measurable gradient. -/
theorem exists_frostman_gradient_trace_carleson_real
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure ParabolicPoint) [IsFiniteMeasure μ] (k : ℕ)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {r₀ ρ : ℝ} (hr₀ : 0 < r₀) (hρ : 0 < ρ)
    (hgrowth : ∀ z r, 0 < r → r < r₀ →
      μ (Metric.ball z r) ≤ C * iteratedLogGauge k (ENNReal.ofReal r))
    (hdouble : ∀ r, 0 < r → 2 * r ≤ ρ →
      iteratedLogGauge k (ENNReal.ofReal (2 * r)) ≤
        2 * iteratedLogGauge k (ENNReal.ofReal r))
    (g : ParabolicGridShift) (D : ParabolicPoint → E)
    (hD : AEStronglyMeasurable D volume) :
    ∃ (n₀ : ℤ) (K : ℝ), 0 ≤ K ∧ ∀ R : ParabolicDyadicIndex, n₀ ≤ R.scale →
      ∀ P : Finset ParabolicDyadicIndex,
        (∀ Q ∈ P, shiftedParabolicDyadicCell g Q ⊆ shiftedParabolicDyadicCell g R) →
        (∫⁻ z in shiftedParabolicDyadicCell g R, ‖D z‖ₑ ^ (2 : ℕ)) < ⊤ →
        (∑ Q ∈ P, Real.sqrt
          ((μ (shiftedParabolicDyadicCell g Q)).toReal * dyadicScale Q.scale /
            dyadicLogFactor k Q.scale) * (dyadicMixedGradientActivity g D Q).toReal) ≤
          K * (∫⁻ z in shiftedParabolicDyadicCell g R, ‖D z‖ₑ ^ (2 : ℕ)).toReal := by
  obtain ⟨n₀, hbound⟩ :=
    exists_frostman_gradient_trace_carleson_of_aestronglyMeasurable μ k hC hr₀ hρ
      hgrowth hdouble g D hD
  refine ⟨n₀, (frostmanGradientTraceConstant C).toReal, ENNReal.toReal_nonneg,
    fun R hR P hP hfinite ↦ ?_⟩
  let β : ParabolicDyadicIndex → ℝ≥0∞ := fun Q ↦ ENNReal.ofReal
    (Real.sqrt ((μ (shiftedParabolicDyadicCell g Q)).toReal * dyadicScale Q.scale /
      dyadicLogFactor k Q.scale)) * dyadicMixedGradientActivity g D Q
  have hb : (∑ Q ∈ P, β Q) ≤ frostmanGradientTraceConstant C *
      ∫⁻ z in shiftedParabolicDyadicCell g R, ‖D z‖ₑ ^ (2 : ℕ) :=
    hbound R hR P hP hfinite
  have hBfinite : frostmanGradientTraceConstant C *
      (∫⁻ z in shiftedParabolicDyadicCell g R, ‖D z‖ₑ ^ (2 : ℕ)) ≠ ⊤ :=
    ENNReal.mul_ne_top (frostmanGradientTraceConstant_ne_top C) hfinite.ne
  have hsumfinite : (∑ Q ∈ P, β Q) ≠ ⊤ := ne_top_of_le_ne_top hBfinite hb
  have htermfinite (Q : ParabolicDyadicIndex) (hQ : Q ∈ P) : β Q ≠ ⊤ :=
    ne_top_of_le_ne_top hsumfinite (Finset.single_le_sum (fun _ _ ↦ bot_le) hQ)
  have hreal := ENNReal.toReal_mono hBfinite hb
  rw [ENNReal.toReal_sum htermfinite, ENNReal.toReal_mul] at hreal
  simpa only [β, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using hreal

end FluidSingularSets
