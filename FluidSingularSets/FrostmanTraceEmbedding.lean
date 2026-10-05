module

public import FluidSingularSets.FrostmanCellGrowth
public import FluidSingularSets.SpatialTraceCarleson

/-!
# Integrated embedding for actual Frostman slice coefficients

The Frostman ball estimate derives the root cell growth, the fine-level cutoff,
and every spatial descendant coefficient bound. No Carleson estimate is included
among the hypotheses of this concrete embedding theorem.
-/

@[expose] public section

open MeasureTheory Set CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

noncomputable section

namespace FluidSingularSets

/-- The actual cubes of a fixed grid at and below a specified side length. -/
def fineShiftedSpatialGrid (g : ParabolicGridShift) (n₀ : ℤ) : Set (Set Vec3) :=
  {A | A ∈ shiftedSpatialGrid g ∧ n₀ ≤ (shiftedSpatialRepresentation g A).scale}

/-- Genuine Frostman growth gives a finite full time-integrated dissipation embedding.
The density can be the localized gradient to the power `12/7`, for which its
`7/6` product-space mass is the usual dissipation. -/
theorem exists_finite_frostman_trace_embedding
    (μ : Measure ParabolicPoint) [IsFiniteMeasure μ] (k : ℕ)
    {C : ℝ≥0∞} (hC : C ≠ ∞) {r₀ ρ : ℝ} (hr₀ : 0 < r₀) (hρ : 0 < ρ)
    (hgrowth : ∀ z r, 0 < r → r < r₀ →
      μ (Metric.ball z r) ≤ C * iteratedLogGauge k (ENNReal.ofReal r))
    (hdouble : ∀ r, 0 < r → 2 * r ≤ ρ →
      iteratedLogGauge k (ENNReal.ofReal (2 * r)) ≤
        2 * iteratedLogGauge k (ENNReal.ofReal r))
    (g : ParabolicGridShift) (τ : Measure ℝ) (f : ℝ → Vec3 → ℝ≥0∞)
    (hf : Measurable (fun z : ℝ × Vec3 ↦ f z.1 z.2))
    (hfp : (∫⁻ z : ℝ × Vec3, f z.1 z.2 ^ (7 / 6 : ℝ) ∂τ.prod volume) < ⊤) :
    ∃ n₀ : ℤ,
      (∑' A : fineShiftedSpatialGrid g n₀, ∫⁻ t,
        spatialTraceSetCoefficient μ (dyadicLogFactor k) g A t *
          (⨍⁻ x in A, f t x ∂volume) ^ (7 / 6 : ℝ) ∂τ) < ⊤ := by
  obtain ⟨n₀, hcut⟩ := exists_dyadicLogFactor_frostman_cutoff k hr₀ hρ
  refine ⟨n₀, ?_⟩
  have hgrid (A : Set Vec3) (hA : A ∈ fineShiftedSpatialGrid g n₀) :
      A ∈ shiftedSpatialGrid g := hA.1
  have hF (A : Set Vec3) (_hA : A ∈ fineShiftedSpatialGrid g n₀) :
      0 < dyadicLogFactor k (shiftedSpatialRepresentation g A).scale :=
    zero_lt_one.trans_le (one_le_dyadicLogFactor _ _)
  have hmono (A : Set Vec3) (hA : A ∈ fineShiftedSpatialGrid g n₀) (d : ℕ) :
      dyadicLogFactor k (shiftedSpatialRepresentation g A).scale ≤
        dyadicLogFactor k ((shiftedSpatialRepresentation g A).scale + d) :=
    (hcut _ hA.2).2.2.2 d
  have hmass (t : ℝ) (A : Set Vec3) (hA : A ∈ fineShiftedSpatialGrid g n₀) :
      (μ (shiftedTraceCell g (shiftedSpatialRepresentation g A).scale
        (shiftedSpatialRepresentation g A).corner t)).toReal ≤
          (4 * C.toReal) * dyadicScale (shiftedSpatialRepresentation g A).scale *
            dyadicLogFactor k (shiftedSpatialRepresentation g A).scale := by
    let Q := shiftedTraceIndex g (shiftedSpatialRepresentation g A).scale
      (shiftedSpatialRepresentation g A).corner t
    exact shiftedParabolicDyadicCell_real_mass_le_log_growth μ k hC hgrowth hdouble
      g Q (hcut _ hA.2).1 (hcut _ hA.2).2.1
  have hbound := integrated_spatialTraceSetCoefficient_embedding μ (dyadicLogFactor k)
    g τ (fineShiftedSpatialGrid g n₀) f (by positivity : 0 ≤ 4 * C.toReal)
    (by norm_num : (1 : ℝ) < 7 / 6) hgrid hF hmono hmass hf hfp
  apply hbound.trans_lt
  rw [mul_assoc (ENNReal.ofReal _)]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top
    (lt_top_iff_ne_top.2 ENNReal.ofReal_ne_top)
    (lt_top_iff_ne_top.2 (carleson_maximal_constant_ne_top (by norm_num)))) hfp

end FluidSingularSets
