module

public import FluidSingularSets.ParabolicFrostmanGeometry
public import FluidSingularSets.IteratedFrostman

/-!
# Concrete cell growth from a Frostman ball bound

The proved diameter bound places every actual grid cell inside a ball of radius
four times its side length. Two local doubling steps transfer the ball estimate
to the exact cell masses used by the dissipation trace.
-/

@[expose] public section

open MeasureTheory Set CKN.Foundation.Parabolic CKN.Foundation.Euclidean
open scoped ENNReal

noncomputable section

namespace FluidSingularSets

/-- A cell lies in a small open parabolic ball around any of its points. -/
theorem shiftedParabolicDyadicCell_subset_ball (g : ParabolicGridShift)
    (Q : ParabolicDyadicIndex) {z : ParabolicPoint}
    (hz : z ∈ shiftedParabolicDyadicCell g Q) :
    shiftedParabolicDyadicCell g Q ⊆ Metric.ball z (4 * dyadicScale Q.scale) := by
  intro y hy
  have hd := (Metric.edist_le_ediam_of_mem hy hz).trans
    (ediam_shiftedParabolicDyadicCell_le g Q)
  have hdreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
  simp only [← dist_edist,
    ENNReal.toReal_ofReal
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (dyadicScale_pos Q.scale).le)] at hdreal
  exact lt_of_le_of_lt hdreal (by nlinarith only [dyadicScale_pos Q.scale])

/-- Frostman ball growth and actual cell geometry give the cell mass estimate. -/
theorem shiftedParabolicDyadicCell_measure_le_of_ball_growth
    (μ : Measure ParabolicPoint) (h : ℝ≥0∞ → ℝ≥0∞)
    {C : ℝ≥0∞} {r₀ ρ : ℝ}
    (hgrowth : ∀ z r, 0 < r → r < r₀ → μ (Metric.ball z r) ≤ C * h (ENNReal.ofReal r))
    (hdouble : ∀ r, 0 < r → 2 * r ≤ ρ →
      h (ENNReal.ofReal (2 * r)) ≤ 2 * h (ENNReal.ofReal r))
    (g : ParabolicGridShift) (Q : ParabolicDyadicIndex)
    (hsmall : 4 * dyadicScale Q.scale < r₀)
    (hρ : 4 * dyadicScale Q.scale ≤ ρ) :
    μ (shiftedParabolicDyadicCell g Q) ≤
      4 * C * h (ENNReal.ofReal (dyadicScale Q.scale)) := by
  obtain ⟨z, hz⟩ := shiftedParabolicDyadicCell_nonempty g Q
  have hs := dyadicScale_pos Q.scale
  have hfour : h (ENNReal.ofReal (4 * dyadicScale Q.scale)) ≤
      2 * h (ENNReal.ofReal (2 * dyadicScale Q.scale)) := by
    simpa only [show 2 * (2 * dyadicScale Q.scale) = 4 * dyadicScale Q.scale by ring] using
      hdouble (2 * dyadicScale Q.scale) (by positivity) (by nlinarith)
  have htwo := hdouble (dyadicScale Q.scale) hs (by nlinarith)
  calc
    _ ≤ μ (Metric.ball z (4 * dyadicScale Q.scale)) :=
      measure_mono (shiftedParabolicDyadicCell_subset_ball g Q hz)
    _ ≤ C * h (ENNReal.ofReal (4 * dyadicScale Q.scale)) :=
      hgrowth z _ (by positivity) hsmall
    _ ≤ C * (2 * (2 * h (ENNReal.ofReal (dyadicScale Q.scale)))) := by
      exact mul_le_mul' le_rfl (hfour.trans (mul_le_mul' le_rfl htwo))
    _ = _ := by ring

/-- The finite product in the dyadic logarithmic gauge. -/
def dyadicLogFactor (k : ℕ) (n : ℤ) : ℝ :=
  ∏ i ∈ Finset.range k, (max 1 (logIterate (i + 1) (1 / dyadicScale n))) ^ 2

/-- Each logarithmic factor is positive, including outside the eventual exact range. -/
theorem one_le_dyadicLogFactor (k : ℕ) (n : ℤ) : 1 ≤ dyadicLogFactor k n := by
  apply Finset.one_le_prod₀
  intro i _hi
  have h := le_max_left 1 (logIterate (i + 1) (1 / dyadicScale n))
  nlinarith

/-- The actual dyadic gauge is its side length times the finite logarithmic product. -/
theorem iteratedLogGauge_dyadicScale (k : ℕ) (n : ℤ) :
    iteratedLogGauge k (ENNReal.ofReal (dyadicScale n)) =
      ENNReal.ofReal (dyadicScale n * dyadicLogFactor k n) := by
  simp only [iteratedLogGauge, ENNReal.ofReal_ne_top, ↓reduceIte,
    ENNReal.toReal_ofReal (dyadicScale_pos n).le, dyadicLogFactor]

/-- The actual Frostman cell bound supplies the real root growth used by the trace. -/
theorem shiftedParabolicDyadicCell_real_mass_le_log_growth
    (μ : Measure ParabolicPoint) [IsFiniteMeasure μ] (k : ℕ)
    {C : ℝ≥0∞} (hC : C ≠ ∞) {r₀ ρ : ℝ}
    (hgrowth : ∀ z r, 0 < r → r < r₀ →
      μ (Metric.ball z r) ≤ C * iteratedLogGauge k (ENNReal.ofReal r))
    (hdouble : ∀ r, 0 < r → 2 * r ≤ ρ →
      iteratedLogGauge k (ENNReal.ofReal (2 * r)) ≤
        2 * iteratedLogGauge k (ENNReal.ofReal r))
    (g : ParabolicGridShift) (Q : ParabolicDyadicIndex)
    (hsmall : 4 * dyadicScale Q.scale < r₀)
    (hρ : 4 * dyadicScale Q.scale ≤ ρ) :
    (μ (shiftedParabolicDyadicCell g Q)).toReal ≤
      (4 * C.toReal) * dyadicScale Q.scale * dyadicLogFactor k Q.scale := by
  have h := shiftedParabolicDyadicCell_measure_le_of_ball_growth μ (iteratedLogGauge k)
    hgrowth hdouble g Q hsmall hρ
  rw [iteratedLogGauge_dyadicScale] at h
  have hfin : 4 * C * ENNReal.ofReal (dyadicScale Q.scale * dyadicLogFactor k Q.scale) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hC) ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono hfin h
  have hnonneg : 0 ≤ dyadicScale Q.scale * dyadicLogFactor k Q.scale :=
    mul_nonneg (dyadicScale_pos _).le (zero_le_one.trans (one_le_dyadicLogFactor _ _))
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal hnonneg, mul_assoc] using hreal

/-- Finer integer levels have smaller side length. -/
theorem dyadicScale_antitone : Antitone dyadicScale := by
  intro n m hnm
  dsimp only [dyadicScale]
  exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).2 (by omega)

/-- On the positive logarithmic tail, the actual scale factors increase with refinement. -/
theorem dyadicLogFactor_le_of_log_positive (k : ℕ) {n m : ℤ} (hnm : n ≤ m)
    (hlog : ∀ i ≤ k, 0 < logIterate i (1 / dyadicScale n)) :
    dyadicLogFactor k n ≤ dyadicLogFactor k m := by
  have hinv : 1 / dyadicScale n ≤ 1 / dyadicScale m :=
    one_div_le_one_div_of_le (dyadicScale_pos m) (dyadicScale_antitone hnm)
  apply Finset.prod_le_prod₀
  · intro i _hi
    exact sq_nonneg _
  · intro i hi
    have hlogle := logIterate_le_of_positive hinv (i + 1) (fun j hj ↦
      hlog j (by have := Finset.mem_range.1 hi; omega))
    exact pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _))
      (max_le_max_left 1 hlogle) 2

/-- A single level cutoff simultaneously gives ball admissibility and positive,
monotone logarithmic factors at every finer level. -/
theorem exists_dyadicLogFactor_frostman_cutoff (k : ℕ) {r₀ ρ : ℝ}
    (hr₀ : 0 < r₀) (hρ : 0 < ρ) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n →
      4 * dyadicScale n < r₀ ∧ 4 * dyadicScale n ≤ ρ ∧
      (∀ i ≤ k, 1 ≤ logIterate i (1 / dyadicScale n)) ∧
      (∀ d : ℕ, dyadicLogFactor k n ≤ dyadicLogFactor k (n + d)) := by
  obtain ⟨S, hS, hlogs, _hanti⟩ := exists_antitone_logGaugeExponent_tail k
  let B : ℝ := min (min (r₀ / 4) (ρ / 4)) S⁻¹
  have hB : 0 < B := lt_min (lt_min (by positivity) (by positivity)) (inv_pos.2 hS)
  obtain ⟨n₀, _, hn₀⟩ := exists_dyadicScale_for_radius (show 0 < B / 64 by positivity)
  have hn₀B : dyadicScale n₀ < B := by linarith only [hn₀, hB]
  refine ⟨n₀, ?_⟩
  intro n hn
  have hnB : dyadicScale n < B := (dyadicScale_antitone hn).trans_lt hn₀B
  have hnsmall : dyadicScale n < r₀ / 4 :=
    hnB.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hnρ : dyadicScale n < ρ / 4 :=
    hnB.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hnS : dyadicScale n ≤ S⁻¹ := hnB.le.trans (min_le_right _ _)
  have hinv : S ≤ 1 / dyadicScale n := by
    simpa only [one_div, inv_inv] using inv_anti₀ (dyadicScale_pos n) hnS
  have hlog (i : ℕ) (hi : i ≤ k) := hlogs _ hinv i hi
  refine ⟨by linarith, by linarith, hlog, ?_⟩
  intro d
  exact dyadicLogFactor_le_of_log_positive k (by omega)
    (fun i hi ↦ zero_lt_one.trans_le (hlog i hi))

end FluidSingularSets
