module

public import FluidSingularSets.Gauge
public import Mathlib.Tactic

/-!
# Finite families of successive logarithmic gauges

At sufficiently small radii the gauge with `k` factors is the radius times the product of
the squares of its first `k` successive logarithms. The maximum with one gives a nonnegative
total extension outside that small-radius range. These gauge properties do not establish
Hausdorff nullity of a suitable weak solution's singular set.
-/

@[expose] public section

open Filter Finset
open scoped ENNReal Topology

noncomputable section

namespace FluidSingularSets



@[simp] theorem logIterate_zero (x : ℝ) : logIterate 0 x = x := rfl

@[simp] theorem logIterate_succ (n : ℕ) (x : ℝ) :
    logIterate (n + 1) x = Real.log (logIterate n x) := rfl

@[simp] theorem iteratedLogGauge_zero (k : ℕ) : iteratedLogGauge k 0 = 0 := by
  simp [iteratedLogGauge]

@[simp] theorem iteratedLogGauge_top (k : ℕ) : iteratedLogGauge k ∞ = ∞ := by
  simp [iteratedLogGauge]

@[simp] theorem iteratedLogGauge_zero_factors (d : ℝ≥0∞) :
    iteratedLogGauge 0 d = d := by
  by_cases hd : d = ∞
  · simp [hd]
  · simp [iteratedLogGauge, hd]

/-- Each extra squared factor is at least one, so increasing the number of factors
increases the total extended gauge. -/
theorem iteratedLogGauge_le_succ (k : ℕ) (d : ℝ≥0∞) :
    iteratedLogGauge k d ≤ iteratedLogGauge (k + 1) d := by
  by_cases hd : d = ∞
  · simp [hd]
  simp only [iteratedLogGauge, hd, ↓reduceIte]
  apply ENNReal.ofReal_le_ofReal
  rw [prod_range_succ]
  have hfactor : 1 ≤ (max 1 (logIterate (k + 1) (1 / d.toReal))) ^ 2 := by
    have hmax := le_max_left 1 (logIterate (k + 1) (1 / d.toReal))
    nlinarith
  have hproduct : 0 ≤ ∏ i ∈ range k,
      (max 1 (logIterate (i + 1) (1 / d.toReal))) ^ 2 :=
    prod_nonneg fun i _ ↦ sq_nonneg _
  have hproduct_le := mul_le_mul_of_nonneg_left hfactor hproduct
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hproduct_le (ENNReal.toReal_nonneg (a := d))

/-- The finite logarithmic gauge family is monotone in its number of factors. -/
theorem iteratedLogGauge_monotone (d : ℝ≥0∞) : Monotone (fun k ↦ iteratedLogGauge k d) :=
  monotone_nat_of_le_succ fun k ↦ iteratedLogGauge_le_succ k d

/-- Every finite family dominates the linear gauge. -/
theorem le_iteratedLogGauge (k : ℕ) (d : ℝ≥0∞) : d ≤ iteratedLogGauge k d := by
  simpa using iteratedLogGauge_monotone d (Nat.zero_le k)

/-- With no logarithmic factors the family is ordinary one-dimensional Hausdorff
measure in the parabolic metric. -/
theorem iteratedLogHausdorffMeasure_zero_eq (E : Set SpaceTime) :
    iteratedLogHausdorffMeasure 0 E =
      (MeasureTheory.Measure.hausdorffMeasure 1 :
        MeasureTheory.Measure ParabolicSpaceTime) (toParabolic '' E) := by
  have hzero : iteratedLogGauge 0 = fun d : ℝ≥0∞ ↦ d :=
    funext iteratedLogGauge_zero_factors
  simp [iteratedLogHausdorffMeasure, MeasureTheory.Measure.hausdorffMeasure, hzero]

/-- Increasing the finite number of factors increases the corresponding Hausdorff measure. -/
theorem iteratedLogHausdorffMeasure_monotone (E : Set SpaceTime) :
    Monotone (fun k ↦ iteratedLogHausdorffMeasure k E) := by
  intro k l hkl
  exact MeasureTheory.Measure.mkMetric_mono
    (Eventually.of_forall fun d ↦ iteratedLogGauge_monotone d hkl) (toParabolic '' E)

/-- One logarithmic factor agrees with the original logarithmic square gauge throughout
its small-radius range, including diameter zero. -/
theorem iteratedLogGauge_one_of_small {d : ℝ≥0∞} (hd : d ≠ ∞)
    (hsmall : d.toReal ≤ Real.exp (-2)) : iteratedLogGauge 1 d = logSquaredGauge d := by
  rw [logSquaredGauge_of_small hd hsmall]
  by_cases hzero : d.toReal = 0
  · simp [iteratedLogGauge, hd, hzero]
  have hpos : 0 < d.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
  have hlog : Real.log d.toReal ≤ -2 := by
    simpa using Real.log_le_log hpos hsmall
  have hlarge : 1 ≤ Real.log (1 / d.toReal) := by
    rw [one_div, Real.log_inv]
    linarith
  simp only [iteratedLogGauge, hd, ↓reduceIte, prod_range_one]
  change ENNReal.ofReal (d.toReal * (max 1 (Real.log (1 / d.toReal))) ^ 2) = _
  rw [max_eq_right hlarge]

/-- The one-factor extension and the original gauge agree near diameter zero. -/
theorem eventually_iteratedLogGauge_one_eq :
    iteratedLogGauge 1 =ᶠ[𝓝 (0 : ℝ≥0∞)] logSquaredGauge := by
  have hreal : Tendsto ENNReal.toReal (𝓝 (0 : ℝ≥0∞)) (𝓝 (0 : ℝ)) := by
    simpa using ENNReal.tendsto_toReal ENNReal.zero_ne_top
  filter_upwards [eventually_ne_nhds ENNReal.zero_ne_top,
    hreal.eventually (eventually_lt_nhds (Real.exp_pos (-2)))] with d hd hsmall
  exact iteratedLogGauge_one_of_small hd hsmall.le

/-- Changing the harmless large-radius extension does not change the Hausdorff measure.
The one-factor member therefore equals the original logarithmic square Hausdorff measure. -/
theorem iteratedLogHausdorffMeasure_one_eq (E : Set SpaceTime) :
    iteratedLogHausdorffMeasure 1 E = logSquaredHausdorffMeasure E := by
  have hle : (MeasureTheory.Measure.mkMetric (iteratedLogGauge 1) :
      MeasureTheory.Measure ParabolicSpaceTime) ≤
        MeasureTheory.Measure.mkMetric logSquaredGauge :=
    MeasureTheory.Measure.mkMetric_mono eventually_iteratedLogGauge_one_eq.le
  have hge : (MeasureTheory.Measure.mkMetric logSquaredGauge :
      MeasureTheory.Measure ParabolicSpaceTime) ≤
        MeasureTheory.Measure.mkMetric (iteratedLogGauge 1) :=
    MeasureTheory.Measure.mkMetric_mono eventually_iteratedLogGauge_one_eq.symm.le
  exact le_antisymm (hle (toParabolic '' E)) (hge (toParabolic '' E))

/-- Every fixed logarithmic iterate tends to infinity at infinity. -/
theorem tendsto_logIterate_atTop (n : ℕ) : Tendsto (logIterate n) atTop atTop := by
  induction n with
  | zero => exact tendsto_id
  | succ n ih => exact Real.tendsto_log_atTop.comp ih

/-- Finitely many successive logarithms are simultaneously at least one far enough out. -/
theorem eventually_logIterates_ge_one (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ i ∈ range k, 1 ≤ logIterate (i + 1) x := by
  rw [eventually_all_finset]
  intro i _
  exact (tendsto_logIterate_atTop (i + 1)).eventually (eventually_ge_atTop 1)

/-- The total extension drops out whenever all the requested logarithmic factors
are at least one. -/
theorem iteratedLogGauge_of_logIterates_ge_one (k : ℕ) {d : ℝ≥0∞} (hd : d ≠ ∞)
    (hlog : ∀ i ∈ range k, 1 ≤ logIterate (i + 1) (1 / d.toReal)) :
    iteratedLogGauge k d =
      ENNReal.ofReal (d.toReal * ∏ i ∈ range k, (logIterate (i + 1) (1 / d.toReal)) ^ 2) := by
  simp only [iteratedLogGauge, hd, ↓reduceIte]
  congr 2
  apply prod_congr rfl
  intro i hi
  rw [max_eq_right (hlog i hi)]

/-- At sufficiently small positive radii, all finitely many logarithmic factors
lie in the range where the total extension agrees with the unextended formula. -/
theorem eventually_small_logIterates (k : ℕ) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ i ∈ range k, 1 ≤ logIterate (i + 1) (1 / r) := by
  have hinv : Tendsto (fun r : ℝ ↦ 1 / r) (𝓝[>] 0) atTop := by
    simpa only [one_div] using tendsto_inv_nhdsGT_zero
  exact hinv.eventually (eventually_logIterates_ge_one k)

/-- The gauge agrees eventually with the finite product of the actual successive
logarithmic squares, without truncating any factor. -/
theorem eventually_iteratedLogGauge_eq (k : ℕ) :
    (fun r : ℝ ↦ iteratedLogGauge k (ENNReal.ofReal r)) =ᶠ[𝓝[>] 0]
      (fun r : ℝ ↦ ENNReal.ofReal
        (r * ∏ i ∈ range k, (logIterate (i + 1) (1 / r)) ^ 2)) := by
  filter_upwards [self_mem_nhdsWithin, eventually_small_logIterates k] with r hr hlogs
  have hformula := iteratedLogGauge_of_logIterates_ge_one k
    (d := ENNReal.ofReal r) ENNReal.ofReal_ne_top
    (by simpa only [ENNReal.toReal_ofReal hr.le] using hlogs)
  simpa only [ENNReal.toReal_ofReal hr.le] using hformula

/-- While the intervening logarithms stay nonnegative, every later iterate is
at most the first logarithm. -/
theorem logIterate_le_first {x : ℝ} (n : ℕ)
    (hlog : ∀ i ≤ n, 0 ≤ logIterate (i + 1) x) :
    logIterate (n + 1) x ≤ Real.log x := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      logIterate (n + 1 + 1) x ≤ logIterate (n + 1) x :=
        Real.log_le_self (hlog n (Nat.le_succ n))
      _ ≤ Real.log x := ih (fun i hi ↦ hlog i (hi.trans (Nat.le_succ n)))

/-- A finite product of successive logarithmic squares grows slower than its argument. -/
theorem tendsto_iteratedLogProduct_div (k : ℕ) :
    Tendsto (fun x : ℝ ↦ (∏ i ∈ range k, (max 1 (logIterate (i + 1) x)) ^ 2) / x)
      atTop (𝓝 0) := by
  have hnonneg : ∀ᶠ x : ℝ in atTop,
      0 ≤ (∏ i ∈ range k, (max 1 (logIterate (i + 1) x)) ^ 2) / x := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact div_nonneg (prod_nonneg fun i _ ↦ sq_nonneg _) hx
  have hfirst : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hupper : ∀ᶠ x : ℝ in atTop,
      (∏ i ∈ range k, (max 1 (logIterate (i + 1) x)) ^ 2) / x ≤
        (Real.log x) ^ (2 * k) / x := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), hfirst,
      eventually_logIterates_ge_one k] with x hx hxlog hlogs
    apply div_le_div_of_nonneg_right _ hx
    calc
      (∏ i ∈ range k, (max 1 (logIterate (i + 1) x)) ^ 2)
          ≤ ∏ i ∈ range k, (Real.log x) ^ 2 := by
        apply prod_le_prod₀ (fun i _ ↦ sq_nonneg _)
        intro i hi
        have hlater : logIterate (i + 1) x ≤ Real.log x :=
          logIterate_le_first i (fun j hj ↦
            (show (0 : ℝ) ≤ 1 by norm_num).trans
              (hlogs j (mem_range.mpr (hj.trans_lt (mem_range.mp hi)))))
        have hmax : max 1 (logIterate (i + 1) x) ≤ Real.log x := max_le hxlog hlater
        exact pow_le_pow_left₀ (by positivity) hmax 2
      _ = (Real.log x) ^ (2 * k) := by simp [pow_mul]
  apply squeeze_zero' hnonneg hupper
  simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 (2 * k) one_ne_zero

/-- Every fixed finite iterated logarithmic gauge tends to zero at small positive radii. -/
theorem tendsto_iteratedLogGauge (k : ℕ) :
    Tendsto (fun r : ℝ ↦ iteratedLogGauge k (ENNReal.ofReal r)) (𝓝[>] 0) (𝓝 0) := by
  have hinv : Tendsto (fun r : ℝ ↦ 1 / r) (𝓝[>] 0) atTop := by
    simpa only [one_div] using tendsto_inv_nhdsGT_zero
  have hreal : Tendsto (fun r : ℝ ↦
      r * ∏ i ∈ range k, (max 1 (logIterate (i + 1) (1 / r))) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    convert (tendsto_iteratedLogProduct_div k).comp hinv using 1
    ext r
    simp [div_eq_mul_inv, mul_comm]
  have hlifted := ENNReal.tendsto_ofReal hreal
  simp only [ENNReal.ofReal_zero] at hlifted
  apply hlifted.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [iteratedLogGauge, ENNReal.ofReal_ne_top, ↓reduceIte,
    ENNReal.toReal_ofReal hr.le]

end FluidSingularSets
