module

public import FluidSingularSets.IteratedScaling
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Regularity of the finite logarithmic gauges

With `s = log(1/r)`, the logarithm of the gauge is
`-s + 2 * sum (logIterate (i+1) s)`. Its derivative is eventually negative, which
gives the small-radius monotonicity required by the gauge measure construction.
-/

@[expose] public section

open Finset Filter Set
open scoped ENNReal Topology

noncomputable section

namespace FluidSingularSets

/-- The derivative of an iterated logarithm is the corresponding reciprocal product. -/
theorem hasDerivAt_logIterate (n : ℕ) {x : ℝ}
    (hne : ∀ i ≤ n, logIterate i x ≠ 0) :
    HasDerivAt (logIterate (n + 1)) (reciprocalLogWeight n x) x := by
  induction n with
  | zero =>
    change HasDerivAt Real.log x⁻¹ x
    simpa only [id_eq, one_div]
      using (hasDerivAt_id x).log (hne 0 le_rfl)
  | succ n ih =>
    have hD := (ih (fun i hi ↦ hne i (hi.trans (Nat.le_succ _)))).log
      (hne (n + 1) le_rfl)
    convert hD using 1
    · rfl
    · rw [reciprocalLogWeight_eq_inv_prod, reciprocalLogWeight_eq_inv_prod,
        prod_range_succ, mul_inv_rev, div_eq_mul_inv]
      ring

/-- Later reciprocal products are bounded by the ordinary reciprocal on a positive tail. -/
theorem reciprocalLogWeight_le_inv {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hlog : ∀ i ∈ range n, 1 ≤ logIterate (i + 1) x) :
    reciprocalLogWeight n x ≤ x⁻¹ := by
  rw [reciprocalLogWeight_eq_inv_prod, prod_range_succ', logIterate_zero]
  apply inv_anti₀ hx
  have hprod : 1 ≤ ∏ i ∈ range n, logIterate (i + 1) x := one_le_prod₀ hlog
  simpa only [mul_one, mul_comm] using mul_le_mul_of_nonneg_left hprod hx.le

/-- The logarithm of the gauge after setting `r = exp(-s)`. -/
def logGaugeExponent (k : ℕ) (s : ℝ) : ℝ :=
  -s + 2 * ∑ i ∈ range k, logIterate (i + 1) s

/-- The logarithmic gauge exponent has an explicit finite-sum derivative. -/
theorem hasDerivAt_logGaugeExponent (k : ℕ) {s : ℝ}
    (hne : ∀ i ≤ k, logIterate i s ≠ 0) :
    HasDerivAt (logGaugeExponent k)
      (-1 + 2 * ∑ i ∈ range k, reciprocalLogWeight i s) s := by
  have hD := HasDerivAt.fun_sum (u := range k) (fun i hi ↦
    hasDerivAt_logIterate i (fun j hj ↦ hne j (by have := mem_range.1 hi; omega)))
  exact (hasDerivAt_id s).neg.fun_add (hD.const_mul 2)

/-- A late enough tail makes the logarithmic gauge exponent antitone. -/
theorem exists_antitone_logGaugeExponent_tail (k : ℕ) :
    ∃ S : ℝ, 0 < S ∧
      (∀ s ≥ S, ∀ i ≤ k, 1 ≤ logIterate i s) ∧
      AntitoneOn (logGaugeExponent k) (Ici S) := by
  have hgood : ∀ᶠ s : ℝ in atTop,
      1 ≤ s ∧ 2 * (k : ℝ) ≤ s ∧ ∀ i ≤ k, 1 ≤ logIterate i s := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (2 * (k : ℝ)),
      eventually_logIterates_ge_one k] with s hs hk hlogs
    refine ⟨hs, hk, ?_⟩
    intro i hi
    cases i with
    | zero => exact hs
    | succ i => exact hlogs i (mem_range.2 (by omega))
  obtain ⟨S₀, hS₀⟩ := eventually_atTop.1 hgood
  let S := max S₀ 1
  have hS (s : ℝ) (hs : S ≤ s) := hS₀ s ((le_max_left _ _).trans hs)
  have hD (s : ℝ) (hs : S ≤ s) := hasDerivAt_logGaugeExponent k
    (fun i hi ↦ (zero_lt_one.trans_le ((hS s hs).2.2 i hi)).ne')
  refine ⟨S, zero_lt_one.trans_le (le_max_right _ _),
    (fun s hs ↦ (hS s hs).2.2), ?_⟩
  apply antitoneOn_of_deriv_nonpos (convex_Ici S)
  · intro s hs
    exact (hD s hs).continuousAt.continuousWithinAt
  · intro s hs
    exact (hD s (interior_subset hs)).differentiableAt.differentiableWithinAt
  · intro s hs
    have hsS : S ≤ s := interior_subset hs
    have hs0 : 0 < s := zero_lt_one.trans_le (hS s hsS).1
    rw [(hD s hsS).deriv]
    have hsum : (∑ i ∈ range k, reciprocalLogWeight i s) ≤ (k : ℝ) * s⁻¹ := by
      calc
        _ ≤ ∑ _i ∈ range k, s⁻¹ := by
          apply sum_le_sum
          intro i hi
          apply reciprocalLogWeight_le_inv hs0
          intro j hj
          exact (hS s hsS).2.2 (j + 1) (by
            have := mem_range.1 hi
            have := mem_range.1 hj
            omega)
        _ = _ := by simp
    have hbound : 2 * (k : ℝ) * s⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv]
      apply (div_le_iff₀ hs0).2
      simpa only [one_mul] using (hS s hsS).2.1
    linarith

/-- One logarithm cancels an exponential before the remaining iterations. -/
theorem logIterate_apply_exp (n : ℕ) (s : ℝ) :
    logIterate (n + 1) (Real.exp s) = logIterate n s := by
  induction n with
  | zero => simp
  | succ n ih => rw [logIterate_succ, ih, logIterate_succ]

/-- Exponentiating the logarithmic expression recovers the finite product. -/
theorem exp_logGaugeExponent (k : ℕ) {s : ℝ}
    (hpos : ∀ i ∈ range k, 0 < logIterate i s) :
    Real.exp (logGaugeExponent k s) =
      Real.exp (-s) * ∏ i ∈ range k, (logIterate i s) ^ 2 := by
  rw [logGaugeExponent, Real.exp_add, Finset.mul_sum, Real.exp_sum]
  congr 1
  apply prod_congr rfl
  intro i hi
  simpa only [Nat.cast_ofNat, logIterate_succ, Real.exp_log (hpos i hi)]
    using Real.exp_nat_mul (Real.log (logIterate i s)) 2

/-- The actual ENNReal gauge agrees with this expression on a late logarithmic tail. -/
theorem iteratedLogGauge_exp_neg (k : ℕ) {s : ℝ}
    (hlog : ∀ i ∈ range k, 1 ≤ logIterate i s) :
    iteratedLogGauge k (ENNReal.ofReal (Real.exp (-s))) =
      ENNReal.ofReal (Real.exp (logGaugeExponent k s)) := by
  have hinv : 1 / Real.exp (-s) = Real.exp s := by simp [Real.exp_neg]
  rw [iteratedLogGauge_of_logIterates_ge_one k ENNReal.ofReal_ne_top]
  · rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, hinv]
    simp only [logIterate_apply_exp]
    rw [exp_logGaugeExponent k (fun i hi ↦ zero_lt_one.trans_le (hlog i hi))]
  · simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le, hinv,
      logIterate_apply_exp] using hlog

/-- Every fixed finite-depth gauge is monotone on a sufficiently small radius interval. -/
theorem exists_small_radius_monotone_iteratedLogGauge (k : ℕ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      MonotoneOn (fun r : ℝ ↦ iteratedLogGauge k (ENNReal.ofReal r)) (Icc 0 r₀) := by
  obtain ⟨S, _hS, hlogs, hanti⟩ := exists_antitone_logGaugeExponent_tail k
  refine ⟨Real.exp (-S), Real.exp_pos _, ?_⟩
  have htail {r : ℝ} (hr : 0 < r) (hrS : r ≤ Real.exp (-S)) :
      S ≤ Real.log (1 / r) := by
    have := Real.log_le_log hr hrS
    rw [Real.log_exp] at this
    rw [one_div, Real.log_inv]
    linarith
  have hexp {r : ℝ} (hr : 0 < r) : Real.exp (-Real.log (1 / r)) = r := by
    simp only [one_div, Real.log_inv, neg_neg, Real.exp_log hr]
  have hformula {r : ℝ} (hr : 0 < r) (hrS : r ≤ Real.exp (-S)) :
      iteratedLogGauge k (ENNReal.ofReal r) =
        ENNReal.ofReal (Real.exp (logGaugeExponent k (Real.log (1 / r)))) := by
    have h := iteratedLogGauge_exp_neg k (s := Real.log (1 / r)) (fun i hi ↦
      hlogs _ (htail hr hrS) i (Nat.le_of_lt (mem_range.1 hi)))
    simpa only [hexp hr] using h
  intro r hr q hq hrq
  rcases eq_or_lt_of_le hr.1 with rfl | hrpos
  · simp
  have hqpos : 0 < q := hrpos.trans_le hrq
  change iteratedLogGauge k (ENNReal.ofReal r) ≤ iteratedLogGauge k (ENNReal.ofReal q)
  rw [hformula hrpos hr.2, hformula hqpos hq.2]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply hanti (htail hqpos hq.2) (htail hrpos hr.2)
  simpa only [one_div, Real.log_inv, neg_le_neg_iff]
    using Real.log_le_log hrpos hrq

/-- Iterated logarithms preserve order as long as the smaller input stays positive. -/
theorem logIterate_le_of_positive {a b : ℝ} (hab : a ≤ b) (n : ℕ)
    (hpos : ∀ i < n, 0 < logIterate i a) : logIterate n a ≤ logIterate n b := by
  induction n with
  | zero => exact hab
  | succ n ih =>
    rw [logIterate_succ, logIterate_succ]
    exact Real.log_le_log (hpos n (Nat.lt_succ_self _))
      (ih (fun i hi ↦ hpos i (hi.trans (Nat.lt_succ_self _))))

/-- On sufficiently small radii, doubling costs at most a factor of two. -/
theorem exists_small_radius_doubling_iteratedLogGauge (k : ℕ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → 2 * r ≤ r₀ →
      iteratedLogGauge k (ENNReal.ofReal (2 * r)) ≤
        2 * iteratedLogGauge k (ENNReal.ofReal r) := by
  obtain ⟨S, hS, hlogs, _hanti⟩ := exists_antitone_logGaugeExponent_tail k
  refine ⟨S⁻¹, inv_pos.2 hS, ?_⟩
  intro r hr hsmall
  have h2r : 0 < 2 * r := by positivity
  have ha : S ≤ 1 / (2 * r) := by
    rw [one_div]
    simpa only [inv_inv] using inv_anti₀ h2r hsmall
  have hab : 1 / (2 * r) ≤ 1 / r := one_div_le_one_div_of_le hr (by linarith)
  have hprod : (∏ i ∈ range k, (max 1 (logIterate (i + 1) (1 / (2 * r)))) ^ 2) ≤
      ∏ i ∈ range k, (max 1 (logIterate (i + 1) (1 / r))) ^ 2 := by
    apply Finset.prod_le_prod₀
    · intro i _hi
      positivity
    · intro i hi
      have hlog := logIterate_le_of_positive hab (i + 1) (fun j hj ↦
        zero_lt_one.trans_le (hlogs _ ha j (by have := mem_range.1 hi; omega)))
      have hmax : max 1 (logIterate (i + 1) (1 / (2 * r))) ≤
          max 1 (logIterate (i + 1) (1 / r)) := max_le_max_left _ hlog
      exact pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) hmax 2
  simp only [iteratedLogGauge, ENNReal.ofReal_ne_top, ↓reduceIte,
    ENNReal.toReal_ofReal h2r.le, ENNReal.toReal_ofReal hr.le]
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  rw [← htwo, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (2 * r) * ∏ i ∈ range k, (max 1 (logIterate (i + 1) (1 / r))) ^ 2 :=
      mul_le_mul_of_nonneg_left hprod h2r.le
    _ = _ := by ring

end FluidSingularSets
