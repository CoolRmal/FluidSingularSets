-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.CriticalSobolev
public import CKN.Foundation.Sobolev.Poincare.Lp
public import CKN.Foundation.Sobolev.Inequalities.SeeleyPoincare
public import CKN.Foundation.Sobolev.Inequalities.SeeleyScaling
public import CKN.Foundation.Sobolev.Cutoff.BallTopology
public import CKN.Foundation.Sobolev.WeakGradientGluingTPressureMean

/-!
# Mean subtraction for the mixed-gradient Sobolev exponent

Convergence in the critical gradient exponent preserves spatial averages on finite
measure sets. The smooth convex-domain Poincaré theorem can therefore be passed to
weak representatives using the general-exponent mollifier approximation.

The cutoff and mollifier arguments adapt the proofs by Scott Armstrong and Vlad Vicol
in the CKN library, distributed under the Apache 2.0 license.
-/

@[expose] public section

open MeasureTheory Set Filter CKN
open scoped ENNReal NNReal Convolution Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

private theorem criticalExponent_one_le : (1 : ℝ≥0∞) ≤ 12 / 7 := by
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  norm_num

section Convergence

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
  {μ : Measure α} {p : ℝ≥0∞} {f : α → F} {g : ℕ → α → F}

/-- Convergence of representatives in `L^p` implies convergence of their extended norms. -/
theorem tendsto_eLpNorm_of_sub (hp : 1 ≤ p) (hf : MemLp f p μ)
    (hg : ∀ n, MemLp (g n) p μ)
    (hconv : Tendsto (fun n ↦ eLpNorm (g n - f) p μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (g n) p μ) atTop (𝓝 (eLpNorm f p μ)) := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg f hf).2 hconv
  simpa only [Function.comp_def, Lp.enorm_toLp] using
    continuous_enorm.continuousAt.tendsto.comp hLp

end Convergence

section MeanConvergence

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {f : α → ℝ} {g : ℕ → α → ℝ}

/-- On a finite measure space, critical-exponent convergence implies `L¹` convergence. -/
theorem tendsto_eLpNorm_one_of_critical_sub
    (hf : MemLp f (12 / 7) μ) (hg : ∀ n, MemLp (g n) (12 / 7) μ)
    (hconv : Tendsto (fun n ↦ eLpNorm (g n - f) (12 / 7) μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (g n - f) 1 μ) atTop (𝓝 0) := by
  have hbound (n : ℕ) : eLpNorm (g n - f) 1 μ ≤
      eLpNorm (g n - f) (12 / 7) μ * μ univ ^ (5 / 12 : ℝ) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ criticalExponent_one_le
      ((hg n).sub hf).aestronglyMeasurable
    norm_num at h
    exact h
  have hfactor : μ univ ^ (5 / 12 : ℝ) ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top μ univ)).ne
  have hzero := ENNReal.Tendsto.mul_const hconv (Or.inr hfactor)
  simp only [zero_mul] at hzero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
    (Eventually.of_forall fun _ ↦ zero_le) (Eventually.of_forall hbound)

/-- Critical-exponent convergence preserves the integral and hence spatial averages. -/
theorem tendsto_average_of_critical_sub
    (hf : MemLp f (12 / 7) μ) (hg : ∀ n, MemLp (g n) (12 / 7) μ)
    (hconv : Tendsto (fun n ↦ eLpNorm (g n - f) (12 / 7) μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ average μ (g n)) atTop (𝓝 (average μ f)) := by
  have hInt := tendsto_integral_of_L1' f
    (Eventually.of_forall fun n ↦ (hg n).integrable criticalExponent_one_le)
    (tendsto_eLpNorm_one_of_critical_sub hf hg hconv)
  simpa only [average_eq, smul_eq_mul, measureReal_def] using
    hInt.const_mul (μ univ).toReal⁻¹

/-- Mean-subtracted representatives converge in the critical exponent as well. -/
theorem tendsto_centered_eLpNorm_of_critical_sub
    (hf : MemLp f (12 / 7) μ) (hg : ∀ n, MemLp (g n) (12 / 7) μ)
    (hconv : Tendsto (fun n ↦ eLpNorm (g n - f) (12 / 7) μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun x ↦ g n x - average μ (g n)) (12 / 7) μ)
      atTop (𝓝 (eLpNorm (fun x ↦ f x - average μ f) (12 / 7) μ)) := by
  have havg := tendsto_average_of_critical_sub hf hg hconv
  have hdiff : Tendsto (fun n ↦ average μ f - average μ (g n)) atTop (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds (x := average μ f)).sub havg
  have henorm : Tendsto (fun n ↦ ‖average μ f - average μ (g n)‖ₑ) atTop (𝓝 0) := by
    simpa only [enorm_zero, Function.comp_def] using
      continuous_enorm.continuousAt.tendsto.comp hdiff
  have hfactor : μ univ ^ (7 / 12 : ℝ) ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top μ univ)).ne
  have hconst : Tendsto (fun n ↦
      eLpNorm (fun _ : α ↦ average μ f - average μ (g n)) (12 / 7) μ) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.mul_const henorm (Or.inr hfactor)
    simp only [zero_mul] at h
    simp_rw [eLpNorm_const' _ (by norm_num : (12 / 7 : ℝ≥0∞) ≠ 0)
      (by finiteness : (12 / 7 : ℝ≥0∞) ≠ ∞)]
    norm_num
    exact h
  have hbound (n : ℕ) :
      eLpNorm ((fun x ↦ g n x - average μ (g n)) - (fun x ↦ f x - average μ f))
        (12 / 7) μ ≤ eLpNorm (g n - f) (12 / 7) μ +
          eLpNorm (fun _ : α ↦ average μ f - average μ (g n)) (12 / 7) μ := by
    convert eLpNorm_add_le (p := (12 / 7 : ℝ≥0∞)) criticalExponent_one_le
      (f := g n - f) (g := fun _ : α ↦ average μ f - average μ (g n)) using 1
    congr 1
    funext x
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hcenterConv : Tendsto (fun n ↦
      eLpNorm ((fun x ↦ g n x - average μ (g n)) - (fun x ↦ f x - average μ f))
        (12 / 7) μ) atTop (𝓝 0) := by
    have hsum := hconv.add hconst
    simp only [zero_add] at hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ ↦ zero_le) (Eventually.of_forall hbound)
  exact tendsto_eLpNorm_of_sub criticalExponent_one_le
    (hf.sub (memLp_const _)) (fun n ↦ (hg n).sub (memLp_const _)) hcenterConv

end MeanConvergence

/-- The power of the critical extended norm is its gradient integral. -/
theorem critical_eLpNorm_pow_eq_lintegral
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {μ : Measure α} {f : α → F} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (12 / 7) μ ^ (12 / 7 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (12 / 7 : ℝ) ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral
    (p := (12 / 7 : ℝ≥0)) (by positivity) hf
  simpa [ENNReal.coe_div (by norm_num : (7 : ℝ≥0) ≠ 0)] using h

/-- Explicit finite Poincaré constant at the critical exponent for a bounded convex domain. -/
def criticalPoincarePowConstant {U : Set (Vec 3)} (hU : IsOpenBoundedConvexDomain U) :
    ℝ≥0∞ :=
  let A : ℝ := (volume U).toReal⁻¹ *
    ((2 * Classical.choose hU.isBoundedDomain) ^ 3 / 3)
  let B : ℝ := 3 * (volume (Metric.ball (0 : Vec 3) 1)).toReal *
    (4 * Classical.choose hU.isBoundedDomain)
  ENNReal.ofReal (A ^ (12 / 7 : ℝ) * B ^ (12 / 7 : ℝ) * (3 : ℝ) ^ (12 / 7 : ℝ))

/-- Smooth Poincaré at the critical exponent, expressed directly in extended norms. -/
theorem smoothCriticalPoincare
    {U : Set (Vec 3)} (hU : IsOpenBoundedConvexDomain U)
    (hvol : 0 < (volume U).toReal) {v : Vec 3 → ℝ} (hv : ContDiff ℝ 1 v) :
    eLpNorm (fun x ↦ v x - integralAverage U v) (12 / 7) (volume.restrict U) ^
        (12 / 7 : ℝ) ≤ criticalPoincarePowConstant hU *
      eLpNorm (classicalGradient v) (12 / 7) (volume.restrict U) ^ (12 / 7 : ℝ) := by
  let : IsFiniteMeasure (volume.restrict U) := hU.isFiniteMeasure_restrict_volume
  let A : ℝ := (volume U).toReal⁻¹ *
    ((2 * Classical.choose hU.isBoundedDomain) ^ 3 / 3)
  let B : ℝ := 3 * (volume (Metric.ball (0 : Vec 3) 1)).toReal *
    (4 * Classical.choose hU.isBoundedDomain)
  have hchoose : 0 < Classical.choose hU.isBoundedDomain :=
    (Classical.choose_spec hU.isBoundedDomain).1
  have hAnonneg : 0 ≤ A := by dsimp [A]; positivity
  have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
  have hcompact : IsCompact (closure U) := hU.isBoundedDomain.isBounded.isCompact_closure
  have hvint : IntegrableOn v U :=
    (hv.continuous.continuousOn.integrableOn_compact hcompact).mono_set subset_closure
  have hfdcont : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by norm_num)
  have hgradcont : Continuous (classicalGradient v) := by
    apply continuous_pi
    intro i
    simpa only [classicalGradient_apply] using
      hfdcont.clm_apply continuous_const
  have hfdPowCont : Continuous (fun x ↦ ‖fderiv ℝ v x‖ ^ (12 / 7 : ℝ)) :=
    hfdcont.norm.rpow_const (fun _ ↦ Or.inr (by norm_num))
  have hgradPowCont : Continuous (fun x ↦ ‖classicalGradient v x‖ ^ (12 / 7 : ℝ)) :=
    hgradcont.norm.rpow_const (fun _ ↦ Or.inr (by norm_num))
  have hleftPowCont : Continuous (fun x ↦ ‖v x - integralAverage U v‖ ^ (12 / 7 : ℝ)) :=
    (hv.continuous.sub continuous_const).norm.rpow_const (fun _ ↦ Or.inr (by norm_num))
  have hfdint : IntegrableOn (fun x ↦ ‖fderiv ℝ v x‖ ^ (12 / 7 : ℝ)) U :=
    (hfdPowCont.continuousOn.integrableOn_compact hcompact).mono_set subset_closure
  have hgradint : IntegrableOn (fun x ↦ ‖classicalGradient v x‖ ^ (12 / 7 : ℝ)) U :=
    (hgradPowCont.continuousOn.integrableOn_compact hcompact).mono_set subset_closure
  have hleftint : IntegrableOn (fun x ↦ ‖v x - integralAverage U v‖ ^ (12 / 7 : ℝ)) U :=
    (hleftPowCont.continuousOn.integrableOn_compact hcompact).mono_set subset_closure
  have hfdle : ∫ x in U, ‖fderiv ℝ v x‖ ^ (12 / 7 : ℝ) ≤
      (3 : ℝ) ^ (12 / 7 : ℝ) * ∫ x in U, ‖classicalGradient v x‖ ^ (12 / 7 : ℝ) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hfdint (hgradint.const_mul _)
    filter_upwards [] with x
    calc
      _ ≤ (3 * ‖classicalGradient v x‖) ^ (12 / 7 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _)
          (seeley_fderiv_norm_le_three_classicalGradient v x) (by norm_num)
      _ = _ := Real.mul_rpow (by norm_num) (norm_nonneg _)
  have hP := integral_rpow_norm_sub_integralAverage_le_bound_of_isOpenBoundedConvexDomain
    hU hvint hv (by norm_num : (1 : ℝ) < 12 / 7) hvol
  have hreal : ∫ x in U, ‖v x - integralAverage U v‖ ^ (12 / 7 : ℝ) ≤
      (A ^ (12 / 7 : ℝ) * B ^ (12 / 7 : ℝ) * (3 : ℝ) ^ (12 / 7 : ℝ)) *
        ∫ x in U, ‖classicalGradient v x‖ ^ (12 / 7 : ℝ) := by
    calc
      _ ≤ A ^ (12 / 7 : ℝ) * (B ^ (12 / 7 : ℝ) *
          ∫ x in U, ‖fderiv ℝ v x‖ ^ (12 / 7 : ℝ)) := by
        simpa [A, B] using hP
      _ ≤ A ^ (12 / 7 : ℝ) * (B ^ (12 / 7 : ℝ) *
          ((3 : ℝ) ^ (12 / 7 : ℝ) *
            ∫ x in U, ‖classicalGradient v x‖ ^ (12 / 7 : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hfdle (Real.rpow_nonneg hBnonneg _))
          (Real.rpow_nonneg hAnonneg _)
      _ = _ := by ring
  have hleftEq : ∫⁻ x in U, ‖v x - integralAverage U v‖ₑ ^ (12 / 7 : ℝ) =
      ENNReal.ofReal (∫ x in U, ‖v x - integralAverage U v‖ ^ (12 / 7 : ℝ)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hleftint
      (Eventually.of_forall fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)]
    apply lintegral_congr
    intro x
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      ofReal_norm]
  have hgradEq : ∫⁻ x in U, ‖classicalGradient v x‖ₑ ^ (12 / 7 : ℝ) =
      ENNReal.ofReal (∫ x in U, ‖classicalGradient v x‖ ^ (12 / 7 : ℝ)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgradint
      (Eventually.of_forall fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)]
    apply lintegral_congr
    intro x
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      ofReal_norm]
  have hleftMeas : AEStronglyMeasurable
      (fun x ↦ v x - integralAverage U v) (volume.restrict U) :=
    (hv.continuous.sub continuous_const).aestronglyMeasurable.restrict
  rw [critical_eLpNorm_pow_eq_lintegral hleftMeas,
    critical_eLpNorm_pow_eq_lintegral hgradcont.aestronglyMeasurable.restrict,
    hleftEq, hgradEq, criticalPoincarePowConstant]
  rw [← ENNReal.ofReal_mul (mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hAnonneg _) (Real.rpow_nonneg hBnonneg _))
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _))]
  exact ENNReal.ofReal_le_ofReal hreal

private theorem eLpNorm_pi_le_sum
    {f : Vec 3 → Vec 3} {μ : Measure (Vec 3)}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (12 / 7) μ ≤ ∑ i : Fin 3, eLpNorm (fun x => f x i) (12 / 7) μ := by
  have hpoint : ∀ x, ‖f x‖ ≤ ∑ i : Fin 3, ‖f x i‖ := by
    intro x
    rw [Pi.norm_def]
    have hsup : Finset.univ.sup (fun i => ‖f x i‖₊) ≤
        ∑ i : Fin 3, ‖f x i‖₊ := by
      apply Finset.sup_le
      intro i hi
      have hnonneg : ∀ j : Fin 3, j ∈ Finset.univ → 0 ≤ ‖f x j‖₊ := by
        intro j hj
        exact bot_le
      simpa only [Finset.sum_filter, Finset.mem_univ, ite_true] using
        (Finset.single_le_sum hnonneg (Finset.mem_univ i))
    exact_mod_cast hsup
  calc
    eLpNorm f (12 / 7) μ ≤ eLpNorm (fun x => ∑ i : Fin 3, ‖f x i‖) (12 / 7) μ := by
      apply eLpNorm_mono_ae hf
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg
        (fun i _ => norm_nonneg (f x i)))]
      exact hpoint x
    _ = eLpNorm (∑ i : Fin 3, (fun x => ‖f x i‖)) (12 / 7) μ := by rfl
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x => ‖f x i‖) (12 / 7) μ := by
      simpa using (eLpNorm_sum_le (p := (12 / 7 : ENNReal)) (s := Finset.univ)
        (f := fun i : Fin 3 => (fun x => ‖f x i‖)) criticalExponent_one_le)
    _ = ∑ i : Fin 3, eLpNorm (fun x => f x i) (12 / 7) μ := by
      congr 1
      funext i
      have hfi : AEStronglyMeasurable (fun x => f x i) μ := by
        simpa only [ContinuousLinearMap.proj_apply] using
          (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable hf
      rw [eLpNorm_norm _ hfi]

private theorem mollify_memLp_critical
    {f : Vec 3 → ℝ} (hf : MemLp f (12 / 7) volume) {ε : ℝ} (hε : 0 < ε) :
    MemLp (mollify f ε hε) (12 / 7) volume := by
  have hconv := young_convolution_nonneg_integral_one_of_aemeasurable
    (p := (12 / 7 : ℝ≥0∞)) criticalExponent_one_le (by finiteness)
    (mollifier_nonneg hε)
    ((mollifier_contDiff hε (n := 0)).continuous.integrable_of_hasCompactSupport
      (mollifier_hasCompactSupport hε))
    (mollifier_integral_one hε) (mollifier_contDiff hε (n := 0)).continuous.measurable
    hf.aestronglyMeasurable.aemeasurable
  rw [memLp_iff]
  simpa only [mollify] using hconv.trans_lt hf

private theorem tendsto_eLpNorm_restrict_of_sub
    {F : Type*} [NormedAddCommGroup F] {f : Vec 3 → F} {g : ℕ → Vec 3 → F}
    (U : Set (Vec 3))
    (hconv : Tendsto (fun n ↦ eLpNorm (g n - f) (12 / 7) volume) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (g n - f) (12 / 7) (volume.restrict U))
      atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hconv
    (Eventually.of_forall fun _ ↦ zero_le)
    (Eventually.of_forall fun n ↦ eLpNorm_mono_measure _ Measure.restrict_le_self)

private theorem weakCriticalPoincare_of_smooth
    {U : Set (Vec 3)} [IsFiniteMeasure (volume.restrict U)]
    {K : ℝ≥0∞} (hKtop : K ≠ ∞)
    (hSmooth : ∀ (v : Vec 3 → ℝ), ContDiff ℝ 1 v →
      eLpNorm (fun x ↦ v x - integralAverage U v) (12 / 7) (volume.restrict U) ^
        (12 / 7 : ℝ) ≤ K *
          eLpNorm (classicalGradient v) (12 / 7) (volume.restrict U) ^ (12 / 7 : ℝ))
    {u : Vec 3 → ℝ} {Du : Vec 3 → Vec 3}
    (hu : MemLp u (12 / 7) volume) (hDu : MemLp Du (12 / 7) volume)
    (hweak : HasWeakGradientOn univ u Du) :
    eLpNorm (fun x ↦ u x - integralAverage U u) (12 / 7) (volume.restrict U) ^
        (12 / 7 : ℝ) ≤ K *
      eLpNorm Du (12 / 7) (volume.restrict U) ^ (12 / 7 : ℝ) := by
  have hDu_i (i : Fin 3) : MemLp (fun x ↦ Du x i) (12 / 7) volume :=
    (memLp_pi_iff).1 hDu i
  let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := by intro n; dsimp [ε]; positivity
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let v : ℕ → Vec 3 → ℝ := fun n ↦ mollify u (ε n) (hεpos n)
  let D : ℕ → Vec 3 → Vec 3 := fun n ↦ classicalGradient (v n)
  have hvMem (n : ℕ) : MemLp (v n) (12 / 7) volume := mollify_memLp_critical hu (hεpos n)
  have hvCont (n : ℕ) : ContDiff ℝ 1 (v n) :=
    mollify_contDiff (hεpos n) (hu.locallyIntegrable criticalExponent_one_le)
  have huApprox := tendsto_eLpNorm_sub_zero_mollify
    criticalExponent_one_le (by finiteness) hu hε hεpos
  have hDuApprox (i : Fin 3) := tendsto_eLpNorm_sub_zero_mollify
    criticalExponent_one_le (by finiteness) (hDu_i i) hε hεpos
  have hD_i (n : ℕ) (i : Fin 3) :
      (fun x ↦ D n x i) = mollify (fun x ↦ Du x i) (ε n) (hεpos n) := by
    funext x
    exact fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn isOpen_univ
      (hu.locallyIntegrable criticalExponent_one_le)
      ((hDu_i i).locallyIntegrable criticalExponent_one_le)
      (hweak i) (hεpos n) (by simp)
  have hDmem (n : ℕ) : MemLp (D n) (12 / 7) volume := by
    apply (memLp_pi_iff).2
    intro i
    rw [hD_i]
    exact mollify_memLp_critical (hDu_i i) (hεpos n)
  have hDerr : Tendsto (fun n ↦ eLpNorm (D n - Du) (12 / 7) volume) atTop (𝓝 0) := by
    have hbound (n : ℕ) : eLpNorm (D n - Du) (12 / 7) volume ≤
        ∑ i : Fin 3, eLpNorm
          (fun x ↦ mollify (fun y ↦ Du y i) (ε n) (hεpos n) x - Du x i)
            (12 / 7) volume := by
      have hmeas := ((hDmem n).sub hDu).aestronglyMeasurable
      calc
        _ ≤ ∑ i : Fin 3, eLpNorm (fun x ↦ (D n - Du) x i) (12 / 7) volume :=
          eLpNorm_pi_le_sum hmeas
        _ = _ := by
          congr 1
          funext i
          congr 1
          funext x
          simp only [Pi.sub_apply]
          exact congrArg (fun a ↦ a - Du x i) (congrFun (hD_i n i) x)
    have hsum : Tendsto (fun n ↦ ∑ i : Fin 3, eLpNorm
        (fun x ↦ mollify (fun y ↦ Du y i) (ε n) (hεpos n) x - Du x i)
          (12 / 7) volume) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ (fun i _ ↦ hDuApprox i)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ ↦ zero_le) (Eventually.of_forall hbound)
  have hcenter : Tendsto (fun n ↦
      eLpNorm (fun x ↦ v n x - integralAverage U (v n)) (12 / 7) (volume.restrict U))
        atTop (𝓝 (eLpNorm (fun x ↦ u x - integralAverage U u) (12 / 7)
          (volume.restrict U))) := by
    simpa only [integralAverage] using tendsto_centered_eLpNorm_of_critical_sub
      (hu.mono_measure Measure.restrict_le_self)
      (fun n ↦ (hvMem n).mono_measure Measure.restrict_le_self)
      (tendsto_eLpNorm_restrict_of_sub U huApprox)
  have hgrad : Tendsto (fun n ↦ eLpNorm (D n) (12 / 7) (volume.restrict U))
      atTop (𝓝 (eLpNorm Du (12 / 7) (volume.restrict U))) :=
    tendsto_eLpNorm_of_sub criticalExponent_one_le
      (hDu.mono_measure Measure.restrict_le_self)
      (fun n ↦ (hDmem n).mono_measure Measure.restrict_le_self)
      (tendsto_eLpNorm_restrict_of_sub U hDerr)
  have hpow : Continuous (fun a : ℝ≥0∞ ↦ a ^ (12 / 7 : ℝ)) :=
    ENNReal.continuous_rpow_const
  have hleft := hpow.continuousAt.tendsto.comp hcenter
  have hgradPow := hpow.continuousAt.tendsto.comp hgrad
  have hright := ENNReal.Tendsto.const_mul hgradPow (Or.inr hKtop)
  exact le_of_tendsto_of_tendsto' hleft hright (fun n ↦ hSmooth (v n) (hvCont n))

/-- Poincaré for a global representative with a genuine weak gradient, obtained
by mollifying both fields and passing the smooth inequality to the limit. -/
theorem weakCriticalPoincare_global
    {U : Set (Vec 3)} (hU : IsOpenBoundedConvexDomain U)
    (hvol : 0 < (volume U).toReal) {u : Vec 3 → ℝ} {Du : Vec 3 → Vec 3}
    (hu : MemLp u (12 / 7) volume) (hDu : MemLp Du (12 / 7) volume)
    (hweak : HasWeakGradientOn univ u Du) :
    eLpNorm (fun x ↦ u x - integralAverage U u) (12 / 7) (volume.restrict U) ^
        (12 / 7 : ℝ) ≤ criticalPoincarePowConstant hU *
      eLpNorm Du (12 / 7) (volume.restrict U) ^ (12 / 7 : ℝ) := by
  let : IsFiniteMeasure (volume.restrict U) := hU.isFiniteMeasure_restrict_volume
  apply weakCriticalPoincare_of_smooth (by
    unfold criticalPoincarePowConstant
    exact ENNReal.ofReal_ne_top) (fun v hv ↦ smoothCriticalPoincare hU hvol hv) hu hDu hweak

/-- Fixed finite power constant, taken from the unit Euclidean ball. -/
def criticalBallPoincarePowConstant : ℝ≥0∞ :=
  criticalPoincarePowConstant seeleyUnitEuclideanBall_domain

/-- The smooth critical Poincaré estimate has a scale-uniform ball constant. -/
theorem smoothCriticalPoincare_ball
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r) {v : Vec 3 → ℝ} (hv : ContDiff ℝ 1 v) :
    eLpNorm (fun x ↦ v x - integralAverage (euclideanBall x₀ r) v) (12 / 7)
        (volume.restrict (euclideanBall x₀ r)) ^ (12 / 7 : ℝ) ≤
      criticalBallPoincarePowConstant * ENNReal.ofReal r ^ (12 / 7 : ℝ) *
        eLpNorm (classicalGradient v) (12 / 7)
          (volume.restrict (euclideanBall x₀ r)) ^ (12 / 7 : ℝ) := by
  let B := euclideanBall x₀ r
  let U := euclideanBall (0 : Vec 3) 1
  let w := v ∘ seeleyAffineMap x₀ r
  let L := ENNReal.ofReal (r⁻¹ ^ 3) ^ (7 / 12 : ℝ)
  have hw : ContDiff ℝ 1 w :=
    hv.comp (contDiff_const.add (contDiff_id.const_smul r))
  have hvol : 0 < (volume U).toReal := ENNReal.toReal_pos
    (volume_euclideanBall_pos (0 : Vec 3) (by norm_num)).ne'
    (volume_euclideanBall_lt_top (0 : Vec 3) (by norm_num)).ne
  have hP := smoothCriticalPoincare seeleyUnitEuclideanBall_domain hvol hw
  have hleft : eLpNorm (fun x ↦ w x - integralAverage U w) (12 / 7) (volume.restrict U) =
      L * eLpNorm (fun x ↦ v x - integralAverage B v) (12 / 7) (volume.restrict B) := by
    have hmean : integralAverage U w = integralAverage B v :=
      seeleyAffine_average (x₀ := x₀) hr hv.continuous
    have hnorm := seeleyAffine_eLpNorm_comp (x₀ := x₀) hr
      (hv.continuous.sub (continuous_const (y := integralAverage B v))) (12 / 7)
    rw [hmean]
    simpa [w, L, U, B, Function.comp_def, Pi.sub_def] using hnorm
  have hgradCont : Continuous (classicalGradient v) := by
    apply continuous_pi
    intro i
    simpa only [classicalGradient_apply] using
      (hv.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hgrad : eLpNorm (classicalGradient w) (12 / 7) (volume.restrict U) =
      ENNReal.ofReal r * (L * eLpNorm (classicalGradient v) (12 / 7)
        (volume.restrict B)) := by
    have hfun : classicalGradient w = r • (classicalGradient v ∘ seeleyAffineMap x₀ r) := by
      funext x
      exact seeleyAffine_classicalGradient hv x
    rw [hfun, eLpNorm_const_smul]
    have hnorm := seeleyAffine_eLpNorm_comp (x₀ := x₀) hr hgradCont (12 / 7)
    simpa [L, U, B, Real.enorm_eq_ofReal hr.le] using
      congrArg (fun a ↦ ENNReal.ofReal r * a) hnorm
  change eLpNorm (fun x ↦ w x - integralAverage U w) (12 / 7) (volume.restrict U) ^
    (12 / 7 : ℝ) ≤ criticalBallPoincarePowConstant *
      eLpNorm (classicalGradient w) (12 / 7) (volume.restrict U) ^ (12 / 7 : ℝ) at hP
  rw [hleft, hgrad] at hP
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 12 / 7)] at hP
  have hLzero : L ^ (12 / 7 : ℝ) ≠ 0 := by dsimp [L]; positivity
  have hLtop : L ^ (12 / 7 : ℝ) ≠ ∞ := by dsimp [L]; finiteness
  apply (ENNReal.mul_le_mul_iff_left hLzero hLtop).1
  convert hP using 1 <;> ac_rfl

/-- A global weak representative obeys the scale-uniform Poincaré estimate on every ball. -/
theorem weakCriticalPoincare_ball_global
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r) {u : Vec 3 → ℝ} {Du : Vec 3 → Vec 3}
    (hu : MemLp u (12 / 7) volume) (hDu : MemLp Du (12 / 7) volume)
    (hweak : HasWeakGradientOn univ u Du) :
    eLpNorm (fun x ↦ u x - integralAverage (euclideanBall x₀ r) u) (12 / 7)
        (volume.restrict (euclideanBall x₀ r)) ^ (12 / 7 : ℝ) ≤
      criticalBallPoincarePowConstant * ENNReal.ofReal r ^ (12 / 7 : ℝ) *
        eLpNorm Du (12 / 7) (volume.restrict (euclideanBall x₀ r)) ^ (12 / 7 : ℝ) := by
  let : IsFiniteMeasure (volume.restrict (euclideanBall x₀ r)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact volume_euclideanBall_lt_top x₀ hr
  apply weakCriticalPoincare_of_smooth (by
    unfold criticalBallPoincarePowConstant criticalPoincarePowConstant
    finiteness) (fun v hv ↦ smoothCriticalPoincare_ball hr hv) hu hDu hweak

private theorem memLp_mul_cutoff_le
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    {p : ENNReal} {f : Vec d → ℝ} (hf : MemLp f p (volume.restrict U))
    {η : Vec d → ℝ} (hηMeas : Measurable η) (hηU : tsupport η ⊆ U)
    {c : ℝ} (hη : ∀ x, ‖η x‖ ≤ c) :
    MemLp (fun x => η x * f x) p volume := by
  have hmeas : AEStronglyMeasurable (fun x => η x * f x) (volume.restrict U) := by
    exact (hηMeas.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  have hmul : MemLp (fun x => η x * f x) p (volume.restrict U) := by
    apply MemLp.of_le_mul hf hmeas
    filter_upwards [] with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hη x) (norm_nonneg (f x))
  have hglob : MemLp (U.indicator (fun x => η x * f x)) p volume :=
    (memLp_indicator_iff_restrict hU).2 hmul
  have heq : U.indicator (fun x => η x * f x) = (fun x => η x * f x) := by
    funext x
    by_cases hx : x ∈ U
    · simp only [Set.indicator_of_mem hx]
    · have hη0 : η x = 0 := image_eq_zero_of_notMem_tsupport (fun hxt => hx (hηU hxt))
      simp [hη0]
  rw [heq] at hglob
  exact hglob
private theorem fderiv_component_tsupport_subset
    {d : ℕ} {η : Vec d → ℝ} (i : Fin d) :
    tsupport (fun x => (fderiv ℝ η x) (basisVec i)) ⊆ tsupport η := by
  apply closure_minimal
  · intro x hx
    by_contra hxt
    have hηzero : η =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := η)).isOpen_compl.eventually_mem hxt |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    have hderivzero := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hηzero
    have hzero : (fderiv ℝ η x) (basisVec i) = 0 := by
      rw [hderivzero]
      simp
    exact hx hzero
  · exact isClosed_tsupport (f := η)

/-- A local weak representative admits a global weak cutoff extension that preserves
both fields on the inner ball. -/
theorem cutoff_critical_weak_extension
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r)
    {u : Vec 3 → ℝ} {Du : Vec 3 → Vec 3}
    (hu : MemLp u (12 / 7) (volume.restrict (euclideanBall x₀ (2 * r))))
    (hDu : MemLp Du (12 / 7) (volume.restrict (euclideanBall x₀ (2 * r))))
    (hweakInput : HasWeakGradientOn (euclideanBall x₀ (2 * r)) u Du) :
    ∃ (v : Vec 3 → ℝ) (G : Vec 3 → Vec 3),
      MemLp v (12 / 7) volume ∧ MemLp G (12 / 7) volume ∧
        HasWeakGradientOn univ v G ∧ EqOn v u (euclideanBall x₀ r) ∧
          EqOn G Du (euclideanBall x₀ r) := by
  have hDu_i (i : Fin 3) : MemLp (fun x ↦ Du x i) (12 / 7)
      (volume.restrict (euclideanBall x₀ (2 * r))) := (memLp_pi_iff).1 hDu i
  let U : Set (Vec 3) := euclideanBall x₀ (2 * r)
  let inner : Set (Vec 3) := euclideanBall x₀ r
  let η : Vec 3 → ℝ := canonicalBallCutoff x₀ r (2 * r)
  let v : Vec 3 → ℝ := fun x => η x * u x
  let G : Vec 3 → Vec 3 := fun x => η x • Du x +
    u x • classicalGradient η x
  have hUopen : IsOpen U := by
    change IsOpen {x | euclideanSqDist x x₀ < (2 * r) ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hinnerMeas : MeasurableSet inner := by
    change MeasurableSet {x | euclideanSqDist x x₀ < r ^ 2}
    exact (isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const).measurableSet
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := by
    exact canonicalBallCutoff_smooth x₀ (le_of_lt hr) (by linarith only [hr])
  have hηMeas : Measurable η := hη.continuous.measurable
  have hηSupport : HasCompactSupport η := by
    exact canonicalBallCutoff_hasCompactSupport (le_of_lt hr) (by linarith only [hr])
  have hηU : tsupport η ⊆ U := by
    exact canonicalBallCutoff_tsupport_subset_outer (le_of_lt hr) (by linarith only [hr])
  have hηBound : ∀ x, ‖η x‖ ≤ (1 : ℝ) := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (canonicalBallCutoff_nonneg x₀ r (2 * r) x)]
    exact canonicalBallCutoff_le_one x₀ r (2 * r) x
  have hgradη : ∀ x, ‖classicalGradient η x‖ ≤ 32 / r := by
    intro x
    calc
      ‖classicalGradient η x‖ ≤
          vecEuclideanNorm (classicalGradient η x) := pi_norm_le_vecEuclideanNorm _
      _ ≤ 32 / ((2 * r) - r) := canonicalBallCutoff_gradient_bound
        (le_of_lt hr) (by linarith only [hr]) x
      _ = 32 / r := by ring_nf
  have hgradηMeas (i : Fin 3) :
      Measurable (fun x => (classicalGradient η x) i) := by
    simpa only [classicalGradient_apply] using
      (hη.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.measurable
  have hgradηSupport (i : Fin 3) :
      tsupport (fun x => (classicalGradient η x) i) ⊆ U := by
    exact (fderiv_component_tsupport_subset i).trans hηU
  have hgradηBound (i : Fin 3) :
      ∀ x, ‖(classicalGradient η x) i‖ ≤ 32 / r := by
    intro x
    exact (norm_le_pi_norm (classicalGradient η x) i).trans (hgradη x)
  have huLoc : LocallyIntegrableOn u U volume := by
    exact locallyIntegrableOn_of_locallyIntegrable_restrict
      (hu.locallyIntegrable criticalExponent_one_le)
  have hgradLoc (i : Fin 3) :
      LocallyIntegrableOn (fun x => Du x i) U volume := by
    exact locallyIntegrableOn_of_locallyIntegrable_restrict
      ((hDu_i i).locallyIntegrable criticalExponent_one_le)
  have hweak : HasWeakGradientOn Set.univ v G := by
    exact HasWeakGradientOn.mul_smooth_zeroExtend hUopen huLoc hgradLoc hweakInput
      hη hηSupport hηU
  have hv : MemLp v (12 / 7) volume := by
    exact memLp_mul_cutoff_le hUmeas hu hηMeas hηU hηBound
  have hG_i (i : Fin 3) : MemLp (fun x => G x i) (12 / 7) volume := by
    have hηg : MemLp (fun x => η x * Du x i) (12 / 7) volume :=
      memLp_mul_cutoff_le hUmeas (hDu_i i) hηMeas hηU hηBound
    have hηd : MemLp (fun x => (classicalGradient η x) i * u x) (12 / 7) volume :=
      memLp_mul_cutoff_le hUmeas hu (hgradηMeas i) (hgradηSupport i) (hgradηBound i)
    convert hηg.add hηd using 1
    · ext x
      simp [G, Pi.smul_apply, smul_eq_mul, classicalGradient_apply,
        mul_comm, Pi.add_apply]
  have hG : MemLp G (12 / 7) volume := (memLp_pi_iff).2 hG_i
  have hηone (x : Vec 3) (hx : x ∈ inner) : η x = 1 :=
    canonicalBallCutoff_eq_one_on_inner hr.le (by linarith only [hr]) hx
  have hvEq : EqOn v u inner := by
    intro x hx
    simp [v, hηone x hx]
  have hGEq : EqOn G Du inner := by
    intro x hx
    have hηlocal : η =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [(isOpen_euclideanBall x₀ r).mem_nhds hx] with y hy
      exact hηone y hy
    have hfd : fderiv ℝ η x = 0 := by
      rw [hηlocal.fderiv_eq]
      simp
    have hgradzero : classicalGradient η x = 0 := by
      funext i
      rw [classicalGradient_apply, hfd]
      simp
    simp [G, hηone x hx, hgradzero]
  exact ⟨v, G, hv, hG, hweak, hvEq, hGEq⟩

/-- A local weak representative obeys Poincaré on the inner ball with an absolute,
scale-uniform constant. Its energy class is required only on the doubled ball. -/
theorem weakCriticalPoincare_ball
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r)
    {u : Vec 3 → ℝ} {Du : Vec 3 → Vec 3}
    (hu : MemLp u (12 / 7) (volume.restrict (euclideanBall x₀ (2 * r))))
    (hDu : MemLp Du (12 / 7) (volume.restrict (euclideanBall x₀ (2 * r))))
    (hweak : HasWeakGradientOn (euclideanBall x₀ (2 * r)) u Du) :
    eLpNorm (fun x ↦ u x - integralAverage (euclideanBall x₀ r) u) (12 / 7)
        (volume.restrict (euclideanBall x₀ r)) ^ (12 / 7 : ℝ) ≤
      criticalBallPoincarePowConstant * ENNReal.ofReal r ^ (12 / 7 : ℝ) *
        eLpNorm Du (12 / 7) (volume.restrict (euclideanBall x₀ r)) ^ (12 / 7 : ℝ) := by
  obtain ⟨v, G, hv, hG, hw, hvEq, hGEq⟩ := cutoff_critical_weak_extension hr hu hDu hweak
  have hvAE : v =ᵐ[volume.restrict (euclideanBall x₀ r)] u := by
    filter_upwards [ae_restrict_mem (isOpen_euclideanBall x₀ r).measurableSet] with x hx
    exact hvEq hx
  have hGAE : G =ᵐ[volume.restrict (euclideanBall x₀ r)] Du := by
    filter_upwards [ae_restrict_mem (isOpen_euclideanBall x₀ r).measurableSet] with x hx
    exact hGEq hx
  have hmean : integralAverage (euclideanBall x₀ r) v =
      integralAverage (euclideanBall x₀ r) u := average_congr hvAE
  have hcenterAE : (fun x ↦ v x - integralAverage (euclideanBall x₀ r) v) =ᵐ[
      volume.restrict (euclideanBall x₀ r)]
        (fun x ↦ u x - integralAverage (euclideanBall x₀ r) u) := by
    filter_upwards [hvAE] with x hx
    rw [hx, hmean]
  have h := weakCriticalPoincare_ball_global (x₀ := x₀) hr hv hG hw
  rw [eLpNorm_congr_ae hcenterAE, eLpNorm_congr_ae hGAE] at h
  exact h

/-- Absolute norm constant for ball Poincaré at the mixed-gradient exponent. -/
def criticalBallPoincareConstant : ℝ≥0∞ := criticalBallPoincarePowConstant ^ (7 / 12 : ℝ)

/-- The norm form of the local critical Poincaré inequality. -/
theorem weakCriticalPoincare_ball_norm
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r)
    {u : Vec 3 → ℝ} {Du : Vec 3 → Vec 3}
    (hu : MemLp u (12 / 7) (volume.restrict (euclideanBall x₀ (2 * r))))
    (hDu : MemLp Du (12 / 7) (volume.restrict (euclideanBall x₀ (2 * r))))
    (hweak : HasWeakGradientOn (euclideanBall x₀ (2 * r)) u Du) :
    eLpNorm (fun x ↦ u x - integralAverage (euclideanBall x₀ r) u) (12 / 7)
        (volume.restrict (euclideanBall x₀ r)) ≤
      criticalBallPoincareConstant * ENNReal.ofReal r *
        eLpNorm Du (12 / 7) (volume.restrict (euclideanBall x₀ r)) := by
  have h := ENNReal.rpow_le_rpow (weakCriticalPoincare_ball hr hu hDu hweak)
    (by norm_num : (0 : ℝ) ≤ 7 / 12)
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 7 / 12),
    ← ENNReal.rpow_mul] at h
  norm_num at h
  exact h

/-- An absolute critical Sobolev constant after subtracting a spatial mean. -/
def criticalSobolevPoincareConstant : ℝ≥0∞ :=
  criticalSobolevConstant * (1 + 64 * criticalBallPoincareConstant)

/-- The scale-uniform Sobolev–Poincaré coefficient is finite. -/
theorem criticalSobolevPoincareConstant_ne_top : criticalSobolevPoincareConstant ≠ ∞ := by
  unfold criticalSobolevPoincareConstant criticalSobolevConstant criticalBallPoincareConstant
    criticalBallPoincarePowConstant criticalPoincarePowConstant
  finiteness

/-- Critical Sobolev control of the mean-subtracted representative by its gradient.
The local weak energy class is required on a fourfold ball; the spatial mean and
gradient norm are evaluated on the doubled ball. All constants are independent of
the centre and radius. -/
theorem weakCriticalSobolevPoincareBall
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r)
    {u : Vec 3 → ℝ} {Du : Vec 3 → Vec 3}
    (hu : MemLp u (12 / 7) (volume.restrict (euclideanBall x₀ (4 * r))))
    (hDu : MemLp Du (12 / 7) (volume.restrict (euclideanBall x₀ (4 * r))))
    (hweak : HasWeakGradientOn (euclideanBall x₀ (4 * r)) u Du) :
    lpNormOn 4 (euclideanBall x₀ r)
        (fun x ↦ u x - integralAverage (euclideanBall x₀ (2 * r)) u) ≤
      criticalSobolevPoincareConstant *
        weakGradientLpNormOn (12 / 7) (euclideanBall x₀ (2 * r)) Du := by
  have hr2 : 0 < 2 * r := by positivity
  have hr4 : 0 < 4 * r := by positivity
  have hsub : euclideanBall x₀ (2 * r) ⊆ euclideanBall x₀ (4 * r) := by
    intro x hx
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr4]
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr2).1 hx
    linarith only [hx', hr]
  have hu2 : MemLp u (12 / 7) (volume.restrict (euclideanBall x₀ (2 * r))) :=
    hu.mono_measure (Measure.restrict_mono_set volume hsub)
  have hDu2 : MemLp Du (12 / 7) (volume.restrict (euclideanBall x₀ (2 * r))) :=
    hDu.mono_measure (Measure.restrict_mono_set volume hsub)
  have hweak2 : HasWeakGradientOn (euclideanBall x₀ (2 * r)) u Du :=
    hweak.mono (isOpen_euclideanBall x₀ (2 * r)) hsub
  let b := integralAverage (euclideanBall x₀ (2 * r)) u
  let : IsFiniteMeasure (volume.restrict (euclideanBall x₀ (2 * r))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact volume_euclideanBall_lt_top x₀ hr2
  have hub : MemLp (fun x ↦ u x - b) (12 / 7)
      (volume.restrict (euclideanBall x₀ (2 * r))) := hu2.sub (memLp_const b)
  have hweakb : HasWeakGradientOn (euclideanBall x₀ (2 * r))
      (fun x ↦ u x - b) Du := by
    intro i
    apply HasWeakPartialDerivOn.sub_const (isOpen_euclideanBall x₀ (2 * r))
    · exact locallyIntegrableOn_of_locallyIntegrable_restrict
        (hu2.locallyIntegrable criticalExponent_one_le)
    · exact locallyIntegrableOn_of_locallyIntegrable_restrict
        (((memLp_pi_iff).1 hDu2 i).locallyIntegrable criticalExponent_one_le)
    · exact hweak2 i
  have hmean : lpNormOn (12 / 7) (euclideanBall x₀ (2 * r)) (fun x ↦ u x - b) ≤
      criticalBallPoincareConstant * ENNReal.ofReal (2 * r) *
        weakGradientLpNormOn (12 / 7) (euclideanBall x₀ (2 * r)) Du := by
    apply weakCriticalPoincare_ball_norm hr2
    · simpa only [show 2 * (2 * r) = 4 * r by ring] using hu
    · simpa only [show 2 * (2 * r) = 4 * r by ring] using hDu
    · simpa only [show 2 * (2 * r) = 4 * r by ring] using hweak
  have hfactor : (Real.toNNReal (32 / r) : ℝ≥0∞) * ENNReal.ofReal (2 * r) = 64 := by
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    have hscalar : 32 / r * (2 * r) = (64 : ℝ) := by field_simp; ring
    rw [hscalar]
    norm_num
  calc
    _ ≤ criticalSobolevConstant *
        (weakGradientLpNormOn (12 / 7) (euclideanBall x₀ (2 * r)) Du +
          (Real.toNNReal (32 / r) : ℝ≥0∞) *
            lpNormOn (12 / 7) (euclideanBall x₀ (2 * r)) (fun x ↦ u x - b)) :=
      weakCriticalSobolevBall hr hub hDu2 hweakb
    _ ≤ criticalSobolevConstant *
        (weakGradientLpNormOn (12 / 7) (euclideanBall x₀ (2 * r)) Du +
          (Real.toNNReal (32 / r) : ℝ≥0∞) *
            (criticalBallPoincareConstant * ENNReal.ofReal (2 * r) *
              weakGradientLpNormOn (12 / 7) (euclideanBall x₀ (2 * r)) Du)) := by
      gcongr
    _ = _ := by
      unfold criticalSobolevPoincareConstant
      have hswap : (Real.toNNReal (32 / r) : ℝ≥0∞) *
          (criticalBallPoincareConstant * ENNReal.ofReal (2 * r)) =
          64 * criticalBallPoincareConstant := by
        rw [mul_left_comm, hfactor, mul_comm]
      simp only [← mul_assoc, hswap]
      ring

end FluidSingularSets
