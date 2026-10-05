-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import CKN.Setting.Energy.AELocalEnergy
public import CKN.Setting.Energy.TimeCutoff

/-!
# Genuine scalar time energy extraction

Actual backward smooth cutoff inequalities imply the almost-every-time
energy inequality for integrable densities. The differentiation and kernel
proofs adapt the CKN local-energy development to scalar time densities, so
this tool also applies to the true projected energy inequality.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- Lebesgue differentiation holds for the literal left interval average. -/
theorem oneSidedAverage_norm_sub_real
    {Λ : ℝ → ℝ} (hΛ : LocallyIntegrable Λ volume) :
    ∀ᵐ t ∂volume, Tendsto
      (fun h : ℝ => ⨍ s in Icc (t - h) t, |Λ s - Λ t|)
      (𝓝[>] 0) (𝓝 0) := by
  have hLDT := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
    (volume : Measure ℝ) hΛ 1
  filter_upwards [hLDT] with t ht
  have hδ : Tendsto (fun h : ℝ => h / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hid : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        (tendsto_id : Tendsto id (𝓝 (0 : ℝ)) (𝓝 0)).mono_left nhdsWithin_le_nhds
      simpa only [id_eq, zero_div] using hid.div_const (2 : ℝ)
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact half_pos (by simpa only [mem_Ioi] using hh)
  have hball := ht (w := fun h : ℝ => t - h / 2)
    (δ := fun h => h / 2) hδ
    (by
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh' : 0 ≤ h / 2 := le_of_lt
        (half_pos (by simpa only [mem_Ioi] using hh))
      rw [Metric.mem_closedBall]
      simpa only [one_mul, Real.dist_eq, sub_sub_cancel, abs_of_nonneg hh'] using
        (le_refl (h / 2)))
  have heq : ∀ h : ℝ, Metric.closedBall (t - h / 2) (h / 2) = Icc (t - h) t := by
    intro h
    ext s
    rw [Metric.mem_closedBall, mem_Icc]
    constructor
    · intro hs
      have hs' := (abs_le.mp (by simpa [Real.dist_eq] using hs))
      constructor <;> linarith only [hs'.1, hs'.2]
    · rintro ⟨hs₁, hs₂⟩
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith only [hs₁, hs₂]
  have hball' := hball.congr' (Eventually.of_forall (fun h => by rw [heq h]))
  change Tendsto (fun h : ℝ => ⨍ s in Icc (t - h) t, |Λ s - Λ t|)
    (𝓝[>] 0) (𝓝 0) at hball'
  exact hball'

/-- The actual cutoff derivative recovers an integrable energy at almost every time. -/
theorem backwardTimeCutoff_weighted_limit
    {Λ : ℝ → ℝ} (hΛ : LocallyIntegrable Λ volume) :
    ∀ᵐ t ∂volume, Tendsto
      (fun h : ℝ => ∫ s, (-deriv (backwardTimeCutoff t h) s) • Λ s)
      (𝓝[>] 0) (𝓝 (Λ t)) := by
  filter_upwards [oneSidedAverage_norm_sub_real hΛ] with t ht
  apply tendsto_integral_smul_of_tendsto_average_norm_sub 16 ht
  · filter_upwards [] with h
    exact hΛ.integrableOn_isCompact isCompact_Icc
  · apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[>] 0) (𝓝 1)).congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := by simpa only [mem_Ioi] using hh
    exact (backwardTimeCutoff_kernel_integral (t := t) (h := h) hh').symm
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact backwardTimeCutoff_kernel_support (by simpa only [mem_Ioi] using hh)
  · filter_upwards [self_mem_nhdsWithin] with h hh s
    have hh' : 0 < h := by simpa only [mem_Ioi] using hh
    have hvol : volume.real (Icc (t - h) t) = h := by
      rw [measureReal_def, Real.volume_Icc]
      convert ENNReal.toReal_ofReal (le_of_lt hh') using 1
      ring_nf
    rw [hvol]
    simpa only [abs_neg] using
      (backwardTimeCutoff_abs_deriv_le (t := t) (h := h) (s := s) hh')

/-- The genuine smooth ramp converges to the indicator of the past time interval. -/
theorem backwardTimeCutoff_tendsto_indicator {t s : ℝ} :
    Tendsto (fun h : ℝ => backwardTimeCutoff t h s) (𝓝[>] 0)
      (𝓝 ((Iio t).indicator (fun _ : ℝ => (1 : ℝ)) s)) := by
  by_cases hs : s < t
  · have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < t - s :=
      (eventually_lt_nhds (sub_pos.mpr hs)).filter_mono nhdsWithin_le_nhds
    have htarget : (Iio t).indicator (fun _ : ℝ => (1 : ℝ)) s = 1 := by
      simp [hs]
    rw [htarget]
    apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[>] 0) (𝓝 1)).congr'
    filter_upwards [hsmall, self_mem_nhdsWithin] with h hsmall' hh
    have hh' : 0 < h := by simpa only [mem_Ioi] using hh
    exact (backwardTimeCutoff_eq_one_of_le (t := t) (h := h) (s := s) hh'
      (by linarith only [hsmall'])).symm
  · have hs' : t ≤ s := le_of_not_gt hs
    have htarget : (Iio t).indicator (fun _ : ℝ => (1 : ℝ)) s = 0 := by
      simp [hs]
    rw [htarget]
    apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ))
      (𝓝[>] 0) (𝓝 0)).congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (backwardTimeCutoff_eq_zero_of_ge
      (by simpa only [mem_Ioi] using hh) hs').symm

/-- True integrable time densities converge under the backward smooth cutoff. -/
theorem backwardTimeCutoff_integral_tendsto {g : ℝ → ℝ}
    (hg : Integrable g volume) (t : ℝ) :
    Tendsto (fun h : ℝ ↦ ∫ s, g s * backwardTimeCutoff t h s)
      (𝓝[>] 0) (𝓝 (∫ s in Iio t, g s)) := by
  have ht := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ)) (F := fun h s ↦ g s * backwardTimeCutoff t h s)
    (f := fun s ↦ (Iio t).indicator g s) (μ := volume) (fun s ↦ ‖g s‖)
    (Eventually.of_forall fun h ↦ hg.aestronglyMeasurable.mul
      (backwardTimeCutoff_smooth (t := t) (h := h)).continuous.aestronglyMeasurable)
    (Eventually.of_forall fun h ↦ ae_of_all _ fun s ↦ by
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (backwardTimeCutoff_nonneg (t := t) (h := h) (s := s))]
      exact mul_le_of_le_one_right (abs_nonneg _) (backwardTimeCutoff_le_one))
    hg.norm (ae_of_all _ fun s ↦ by
      have hs := (backwardTimeCutoff_tendsto_indicator (t := t) (s := s)).const_mul (g s)
      convert hs using 1
      by_cases hst : s ∈ Iio t <;> simp [hst])
  rwa [integral_indicator measurableSet_Iio] at ht

/-- Every actual backward smooth cutoff inequality yields the true time energy inequality. -/
theorem tested_backwardTimeCutoff_energy_ae {E D R : ℝ → ℝ}
    (hE : Integrable E volume) (hD : Integrable D volume) (hR : Integrable R volume)
    (hcut : ∀ t h : ℝ, 0 < h →
      (∫ s, D s * backwardTimeCutoff t h s) ≤
        (∫ s, R s * backwardTimeCutoff t h s) +
          ∫ s, E s * deriv (backwardTimeCutoff t h) s) :
    ∀ᵐ t ∂volume, E t + (∫ s in Iio t, D s) ≤ ∫ s in Iio t, R s := by
  filter_upwards [backwardTimeCutoff_weighted_limit hE.locallyIntegrable] with t ht
  have hlimE : Tendsto (fun h : ℝ ↦ ∫ s, E s * deriv (backwardTimeCutoff t h) s)
      (𝓝[>] 0) (𝓝 (-E t)) := by
    have heq (h : ℝ) : (∫ s, E s * deriv (backwardTimeCutoff t h) s) =
        -(∫ s, (-deriv (backwardTimeCutoff t h) s) • E s) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact ae_of_all _ fun s ↦ by simp only [smul_eq_mul]; ring
    exact (tendsto_congr heq).2 ht.neg
  have hlimD := backwardTimeCutoff_integral_tendsto hD t
  have hlimR := (backwardTimeCutoff_integral_tendsto hR t).add hlimE
  have hb : (∫ s in Iio t, D s) ≤ (∫ s in Iio t, R s) + -E t :=
    le_of_tendsto_of_tendsto hlimD hlimR (by
      filter_upwards [self_mem_nhdsWithin] with h hh
      exact hcut t h (by simpa only [mem_Ioi] using hh))
  linarith

/-- Nonnegative energy and dissipation give a quantitative essential supremum
from the literal tested cutoff inequalities. -/
theorem tested_backwardTimeCutoff_energy_essSup_le {E D R : ℝ → ℝ}
    (hE : Integrable E volume) (hD : Integrable D volume) (hR : Integrable R volume)
    (hEpos : ∀ᵐ t ∂volume, 0 ≤ E t) (hDpos : ∀ᵐ t ∂volume, 0 ≤ D t)
    (hcut : ∀ t h : ℝ, 0 < h →
      (∫ s, D s * backwardTimeCutoff t h s) ≤
        (∫ s, R s * backwardTimeCutoff t h s) +
          ∫ s, E s * deriv (backwardTimeCutoff t h) s) :
    eLpNorm E ⊤ volume ≤ ENNReal.ofReal (∫ s, |R s|) := by
  rw [eLpNorm_exponent_top hE.aestronglyMeasurable]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [tested_backwardTimeCutoff_energy_ae hE hD hR hcut, hEpos]
    with t ht hEt
  have hDt : 0 ≤ ∫ s in Iio t, D s := integral_nonneg_of_ae
    (ae_restrict_of_ae hDpos)
  have hRt : (∫ s in Iio t, R s) ≤ ∫ s, |R s| := by
    apply (integral_mono_ae hR.integrableOn hR.abs.integrableOn
      (ae_of_all _ fun s ↦ le_abs_self (R s))).trans
    exact setIntegral_le_integral hR.abs (ae_of_all _ fun s ↦ abs_nonneg (R s))
  rw [Real.norm_eq_abs, abs_of_nonneg hEt]
  linarith

/-- Literal product integration commutes with a bounded time multiplier. -/
theorem integral_product_mul_time
    {A : Type*} [MeasurableSpace A] {μ : Measure A} {ν : Measure ℝ}
    [SFinite μ] [SFinite ν] {F : A × ℝ → ℝ} {χ : ℝ → ℝ}
    (hF : Integrable F (μ.prod ν)) (hχ : AEStronglyMeasurable χ ν)
    {C : ℝ} (hb : ∀ᵐ t ∂ν, ‖χ t‖ ≤ C) :
    (∫ z : A × ℝ, F z * χ z.2 ∂μ.prod ν) =
      ∫ t, (∫ x, F (x, t) ∂μ) * χ t ∂ν := by
  have hm : AEStronglyMeasurable (fun z : A × ℝ ↦ χ z.2) (μ.prod ν) :=
    hχ.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hb' : ∀ᵐ z : A × ℝ ∂μ.prod ν, ‖χ z.2‖ ≤ C :=
    Measure.quasiMeasurePreserving_snd.ae hb
  have hi := hF.mul_bdd hm hb'
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun t ↦ by
    change (∫ x, F (x, t) * χ t ∂μ) = (∫ x, F (x, t) ∂μ) * χ t
    exact integral_mul_const (χ t) (fun x ↦ F (x, t))

/-- Actual product cutoff inequalities on a measurable interval give the
true energy inequality after zero extension of the genuine spatial integrals. -/
theorem tested_backwardTimeCutoff_product_energy_ae
    {A : Type*} [MeasurableSpace A] {μ : Measure A} [SFinite μ]
    {J : Set ℝ} (hJ : MeasurableSet J) {E D R : A × ℝ → ℝ}
    (hE : Integrable E (μ.prod (volume.restrict J)))
    (hD : Integrable D (μ.prod (volume.restrict J)))
    (hR : Integrable R (μ.prod (volume.restrict J)))
    (hcut : ∀ t h : ℝ, 0 < h →
      (∫ z, D z * backwardTimeCutoff t h z.2 ∂μ.prod (volume.restrict J)) ≤
        (∫ z, R z * backwardTimeCutoff t h z.2 ∂μ.prod (volume.restrict J)) +
          ∫ z, E z * deriv (backwardTimeCutoff t h) z.2
            ∂μ.prod (volume.restrict J)) :
    ∀ᵐ t ∂volume,
      J.indicator (fun s ↦ ∫ x, E (x, s) ∂μ) t +
        (∫ s in Iio t, J.indicator (fun s ↦ ∫ x, D (x, s) ∂μ) s) ≤
          ∫ s in Iio t, J.indicator (fun s ↦ ∫ x, R (x, s) ∂μ) s := by
  have hEi := (integrable_indicator_iff hJ).mpr hE.integral_prod_right
  have hDi := (integrable_indicator_iff hJ).mpr hD.integral_prod_right
  have hRi := (integrable_indicator_iff hJ).mpr hR.integral_prod_right
  apply tested_backwardTimeCutoff_energy_ae hEi hDi hRi
  intro t h hh
  have hx {F : A × ℝ → ℝ} (hF : Integrable F (μ.prod (volume.restrict J)))
      {χ : ℝ → ℝ} (hχ : AEStronglyMeasurable χ (volume.restrict J))
      {C : ℝ} (hb : ∀ᵐ s ∂volume.restrict J, ‖χ s‖ ≤ C) :
      (∫ s, J.indicator (fun s ↦ ∫ x, F (x, s) ∂μ) s * χ s) =
        ∫ z, F z * χ z.2 ∂μ.prod (volume.restrict J) := by
    rw [integral_product_mul_time hF hχ hb]
    rw [← integral_indicator hJ]
    apply integral_congr_ae
    exact ae_of_all _ fun s ↦ by
      by_cases hs : s ∈ J <;> simp [hs]
  have hbχ : ∀ᵐ s ∂volume.restrict J, ‖backwardTimeCutoff t h s‖ ≤ 1 :=
    ae_of_all _ fun s ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg backwardTimeCutoff_nonneg]
      exact backwardTimeCutoff_le_one
  have hbχ' : ∀ᵐ s ∂volume.restrict J,
      ‖deriv (backwardTimeCutoff t h) s‖ ≤ 16 / h :=
    ae_of_all _ fun s ↦ by
      simpa only [Real.norm_eq_abs] using backwardTimeCutoff_abs_deriv_le hh
  rw [hx hD backwardTimeCutoff_smooth.continuous.aestronglyMeasurable hbχ,
    hx hR backwardTimeCutoff_smooth.continuous.aestronglyMeasurable hbχ,
    hx hE (backwardTimeCutoff_smooth.continuous_deriv (by simp)).aestronglyMeasurable hbχ']
  exact hcut t h hh

end FluidSingularSets
