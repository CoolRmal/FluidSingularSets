-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.TestedTimeEnergy

/-!
# Quantitative energy from actual time tests

A uniform bound on the literal tested right hand side bounds both the true
energy essential supremum and the whole dissipation integral. Signed spatial
cancellations may be performed before estimating that right hand side.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open scoped ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The real smooth backward ramp tends to one as the terminal time goes to infinity. -/
theorem backwardTimeCutoff_tendsto_one_atTop (s : ℝ) :
    Tendsto (fun t ↦ backwardTimeCutoff t 1 s) atTop (𝓝 1) := by
  apply (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1)).congr'
  filter_upwards [eventually_ge_atTop (s + 1)] with t ht
  exact (backwardTimeCutoff_eq_one_of_le (by norm_num : (0 : ℝ) < 1)
    (by linarith only [ht])).symm

/-- True integrable densities converge to their whole integral under terminal ramps. -/
theorem backwardTimeCutoff_integral_tendsto_atTop {g : ℝ → ℝ}
    (hg : Integrable g volume) :
    Tendsto (fun t ↦ ∫ s, g s * backwardTimeCutoff t 1 s) atTop (𝓝 (∫ s, g s)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun s ↦ ‖g s‖)
  · exact Eventually.of_forall fun t ↦ hg.aestronglyMeasurable.mul
      backwardTimeCutoff_smooth.continuous.aestronglyMeasurable
  · exact Eventually.of_forall fun t ↦ ae_of_all _ fun s ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg backwardTimeCutoff_nonneg]
      exact mul_le_of_le_one_right (abs_nonneg _) backwardTimeCutoff_le_one
  · exact hg.norm
  · exact ae_of_all _ fun s ↦ by
      simpa only [mul_one] using (backwardTimeCutoff_tendsto_one_atTop s).const_mul (g s)

/-- The actual tested right hand side bounds energy at almost every time. -/
theorem tested_backwardTimeCutoff_energy_ae_le
    {E D R : ℝ → ℝ} {A : ℝ}
    (hE : Integrable E volume) (hD : Integrable D volume) (hR : Integrable R volume)
    (hDpos : ∀ᵐ t ∂volume, 0 ≤ D t)
    (hcut : ∀ t h : ℝ, 0 < h →
      (∫ s, D s * backwardTimeCutoff t h s) ≤
        (∫ s, R s * backwardTimeCutoff t h s) +
          ∫ s, E s * deriv (backwardTimeCutoff t h) s)
    (hRcut : ∀ t h : ℝ, 0 < h → (∫ s, R s * backwardTimeCutoff t h s) ≤ A) :
    ∀ᵐ t ∂volume, E t ≤ A := by
  filter_upwards [tested_backwardTimeCutoff_energy_ae hE hD hR hcut] with t ht
  have hDb : 0 ≤ ∫ s in Iio t, D s :=
    integral_nonneg_of_ae (ae_restrict_of_ae hDpos)
  have hRb : (∫ s in Iio t, R s) ≤ A :=
    le_of_tendsto_of_tendsto (backwardTimeCutoff_integral_tendsto hR t)
      tendsto_const_nhds (by
        filter_upwards [self_mem_nhdsWithin] with h hh
        exact hRcut t h (by simpa only [mem_Ioi] using hh))
  linarith

/-- Nonnegative actual energy bounds the whole true dissipation integral. -/
theorem tested_backwardTimeCutoff_dissipation_le
    {E D R : ℝ → ℝ} {A : ℝ} (hD : Integrable D volume)
    (hEpos : ∀ᵐ t ∂volume, 0 ≤ E t)
    (hcut : ∀ t h : ℝ, 0 < h →
      (∫ s, D s * backwardTimeCutoff t h s) ≤
        (∫ s, R s * backwardTimeCutoff t h s) +
          ∫ s, E s * deriv (backwardTimeCutoff t h) s)
    (hRcut : ∀ t h : ℝ, 0 < h → (∫ s, R s * backwardTimeCutoff t h s) ≤ A) :
    (∫ s, D s) ≤ A := by
  apply le_of_tendsto_of_tendsto (backwardTimeCutoff_integral_tendsto_atTop hD)
    tendsto_const_nhds
  exact Eventually.of_forall fun t ↦ by
    have hEt : (∫ s, E s * deriv (backwardTimeCutoff t 1) s) ≤ 0 :=
      integral_nonpos_of_ae (hEpos.mono fun s hs ↦
        mul_nonpos_of_nonneg_of_nonpos hs
          (backwardTimeCutoff_deriv_nonpos (by norm_num : (0 : ℝ) < 1)))
    have ht := hcut t 1 (by norm_num)
    have hRt := hRcut t 1 (by norm_num)
    linarith

/-- One genuine right hand side bound gives both energy and dissipation estimates. -/
theorem tested_backwardTimeCutoff_energy_dissipation_bound
    {E D R : ℝ → ℝ} {A : ℝ}
    (hE : Integrable E volume) (hD : Integrable D volume) (hR : Integrable R volume)
    (hEpos : ∀ᵐ t ∂volume, 0 ≤ E t) (hDpos : ∀ᵐ t ∂volume, 0 ≤ D t)
    (hcut : ∀ t h : ℝ, 0 < h →
      (∫ s, D s * backwardTimeCutoff t h s) ≤
        (∫ s, R s * backwardTimeCutoff t h s) +
          ∫ s, E s * deriv (backwardTimeCutoff t h) s)
    (hRcut : ∀ t h : ℝ, 0 < h → (∫ s, R s * backwardTimeCutoff t h s) ≤ A) :
    eLpNorm E ⊤ volume ≤ ENNReal.ofReal A ∧ (∫ s, D s) ≤ A := by
  refine ⟨?_, tested_backwardTimeCutoff_dissipation_le hD hEpos hcut hRcut⟩
  rw [eLpNorm_exponent_top hE.aestronglyMeasurable]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [tested_backwardTimeCutoff_energy_ae_le hE hD hR hDpos hcut hRcut,
    hEpos] with t ht hp
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp] using ht

/-- A bounded literal product right hand side controls both actual spatial energy
and the whole spacetime dissipation. -/
theorem tested_backwardTimeCutoff_product_energy_dissipation_bound
    {K : Type*} [MeasurableSpace K] {μ : Measure K} [SFinite μ]
    {J : Set ℝ} (hJ : MeasurableSet J) {E D R : K × ℝ → ℝ} {A : ℝ}
    (hE : Integrable E (μ.prod (volume.restrict J)))
    (hD : Integrable D (μ.prod (volume.restrict J)))
    (hR : Integrable R (μ.prod (volume.restrict J)))
    (hEpos : ∀ z, 0 ≤ E z) (hDpos : ∀ z, 0 ≤ D z)
    (hcut : ∀ t h : ℝ, 0 < h →
      (∫ z, D z * backwardTimeCutoff t h z.2 ∂μ.prod (volume.restrict J)) ≤
        (∫ z, R z * backwardTimeCutoff t h z.2 ∂μ.prod (volume.restrict J)) +
          ∫ z, E z * deriv (backwardTimeCutoff t h) z.2
            ∂μ.prod (volume.restrict J))
    (hRcut : ∀ t h : ℝ, 0 < h →
      (∫ z, R z * backwardTimeCutoff t h z.2 ∂μ.prod (volume.restrict J)) ≤ A) :
    eLpNorm (J.indicator (fun t ↦ ∫ x, E (x, t) ∂μ)) ⊤ volume ≤ ENNReal.ofReal A ∧
      (∫ z, D z ∂μ.prod (volume.restrict J)) ≤ A := by
  have hEi := (integrable_indicator_iff hJ).mpr hE.integral_prod_right
  have hDi := (integrable_indicator_iff hJ).mpr hD.integral_prod_right
  have hRi := (integrable_indicator_iff hJ).mpr hR.integral_prod_right
  have hiPos {F : K × ℝ → ℝ} (hF : ∀ z, 0 ≤ F z) :
      ∀ᵐ t ∂volume, 0 ≤ J.indicator (fun t ↦ ∫ x, F (x, t) ∂μ) t :=
    ae_of_all _ fun t ↦ by
      by_cases ht : t ∈ J
      · simpa only [indicator_of_mem ht] using integral_nonneg (fun x ↦ hF (x, t))
      · simp only [indicator_of_notMem ht, le_refl]
  have hx {F : K × ℝ → ℝ} (hF : Integrable F (μ.prod (volume.restrict J)))
      {χ : ℝ → ℝ} (hχ : AEStronglyMeasurable χ (volume.restrict J))
      {C : ℝ} (hb : ∀ᵐ s ∂volume.restrict J, ‖χ s‖ ≤ C) :
      (∫ s, J.indicator (fun s ↦ ∫ x, F (x, s) ∂μ) s * χ s) =
        ∫ z, F z * χ z.2 ∂μ.prod (volume.restrict J) := by
    rw [integral_product_mul_time hF hχ hb, ← integral_indicator hJ]
    apply integral_congr_ae
    exact ae_of_all _ fun s ↦ by
      by_cases hs : s ∈ J <;> simp [hs]
  have hbχ (t h : ℝ) :
      ∀ᵐ s ∂volume.restrict J, ‖backwardTimeCutoff t h s‖ ≤ 1 :=
    ae_of_all _ fun s ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg backwardTimeCutoff_nonneg]
      exact backwardTimeCutoff_le_one
  have hbχ' (t h : ℝ) (hh : 0 < h) :
      ∀ᵐ s ∂volume.restrict J, ‖deriv (backwardTimeCutoff t h) s‖ ≤ 16 / h :=
    ae_of_all _ fun s ↦ by
      simpa only [Real.norm_eq_abs] using backwardTimeCutoff_abs_deriv_le hh
  obtain ⟨hEbound, hDbound⟩ := tested_backwardTimeCutoff_energy_dissipation_bound
    hEi hDi hRi (hiPos hEpos) (hiPos hDpos) (fun t h hh ↦ by
      rw [hx hD backwardTimeCutoff_smooth.continuous.aestronglyMeasurable (hbχ t h),
        hx hR backwardTimeCutoff_smooth.continuous.aestronglyMeasurable (hbχ t h),
        hx hE (backwardTimeCutoff_smooth.continuous_deriv (by simp)).aestronglyMeasurable
          (hbχ' t h hh)]
      exact hcut t h hh) (fun t h hh ↦ by
      rw [hx hR backwardTimeCutoff_smooth.continuous.aestronglyMeasurable (hbχ t h)]
      exact hRcut t h hh)
  refine ⟨hEbound, ?_⟩
  rw [integral_indicator hJ, ← integral_prod_symm _ hD] at hDbound
  exact hDbound

end FluidSingularSets
