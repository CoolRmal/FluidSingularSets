-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.SliceLpMoments
public import FluidSingularSets.StrongLpProducts

/-!
# Uniform bounds and actual mixed spatial classes

Uniform convergence of actual jointly measurable fields gives strong local
Lp convergence. For true spatial L² slices, the same bound gives strong
convergence of the actual class curves in time L∞. Good spatial slices of the
approximants follow from the original good slices and their bounded difference.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A true uniform difference bounds every finite-exponent local seminorm. -/
theorem eLpNorm_sub_le_uniform_bound
    {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    {μ : Measure A} {p : ℝ≥0∞} (hp : p ≠ 0) (hpfin : p ≠ ⊤)
    {f g : A → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ x ∂μ, ‖f x - g x‖ ≤ C) :
    eLpNorm (f - g) p μ ≤ ENNReal.ofReal C * μ univ ^ (1 / p.toReal) := by
  have hle : eLpNorm (f - g) p μ ≤ eLpNorm (fun _ : A ↦ C) p μ :=
    eLpNorm_mono_ae (hf.sub hg) (hbound.mono fun x hx ↦
      hx.trans_eq (Real.norm_of_nonneg hC).symm)
  exact hle.trans_eq (by rw [eLpNorm_const' C hp hpfin, Real.enorm_eq_ofReal hC])

/-- Uniformly vanishing actual differences give strong finite-exponent convergence. -/
theorem tendsto_eLpNorm_sub_of_uniform_bound
    {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    {μ : Measure A} [IsFiniteMeasure μ] {p : ℝ≥0∞} (hp : p ≠ 0) (hpfin : p ≠ ⊤)
    {f : A → E} {fs : ℕ → A → E}
    (hf : AEStronglyMeasurable f μ) (hfs : ∀ n, AEStronglyMeasurable (fs n) μ)
    {C : ℕ → ℝ} (hC : ∀ n, 0 ≤ C n) (hzero : Tendsto C atTop (𝓝 0))
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x - f x‖ ≤ C n) :
    Tendsto (fun n ↦ eLpNorm (fs n - f) p μ) atTop (𝓝 0) := by
  have hc : Tendsto (fun n ↦ ENNReal.ofReal (C n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hzero
  have hm : μ univ ^ (1 / p.toReal) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) (measure_ne_top μ univ)).ne
  have hlim := ENNReal.Tendsto.mul_const hc (Or.inr hm)
  simp only [zero_mul] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ zero_le)
    (Eventually.of_forall fun n ↦ eLpNorm_sub_le_uniform_bound hp hpfin
      (hfs n) hf (hC n) (hbound n))

/-- Uniformly vanishing measurable differences give strong essential-supremum convergence. -/
theorem tendsto_eLpNorm_top_sub_of_uniform_bound
    {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    {μ : Measure A} {f : A → E} {fs : ℕ → A → E}
    (hf : AEStronglyMeasurable f μ) (hfs : ∀ n, AEStronglyMeasurable (fs n) μ)
    {C : ℕ → ℝ} (hzero : Tendsto C atTop (𝓝 0))
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x - f x‖ ≤ C n) :
    Tendsto (fun n ↦ eLpNorm (fs n - f) ⊤ μ) atTop (𝓝 0) := by
  have hc : Tendsto (fun n ↦ ENNReal.ofReal (C n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hzero
  have hb (n : ℕ) : eLpNorm (fs n - f) ⊤ μ ≤ ENNReal.ofReal (C n) := by
    rw [eLpNorm_exponent_top ((hfs n).sub hf)]
    exact eLpNormEssSup_le_of_ae_bound (hbound n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc
    (Eventually.of_forall fun _ ↦ zero_le) (Eventually.of_forall hb)

/-- At every genuine good time, the class difference has the literal difference seminorm. -/
theorem actualSliceLp_sub_enorm
    {A T E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    {μ : Measure A} {F G : A × T → E} (t : T)
    (hF : MemLp (fun x ↦ F (x, t)) 2 μ) (hG : MemLp (fun x ↦ G (x, t)) 2 μ) :
    ‖actualSliceLp (μ := μ) (p := 2) F t - actualSliceLp (μ := μ) (p := 2) G t‖ₑ =
      eLpNorm (fun x ↦ F (x, t) - G (x, t)) 2 μ := by
  rw [Lp.enorm_def]
  apply eLpNorm_congr_ae
  exact (Lp.coeFn_sub _ _).trans ((actualSliceLp_ae F t hF).sub (actualSliceLp_ae G t hG))

/-- A true bounded spatial difference controls the norm of the genuine L² class difference. -/
theorem actualSliceLp_sub_enorm_le_uniform_bound
    {A T E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    {μ : Measure A} {F G : A × T → E} (t : T)
    (hF : MemLp (fun x ↦ F (x, t)) 2 μ) (hG : MemLp (fun x ↦ G (x, t)) 2 μ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ x ∂μ, ‖F (x, t) - G (x, t)‖ ≤ C) :
    ‖actualSliceLp (μ := μ) (p := 2) F t - actualSliceLp (μ := μ) (p := 2) G t‖ₑ ≤
      ENNReal.ofReal C * μ univ ^ (1 / 2 : ℝ) := by
  rw [actualSliceLp_sub_enorm t hF hG]
  have hb := eLpNorm_sub_le_uniform_bound (p := 2)
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    hF.aestronglyMeasurable hG.aestronglyMeasurable hC hbound
  have heq : ((fun x ↦ F (x, t)) - fun x ↦ G (x, t)) =
      fun x ↦ F (x, t) - G (x, t) := rfl
  rw [heq] at hb
  norm_num only [ENNReal.toReal_ofNat] at hb
  exact hb

/-- Joint true measurability and actual good slices give the time-uniform class-difference bound. -/
theorem actualSliceLp_sub_eLpNorm_top_le_uniform_bound
    {A T E : Type*} [MeasurableSpace A] [MeasurableSpace T]
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure A} [SFinite μ] [IsSeparable μ] {ν : Measure T} [SFinite ν]
    {F G : A × T → E}
    (hF : AEStronglyMeasurable F (μ.prod ν)) (hG : AEStronglyMeasurable G (μ.prod ν))
    (hFs : ∀ᵐ t ∂ν, MemLp (fun x ↦ F (x, t)) 2 μ)
    (hGs : ∀ᵐ t ∂ν, MemLp (fun x ↦ G (x, t)) 2 μ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, ‖F (x, t) - G (x, t)‖ ≤ C) :
    eLpNorm (actualSliceLp (μ := μ) (p := 2) F -
      actualSliceLp (μ := μ) (p := 2) G) ⊤ ν ≤
      ENNReal.ofReal C * μ univ ^ (1 / 2 : ℝ) := by
  have hFc := aestronglyMeasurable_actualSliceLp hF (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have hGc := aestronglyMeasurable_actualSliceLp hG (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  rw [eLpNorm_exponent_top (hFc.sub hGc)]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  filter_upwards [hFs, hGs, hbound] with t hft hgt hbt
  exact actualSliceLp_sub_enorm_le_uniform_bound t hft hgt hC hbt

/-- Actual original good slices and bounded measurable differences imply genuine good new slices. -/
theorem actualSlice_memLp_two_of_uniform_difference
    {A T E : Type*} [MeasurableSpace A] [MeasurableSpace T] [NormedAddCommGroup E]
    {μ : Measure A} [IsFiniteMeasure μ] {ν : Measure T} [SFinite ν]
    {F G : A × T → E} (hF : AEStronglyMeasurable F (μ.prod ν))
    (hG : AEStronglyMeasurable G (μ.prod ν))
    (hGs : ∀ᵐ t ∂ν, MemLp (fun x ↦ G (x, t)) 2 μ)
    {C : ℝ} (hbound : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, ‖F (x, t) - G (x, t)‖ ≤ C) :
    ∀ᵐ t ∂ν, MemLp (fun x ↦ F (x, t)) 2 μ := by
  filter_upwards [hF.prodMk_right, hG.prodMk_right, hGs, hbound] with t hft hgt hg hbt
  have hdiff : MemLp (fun x ↦ F (x, t) - G (x, t)) 2 μ :=
    MemLp.of_bound (hft.sub hgt) C hbt
  have hadd := hdiff.add hg
  apply hadd.congr_norm hft
  exact ae_of_all _ fun x ↦ by simp only [Pi.add_apply, sub_add_cancel]

/-- Uniform approximation gives strong time L∞ convergence of actual spatial L² classes,
including the good-slice facts derived from the original field. -/
theorem tendsto_actualSliceLp_top_sub_of_uniform_bound
    {A T E : Type*} [MeasurableSpace A] [MeasurableSpace T]
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure A} [IsFiniteMeasure μ] [IsSeparable μ] {ν : Measure T} [SFinite ν]
    {F : A × T → E} {Fs : ℕ → A × T → E}
    (hF : AEStronglyMeasurable F (μ.prod ν))
    (hFs : ∀ n, AEStronglyMeasurable (Fs n) (μ.prod ν))
    (hgood : ∀ᵐ t ∂ν, MemLp (fun x ↦ F (x, t)) 2 μ)
    {C : ℕ → ℝ} (hC : ∀ n, 0 ≤ C n) (hzero : Tendsto C atTop (𝓝 0))
    (hbound : ∀ n, ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, ‖Fs n (x, t) - F (x, t)‖ ≤ C n) :
    Tendsto (fun n ↦ eLpNorm (actualSliceLp (μ := μ) (p := 2) (Fs n) -
      actualSliceLp (μ := μ) (p := 2) F) ⊤ ν) atTop (𝓝 0) := by
  have hc : Tendsto (fun n ↦ ENNReal.ofReal (C n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hzero
  have hm : μ univ ^ (1 / 2 : ℝ) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top μ univ)).ne
  have hlim := ENNReal.Tendsto.mul_const hc (Or.inr hm)
  simp only [zero_mul] at hlim
  have hb (n : ℕ) := actualSliceLp_sub_eLpNorm_top_le_uniform_bound (hFs n) hF
    (actualSlice_memLp_two_of_uniform_difference (hFs n) hF hgood (hbound n))
    hgood (hC n) (hbound n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ zero_le) (Eventually.of_forall hb)

end FluidSingularSets
