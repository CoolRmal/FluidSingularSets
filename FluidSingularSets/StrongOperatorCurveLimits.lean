-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StrongLpProducts
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Genuine strong limits for uniformly bounded operator curves

Pointwise convergence of actual bounded linear operators implies strong L¹
convergence on every genuine Bochner-integrable curve. Uniform operator bounds
also allow the input curve to vary in strong L¹. This is the pressure-curve
limit needed for actual spatial smoothing of harmonic force approximations.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Genuine uniformly bounded operator approximations converge strongly on actual L¹ curves. -/
theorem tendsto_eLpNorm_operator_curve_one
    {A E F : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure A} {L : E →L[ℝ] F} {Ls : ℕ → E →L[ℝ] F}
    {C : ℝ} (hLs : ∀ n, ‖Ls n‖ ≤ C)
    (hpoint : ∀ x : E, Tendsto (fun n ↦ Ls n x) atTop (𝓝 (L x)))
    {g : A → E} (hg : Integrable g μ) :
    Tendsto (fun n ↦ eLpNorm (fun a ↦ Ls n (g a) - L (g a)) 1 μ)
      atTop (𝓝 0) := by
  let B : A → ℝ := fun a ↦ (C + ‖L‖) * ‖g a‖
  have hi (n : ℕ) : Integrable (fun a ↦ Ls n (g a) - L (g a)) μ :=
    ((Ls n).integrable_comp hg).sub (L.integrable_comp hg)
  have hB : Integrable B μ := hg.norm.const_mul (C + ‖L‖)
  have hbound (n : ℕ) : ∀ᵐ a ∂μ, ‖‖Ls n (g a) - L (g a)‖‖ ≤ B a := by
    exact ae_of_all _ fun a ↦ by
      rw [norm_norm]
      calc
        _ ≤ ‖Ls n (g a)‖ + ‖L (g a)‖ := norm_sub_le _ _
        _ ≤ C * ‖g a‖ + ‖L‖ * ‖g a‖ := add_le_add
          (((Ls n).le_opNorm (g a)).trans
            (mul_le_mul_of_nonneg_right (hLs n) (norm_nonneg _)))
          (L.le_opNorm (g a))
        _ = B a := by dsimp [B]; ring
  have hlim : ∀ᵐ a ∂μ, Tendsto (fun n ↦ ‖Ls n (g a) - L (g a)‖) atTop (𝓝 0) := by
    exact ae_of_all _ fun a ↦ by
      have hc : Tendsto (fun _n : ℕ ↦ L (g a)) atTop (𝓝 (L (g a))) :=
        tendsto_const_nhds
      simpa only [sub_self, norm_zero] using ((hpoint (g a)).sub hc).norm
  have ht := tendsto_integral_of_dominated_convergence B (fun n ↦ (hi n).norm.aestronglyMeasurable)
    hB hbound hlim
  simp only [integral_zero] at ht
  have heq (n : ℕ) : eLpNorm (fun a ↦ Ls n (g a) - L (g a)) 1 μ =
      ENNReal.ofReal (∫ a, ‖Ls n (g a) - L (g a)‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hi n).aestronglyMeasurable,
      ofReal_integral_norm_eq_lintegral_enorm (hi n)]
  have ht' := ENNReal.tendsto_ofReal ht
  simp only [ENNReal.ofReal_zero] at ht'
  exact (tendsto_congr fun n ↦ heq n).2 ht'

/-- A true uniformly bounded linear operator gives the literal strong norm bound. -/
theorem eLpNorm_operator_apply_le
    {A E F : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure A} {p : ℝ≥0∞} (L : E →L[ℝ] F) {C : ℝ} (hLC : ‖L‖ ≤ C)
    {g : A → E} (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun a ↦ L (g a)) p μ ≤ ENNReal.ofReal C * eLpNorm g p μ := by
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (L.continuous.comp_aestronglyMeasurable hg)
  exact ae_of_all _ fun a ↦ (L.le_opNorm (g a)).trans
    (mul_le_mul_of_nonneg_right hLC (norm_nonneg _))

/-- Strong L¹ input approximation and actual pointwise operator approximation commute. -/
theorem tendsto_eLpNorm_moving_operator_curve_one
    {A E F : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure A} {L : E →L[ℝ] F} {Ls : ℕ → E →L[ℝ] F}
    {C : ℝ} (hLs : ∀ n, ‖Ls n‖ ≤ C)
    (hpoint : ∀ x : E, Tendsto (fun n ↦ Ls n x) atTop (𝓝 (L x)))
    {g : A → E} {gs : ℕ → A → E} (hg : MemLp g 1 μ)
    (hgs : ∀ n, MemLp (gs n) 1 μ)
    (hconv : Tendsto (fun n ↦ eLpNorm (gs n - g) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun a ↦ Ls n (gs n a) - L (g a)) 1 μ)
      atTop (𝓝 0) := by
  have hf := tendsto_eLpNorm_operator_curve_one hLs hpoint
    (memLp_one_iff_integrable.mp hg)
  have hv := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hconv
    (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hv
  have ht := hv.add hf
  simp only [zero_add] at ht
  have hb (n : ℕ) : eLpNorm (fun a ↦ Ls n (gs n a) - L (g a)) 1 μ ≤
      ENNReal.ofReal C * eLpNorm (gs n - g) 1 μ +
        eLpNorm (fun a ↦ Ls n (g a) - L (g a)) 1 μ := by
    have heq : (fun a ↦ Ls n (gs n a) - L (g a)) =
        (fun a ↦ Ls n ((gs n - g) a)) + (fun a ↦ Ls n (g a) - L (g a)) := by
      funext a
      simp only [Pi.add_apply, Pi.sub_apply, map_sub]
      abel
    rw [heq]
    exact (eLpNorm_add_le (by simp : (1 : ℝ≥0∞) ≤ 1)).trans
      (add_le_add (eLpNorm_operator_apply_le (Ls n) (hLs n)
        ((hgs n).sub hg).aestronglyMeasurable) le_rfl)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun _ ↦ zero_le) (Eventually.of_forall hb)

end FluidSingularSets
