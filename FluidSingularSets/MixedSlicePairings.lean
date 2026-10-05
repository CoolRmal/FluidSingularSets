-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StrongMixedPairings
public import FluidSingularSets.SliceLpMoments

/-!
# Genuine mixed spatial L² pairings

Actual jointly measurable scalar fields whose true spatial L² classes have
time L¹ and L∞ norms have an integrable spacetime product. Its ordinary
integral is the time integral of the genuine spatial Hilbert pairing. Strong
convergence of those actual class curves therefore preserves the tested
spacetime pressure-velocity integral.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The actual absolute-product integral is bounded by the true spatial L² norms. -/
theorem integral_norm_mul_le_L2_norms
    {A : Type*} [MeasurableSpace A] {μ : Measure A} {f g : A → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, ‖f x * g x‖ ∂μ) ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  let F := hf.norm.toLp (fun x ↦ ‖f x‖)
  let G := hg.norm.toLp (fun x ↦ ‖g x‖)
  have heq : (∫ x, ‖f x * g x‖ ∂μ) = inner ℝ F G := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.norm.coeFn_toLp, hg.norm.coeFn_toLp] with x hx hy
    simp only [F, G, hx, hy, Real.inner_apply, norm_mul]
  have hn : |inner ℝ F G| ≤ ‖F‖ * ‖G‖ := by
    simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) F G)
  have hbound := (le_abs_self (inner ℝ F G)).trans hn
  have hFn : ‖F‖ = (eLpNorm f 2 μ).toReal := by
    rw [Lp.norm_toLp, eLpNorm_norm f hf.aestronglyMeasurable]
  have hGn : ‖G‖ = (eLpNorm g 2 μ).toReal := by
    rw [Lp.norm_toLp, eLpNorm_norm g hg.aestronglyMeasurable]
  exact heq.trans_le (hbound.trans_eq (congrArg₂ (fun a b : ℝ ↦ a * b) hFn hGn))

/-- Every genuine good slice has the ordinary integral represented by its actual Hilbert class. -/
theorem actualSliceLp_inner_eq_integral
    {A T : Type*} [MeasurableSpace A] {μ : Measure A}
    {F G : A × T → ℝ} (t : T)
    (hF : MemLp (fun x ↦ F (x, t)) 2 μ) (hG : MemLp (fun x ↦ G (x, t)) 2 μ) :
    inner ℝ (actualSliceLp (μ := μ) (p := 2) F t)
      (actualSliceLp (μ := μ) (p := 2) G t) = ∫ x, F (x, t) * G (x, t) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [actualSliceLp_ae F t hF, actualSliceLp_ae G t hG] with x hx hy
  simp only [hx, hy, Real.inner_apply]

/-- Genuine spatial L² slices with actual time L¹/L∞ class norms have an integrable product. -/
theorem integrable_mul_of_actualSliceLp_one_top
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    {μ : Measure A} {ν : Measure T} [SFinite μ] [SFinite ν]
    {F G : A × T → ℝ}
    (hF : AEStronglyMeasurable F (μ.prod ν)) (hG : AEStronglyMeasurable G (μ.prod ν))
    (hFs : ∀ᵐ t ∂ν, MemLp (fun x ↦ F (x, t)) 2 μ)
    (hGs : ∀ᵐ t ∂ν, MemLp (fun x ↦ G (x, t)) 2 μ)
    (hFc : MemLp (actualSliceLp (μ := μ) (p := 2) F) 1 ν)
    (hGc : MemLp (actualSliceLp (μ := μ) (p := 2) G) ⊤ ν) :
    Integrable (fun z ↦ F z * G z) (μ.prod ν) := by
  have hFG := hF.mul hG
  apply (integrable_prod_iff' hFG).2
  refine ⟨?_, ?_⟩
  · filter_upwards [hFs, hGs] with t hft hgt
    exact hft.integrable_mul hgt
  · have hnorm : Integrable
        (fun t ↦ ‖actualSliceLp (μ := μ) (p := 2) F t‖ *
          ‖actualSliceLp (μ := μ) (p := 2) G t‖) ν :=
      memLp_one_iff_integrable.mp (hFc.norm.mul (r := 1) hGc.norm)
    apply hnorm.mono' hFG.norm.prod_swap.integral_prod_right'
    filter_upwards [hFs, hGs] with t hft hgt
    have hFn : ‖actualSliceLp (μ := μ) (p := 2) F t‖ =
        (eLpNorm (fun x ↦ F (x, t)) 2 μ).toReal := by
      rw [← toReal_enorm, actualSliceLp_enorm F t hft]
    have hGn : ‖actualSliceLp (μ := μ) (p := 2) G t‖ =
        (eLpNorm (fun x ↦ G (x, t)) 2 μ).toReal := by
      rw [← toReal_enorm, actualSliceLp_enorm G t hgt]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _), hFn, hGn]
    exact integral_norm_mul_le_L2_norms hft hgt

/-- The genuine spacetime product integral is the time integral of the actual spatial L² pairing. -/
theorem integral_mul_eq_integral_actualSliceLp_inner
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    {μ : Measure A} {ν : Measure T} [SFinite μ] [SFinite ν]
    {F G : A × T → ℝ}
    (hF : AEStronglyMeasurable F (μ.prod ν)) (hG : AEStronglyMeasurable G (μ.prod ν))
    (hFs : ∀ᵐ t ∂ν, MemLp (fun x ↦ F (x, t)) 2 μ)
    (hGs : ∀ᵐ t ∂ν, MemLp (fun x ↦ G (x, t)) 2 μ)
    (hFc : MemLp (actualSliceLp (μ := μ) (p := 2) F) 1 ν)
    (hGc : MemLp (actualSliceLp (μ := μ) (p := 2) G) ⊤ ν) :
    (∫ z, F z * G z ∂μ.prod ν) =
      ∫ t, inner ℝ (actualSliceLp (μ := μ) (p := 2) F t)
        (actualSliceLp (μ := μ) (p := 2) G t) ∂ν := by
  have hi := integrable_mul_of_actualSliceLp_one_top hF hG hFs hGs hFc hGc
  refine (integral_prod_symm _ hi).trans ?_
  apply integral_congr_ae
  filter_upwards [hFs, hGs] with t hft hgt
  exact (actualSliceLp_inner_eq_integral t hft hgt).symm

/-- Strong actual mixed spatial classes preserve the ordinary spacetime product integral. -/
theorem tendsto_integral_mul_actualSliceLp_one_top
    {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    {μ : Measure A} {ν : Measure T} [SFinite μ] [SFinite ν] [IsFiniteMeasure ν]
    {F G : A × T → ℝ} {Fs Gs : ℕ → A × T → ℝ}
    (hF : AEStronglyMeasurable F (μ.prod ν)) (hG : AEStronglyMeasurable G (μ.prod ν))
    (hFs : ∀ᵐ t ∂ν, MemLp (fun x ↦ F (x, t)) 2 μ)
    (hGs : ∀ᵐ t ∂ν, MemLp (fun x ↦ G (x, t)) 2 μ)
    (hFc : MemLp (actualSliceLp (μ := μ) (p := 2) F) 1 ν)
    (hGc : MemLp (actualSliceLp (μ := μ) (p := 2) G) ⊤ ν)
    (hFsm : ∀ n, AEStronglyMeasurable (Fs n) (μ.prod ν))
    (hGsm : ∀ n, AEStronglyMeasurable (Gs n) (μ.prod ν))
    (hFss : ∀ n, ∀ᵐ t ∂ν, MemLp (fun x ↦ Fs n (x, t)) 2 μ)
    (hGss : ∀ n, ∀ᵐ t ∂ν, MemLp (fun x ↦ Gs n (x, t)) 2 μ)
    (hFsc : ∀ n, MemLp (actualSliceLp (μ := μ) (p := 2) (Fs n)) 1 ν)
    (hGsc : ∀ n, MemLp (actualSliceLp (μ := μ) (p := 2) (Gs n)) ⊤ ν)
    (hconvF : Tendsto (fun n ↦ eLpNorm
      (actualSliceLp (μ := μ) (p := 2) (Fs n) - actualSliceLp (μ := μ) (p := 2) F) 1 ν)
      atTop (𝓝 0))
    (hconvG : Tendsto (fun n ↦ eLpNorm
      (actualSliceLp (μ := μ) (p := 2) (Gs n) - actualSliceLp (μ := μ) (p := 2) G) ⊤ ν)
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ z, Fs n z * Gs n z ∂μ.prod ν)
      atTop (𝓝 (∫ z, F z * G z ∂μ.prod ν)) := by
  have ht := tendsto_integral_real_inner_one_top hFc hGc hFsc hGsc hconvF hconvG
  have hlim := integral_mul_eq_integral_actualSliceLp_inner hF hG hFs hGs hFc hGc
  have hn (n : ℕ) := integral_mul_eq_integral_actualSliceLp_inner
    (hFsm n) (hGsm n) (hFss n) (hGss n) (hFsc n) (hGsc n)
  exact (tendsto_congr fun n ↦ hn n).2 (hlim.symm ▸ ht)

end FluidSingularSets
