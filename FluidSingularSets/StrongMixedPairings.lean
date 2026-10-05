-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StrongLpProducts
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Strong limits of genuine Hilbert pairings

Time L¹ pressure curves pair with actual time L∞ velocity curves in spatial
L². Genuine Hölder estimates and bilinearity prove convergence of their real
inner products and ordinary tested integrals. These lemmas require true strong
norm convergence of the curves, without any weak equation or energy premise.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- Actual Hilbert pairings obey genuine Hölder at arbitrary compatible exponents. -/
theorem eLpNorm_real_inner_le
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure α} {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x ↦ inner ℝ (f x) (g x)) r μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  simpa only [ENNReal.coe_one, one_mul] using
    eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := p) (q := q) (r := r)
      (fun x y : E ↦ inner ℝ x y) 1 continuous_inner hf hg
      (ae_of_all _ fun x ↦ by
        simpa only [NNReal.coe_one, one_mul] using norm_inner_le_norm (f x) (g x))

/-- True compatible Hilbert pairings have the actual target Lp class. -/
theorem memLp_real_inner
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure α} {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    MemLp (fun x ↦ inner ℝ (f x) (g x)) r μ := by
  have hprod : MemLp (fun x ↦ ‖f x‖ * ‖g x‖) r μ := hf.norm.mul hg.norm
  apply hprod.of_le (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
  exact ae_of_all _ fun x ↦ by
    simpa only [norm_mul, norm_norm] using norm_inner_le_norm (f x) (g x)

/-- Bilinearity and true strong norms preserve the actual Hilbert pairing. -/
theorem tendsto_eLpNorm_sub_real_inner
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure α} {p q r : ℝ≥0∞} (hq : 1 ≤ q) (hr : 1 ≤ r)
    [ENNReal.HolderTriple p q r] {f g : α → E} {fs gs : ℕ → α → E}
    (hf : MemLp f p μ) (hg : MemLp g q μ)
    (hfs : ∀ n, MemLp (fs n) p μ) (hgs : ∀ n, MemLp (gs n) q μ)
    (hfc : Tendsto (fun n ↦ eLpNorm (fs n - f) p μ) atTop (𝓝 0))
    (hgc : Tendsto (fun n ↦ eLpNorm (gs n - g) q μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm
      (fun x ↦ inner ℝ (fs n x) (gs n x) - inner ℝ (f x) (g x)) r μ)
      atTop (𝓝 0) := by
  have hgn := tendsto_eLpNorm_of_sub hq hg hgs hgc
  have hl := ENNReal.Tendsto.mul hfc (Or.inr hg.eLpNorm_ne_top) hgn
    (Or.inr (by simp : (0 : ℝ≥0∞) ≠ ⊤))
  have hr' := ENNReal.Tendsto.const_mul (a := eLpNorm f p μ) hgc
    (Or.inr hf.eLpNorm_ne_top)
  have hsum := hl.add hr'
  simp only [zero_mul, mul_zero, zero_add] at hsum
  have hbound (n : ℕ) : eLpNorm
      (fun x ↦ inner ℝ (fs n x) (gs n x) - inner ℝ (f x) (g x)) r μ ≤
        eLpNorm (fs n - f) p μ * eLpNorm (gs n) q μ +
          eLpNorm f p μ * eLpNorm (gs n - g) q μ := by
    have heq : (fun x ↦ inner ℝ (fs n x) (gs n x) - inner ℝ (f x) (g x)) =
        (fun x ↦ inner ℝ (fs n x - f x) (gs n x)) +
          (fun x ↦ inner ℝ (f x) (gs n x - g x)) := by
      funext x
      simp only [Pi.add_apply, inner_sub_left, inner_sub_right]
      ring
    rw [heq]
    exact (eLpNorm_add_le hr).trans (add_le_add
      (eLpNorm_real_inner_le ((hfs n).sub hf).aestronglyMeasurable
        (hgs n).aestronglyMeasurable)
      (eLpNorm_real_inner_le hf.aestronglyMeasurable
        ((hgs n).sub hg).aestronglyMeasurable))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ ↦ zero_le) (Eventually.of_forall hbound)

/-- The actual integral of compatible strongly converging Hilbert pairings converges. -/
theorem tendsto_integral_real_inner
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure α} [IsFiniteMeasure μ] {p q r : ℝ≥0∞}
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hrfin : r ≠ ⊤) [ENNReal.HolderTriple p q r]
    {f g : α → E} {fs gs : ℕ → α → E}
    (hf : MemLp f p μ) (hg : MemLp g q μ)
    (hfs : ∀ n, MemLp (fs n) p μ) (hgs : ∀ n, MemLp (gs n) q μ)
    (hfc : Tendsto (fun n ↦ eLpNorm (fs n - f) p μ) atTop (𝓝 0))
    (hgc : Tendsto (fun n ↦ eLpNorm (gs n - g) q μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, inner ℝ (fs n x) (gs n x) ∂μ)
      atTop (𝓝 (∫ x, inner ℝ (f x) (g x) ∂μ)) :=
  tendsto_integral_of_eLpNorm_sub hr hrfin (memLp_real_inner hf hg)
    (fun n ↦ memLp_real_inner (hfs n) (hgs n))
    (tendsto_eLpNorm_sub_real_inner hq hr hf hg hfs hgs hfc hgc)

/-- Actual time L¹ spatial-pressure classes pair continuously with time L∞ velocity classes. -/
theorem tendsto_integral_real_inner_one_top
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure α} [IsFiniteMeasure μ] {f g : α → E} {fs gs : ℕ → α → E}
    (hf : MemLp f 1 μ) (hg : MemLp g ⊤ μ)
    (hfs : ∀ n, MemLp (fs n) 1 μ) (hgs : ∀ n, MemLp (gs n) ⊤ μ)
    (hfc : Tendsto (fun n ↦ eLpNorm (fs n - f) 1 μ) atTop (𝓝 0))
    (hgc : Tendsto (fun n ↦ eLpNorm (gs n - g) ⊤ μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, inner ℝ (fs n x) (gs n x) ∂μ)
      atTop (𝓝 (∫ x, inner ℝ (f x) (g x) ∂μ)) :=
  tendsto_integral_real_inner (p := 1) (q := ⊤) (r := 1)
    (by simp) (by simp) (by simp) hf hg hfs hgs hfc hgc

end FluidSingularSets
