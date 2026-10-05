-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.StrongLpProducts

/-!
# Genuine weighted monomial integral limits

Bounded smooth-test coefficients multiply the strong local field limits.
Holder products then give the exact quadratic and cubic integrals needed by
weak momentum and local energy. These are ordinary Bochner integrals of actual
integrable fields, with no distributional identity or energy inequality assumed.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- A fixed bounded coefficient preserves strong local integral convergence. -/
theorem tendsto_integral_mul_bounded
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤)
    {f b : α → ℝ} {fs : ℕ → α → ℝ} (hf : MemLp f p μ)
    (hfs : ∀ n, MemLp (fs n) p μ) (hb : MemLp b ⊤ μ)
    (hconv : Tendsto (fun n ↦ eLpNorm (fs n - f) p μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, fs n x * b x ∂μ) atTop (𝓝 (∫ x, f x * b x ∂μ)) := by
  have hbc : Tendsto (fun _n : ℕ ↦ eLpNorm (b - b) ⊤ μ) atTop (𝓝 0) := by
    simp
  have hpc := tendsto_eLpNorm_sub_mul (p := p) (q := ⊤) (r := p)
    hp (by simp) hp hf hb hfs (fun _ ↦ hb) hconv hbc
  have hprod : MemLp (fun x ↦ f x * b x) p μ := by
    change MemLp (f * b) p μ
    exact hf.mul hb
  have hprods (n : ℕ) : MemLp (fun x ↦ fs n x * b x) p μ := by
    change MemLp (fs n * b) p μ
    exact (hfs n).mul hb
  exact tendsto_integral_of_eLpNorm_sub hp hpfin hprod hprods hpc

/-- Quadratic Holder products with a bounded test coefficient converge in the
actual integral on any finite local measure. -/
theorem tendsto_integral_mul_mul_bounded
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hrfin : r ≠ ⊤)
    [ENNReal.HolderTriple p q r]
    {f g b : α → ℝ} {fs gs : ℕ → α → ℝ}
    (hf : MemLp f p μ) (hg : MemLp g q μ)
    (hfs : ∀ n, MemLp (fs n) p μ) (hgs : ∀ n, MemLp (gs n) q μ)
    (hb : MemLp b ⊤ μ)
    (hfc : Tendsto (fun n ↦ eLpNorm (fs n - f) p μ) atTop (𝓝 0))
    (hgc : Tendsto (fun n ↦ eLpNorm (gs n - g) q μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, (fs n x * gs n x) * b x ∂μ)
      atTop (𝓝 (∫ x, (f x * g x) * b x ∂μ)) := by
  have hprod : MemLp (fun x ↦ f x * g x) r μ := by
    change MemLp (f * g) r μ
    exact hf.mul hg
  have hprods (n : ℕ) : MemLp (fun x ↦ fs n x * gs n x) r μ := by
    change MemLp (fs n * gs n) r μ
    exact (hfs n).mul (hgs n)
  exact tendsto_integral_mul_bounded hr hrfin hprod hprods hb
    (tendsto_eLpNorm_sub_mul hp hq hr hf hg hfs hgs hfc hgc)

/-- The genuine cubic Holder monomials converge against a bounded test
coefficient. The intermediate and final Holder exponents are explicit. -/
theorem tendsto_integral_mul_mul_mul_bounded
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {p q s r t : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (hr : 1 ≤ r) (ht : 1 ≤ t) (htfin : t ≠ ⊤)
    [ENNReal.HolderTriple p q r] [ENNReal.HolderTriple r s t]
    {f g h b : α → ℝ} {fs gs hs' : ℕ → α → ℝ}
    (hf : MemLp f p μ) (hg : MemLp g q μ) (hh : MemLp h s μ)
    (hfs : ∀ n, MemLp (fs n) p μ) (hgs : ∀ n, MemLp (gs n) q μ)
    (hhs : ∀ n, MemLp (hs' n) s μ) (hb : MemLp b ⊤ μ)
    (hfc : Tendsto (fun n ↦ eLpNorm (fs n - f) p μ) atTop (𝓝 0))
    (hgc : Tendsto (fun n ↦ eLpNorm (gs n - g) q μ) atTop (𝓝 0))
    (hhc : Tendsto (fun n ↦ eLpNorm (hs' n - h) s μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, ((fs n x * gs n x) * hs' n x) * b x ∂μ)
      atTop (𝓝 (∫ x, ((f x * g x) * h x) * b x ∂μ)) := by
  have hprod : MemLp (fun x ↦ f x * g x) r μ := by
    change MemLp (f * g) r μ
    exact hf.mul hg
  have hprods (n : ℕ) : MemLp (fun x ↦ fs n x * gs n x) r μ := by
    change MemLp (fs n * gs n) r μ
    exact (hfs n).mul (hgs n)
  exact tendsto_integral_mul_mul_bounded hr hs ht htfin hprod hh hprods hhs hb
    (tendsto_eLpNorm_sub_mul hp hq hr hf hg hfs hgs hfc hgc) hhc

end FluidSingularSets
