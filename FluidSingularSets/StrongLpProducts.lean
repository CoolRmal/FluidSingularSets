-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.CriticalPoincare

/-!
# Strong convergence of the actual nonlinear weak-equation terms

Holder products preserve strong local convergence at the exact reciprocal
exponents. This supplies the quadratic, cubic and pressure-velocity limits
needed when smooth accelerating frames approximate an absolutely continuous
frame. The hypotheses describe ordinary strong norms of genuine `MemLp` fields.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- Strong Holder convergence preserves a genuine product at its exact target
exponent. The norm of the second factor converges to a finite actual norm. -/
theorem tendsto_eLpNorm_sub_mul
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q r : ℝ≥0∞} (_hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    [ENNReal.HolderTriple p q r] {f g : α → ℝ} {fs gs : ℕ → α → ℝ}
    (hf : MemLp f p μ) (hg : MemLp g q μ)
    (hfs : ∀ n, MemLp (fs n) p μ) (hgs : ∀ n, MemLp (gs n) q μ)
    (hfc : Tendsto (fun n ↦ eLpNorm (fs n - f) p μ) atTop (𝓝 0))
    (hgc : Tendsto (fun n ↦ eLpNorm (gs n - g) q μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun x ↦ fs n x * gs n x - f x * g x) r μ)
      atTop (𝓝 0) := by
  have hgn := tendsto_eLpNorm_of_sub hq hg hgs hgc
  have hleft := ENNReal.Tendsto.mul hfc (Or.inr hg.eLpNorm_ne_top) hgn
    (Or.inr (by simp : (0 : ℝ≥0∞) ≠ ⊤))
  have hright := ENNReal.Tendsto.const_mul (a := eLpNorm f p μ) hgc
    (Or.inr hf.eLpNorm_ne_top)
  have hsum := hleft.add hright
  simp only [zero_mul, mul_zero, zero_add] at hsum
  have hbound (n : ℕ) :
      eLpNorm (fun x ↦ fs n x * gs n x - f x * g x) r μ ≤
        eLpNorm (fs n - f) p μ * eLpNorm (gs n) q μ +
          eLpNorm f p μ * eLpNorm (gs n - g) q μ := by
    have heq : (fun x ↦ fs n x * gs n x - f x * g x) =
        (fun x ↦ (fs n x - f x) * gs n x) +
          (fun x ↦ f x * (gs n x - g x)) := by
      funext x
      simp only [Pi.add_apply]
      ring
    rw [heq]
    calc
      _ ≤ eLpNorm (fun x ↦ (fs n x - f x) * gs n x) r μ +
          eLpNorm (fun x ↦ f x * (gs n x - g x)) r μ := eLpNorm_add_le hr
      _ ≤ _ := by
        apply add_le_add
        · change eLpNorm ((fs n - f) • gs n) r μ ≤ _
          exact eLpNorm_smul_le_mul_eLpNorm (p := p) (q := q) (r := r)
            ((hfs n).sub hf).aestronglyMeasurable (hgs n).aestronglyMeasurable
        · change eLpNorm (f • (gs n - g)) r μ ≤ _
          exact eLpNorm_smul_le_mul_eLpNorm (p := p) (q := q) (r := r)
            hf.aestronglyMeasurable ((hgs n).sub hg).aestronglyMeasurable
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ ↦ zero_le) (Eventually.of_forall hbound)

/-- On a finite local measure, strong convergence in an exponent at least one
implies strong `L¹` convergence. -/
theorem tendsto_eLpNorm_one_of_sub
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} [IsFiniteMeasure μ] {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤)
    {f : α → E} {fs : ℕ → α → E} (hf : MemLp f p μ)
    (hfs : ∀ n, MemLp (fs n) p μ)
    (hconv : Tendsto (fun n ↦ eLpNorm (fs n - f) p μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fs n - f) 1 μ) atTop (𝓝 0) := by
  have hpReal : 1 ≤ p.toReal := by
    simpa using (ENNReal.toReal_le_toReal ENNReal.one_ne_top hpfin).2 hp
  have hpow : 0 ≤ 1 - p.toReal⁻¹ := by
    have hinv : p.toReal⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).2 hpReal
    linarith
  have hfactor : μ univ ^ (1 - p.toReal⁻¹) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg hpow (measure_ne_top μ univ)).ne
  have hzero := ENNReal.Tendsto.mul_const hconv (Or.inr hfactor)
  simp only [zero_mul] at hzero
  have hbound (n : ℕ) : eLpNorm (fs n - f) 1 μ ≤
      eLpNorm (fs n - f) p μ * μ univ ^ (1 - p.toReal⁻¹) := by
    simpa only [ENNReal.toReal_one, one_div, inv_one] using
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp ((hfs n).sub hf).aestronglyMeasurable
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
    (Eventually.of_forall fun _ ↦ zero_le) (Eventually.of_forall hbound)

/-- Strong local convergence preserves the actual Bochner integrals. -/
theorem tendsto_integral_of_eLpNorm_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤)
    {f : α → ℝ} {fs : ℕ → α → ℝ} (hf : MemLp f p μ)
    (hfs : ∀ n, MemLp (fs n) p μ)
    (hconv : Tendsto (fun n ↦ eLpNorm (fs n - f) p μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, fs n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
  tendsto_integral_of_L1' f (Eventually.of_forall fun n ↦ (hfs n).integrable hp)
    (tendsto_eLpNorm_one_of_sub hp hpfin hf hfs hconv)

end FluidSingularSets
