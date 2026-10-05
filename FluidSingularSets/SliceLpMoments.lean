-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.SliceLpMeasurable

/-!
# Actual spatial Lp class norms and time moments

The norm of a genuine good slice is its spatial Lp seminorm. The exceptional
zero branch only decreases it. Tonelli then turns actual joint Lp data into
Lp integrability of the true class-valued slice curve. Mixed time moments may
also be used directly, without a separate measurability assumption.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

open Classical

section Norms

variable {A T E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
  {μ : Measure A} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual extended norm of every genuine good spatial slice. -/
theorem actualSliceLp_enorm (F : A × T → E) (t : T)
    (ht : MemLp (fun x ↦ F (x, t)) p μ) :
    ‖actualSliceLp (μ := μ) (p := p) F t‖ₑ = eLpNorm (fun x ↦ F (x, t)) p μ := by
  rw [Lp.enorm_def]
  exact eLpNorm_congr_ae (actualSliceLp_ae F t ht)

/-- The exceptional zero branch decreases the genuine slice seminorm. -/
theorem actualSliceLp_enorm_le (F : A × T → E) (t : T) :
    ‖actualSliceLp (μ := μ) (p := p) F t‖ₑ ≤ eLpNorm (fun x ↦ F (x, t)) p μ := by
  by_cases ht : MemLp (fun x ↦ F (x, t)) p μ
  · exact (actualSliceLp_enorm F t ht).le
  · simp only [actualSliceLp, dite_eq_right ht, enorm_zero]
    exact bot_le

end Norms

section Moments

variable {A T E : Type*} [MeasurableSpace A] [MeasurableSpace T]
  [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure A} [SFinite μ] [IsSeparable μ]
  {ν : Measure T} [SFinite ν] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A true finite mixed time moment gives Lp of the actual spatial class curve.
Its strong measurability is derived from the original joint field. -/
theorem actualSliceLp_memLp_of_mixed_moment {F : A × T → E}
    (hF : AEStronglyMeasurable F (μ.prod ν)) (hp : p ≠ ∞)
    {b : ℝ≥0∞} (hb0 : b ≠ 0) (hb : b ≠ ∞)
    (hmoment : (∫⁻ t, eLpNorm (fun x ↦ F (x, t)) p μ ^ b.toReal ∂ν) < ∞) :
    MemLp (actualSliceLp (μ := μ) (p := p) F) b ν := by
  have hm := aestronglyMeasurable_actualSliceLp (μ := μ) (p := p) hF hp
  apply memLp_iff.mpr
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hb0 hb hm]
  apply ENNReal.rpow_lt_top_of_nonneg (by positivity)
  exact (lt_of_le_of_lt (lintegral_mono fun t ↦
    ENNReal.rpow_le_rpow (actualSliceLp_enorm_le F t) ENNReal.toReal_nonneg) hmoment).ne

omit [SecondCountableTopology E] [IsSeparable μ] in
/-- Tonelli gives the exact spatial-norm moment of a genuine joint measurable field. -/
theorem actualSlice_eLpNorm_moment_eq_prod {F : A × T → E}
    (hF : AEStronglyMeasurable F (μ.prod ν)) (hp : p ≠ ∞) :
    (∫⁻ t, eLpNorm (fun x ↦ F (x, t)) p μ ^ p.toReal ∂ν) =
      ∫⁻ z, ‖F z‖ₑ ^ p.toReal ∂μ.prod ν := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1)
    Fact.out)
  have hpr : p.toReal ≠ 0 := (ENNReal.toReal_pos hp0 hp).ne'
  rw [lintegral_prod_symm _ (hF.aemeasurable.enorm.pow_const p.toReal)]
  apply lintegral_congr_ae
  filter_upwards [hF.prodMk_right] with t ht
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp ht, ← ENNReal.rpow_mul,
    one_div_mul_cancel hpr, ENNReal.rpow_one]

/-- Genuine joint Lp data yield Lp in time of their actual spatial Lp class. -/
theorem actualSliceLp_memLp_of_prod_memLp {F : A × T → E}
    (hF : MemLp F p (μ.prod ν)) (hp : p ≠ ∞) :
    MemLp (actualSliceLp (μ := μ) (p := p) F) p ν := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1)
    Fact.out)
  apply actualSliceLp_memLp_of_mixed_moment hF.aestronglyMeasurable hp hp0 hp
  rw [actualSlice_eLpNorm_moment_eq_prod hF.aestronglyMeasurable hp]
  exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hF.eLpNorm_lt_top

end Moments

end FluidSingularSets
