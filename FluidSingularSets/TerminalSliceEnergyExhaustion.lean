-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.TruncatedCylinderExhaustion
public import Mathlib.MeasureTheory.Function.EssSup

/-!
# Genuine terminal exhaustion of essential slice-energy bounds

A uniform actual essential bound on every strictly truncated original time
interval bounds the full interval. Countably many exceptional null sets are
combined before the endpoint is exhausted.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option autoImplicit false

namespace FluidSingularSets

/-- The same true essential slice bound holds on the entire original open interval. -/
theorem essSup_Ioo_le_of_terminal_truncations {a b : ℝ} (hab : a < b)
    {E : ℝ → ℝ≥0∞} {C : ℝ≥0∞}
    (hbound : ∀ δ : ℝ, 0 < δ → δ < b - a →
      essSup E (volume.restrict (Ioo a (b - δ))) ≤ C) :
    essSup E (volume.restrict (Ioo a b)) ≤ C := by
  let δ : ℕ → ℝ := fun n ↦ (b - a) / ((n : ℝ) + 2)
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hδpos (n : ℕ) : 0 < δ n := div_pos hgap (by positivity)
  have hδlt (n : ℕ) : δ n < b - a := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    exact div_lt_self hgap (by linarith)
  have hδzero : Tendsto δ atTop (𝓝 0) := by
    have ht := (tendsto_const_div_atTop_nhds_zero_nat (b - a)).comp
      (tendsto_add_atTop_nat 2)
    simpa only [δ, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using ht
  have hn (n : ℕ) : ∀ᵐ t : ℝ ∂volume, t ∈ Ioo a (b - δ n) → E t ≤ C := by
    apply (ae_restrict_iff' measurableSet_Ioo).mp
    filter_upwards [ENNReal.ae_le_essSup (μ := volume.restrict (Ioo a (b - δ n))) E] with t ht
    exact ht.trans (hbound (δ n) (hδpos n) (hδlt n))
  refine essSup_le_of_ae_le C ?_
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [ae_all_iff.mpr hn] with t ht htI
  obtain ⟨n, hsmall⟩ := (hδzero.eventually
    (eventually_lt_nhds (sub_pos.mpr htI.2))).exists
  exact ht n ⟨htI.1, by linarith⟩

end FluidSingularSets
