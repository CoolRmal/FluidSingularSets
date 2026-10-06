-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import CKN.Foundation.Parabolic.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-!
# Genuine terminal exhaustion of spacetime cylinders

Uniform nonnegative density bounds on every strictly terminal-truncated
cylinder pass to the full original cylinder by a countable increasing
exhaustion. No temporal continuity or auxiliary energy bound is assumed.
-/

@[expose] public section

open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FluidSingularSets

/-- True uniform density bounds on all terminal truncations bound the whole cylinder. -/
theorem lintegral_cylinder_le_of_terminal_truncations
    {B : Set Vec3} {a b : ℝ} (hab : a < b) {F : ParabolicPoint → ℝ≥0∞} {C : ℝ≥0∞}
    (hbound : ∀ δ : ℝ, 0 < δ → δ < b - a →
      (∫⁻ z : ParabolicPoint in B ×ˢ Ioo a (b - δ), F z) ≤ C) :
    (∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b, F z) ≤ C := by
  let δ : ℕ → ℝ := fun n ↦ (b - a) / ((n : ℝ) + 2)
  let s : ℕ → Set ParabolicPoint := fun n ↦ B ×ˢ Ioo a (b - δ n)
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hδpos (n : ℕ) : 0 < δ n :=
    div_pos hgap (by positivity)
  have hδlt (n : ℕ) : δ n < b - a := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    exact div_lt_self hgap (by linarith)
  have hδanti : Antitone δ := by
    intro m n hmn
    exact div_le_div_of_nonneg_left hgap.le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hmn 2)
  have hmono : Monotone s := by
    intro m n hmn z hz
    refine ⟨hz.1, hz.2.1, ?_⟩
    have hh := hδanti hmn
    linarith [hz.2.2]
  have hδzero : Tendsto δ atTop (𝓝 0) := by
    have ht := (tendsto_const_div_atTop_nhds_zero_nat (b - a)).comp
      (tendsto_add_atTop_nat 2)
    simpa only [δ, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using ht
  have hunion : (⋃ n, s n) = B ×ˢ Ioo a b := by
    ext z
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := mem_iUnion.mp hz
      exact ⟨hn.1, hn.2.1, hn.2.2.trans (sub_lt_self _ (hδpos n))⟩
    · intro hz
      obtain ⟨n, hn⟩ := (hδzero.eventually
        (eventually_lt_nhds (sub_pos.mpr hz.2.2))).exists
      exact mem_iUnion.mpr ⟨n, hz.1, hz.2.1, by linarith⟩
  have hd : Directed (· ⊆ ·) s := fun m n ↦
    ⟨max m n, hmono (le_max_left m n), hmono (le_max_right m n)⟩
  calc
    _ = ∫⁻ z : ParabolicPoint in ⋃ n, s n, F z :=
      congrArg (fun A : Set ParabolicPoint ↦ ∫⁻ z in A, F z) hunion.symm
    _ = ⨆ n, ∫⁻ z : ParabolicPoint in s n, F z :=
      setLIntegral_iUnion_of_directed F hd
    _ ≤ C := iSup_le fun n ↦ hbound (δ n) (hδpos n) (hδlt n)

/-- The literal parabolic inner cylinder needs no future endpoint enlargement. -/
theorem lintegral_parabolic_cylinder_le_of_terminal_truncations
    {r : ℝ} (hr : 0 < r) {F : ParabolicPoint → ℝ≥0∞} {C : ℝ≥0∞}
    (hbound : ∀ δ : ℝ, 0 < δ → δ < r ^ 2 →
      (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) (-δ), F z) ≤ C) :
    (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) 0, F z) ≤ C := by
  apply lintegral_cylinder_le_of_terminal_truncations (by nlinarith [sq_pos_of_pos hr])
  intro δ hδ hδlt
  simpa only [zero_sub, sub_neg_eq_add, zero_add] using hbound δ hδ
    (by simpa only [sub_neg_eq_add, zero_add] using hδlt)

/-- Native spacetime volume genuinely ignores the terminal time slice. -/
theorem lintegral_cylinder_Ioo_eq_Ioc (B : Set Vec3) (a b : ℝ)
    (F : ParabolicPoint → ℝ≥0∞) :
    (∫⁻ z : ParabolicPoint in B ×ˢ Ioo a b, F z) =
      ∫⁻ z : ParabolicPoint in B ×ˢ Ioc a b, F z := by
  have hp := Measure.set_prod_ae_eq (μ := (volume : Measure Vec3)) (ν := (volume : Measure ℝ))
    (s := B) (s' := B) EventuallyEq.rfl (Ioo_ae_eq_Ioc (a := a) (b := b))
  have hn : (B ×ˢ Ioo a b : Set ParabolicPoint) =ᵐ[volume] B ×ˢ Ioc a b := hp
  exact congrArg (fun μ : Measure ParabolicPoint ↦ ∫⁻ z, F z ∂μ)
    (Measure.restrict_congr_set hn)

/-- The same actual bound holds for the pinned CKN cylinder including its terminal slice. -/
theorem lintegral_parabolicCylinder_le_of_terminal_truncations
    {r : ℝ} (hr : 0 < r) {F : ParabolicPoint → ℝ≥0∞} {C : ℝ≥0∞}
    (hbound : ∀ δ : ℝ, 0 < δ → δ < r ^ 2 →
      (∫⁻ z : ParabolicPoint in vec3Ball 0 r ×ˢ Ioo (-(r ^ 2)) (-δ), F z) ≤ C) :
    (∫⁻ z : ParabolicPoint in parabolicCylinder 0 0 r, F z) ≤ C := by
  simpa only [parabolicCylinder, zero_sub] using
    (lintegral_cylinder_Ioo_eq_Ioc (vec3Ball 0 r) (-(r ^ 2)) 0 F).symm.trans_le
      (lintegral_parabolic_cylinder_le_of_terminal_truncations hr hbound)

end FluidSingularSets
