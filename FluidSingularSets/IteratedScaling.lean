module

public import FluidSingularSets.IteratedLogSeries
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Affine scale comparison for iterated logarithmic weights

Passing from a geometric cylinder sequence to dyadic box levels replaces a scale index
by an affine expression. Every finite reciprocal logarithmic weight changes only by
a fixed asymptotic factor under this replacement.
-/

@[expose] public section

open Filter
open scoped Topology

namespace FluidSingularSets

/-- Taking logarithms removes a finite positive multiplicative asymptotic factor. -/
theorem tendsto_log_ratio_one {X : Type*} {l : Filter X} {f g : X → ℝ} {c : ℝ}
    (hc : 0 < c) (hf : Tendsto f l atTop) (hg : Tendsto g l atTop)
    (hratio : Tendsto (fun x ↦ f x / g x) l (𝓝 c)) :
    Tendsto (fun x ↦ Real.log (f x) / Real.log (g x)) l (𝓝 1) := by
  have hlog : Tendsto (fun x ↦ Real.log (f x / g x)) l (𝓝 (Real.log c)) :=
    (Real.continuousAt_log hc.ne').tendsto.comp hratio
  have hsmall := hlog.div_atTop (Real.tendsto_log_atTop.comp hg)
  have hlim : Tendsto (fun x ↦ 1 + Real.log (f x / g x) / Real.log (g x)) l (𝓝 1) := by
    simpa only [Function.comp_apply, add_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).add hsmall
  apply hlim.congr'
  filter_upwards [hf.eventually (eventually_gt_atTop 1),
    hg.eventually (eventually_gt_atTop 1)] with x hfx hgx
  have hf0 : f x ≠ 0 := (zero_lt_one.trans hfx).ne'
  have hg0 : g x ≠ 0 := (zero_lt_one.trans hgx).ne'
  have hlog0 : Real.log (g x) ≠ 0 := (Real.log_pos hgx).ne'
  rw [Real.log_div hf0 hg0]
  field_simp
  ring

/-- Reciprocal logarithmic products have asymptotic dilation factor `1/c` at every depth. -/
theorem tendsto_reciprocalLogWeight_ratio {X : Type*} {l : Filter X} (k : ℕ)
    {f g : X → ℝ} {c : ℝ} (hc : 0 < c) (hf : Tendsto f l atTop)
    (hg : Tendsto g l atTop) (hratio : Tendsto (fun x ↦ f x / g x) l (𝓝 c)) :
    Tendsto (fun x ↦ reciprocalLogWeight k (f x) / reciprocalLogWeight k (g x))
      l (𝓝 c⁻¹) := by
  induction k generalizing f g c with
  | zero =>
    simpa only [reciprocalLogWeight_zero, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_comm]
      using hratio.inv₀ hc.ne'
  | succ k ih =>
    have hlogs := tendsto_log_ratio_one hc hf hg hratio
    have hinner := ih zero_lt_one (Real.tendsto_log_atTop.comp hf)
      (Real.tendsto_log_atTop.comp hg) hlogs
    have houter := hratio.inv₀ hc.ne'
    simpa only [reciprocalLogWeight_succ, mul_div_mul_comm, Function.comp_apply,
      div_eq_mul_inv, mul_inv_rev, inv_inv, inv_one, mul_one, mul_comm,
      mul_assoc, mul_left_comm]
      using houter.mul hinner

/-- The affine cylinder-to-grid index change preserves each reciprocal logarithmic weight,
up to the reciprocal of the positive slope. -/
theorem tendsto_reciprocalLogWeight_affine_ratio (k : ℕ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ ↦ reciprocalLogWeight k (a * x + b) / reciprocalLogWeight k x)
      atTop (𝓝 a⁻¹) := by
  have haff : Tendsto (fun x : ℝ ↦ a * x + b) atTop atTop :=
    tendsto_atTop_add_const_right atTop b (tendsto_id.const_mul_atTop ha)
  have hratio : Tendsto (fun x : ℝ ↦ (a * x + b) / x) atTop (𝓝 a) := by
    have hlim : Tendsto (fun x : ℝ ↦ a + b / x) atTop (𝓝 a) := by
      simpa only [id_eq, add_zero] using (tendsto_const_nhds (x := a)).add
        ((tendsto_const_nhds (x := b)).div_atTop tendsto_id)
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  exact tendsto_reciprocalLogWeight_ratio k ha haff tendsto_id hratio

/-- The explicit two-sided comparison used to transfer the divergent scale cost to grid levels.
-/
theorem eventually_reciprocalLogWeight_affine_comparable (k : ℕ) {a : ℝ}
    (ha : 0 < a) (b : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      (a⁻¹ / 2) * reciprocalLogWeight k x ≤ reciprocalLogWeight k (a * x + b) ∧
      reciprocalLogWeight k (a * x + b) ≤ (2 * a⁻¹) * reciprocalLogWeight k x := by
  obtain ⟨x₀, _, hpositive, _⟩ := reciprocalLogWeight_positive_antitone_tail k
  have hi : 0 < a⁻¹ := inv_pos.mpr ha
  have hnear := (tendsto_reciprocalLogWeight_affine_ratio k ha b).eventually
    (Ioo_mem_nhds (by linarith : a⁻¹ / 2 < a⁻¹) (by linarith : a⁻¹ < 2 * a⁻¹))
  filter_upwards [hnear, eventually_ge_atTop x₀] with x hx hcutoff
  have hw : 0 < reciprocalLogWeight k x := hpositive x hcutoff
  exact ⟨(le_div_iff₀ hw).1 hx.1.le, (div_le_iff₀ hw).1 hx.2.le⟩

end FluidSingularSets
