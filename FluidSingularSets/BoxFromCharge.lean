-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.BoxDimension
public import FluidSingularSets.Packing

/-!
# Upper parabolic box dimension from a uniform ball charge

This is a geometric reduction: a finite measure that charges every sufficiently small
half-radius ball at points of a set by at least `η * r ^ s` gives box dimension at most `s`.
The uniform charge is an explicit hypothesis, separate from its derivation for a PDE.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- A finite measure with a positive uniform power charge controls parabolic box dimension. -/
theorem upperParabolicBoxDimension_le_of_uniform_ball_charge
    (ν : Measure ParabolicSpaceTime) (E : Set SpaceTime) (η s r₀ : ℝ)
    (hν : ν Set.univ ≠ ⊤) (hη : 0 < η) (hs : 0 ≤ s) (hr₀ : 0 < r₀)
    (hcharge : ∀ r : ℝ, 0 < r → r < r₀ → ∀ z ∈ toParabolic '' E,
      ENNReal.ofReal (η * r ^ s) ≤ ν (Metric.ball z (r / 2))) :
    upperParabolicBoxDimension E ≤ ENNReal.ofReal s := by
  let M : ℝ := max 1 (ν Set.univ).toReal
  let C : ℝ := M / η
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  apply upperParabolicBoxDimension_le_of_covering_bound hs (div_pos hM hη) hr₀
  intro r hr hrsmall
  have hpower : 0 < r ^ s := Real.rpow_pos_of_pos hr s
  have hcharge_pos : 0 < η * r ^ s := mul_pos hη hpower
  obtain ⟨hNfinite, hNbound⟩ :=
    externalCoveringNumber_le_measure_div_ball_charge_of_finite_mass
      ν (toParabolic '' E) r.toNNReal hν (ENNReal.ofReal (η * r ^ s))
      (ENNReal.ofReal_pos.mpr hcharge_pos).ne' ENNReal.ofReal_ne_top (by
        intro z hz
        simpa only [Real.coe_toNNReal r hr.le] using hcharge r hr hrsmall z hz)
  have hNcast : (parabolicCoveringNumber E r.toNNReal).toENNReal =
      ((parabolicCoveringNumber E r.toNNReal).toNat : ℝ≥0∞) := by
    have h := congrArg ENat.toENNReal (ENat.natCast_toNat hNfinite)
    simpa only [ENat.toENNReal_coe, parabolicCoveringNumber] using h.symm
  rw [hNcast]
  calc
    ((parabolicCoveringNumber E r.toNNReal).toNat : ℝ≥0∞) ≤
        ν Set.univ / ENNReal.ofReal (η * r ^ s) := hNbound
    _ = ENNReal.ofReal ((ν Set.univ).toReal / (η * r ^ s)) := by
      rw [ENNReal.ofReal_div_of_pos hcharge_pos, ENNReal.ofReal_toReal hν]
    _ ≤ ENNReal.ofReal (M / (η * r ^ s)) := by
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_right (le_max_right _ _) hcharge_pos.le
    _ = ENNReal.ofReal (C * r ^ (-s)) := by
      congr 1
      dsimp [C]
      rw [Real.rpow_neg hr.le]
      simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc]
      rw [mul_comm η⁻¹]

end FluidSingularSets
