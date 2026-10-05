-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic

/-!
# Endpoint projected Caccioppoli absorption and iteration

This module proves scalar consequences of explicit quantitative inequalities.
At p = 2 and q = 6 the interpolation parameter is 4/3. Weighted Young
absorption turns the convection power 5/6 of the square energy into power
eight of the mixed velocity norm. A bounded geometric iteration removes the
outer energy term. No velocity regularity criterion is an assumption here.

The scalar exponents follow Proposition 3.1, Section 3.2, of Li--Wang--Zhou,
arXiv:2305.00698. The actual projected energy and pressure estimates are
separate analytic inputs to the quantitative inequalities.
-/

@[expose] public section

open Filter
open scoped BigOperators Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- The precise interpolation and absorption exponents at the endpoint. -/
theorem endpoint_projected_caccioppoli_exponents :
    (2 / (2 / 2 + 3 / 6) : ℝ) = 4 / 3 ∧
      (3 - 4 / 3) / 2 = (5 / 6 : ℝ) ∧
      (2 * (4 / 3)) / ((4 / 3) - 1) = (8 : ℝ) := by
  norm_num

/-- A genuine scaled Young inequality for the convection energy exponent. -/
theorem fiveSixths_energy_absorption {a Y δ : ℝ}
    (ha : 0 ≤ a) (hY : 0 ≤ Y) (hδ : 0 < δ) :
    a * Y ^ (5 / 6 : ℝ) ≤ δ * Y + a ^ 6 / δ ^ 5 := by
  let u := (δ * Y) ^ (5 / 6 : ℝ)
  let v := a / δ ^ (5 / 6 : ℝ)
  have hp : Real.HolderConjugate (6 / 5) 6 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := Real.young_inequality_of_nonneg
    (Real.rpow_nonneg (mul_nonneg hδ.le hY) (5 / 6)) (div_nonneg ha
      (Real.rpow_nonneg hδ.le (5 / 6))) hp
  have hprod : u * v = a * Y ^ (5 / 6 : ℝ) := by
    dsimp [u, v]
    rw [Real.mul_rpow hδ.le hY]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hδ (5 / 6))]
  have hu : u ^ (6 / 5 : ℝ) = δ * Y := by
    dsimp [u]
    rw [← Real.rpow_mul (mul_nonneg hδ.le hY)]
    norm_num
  have hv : v ^ (6 : ℝ) = a ^ 6 / δ ^ 5 := by
    dsimp [v]
    rw [Real.div_rpow ha (Real.rpow_nonneg hδ.le (5 / 6)), ← Real.rpow_mul hδ.le]
    norm_num
  change u * v ≤ u ^ (6 / 5 : ℝ) / (6 / 5) + v ^ (6 : ℝ) / 6 at h
  rw [hprod, hu, hv] at h
  have hfirst := mul_nonneg hδ.le hY
  have hlast : 0 ≤ a ^ 6 / δ ^ 5 := by positivity
  nlinarith

/-- Scaled Young absorption for a square root of the square energy. -/
theorem half_energy_absorption {a Y δ : ℝ}
    (ha : 0 ≤ a) (hY : 0 ≤ Y) (hδ : 0 < δ) :
    a * Y ^ (1 / 2 : ℝ) ≤ δ * Y + a ^ 2 / δ := by
  let u := (δ * Y) ^ (1 / 2 : ℝ)
  let v := a / δ ^ (1 / 2 : ℝ)
  have hp : Real.HolderConjugate 2 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := Real.young_inequality_of_nonneg
    (Real.rpow_nonneg (mul_nonneg hδ.le hY) (1 / 2)) (div_nonneg ha
      (Real.rpow_nonneg hδ.le (1 / 2))) hp
  have hprod : u * v = a * Y ^ (1 / 2 : ℝ) := by
    dsimp [u, v]
    rw [Real.mul_rpow hδ.le hY]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hδ (1 / 2))]
  have hu : u ^ (2 : ℝ) = δ * Y := by
    dsimp [u]
    rw [← Real.rpow_mul (mul_nonneg hδ.le hY)]
    norm_num
  have hv : v ^ (2 : ℝ) = a ^ 2 / δ := by
    dsimp [v]
    rw [Real.div_rpow ha (Real.rpow_nonneg hδ.le (1 / 2)), ← Real.rpow_mul hδ.le]
    norm_num
  change u * v ≤ u ^ (2 : ℝ) / 2 + v ^ (2 : ℝ) / 2 at h
  rw [hprod, hu, hv] at h
  have hfirst := mul_nonneg hδ.le hY
  have hlast : 0 ≤ a ^ 2 / δ := by positivity
  exact h.trans (add_le_add (div_le_self hfirst (by norm_num))
    (div_le_self hlast (by norm_num)))

/-- The endpoint convection coefficient gives precisely power eight of the mixed norm. -/
theorem endpoint_convection_energy_absorption {K X Y δ : ℝ}
    (hK : 0 ≤ K) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hδ : 0 < δ) :
    K * X ^ (4 / 3 : ℝ) * Y ^ (5 / 6 : ℝ) ≤
      δ * Y + K ^ 6 * X ^ 8 / δ ^ 5 := by
  have h := fiveSixths_energy_absorption
    (mul_nonneg hK (Real.rpow_nonneg hX (4 / 3))) hY hδ
  have he : (X ^ (4 / 3 : ℝ)) ^ 6 = X ^ (8 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX]
    norm_num
  simpa only [mul_pow, he] using h

/-- Harmonic and pressure terms with coefficient quadratic in velocity give power four. -/
theorem endpoint_quadratic_energy_absorption {K X Y δ : ℝ}
    (hK : 0 ≤ K) (hY : 0 ≤ Y) (hδ : 0 < δ) :
    K * X ^ 2 * Y ^ (1 / 2 : ℝ) ≤ δ * Y + K ^ 2 * X ^ 4 / δ := by
  have h := half_energy_absorption (mul_nonneg hK (sq_nonneg X)) hY hδ
  simpa only [mul_pow, ← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using h

/-- Two genuine nonlinear error bounds can be absorbed without an energy hypothesis. -/
theorem projected_energy_two_error_absorption {Y Z a₀ a₁ a₂ γ δ : ℝ}
    (hY : 0 ≤ Y) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (henergy : Y ≤ a₀ + a₁ * Y ^ (5 / 6 : ℝ) + a₂ * Y ^ (1 / 2 : ℝ) + γ * Z) :
    Y ≤ (a₀ + a₁ ^ 6 / δ ^ 5 + a₂ ^ 2 / δ + γ * Z) / (1 - 2 * δ) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 - 2 * δ)).mpr
  have h₁ := fiveSixths_energy_absorption ha₁ hY hδ
  have h₂ := half_energy_absorption ha₂ hY hδ
  nlinarith

/-- Finite unrolling of the explicit geometric energy inequality. -/
theorem energy_iteration_unroll {u : ℕ → ℝ} {θ L A : ℝ}
    (hθ : 0 ≤ θ) (hprod : θ * L < 1)
    (hstep : ∀ n, u n ≤ θ * u (n + 1) + A * L ^ n) (n : ℕ) :
    u 0 ≤ θ ^ n * u n + A / (1 - θ * L) * (1 - (θ * L) ^ n) := by
  have hden : 1 - θ * L ≠ 0 := by linarith
  induction n with
  | zero => simp
  | succ n hn =>
      apply hn.trans
      have hs := mul_le_mul_of_nonneg_left (hstep n) (pow_nonneg hθ n)
      calc
        _ ≤ θ ^ n * (θ * u (n + 1) + A * L ^ n) +
            A / (1 - θ * L) * (1 - (θ * L) ^ n) := add_le_add hs le_rfl
        _ = _ := by
          rw [pow_succ, pow_succ, mul_pow]
          field_simp [hden]
          ring

/-- Boundedness eliminates the outer energy in the explicit geometric iteration. -/
theorem bounded_energy_geometric_iteration {u : ℕ → ℝ} {θ L A M : ℝ}
    (hθ : 0 ≤ θ) (hθone : θ < 1) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hprod : θ * L < 1) (hbound : ∀ n, u n ≤ M)
    (hstep : ∀ n, u n ≤ θ * u (n + 1) + A * L ^ n) :
    u 0 ≤ A / (1 - θ * L) := by
  have hK : 0 ≤ A / (1 - θ * L) := div_nonneg hA (by linarith)
  have hfinite (n : ℕ) : u 0 ≤ θ ^ n * M + A / (1 - θ * L) := by
    apply (energy_iteration_unroll hθ hprod hstep n).trans
    have hfirst := mul_le_mul_of_nonneg_left (hbound n) (pow_nonneg hθ n)
    have hlast : A / (1 - θ * L) * (1 - (θ * L) ^ n) ≤ A / (1 - θ * L) := by
      nlinarith [pow_nonneg (mul_nonneg hθ hL) n]
    exact add_le_add hfirst hlast
  have hlim : Tendsto (fun n : ℕ ↦ θ ^ n * M + A / (1 - θ * L)) atTop
      (𝓝 (A / (1 - θ * L))) := by
    simpa only [zero_mul, zero_add] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθone).mul_const M |>.add_const
        (A / (1 - θ * L))
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hfinite

/-- A fixed radius ratio whose eighth power dominates the energy contraction. -/
def projectedHoleFillingRatio : ℝ := 63 / 64

def projectedHoleFillingGrowth : ℝ := (projectedHoleFillingRatio⁻¹) ^ 8

theorem projectedHoleFillingRatio_pos : 0 < projectedHoleFillingRatio := by
  norm_num [projectedHoleFillingRatio]

theorem projectedHoleFillingRatio_lt_one : projectedHoleFillingRatio < 1 := by
  norm_num [projectedHoleFillingRatio]

theorem projectedHoleFillingGrowth_nonneg : 0 ≤ projectedHoleFillingGrowth := by
  unfold projectedHoleFillingGrowth
  positivity

theorem projectedHoleFillingGrowth_contraction : (3 / 4 : ℝ) * projectedHoleFillingGrowth < 1 := by
  norm_num [projectedHoleFillingGrowth, projectedHoleFillingRatio]

/-- Actual increasing nested radii, with initial radius r and limiting outer radius R. -/
def projectedNestedRadius (r R : ℝ) (n : ℕ) : ℝ :=
  r + (R - r) * (1 - projectedHoleFillingRatio ^ n)

@[simp]
theorem projectedNestedRadius_zero (r R : ℝ) : projectedNestedRadius r R 0 = r := by
  simp [projectedNestedRadius]

theorem projectedNestedRadius_mem {r R : ℝ} (hrR : r < R) (n : ℕ) :
    projectedNestedRadius r R n ∈ Set.Icc r R := by
  have hp := pow_nonneg projectedHoleFillingRatio_pos.le n
  have hone := pow_le_one₀ (n := n) projectedHoleFillingRatio_pos.le
    projectedHoleFillingRatio_lt_one.le
  unfold projectedNestedRadius
  constructor <;> nlinarith

theorem projectedNestedRadius_gap (r R : ℝ) (n : ℕ) :
    projectedNestedRadius r R (n + 1) - projectedNestedRadius r R n =
      ((R - r) * (1 - projectedHoleFillingRatio)) * projectedHoleFillingRatio ^ n := by
  unfold projectedNestedRadius
  rw [pow_succ]
  ring

theorem projectedNestedRadius_strictMono {r R : ℝ} (hrR : r < R) :
    StrictMono (projectedNestedRadius r R) := by
  apply strictMono_nat_of_lt_succ
  intro n
  apply lt_of_sub_pos
  rw [projectedNestedRadius_gap]
  exact mul_pos (mul_pos (sub_pos.mpr hrR) (sub_pos.mpr projectedHoleFillingRatio_lt_one))
    (pow_pos projectedHoleFillingRatio_pos n)

/-- The literal reciprocal gap power is exactly the forcing geometric growth. -/
theorem projectedNestedRadius_forcing (r R A : ℝ) (n : ℕ) :
    A / (projectedNestedRadius r R (n + 1) - projectedNestedRadius r R n) ^ 8 =
      (A / ((R - r) * (1 - projectedHoleFillingRatio)) ^ 8) *
        projectedHoleFillingGrowth ^ n := by
  rw [projectedNestedRadius_gap]
  simp only [projectedHoleFillingGrowth, div_eq_mul_inv, mul_pow, mul_inv_rev,
    inv_pow, ← pow_mul, Nat.mul_comm]
  ring

/-- True bounded nested-radius iteration removes the outer square-energy term. -/
theorem bounded_projected_nested_radius_iteration {E : ℝ → ℝ} {r R A M : ℝ}
    (hrR : r < R) (hA : 0 ≤ A) (hbound : ∀ s ∈ Set.Icc r R, E s ≤ M)
    (hstep : ∀ s t, r ≤ s → s < t → t ≤ R → E s ≤ (3 / 4) * E t + A / (t - s) ^ 8) :
    E r ≤ (A / ((R - r) * (1 - projectedHoleFillingRatio)) ^ 8) /
      (1 - (3 / 4) * projectedHoleFillingGrowth) := by
  have hA' : 0 ≤ A / ((R - r) * (1 - projectedHoleFillingRatio)) ^ 8 := by positivity
  have hb (n : ℕ) : E (projectedNestedRadius r R n) ≤ M :=
    hbound _ (projectedNestedRadius_mem hrR n)
  have hs (n : ℕ) : E (projectedNestedRadius r R n) ≤
      (3 / 4) * E (projectedNestedRadius r R (n + 1)) +
        (A / ((R - r) * (1 - projectedHoleFillingRatio)) ^ 8) *
          projectedHoleFillingGrowth ^ n := by
    have h := hstep _ _ (projectedNestedRadius_mem hrR n).1
      (projectedNestedRadius_strictMono hrR (Nat.lt_succ_self n))
      (projectedNestedRadius_mem hrR (n + 1)).2
    simpa only [projectedNestedRadius_forcing] using h
  simpa only [projectedNestedRadius_zero] using bounded_energy_geometric_iteration
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
    projectedHoleFillingGrowth_nonneg hA' projectedHoleFillingGrowth_contraction hb hs

/-- A finite universal coefficient for the unit-cylinder radius interval. -/
def projectedUnitCaccioppoliConstant : ℝ :=
  (1 / (((1 / 4 : ℝ) * (1 - projectedHoleFillingRatio)) ^ 8)) /
    (1 - (3 / 4) * projectedHoleFillingGrowth)

theorem projectedUnitCaccioppoliConstant_nonneg : 0 ≤ projectedUnitCaccioppoliConstant := by
  unfold projectedUnitCaccioppoliConstant
  exact div_nonneg (by positivity) (by linarith [projectedHoleFillingGrowth_contraction])

/-- The exact scalar hole-filling conclusion on the unit-cylinder radius interval. -/
theorem bounded_projected_unit_radius_iteration {E : ℝ → ℝ} {A M : ℝ}
    (hA : 0 ≤ A) (hbound : ∀ s ∈ Set.Icc (3 / 4 : ℝ) 1, E s ≤ M)
    (hstep : ∀ s t, (3 / 4 : ℝ) ≤ s → s < t → t ≤ 1 →
      E s ≤ (3 / 4) * E t + A / (t - s) ^ 8) :
    E (3 / 4) ≤ projectedUnitCaccioppoliConstant * A := by
  have h := bounded_projected_nested_radius_iteration (by norm_num : (3 / 4 : ℝ) < 1)
    hA hbound hstep
  apply h.trans_eq
  norm_num only [show (1 - 3 / 4 : ℝ) = 1 / 4 by norm_num]
  unfold projectedUnitCaccioppoliConstant
  ring

/-- Lower gap powers are dominated by the eighth power on the actual unit-radius interval. -/
theorem endpoint_caccioppoli_gap_errors_le {d X K : ℝ}
    (hd : 0 < d) (hdone : d ≤ 1) (hK : 0 ≤ K) :
    K * (X ^ 2 / d ^ 2 + X ^ 4 / d ^ 8 + X ^ 8 / d ^ 6) ≤
      K * (X ^ 2 + X ^ 4 + X ^ 8) / d ^ 8 := by
  have htwo := div_le_div_of_nonneg_left (sq_nonneg X) (pow_pos hd 8)
    (pow_le_pow_of_le_one hd.le hdone (by norm_num : (2 : ℕ) ≤ 8))
  have heighth : 0 ≤ X ^ 8 := by positivity
  have hsix := div_le_div_of_nonneg_left heighth (pow_pos hd 8)
    (pow_le_pow_of_le_one hd.le hdone (by norm_num : (6 : ℕ) ≤ 8))
  calc
    _ ≤ K * (X ^ 2 / d ^ 8 + X ^ 4 / d ^ 8 + X ^ 8 / d ^ 8) := by
      gcongr
    _ = _ := by ring

/-- Explicit quantitative one-step Caccioppoli bounds give the precise endpoint norm powers. -/
theorem endpoint_caccioppoli_bounded_iteration {E : ℝ → ℝ} {X K M : ℝ}
    (hK : 0 ≤ K) (hbound : ∀ s ∈ Set.Icc (3 / 4 : ℝ) 1, E s ≤ M)
    (hstep : ∀ s t, (3 / 4 : ℝ) ≤ s → s < t → t ≤ 1 →
      E s ≤ (3 / 4) * E t +
        K * (X ^ 2 / (t - s) ^ 2 + X ^ 4 / (t - s) ^ 8 + X ^ 8 / (t - s) ^ 6)) :
    E (3 / 4) ≤ projectedUnitCaccioppoliConstant * K * (X ^ 2 + X ^ 4 + X ^ 8) := by
  have hA : 0 ≤ K * (X ^ 2 + X ^ 4 + X ^ 8) := by positivity
  have hs s t (hslow : (3 / 4 : ℝ) ≤ s) (hst : s < t) (ht : t ≤ 1) :
      E s ≤ (3 / 4) * E t + K * (X ^ 2 + X ^ 4 + X ^ 8) / (t - s) ^ 8 := by
    apply (hstep s t hslow hst ht).trans
    exact add_le_add le_rfl (endpoint_caccioppoli_gap_errors_le (sub_pos.mpr hst)
      (by linarith) hK)
  simpa only [mul_assoc] using bounded_projected_unit_radius_iteration hA hbound hs

/-- Squared mixed cost has precisely powers one, two, and four. -/
theorem endpoint_squared_cost_polynomial_eq (X : ℝ) :
    X ^ 2 + X ^ 4 + X ^ 8 = X ^ 2 + (X ^ 2) ^ 2 + (X ^ 2) ^ 4 := by ring

theorem endpoint_squared_cost_polynomial_le {A : ℝ} (hA : 0 ≤ A) (hAone : A ≤ 1) :
    A + A ^ 2 + A ^ 4 ≤ 3 * A := by
  have htwo := pow_le_pow_of_le_one hA hAone (by norm_num : (1 : ℕ) ≤ 2)
  have hfour := pow_le_pow_of_le_one hA hAone (by norm_num : (1 : ℕ) ≤ 4)
  norm_num only [pow_one] at htwo hfour
  linarith

end FluidSingularSets
