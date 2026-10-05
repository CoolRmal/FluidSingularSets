-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedCaccioppoliAlgebra

/-!
# Bounded projected radius iteration with reciprocal gap power thirty-two

These are scalar consequences of explicit quantitative inequalities. The genuine
harmonic boundary-margin estimates may require larger reciprocal gap powers
than eight. The ratio 255/256 allows all powers up to thirty-two while preserving
the original endpoint source polynomial X² + X⁴ + X⁸.
-/

@[expose] public section

open Filter
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- A true radius ratio whose reciprocal thirty-second power preserves contraction. -/
def projectedHoleFillingRatio32 : ℝ := 255 / 256

/-- The actual forcing growth for reciprocal gap power thirty-two. -/
def projectedHoleFillingGrowth32 : ℝ := (projectedHoleFillingRatio32⁻¹) ^ 32

theorem projectedHoleFillingRatio32_pos : 0 < projectedHoleFillingRatio32 := by
  norm_num [projectedHoleFillingRatio32]

theorem projectedHoleFillingRatio32_lt_one : projectedHoleFillingRatio32 < 1 := by
  norm_num [projectedHoleFillingRatio32]

theorem projectedHoleFillingGrowth32_nonneg : 0 ≤ projectedHoleFillingGrowth32 := by
  unfold projectedHoleFillingGrowth32
  positivity

/-- The explicit geometric energy coefficient still contracts at exponent thirty-two. -/
theorem projectedHoleFillingGrowth32_contraction :
    (3 / 4 : ℝ) * projectedHoleFillingGrowth32 < 1 := by
  norm_num [projectedHoleFillingGrowth32, projectedHoleFillingRatio32]

/-- The actual nested radii for the larger reciprocal gap exponent. -/
def projectedNestedRadius32 (r R : ℝ) (n : ℕ) : ℝ :=
  r + (R - r) * (1 - projectedHoleFillingRatio32 ^ n)

@[simp]
theorem projectedNestedRadius32_zero (r R : ℝ) : projectedNestedRadius32 r R 0 = r := by
  simp [projectedNestedRadius32]

theorem projectedNestedRadius32_mem {r R : ℝ} (hrR : r < R) (n : ℕ) :
    projectedNestedRadius32 r R n ∈ Set.Icc r R := by
  have hp := pow_nonneg projectedHoleFillingRatio32_pos.le n
  have hone := pow_le_one₀ (n := n) projectedHoleFillingRatio32_pos.le
    projectedHoleFillingRatio32_lt_one.le
  unfold projectedNestedRadius32
  constructor <;> nlinarith

theorem projectedNestedRadius32_gap (r R : ℝ) (n : ℕ) :
    projectedNestedRadius32 r R (n + 1) - projectedNestedRadius32 r R n =
      ((R - r) * (1 - projectedHoleFillingRatio32)) * projectedHoleFillingRatio32 ^ n := by
  unfold projectedNestedRadius32
  rw [pow_succ]
  ring

theorem projectedNestedRadius32_strictMono {r R : ℝ} (hrR : r < R) :
    StrictMono (projectedNestedRadius32 r R) := by
  apply strictMono_nat_of_lt_succ
  intro n
  apply lt_of_sub_pos
  rw [projectedNestedRadius32_gap]
  exact mul_pos (mul_pos (sub_pos.mpr hrR) (sub_pos.mpr projectedHoleFillingRatio32_lt_one))
    (pow_pos projectedHoleFillingRatio32_pos n)

/-- The actual reciprocal gap power is exactly a geometric forcing sequence. -/
theorem projectedNestedRadius32_forcing (r R A : ℝ) (n : ℕ) :
    A / (projectedNestedRadius32 r R (n + 1) - projectedNestedRadius32 r R n) ^ 32 =
      (A / ((R - r) * (1 - projectedHoleFillingRatio32)) ^ 32) *
        projectedHoleFillingGrowth32 ^ n := by
  rw [projectedNestedRadius32_gap]
  simp only [projectedHoleFillingGrowth32, div_eq_mul_inv, mul_pow, mul_inv_rev,
    inv_pow, ← pow_mul, Nat.mul_comm]
  ring

/-- Genuine bounded scalar iteration removes the outer energy at exponent thirty-two. -/
theorem bounded_projected_nested_radius_iteration32 {E : ℝ → ℝ} {r R A M : ℝ}
    (hrR : r < R) (hA : 0 ≤ A) (hbound : ∀ s ∈ Set.Icc r R, E s ≤ M)
    (hstep : ∀ s t, r ≤ s → s < t → t ≤ R →
      E s ≤ (3 / 4) * E t + A / (t - s) ^ 32) :
    E r ≤ (A / ((R - r) * (1 - projectedHoleFillingRatio32)) ^ 32) /
      (1 - (3 / 4) * projectedHoleFillingGrowth32) := by
  have hA' : 0 ≤ A / ((R - r) * (1 - projectedHoleFillingRatio32)) ^ 32 := by positivity
  have hb (n : ℕ) : E (projectedNestedRadius32 r R n) ≤ M :=
    hbound _ (projectedNestedRadius32_mem hrR n)
  have hs (n : ℕ) : E (projectedNestedRadius32 r R n) ≤
      (3 / 4) * E (projectedNestedRadius32 r R (n + 1)) +
        (A / ((R - r) * (1 - projectedHoleFillingRatio32)) ^ 32) *
          projectedHoleFillingGrowth32 ^ n := by
    have h := hstep _ _ (projectedNestedRadius32_mem hrR n).1
      (projectedNestedRadius32_strictMono hrR (Nat.lt_succ_self n))
      (projectedNestedRadius32_mem hrR (n + 1)).2
    simpa only [projectedNestedRadius32_forcing] using h
  simpa only [projectedNestedRadius32_zero] using bounded_energy_geometric_iteration
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
    projectedHoleFillingGrowth32_nonneg hA' projectedHoleFillingGrowth32_contraction hb hs

/-- A finite genuine unit-radius coefficient for forcing gap power thirty-two. -/
def projectedUnitCaccioppoliConstant32 : ℝ :=
  (1 / (((1 / 4 : ℝ) * (1 - projectedHoleFillingRatio32)) ^ 32)) /
    (1 - (3 / 4) * projectedHoleFillingGrowth32)

theorem projectedUnitCaccioppoliConstant32_nonneg :
    0 ≤ projectedUnitCaccioppoliConstant32 := by
  unfold projectedUnitCaccioppoliConstant32
  exact div_nonneg (by positivity) (by linarith [projectedHoleFillingGrowth32_contraction])

/-- The explicit scalar iteration conclusion on the actual unit-radius interval. -/
theorem bounded_projected_unit_radius_iteration32 {E : ℝ → ℝ} {A M : ℝ}
    (hA : 0 ≤ A) (hbound : ∀ s ∈ Set.Icc (3 / 4 : ℝ) 1, E s ≤ M)
    (hstep : ∀ s t, (3 / 4 : ℝ) ≤ s → s < t → t ≤ 1 →
      E s ≤ (3 / 4) * E t + A / (t - s) ^ 32) :
    E (3 / 4) ≤ projectedUnitCaccioppoliConstant32 * A := by
  have h := bounded_projected_nested_radius_iteration32 (by norm_num : (3 / 4 : ℝ) < 1)
    hA hbound hstep
  apply h.trans_eq
  norm_num only [show (1 - 3 / 4 : ℝ) = 1 / 4 by norm_num]
  unfold projectedUnitCaccioppoliConstant32
  ring

/-- Every smaller reciprocal gap power is controlled by the true thirty-second power. -/
theorem projected_gap_power32_le {d A : ℝ} {n : ℕ}
    (hd : 0 < d) (hdone : d ≤ 1) (hA : 0 ≤ A) (hn : n ≤ 32) :
    A / d ^ n ≤ A / d ^ 32 :=
  div_le_div_of_nonneg_left hA (pow_pos hd 32) (pow_le_pow_of_le_one hd.le hdone hn)

/-- All three true endpoint source powers survive arbitrary gap exponents up to thirty-two. -/
theorem endpoint_caccioppoli_gap_errors32_le {d X K : ℝ} {n₂ n₄ n₈ : ℕ}
    (hd : 0 < d) (hdone : d ≤ 1) (hK : 0 ≤ K)
    (h₂ : n₂ ≤ 32) (h₄ : n₄ ≤ 32) (h₈ : n₈ ≤ 32) :
    K * (X ^ 2 / d ^ n₂ + X ^ 4 / d ^ n₄ + X ^ 8 / d ^ n₈) ≤
      K * (X ^ 2 + X ^ 4 + X ^ 8) / d ^ 32 := by
  have ht := projected_gap_power32_le hd hdone (sq_nonneg X) h₂
  have hf := projected_gap_power32_le hd hdone (by positivity : 0 ≤ X ^ 4) h₄
  have he := projected_gap_power32_le hd hdone (by positivity : 0 ≤ X ^ 8) h₈
  calc
    _ ≤ K * (X ^ 2 / d ^ 32 + X ^ 4 / d ^ 32 + X ^ 8 / d ^ 32) := by gcongr
    _ = _ := by ring

/-- The honest polynomial source gives the endpoint energy bound with the larger gap exponent. -/
theorem endpoint_caccioppoli_polynomial_iteration32 {E : ℝ → ℝ} {X K M : ℝ}
    (hK : 0 ≤ K) (hbound : ∀ s ∈ Set.Icc (3 / 4 : ℝ) 1, E s ≤ M)
    (hstep : ∀ s t, (3 / 4 : ℝ) ≤ s → s < t → t ≤ 1 →
      E s ≤ (3 / 4) * E t + K * (X ^ 2 + X ^ 4 + X ^ 8) / (t - s) ^ 32) :
    E (3 / 4) ≤ projectedUnitCaccioppoliConstant32 * K * (X ^ 2 + X ^ 4 + X ^ 8) := by
  have hA : 0 ≤ K * (X ^ 2 + X ^ 4 + X ^ 8) := by positivity
  simpa only [mul_assoc] using bounded_projected_unit_radius_iteration32 hA hbound hstep

/-- Explicit quantitative endpoint errors with any smaller gap powers yield the same bound. -/
theorem endpoint_caccioppoli_bounded_iteration32
    {E : ℝ → ℝ} {X K M : ℝ} {n₂ n₄ n₈ : ℕ}
    (hK : 0 ≤ K) (hbound : ∀ s ∈ Set.Icc (3 / 4 : ℝ) 1, E s ≤ M)
    (h₂ : n₂ ≤ 32) (h₄ : n₄ ≤ 32) (h₈ : n₈ ≤ 32)
    (hstep : ∀ s t, (3 / 4 : ℝ) ≤ s → s < t → t ≤ 1 →
      E s ≤ (3 / 4) * E t +
        K * (X ^ 2 / (t - s) ^ n₂ + X ^ 4 / (t - s) ^ n₄ + X ^ 8 / (t - s) ^ n₈)) :
    E (3 / 4) ≤ projectedUnitCaccioppoliConstant32 * K * (X ^ 2 + X ^ 4 + X ^ 8) := by
  apply endpoint_caccioppoli_polynomial_iteration32 hK hbound
  intro s t hslow hst ht
  exact (hstep s t hslow hst ht).trans (add_le_add le_rfl
    (endpoint_caccioppoli_gap_errors32_le (sub_pos.mpr hst) (by linarith) hK h₂ h₄ h₈))

end FluidSingularSets
