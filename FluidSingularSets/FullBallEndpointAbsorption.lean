-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import FluidSingularSets.ProjectedRadiusIteration32
public import FluidSingularSets.FullBallEndpointGapBounds

/-!
# Absorption for the genuine endpoint source coefficients

The source variable in this module is the square of the mixed velocity norm.
The two nonlinear errors therefore have source powers 2/3 and one. Their
absorption gives the polynomial X + X² + X⁴, which is the polynomial of
degrees two, four and eight in the mixed norm.

These are scalar consequences of explicitly stated quantitative inequalities.
The connector Y ≤ 2A + SX expresses the tested energy and the actual mixed
velocity source estimate. The pressure and convection estimates supplying A
are separate analytic theorems; no regularity criterion is assumed here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace FluidSingularSets

/-- Convection absorption when X denotes the square of the mixed velocity norm. -/
theorem endpoint_squaredSource_convection_absorption {K X Y δ : ℝ}
    (hK : 0 ≤ K) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hδ : 0 < δ) :
    K * X ^ (2 / 3 : ℝ) * Y ^ (5 / 6 : ℝ) ≤
      δ * Y + K ^ 6 * X ^ 4 / δ ^ 5 := by
  have h := fiveSixths_energy_absorption
    (mul_nonneg hK (Real.rpow_nonneg hX (2 / 3))) hY hδ
  have he : (X ^ (2 / 3 : ℝ)) ^ 6 = X ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX]
    norm_num
  simpa only [mul_pow, he] using h

/-- Pressure and harmonic square-root errors give the square of the squared source. -/
theorem endpoint_squaredSource_half_absorption {K X Y δ : ℝ}
    (hK : 0 ≤ K) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hδ : 0 < δ) :
    K * X * Y ^ (1 / 2 : ℝ) ≤ δ * Y + K ^ 2 * X ^ 2 / δ := by
  simpa only [mul_pow] using half_energy_absorption (mul_nonneg hK hX) hY hδ

/-- The actual tested-energy connector preserves the three required source powers. -/
theorem endpoint_squaredSource_connector_absorption {Y A X S c₀ c₁ c₂ γ Z : ℝ}
    (hY : 0 ≤ Y) (hX : 0 ≤ X) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hconnector : Y ≤ 2 * A + S * X)
    (hA : A ≤ c₀ * X + c₁ * X ^ (2 / 3 : ℝ) * Y ^ (5 / 6 : ℝ) +
      c₂ * X * Y ^ (1 / 2 : ℝ) + γ * Z) :
    Y ≤ (4 * c₀ + 2 * S) * X + 131072 * c₁ ^ 6 * X ^ 4 +
      32 * c₂ ^ 2 * X ^ 2 + 4 * γ * Z := by
  have hc := endpoint_squaredSource_convection_absorption
    (by positivity : 0 ≤ 2 * c₁) hX hY (by norm_num : (0 : ℝ) < 1 / 4)
  have hh := endpoint_squaredSource_half_absorption
    (by positivity : 0 ≤ 2 * c₂) hX hY (by norm_num : (0 : ℝ) < 1 / 4)
  norm_num [mul_pow] at hc hh
  nlinarith

/-- The explicit finite coefficient after the two genuine Young absorptions. -/
def fullBallEndpointAbsorptionConstant (K₀ K₁ K₂ KS : ℝ) : ℝ :=
  4 * K₀ + 2 * KS + 32 * K₂ ^ 2 + 131072 * K₁ ^ 6

theorem fullBallEndpointAbsorptionConstant_nonneg {K₀ K₁ K₂ KS : ℝ}
    (hK₀ : 0 ≤ K₀) (hKS : 0 ≤ KS) :
    0 ≤ fullBallEndpointAbsorptionConstant K₀ K₁ K₂ KS := by
  unfold fullBallEndpointAbsorptionConstant
  positivity

/-- Smaller reciprocal powers on a gap at most one are dominated by larger powers. -/
theorem endpoint_reciprocal_gap_power_le {d K : ℝ} {m n : ℕ}
    (hd : 0 < d) (hdone : d ≤ 1) (hK : 0 ≤ K) (hmn : m ≤ n) :
    K / d ^ m ≤ K / d ^ n :=
  div_le_div_of_nonneg_left hK (pow_pos hd n)
    (pow_le_pow_of_le_one hd.le hdone hmn)

/-- Actual endpoint coefficient powers give a twelfth-power forcing gap after absorption. -/
theorem endpoint_squaredSource_gap_connector_absorption
    {Y A X S K₀ K₁ K₂ KS d γ Z : ℝ}
    (hY : 0 ≤ Y) (hX : 0 ≤ X)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hKS : 0 ≤ KS)
    (hd : 0 < d) (hdone : d ≤ 1) (hS : S ≤ KS / d ^ 6)
    (hconnector : Y ≤ 2 * A + S * X)
    (hA : A ≤ K₀ / d ^ 8 * X + K₁ / d ^ 2 * X ^ (2 / 3 : ℝ) *
      Y ^ (5 / 6 : ℝ) + K₂ / d ^ 6 * X * Y ^ (1 / 2 : ℝ) + γ * Z) :
    Y ≤ 4 * γ * Z + fullBallEndpointAbsorptionConstant K₀ K₁ K₂ KS /
      d ^ 12 * (X + X ^ 2 + X ^ 4) := by
  have h := endpoint_squaredSource_connector_absorption hY hX
    (by positivity : 0 ≤ K₁ / d ^ 2) (by positivity : 0 ≤ K₂ / d ^ 6)
    hconnector hA
  have hp₁ : (K₁ / d ^ 2) ^ 6 = K₁ ^ 6 / d ^ 12 := by
    rw [div_pow, ← pow_mul]
  have hp₂ : (K₂ / d ^ 6) ^ 2 = K₂ ^ 2 / d ^ 12 := by
    rw [div_pow, ← pow_mul]
  rw [hp₁, hp₂] at h
  have hc₀ : 4 * (K₀ / d ^ 8) + 2 * S ≤ (4 * K₀ + 2 * KS) / d ^ 12 := by
    have h₀ := endpoint_reciprocal_gap_power_le hd hdone hK₀
      (by norm_num : (8 : ℕ) ≤ 12)
    have hs := hS.trans (endpoint_reciprocal_gap_power_le hd hdone hKS
      (by norm_num : (6 : ℕ) ≤ 12))
    calc
      _ ≤ 4 * (K₀ / d ^ 12) + 2 * (KS / d ^ 12) := by linarith
      _ = _ := by ring
  have hP₁ : X ≤ X + X ^ 2 + X ^ 4 := by nlinarith [sq_nonneg X, sq_nonneg (X ^ 2)]
  have hP₂ : X ^ 2 ≤ X + X ^ 2 + X ^ 4 := by nlinarith [sq_nonneg (X ^ 2)]
  have hP₄ : X ^ 4 ≤ X + X ^ 2 + X ^ 4 := by nlinarith [sq_nonneg X]
  calc
    Y ≤ (4 * K₀ + 2 * KS) / d ^ 12 * X +
        131072 * (K₁ ^ 6 / d ^ 12) * X ^ 4 +
        32 * (K₂ ^ 2 / d ^ 12) * X ^ 2 + 4 * γ * Z := by
      exact h.trans (by gcongr)
    _ ≤ (4 * K₀ + 2 * KS) / d ^ 12 * (X + X ^ 2 + X ^ 4) +
        131072 * (K₁ ^ 6 / d ^ 12) * (X + X ^ 2 + X ^ 4) +
        32 * (K₂ ^ 2 / d ^ 12) * (X + X ^ 2 + X ^ 4) + 4 * γ * Z := by
      gcongr
    _ = _ := by unfold fullBallEndpointAbsorptionConstant; ring

/-- The true original-gradient source error preserves the same endpoint source polynomial. -/
theorem endpoint_squaredSource_gap_original_energy_absorption
    {E Y A X S K₀ K₁ K₂ KS H d γ Z : ℝ}
    (hY : 0 ≤ Y) (hX : 0 ≤ X)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hKS : 0 ≤ KS) (hH : 0 ≤ H)
    (hd : 0 < d) (hdone : d ≤ 1) (hS : S ≤ KS / d ^ 6)
    (hconnector : Y ≤ 2 * A + S * X)
    (hA : A ≤ K₀ / d ^ 8 * X + K₁ / d ^ 2 * X ^ (2 / 3 : ℝ) *
      Y ^ (5 / 6 : ℝ) + K₂ / d ^ 6 * X * Y ^ (1 / 2 : ℝ) + γ * Z)
    (hE : E ≤ Y + H / d ^ 12 * X) :
    E ≤ 4 * γ * Z + (fullBallEndpointAbsorptionConstant K₀ K₁ K₂ KS + H) /
      d ^ 12 * (X + X ^ 2 + X ^ 4) := by
  have hy := endpoint_squaredSource_gap_connector_absorption hY hX hK₀ hK₁ hK₂ hKS
    hd hdone hS hconnector hA
  have hP : X ≤ X + X ^ 2 + X ^ 4 := by nlinarith [sq_nonneg X, sq_nonneg (X ^ 2)]
  calc
    E ≤ Y + H / d ^ 12 * X := hE
    _ ≤ 4 * γ * Z + fullBallEndpointAbsorptionConstant K₀ K₁ K₂ KS /
        d ^ 12 * (X + X ^ 2 + X ^ 4) + H / d ^ 12 * (X + X ^ 2 + X ^ 4) := by
      exact add_le_add hy (mul_le_mul_of_nonneg_left hP (by positivity))
    _ = _ := by ring

/-- A chosen adjustable gradient coefficient gives the actual three-quarter scalar contraction. -/
theorem endpoint_squaredSource_gap_original_energy_holeFilling
    {E Y A X S K₀ K₁ K₂ KS H d Z : ℝ}
    (hY : 0 ≤ Y) (hX : 0 ≤ X)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hKS : 0 ≤ KS) (hH : 0 ≤ H)
    (hd : 0 < d) (hdone : d ≤ 1) (hS : S ≤ KS / d ^ 6)
    (hconnector : Y ≤ 2 * A + S * X)
    (hA : A ≤ K₀ / d ^ 8 * X + K₁ / d ^ 2 * X ^ (2 / 3 : ℝ) *
      Y ^ (5 / 6 : ℝ) + K₂ / d ^ 6 * X * Y ^ (1 / 2 : ℝ) + (3 / 16) * Z)
    (hE : E ≤ Y + H / d ^ 12 * X) :
    E ≤ (3 / 4) * Z + (fullBallEndpointAbsorptionConstant K₀ K₁ K₂ KS + H) /
      d ^ 32 * (X + X ^ 2 + X ^ 4) := by
  have h := endpoint_squaredSource_gap_original_energy_absorption hY hX hK₀ hK₁ hK₂ hKS
    hH hd hdone hS hconnector hA hE
  norm_num only [show (4 : ℝ) * (3 / 16) = 3 / 4 by norm_num] at h
  apply h.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right
  · exact projected_gap_power32_le hd hdone
      (add_nonneg (fullBallEndpointAbsorptionConstant_nonneg hK₀ hKS) hH)
      (by norm_num : (12 : ℕ) ≤ 32)
  · positivity

/-- Genuine bounded radius iteration for the square of the mixed velocity norm. -/
theorem endpoint_squaredSource_caccioppoli_iteration32 {E : ℝ → ℝ} {X K M : ℝ}
    (hX : 0 ≤ X) (hK : 0 ≤ K) (hbound : ∀ s ∈ Set.Icc (3 / 4 : ℝ) 1, E s ≤ M)
    (hstep : ∀ s t, (3 / 4 : ℝ) ≤ s → s < t → t ≤ 1 →
      E s ≤ (3 / 4) * E t + K * (X + X ^ 2 + X ^ 4) / (t - s) ^ 32) :
    E (3 / 4) ≤ projectedUnitCaccioppoliConstant32 * K * (X + X ^ 2 + X ^ 4) := by
  have hA : 0 ≤ K * (X + X ^ 2 + X ^ 4) := by positivity
  simpa only [mul_assoc] using bounded_projected_unit_radius_iteration32 hA hbound hstep

/-- The true midpoint slice-source square has a universal reciprocal sixth-gap bound. -/
theorem fullBall_endpoint_connectorSource_midpoint_le_gap {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hR : R ≤ 1) :
    (fullBallProjectedVelocitySliceCoefficient ((r + R) / 2)).toReal ^ 2 ≤
      (64 * fullBallFixedProjectedSliceConstant ^ 2) / (R - r) ^ 6 := by
  have h := pow_le_pow_left₀ ENNReal.toReal_nonneg
    (fullBallProjectedVelocitySliceCoefficient_midpoint_le_gap hr hrR hR) 2
  apply h.trans_eq
  rw [div_pow, ← pow_mul]
  norm_num only [show (3 : ℕ) * 2 = 6 by norm_num, mul_pow,
    show (8 : ℝ) ^ (2 : ℕ) = 64 by norm_num]

end FluidSingularSets
